module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.StableRootSuffixOrigin

@[expose] public section

/-! # Confirmation-record origins

The confirmation floor has a third outcome. A stored confirmation value can
therefore come from genesis, from a user selection, or from the stable root
written by an earlier confirmation tick. The stable-root arm is explicit so
consumers do not silently assume the pre-floor two-way origin.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace ConfirmationOrigin

open Internal Execution Internal.NamedRecoveryRead Protocol Proofs.Optimistic
open StableRecord NamedOutageClosure

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A non-confirmation tick leaves the confirmation record unchanged. -/
theorem on_tick_emit_latest_of_ne
    (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time)
    (h : ¬ (0 < S.E.slotOf t ∧
      t = Protocol.support_cutoff S.E (S.E.slotOf t))) :
    (on_tick_emit S v n t).1.st.latest_confirmed = n.st.latest_confirmed := by
  show (Protocol.NamedTick.tick
      (NamedProfile.gradeContract
        (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
      S.E S.hc S.cfg (S.node v) n.st n.record t).1.latest_confirmed =
      n.st.latest_confirmed
  simp only [Protocol.NamedTick.tick, Protocol.TickScheduler.runWith,
    Protocol.NamedTick.namedOps, if_neg h]
  split_ifs <;>
    simp only [Protocol.attest_with_latest,
      Protocol.propose_block_with_latest,
      Protocol.named_goldfish_vote_with_latest]

/-- The floor's first arm gives the three possible values of one named
confirmation write. -/
theorem named_confirmation_latest_cases (S : Setup V) (nd : NamedNodeState V) (s : Slot)
    (hfirst : Block.Preceq
      (Protocol.NamedDuties.update_confirmation_with
        (NamedProfile.gradeContract nd.cache) S.E S.hc nd.st s).latest_stable
      (match (NamedProfile.gradeContract nd.cache).confirmationSG with
        | .optional select =>
          if confirmationEligible S.E nd.st.core s (namedConfirmationWalk S nd s) then
            Protocol.advance_confirmed nd.st.core.latest_confirmed
              (namedConfirmationWalk S nd s)
          else
            match select S.E S.hc nd.st.core.toHealing s with
            | some candidate =>
                Protocol.advance_confirmed nd.st.core.latest_confirmed candidate
            | none => nd.st.core.latest_confirmed)) :
    (Protocol.NamedDuties.update_confirmation_with
        (NamedProfile.gradeContract nd.cache) S.E S.hc nd.st s).latest_confirmed =
        nd.st.core.latest_confirmed ∨
      (Protocol.NamedDuties.update_confirmation_with
        (NamedProfile.gradeContract nd.cache) S.E S.hc nd.st s).latest_confirmed =
        namedConfirmationWalk S nd s ∨
      ∃ select, (NamedProfile.gradeContract nd.cache).confirmationSG =
          Protocol.ConfirmationSGCandidate.optional select ∧
        confirmationEligible S.E nd.st.core s (namedConfirmationWalk S nd s) = false ∧
        ∃ B, select S.E S.hc nd.st.core.toHealing s = some B ∧
          (Protocol.NamedDuties.update_confirmation_with
            (NamedProfile.gradeContract nd.cache) S.E S.hc nd.st s).latest_confirmed = B := by
  have hval : (Protocol.NamedDuties.update_confirmation_with
      (NamedProfile.gradeContract nd.cache) S.E S.hc nd.st s).latest_confirmed =
      (match (NamedProfile.gradeContract nd.cache).confirmationSG with
        | .optional select =>
          if confirmationEligible S.E nd.st.core s (namedConfirmationWalk S nd s) then
            Protocol.advance_confirmed nd.st.core.latest_confirmed
              (namedConfirmationWalk S nd s)
          else
            match select S.E S.hc nd.st.core.toHealing s with
            | some candidate =>
                Protocol.advance_confirmed nd.st.core.latest_confirmed candidate
            | none => nd.st.core.latest_confirmed) := by
    have hpre : (Protocol.NamedDuties.update_confirmation_with
        (NamedProfile.gradeContract nd.cache) S.E S.hc nd.st s).latest_confirmed =
        Protocol.floor_on_stable
          (Protocol.NamedDuties.update_confirmation_with
            (NamedProfile.gradeContract nd.cache) S.E S.hc nd.st s).latest_stable
          (match (NamedProfile.gradeContract nd.cache).confirmationSG with
            | .optional select =>
              if confirmationEligible S.E nd.st.core s (namedConfirmationWalk S nd s) then
                Protocol.advance_confirmed nd.st.core.latest_confirmed
                  (namedConfirmationWalk S nd s)
              else
                match select S.E S.hc nd.st.core.toHealing s with
                | some candidate =>
                    Protocol.advance_confirmed nd.st.core.latest_confirmed candidate
                | none => nd.st.core.latest_confirmed)
          nd.st.core.latest_confirmed := rfl
    rw [hpre]
    unfold Protocol.floor_on_stable
    have hfirst' : Block.preceq
        (Protocol.NamedDuties.update_confirmation_with
          (NamedProfile.gradeContract nd.cache) S.E S.hc nd.st s).latest_stable
        (match (NamedProfile.gradeContract nd.cache).confirmationSG with
          | .optional select =>
            if confirmationEligible S.E nd.st.core s (namedConfirmationWalk S nd s) then
              Protocol.advance_confirmed nd.st.core.latest_confirmed
                (namedConfirmationWalk S nd s)
            else
              match select S.E S.hc nd.st.core.toHealing s with
              | some candidate =>
                  Protocol.advance_confirmed nd.st.core.latest_confirmed candidate
              | none => nd.st.core.latest_confirmed) = true := hfirst
    rw [if_pos hfirst']
  have hcases : ∃ select, (NamedProfile.gradeContract nd.cache).confirmationSG =
        Protocol.ConfirmationSGCandidate.optional select := by
    cases h : (NamedProfile.gradeContract nd.cache).confirmationSG with
    | optional select => exact ⟨select, rfl⟩
  rcases hcases with ⟨select, hmode⟩
  simp only [hmode] at hval
  split_ifs at hval with helig
  · rcases Proofs.ConfirmationPolicy.advance_eq_old_or_candidate nd.st.core.latest_confirmed
        (namedConfirmationWalk S nd s) with h | h
    · exact Or.inl (hval.trans h)
    · exact Or.inr (Or.inl (hval.trans h))
  · have helig' : confirmationEligible S.E nd.st.core s
        (namedConfirmationWalk S nd s) = false := by simpa using helig
    cases hsel : select S.E S.hc nd.st.core.toHealing s with
    | none =>
        simp only [hsel] at hval
        exact Or.inl hval
    | some B =>
        simp only [hsel] at hval
        rcases Proofs.ConfirmationPolicy.advance_eq_old_or_candidate
            nd.st.core.latest_confirmed B with h | h
        · exact Or.inl (hval.trans h)
        · exact Or.inr (Or.inr ⟨select, hmode, helig', B, hsel, hval.trans h⟩)

/-- The two record fields exposed after one confirmation tick. -/
theorem stateBefore_succ_of_confirmation_tick (S : Setup V) (rho : Run V) (v : V)
    (n : Nat) {t : Time} (hn : rho.events[n]? = some (Event.tick v t))
    (hpos : 0 < S.E.slotOf t)
    (ht : t = Protocol.support_cutoff S.E (S.E.slotOf t)) :
    (rho.stateBefore S (n + 1) v).st.latest_confirmed =
        (Protocol.NamedDuties.update_confirmation_with
          (NamedProfile.gradeContract
            (NamedActionReads.confirmationReadFrom S
              (rho.stateBefore S n v) t).cache)
          S.E S.hc
          (NamedActionReads.confirmationReadFrom S
            (rho.stateBefore S n v) t).st (S.E.slotOf t - 1)).latest_confirmed ∧
      (rho.stateBefore S (n + 1) v).st.latest_stable =
        (Protocol.NamedDuties.update_confirmation_with
          (NamedProfile.gradeContract
            (NamedActionReads.confirmationReadFrom S
              (rho.stateBefore S n v) t).cache)
          S.E S.hc
          (NamedActionReads.confirmationReadFrom S
            (rho.stateBefore S n v) t).st (S.E.slotOf t - 1)).latest_stable := by
  have hout := on_tick_emit_confirmation_latest S v
    (rho.stateBefore S n v) (S.E.slotOf t) hpos
  have hstable := on_tick_emit_confirmation_stable S v
    (rho.stateBefore S n v) (S.E.slotOf t) hpos
  rw [← ht] at hout hstable
  constructor
  · unfold Run.stateBefore NamedRun.stateBefore
    rw [List.take_add_one, List.foldl_append, hn]
    simp only [Option.toList, List.foldl_cons, List.foldl_nil,
      NamedWorld.step, Function.update_self]
    exact hout
  · unfold Run.stateBefore NamedRun.stateBefore
    rw [List.take_add_one, List.foldl_append, hn]
    simp only [Option.toList, List.foldl_cons, List.foldl_nil,
      NamedWorld.step, Function.update_self]
    exact hstable

omit [Fintype V] in
/-- The floor keeps its stable argument below the result. -/
theorem stable_preceq_floor_on_stable (stable candidate old : Block V) :
    Block.Preceq stable (Protocol.floor_on_stable stable candidate old) := by
  unfold Protocol.floor_on_stable
  split_ifs with h1 h2
  · exact h1
  · exact h2
  · exact Block.preceq_self _

/-- One confirmation write leaves its stable record below its confirmation
record. -/
theorem update_confirmation_stable_le_confirmed
    (contract : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) (s : Slot) :
    Block.Preceq
      (Protocol.NamedDuties.update_confirmation_with contract E hc st s).latest_stable
      (Protocol.NamedDuties.update_confirmation_with contract E hc st s).latest_confirmed :=
  stable_preceq_floor_on_stable _ _ _

/-- The stable and confirmation records nest at every event prefix. -/
theorem stateBefore_stable_below_confirmed (S : Setup V) (rho : Run V) (v : V) :
    ∀ n : Nat, Block.Preceq (rho.stateBefore S n v).st.latest_stable
      (rho.stateBefore S n v).st.latest_confirmed := by
  intro n
  induction n with
  | zero => exact Block.preceq_self _
  | succ n ih =>
      unfold Run.stateBefore NamedRun.stateBefore
      rw [List.take_add_one, List.foldl_append]
      cases hn : rho.events[n]? with
      | none => exact ih
      | some e =>
          simp only [Option.toList, List.foldl_cons, List.foldl_nil]
          cases e with
          | deliver u o t =>
              by_cases hu : u = v
              · subst u
                simp only [NamedWorld.step, Function.update_self,
                  NamedOutageClosure.node_process_latest,
                  NamedOutageClosure.node_process_stable]
                exact ih
              · simp only [NamedWorld.step, Function.update_of_ne (Ne.symm hu)]
                exact ih
          | tick u t =>
              by_cases hu : u = v
              · subst u
                simp only [NamedWorld.step, Function.update_self]
                by_cases hbranch : 0 < S.E.slotOf t ∧
                    t = Protocol.support_cutoff S.E (S.E.slotOf t)
                · obtain ⟨hpos, ht⟩ := hbranch
                  have houtC := Protocol.on_tick_emit_confirmation_latest S v
                    (rho.stateBefore S n v) (S.E.slotOf t) hpos
                  have houtS := StableRecord.on_tick_emit_confirmation_stable S v
                    (rho.stateBefore S n v) (S.E.slotOf t) hpos
                  rw [← ht] at houtC houtS
                  show Block.Preceq
                    (on_tick_emit S v (rho.stateBefore S n v) t).1.st.latest_stable
                    (on_tick_emit S v (rho.stateBefore S n v) t).1.st.latest_confirmed
                  rw [houtC, houtS]
                  exact update_confirmation_stable_le_confirmed _ S.E S.hc _ _
                · show Block.Preceq
                    (on_tick_emit S v (rho.stateBefore S n v) t).1.st.latest_stable
                    (on_tick_emit S v (rho.stateBefore S n v) t).1.st.latest_confirmed
                  rw [on_tick_emit_latest_of_ne S v (rho.stateBefore S n v) t hbranch,
                    StableRecord.on_tick_emit_stable_of_ne S v
                      (rho.stateBefore S n v) t hbranch]
                  exact ih
              · simp only [NamedWorld.step, Function.update_of_ne (Ne.symm hu)]
                exact ih

namespace StableRecord

/-- The named store-level facade for the record-nesting invariant. -/
theorem stableBelowConfirmed_storeAt (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) (v : V) (t : Time) :
    Protocol.StableBelowConfirmed (rho.storeAt S v t).core := by
  obtain ⟨n, hn⟩ := Proofs.Bridges.stateAt_eq_stateBefore S sch t
  change Block.Preceq (rho.storeAt S v t).core.latest_stable
    (rho.storeAt S v t).core.latest_confirmed
  simp only [Run.storeAt, hn]
  exact stateBefore_stable_below_confirmed S rho v n

end StableRecord

/-- Every stored confirmation value is genesis, a user selection, or a stable
root computed by an earlier confirmation tick. -/
theorem stateBefore_latest_confirmed_origin (S : Setup V) (rho : Run V) (v : V) :
    ∀ n : Nat,
      (rho.stateBefore S n v).st.latest_confirmed = Block.genesis ∨
        (∃ i C, i < n ∧ UserConfirmationSelectionAt S rho v i C ∧
          (rho.stateBefore S n v).st.latest_confirmed = C) ∨
        (∃ i, i < n ∧ StableRecord.StableRootAt S rho v i
          (rho.stateBefore S n v).st.latest_confirmed) := by
  intro n
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
      by_cases hcase : ∃ t : Time, rho.events[n]? = some (Event.tick v t) ∧
          0 < S.E.slotOf t ∧ t = Protocol.support_cutoff S.E (S.E.slotOf t)
      · obtain ⟨t, hn, hpos, ht⟩ := hcase
        obtain ⟨hrec, hstable⟩ := stateBefore_succ_of_confirmation_tick
          S rho v n hn hpos ht
        set nd := NamedActionReads.confirmationReadFrom S
          (rho.stateBefore S n v) t with hndDef
        let s := S.E.slotOf t - 1
        let arm := match (NamedProfile.gradeContract nd.cache).confirmationSG with
          | .optional select =>
              if confirmationEligible S.E nd.st.core s
                  (namedConfirmationWalk S nd s) then
                Protocol.advance_confirmed nd.st.core.latest_confirmed
                  (namedConfirmationWalk S nd s)
              else
                match select S.E S.hc nd.st.core.toHealing s with
                | some candidate =>
                    Protocol.advance_confirmed nd.st.core.latest_confirmed candidate
                | none => nd.st.core.latest_confirmed
        have hfirst : Block.Preceq
            (Protocol.NamedDuties.update_confirmation_with
              (NamedProfile.gradeContract nd.cache) S.E S.hc nd.st s).latest_stable
            arm ∨ ¬ Block.Preceq
              (Protocol.NamedDuties.update_confirmation_with
                (NamedProfile.gradeContract nd.cache) S.E S.hc nd.st s).latest_stable
              arm := Classical.em _
        rw [hrec]
        rcases hfirst with hfirst | hnot
        · have hcases := named_confirmation_latest_cases S nd s hfirst
          rcases hcases with hkeep | hwalk | ⟨select, hmode, helig, B, hsel, hB⟩
          · rw [hkeep]
            rcases ih with hgen | ⟨i, C, hi, hsel', hvalue⟩ | ⟨i, hi, hroot⟩
            · exact Or.inl hgen
            · exact Or.inr (Or.inl ⟨i, C, Nat.lt_succ_of_lt hi, hsel', hvalue⟩)
            · exact Or.inr (Or.inr ⟨i, Nat.lt_succ_of_lt hi, hroot⟩)
          · rw [hwalk]
            exact Or.inr (Or.inl ⟨n, _, Nat.lt_succ_self n,
              ⟨t, hn, hpos, ht, Or.inl rfl⟩, rfl⟩)
          · rw [hB]
            refine Or.inr (Or.inl ⟨n, B, Nat.lt_succ_self n,
              ⟨t, hn, hpos, ht, Or.inr ?_⟩, rfl⟩)
            simp only [userSGCandidateAtIndex]
            rw [← hndDef]
            simp only [hmode]
            split_ifs with heligTrue
            · rw [helig] at heligTrue
              exact absurd heligTrue Bool.false_ne_true
            · exact hsel
        · have hpre :
              (Protocol.NamedDuties.update_confirmation_with
                (NamedProfile.gradeContract nd.cache) S.E S.hc nd.st s).latest_confirmed =
              Protocol.floor_on_stable
                (Protocol.NamedDuties.update_confirmation_with
                  (NamedProfile.gradeContract nd.cache) S.E S.hc nd.st s).latest_stable
                arm nd.st.core.latest_confirmed := rfl
          rw [hpre]
          unfold Protocol.floor_on_stable
          split_ifs with hfirst' hold'
          · exact False.elim (hnot hfirst')
          ·
            rcases ih with hgen | ⟨i, C, hi, hsel', hvalue⟩ | ⟨i, hi, hroot⟩
            · exact Or.inl hgen
            · exact Or.inr (Or.inl ⟨i, C, Nat.lt_succ_of_lt hi, hsel', hvalue⟩)
            · exact Or.inr (Or.inr ⟨i, Nat.lt_succ_of_lt hi, hroot⟩)
          ·
            rw [← hstable]
            rcases StableRecord.stateBefore_latest_stable_rootOrigin S rho v (n + 1) with
              hgen | ⟨i, hi, hroot⟩
            · exact Or.inl hgen
            · exact Or.inr (Or.inr ⟨i, hi, hroot⟩)
      · have hstep :
            (rho.stateBefore S (n + 1) v).st.latest_confirmed =
              (rho.stateBefore S n v).st.latest_confirmed := by
          unfold Run.stateBefore NamedRun.stateBefore
          rw [List.take_add_one, List.foldl_append]
          cases hn : rho.events[n]? with
          | none => rfl
          | some e =>
              simp only [Option.toList, List.foldl_cons, List.foldl_nil]
              cases e with
              | deliver u o t =>
                  by_cases hu : u = v
                  · subst u
                    simpa only [NamedWorld.step, Function.update_self,
                      NamedOutageClosure.node_process_latest] using
                      (show (NamedNode.process S
                        (rho.stateBefore S n v) o).st.core.latest_confirmed =
                          (rho.stateBefore S n v).st.core.latest_confirmed from
                        NamedOutageClosure.node_process_latest S
                          (rho.stateBefore S n v) o)
                  · simp only [NamedWorld.step, Function.update_of_ne (Ne.symm hu)]
              | tick u t =>
                  by_cases hu : u = v
                  · subst u
                    have hbranch : ¬ (0 < S.E.slotOf t ∧
                        t = Protocol.support_cutoff S.E (S.E.slotOf t)) := by
                      intro hc
                      exact hcase ⟨t, hn, hc.1, hc.2⟩
                    simpa only [NamedWorld.step, Function.update_self] using
                      on_tick_emit_latest_of_ne S v
                        (rho.stateBefore S n v) t hbranch
                  · simp only [NamedWorld.step, Function.update_of_ne (Ne.symm hu)]
        rw [hstep]
        rcases ih with hgen | ⟨i, C, hi, hsel, hvalue⟩ | ⟨i, hi, hroot⟩
        · exact Or.inl hgen
        · exact Or.inr (Or.inl ⟨i, C, Nat.lt_succ_of_lt hi, hsel, hvalue⟩)
        · exact Or.inr (Or.inr ⟨i, Nat.lt_succ_of_lt hi, hroot⟩)

end ConfirmationOrigin

namespace StableRecord

open Internal Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Public root namespace facade for the named record-nesting invariant. -/
theorem stableBelowConfirmed_storeAt (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) (v : V) (t : Time) :
    Protocol.StableBelowConfirmed (rho.storeAt S v t).core :=
  ConfirmationOrigin.StableRecord.stableBelowConfirmed_storeAt S sch v t

end StableRecord
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.ConfirmationOrigin
#print axioms stateBefore_succ_of_confirmation_tick
#print axioms StableRecord.stableBelowConfirmed_storeAt
#print axioms stateBefore_latest_confirmed_origin
end DecoupledConsensusModel.Proofs.ConfirmationOrigin

namespace DecoupledConsensusModel.Proofs.StableRecord
#print axioms stableBelowConfirmed_storeAt
end DecoupledConsensusModel.Proofs.StableRecord

end
