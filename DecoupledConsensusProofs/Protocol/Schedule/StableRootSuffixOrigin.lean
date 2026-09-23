module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.CandidateSafety
public import DecoupledConsensusProofs.Protocol.Handlers.RetentionNamed
public import DecoupledConsensusProofs.Protocol.Grades.Q10Frame

@[expose] public section

/-! # Stable-record origins after an arbitrary prefix

The frame runtime's stable root is total: it is the active projected G2 root,
or the finalized-root fallback when the projection is empty. This file keeps
the root origin explicit at the confirmation read, including that fallback.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace StableRecord

open Internal Execution Internal.NamedRecoveryRead Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A non-confirmation tick leaves the stable record unchanged. -/
theorem on_tick_emit_stable_of_ne
    (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time)
    (h : ¬ (0 < S.E.slotOf t ∧
      t = Protocol.support_cutoff S.E (S.E.slotOf t))) :
    (on_tick_emit S v n t).1.st.latest_stable = n.st.latest_stable := by
  show (Protocol.NamedTick.tick
      (NamedProfile.gradeContract
        (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
      S.E S.hc S.cfg (S.node v) n.st n.record t).1.latest_stable =
      n.st.latest_stable
  simp only [Protocol.NamedTick.tick, Protocol.TickScheduler.runWith,
    Protocol.NamedTick.namedOps, if_neg h]
  split_ifs <;>
    simp only [NamedOutageClosure.attest_with_stable,
      NamedOutageClosure.propose_block_with_stable,
      NamedOutageClosure.named_goldfish_vote_with_stable]

/-- At a support cutoff, the tick's stable field is the confirmation duty's
stable field on its prepared read. -/
theorem on_tick_emit_confirmation_stable (S : Setup V) (v : V)
    (n : NamedNodeState V) (s : Slot) (hs : 0 < s) :
    (on_tick_emit S v n (Protocol.support_cutoff S.E s)).1.st.latest_stable =
      (Protocol.NamedDuties.update_confirmation_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S n
            (Protocol.support_cutoff S.E s)).cache)
        S.E S.hc
        (NamedActionReads.confirmationReadFrom S n
          (Protocol.support_cutoff S.E s)).st (s - 1)).latest_stable := by
  have hslot : S.E.slotOf (Protocol.support_cutoff S.E s) = s :=
    slotOf_support_cutoff S.E s
  simp only [NamedNode.tick, NamedProfile.tick, Protocol.NamedTick.tick,
    Protocol.TickScheduler.runWith, Protocol.NamedTick.namedOps, hslot,
    support_cutoff_ne_proposal_time S.E s, support_cutoff_ne_vote_time S.E s,
    hs, and_true, and_false, false_and, if_true, if_false,
    NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
    Protocol.NamedStore.setClock]
  split
  · exact NamedOutageClosure.attest_with_stable _ S.E S.hc _ _ _
  · rfl

/-! ## The stable root and the prepared SG anchor -/


/-- The stable root computed by an actual confirmation tick. -/
def StableRootAt (S : Setup V) (rho : Run V) (v : V) (i : Nat) (G : Block V) : Prop :=
  ∃ time : Time,
    rho.events[i]? = some (Event.tick v time) ∧
      0 < S.E.slotOf time ∧
      time = Protocol.support_cutoff S.E (S.E.slotOf time) ∧
      DecoupledConsensusModel.Protocol.frameStableRoot
          (NamedActionReads.confirmationReadFrom S
            (rho.stateBefore S i v) time).cache S.E S.hc
          (NamedActionReads.confirmationReadFrom S
            (rho.stateBefore S i v) time).st.core.toHealing
          (S.hc.round_of
            (NamedActionReads.confirmationReadFrom S
              (rho.stateBefore S i v) time).st.core.s) = some G

set_option maxHeartbeats 800000 in
/-- Every stable-record value is genesis or a root written at an earlier
confirmation tick. -/
theorem stateBefore_latest_stable_rootOrigin (S : Setup V) (rho : Run V) (v : V) :
    ∀ n : Nat,
      (rho.stateBefore S n v).st.latest_stable = Block.genesis ∨
        ∃ i : Nat, i < n ∧
          StableRootAt S rho v i (rho.stateBefore S n v).st.latest_stable := by
  intro n
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
      unfold Run.stateBefore NamedRun.stateBefore
      rw [List.take_add_one, List.foldl_append]
      cases hn : rho.events[n]? with
      | none =>
          rcases ih with hgen | ⟨i, hi, hroot⟩
          · exact Or.inl hgen
          · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, hroot⟩
      | some e =>
          simp only [Option.toList, List.foldl_cons, List.foldl_nil]
          cases e with
          | deliver u o t =>
              by_cases hu : u = v
              · subst u
                simp only [NamedWorld.step, Function.update_self,
                  NamedOutageClosure.node_process_stable]
                rcases ih with hgen | ⟨i, hi, hroot⟩
                · exact Or.inl hgen
                · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, hroot⟩
              · simp only [NamedWorld.step, Function.update_of_ne (Ne.symm hu)]
                rcases ih with hgen | ⟨i, hi, hroot⟩
                · exact Or.inl hgen
                · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, hroot⟩
          | tick u t =>
              by_cases hu : u = v
              · subst u
                simp only [NamedWorld.step, Function.update_self]
                by_cases hbranch : 0 < S.E.slotOf t ∧
                    t = Protocol.support_cutoff S.E (S.E.slotOf t)
                · obtain ⟨hpos, ht⟩ := hbranch
                  have hout := on_tick_emit_confirmation_stable S v
                    (rho.stateBefore S n v) (S.E.slotOf t) hpos
                  rw [← ht] at hout
                  change
                    (on_tick_emit S v (rho.stateBefore S n v) t).1.st.latest_stable =
                      Block.genesis ∨
                    ∃ i : Nat, i < n + 1 ∧ StableRootAt S rho v i
                      (on_tick_emit S v (rho.stateBefore S n v) t).1.st.latest_stable
                  rw [hout]
                  let nd := NamedActionReads.confirmationReadFrom S
                    (rho.stateBefore S n v) t
                  let root := (NamedProfile.gradeContract nd.cache).stableRoot S.E S.hc
                    nd.st.core.toHealing (S.hc.round_of nd.st.core.s)
                  change
                    (match root with
                    | some G =>
                        Protocol.advance_confirmed
                          (rho.stateBefore S n v).st.latest_stable G
                    | none => (rho.stateBefore S n v).st.latest_stable) =
                    Block.genesis ∨
                    ∃ i : Nat, i < n + 1 ∧ StableRootAt S rho v i
                      (match root with
                      | some G =>
                          Protocol.advance_confirmed
                            (rho.stateBefore S n v).st.latest_stable G
                      | none => (rho.stateBefore S n v).st.latest_stable)
                  cases hroot : root with
                  | none =>
                      dsimp only
                      rcases ih with hgen | ⟨i, hi, hr⟩
                      · exact Or.inl hgen
                      · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, hr⟩
                  | some G =>
                      dsimp only
                      have hrootAt : StableRootAt S rho v n G := by
                        refine ⟨t, hn, hpos, ht, ?_⟩
                        simpa only [nd, root, NamedProfile.gradeContract] using hroot
                      rcases Proofs.ConfirmationPolicy.advance_eq_old_or_candidate
                          (rho.stateBefore S n v).st.latest_stable G with hkeep | hnew
                      · rw [hkeep]
                        rcases ih with hgen | ⟨i, hi, hr⟩
                        · exact Or.inl hgen
                        · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, hr⟩
                      · rw [hnew]
                        exact Or.inr ⟨n, Nat.lt_succ_self n, hrootAt⟩
                · change
                    (on_tick_emit S v (rho.stateBefore S n v) t).1.st.latest_stable =
                      Block.genesis ∨
                    ∃ i : Nat, i < n + 1 ∧ StableRootAt S rho v i
                      (on_tick_emit S v (rho.stateBefore S n v) t).1.st.latest_stable
                  rw [on_tick_emit_stable_of_ne S v
                    (rho.stateBefore S n v) t hbranch]
                  rcases ih with hgen | ⟨i, hi, hroot⟩
                  · exact Or.inl hgen
                  · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, hroot⟩
              · simp only [NamedWorld.step, Function.update_of_ne (Ne.symm hu)]
                rcases ih with hgen | ⟨i, hi, hroot⟩
                · exact Or.inl hgen
                · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, hroot⟩

set_option maxHeartbeats 800000 in
/-- After an earlier prefix, the stable record is unchanged or was computed by
a confirmation tick at or after that prefix. -/
theorem stateBefore_latest_stable_rootOrigin_after_prefix
    (S : Setup V) (rho : Run V) (v : V) :
    ∀ n m : Nat, m ≤ n →
      (rho.stateBefore S n v).st.latest_stable =
          (rho.stateBefore S m v).st.latest_stable ∨
        ∃ i : Nat, m ≤ i ∧ i < n ∧
          StableRootAt S rho v i (rho.stateBefore S n v).st.latest_stable := by
  intro n
  induction n with
  | zero =>
      intro m hm
      have heq : m = 0 := Nat.eq_zero_of_le_zero hm
      subst m
      exact Or.inl rfl
  | succ n ih =>
      intro m hmn
      by_cases hmn' : m ≤ n
      · have ih' := ih m hmn'
        unfold Run.stateBefore NamedRun.stateBefore
        rw [List.take_add_one, List.foldl_append]
        cases hn : rho.events[n]? with
        | none =>
            rcases ih' with hsame | ⟨i, hmi, hi, hroot⟩
            · exact Or.inl hsame
            · exact Or.inr ⟨i, hmi, Nat.lt_succ_of_lt hi, hroot⟩
        | some e =>
            simp only [Option.toList, List.foldl_cons, List.foldl_nil]
            cases e with
            | deliver u o t =>
                by_cases hu : u = v
                · subst u
                  simp only [NamedWorld.step, Function.update_self,
                    NamedOutageClosure.node_process_stable]
                  rcases ih' with hsame | ⟨i, hmi, hi, hroot⟩
                  · exact Or.inl hsame
                  · exact Or.inr ⟨i, hmi, Nat.lt_succ_of_lt hi, hroot⟩
                · simp only [NamedWorld.step, Function.update_of_ne (Ne.symm hu)]
                  rcases ih' with hsame | ⟨i, hmi, hi, hroot⟩
                  · exact Or.inl hsame
                  · exact Or.inr ⟨i, hmi, Nat.lt_succ_of_lt hi, hroot⟩
            | tick u t =>
                by_cases hu : u = v
                · subst u
                  simp only [NamedWorld.step, Function.update_self]
                  by_cases hbranch : 0 < S.E.slotOf t ∧
                      t = Protocol.support_cutoff S.E (S.E.slotOf t)
                  · obtain ⟨hpos, ht⟩ := hbranch
                    have hout := on_tick_emit_confirmation_stable S v
                      (rho.stateBefore S n v) (S.E.slotOf t) hpos
                    rw [← ht] at hout
                    change
                      (on_tick_emit S v (rho.stateBefore S n v) t).1.st.latest_stable =
                        (rho.stateBefore S m v).st.latest_stable ∨
                      ∃ i : Nat, m ≤ i ∧ i < n + 1 ∧
                        StableRootAt S rho v i
                          (on_tick_emit S v (rho.stateBefore S n v) t).1.st.latest_stable
                    rw [hout]
                    let nd := NamedActionReads.confirmationReadFrom S
                      (rho.stateBefore S n v) t
                    let root := (NamedProfile.gradeContract nd.cache).stableRoot S.E S.hc
                      nd.st.core.toHealing (S.hc.round_of nd.st.core.s)
                    change
                      (match root with
                      | some G =>
                          Protocol.advance_confirmed
                            (rho.stateBefore S n v).st.latest_stable G
                      | none => (rho.stateBefore S n v).st.latest_stable) =
                        (rho.stateBefore S m v).st.latest_stable ∨
                      ∃ i : Nat, m ≤ i ∧ i < n + 1 ∧
                        StableRootAt S rho v i
                          (match root with
                          | some G =>
                              Protocol.advance_confirmed
                                (rho.stateBefore S n v).st.latest_stable G
                          | none => (rho.stateBefore S n v).st.latest_stable)
                    cases hroot : root with
                    | none =>
                        dsimp only
                        rcases ih' with hsame | ⟨i, hmi, hi, hr⟩
                        · exact Or.inl hsame
                        · exact Or.inr ⟨i, hmi, Nat.lt_succ_of_lt hi, hr⟩
                    | some G =>
                        dsimp only
                        have hrootAt : StableRootAt S rho v n G := by
                          refine ⟨t, hn, hpos, ht, ?_⟩
                          simpa only [nd, root, NamedProfile.gradeContract] using hroot
                        rcases Proofs.ConfirmationPolicy.advance_eq_old_or_candidate
                            (rho.stateBefore S n v).st.latest_stable G with hkeep | hnew
                        · rw [hkeep]
                          rcases ih' with hsame | ⟨i, hmi, hi, hr⟩
                          · exact Or.inl hsame
                          · exact Or.inr ⟨i, hmi, Nat.lt_succ_of_lt hi, hr⟩
                        · rw [hnew]
                          exact Or.inr ⟨n, hmn', Nat.lt_succ_self n, hrootAt⟩
                  · change
                      (on_tick_emit S v (rho.stateBefore S n v) t).1.st.latest_stable =
                        (rho.stateBefore S m v).st.latest_stable ∨
                      ∃ i : Nat, m ≤ i ∧ i < n + 1 ∧
                        StableRootAt S rho v i
                          (on_tick_emit S v (rho.stateBefore S n v) t).1.st.latest_stable
                    rw [on_tick_emit_stable_of_ne S v
                      (rho.stateBefore S n v) t hbranch]
                    rcases ih' with hsame | ⟨i, hmi, hi, hroot⟩
                    · exact Or.inl hsame
                    · exact Or.inr ⟨i, hmi, Nat.lt_succ_of_lt hi, hroot⟩
                · simp only [NamedWorld.step, Function.update_of_ne (Ne.symm hu)]
                  rcases ih' with hsame | ⟨i, hmi, hi, hroot⟩
                  · exact Or.inl hsame
                  · exact Or.inr ⟨i, hmi, Nat.lt_succ_of_lt hi, hroot⟩
      · have heq : m = n + 1 := by omega
        subst m
        exact Or.inl rfl

end StableRecord
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.StableRecord
#print axioms StableRootAt
#print axioms stateBefore_latest_stable_rootOrigin
#print axioms stateBefore_latest_stable_rootOrigin_after_prefix
end DecoupledConsensusModel.Proofs.StableRecord

end
