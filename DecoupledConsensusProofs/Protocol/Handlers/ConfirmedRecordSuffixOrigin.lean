module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.ConfirmationRecordOrigin

@[expose] public section

/-! # Confirmation-record origins after an arbitrary prefix

The floor can keep the prefix record, return the prefix's stable record, write
a later user selection, or write a later stable root. -/

namespace DecoupledConsensusModel
namespace Proofs
namespace ConfirmationOrigin

open Internal Execution Internal.NamedRecoveryRead Protocol Proofs.Optimistic
open StableRecord NamedOutageClosure

variable {V : Type} [DecidableEq V] [Fintype V]

set_option maxHeartbeats 1000000 in
/-- Every confirmation value after a prefix is unchanged from the prefix,
equal to the prefix's stable record, a later user selection, or a later stable
root. -/
theorem stateBefore_latest_confirmed_origin_after_prefix
    (S : Setup V) (rho : Run V) (v : V) :
    ∀ n m : Nat, m ≤ n →
      (rho.stateBefore S n v).st.latest_confirmed =
          (rho.stateBefore S m v).st.latest_confirmed ∨
        (rho.stateBefore S n v).st.latest_confirmed =
          (rho.stateBefore S m v).st.latest_stable ∨
        (∃ i C, m ≤ i ∧ i < n ∧ UserConfirmationSelectionAt S rho v i C ∧
          (rho.stateBefore S n v).st.latest_confirmed = C) ∨
        (∃ i, m ≤ i ∧ i < n ∧ StableRecord.StableRootAt S rho v i
          (rho.stateBefore S n v).st.latest_confirmed) := by
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
            rcases hcases with hkeep | hwalk |
                ⟨select, hmode, helig, B, hsel, hB⟩
            · rw [hkeep]
              rcases ih' with
                hsame | hstable0 | ⟨i, C, hmi, hi, hsel', hvalue⟩ | ⟨i, hmi, hi, hroot⟩
              · exact Or.inl hsame
              · exact Or.inr (Or.inl hstable0)
              · exact Or.inr (Or.inr (Or.inl
                  ⟨i, C, hmi, Nat.lt_succ_of_lt hi, hsel', hvalue⟩))
              · exact Or.inr (Or.inr (Or.inr
                  ⟨i, hmi, Nat.lt_succ_of_lt hi, hroot⟩))
            · rw [hwalk]
              exact Or.inr (Or.inr (Or.inl
                ⟨n, _, hmn', Nat.lt_succ_self n,
                  ⟨t, hn, hpos, ht, Or.inl rfl⟩, rfl⟩))
            · rw [hB]
              refine Or.inr (Or.inr (Or.inl
                ⟨n, B, hmn', Nat.lt_succ_self n,
                  ⟨t, hn, hpos, ht, Or.inr ?_⟩, rfl⟩))
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
            · rcases ih' with
                hsame | hstable0 | ⟨i, C, hmi, hi, hsel', hvalue⟩ | ⟨i, hmi, hi, hroot⟩
              · exact Or.inl hsame
              · exact Or.inr (Or.inl hstable0)
              · exact Or.inr (Or.inr (Or.inl
                  ⟨i, C, hmi, Nat.lt_succ_of_lt hi, hsel', hvalue⟩))
              · exact Or.inr (Or.inr (Or.inr
                  ⟨i, hmi, Nat.lt_succ_of_lt hi, hroot⟩))
            · rw [← hstable]
              rcases StableRecord.stateBefore_latest_stable_rootOrigin_after_prefix
                  S rho v (n + 1) m (hmn'.trans (Nat.le_succ n)) with
                hsame | ⟨i, hmi, hi, hroot⟩
              · exact Or.inr (Or.inl hsame)
              · exact Or.inr (Or.inr (Or.inr ⟨i, hmi, hi, hroot⟩))
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
                        (NamedOutageClosure.node_process_latest S
                          (rho.stateBefore S n v) o)
                    · simp only [NamedWorld.step,
                        Function.update_of_ne (Ne.symm hu)]
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
                    · simp only [NamedWorld.step,
                        Function.update_of_ne (Ne.symm hu)]
          rw [hstep]
          rcases ih' with
            hsame | hstable0 | ⟨i, C, hmi, hi, hsel, hvalue⟩ | ⟨i, hmi, hi, hroot⟩
          · exact Or.inl hsame
          · exact Or.inr (Or.inl hstable0)
          · exact Or.inr (Or.inr (Or.inl
              ⟨i, C, hmi, Nat.lt_succ_of_lt hi, hsel, hvalue⟩))
          · exact Or.inr (Or.inr (Or.inr
              ⟨i, hmi, Nat.lt_succ_of_lt hi, hroot⟩))
      · have heq : m = n + 1 := by omega
        subst m
        exact Or.inl rfl

end ConfirmationOrigin
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.ConfirmationOrigin
#print axioms stateBefore_latest_confirmed_origin_after_prefix
end DecoupledConsensusModel.Proofs.ConfirmationOrigin

end
