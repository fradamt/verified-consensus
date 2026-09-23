module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.UserConfirmationHistory
public import DecoupledConsensusProofs.Protocol.Handlers.FinalityMonotoneCore
public import DecoupledConsensusProofs.Protocol.Schedule.CandidateSafety
public import DecoupledConsensusProofs.Protocol.Handlers.BlockAdmission
public import DecoupledConsensusProofs.Generic.EvaluationStore
public import DecoupledConsensusProofs.Protocol.Handlers.HonestProposalAdmission
public import DecoupledConsensusProofs.Protocol.Handlers.AcceptanceTiming
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Adoption
public import DecoupledConsensusProofs.Generic.GSTZeroHealthy
public import DecoupledConsensusProofs.Protocol.Handlers.GoldfishVotePool
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.VoteViewValidity

@[expose] public section



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution
open Internal.NamedRecoveryRead
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]





/-! ## Directed protocol selections and user candidates -/

/-- A tick that is not a confirmation tick leaves `latest_confirmed` unchanged.
Proposal, vote, and round-action subduties do not write this field. -/
theorem on_tick_emit_latest_of_ne
    (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time)
    (h : ¬ (0 < S.E.slotOf t ∧
      t = Protocol.support_cutoff S.E (S.E.slotOf t))) :
    (on_tick_emit S v n t).1.st.latest_confirmed = n.st.latest_confirmed :=
  Proofs.UserConfirmation.on_tick_emit_latest_of_ne S v n t h

/-- The value a Section 7 confirmation duty writes from one prepared state:
the guarded selection of the confirmation read's own contract. -/
abbrev confirmationWrite (S : Setup V) (n : NamedNodeState V) (time : Time) :
    Block V :=
  (Protocol.NamedDuties.update_confirmation_with
    (NamedProfile.gradeContract
      (NamedActionReads.confirmationReadFrom S n time).cache)
    S.E S.hc (NamedActionReads.confirmationReadFrom S n time).st
    (S.E.slotOf time - 1)).live_confirmed

/-- The value a Section 7 confirmation duty actually writes at one indexed
tick. -/
abbrev confirmationWriteAt (S : Setup V) (rho : Run V) (v : V) (i : Nat)
    (time : Time) : Block V :=
  confirmationWrite S (rho.stateBefore S i v) time

/-- Every confirmation selection made by node `v` before event prefix `n`
precedes `B`.

The selected value is read from the exact prepared read the named tick uses,
under that read's own contract. The definition does not classify it as genuine
or fallback, so both branches are part of the invariant. -/
def PriorSelectionsPreceqAtIndex
    (S : Setup V) (rho : Run V) (v : V) (n : Nat) (B : Block V) : Prop :=
  ∀ (i : Nat) (t : Time), i < n →
    rho.events[i]? = some (Event.tick v t) →
    0 < S.E.slotOf t →
    t = Protocol.support_cutoff S.E (S.E.slotOf t) →
    Block.Preceq (confirmationWriteAt S rho v i t) B

/-- The mutable `live_confirmed` field is below `B` after a prefix when every
confirmation selection in that prefix is below `B`.

The confirmation case does not use the induction hypothesis: `live_confirmed`
is replaced directly by the current selection. -/
theorem stateBefore_live_preceq_of_priorSelections
    (S : Setup V) (rho : Run V) (v : V) (B : Block V) :
    ∀ n : Nat, PriorSelectionsPreceqAtIndex S rho v n B →
      Block.Preceq (rho.stateBefore S n v).st.live_confirmed B := by
  intro n
  induction n with
  | zero =>
      intro _
      exact Protocol.preceq_genesis B
  | succ n ih =>
      intro hprior
      have hpriorN : PriorSelectionsPreceqAtIndex S rho v n B := by
        intro i t hi
        exact hprior i t (Nat.lt_succ_of_lt hi)
      have hIH := ih hpriorN
      show Block.Preceq (NamedRun.stateBefore S rho (n + 1) v).st.live_confirmed B
      rw [Proofs.NamedRuntime.stateBefore_succ]
      cases hn : rho.events[n]? with
      | none => simpa using hIH
      | some e =>
          simp only [Option.toList, List.foldl_cons, List.foldl_nil]
          cases e with
          | deliver u o t =>
              by_cases hu : v = u
              · subst u
                simp only [NamedWorld.step, Function.update_self]
                rw [Proofs.Optimistic.process_live_confirmed]
                exact hIH
              · simp only [NamedWorld.step]
                rw [Function.update_of_ne hu]
                exact hIH
          | tick u t =>
              by_cases hu : v = u
              · subst u
                simp only [NamedWorld.step, Function.update_self]
                by_cases hbranch : 0 < S.E.slotOf t ∧
                    t = Protocol.support_cutoff S.E (S.E.slotOf t)
                · obtain ⟨hpos, ht⟩ := hbranch
                  have hout := Proofs.Optimistic.on_tick_emit_confirmation S v
                    (rho.stateBefore S n v) (S.E.slotOf t) hpos
                  rw [← ht] at hout
                  rw [hout]
                  exact hprior n t (Nat.lt_succ_self n) hn hpos ht
                · rw [Proofs.Optimistic.on_tick_emit_live_confirmed_of_ne S v
                    (rho.stateBefore S n v) t hbranch]
                  exact hIH
              · simp only [NamedWorld.step]
                rw [Function.update_of_ne hu]
                exact hIH






/-! ## Actual selection events and global confirmation safety -/

/-- `C` is the actual value selected by one node's Section 7 confirmation
branch at event `i`.

This is not restricted to genuine confirmations. When the walk does not pass
its gate, `C` is the contract's own fallback. -/
def ConfirmationSelectionAt
    (S : Setup V) (rho : Run V) (v : V) (i : Nat) (C : Block V) : Prop :=
  ∃ time : Time,
    rho.events[i]? = some (Event.tick v time) ∧
      0 < S.E.slotOf time ∧
      time = Protocol.support_cutoff S.E (S.E.slotOf time) ∧
      confirmationWriteAt S rho v i time = C


/-- Core-admissibility twin of `confirmationSelectionAt_slot`. -/
theorem confirmationSelectionAt_slot_core
    (S : Setup V) {rho : Run V} (core : Proofs.AdmissibleCore S rho)
    {v : V} {i : Nat} {C : Block V}
    (hsel : ConfirmationSelectionAt S rho v i C) :
    ∃ s : Slot,
      rho.events[i]? = some
        (Event.tick v (Protocol.confirmation_time S.E s)) ∧
      confirmationWrite S
        (rho.stateBeforeTime S (Protocol.confirmation_time S.E s) v)
        (Protocol.confirmation_time S.E s) = C ∧
      Protocol.confirmation_time S.E s ≤ rho.horizon := by
  rcases hsel with ⟨time, hi, hpos, htime, hC⟩
  let k := S.E.slotOf time
  let s := k - 1
  have hkpos : 0 < k := by simpa only [k] using hpos
  have hk : s + 1 = k := by
    dsimp only [s, k]
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hkpos))
  have hconfirmation : time = Protocol.confirmation_time S.E s := by
    rw [Protocol.confirmation_time_eq_support_cutoff_succ S.E s, hk]
    exact htime
  have hstate := Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
    S core.toNamedScheduleWellFormed hi
  refine ⟨s, ?_, ?_, ?_⟩
  · simpa only [hconfirmation] using hi
  · have hC' : confirmationWrite S
        (rho.stateBeforeTime S time v) time = C := by
      rw [← hstate]
      exact hC
    rw [hconfirmation] at hC'
    exact hC'
  · have hhor := (core.toNamedScheduleWellFormed.in_horizon
      (Event.tick v time) (List.mem_of_getElem? hi)).2
    simpa only [Event.time, hconfirmation] using hhor

#print axioms confirmationSelectionAt_slot_core












/-! ## Pairwise record compatibility -/




/-! ## Event-indexed canonical history and receiver admission -/



















/-! ## Receiver-side admission from canonical history -/






/-! ## Mutual event/slot producer interface -/






end Protocol
end DecoupledConsensusModel

end
