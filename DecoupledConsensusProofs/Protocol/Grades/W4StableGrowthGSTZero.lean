module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Liveness
public import DecoupledConsensusProofs.Protocol.Handlers.Bridges
public import DecoupledConsensusProofs.Generic.SlotFreshness
public import DecoupledConsensusProofs.Protocol.Handlers.ConfirmationRecordOrigin
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Grades.Interpolation
public import DecoupledConsensusProofs.Execution.GSTZeroSafetyClosedNamed
public import DecoupledConsensusProofs.Generic.StableRecordSafetyAssembly
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryProposalConfirmationRead
public import DecoupledConsensusProofs.Protocol.Schedule.PostHealingContinuation
public import DecoupledConsensusProofs.Protocol.Schedule.W4StableWriteDuty
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.PostGainOpeningStableWrite
public import DecoupledConsensusProofs.Protocol.ChainState.FGRootWitness
public import DecoupledConsensusProofs.Protocol.Grades.WeakFiniteWindow
public import DecoupledConsensusProofs.Protocol.Grades.RelativeCrossReader
public import DecoupledConsensusProofs.Protocol.Grades.RelativeOneChain
public import DecoupledConsensusProofs.Protocol.Grades.RoundVoterTransportTwoCutoff
public import DecoupledConsensusProofs.Protocol.Grades.Inclusions
public import DecoupledConsensusProofs.Execution.EmissionShape
public import DecoupledConsensusProofs.Execution.HealthyLocalFacts
public import DecoupledConsensusProofs.Execution.WeakGenesisGSTZeroActionSources

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs

open Internal Execution Statements
open Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Timing of the confirmation duty that writes the stable record -/

/-- The confirmation duty of round `r`: the support cutoff of its opening slot.
A local copy of the red growth module's `stableRecordDutyTime`. -/
def w4StableDutyTime (S : Setup V) (r : Round) : Time :=
  Protocol.support_cutoff S.E (S.hc.opening_slot r)



/-! ## Slot freshness at an inclusive read -/

private theorem w4_stateAt_eq_stateBefore_le (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) (t : Time) :
    ∃ n : Nat, Run.stateAt S rho t = rho.stateBefore S n ∧
      ∀ (j : Nat) (e : Event V), j < n → rho.events[j]? = some e → e.time ≤ t :=
  (Proofs.Bridges.filtered_fold_eq_stateBefore S sch
    (p := fun e => decide (e.time ≤ t))
    (fun e f hk hf => by
      simp only [decide_eq_true_eq] at hf ⊢
      exact le_trans (Proofs.Bridges.time_le_of_key_le hk) hf)).imp fun _ h =>
    ⟨h.1, fun j e hj hget => by simpa using h.2 j e hj hget⟩

/-- Inclusive-read twin of `Proofs.NamedSlotFreshness.block_slot_lt_of_mem_before_proposal`:
a block a store holds at a time before a proposal instant sits at a strictly
smaller slot. -/
theorem w4_block_slot_lt_of_mem_storeAt
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} {s : Slot} {t : Time} (hs : 0 < s)
    (ht : t < Protocol.proposal_time S.E s) {C : Block V}
    (hC : C ∈ (rho.storeAt S v t).T) : C.slot < s := by
  obtain ⟨n, hn, hbefore⟩ :=
    w4_stateAt_eq_stateBefore_le S adm.toNamedScheduleWellFormed t
  have hCn : C ∈ (rho.stateBefore S n v).st.core.T := by
    have hnv : NamedRun.readAt S rho t v = rho.stateBefore S n v := congrFun hn v
    have hC' : C ∈ (NamedRun.readAt S rho t v).st.core.T := hC
    rwa [hnv] at hC'
  obtain ⟨D, hD, hDe⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n v hCn
  have hprocessed : Object.processed (rho.stateBefore S n v).st (.block D) = true := by
    simp only [NamedReceipt.processed, decide_eq_true_eq]
    exact hD
  rcases Protocol.acceptsAt_block_of_processed S rho v n D hprocessed with
      hgen | hacc
  · subst D
    simp only [NamedBlock.erase] at hDe
    subst C
    simpa using hs
  · obtain ⟨i, hin, atime, haccepts⟩ := hacc
    obtain ⟨-, e, he, -, het⟩ := haccepts.1
    have hatime : atime < Protocol.proposal_time S.E s := by
      rw [← het]
      exact lt_of_le_of_lt (hbefore i e hin he) ht
    by_contra hnot
    have hsC : s ≤ D.erase.slot := by rw [hDe]; exact Nat.le_of_not_gt hnot
    have hmono := Protocol.proposal_time_mono S.E hsC
    have hCtime :=
      Proofs.NamedSlotFreshness.proposal_time_le_of_acceptsAt_block S adm haccepts
    exact (not_lt_of_ge (le_trans hmono hCtime)) hatime

#print axioms w4_block_slot_lt_of_mem_storeAt

/-! ## The strict clause -/





/-! ## Retention of the write -/










/-! ## Reducing the write to the round's own frozen G2 slot -/

theorem w4StableDutyTime_eq_dutyTime (S : Setup V) (r : Round) :
    w4StableDutyTime S r = W4StableWrite.dutyTime S r := rfl





/-! ## The remaining obligation: the round's stable write -/


/-! ## The public GST-zero branch -/



/-! ## The residual obligation, stated at the frozen G2 slot -/




















end Proofs
end DecoupledConsensusModel

end
