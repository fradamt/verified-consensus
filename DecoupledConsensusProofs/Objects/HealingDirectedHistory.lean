module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.GoldfishConePersistence
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryCapturedActionCarrier
public import DecoupledConsensusProofs.Execution.RecoveryActionInterval
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryHandoffCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalVoteDuty
public import DecoupledConsensusProofs.Protocol.Grades.ProposalLifecycleCore
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryOpeningFrontierRunBlock
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.GoldfishCone

@[expose] public section

/-!
# Directed Goldfish history in a fixed-root window

This module states the joint vote-head and genuine-confirmation invariant in
the form consumed by the healing debt state. A genuine confirmation at slot
`c` is used as a new Goldfish-cone base. The regime-free cone induction then
puts every later honest vote and every later genuine confirmation above it.
Same-slot confirmations are compatible by the post-GST cross-view theorem.

`HealingJointConeRun` constructs the fixed-root local candidate, root, anchor,
and path inputs for the lifecycle block and every rebased confirmation. The
supplier interface below keeps that construction separate from the generic
history fold.
-/

namespace DecoupledConsensusModel.Protocol

open Internal
open Execution
open Internal.NamedRecoveryRead

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Genuine confirmations from the same post-GST slot are compatible.

The confirmation values use the contract of each confirmation input read.
The two cross views come from the shared post-GST confirmation-time producer. -/
theorem sameSlot_genuine_compatible_after_gst
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) {s : Slot}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {B C : Block V}
    (hB : GenuineConfirmationWith
      (NamedProfile.gradeContract (confirmationInputRead S rho v s).cache)
      S.E S.hc (Proofs.Optimistic.confStore S rho v s) s B)
    (hC : GenuineConfirmationWith
      (NamedProfile.gradeContract (confirmationInputRead S rho w s).cache)
      S.E S.hc (Proofs.Optimistic.confStore S rho w s) s C) :
    Block.compatible B C = true := by
  have hcross := opening_frontier_crossViews_confStore_after_gst
    S adm hv hw hpost hhor
  have hBeligible := hB.genuine
  have hCeligible := hC.genuine
  simp only [confEligible, confCount, confScore, decide_eq_true_eq]
    at hBeligible hCeligible
  rw [← hB.selected, ← hC.selected]
  rw [update_confirmation_with_live_confirmed,
    update_confirmation_with_live_confirmed, if_pos hB.genuine, if_pos hC.genuine]
  exact eligible_compatible (confNumerator S.E (Proofs.Optimistic.confStore S rho v s) s)
    (confNumerator S.E (Proofs.Optimistic.confStore S rho w s) s) hcross.1 hcross.2
    hBeligible hCeligible

#print axioms sameSlot_genuine_compatible_after_gst

end DecoupledConsensusModel.Protocol

end
