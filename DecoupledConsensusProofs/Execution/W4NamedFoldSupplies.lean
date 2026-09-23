module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.W4BaseFold
public import DecoupledConsensusProofs.Execution.W4IteratePinFree
public import DecoupledConsensusProofs.Protocol.Schedule.W4ExecState
public import DecoupledConsensusProofs.Protocol.Schedule.W4NamedHonestBoundaryFold

@[expose] public section

/-!
# Separate named fold supplies

The ordinary and ceiling records used by the named fold are different
contracts. This leaf supplies the ceiling record in the ordinary region by
using the fold's event-indexed history to bound the previous action carriers.
The boundary-region ceiling records continue to come from the dedicated
ceiling schedule producers.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.NamedRecoveryRead
open Protocol Proofs.HealingLemmas
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem w4nfs_opening_slot_eq_of_action_eq_confirmation
    (S : Setup V) {r : Round} {s : Slot}
    (h : S.a r = Protocol.confirmation_time S.E s) :
    S.hc.opening_slot r = s := by
  have hslot := congrArg S.E.slotOf
    ((Protocol.a_eq_confirmation_time S.hc S.E r).symm.trans h)
  rw [Proofs.Optimistic.slotOf_confirmation_time,
    Proofs.Optimistic.slotOf_confirmation_time] at hslot
  exact Nat.add_right_cancel hslot

/-- Turn an ordinary action-timing record into the ceiling action-timing
record once the previous-action carrier bound is supplied. -/
private theorem w4nfs_actionCeiling_of_ordinaryTiming
    (S : Setup V) {rho : Run V}
    {t1 : Time} {c : Slot} {Prev : Block V} {r : Round}
    (htiming : MovingSlotActionTiming S rho t1 c)
    (hround : S.hc.round_of (c + 1) = r + 1)
    (hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) Prev) :
    MovingSlotActionCeiling S rho c Prev := by
  intro q hq
  obtain ⟨hqpos, hpost, hcut, _ht1, _hhor, _hbefore⟩ := htiming q hq
  have hopen : S.hc.opening_slot q = c :=
    w4nfs_opening_slot_eq_of_action_eq_confirmation S hq
  have hroundq : S.hc.round_of (c + 1) = q := by
    rw [← hopen]
    exact Proofs.HealingLemmas.round_of_opening_succ S.hc q
  have hqeq : q = r + 1 := hroundq.symm.trans hround
  have hqpred : q - 1 = r := by
    rw [hqeq]
    simp only [Nat.add_sub_cancel]
  refine ⟨hqpos, hpost, hcut, ?_⟩
  simpa only [hqpred] using hupper

/-- Produce the ceiling record at an ordinary fold step. The third field is
the ordinary entered-slot record already carried by the step supply; it is
not inferred from the ceiling record. -/
theorem w4MovingSlotCeilingSupplyAt_of_ordinaryFoldStep
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {t1 : Time} {M0 : Height} {s0 c : Slot} {F : Slot → Block V}
    {End : Block V}
    (hfold : MovingSlotFoldAtN S rho t1 M0 s0 (c + 1) F End)
    (hsupply : MovingSlotStepSupply S rho t1 M0 c) :
    MovingSlotCeilingSupplyAt S rho t1 M0 c (F (c + 1)) := by
  obtain ⟨hdata, htiming, hdataEntered⟩ := hsupply
  obtain ⟨r, hround, ht1, hpostAction, hcut⟩ := hdata.round
  have hactionHor : S.a r ≤ rho.horizon := by
    exact (Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
      ((action_add_delta_le_next_Γ_neg1 S r).trans hcut)
  obtain ⟨EndAt, hhistory, hEnd⟩ := hfold.historyAt
    (c + 1) hfold.base (Nat.le_refl _)
  have hroundPos : 0 < S.hc.round_of (c + 1) := by
    rw [hround]
    exact Nat.succ_pos r
  have hbefore : S.a r < Protocol.proposal_time S.E (c + 1) := by
    have hdelay := Protocol.previous_action_add_delta_le_proposal S
      hroundPos
    have hdelay' : S.a r + S.E.Δ ≤
        Protocol.proposal_time S.E (c + 1) := by
      simpa only [hround, Nat.add_sub_cancel] using hdelay
    exact (Int.lt_add_of_pos_right (S.a r) S.E.Δ_pos).trans_le hdelay'
  have hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) (F (c + 1)) := by
    have hcarriers := hhistory.previousActionCarriersPreceqAtRead S
      adm ht1 hactionHor hbefore (by rfl)
    simpa only [hEnd] using hcarriers
  have htimingC := w4nfs_actionCeiling_of_ordinaryTiming S htiming
    hround hupper
  exact ⟨
    { pos := hdata.pos
      round := ⟨r, hround, hpostAction, hcut, hupper⟩
      postVote := hdata.postVote
      postProp := hdata.postProp
      slotHor := hdata.slotHor },
    htimingC,
    hdataEntered⟩

#print axioms w4MovingSlotCeilingSupplyAt_of_ordinaryFoldStep

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
