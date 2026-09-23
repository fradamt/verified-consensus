module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.MovingChainCeiling
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.ValidatorClient.MovingChainRow

@[expose] public section

/-!
# The boundary's confirmation-side data, from the two-slot handoff

The fold starts at slot `opening q + 3`, whose bootstrap cutoff is the
confirmation instant of slot `opening q + 1`. `MovingSlotBoundaryConfFacts`
collects the four facts the moving chain reads there. All four come from the
healing exit, `Protocol.HealedTwoSlotHandoff S rho q D carrier`:

* `confirmed` is its `boundary_outputs` field at the opening-plus-one slot,
  because a genuine confirmation is exactly the selected `live_confirmed`;
* `carrier` and `outputs` are VACUOUS: no round action fires at that instant,
  since `a q' = confirmation_time (opening q')` and `opening q' = opening q + 1`
  is impossible when `R ≥ 2`;
* `anchorCompatible` is the genuine confirmation's own anchor floor.

The slot-`(opening q + 2)` honest vote cone that the base also needs is the
handoff's `honestVotesCone_two_after`, so nothing outside the healing exit is
read here.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

-- moved from DecoupledConsensusProofs/Availability/GenuineAnchorFloorRun.lean (C1)

private theorem nat_not_add_two_le_add_one (a : Nat) : ¬ (a + 2 ≤ a + 1) := by
  omega

/-- No round's opening slot is the successor of another's, because `R ≥ 2`. -/
theorem openingSlot_ne_openingSlot_succ
    (S : Setup V) (q q' : Round) :
    S.hc.opening_slot q' ≠ S.hc.opening_slot q + 1 := by
  intro heq
  simp only [Protocol.HealConfig.opening_slot] at heq
  have hlt : q * S.hc.R < q' * S.hc.R := by
    rw [heq]
    exact Nat.lt_succ_self _
  have hq : q < q' := by
    by_contra hnot
    exact absurd (Nat.mul_le_mul_right S.hc.R (Nat.le_of_not_lt hnot))
      (not_le_of_gt hlt)
  have hstep : q * S.hc.R + 2 ≤ q' * S.hc.R := by
    calc q * S.hc.R + 2 ≤ q * S.hc.R + S.hc.R := by
          exact Nat.add_le_add_left S.hc.R_ge_two _
      _ = (q + 1) * S.hc.R := by rw [Nat.succ_mul]
      _ ≤ q' * S.hc.R := Nat.mul_le_mul_right S.hc.R hq
  rw [heq] at hstep
  exact nat_not_add_two_le_add_one (q * S.hc.R) hstep

/-- No round action fires at the confirmation instant of the opening-plus-one
slot. -/
theorem no_action_at_openingSucc_confirmation
    (S : Setup V) (q q' : Round) :
    S.a q' ≠ Protocol.confirmation_time S.E (S.hc.opening_slot q + 1) := by
  intro heq
  have hslot := congrArg S.E.slotOf
    ((Protocol.a_eq_confirmation_time S.hc S.E q').symm.trans heq)
  rw [Proofs.Optimistic.slotOf_confirmation_time,
    Proofs.Optimistic.slotOf_confirmation_time] at hslot
  exact openingSlot_ne_openingSlot_succ S q q' (Nat.add_right_cancel hslot)


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
