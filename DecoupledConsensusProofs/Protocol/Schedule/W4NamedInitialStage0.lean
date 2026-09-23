module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.W4NamedBoundaryStage0

@[expose] public section

/-!
# The initial named fold from stage-0 data

The selected boundary has one initial fold. This leaf performs the required
honest/Byzantine proposer split and leaves the later slot iteration to the
named execution leaf.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.NamedRecoveryRead
open Protocol Proofs.HealingLemmas
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

/-- The initial named fold from the selected handoff and boundary. -/
theorem w4MovingSlotFoldAtN_boundary_initial_stage0
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {rGST gap q : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    (hqLate : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ q)
    {D : NamedBlock V} {carrier : V} {M0 : Height}
    (hhandoff : HealedTwoSlotHandoffPrepared S rho q D.erase carrier)
    (hboundary : W4NamedHandoffBoundaryCore S rho q
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0 D)
    (hbaseTiming :
      0 < S.hc.round_of (S.hc.opening_slot q + 3) ∧
      S.E.t_GST ≤ S.a
        (S.hc.round_of (S.hc.opening_slot q + 3) - 1) ∧
      Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤
        rho.horizon) :
    ∃ F : Slot → Block V, ∃ End : Block V,
      MovingSlotFoldAtN S rho
        (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
        (S.hc.opening_slot q + 3) (S.hc.opening_slot q + 3) F End ∧
      F (S.hc.opening_slot q + 3) = D.erase := by
  by_cases hprop : S.E.proposer (S.hc.opening_slot q + 3) ∈ rho.honest
  · exact w4MovingSlotFoldAtN_boundary_honest_stage0 S adm hcom hfb
      hrec hdelay hpost hqLate hhandoff hboundary hbaseTiming hprop
  · exact w4MovingSlotFoldAtN_boundary_byzantine S adm hcom hfb hhandoff
      hboundary hbaseTiming hprop

#print axioms w4MovingSlotFoldAtN_boundary_initial_stage0

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
