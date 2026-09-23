module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.HandoverHeight
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalAdoptionNamedClosed

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Direct named handover heights -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

theorem handoverHeights_of_carrier_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {base m : Round}
    (hbaseLo : fgSafetyProgressDeadline S rho rGST gap delayExtra +
      2 * progressLag' gap delayExtra + 1 ≤ base)
    (hcutm : base + S.hc.η_SG ≤ m)
    (hcarrier : ProposerCarrierAt S rho m)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot m) ≤ rho.horizon)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot m) = some P) :
    HandoverHeights S rho base
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 1)
      (S.hc.opening_slot m) P :=
  handoverHeights_of_carrier_named_of_pins
    exists_namedCommonPreviousHeadAncestor_in_frontierBand_through_confirmation_after_GST
    honestProposal_voterHeadAt_eq_after_SG_healing_named
    S adm hcom hbelow hrec hdelay hpost hbaseLo hcutm hcarrier hhor hP

#print axioms handoverHeights_of_carrier_named

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
