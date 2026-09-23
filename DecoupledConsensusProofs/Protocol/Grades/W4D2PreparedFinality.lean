module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.W4D2OpeningCarrierFinality
public import DecoupledConsensusProofs.Execution.W4PreparedCarrierSelection
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.W4D2PreparedRegime
public import DecoupledConsensusProofs.Protocol.ChainState.W4CarrierFirstHalf

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # D2 finality over the prepared density interface
Additive twin of
`commonFinalityAboveFrontier_of_openingCarrierRecurrence_of_pins`. The only
record-level change is `CanonicalCarrierDensityFrom` to
`CanonicalCarrierDensityFromPrepared`; the carrier-pair selection call uses
the available prepared theorem. All other pins and the conclusion stay exactly
as in D2. The execution core pin remains an explicit D2 input because this
leaf only removes the density record's default-contract execution field.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Selected-opening first-half callback. The named previous opening and its
prepared live/anchor facts are passed at the selected carrier; the height
case is split by the callback, not hidden in a global pin. -/
def W4PreparedSelectedFirstHalfAt (S : Setup V) (rho : Run V) (q0 : Round) : Prop :=
  ∀ (r : Round) (C End : Block V),
    q0 + 2 < r → ProposerOpeningCarrierAt S rho r →
    CanonicalRegimeRoundAt S rho q0 r →
    MovingChainAtCarrierFor S rho q0 r C End →
    NamedGradeFormsAt S rho r C →
    ¬ LostRoundAt S rho r → ¬ LostRoundAt S rho (r - 1) →
    healingBoundaryTime S q0 <
      Protocol.proposal_time S.E (S.hc.opening_slot (r - 1)) →
    S.E.t_GST ≤ S.a (r - 1) →
    S.E.t_GST ≤ Protocol.proposal_time S.E (S.hc.opening_slot r) →
    honestHMaxAt S rho (S.a q0) < carrierOpeningHeight S rho r →
    (∀ P0 : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r) = some P0 →
      (Protocol.derive_named S.E S.cfg P0).nj = false) →
    (∀ v ∈ rho.honest, ∀ w ∈ rho.honest,
      (actionStoreAt S rho v (r - 1)).st.core.live_confirmed =
        (actionStoreAt S rho w (r - 1)).st.core.live_confirmed) →
    {Pprev P0 P1 : NamedBlock V} →
    proposedBlockAt S rho (S.hc.opening_slot (r - 1)) = some Pprev →
    RunBlock S rho Pprev →
    proposedBlockAt S rho (S.hc.opening_slot r) = some P0 →
    proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1 →
    NamedBlock.parent? P1 = some P0 → RunBlock S rho P1 →
    S.a (r - 1) ≤ rho.horizon →
    S.E.proposer (S.hc.opening_slot (r - 1)) ∈ rho.honest →
    ((Protocol.derive_named S.E S.cfg Pprev).h <
      (Protocol.derive_named S.E S.cfg P0).h ∨
      (Protocol.derive_named S.E S.cfg P0).h ≤
        (Protocol.derive_named S.E S.cfg Pprev).h) →
    (∀ v ∈ rho.honest,
      (actionStoreAt S rho v (r - 1)).st.core.live_confirmed = Pprev.erase) →
    (∀ v ∈ rho.honest,
      Block.Preceq
        (PhaseGrades.nodeAnchor S (actionReadAt S rho v (r - 1)) (r - 1))
        Pprev.erase) →
    (∀ v ∈ rho.honest,
      actionFGSource S (actionReadAt S rho v (r - 1)) = some Pprev.erase) →
    CarrierFinalityFirstHalfAt S rho r C



/-! The same conclusion with the field-level execution core and regime pin. -/
/-! The same conclusion with the field-level execution core and regime pin. -/



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
