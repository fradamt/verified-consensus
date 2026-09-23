module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.W4D3FinalitySpineCompose
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.W4FKRegime
public import DecoupledConsensusProofs.Protocol.ChainState.W4CarrierFirstHalf
public import DecoupledConsensusProofs.Protocol.Schedule.W4CarrierRecord

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # W4 branches d2: consumers for the pins whose producers have available

`W4FKRegimeRun` imports `W4D3FinalitySpineComposeRun` (that is where
`W4CarrierDensityPin` is declared), so the consumers below cannot live in the
compose leaf without an import cycle. They sit in this leaf instead, above both
sides.

Two of the corresponding branch's pins are discharged here, each by one application:

* `W4CanonicalRegimeRoundPin`, from the corresponding branch's item 2
  (`W4FKRegimeRun.lean:1252`), leaving the moving floor's activity at the
  carrier's G2-domain read as the residual;
* `W4CarrierFirstHalfPin`, from the corresponding branch's export
  (`W4CarrierFirstHalfRun.lean:1079`), leaving that same domain-read activity,
  item 4a's checkpoint-ready branch and the action-head cone.

The post-GST bound at the recovery round stays outside both pins, as: the
producers take it at their own call sites and
`commonFinalityAboveFrontier_of_openingCarrierRecurrence_of_pins` carries it as
`hpostBoundary`. -/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]







/-- The prepared companion of `W4CarrierDensityPinAt`. -/
def W4CarrierDensityPinAtPrepared (S : Setup V) : Prop :=
  ∀ (rho : Run V) (q0 : Round),
    Admissible S rho → HonestCommittees S rho.honest →
    BelowOneThird S rho.honest →
    CanonicalSuffixExecutionPrepared S rho q0 →
    (∀ r : Round, q0 + 1 < r →
      healingBoundaryTime S q0 <
        Protocol.proposal_time S.E (S.hc.opening_slot r)) →
    MovingChainAtCarrierFrom S rho q0 →
    S.E.t_GST ≤ S.a q0 →
    CanonicalCarrierDensityFromPrepared S rho q0


/-- Closed pin-free from the corresponding branch's prepared producer (3eefd837). -/
theorem w4CarrierDensityPinAtPrepared_landed (S : Setup V) :
    W4CarrierDensityPinAtPrepared S :=
  fun _rho _q0 adm hcom hbot hexec hafterAll hchain hpost =>
    canonicalCarrierDensityFromPrepared_of_movingChain_named S adm hcom hbot
      hexec hafterAll hchain hpost



/-! ## Axiom roster. Every public theorem of this file. Each must report a
subset of `propext`, `Classical.choice`, `Quot.sound` and nothing else. A
theorem reporting NO axioms is hollow: it means an import's olean lacked a name
and Lean recovered silently, which still exits zero. -/

#print axioms w4CarrierDensityPinAtPrepared_landed


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
