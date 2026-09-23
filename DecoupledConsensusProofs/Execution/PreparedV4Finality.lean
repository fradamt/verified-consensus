module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.HandoverPreparedV4
public import DecoupledConsensusProofs.Execution.HandoverLegacyFinality

@[expose] public section

/-! # Accountable finality input for the prepared V4 handover -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The V4 run block and its strict named-height increase discharge the previous
finalized-root read obligation. -/
theorem SettledBootstrapPreparedV4.finalizedRootsBelowAtRead_of_accountable
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hsb : SlashableBound S rho)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hheight : cap < (Protocol.derive_named S.E S.cfg P).h) :
    FinalizedRootsBelowAtRead S rho cap P.erase :=
  Handover.finalizedRootsBelowAtRead_of_accountable
    S adm hsb hboot.runBlock hheight

#print axioms SettledBootstrapPreparedV4.finalizedRootsBelowAtRead_of_accountable

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
