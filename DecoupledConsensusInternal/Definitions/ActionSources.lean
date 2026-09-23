module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Definitions.ActionSources

@[expose] public section

/-! Proof-side action-source predicates outside `Statements.Consensus`. -/
namespace DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-- All honest Section 7 action carriers extend one common block. -/
def ActionCarriersCover (S : Setup V) (rho : Run V) (r : Round)
    (P : Block V) : Prop :=
  ∀ v ∈ rho.honest, Block.Preceq P (actionSGBlockAt S rho v r)

end DecoupledConsensusModel.Proofs.HealingSurface

end
