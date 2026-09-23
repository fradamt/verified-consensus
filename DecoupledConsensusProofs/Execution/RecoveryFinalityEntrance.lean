module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecoveryBoundary
public import DecoupledConsensusProofs.Execution.SeedCommonRootComplement
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Protocol.Handlers.Bridges

@[expose] public section

/-!
# From an in-window finalized-root advance to the causal boundary's finality branch
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]


/-- Every honest store's finalized root, read at any time, is realized by some
processed block's derived state — the finalized-root carrier invariant. -/
theorem exists_carrier_of_F
    (S : Setup V) {rho : Run V} (_adm : Admissible S rho)
    {v : V} (_hv : v ∈ rho.honest) (t : Time) :
    ∃ B ∈ (rho.storeBeforeTime S v t).bodies,
      (Protocol.derive_named S.E S.cfg B).F =
        (rho.storeBeforeTime S v t).core.F := by
  obtain ⟨B, hB, hF, -⟩ :=
    Proofs.Bridges.storeFinalizationOnChain_stateBeforeTime S rho t v
  exact ⟨B, hB, hF⟩



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
