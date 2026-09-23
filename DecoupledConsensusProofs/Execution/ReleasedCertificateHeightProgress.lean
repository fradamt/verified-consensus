module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.HealingSurface
public import DecoupledConsensusProofs.Protocol.Handlers.StoreFinality
public import DecoupledConsensusProofs.Protocol.Handlers.JustificationBound

@[expose] public section

/-!
# Released certificates above a boundary are height/filter progress

Once a certificate above `H` is released, its honest release store has a
justification strictly below `h_max`. The release equality therefore places
`h_max` at least two above `H`. This classifies the captured released-above-
`H` arm as height/viability-filter progress, not as a quiet interval.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- An honest store has exposed a viability frontier at least two heights above
`H` no later than `t`. -/
def HonestHeightFilterProgressAboveThrough
    (S : Setup V) (rho : Run V) (H : Height) (t : Time) : Prop :=
  ∃ v, v ∈ rho.honest ∧ ∃ u, u <= t ∧
    H + 2 <= (rho.storeAt S v u).h_max



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
