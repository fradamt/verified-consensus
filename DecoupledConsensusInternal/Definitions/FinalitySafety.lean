module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Definitions.FinalitySafety

@[expose] public section

/-! Proof-side adapters for the public finality-safety building blocks. -/
namespace DecoupledConsensusModel.Internal
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Project the narrow finality premises from non-network execution validity. -/
def FinalityExecution.of_executionValid {S : Setup V} {rho : Run V}
    (execution : ExecutionValid S rho) : FinalityExecution S rho :=
  { sorted := execution.toNamedScheduleWellFormed.sorted
    rootCollisionFree := execution.toNamedRootCollisionFree }

end DecoupledConsensusModel.Internal

end
