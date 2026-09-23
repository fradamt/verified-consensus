module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Assumptions.Recurrence
public import DecoupledConsensusInternal.Healing

@[expose] public section

/-! # Two honest openings followed by a carrier

The final round has honest proposers at its opening and next two slots.
The preceding two rounds need only honest opening proposers.
-/
namespace DecoupledConsensusModel
namespace Internal
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

end Internal
end DecoupledConsensusModel

end
