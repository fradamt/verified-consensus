module
public import DecoupledConsensusModel

@[expose] public section

namespace DecoupledConsensusModel.Block

variable {V : Type} [DecidableEq V]

/-- §1 two blocks conflict when neither is an ancestor of the other. -/
def conflicts (B C : Block V) : Bool :=
  !compatible B C

end DecoupledConsensusModel.Block

end
