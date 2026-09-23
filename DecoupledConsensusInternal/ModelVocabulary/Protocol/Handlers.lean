module
public import DecoupledConsensusModel

@[expose] public section

namespace DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Protocol

end
