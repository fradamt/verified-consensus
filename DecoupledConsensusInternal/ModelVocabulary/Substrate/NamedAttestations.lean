module
public import DecoupledConsensusModel

@[expose] public section

namespace DecoupledConsensusModel.NamedHeightPair

def properTarget : NamedHeightPair → Bool
  | .empty => false
  | .vote _ _ timeout => !timeout

end DecoupledConsensusModel.NamedHeightPair

end
