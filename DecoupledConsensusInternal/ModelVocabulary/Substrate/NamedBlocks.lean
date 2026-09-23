module
public import DecoupledConsensusModel

@[expose] public section

namespace DecoupledConsensusModel.NamedBlock

variable {V : Type}

def parent? : NamedBlock V → Option (NamedBlock V)
  | .genesis => none
  | .node p _ _ _ _ _ _ => some p

def gf_support_votes : NamedBlock V → List (GoldfishVote V)
  | .genesis => []
  | .node _ _ _ _ support _ _ => support

section Ancestry
variable [DecidableEq V]

def compatible (A B : NamedBlock V) : Bool := preceq A B || preceq B A

end Ancestry
end DecoupledConsensusModel.NamedBlock

end
