module
public import DecoupledConsensusModel

@[expose] public section

namespace DecoupledConsensusModel.Protocol.GoldfishStore

variable {V : Type} [DecidableEq V]

/-- The proof-free parent-closure predicate for a processed Goldfish tree. -/
def parent_closed (st : GoldfishStore V) : Prop :=
  Block.genesis ∈ st.T ∧ ∀ B ∈ st.T, B.parent? = none ∨ B.parent ∈ st.T

end DecoupledConsensusModel.Protocol.GoldfishStore

end
