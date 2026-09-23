module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Safety

@[expose] public section

/-!
# Shared doc1 store-finality properties

These predicates state the store properties that the rewrite shares with
doc1. They use the rewrite's cumulative store and derived chain states.

The viable-tree statement is intentionally about a viable **descendant** of a
historical finalized block. `V_tree st` contains only descendants of the
current `st.F`. Therefore, a historical block leaves the set when `st.F`
advances strictly above it, although every current viable block still descends
from that historical block.
-/

namespace DecoupledConsensusModel
namespace Internal

open Protocol (HeightConfig)

variable {V : Type} [DecidableEq V] [Fintype V]


/-- A derived chain state justifies `T` at height `h`. This is the
justification analogue of `FinalizedAt`. -/
def JustifiedAt (E : Env V) (cfg : HeightConfig) (B T : Block V)
    (h : Height) : Prop :=
  (derived_state E cfg B).J = T ∧ (derived_state E cfg B).h_j = h

/-- B13: every justification carried by a processed block is at or below the
store's current justification height. -/
def NoHighJustifications (E : Env V) (cfg : HeightConfig)
    (st : Protocol.Store V) : Prop :=
  ∀ B ∈ st.T, (derived_state E cfg B).h_j ≤ st.h_j

/-- The store's current justification is strictly below its running maximum
chain-state height. -/
def JustificationBelowMax (st : Protocol.Store V) : Prop :=
  st.h_j < st.h_max

/-- Corrected B9: the current viable tree contains a descendant of the named
historical finalized block. -/
def HasViableDescendant (st : Protocol.Store V) (F : Block V) : Prop :=
  ∃ D ∈ Protocol.V_tree st.toHealing.toFG, Block.Preceq F D

end Internal
end DecoupledConsensusModel

end
