module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Derived
public import DecoupledConsensusModel.Protocol.Handlers

@[expose] public section

/-!
# Store predicates and retained local properties

These proof-free predicates describe store fields and local transition facts.
The former erased absolute-duty reachability relations are not part of the
selected named protocol.
-/

namespace DecoupledConsensusModel
namespace Internal

open Protocol (HeightConfig)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The finalized block precedes the justified block. -/
def FinalizedPrecedesJustified (st : Protocol.Store V) : Prop :=
  st.F ⪯ st.J

/-- The derived finalized height is at most the justification height. -/
def FinalityHeightsOrdered (st : Protocol.Store V) : Prop :=
  st.finalized_height ≤ st.h_j

/-- The finalized block is in the processed tree. -/
def FinalizedInTree (st : Protocol.Store V) : Prop :=
  st.F ∈ st.T

/-- The processed tree is parent closed. -/
def ParentClosed (st : Protocol.Store V) : Prop :=
  Protocol.GoldfishStore.parent_closed st.toHealing.toFG.toSG.toGoldfishStore

/-- The retained store invariant bundle. -/
def StoreInvariants (st : Protocol.Store V) : Prop :=
  FinalizedPrecedesJustified st ∧ FinalizedInTree st

/-- Parent closure is preserved by an admitted block transition. -/
def ParentClosedStep (E : Env V) (cfg : HeightConfig) : Prop :=
  ∀ (st : Protocol.Store V) (B : Block V), ParentClosed st →
    (B.parent? = none ∨ B.parent ∈ st.T) →
    ParentClosed (Protocol.on_block E cfg st B)

/-- The derived chain-state slot agrees with the latest block slot. -/
def ChainStateSlotIsLatestSlot (E : Env V) (cfg : HeightConfig) : Prop :=
  ∀ B : Block V, (derived_state E cfg B).s = (derived_state E cfg B).L.slot

end Internal
end DecoupledConsensusModel

end
