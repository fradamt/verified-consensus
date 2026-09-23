module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.NamedEvidence
public import DecoupledConsensusModel.Protocol.Handlers

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Named twins of the derived-state invariants 

the prior invariants `DerivedStateAgrees`, `JustifiedAt`,
`NoHighJustifications` and `ChainStateSlotIsLatestSlot` (Props/Derived,
Props/StoreFinality, Props/Invariants) recompute chain state with the
erased `derived_state`, which folds height-only rows. The named runtime
caches `derive_named`, which folds the targeted rows, and the two agree
only on timeout-free chains (Q-E1). Every consumer in the height cone
therefore reads these twins; the erased forms stay only for the
accountability views, where erasure is an evidence projection.

`NamedDerivedStateAgrees` is byte-for-byte the runtime's `DerivedView`
clause of the named coherence invariant (`Proofs.NamedStore.Coherent`),
restated here so the statements layer does not import the proofs layer.
-/


namespace DecoupledConsensusModel.Internal
open Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Twin of `DerivedStateAgrees`: every held body's cached chain state is
its named derivation (the `DerivedView` clause of named coherence). -/
def NamedDerivedStateAgrees (E : Env V) (cfg : HeightConfig)
    (st : Protocol.NamedStore V) : Prop :=
  ∀ B ∈ st.bodies, st.core.σ B.erase = derive_named E cfg B

/-- Twin of `JustifiedAt`: the named derivation of `C` justifies `T` at
height `h`. The checkpoint stays an erased block, as in `NamedFinalizedAt`. -/
def NamedJustifiedAt (E : Env V) (cfg : HeightConfig) (C : NamedBlock V) (T : Block V)
    (h : Height) : Prop :=
  (derive_named E cfg C).J = T ∧ (derive_named E cfg C).h_j = h

/-- Twin of `NoHighJustifications` (B13): every held body's named
justification height is at or below the store's current one. -/
def NamedNoHighJustifications (E : Env V) (cfg : HeightConfig)
    (st : Protocol.NamedStore V) : Prop :=
  ∀ B ∈ st.bodies, (derive_named E cfg B).h_j ≤ st.core.h_j

/-- Twin of `ChainStateSlotIsLatestSlot`: the named derivation's slot is
the slot of its latest block, for every named block. -/
def NamedChainStateSlotIsLatestSlot (E : Env V) (cfg : HeightConfig) : Prop :=
  ∀ C : NamedBlock V, (derive_named E cfg C).s = (derive_named E cfg C).L.slot

end DecoupledConsensusModel.Internal

end
