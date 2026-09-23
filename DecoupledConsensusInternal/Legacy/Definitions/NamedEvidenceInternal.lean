module
public import DecoupledConsensusStatements.Instantiation.Certificates
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Definitions.LeakLedger

@[expose] public section

namespace DecoupledConsensusModel.Internal

open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

namespace LeakLedger

/-- Named pre-height snapshot: the parent's named state with this block's
  targeted rows folded (slot staged, rows, latest block), before
  `process_height_events`. This is `fold_rows` of the targeted binding, the
  same staging as `named_transition`. -/
def namedPreHeightSnapshot (E : Env V) (cfg : HeightConfig) : NamedBlock V → ChainState V
  | .genesis => ChainState.initial
  | C@(.node p _ _ _ _ _ _) =>
    fold_rows (TimeoutBinding.targeted V) (derive_named E cfg p) C.erase C.attestations

/-- Named per-block charges: the same 0/1 layer liabilities scaled by the slot
  span, over the named pre-height snapshot and the named derived state. -/
def namedBlockCharges (E : Env V) (cfg : HeightConfig) (C : NamedBlock V) (v : V) :
    LayerCharges :=
  LayerCharges.scale (slotSpan C.erase)
    (charges (namedPreHeightSnapshot E cfg C) (derive_named E cfg C) v)

end LeakLedger

end DecoupledConsensusModel.Internal

end
