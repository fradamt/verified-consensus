module
public import DecoupledConsensusModel
public import DecoupledConsensusInternal.ModelVocabulary.Execution.Objects

@[expose] public section

/-! Canonical state and tick facade. A tick receives the complete saved named
node, including its phase cache. The selected tick keeps the saved frame and
does not reconstruct it from a store-only view. -/
namespace DecoupledConsensusModel.Execution

abbrev NodeState := NamedNodeState
abbrev World := NamedWorld

namespace NodeState
abbrev mk := @NamedNodeState.mk
noncomputable abbrev rec := @NamedNodeState.rec
noncomputable abbrev recOn := @NamedNodeState.recOn
noncomputable abbrev casesOn := @NamedNodeState.casesOn
abbrev st {V : Type} (n : NodeState V) : Protocol.NamedStore V := NamedNodeState.st n
abbrev record {V : Type} (n : NodeState V) : Protocol.NamedRecord := NamedNodeState.record n
abbrev cache {V : Type} (n : NodeState V) : DecoupledConsensusModel.Protocol.Cache V := NamedNodeState.cache n
/-- The canonical record role retains the complete named record. -/
abbrev Λ {V : Type} (n : NodeState V) : Protocol.NamedRecord := NamedNodeState.record n
abbrev initial := @NamedNode.initial
abbrev tick := @NamedNode.tick
abbrev process {V : Type} [DecidableEq V] [Fintype V]
    (S : Setup V) (n : NodeState V) (o : Object V) : NodeState V :=
  NamedNode.process S n o
end NodeState

namespace NamedNodeState
/-- Method lookup on an actual named state retains the full named record. -/
abbrev Λ {V : Type} (n : NamedNodeState V) : Protocol.NamedRecord := n.record
end NamedNodeState

namespace World
abbrev init := @NamedWorld.init
end World

/-- The canonical emitting tick preserves the complete cache-bearing state. -/
abbrev on_tick_emit := @NamedNode.tick

end DecoupledConsensusModel.Execution

end
