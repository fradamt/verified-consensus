module
public import DecoupledConsensusModel
public import DecoupledConsensusInternal.ModelVocabulary.Execution.NamedEvent

@[expose] public section

/-! Canonical events and world transition use the complete named path. -/
namespace DecoupledConsensusModel.Execution

abbrev Event := NamedEvent
namespace Event
abbrev tick := @NamedEvent.tick
abbrev deliver := @NamedEvent.deliver
abbrev time {V : Type} (e : Event V) : Time := NamedEvent.time e
abbrev node {V : Type} (e : Event V) : V := NamedEvent.node e
abbrev key := @NamedEvent.key
abbrev object? := @NamedEvent.object?
end Event

namespace World
abbrev step := @NamedWorld.step
end World

end DecoupledConsensusModel.Execution

end
