module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.ModelVocabulary.Execution.Run

@[expose] public section

/-! # What a protocol exposes to be judged

The public statements read protocol behavior through `Interface` and timing
through `Constants`. The execution model remains concrete in this stage.
-/

namespace DecoupledConsensusModel
namespace Statements

open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The protocol reads used by the public statements. -/
structure Interface (V : Type) [DecidableEq V] where
  /-- The three user-facing outputs, as getters on the node store. -/
  confirmed : Protocol.Store V → Block V
  stable : Protocol.Store V → Block V
  finalized : Protocol.Store V → Block V
  /-- The proposal schedule and the block emitted by a slot. -/
  proposer : Slot → V
  proposalTime : Slot → Time
  proposedBlock : Run V → Slot → Option (NamedBlock V)
  /-- The committee of a slot. -/
  committee : Slot → Finset V
  /-- A finality certificate. -/
  Certificate : Type
  /-- Certificate `c` finalizes target `T`. -/
  finalizes : Certificate → Block V → Prop
  /-- The certificate roots satisfy the model's collision-free idealization. -/
  collisionFree : Certificate → Certificate → Prop
  /-- Two certificates contain slashable evidence. -/
  evidence : Certificate → Certificate → Prop
  /-- Two stores hold slashable evidence against each other. -/
  slashable : Protocol.Store V → Protocol.Store V → Prop
  /-- Certificate `c` is assembled from blocks of the run. -/
  inRun : Run V → Certificate → Prop

/-- Delays, windows, and lengths used by the public statements. -/
structure Constants where
  /-- One SG round. -/
  roundLength : Time
  /-- The sleepy participation window, in rounds. -/
  windowRounds : Nat
  /-- The end of a finite recovery prefix. -/
  prefixEnd : Time → Nat → Nat → Time
  /-- The time at which the run counts as recovered. -/
  recoveryEnd : Time → Nat → Nat → Time
  /-- Time from a proposal to confirmed inclusion. -/
  confirmationDelay : Time
  /-- Growth delays for the confirmed and stable outputs. -/
  growthDelay : Nat → Time
  stableGrowthDelay : Nat → Time
  /-- Finality startup and per-block deadline. -/
  finalityStartup : Nat → Nat → Time
  finalityDeadline : Nat → Nat → Time
  /-- Outage formation margin and vote expiry. -/
  formationMargin : Time
  expiry : Time → Time

end Statements
end DecoupledConsensusModel

end
