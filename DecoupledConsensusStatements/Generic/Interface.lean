module
public import DecoupledConsensusModel.Generic.Run
public import DecoupledConsensusModel.Objects.Blocks

@[expose] public section

/-!
# Generic interface

Purpose: define the protocol observations used by the generic review claims.
An auditor checks that each output, proposal, certificate, and run fact is
exposed without importing proof or fixture code.

Defines: `Interface`, `Output`, and `readAt`.
Read after: `DecoupledConsensusModel.Generic.Run`.
Read next: `Constants`, then `Properties`.
-/

namespace DecoupledConsensusModel.Statements.Generic

open DecoupledConsensusModel

variable {V : Type} [DecidableEq V]

structure Interface (P : DecoupledConsensusModel.Generic.ProtocolSpec V) where
  /-- The three user-facing outputs, as getters on the node state. -/
  confirmed : P.State → Block V
  stable : P.State → Block V
  finalized : P.State → Block V
  /-- The proposal schedule: slot `s` has a proposer, a proposal time, and the
  total output of the proposal duty on the prepared read. -/
  proposer : Slot → V
  proposalTime : Slot → Time
  /-- The block the proposal duty produces for slot `s` on the prepared read;
  total; the duty's output. -/
  proposedBlock : DecoupledConsensusModel.Generic.Run V P.Object → Slot → Option (Block V)
  /-- Slots at which a period opens. This is used only by the recurrence
  premise. -/
  opening : Slot → Prop
  /-- The committee of a proposal slot. -/
  committee : Slot → Finset V
  /-- A finality certificate. -/
  Certificate : Type
  /-- Certificate `c` finalizes target `T`. -/
  finalizes : Certificate → Block V → Prop
  /-- The certificate roots satisfy the model's collision-free idealization. -/
  collisionFree : Certificate → Certificate → Prop
  /-- Two certificates contain slashable evidence. -/
  evidence : Certificate → Certificate → Prop
  /-- Two node states hold slashable evidence against each other. -/
  slashable : P.State → P.State → Prop
  /-- Certificate `c` is attributable to blocks in the run. -/
  inRun : DecoupledConsensusModel.Generic.Run V P.Object → Certificate → Prop
  /-- The hash idealization the protocol assumes on the blocks of a run. -/
  idealization : DecoupledConsensusModel.Generic.Run V P.Object → Prop
  /-- Two reads of the run, at any nodes and any times, hold evidence
  attributable to `v`. -/
  slashes : DecoupledConsensusModel.Generic.Run V P.Object → V → Prop

abbrev Output (P : DecoupledConsensusModel.Generic.ProtocolSpec V) :=
  P.State → Block V

/-- The output `g` read at node `v` and time `t`. -/
def readAt (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) (g : Output P)
    (v : V) (t : Time) : Block V :=
  g (DecoupledConsensusModel.Generic.Run.readAt P rho t v)

end DecoupledConsensusModel.Statements.Generic

end
