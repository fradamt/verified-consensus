module
public import Mathlib.Data.Finset.Max
public import DecoupledConsensusModel.Execution.Setup
public import DecoupledConsensusModel.Protocol.Grades
public import DecoupledConsensusModel.Protocol.Handlers

@[expose] public section

/-!
# Instantiation outage window

Purpose: define the selected protocol's round length and the first action
after an outage-read time.
An auditor checks the integer-division formula against the action schedule.

Defines: `roundLength`, `roundAfter`, and `nextAction`.
Read after: the model execution schedule.
Read next: the instantiation contents page.
-/
namespace DecoupledConsensusModel.Statements.Instantiation
open Execution DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The round length of the healing schedule, `a_{r+1} - a_r = 4·R·Δ`. -/
def roundLength (S : Setup V) : Time := 4 * S.E.Δ * (S.hc.R : Time)

/-- The first round whose action is at or after `T`: the least `s` with
`T ≤ S.a s`, computed from `S.a s = 6Δ + s·roundLength`. -/
def roundAfter (S : Setup V) (T : Time) : Round :=
  (Int.ediv (T - 6 * S.E.Δ + roundLength S - 1) (roundLength S)).toNat

/-- The first round action at or after `T`. -/
def nextAction (S : Setup V) (T : Time) : Time := S.a (roundAfter S T)

end DecoupledConsensusModel.Statements.Instantiation

end
