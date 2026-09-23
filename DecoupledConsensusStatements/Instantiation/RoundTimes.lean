module
public import Mathlib.Tactic
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Data.Int.Interval
public import DecoupledConsensusModel.Execution.Run
public import DecoupledConsensusModel.Protocol.Handlers

@[expose] public section

/-!
# Instantiation round times

Purpose: define the selected protocol's round schedule and recovery timing.
An auditor checks the action-round definition and the protocol-specific
recovery lag used by the generic constants.

Defines: `roundPeriod`, `nextRound`, `roundAt`, `boundedPhaseStartLag`, and
`recoveryRound`.
Read after: the model execution schedule.
Read next: `Deadlines` and the instantiation contents page.
-/

namespace DecoupledConsensusModel.Statements.Instantiation

open DecoupledConsensusModel DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The positive action period, in `Time` and in `Nat` form. -/
def roundPeriod (S : Setup V) : Nat := Int.toNat (S.a 1 - S.a 0)

/-- The first round whose action time is at or after `t`, using
`max 0 ⌈(t − a₀) / period⌉` in integer arithmetic. `Int.toNat` supplies the
zero clamp for times at or before `a₀`; `Nat.ceilDiv` supplies the ceiling. -/
def nextRound (S : Setup V) (t : Time) : Round :=
  Int.toNat (t - S.a 0) ⌈/⌉ roundPeriod S

/-- The public historical name for `nextRound`. -/
def roundAt (S : Setup V) (t : Time) : Round :=
  nextRound S t

/-- The bounded phase-start lag in rounds: the first parenthesized term covers
the gap-dependent grade work, the next term covers the three progress lags,
and the final terms cover the handoff and extra timeout rounds. -/
def boundedPhaseStartLag (gap extra : Nat) : Nat :=
  (4 * gap + 12 + 2 * extra) + 3 * gap + 10 + 2 * extra

/-- The recovery round starts after the rounded reference time, the bounded
phase-start lag, the two progress lags, the SG lookback, and the recurrence
gap. -/
noncomputable def recoveryRound (S : Setup V) (t₀ : Time) (gap extra : Nat) : Round :=
  roundAt S t₀ + 1 +
    (1 + (S.cfg.D + S.cfg.K + 5) * boundedPhaseStartLag gap extra) +
    2 * boundedPhaseStartLag gap extra +
    max (1 + S.hc.η_SG) (gap + 3) + gap

open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The public boundary after the opening slot and its two vote-duty slots. -/
def healingBoundaryTime (S : Setup V) (q : Round) : Time :=
  Protocol.vote_time S.E (S.hc.opening_slot q + 2)

end DecoupledConsensusModel.Statements.Instantiation

end
