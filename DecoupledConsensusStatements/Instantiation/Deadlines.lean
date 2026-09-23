module
public import DecoupledConsensusModel.Execution.Run

@[expose] public section

/-!
# Instantiation finality deadlines

Purpose: define the selected protocol's finality startup and inclusion
deadline formulas.
An auditor checks the units and the dependence on the recurrence gap and
protocol height parameters.

Defines: `finalityStartup` and `finalityDeadline`.
Read after: `RoundTimes`.
Read next: the instantiation contents page.
-/

namespace DecoupledConsensusModel.Statements.Instantiation

open DecoupledConsensusModel DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-
The concrete startup lag for finality liveness.

The term `7 * gap + 22 + 4 * extra` is the height-progress lag. The factor
`D + K + 5` reaches the first `K` multiple at least `D + 3` heights above the
post-GST honest frontier and then crosses three further heights. The next
three progress lags and `gap + 5` pay for the bounded handoff. The bound is a
lag from the statement's `rGST`; it is independent of `rGST`, `t_GST`, and the
frontier height.
-/
def finalityStartup (S : Setup V) (gap : Round) (extra : Nat) : Round :=
  1 + (S.cfg.D + S.cfg.K + 5) * (7 * gap + 22 + 4 * extra) +
    3 * (7 * gap + 22 + 4 * extra) + gap + 5

/-
The concrete finality deadline after a known common finalized frontier.

The factor `D + K + 2` pays for raw height progress from that frontier to a
height above the finality debt and through the next `K`-band. In each factor,
`4 * L + 4 * gap + 7`, with `L = 7 * gap + 22 + 4 * extra`, pays for the raw
progress and the separated proposal endpoints. The term
`(D + K + 5) * (gap + 1)` pays for the recurrence selection window. This
window is included in every factor, so it does not need one more factor.
-/
def finalityDeadline (S : Setup V) (gap : Round) (extra : Nat) : Round :=
  (S.cfg.D + S.cfg.K + 2) *
    (4 * (7 * gap + 22 + 4 * extra) + 4 * gap + 7 +
      (S.cfg.D + S.cfg.K + 5) * (gap + 1))

end DecoupledConsensusModel.Statements.Instantiation

end
