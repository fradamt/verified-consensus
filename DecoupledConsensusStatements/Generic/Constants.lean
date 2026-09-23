module
public import DecoupledConsensusModel.Generic.Env

@[expose] public section

/-!
# Generic constants

Purpose: define the timing and bound parameters used by the generic claims.
An auditor checks the unit of every field and the inclusion/growth delay pair
for each output.

Defines: `Constants`.
Read after: `Interface`.
Read next: `Properties`, `Conditions`, and `Regimes`.
-/

namespace DecoupledConsensusModel.Statements.Generic

open DecoupledConsensusModel

/-- Timing and bound constants for the generic claims.

`gap` counts periods in recurrence and growth premises. Recovery and finality
deadlines are protocol-specific functions of the start time and recurrence
gap. The concrete instances are expected to have `period > 0`, and opening
slots are expected to be `period` apart; these are interface properties, not
fields here. The inclusion/growth pairs are: confirmed
(`confirmationDelay`, `growthDelay`), stable (`stableInclusionDelay`,
`stableGrowthDelay`), and finalized (`finalityDeadline`,
`finalityStartup`/the resulting finalized live delay).
The delay grid is:

```text
output inclusion delay growth delay
confirmed confirmationDelay growthDelay
stable stableInclusionDelay stableGrowthDelay
finalized finalityDeadline gap * period + finalityDeadline
```

All delay fields and `period`, `participationWindow`, `participationLag`,
`prefixEnd`, `recoveryEnd`, `outageStart`, and `expiry` use `Time`. The
`proposerSlots` and `maxGap` fields use `Nat`; `gap` is measured in periods. -/
structure Constants where
  /-- Duration of one recurrence period, in `Time`; expected to be positive. -/
  period : Time
  /-- Width of the awake-history window used by `WindowMajority`, in `Time`. -/
  participationWindow : Time
  /-- Time offset serves to form the sleepy and outage reference sample. In the
  selected instance it is one SG action round; the generic regimes also guard
  that the reference time is nonnegative and in the run horizon. -/
  participationLag : Time
  /-- Number of consecutive proposer slots, including the opening slot. -/
  proposerSlots : Nat
  /-- End time of the source prefix at reference time `t₀` and recurrence gap
  `gap`. -/
  prefixEnd : Time → Nat → Time
  /-- Time at which the continuation counts as recovered, from reference time
  `t₀` and recurrence gap `gap`. -/
  recoveryEnd : Time → Nat → Time
  /-- Maximum recurrence gap, measured in periods. -/
  maxGap : Nat
  /-- Delay from a proposal at its proposal time to confirmed inclusion, in
  `Time`; the confirmed inclusion delay. -/
  confirmationDelay : Time
  /-- The delay used by `liveFrom_of_includedFrom`: `gap · period + D`, with
  `D = confirmationDelay`, in `Time`; the confirmed growth delay. -/
  growthDelay : Nat → Time
  /-- The stable growth delay for recurrence gap `gap`: `gap · period + D`,
  with `D = stableInclusionDelay`, in `Time`. -/
  stableGrowthDelay : Nat → Time
  /-- Delay from a proposal at its proposal time to stable inclusion, in
  `Time`; the stable inclusion delay. -/
  stableInclusionDelay : Time
  /-- Protocol-specific finality startup delay for recurrence gap `gap`, in
  `Time`; the finalized startup delay. -/
  finalityStartup : Nat → Time
  /-- Protocol-specific finality inclusion deadline after startup for
  recurrence gap `gap`, in `Time`; the finalized inclusion delay. -/
  finalityDeadline : Nat → Time
  /-- Earliest permitted outage start for the stable output read at time `T`,
  in `Time`. -/
  outageStart : Time → Time
  /-- The time after which votes formed for the stable output read at `T` may
  expire, in `Time`. -/
  expiry : Time → Time

/-- The constants are well formed; the live and outage claims below are not
vacuous. -/
structure Constants.Valid (C : Constants) : Prop where
  period_pos : 0 < C.period
  participationWindow_nonneg : 0 ≤ C.participationWindow
  participationLag_nonneg : 0 ≤ C.participationLag
  proposerSlots_pos : 0 < C.proposerSlots
  maxGap_ge_two : 2 ≤ C.maxGap
  delays_nonneg : ∀ gap,
    0 ≤ C.confirmationDelay ∧
    0 ≤ C.growthDelay gap ∧
    0 ≤ C.stableGrowthDelay gap ∧
    0 ≤ C.stableInclusionDelay ∧
    0 ≤ C.finalityStartup gap ∧
    0 ≤ C.finalityDeadline gap
  prefixEnd_le_recoveryEnd : ∀ t₀ gap, C.prefixEnd t₀ gap ≤ C.recoveryEnd t₀ gap
  outage_window_nonempty : ∀ T, C.outageStart T < C.expiry T

end DecoupledConsensusModel.Statements.Generic

end
