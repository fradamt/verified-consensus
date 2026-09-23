module
public import DecoupledConsensusModel.Objects.Blocks
public import DecoupledConsensusModel.Objects.Parameters
public import DecoupledConsensusModel.Protocol.Schedule
public import DecoupledConsensusModel.Protocol.Grades
public import DecoupledConsensusModel.Protocol.ChainState

@[expose] public section

/-!
# `DecoupledConsensusModel/Execution/Setup.lean`

Purpose: execution — the parameters and structural conditions of a run, including root collision freedom.
Paper: `sec:goldfish-schedule`, `sec:sg-schedule`, `sec:healing-schedule`,
and `sec:complete-store`.

Defines: RootInjectiveOnAncestors, Setup, and PublicTime.

Read after: `DecoupledConsensusModel.Objects.Blocks`, `DecoupledConsensusModel.Objects.Parameters`, `DecoupledConsensusModel.Protocol.Schedule`
Read next: `DecoupledConsensusModel.Execution.Node`.

State read: `Setup`, node state, protocol records, and event/run observations.
State written: execution state, receipts, handles, or the protocol-spec value returned by the adapter.

Representation notes: Execution records keep named payloads beside erased protocol state; adapters preserve the protocol definitions.
-/

-- ── from Roots.lean ──
section
/-!
# Root collision freedom

Block roots are the model's hash identifiers. The `Block` inductive remains a
total raw datatype, so malformed values may reuse a root. Protocol and execution
theorems exclude such collisions on the blocks in their scope.

The two predicates below are the pure, scope-local surface. The execution layer
packages them over every block that one run puts in play.
-/

namespace DecoupledConsensusModel
namespace Execution

variable {V : Type} [DecidableEq V]

/-- Roots identify blocks within the ancestry below `S`.

This is the collision-free hash idealization needed when a transition compares
roots but a theorem concludes equality of blocks. It is scoped so that pure
theorems can still quantify over the raw `Block` datatype. -/
def RootInjectiveBelow (S : Finset (Block V)) : Prop :=
  ∀ A C : Block V, (∃ B ∈ S, A ⪯ B) → (∃ B ∈ S, C ⪯ B) → A.root = C.root → A = C

/-- Root collision freedom across the ancestors of two chain tips. -/
def RootInjectiveOnAncestors (tip₁ tip₂ : Block V) : Prop :=
  RootInjectiveBelow {tip₁, tip₂}

end Execution
end DecoupledConsensusModel
end

-- ── from Execution/Setup.lean ──
section
/-!
# Execution layer — the fixed data of a run
(§2, §3.1; paper labels above)

`Setup` bundles what every handler already takes — the environment, the two
parameter structures, and the per-validator node identity — so that no statement
below has to thread five arguments.

`PublicTime` is the tick schedule. The four per-slot instants in
`sec:goldfish-schedule` are `t_s + kΔ` for `k ∈ {0,1,2,3}` and `t_s = 4Δs`, so the
public times are exactly the natural multiples of `Δ`. Stating the schedule this
way records the public observation times used by the store and handler rules.

This library states the execution data; proof-side results establish its properties.
The agreement between `PublicTime` and the four instants is proved by the proof-side `publicTime_iff` result.
-/

namespace DecoupledConsensusModel
namespace Execution

open Protocol (HeightConfig)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The fixed data of a run: the protocol environment and wire objects from
`sec:goldfish-schedule`, the healing schedule from `sec:healing-schedule`, the
height configuration from `sec:state-machine`, and the per-validator node
identity used by the complete protocol.

The setup domain is finite validators, `Δ > 0`, `R ≥ 3`, `η_SG ≥ 1`, `K ≥ 4`,
`D ≥ 2`, `timeout_rounds`, and `node_val_index`. `node_val_index` is what ties
the node record to the validator it runs: without it a validator could tick
with someone else's identity and every proposer and committee test would read
the wrong name. -/
structure Setup (V : Type) [DecidableEq V] [Fintype V] where
  /-- The protocol environment and electorate used by the schedule and store
  (`sec:goldfish-schedule`, `sec:complete-store`). -/
  E : Env V
  /-- The healing round schedule (`sec:healing-schedule`). -/
  hc : Protocol.HealConfig
  /-- The finality-gadget height parameters (`sec:state-machine`). -/
  cfg : HeightConfig
  /-- The named node each validator runs (`sec:complete-store`). -/
  node : V → Protocol.Node V
  /-- The node's validator identity, equal to the validator running it. -/
  node_val_index : ∀ v, (node v).val_index = v
  /-- The timeout is a whole number of rounds and at least two rounds
  (`sec:healing-schedule`, `sec:state-machine`). -/
  timeout_rounds : hc.R ∣ cfg.timeoutDelay ∧ 2 * hc.R ≤ cfg.timeoutDelay
  /-- Every committee is nonempty; an empty committee would make every committee premise false. -/
  committee_nonempty : ∀ s, (E.committee s).Nonempty
  /-- The outage window `[outageStart T, expiry T)` is nonempty only when a
  round is long enough: at `R = 3`, `η_SG = 1` it is empty. -/
  outage_window : 4 ≤ hc.R * hc.η_SG

namespace Setup

variable (S : Setup V)

/-- `a_r = t_{rR} + 6Δ`, the round action time (`sec:healing-schedule`). -/
abbrev a (r : Round) : Time := S.hc.a S.E.Δ r

end Setup

end Execution
end DecoupledConsensusModel
end

end
