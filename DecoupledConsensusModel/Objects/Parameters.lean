module
public import DecoupledConsensusModel.Objects.Blocks
public import DecoupledConsensusModel.Objects.Time
public import DecoupledConsensusModel.Objects.Weights

@[expose] public section

/-!
# `DecoupledConsensusModel/Objects/Parameters.lean`

Purpose: §1 parameters — the fixed environment: committees, W, q, schedule.
Paper: `docs/PROTOCOL.md` `sec:complete-store`; algorithm block: the Section 7 wire objects and parameters.

Defines: Env, committee, slotOf, and proposer schedule reads.

Read after: `DecoupledConsensusModel.Objects.Blocks`, `DecoupledConsensusModel.Objects.Time`, `DecoupledConsensusModel.Objects.Weights`
Read next: `DecoupledConsensusModel.Protocol.Schedule`.

State read: the identifier, time, weight, parameter, and wire types imported by this subject.
State written: typed wire values, parameters, and pure projections; no mutable state is written.

Representation notes: The paper objects use typed Lean inductives/structures and finite collections. Named payloads retain their erased twin where both are active.
-/

-- ── from Substrate/Env.lean ──
/-!
# §1 Protocol environment

The fixed data every section reads: the validator set (as the type `V`), the
schedule unit `Δ`, `t_GST`, the per-slot proposer and committee oracles, and the
weighted electorate (PROTOCOL.md `sec:substrate`, `sec:sg-schedule`).

`Δ` is a schedule constant unconditionally; only the delivery guarantee is
conditional on `t_GST`, so nothing here mentions delivery. `R`, `η_SG`,
`K` and `D` are not here: they enter with §3 and §4.
-/

namespace DecoupledConsensusModel

/-- §1 the fixed protocol environment (PROTOCOL.md `sec:substrate`). -/
structure Env (V : Type) [DecidableEq V] [Fintype V] where
  /-- §1 `Δ`: the schedule unit, and a strict delivery bound after `t_GST`
  (PROTOCOL.md `sec:substrate`). -/
  Δ : Time
  /-- `Δ` is positive, so `t_s = 4Δs` is strictly increasing. -/
  Δ_pos : 0 < Δ
  /-- §1 `t_GST`: after it, `Δ` bounds delivery and honest nodes relay every
  object they process (PROTOCOL.md `sec:substrate`). -/
  t_GST : Time
  /-- `t_GST` is a time of the run: no event happens before time 0, so a GST
  before genesis is normalized to 0. -/
  t_GST_nonneg : 0 ≤ t_GST
  /-- §1 the assigned proposer of each slot (PROTOCOL.md `sec:substrate`). -/
  proposer : Slot → V
  /-- §1 the fixed committees `K_s ⊆ V` (PROTOCOL.md `sec:substrate`). -/
  committees : Committees V
  /-- §3 the weighted electorate `w(·)`, `W` (PROTOCOL.md `sec:sg-schedule`). -/
  electorate : Electorate V

namespace Env

variable {V : Type} [DecidableEq V] [Fintype V] (E : Env V)

/-- §1 `K_s` (PROTOCOL.md `sec:substrate`). -/
def committee (s : Slot) : Finset V :=
  E.committees.members s

/-- §1 `t_s = 4Δs` (PROTOCOL.md `sec:substrate`). -/
def t (s : Slot) : Time :=
  slotStart E.Δ s

/-- §1 `s = ⌊t / 4Δ⌋`
(PROTOCOL.md `alg:goldfish-store`, `alg:pair-rules`, `alg:store`). -/
def slotOf (u : Time) : Slot :=
  slotOfTime E.Δ u

/-- §3 `W = w(V)` (PROTOCOL.md `sec:sg-schedule`). -/
def W : Nat :=
  E.electorate.totalWeight

/-- §4 `q = ⌈2W/3⌉` (PROTOCOL.md `sec:state-machine`). -/
def q : Nat :=
  E.electorate.finalityThreshold

end Env

end DecoupledConsensusModel

end
