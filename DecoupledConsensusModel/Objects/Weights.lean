module
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import DecoupledConsensusModel.Objects.Identifiers

@[expose] public section

/-!
# `DecoupledConsensusModel/Objects/Weights.lean`

Purpose: §1 weights — electorate, quorums, committees.
Paper: `docs/PROTOCOL.md` `sec:complete-store`; algorithm block: the Section 7 wire objects and parameters.

Defines: Electorate, Committees, and quorumCheck.

Read after: `DecoupledConsensusModel.Objects.Identifiers`
Read next: `DecoupledConsensusModel.Objects.Parameters`.

State read: the identifier, time, weight, parameter, and wire types imported by this subject.
State written: typed wire values, parameters, and pure projections; no mutable state is written.

Representation notes: The paper objects use typed Lean inductives/structures and finite collections. Named payloads retain their erased twin where both are active.
-/

-- ── from Substrate/Weights.lean ──
/-!
# §1 Electorate and committees

Two counting regimes coexist and must never be conflated (PROTOCOL.md
`sec:sg-schedule` against PROTOCOL.md `sec:substrate`,
`sec:goldfish-schedule`):

* Goldfish (§2) counts **cardinalities** of subsets of `K_s`, never weights;
* SG, FG and the grades (§3–§6) count **weights** `w(·)` over `V`.

`Committees` therefore supplies membership only, and nothing here routes a
committee through `Electorate.weightOf`.

`Electorate` defines weights without a fault bound. `Committees` defines fixed
membership sets; participation and honesty are separate premises.
-/

open scoped BigOperators

namespace DecoupledConsensusModel

/-- §3 a finite electorate with fixed positive integer weights
(PROTOCOL.md `sec:sg-schedule`). -/
structure Electorate (V : Type) [Fintype V] where
  /-- §3 `w(v)`: a fixed positive integer weight per validator. -/
  weight : V → Nat
  /-- §3 weights are positive (PROTOCOL.md `sec:sg-schedule`). -/
  weight_pos : ∀ i, 0 < weight i

namespace Electorate

variable {V : Type} [Fintype V] [DecidableEq V]

/-- §3 `W = w(V)`: the total fixed validator weight (PROTOCOL.md `sec:sg-schedule`). -/
def totalWeight (E : Electorate V) : Nat :=
  ∑ i, E.weight i

/-- §3 `w(S)`, counting each validator in a finite set once
(PROTOCOL.md `sec:sg-schedule`). -/
def weightOf (E : Electorate V) (S : Finset V) : Nat :=
  ∑ i ∈ S, E.weight i

/-- §4 `q = ⌈2W/3⌉` (PROTOCOL.md `sec:state-machine`). Natural-number ceiling
division by three is written `(2W+2)/3`. -/
def finalityThreshold (E : Electorate V) : Nat :=
  (2 * E.totalWeight + 2) / 3

/-- Executable quorum check. -/
def quorumCheck (E : Electorate V) (S : Finset V) : Bool :=
  decide (E.finalityThreshold ≤ E.weightOf S)

end Electorate

/-- §1 the fixed slot committees `K_s ⊆ V` (PROTOCOL.md `sec:substrate`).

Membership is protocol data. This structure states no nonemptiness, size,
weight, honesty, overlap, sampling, fairness, or cross-slot law, and in
particular attaches **no weight** to committee members: Goldfish counts
cardinalities. -/
structure Committees (V : Type) where
  /-- §1 `K_s`: the committee of slot `s` (PROTOCOL.md `sec:substrate`). -/
  members : Slot → Finset V

end DecoupledConsensusModel

end
