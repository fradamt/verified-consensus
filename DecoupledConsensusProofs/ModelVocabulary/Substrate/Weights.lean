module
public import DecoupledConsensusInternal.ModelVocabulary.Substrate.Weights
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import DecoupledConsensusModel.Objects.Identifiers

@[expose] public section

/-!
# §1 Electorate and committees

Two counting regimes coexist and must never be conflated (PROTOCOL.md
`sec:sg-schedule` against PROTOCOL.md `sec:substrate`,
`sec:goldfish-schedule`):

* Goldfish (§2) counts **cardinalities** of subsets of `K_s`, never weights;
* SG, FG and the grades (§3–§6) count **weights** `w(·)` over `V`.

`Committees` therefore supplies membership only, and nothing here routes a
committee through `Electorate.weightOf`.

`Electorate` is copied from `decoupled-consensus-full`'s `Core/Weights/Model.lean`
with the `FaultProfile` half dropped: a model-only formalization states no fault
bound. `Committees` is copied verbatim from `Goldfish/Committees/Model.lean`.
-/

open scoped BigOperators

namespace DecoupledConsensusModel

namespace Electorate

variable {V : Type} [Fintype V] [DecidableEq V]

/-- §6 `m = ⌊W/2⌋ + 1`, the strict-majority threshold of the grades. -/
def strictMajorityThreshold (E : Electorate V) : Nat :=
  E.totalWeight / 2 + 1

end Electorate

end DecoupledConsensusModel

end
