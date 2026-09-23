module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Assumptions.Weight
public import DecoupledConsensusInternal.Execution.Admissible
public import DecoupledConsensusInternal.Derived

@[expose] public section

/-!
# Execution layer — standing assumptions and the good-state interface
(design §5; PROTOCOL.md#the-complete-protocol)

Two counting regimes, never conflated (`Weights.lean`): Goldfish counts
**cardinalities** of committee subsets, the finality gadget counts **weights**.
So the two assumptions below are of different kinds, and neither implies the
other.

**Two fault bounds, and they are not the same assumption** (rev. 4). The
project's statements need a bound on faults in two quite different places, and
rev. 4 names both rather than paying the stronger price everywhere.

* `SlashableBound` — *accountable* faults. No `2q − W` of weight leaves
  **slashable evidence** in the run. A violation is detectable and punishable:
  the evidence is on chain, and P1 hands the caller the names. This is what the
  quorum-clash results need, and it is a much weaker hypothesis than a bound on
  the adversary's size.
* `BelowOneThird` — *adversarial* faults. Fewer than `W/3` of weight deviates at
  all. This is what every Lemma G4 argument needs, because a quorum contains
  honest weight only when the adversary cannot form one alone.

The gap between them is real and is worth stating: **fresh adversarial votes at
a height nobody has voted at are not slashable against anything.** With `b ≥ q`
the adversary assembles a justification off the canonical chain and produces no
evidence at all, so the weak form cannot exclude it. Anything that must exclude
*fresh* off-chain certificates therefore carries `BelowOneThird`; anything that
only has to exclude *conflicting* ones carries `SlashableBound`.

`GoodState` is W1's to fill. The layer supplies its argument — the whole-run
`WorldView` — and leaves the predicate abstract; `AlignedRound.lean` instantiates
it.
-/



namespace DecoupledConsensusModel
namespace Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Honest validators hold a strict majority of the total validator weight.

This is the global fault assumption for the available-chain part of the
ebb-and-flow protocol. It is separate from `HonestCommittees`, because
Goldfish counts committee members while SG, FG, and grades count validator
weight. It is also strictly weaker than `HonestQuorum`: available-chain
confirmation needs one honest participant in each weighted majority or
finality quorum, not an honest finality quorum and not quorum intersection. -/
def HonestWeightMajority (S : Setup V) (H : Finset V) : Prop :=
  S.E.electorate.weightOf (Finset.univ \ H) <
    S.E.electorate.weightOf H

/-- Honest **weight** reaches the finality quorum `q = ⌈2W/3⌉`
(PROTOCOL.md#the-complete-protocol). This is what Lemma G4's `2q − W` margin needs
(p4-statement-research rev. 3 §1.1).

**Derived from `BelowOneThird` since rev. 4.** This stronger arithmetic shape
remains useful for proof layers that need an honest finality quorum. P3(a)
does not assume it: the available-chain proof uses `HonestWeightMajority` and
extracts only one honest participant from each protocol quorum. -/
def HonestQuorum (S : Setup V) (H : Finset V) : Prop :=
  S.E.q ≤ S.E.electorate.weightOf H


/-- W1's interface (design §5, §10). The only design commitment the layer makes is
that the view reads the whole run, which is what lets "no hidden conflicting
justification" be stated without an adversary-state model. -/
abbrev GoodState (V : Type) := WorldView V → Prop

end Execution
end DecoupledConsensusModel

end
