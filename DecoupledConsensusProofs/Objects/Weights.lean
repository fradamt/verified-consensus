module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.Evidence

@[expose] public section

/-!
# Weight arithmetic for the engine lemmas
(design note; PROTOCOL.md#the-complete-protocol)

The reusable half of `decoupled-consensus-full`'s `Core/Weights/Proof.lean`,
restated to this model's `Electorate`. Five facts, all leaves:

* `weightOf_mono` (`Proof.lean:29`);
* `weight_inter_add_weight_union` — weighted inclusion–exclusion
  (`Proof.lean:38`);
* `isQuorum_iff_three_mul_weight` — the ceiling-division reflection
  (`Proof.lean:86`), which is what lets `omega` finish a threshold argument
  without ever unfolding `(2W+2)/3`;
* `totalWeight_le_two_finalityThreshold` — `W ≤ 2q`, so the truncating `2q − W`
  of the document never actually truncates;
* `weightOf_sdiff_add_weightOf` — the complement identity.

**The `2q − W` intersection bound itself is not re-proved here.**
`Proofs.quorum_intersection` (`Evidence.lean:125`) already states it additively
over `Env`, which is the form `HasIntersectionWeight` is written in. This
file adds the two shapes the engine lemmas need on top of it: the truncated
subtraction form the document writes, and the honest-complement bound
`q ≤ w(Q ∩ Hon) + w(V \ Hon)`, which is Lemma G4's arithmetic with **no**
hypothesis on the honest weight at all.
-/

open scoped BigOperators

namespace DecoupledConsensusModel

namespace Electorate

variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
/-- §3 weight is monotone in the set (PROTOCOL.md#the-complete-protocol). -/
theorem weightOf_mono (E : Electorate V) {S T : Finset V} (h : S ⊆ T) :
    E.weightOf S ≤ E.weightOf T :=
  Finset.sum_le_sum_of_subset h

/-- §3 **weighted inclusion–exclusion**: `w(S ∩ T) + w(S ∪ T) = w(S) + w(T)`
(PROTOCOL.md#the-complete-protocol). The one counting identity every quorum argument in the
document runs on. -/
theorem weight_inter_add_weight_union (E : Electorate V) (S T : Finset V) :
    E.weightOf (S ∩ T) + E.weightOf (S ∪ T) = E.weightOf S + E.weightOf T := by
  rw [Nat.add_comm (E.weightOf (S ∩ T))]
  exact Finset.sum_union_inter

/-- §3 the union is no heavier than the two parts (PROTOCOL.md#the-complete-protocol). -/
theorem weightOf_union_le (E : Electorate V) (S T : Finset V) :
    E.weightOf (S ∪ T) ≤ E.weightOf S + E.weightOf T := by
  have h := weight_inter_add_weight_union E S T
  omega

/-- §3 the complement identity: `w(S) + w(V \ S) = W` (PROTOCOL.md#the-complete-protocol). -/
theorem weightOf_add_weightOf_sdiff (E : Electorate V) (S : Finset V) :
    E.weightOf S + E.weightOf (Finset.univ \ S) = E.totalWeight := by
  rw [Nat.add_comm]
  exact Finset.sum_sdiff (Finset.subset_univ S)

omit [DecidableEq V] in
/-- §4 **the ceiling-division reflection** (PROTOCOL.md#the-complete-protocol):
`w(S) ≥ q = ⌈2W/3⌉` is exactly `3·w(S) ≥ 2W`.

The proof of `decoupled-consensus-full`'s `isQuorum_iff_three_mul_weight`. Every
threshold argument below reflects through this and then runs on `omega`; nothing
else in the project unfolds `(2W+2)/3`. -/
theorem isQuorum_iff_three_mul_weight (E : Electorate V) (S : Finset V) :
    E.IsQuorum S ↔ 2 * E.totalWeight ≤ 3 * E.weightOf S := by
  unfold IsQuorum finalityThreshold
  omega

omit [DecidableEq V] in
/-- §4 `W ≤ 2q` (PROTOCOL.md#the-complete-protocol): the document's `2q − W` is a real
quantity, not a truncation artefact. Recorded because the headline statements are
written additively for exactly this reason ( §5 D7),
and a reader is entitled to see that the two forms agree. -/
theorem totalWeight_le_two_finalityThreshold (E : Electorate V) :
    E.totalWeight ≤ 2 * E.finalityThreshold := by
  unfold finalityThreshold
  omega

end Electorate

namespace Proofs

open Internal

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The two shapes the engine lemmas consume (PROTOCOL.md#the-complete-protocol) -/


/-- **Lemma G4's arithmetic, in its weakest form** (PROTOCOL.md#the-complete-protocol,
644–658): a quorum `Q` puts at least `q − w(V \ Hon)` of weight inside `Hon`,
whatever `Hon` is.

No hypothesis on `Hon`: the bound is `Q ⊆ (Q ∩ Hon) ∪ (V \ Hon)` and nothing
else. Stated additively. With `w(Hon) ≥ q` it sharpens to `2q − W`, which is
`quorum_intersection` at `Q':= Hon`; both forms are used, because rev. 3 §1.1
states G4 with the complement and §4.2 (d) uses it with the honest quorum. -/
theorem quorum_meets_set (E : Env V) {Q Hon : Finset V}
    (hQ : E.electorate.IsQuorum Q) :
    E.q ≤ E.electorate.weightOf (Q ∩ Hon) +
      E.electorate.weightOf (Finset.univ \ Hon) := by
  have hsub : Q ⊆ (Q ∩ Hon) ∪ (Finset.univ \ Hon) := by
    intro i hi
    by_cases hmem : i ∈ Hon
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hi, hmem⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hmem⟩)
  have hmono := E.electorate.weightOf_mono hsub
  have hle := E.electorate.weightOf_union_le (Q ∩ Hon) (Finset.univ \ Hon)
  unfold Electorate.IsQuorum at hQ
  unfold Env.q
  omega

/-- §4 an honest quorum intersects any quorum in `2q − W` weight
(PROTOCOL.md#the-complete-protocol). `quorum_intersection` at `Q':= Hon`, named for the way
Lemma G4 reads it: *the honest part of any quorum carries `2q − W`*. -/
theorem honest_part_of_quorum (E : Env V) {Q Hon : Finset V}
    (hQ : E.electorate.IsQuorum Q) (hHon : E.electorate.IsQuorum Hon) :
    HasIntersectionWeight E (Q ∩ Hon) :=
  quorum_intersection E hQ hHon

end Proofs
end DecoupledConsensusModel

end
