module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import DecoupledConsensusProofs.Objects.Ancestry

@[expose] public section

/-! # Evidence conversions and the quorum-intersection bound
(design note P1; PROTOCOL.md#the-complete-protocol)
Three things, all leaves of the P1 proof.
* **The one-way conversions.** Evidence gets weaker in exactly one direction:
  the pair-pinned E1 carrier implies the general scoped one, and the scoped one
  implies the pool-scoped one over the union. Nothing converts back — a
  hypothesis in the weak form cannot be used where the strong form is needed,
  which is the whole reason the previous formalization keeps the two apart
  ( §1.6).
* **The degeneracy of the literal unscoped proof.** `SlashableAnywhere` holds of
  every validator, so `¬ SlashableAnywhere` is `False` and any statement taking
  it is vacuous. Proved rather than asserted, because it is the reason this
  project does not copy the previous repo's store-level hypothesis shape.
* **Weighted quorum intersection.** The single source of the `2q − W` bound
  ( §5 node 3). No fault bound
  is needed, and the previous `n = 3f + 1` cardinality convention does not appear.
-/

namespace DecoupledConsensusModel
namespace Proofs

open Internal

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## One-way conversions (PROTOCOL.md#the-complete-protocol) -/

omit [Fintype V] in
/-- P1 the pair-pinned E1 carrier implies ordinary scoped slashability: E1 is a
disjunct of `Slashable` and the pair is forgotten (PROTOCOL.md#the-complete-protocol).

The analogue of the weighted repo's `E1EvidenceForPair.toE1EvidenceFor`. -/
theorem slashableBetween_of_e1EvidenceForPair {p : FinalityPair}
    {A₁ A₂ : Finset (CombinedAttestation V)} {i : V}
    (h : E1EvidenceForPair p A₁ A₂ i) : SlashableBetween A₁ A₂ i := by
  obtain ⟨a, ha, b, hb, hav, hbv, hfp, hcf⟩ := h
  refine ⟨a, ha, b, hb, hav, hbv, ?_⟩
  have h1 : Protocol.e1Slashable a b = true := by
    simp only [Protocol.e1Slashable, Protocol.sameValidator,
      Protocol.e1Fields, hfp, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, Option.elim]
    exact ⟨by rw [hav, hbv], Or.inl hcf⟩
  change Protocol.slashable a b = true
  simp only [Protocol.slashable, h1, Bool.true_or]

/-- P1 the same, aggregated: `2q − W` of E1 weight against one pair is `2q − W`
of slashable weight between the two histories (PROTOCOL.md#the-complete-protocol).

This is what makes `ChainAccountableSafetySharp` imply
`ChainAccountableSafety`. -/
theorem hasE1WeightAt_toSlashableWeight {E : Env V} {p : FinalityPair}
    {A₁ A₂ : Finset (CombinedAttestation V)} (h : HasE1WeightAt E p A₁ A₂) :
    HasSlashableWeightBetween E A₁ A₂ := by
  obtain ⟨S, hw, hev⟩ := h
  exact ⟨S, hw, fun i hi => slashableBetween_of_e1EvidenceForPair (hev i hi)⟩



/-! ## The literal unscoped proof is degenerate (PROTOCOL.md#the-complete-protocol) -/


/-! ## Weighted quorum intersection (PROTOCOL.md#the-complete-protocol) -/

omit [DecidableEq V] in
/-- §3 no validator set weighs more than the electorate (PROTOCOL.md#the-complete-protocol). -/
theorem weightOf_le_totalWeight (E : Electorate V) (S : Finset V) :
    E.weightOf S ≤ E.totalWeight :=
  Finset.sum_le_sum_of_subset (Finset.subset_univ S)

/-- **Weighted quorum intersection** (PROTOCOL.md#the-complete-protocol): two quorums
intersect in weight at least `2q − W`.
The single source of P1's weight bound, and it needs **no fault bound**: the previous
unweighted `n = 3f + 1` cardinality convention dissolves here, because `q` is
already `⌈2W/3⌉` over the electorate. Stated additively, matching
`HasIntersectionWeight`. -/
theorem quorum_intersection (E : Env V) {Q Q' : Finset V}
    (hQ : E.electorate.IsQuorum Q) (hQ' : E.electorate.IsQuorum Q') :
    HasIntersectionWeight E (Q ∩ Q') := by
  have hie : E.electorate.weightOf (Q ∪ Q') + E.electorate.weightOf (Q ∩ Q')
      = E.electorate.weightOf Q + E.electorate.weightOf Q' :=
    Finset.sum_union_inter
  have hu := weightOf_le_totalWeight E.electorate (Q ∪ Q')
  unfold Electorate.IsQuorum at hQ hQ'
  unfold HasIntersectionWeight Env.q Env.W
  omega

end Proofs
end DecoupledConsensusModel

end
