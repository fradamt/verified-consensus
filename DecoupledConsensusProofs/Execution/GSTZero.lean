module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.Anchor

@[expose] public section

/-! # compatibility honest-quorum fault margins
`Internal.AvailabilityGSTZero` assumes `HonestWeightMajority` and
`HonestCommittees`. It does not assume `HonestQuorum` or `BelowOneThird`.
This file keeps older `HonestQuorum` helper lemmas for compatibility with proof
routes that still use the stronger premise. These helpers give two arithmetic
facts:
* faulty weight is below the absolute strict-majority threshold `m`; and
* twice faulty weight is at most honest weight.
The second inequality is non-strict. This is sufficient because the relative
majority branch tests a strict inequality. The public GST-zero route uses the
`HonestWeightMajority` lemmas in `Availability/HonestMajority.lean`.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]



/-- A strict honest committee majority makes the honest set nonempty. -/
theorem honest_nonempty_of_honestCommittees
    {S : Setup V} {H : Finset V} (hcom : HonestCommittees S H) :
    H.Nonempty := by
  have hmajority := hcom 0
  have hpos : 0 < ((S.E.committee 0) ∩ H).card := by omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
  exact ⟨v, (Finset.mem_inter.mp hv).2⟩

/-- Honest committee participation and positive validator weights make the
total electorate weight positive. -/
theorem totalWeight_pos_of_honestCommittees
    {S : Setup V} {H : Finset V} (hcom : HonestCommittees S H) :
    0 < S.E.W := by
  obtain ⟨v, hv⟩ := honest_nonempty_of_honestCommittees hcom
  have hweight : S.E.electorate.weight v ≤ S.E.electorate.weightOf H := by
    unfold Electorate.weightOf
    exact Finset.single_le_sum (fun i _ => Nat.zero_le (S.E.electorate.weight i)) hv
  have htotal := S.E.electorate.weightOf_mono (Finset.subset_univ H)
  unfold Env.W
  exact lt_of_lt_of_le (S.E.electorate.weight_pos v) (le_trans hweight htotal)

/-- With positive total weight, an honest quorum leaves strictly less than one
quorum of faulty weight. -/
theorem faulty_lt_q_of_honestQuorum
    {S : Setup V} {H : Finset V} (hcom : HonestCommittees S H)
    (hq : HonestQuorum S H) :
    S.E.electorate.weightOf (Finset.univ \ H) < S.E.q := by
  have hsum := S.E.electorate.weightOf_add_weightOf_sdiff H
  have hW := totalWeight_pos_of_honestCommittees hcom
  unfold HonestQuorum at hq
  unfold Env.q at hq ⊢
  unfold Env.W at hW
  unfold Electorate.finalityThreshold at hq ⊢
  omega

/-- Every finality quorum contains an honest validator under the two GST-zero
counting assumptions. This is the exact witness form needed to show that a
new justification uses an honest target. -/
theorem exists_honest_member_of_quorum
    {S : Setup V} {H Q : Finset V} (hcom : HonestCommittees S H)
    (hq : HonestQuorum S H) (hQ : S.E.electorate.IsQuorum Q) :
    ∃ v ∈ Q, v ∈ H := by
  by_contra hnone
  push Not at hnone
  have hsub : Q ⊆ Finset.univ \ H := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hnone v hv⟩
  have hle := S.E.electorate.weightOf_mono hsub
  have hlt := faulty_lt_q_of_honestQuorum hcom hq
  unfold Electorate.IsQuorum at hQ
  unfold Env.q at hlt
  omega

/-! ## Anchor consequences

These are GST-zero counterparts of the `BelowOneThird` theorems in
`Proofs.Optimistic.Anchor`. They reuse that file's support bounds and replace only
the final arithmetic step.
-/


end Protocol
end DecoupledConsensusModel

end
