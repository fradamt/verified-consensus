module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Canonicality
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HonestMajorityCore

@[expose] public section

/-!
# Honest-weight-majority availability lemmas

The relative-SG argument uses the complete represented denominator. A
validator that supports a block is represented, even when it is faulty.
Therefore the denominator contains both the honest set and every supporter of
a conflicting block. Those two sets are disjoint. This sharper accounting
closes the relative-majority fork-choice step from only a strict honest-weight
majority.

The threshold facts and raw support-to-representation lemma live in
`HonestMajorityCore`, which does not import the canonicality layer.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Protocol (derive_named)
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! Consequences of the public `Execution.HonestWeightMajority`
assumption. The namespace avoids collisions with temporary migration lemmas
that use longer names. -/
namespace HonestWeightMajority

/-! ## The represented denominator -/

/-- Honest validators and all supporters of `D` belong to the represented
set. No compatibility or fault threshold is needed for this set inclusion. -/
theorem honest_union_supporters_subset_represented
    {pool : Round → Finset (Protocol.SGVote V)} {etaSG : Round}
    {T : Finset (Block V)} {Hon : Finset V} {r : Round}
    {B D : Block V}
    (hal : SupportCompatible pool etaSG T Hon r B) :
    Hon ∪ Protocol.sgSupporters pool etaSG T r D ⊆
      Protocol.represented_set pool etaSG r := by
  intro v hv
  rw [Protocol.represented_set, Finset.mem_filter]
  refine ⟨Finset.mem_univ v, ?_⟩
  rcases Finset.mem_union.mp hv with hvHon | hvSupport
  · exact hal.represented v hvHon
  · exact represented_of_supports (Finset.mem_filter.mp hvSupport).2




/-! ## Relative-SG compatibility -/


/-! ## Compatible grades and finality-gadget history -/









/-! ## Directed `SupportAligned` form -/







/-- In the directed interface, honest validators and the supporters of a
block outside `Can` are disjoint. -/
theorem honest_disjoint_supporters_of_not_preceq
    {pool : Round → Finset (Protocol.SGVote V)} {etaSG : Round}
    {T : Finset (Block V)} {Hon : Finset V} {r : Round}
    {Can D : Block V}
    (hal : Proofs.Optimistic.SupportAligned pool etaSG T Hon r Can)
    (hD : Block.preceq D Can = false) :
    Disjoint Hon (Protocol.sgSupporters pool etaSG T r D) := by
  rw [Finset.disjoint_left]
  intro v hvHon hvSupport
  have hsupport := (Finset.mem_filter.mp hvSupport).2
  rw [Proofs.Optimistic.not_supports_off_can hal hvHon hD] at hsupport
  exact absurd hsupport (by simp)

/-- In the directed interface, an off-chain block's support weight is counted
on top of honest weight in the represented denominator. -/
theorem honest_add_sg_support_le_W_r_of_not_preceq
    (E : Env V) {pool : Round → Finset (Protocol.SGVote V)}
    {etaSG : Round} {T : Finset (Block V)} {Hon : Finset V} {r : Round}
    {Can D : Block V}
    (hal : Proofs.Optimistic.SupportAligned pool etaSG T Hon r Can)
    (hD : Block.preceq D Can = false) :
    E.electorate.weightOf Hon +
        Protocol.sg_support E pool etaSG T r D ≤
      Protocol.W_r E pool etaSG r := by
  have hcompatible : SupportCompatible pool etaSG T Hon r Can :=
    SupportCompatible.of_supportAligned hal (by
      simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inl (Block.preceq_self Can))
  have hsub := honest_union_supporters_subset_represented
    (D := D) hcompatible
  have hmono := E.electorate.weightOf_mono hsub
  have hdisjoint := honest_disjoint_supporters_of_not_preceq hal hD
  have hunion : E.electorate.weightOf
      (Hon ∪ Protocol.sgSupporters pool etaSG T r D) =
      E.electorate.weightOf Hon +
        E.electorate.weightOf (Protocol.sgSupporters pool etaSG T r D) := by
    unfold Electorate.weightOf
    exact Finset.sum_union hdisjoint
  unfold Protocol.sg_support Protocol.W_r at *
  rw [← hunion]
  exact hmono

/-- The directed relative-majority walk remains below `Can` under only a
strict honest-weight majority. -/
theorem majority_fork_choice_preceq
    (S : Setup V) {pool : Round → Finset (Protocol.SGVote V)}
    {etaSG : Round} {T : Finset (Block V)} {Hon : Finset V} {r : Round}
    {Can anchor : Block V} {tree : Finset (Block V)}
    (hal : Proofs.Optimistic.SupportAligned pool etaSG T Hon r Can)
    (hmajority : Execution.HonestWeightMajority S Hon)
    (hanchor : Block.Preceq anchor Can) :
    Block.Preceq
      (Protocol.majority_fork_choice S.E pool etaSG T anchor tree r) Can := by
  have hdef : Protocol.majority_fork_choice S.E pool etaSG T anchor tree r =
      Protocol.ghost anchor tree (Protocol.sg_support S.E pool etaSG T r)
        (fun B => decide (Protocol.W_r S.E pool etaSG r <
          2 * Protocol.sg_support S.E pool etaSG T r B)) := rfl
  rw [Block.Preceq, hdef]
  rcases ghost_eligible anchor tree
      (Protocol.sg_support S.E pool etaSG T r)
      (fun B => decide (Protocol.W_r S.E pool etaSG r <
        2 * Protocol.sg_support S.E pool etaSG T r B)) with heq | helig
  · rw [heq]
    exact hanchor
  · by_contra hno
    rw [Bool.not_eq_true] at hno
    simp only [decide_eq_true_eq] at helig
    have hdenom := honest_add_sg_support_le_W_r_of_not_preceq S.E hal hno
    have hsup := Proofs.Optimistic.sg_support_le_faulty S.E hal hno
    unfold Execution.HonestWeightMajority at hmajority
    omega


end HonestWeightMajority

end Protocol
end DecoupledConsensusModel

end
