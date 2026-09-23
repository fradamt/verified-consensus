module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal

@[expose] public section

/-!
# Ancestry lemmas (PROTOCOL.md#the-complete-protocol)

`⪯` is a computable structural walk over the second argument
(`Substrate/Blocks.lean:165`), not an inductive `Prop` with `refl`/`step`
constructors, so none of its order properties is free and `cases`/`induction`
cannot be run on it directly. The reasoning kit the proof map calls for
(§4.2 item 3) is proved here once:

* `preceq_self` — reflexivity;
* `preceq_trans` — transitivity;
* `preceq_of_prec` — `≺` implies `⪯`;
* `preceq_depth_le` — the measure that makes the last two work;
* `preceq_antisymm` — antisymmetry, from `depth` alone, with **no**
  well-formedness hypothesis (proof map §5 D6: the prior repo's `Block.WellFormed`
  and `Ancestor.slot_le` are not needed here);
* `preceq_linear` — two ancestors of a common block are comparable, the prior
  `Ancestor.linear` (proof map §4.1 node 10).

These are the only theorems in the project that are not about the protocol.
-/



namespace DecoupledConsensusModel
namespace Block

variable {V : Type} [DecidableEq V]

/-- §1 `B ⪯ B` (PROTOCOL.md#the-complete-protocol: "`B = C`, or `B` is an ancestor of `C`"). -/
theorem preceq_self (B : Block V) : Block.preceq B B = true := by
  cases B <;> simp [Block.preceq]

/-- §1 `B ≺ C` implies `B ⪯ C` (PROTOCOL.md#the-complete-protocol). -/
theorem preceq_of_prec {B C : Block V} (h : Block.prec B C = true) :
    Block.preceq B C = true := by
  rw [Block.prec, Bool.and_eq_true] at h
  exact h.2

/-- §1 `⪯` is transitive (PROTOCOL.md#the-complete-protocol). -/
theorem preceq_trans {A B C : Block V} (h₁ : Block.preceq A B = true)
    (h₂ : Block.preceq B C = true) : Block.preceq A C = true := by
  induction C with
  | genesis =>
      simp only [Block.preceq, decide_eq_true_eq] at h₂
      subst h₂
      exact h₁
  | node p _ _ _ _ _ _ ih =>
      simp only [Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at h₂
      rcases h₂ with h | h
      · subst h
        exact h₁
      · simp only [Block.preceq, Bool.or_eq_true]
        exact Or.inr (ih h)

/-- §1 an ancestor is no deeper than its descendant (PROTOCOL.md#the-complete-protocol). The
measure antisymmetry and linearity both run on. -/
theorem preceq_depth_le {B C : Block V} (h : Block.preceq B C = true) :
    B.depth ≤ C.depth := by
  induction C with
  | genesis =>
      simp only [Block.preceq, decide_eq_true_eq] at h
      subst h
      exact Nat.le_refl _
  | node p _ _ _ _ _ _ ih =>
      simp only [Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with h | h
      · subst h
        exact Nat.le_refl _
      · exact Nat.le_succ_of_le (ih h)

/-- §1 an ancestor at no smaller depth is the block itself (PROTOCOL.md#the-complete-protocol,
90). -/
theorem preceq_eq_of_depth_le {B C : Block V} (h : Block.preceq B C = true)
    (hd : C.depth ≤ B.depth) : B = C := by
  induction C with
  | genesis =>
      simp only [Block.preceq, decide_eq_true_eq] at h
      exact h
  | node p _ _ _ _ _ _ ih =>
      simp only [Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with h | h
      · exact h
      · exact absurd (preceq_depth_le h) (by simp only [Block.depth] at hd; omega)

/-- §1 `⪯` is antisymmetric (PROTOCOL.md#the-complete-protocol). Proved from `depth` alone: no
block well-formedness and no slot monotonicity are needed, which is where the
old formalization's `Block.WellFormed` development goes. -/
theorem preceq_antisymm {B C : Block V} (h₁ : Block.preceq B C = true)
    (h₂ : Block.preceq C B = true) : B = C :=
  preceq_eq_of_depth_le h₁ (preceq_depth_le h₂)

/-- §1 two ancestors of a common block are comparable (PROTOCOL.md#the-complete-protocol) —
the fact that makes "conflicting" the exact negation of "one is an ancestor of
the other". -/
theorem preceq_linear {X Y Z : Block V} (hX : Block.preceq X Z = true)
    (hY : Block.preceq Y Z = true) :
    Block.preceq X Y = true ∨ Block.preceq Y X = true := by
  induction Z with
  | genesis =>
      simp only [Block.preceq, decide_eq_true_eq] at hX hY
      subst hX
      subst hY
      exact Or.inl (preceq_self _)
  | node p _ _ _ _ _ _ ih =>
      simp only [Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at hX hY
      rcases hX with hX | hX
      · rcases hY with hY | hY
        · subst hX
          subst hY
          exact Or.inl (preceq_self _)
        · subst hX
          refine Or.inr ?_
          simp only [Block.preceq, Bool.or_eq_true]
          exact Or.inr hY
      · rcases hY with hY | hY
        · subst hY
          refine Or.inl ?_
          simp only [Block.preceq, Bool.or_eq_true]
          exact Or.inr hX
        · exact ih hX hY

/-- §1 two blocks on one chain are compatible (PROTOCOL.md#the-complete-protocol). -/
theorem compatible_of_preceq_common {X Y Z : Block V}
    (hX : Block.preceq X Z = true) (hY : Block.preceq Y Z = true) :
    Block.compatible X Y = true := by
  simp only [Block.compatible, Bool.or_eq_true]
  exact preceq_linear hX hY

end Block
end DecoupledConsensusModel

end
