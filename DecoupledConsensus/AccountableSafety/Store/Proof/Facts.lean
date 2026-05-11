import DecoupledConsensus.AccountableSafety.Store.Model.Basic

namespace AccountableSafety

/-! # Store Proofs: basic facts

Facts connecting the executable store filters to the Prop-level predicates used
in section-3 statements. -/

variable {n : ℕ}

open scoped Block

namespace Block

/-- The executable ancestry test is sound and complete for parent-pointer
    ancestry. -/
lemma isAncestorOf_eq_true_iff (A B : Block n) :
    isAncestorOf A B = true ↔ A ≼ B := by
  induction B with
  | genesis =>
      constructor
      · intro h
        have hEq : A = Block.genesis := by
          simpa [isAncestorOf] using h
        subst A
        exact .refl _
      · intro h
        cases h
        simp [isAncestorOf]
  | mk bid parent s vs ih =>
      constructor
      · intro h
        by_cases hEq : A = Block.mk bid parent s vs
        · subst A
          exact .refl _
        · have hParent : isAncestorOf A parent = true := by
            simpa [isAncestorOf, hEq] using h
          exact .step ((ih).mp hParent)
      · intro h
        cases h with
        | refl =>
            simp [isAncestorOf]
        | step hParent =>
            have hParentBool : isAncestorOf A parent = true := (ih).mpr hParent
            by_cases hEq : A = Block.mk bid parent s vs
            · simp [isAncestorOf, hEq]
            · simp [isAncestorOf, hEq, hParentBool]

/-- Strict executable ancestry is sound and complete. -/
lemma isStrictAncestorOf_eq_true_iff (A B : Block n) :
    isStrictAncestorOf A B = true ↔ A ≼ B ∧ A ≠ B := by
  simp [isStrictAncestorOf, Bool.and_eq_true, isAncestorOf_eq_true_iff]

end Block

namespace Store

private lemma list_any_true {α : Type} {p : α → Bool} {l : List α}
    (h : l.any p = true) : ∃ a ∈ l, p a = true := by
  simpa using h

private lemma list_any_false_forall {α : Type} {p : α → Bool} {l : List α}
    (h : l.any p = false) : ∀ a ∈ l, p a = false := by
  simpa using h

/-- Membership in `getConfirmed` comes from an accepted entry satisfying the
    executable candidate predicate. -/
lemma getConfirmed_entry {S : Store n} {B : Block n}
    (h : B ∈ S.getConfirmed) :
    ∃ e ∈ S.entries, e.block = B ∧
      S.isConfirmedCandidateEntryBool e = true := by
  rcases (by
    simpa [getConfirmed] using h :
      ∃ e ∈ S.entries, S.isConfirmedCandidateEntryBool e = true ∧ e.block = B) with
    ⟨e, he, hcand, hEq⟩
  exact ⟨e, he, hEq, hcand⟩

/-- Every confirmed output is an accepted block. -/
lemma getConfirmed_contains {S : Store n} {B : Block n}
    (h : B ∈ S.getConfirmed) : Contains S B := by
  rcases getConfirmed_entry h with ⟨e, he, hEq, _⟩
  exact ⟨e, he, hEq⟩

/-- Every confirmed output passes the executable viable-tree filter. -/
lemma getConfirmed_viableBool {S : Store n} {B : Block n}
    (h : B ∈ S.getConfirmed) : S.isViableBool B = true := by
  rcases getConfirmed_entry h with ⟨e, _, hEq, hcand⟩
  subst B
  have hparts :
      (S.isViableBool e.block = true ∧
        Block.isAncestorOf S.confirmationRoot e.block = true) ∧
        decide (S.heightThreshold ≤ e.height) = true := by
    simpa [isConfirmedCandidateEntryBool, Bool.and_eq_true] using hcand
  exact hparts.1.1

/-- An executable leaf result is sound for entries that are known to be in the
    store. The membership premise avoids needing a separate lookup theorem for
    the `containsBlockBool` conjunct. -/
lemma isLeafBool_sound_of_mem {S : Store n} {e : StoreEntry n}
    (he : e ∈ S.entries) (hLeaf : S.isLeafBool e.block = true) :
    IsLeaf S e.block := by
  have hparts : S.containsBlockBool e.block = true ∧
      !S.hasStrictDescendantBool e.block = true := by
    simpa [isLeafBool, Bool.and_eq_true] using hLeaf
  have hNoDesc : S.hasStrictDescendantBool e.block = false := by
    cases hDesc : S.hasStrictDescendantBool e.block
    · rfl
    · simp [hDesc] at hparts
  constructor
  · exact ⟨e, he, rfl⟩
  · intro C hC hAnc
    by_contra hNe
    rcases hC with ⟨eC, heC, hEqC⟩
    have hAncEntry : e.block ≼ eC.block := by
      simpa [hEqC] using hAnc
    have hAncBool : Block.isAncestorOf e.block eC.block = true :=
      (Block.isAncestorOf_eq_true_iff _ _).mpr hAncEntry
    have hNeBool : decide (e.block ≠ eC.block) = true := by
      apply decide_eq_true
      intro hEqBlocks
      exact hNe (hEqC ▸ hEqBlocks.symm)
    have hpFalse := list_any_false_forall hNoDesc eC heC
    have hpTrue :
        (Block.isAncestorOf e.block eC.block &&
          decide (e.block ≠ eC.block)) = true := by
      simp [hAncBool, hNeBool]
    rw [hpTrue] at hpFalse
    cases hpFalse

/-- The executable viable-tree test is sound when the queried block is known
    to be accepted. -/
lemma isViableBool_sound_of_contains {S : Store n} {B : Block n}
    (hB : Contains S B) (hViable : S.isViableBool B = true) :
    Viable S B := by
  have hparts : S.containsBlockBool B = true ∧
      S.entries.any (fun e =>
        S.isViableLeafEntryBool e && Block.isAncestorOf B e.block) = true := by
    simpa [isViableBool, Bool.and_eq_true] using hViable
  rcases list_any_true hparts.2 with ⟨e, he, heViable⟩
  have heParts : S.isViableLeafEntryBool e = true ∧
      Block.isAncestorOf B e.block = true := by
    simpa [Bool.and_eq_true] using heViable
  have hLeafHeight : S.isLeafBool e.block = true ∧
      decide (S.heightThreshold ≤ e.height) = true := by
    simpa [isViableLeafEntryBool, Bool.and_eq_true] using heParts.1
  refine ⟨hB, e.block, ?_, ?_, ?_⟩
  · exact isLeafBool_sound_of_mem he hLeafHeight.1
  · exact (Block.isAncestorOf_eq_true_iff _ _).mp heParts.2
  · exact ⟨e, he, rfl, of_decide_eq_true hLeafHeight.2⟩

/-- Every confirmed output descends from the confirmation root. -/
lemma getConfirmed_root_ancestor {S : Store n} {B : Block n}
    (h : B ∈ S.getConfirmed) : S.confirmationRoot ≼ B := by
  rcases getConfirmed_entry h with ⟨e, _, hEq, hcand⟩
  subst B
  have hrootBool : Block.isAncestorOf S.confirmationRoot e.block = true := by
    have hparts :
        (S.isViableBool e.block = true ∧
          Block.isAncestorOf S.confirmationRoot e.block = true) ∧
          decide (S.heightThreshold ≤ e.height) = true := by
      simpa [isConfirmedCandidateEntryBool, Bool.and_eq_true] using hcand
    exact hparts.1.2
  exact (Block.isAncestorOf_eq_true_iff _ _).mp hrootBool

/-- Every confirmed output has height at least `hmax - 1`. -/
lemma getConfirmed_height {S : Store n} {B : Block n}
    (h : B ∈ S.getConfirmed) : HasHeightAtLeast S B S.heightThreshold := by
  rcases getConfirmed_entry h with ⟨e, he, hEq, hcand⟩
  subst B
  have hheightBool : decide (S.heightThreshold ≤ e.height) = true := by
    have hparts :
        (S.isViableBool e.block = true ∧
          Block.isAncestorOf S.confirmationRoot e.block = true) ∧
          decide (S.heightThreshold ≤ e.height) = true := by
      simpa [isConfirmedCandidateEntryBool, Bool.and_eq_true] using hcand
    exact hparts.2
  exact ⟨e, he, rfl, of_decide_eq_true hheightBool⟩

/-- Every output in the executable `getConfirmed` set satisfies the Prop-level
    confirmed-candidate predicate. -/
lemma getConfirmed_candidate {S : Store n} {B : Block n}
    (h : B ∈ S.getConfirmed) : ConfirmedCandidate S B := by
  exact ⟨
    isViableBool_sound_of_contains (getConfirmed_contains h)
      (getConfirmed_viableBool h),
    getConfirmed_root_ancestor h,
    getConfirmed_height h⟩

end Store

end AccountableSafety
