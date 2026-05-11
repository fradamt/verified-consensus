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

end Store

end AccountableSafety
