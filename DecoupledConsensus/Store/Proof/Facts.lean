import DecoupledConsensus.Store.Model.Basic

namespace DecoupledConsensus

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

private lemma list_any_true_of_exists {α : Type} {p : α → Bool} {l : List α}
    (h : ∃ a ∈ l, p a = true) : l.any p = true := by
  simpa using h

private lemma findSome_chainAs_isSome_of_mem :
    ∀ {entries : List (StoreEntry n)} {e : StoreEntry n},
      e ∈ entries →
      (entries.findSome? fun x => x.chainAs? e.block).isSome = true := by
  intro entries e h
  induction entries with
  | nil =>
      simp at h
  | cons a entries ih =>
      have hOr : e = a ∨ e ∈ entries := by
        simpa [List.mem_cons] using h
      rcases hOr with hEq | hTail
      · subst a
        simp [List.findSome?, StoreEntry.chainAs?]
      · cases hHead : a.chainAs? e.block with
        | none =>
          have hTailSome := ih hTail
          simp [List.findSome?, hHead, hTailSome]
        | some c =>
            simp [List.findSome?, hHead]

private lemma findSome?_some_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {b : β}, l.findSome? f = some b → ∃ a ∈ l, f a = some b := by
  intro l
  induction l with
  | nil =>
      intro b h
      simp [List.findSome?] at h
  | cons a l ih =>
      intro b h
      cases hfa : f a with
      | none =>
          have htail : l.findSome? f = some b := by
            simpa [List.findSome?, hfa] using h
          rcases ih htail with ⟨x, hx, hfx⟩
          exact ⟨x, by simp [hx], hfx⟩
      | some b' =>
          have hb : b' = b := by
            simpa [List.findSome?, hfa] using h
          subst b'
          exact ⟨a, by simp, hfa⟩

/-- Any concrete store entry can be found by block lookup. -/
lemma containsBlockBool_of_entry_mem {S : Store n} {e : StoreEntry n}
    (he : e ∈ S.entries) : S.containsBlockBool e.block = true := by
  simpa [containsBlockBool, findChain?] using
    findSome_chainAs_isSome_of_mem (entries := S.entries) he

/-- Prop-level accepted-block membership implies executable membership. -/
lemma containsBlockBool_of_contains {S : Store n} {B : Block n}
    (h : Contains S B) : S.containsBlockBool B = true := by
  rcases h with ⟨e, he, hEq⟩
  subst B
  exact containsBlockBool_of_entry_mem he

/-- A successful chain lookup returns an accepted store block. -/
lemma findChain?_some_contains {S : Store n} {B : Block n} {c : Chain n B}
    (h : S.findChain? B = some c) : Contains S B := by
  have hfind :
      S.entries.findSome? (fun x : StoreEntry n => x.chainAs? B) = some c := by
    simpa [findChain?] using h
  rcases findSome?_some_mem (f := fun x : StoreEntry n => x.chainAs? B) hfind with
    ⟨e, he, hchain⟩
  by_cases hEq : e.block = B
  · exact ⟨e, he, hEq⟩
  · simp [StoreEntry.chainAs?, hEq] at hchain

/-- Executable accepted-block membership is sound for Prop-level membership. -/
lemma contains_of_containsBlockBool {S : Store n} {B : Block n}
    (h : S.containsBlockBool B = true) : Contains S B := by
  unfold containsBlockBool at h
  cases hfind : S.findChain? B with
  | none =>
      simp [hfind] at h
  | some c =>
      exact findChain?_some_contains hfind

/-- A block is executable-viable when it is accepted and has a high accepted
    descendant. -/
lemma isViableBool_of_entry_ancestor_height {S : Store n} {B : Block n}
    {e : StoreEntry n}
    (hB : S.containsBlockBool B = true)
    (he : e ∈ S.entries)
    (hAnc : B ≼ e.block)
    (hHeight : S.heightThreshold ≤ e.height) :
    S.isViableBool B = true := by
  have hHeightBool : decide (S.heightThreshold ≤ e.height) = true :=
    decide_eq_true hHeight
  have hAncBool : Block.isAncestorOf B e.block = true :=
    (Block.isAncestorOf_eq_true_iff _ _).mpr hAnc
  have hAny :
      S.entries.any (fun e =>
        decide (S.heightThreshold ≤ e.height) && Block.isAncestorOf B e.block) = true :=
    list_any_true_of_exists ⟨e, he, by simp [hHeightBool, hAncBool]⟩
  simp [isViableBool, hB, hAny]

/-- A high accepted entry is viable as a confirmed output candidate target. -/
lemma isViableBool_of_entry_height {S : Store n} {e : StoreEntry n}
    (he : e ∈ S.entries) (hHeight : S.heightThreshold ≤ e.height) :
    S.isViableBool e.block = true :=
  isViableBool_of_entry_ancestor_height
    (containsBlockBool_of_entry_mem he) he (Block.Ancestor.refl _) hHeight

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
        decide (S.heightThreshold ≤ e.height) && Block.isAncestorOf B e.block) = true := by
    simpa [isViableBool, Bool.and_eq_true] using hViable
  rcases list_any_true hparts.2 with ⟨e, he, heViable⟩
  have heParts : decide (S.heightThreshold ≤ e.height) = true ∧
      Block.isAncestorOf B e.block = true := by
    simpa [Bool.and_eq_true] using heViable
  refine ⟨hB, e.block, ?_, ?_, ?_⟩
  · exact ⟨e, he, rfl⟩
  · exact (Block.isAncestorOf_eq_true_iff _ _).mp heParts.2
  · exact ⟨e, he, rfl, of_decide_eq_true heParts.1⟩

/-- Executable viability supplies the high-descendant witness used by the
    store invariants. -/
lemma highDescendant_of_isViableBool {S : Store n} {B : Block n}
    (hViable : S.isViableBool B = true) :
    ∃ e ∈ S.entries, S.heightThreshold ≤ e.height ∧ B ≼ e.block := by
  have hparts : S.containsBlockBool B = true ∧
      S.entries.any (fun e =>
        decide (S.heightThreshold ≤ e.height) && Block.isAncestorOf B e.block) = true := by
    simpa [isViableBool, Bool.and_eq_true] using hViable
  rcases list_any_true hparts.2 with ⟨e, he, heViable⟩
  have heParts : decide (S.heightThreshold ≤ e.height) = true ∧
      Block.isAncestorOf B e.block = true := by
    simpa [Bool.and_eq_true] using heViable
  exact ⟨e, he, of_decide_eq_true heParts.1,
    (Block.isAncestorOf_eq_true_iff _ _).mp heParts.2⟩

/-- If an accepted entry passes the executable candidate predicate, its block
    is present in `getConfirmed`. -/
lemma mem_getConfirmed_of_entry_candidate {S : Store n} {e : StoreEntry n}
    (he : e ∈ S.entries)
    (hcand : S.isConfirmedCandidateEntryBool e = true) :
    e.block ∈ S.getConfirmed := by
  simpa [getConfirmed] using
    (show ∃ x ∈ S.entries, S.isConfirmedCandidateEntryBool x = true ∧ x.block = e.block from
      ⟨e, he, hcand, rfl⟩)

/-- If the confirmation root is viable, then the executable confirmed-output
    set is nonempty. -/
lemma getConfirmed_nonempty_of_root_viableBool {S : Store n}
    (hRoot : S.isViableBool S.confirmationRoot = true) :
    ∃ B : Block n, B ∈ S.getConfirmed := by
  have hparts : S.containsBlockBool S.confirmationRoot = true ∧
      S.entries.any (fun e =>
        decide (S.heightThreshold ≤ e.height) &&
          Block.isAncestorOf S.confirmationRoot e.block) = true := by
    simpa [isViableBool, Bool.and_eq_true] using hRoot
  rcases list_any_true hparts.2 with ⟨e, he, heRoot⟩
  have heParts : decide (S.heightThreshold ≤ e.height) = true ∧
      Block.isAncestorOf S.confirmationRoot e.block = true := by
    simpa [Bool.and_eq_true] using heRoot
  have hHeight : S.heightThreshold ≤ e.height := of_decide_eq_true heParts.1
  have hViable : S.isViableBool e.block = true :=
    isViableBool_of_entry_height he hHeight
  have hcand : S.isConfirmedCandidateEntryBool e = true := by
    simp [isConfirmedCandidateEntryBool, hViable, heParts.1, heParts.2]
  exact ⟨e.block, mem_getConfirmed_of_entry_candidate he hcand⟩

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

/-- In the non-boundary case, confirmed outputs descend from store `F`. -/
lemma getConfirmed_descends_from_F_of_not_boundary {S : Store n} {B : Block n}
    (hBoundary : S.hmax ≠ S.hj + 1) (h : B ∈ S.getConfirmed) :
    S.F ≼ B := by
  have hroot := getConfirmed_root_ancestor h
  simpa [confirmationRoot, hBoundary] using hroot

/-- At the height boundary, confirmed outputs descend from store `J`. -/
lemma getConfirmed_descends_from_J_of_boundary {S : Store n} {B : Block n}
    (hBoundary : S.hmax = S.hj + 1) (h : B ∈ S.getConfirmed) :
    S.J ≼ B := by
  have hroot := getConfirmed_root_ancestor h
  simpa [confirmationRoot, hBoundary] using hroot

end Store

end DecoupledConsensus
