import DecoupledConsensus.State.Proof.Invariants
import DecoupledConsensus.Store.Properties
import DecoupledConsensus.Store.Proof.Facts

namespace DecoupledConsensus

/-! # Store Proofs: invariants

Reachability and local section-3 invariants for stores generated from
`Store.genesis` by `Store.onBlock`. -/

variable {n : ℕ}

open scoped Block

namespace Store

/-- Accepted stores are ancestor-closed: accepting a block also means every
    parent-pointer ancestor of that block has already been accepted. -/
def AncestorClosed (S : Store n) : Prop :=
  ∀ {A B : Block n}, Contains S B → A ≼ B → Contains S A

lemma genesis_F_ancestor_J : (Store.genesis n).F ≼ (Store.genesis n).J := by
  exact .refl _

lemma addEntry_F_ancestor_J {S : Store n} {e : StoreEntry n}
    (h : S.F ≼ S.J) : (S.addEntry e).F ≼ (S.addEntry e).J := by
  simpa [addEntry] using h

lemma addEntry_F_eq {S : Store n} {e : StoreEntry n} :
    (S.addEntry e).F = S.F := by
  rfl

lemma updateJustified_F_eq {S : Store n} {J' : Block n} {h' : ℕ} :
    (S.updateJustified J' h').F = S.F := by
  cases hguard : S.shouldUpdateJustified J' h' <;>
    simp [updateJustified, hguard]

lemma shouldUpdateJustified_parts {S : Store n} {J' : Block n} {h' : ℕ}
    (hguard : S.shouldUpdateJustified J' h' = true) :
    S.containsBlockBool J' = true ∧
      Block.isAncestorOf S.F J' = true ∧
      keyGreater h' J' S.hj S.J = true := by
  have hparts :
      (S.containsBlockBool J' = true ∧
        Block.isAncestorOf S.F J' = true) ∧
        keyGreater h' J' S.hj S.J = true := by
    simpa [shouldUpdateJustified, Bool.and_eq_true] using hguard
  exact ⟨hparts.1.1, hparts.1.2, hparts.2⟩

lemma updateFinalized_J_eq {S : Store n} {F' : Block n} :
    (S.updateFinalized F').J = S.J := by
  cases hguard : S.shouldUpdateFinalized F' <;>
    simp [updateFinalized, hguard]

lemma updateJustified_F_ancestor_J {S : Store n} {J' : Block n} {h' : ℕ}
    (h : S.F ≼ S.J) :
    (S.updateJustified J' h').F ≼ (S.updateJustified J' h').J := by
  cases hguard : S.shouldUpdateJustified J' h'
  · simpa [updateJustified, hguard] using h
  · have hparts := shouldUpdateJustified_parts hguard
    have hFJ' : S.F ≼ J' :=
      (Block.isAncestorOf_eq_true_iff _ _).mp hparts.2.1
    simpa [updateJustified, hguard] using hFJ'

lemma updateFinalized_F_ancestor_J {S : Store n} {F' : Block n}
    (h : S.F ≼ S.J) :
    (S.updateFinalized F').F ≼ (S.updateFinalized F').J := by
  cases hguard : S.shouldUpdateFinalized F'
  · simpa [updateFinalized, hguard] using h
  · have hparts :
        (Block.isStrictAncestorOf S.F F' = true ∧
          Block.isAncestorOf F' S.J = true) ∧
          S.isViableBool F' = true := by
      simpa [shouldUpdateFinalized, Bool.and_eq_true] using hguard
    have hFJ : F' ≼ S.J :=
      (Block.isAncestorOf_eq_true_iff _ _).mp hparts.1.2
    simpa [updateFinalized, hguard] using hFJ

lemma updateFinalized_F_monotone {S : Store n} {F' : Block n} :
    S.F ≼ (S.updateFinalized F').F := by
  cases hguard : S.shouldUpdateFinalized F'
  · simpa [updateFinalized, hguard] using (Block.Ancestor.refl S.F)
  · have hparts :
        (Block.isStrictAncestorOf S.F F' = true ∧
          Block.isAncestorOf F' S.J = true) ∧
          S.isViableBool F' = true := by
      simpa [shouldUpdateFinalized, Bool.and_eq_true] using hguard
    have hStrict := (Block.isStrictAncestorOf_eq_true_iff _ _).mp hparts.1.1
    simpa [updateFinalized, hguard] using hStrict.1

lemma keyGreater_height_ge {h' h : ℕ} {J' J : Block n}
    (hkey : keyGreater h' J' h J = true) : h ≤ h' := by
  unfold keyGreater at hkey
  by_cases hlt : h < h'
  · omega
  · have hparts : h = h' ∧ J.id < J'.id := by
      simpa [hlt, Bool.and_eq_true] using hkey
    omega

lemma KeyLE.refl (h : ℕ) (J : Block n) : KeyLE h J h J := by
  exact Or.inr ⟨rfl, le_rfl⟩

lemma KeyLE.trans {h₁ h₂ h₃ : ℕ} {J₁ J₂ J₃ : Block n}
    (h12 : KeyLE h₁ J₁ h₂ J₂) (h23 : KeyLE h₂ J₂ h₃ J₃) :
    KeyLE h₁ J₁ h₃ J₃ := by
  rcases h12 with h12 | ⟨hh12, hJ12⟩
  · rcases h23 with h23 | ⟨hh23, _⟩
    · exact Or.inl (Nat.lt_trans h12 h23)
    · subst hh23
      exact Or.inl h12
  · rcases h23 with h23 | ⟨hh23, hJ23⟩
    · subst hh12
      exact Or.inl h23
    · subst hh12
      subst hh23
      exact Or.inr ⟨rfl, le_trans hJ12 hJ23⟩

lemma keyGreater_keyLE {h' h : ℕ} {J' J : Block n}
    (hkey : keyGreater h' J' h J = true) : KeyLE h J h' J' := by
  unfold keyGreater at hkey
  by_cases hlt : h < h'
  · exact Or.inl hlt
  · have hparts : h = h' ∧ J.id < J'.id := by
      simpa [hlt, Bool.and_eq_true] using hkey
    exact Or.inr ⟨hparts.1, Nat.le_of_lt hparts.2⟩

lemma addEntry_hj_eq {S : Store n} {e : StoreEntry n} :
    (S.addEntry e).hj = S.hj := by
  rfl

lemma updateJustified_hj_mono {S : Store n} {J' : Block n} {h' : ℕ} :
    S.hj ≤ (S.updateJustified J' h').hj := by
  cases hguard : S.shouldUpdateJustified J' h'
  · simp [updateJustified, hguard]
  · have hparts := shouldUpdateJustified_parts hguard
    simpa [updateJustified, hguard] using keyGreater_height_ge hparts.2.2

lemma updateJustified_key_mono {S : Store n} {J' : Block n} {h' : ℕ} :
    KeyLE S.hj S.J (S.updateJustified J' h').hj
      (S.updateJustified J' h').J := by
  cases hguard : S.shouldUpdateJustified J' h'
  · simpa [updateJustified, hguard] using KeyLE.refl S.hj S.J
  · have hparts := shouldUpdateJustified_parts hguard
    simpa [updateJustified, hguard] using keyGreater_keyLE hparts.2.2

lemma updateFinalized_hj_eq {S : Store n} {F' : Block n} :
    (S.updateFinalized F').hj = S.hj := by
  cases hguard : S.shouldUpdateFinalized F' <;>
    simp [updateFinalized, hguard]

lemma addEntry_hmax_mono {S : Store n} {e : StoreEntry n} :
    S.hmax ≤ (S.addEntry e).hmax := by
  simpa [addEntry] using Nat.le_max_left S.hmax e.height

lemma updateJustified_hmax_eq {S : Store n} {J' : Block n} {h' : ℕ} :
    (S.updateJustified J' h').hmax = S.hmax := by
  cases hguard : S.shouldUpdateJustified J' h' <;>
    simp [updateJustified, hguard]

lemma updateFinalized_hmax_eq {S : Store n} {F' : Block n} :
    (S.updateFinalized F').hmax = S.hmax := by
  cases hguard : S.shouldUpdateFinalized F' <;>
    simp [updateFinalized, hguard]

lemma addEntry_contains_of_contains {S : Store n} {e : StoreEntry n} {B : Block n}
    (h : Contains S B) : Contains (S.addEntry e) B := by
  rcases h with ⟨x, hx, hEq⟩
  exact ⟨x, by simp [addEntry, hx], hEq⟩

lemma addEntry_contains_J {S : Store n} {e : StoreEntry n}
    (h : Contains S S.J) : Contains (S.addEntry e) (S.addEntry e).J := by
  simpa [addEntry] using addEntry_contains_of_contains (e := e) h

lemma updateJustified_contains_J {S : Store n} {J' : Block n} {h' : ℕ}
    (h : Contains S S.J) :
    Contains (S.updateJustified J' h') (S.updateJustified J' h').J := by
  cases hguard : S.shouldUpdateJustified J' h'
  · simpa [updateJustified, hguard] using h
  · have hparts := shouldUpdateJustified_parts hguard
    have hJ' : Contains S J' := contains_of_containsBlockBool hparts.1
    simpa [updateJustified, hguard] using hJ'

lemma updateFinalized_contains_J {S : Store n} {F' : Block n}
    (h : Contains S S.J) :
    Contains (S.updateFinalized F') (S.updateFinalized F').J := by
  cases hguard : S.shouldUpdateFinalized F' <;>
    simpa [updateFinalized, hguard] using h

lemma genesis_ancestorClosed : AncestorClosed (Store.genesis n) := by
  intro A B hB hAnc
  rcases hB with ⟨e, he, hEq⟩
  simp [Store.genesis, StoreEntry.genesis] at he
  subst e
  subst B
  cases hAnc
  exact ⟨StoreEntry.genesis n, by simp [Store.genesis], rfl⟩

lemma updateJustified_ancestorClosed {S : Store n} {J' : Block n} {h' : ℕ}
    (h : AncestorClosed S) : AncestorClosed (S.updateJustified J' h') := by
  intro A B hB hAnc
  cases hguard : S.shouldUpdateJustified J' h' <;>
    simpa [updateJustified, hguard] using
      h (by simpa [updateJustified, hguard] using hB) hAnc

lemma updateFinalized_ancestorClosed {S : Store n} {F' : Block n}
    (h : AncestorClosed S) : AncestorClosed (S.updateFinalized F') := by
  intro A B hB hAnc
  cases hguard : S.shouldUpdateFinalized F' <;>
    simpa [updateFinalized, hguard] using
      h (by simpa [updateFinalized, hguard] using hB) hAnc

lemma updateJustified_viable_unchanged {S : Store n} {J' R : Block n} {h' : ℕ}
    (h : S.isViableBool R = true) :
    (S.updateJustified J' h').isViableBool R = true := by
  cases hguard : S.shouldUpdateJustified J' h' <;>
    simpa [updateJustified, hguard] using h

lemma updateFinalized_viable_unchanged {S : Store n} {F' R : Block n}
    (h : S.isViableBool R = true) :
    (S.updateFinalized F').isViableBool R = true := by
  cases hguard : S.shouldUpdateFinalized F' <;>
    simpa [updateFinalized, hguard] using h

lemma addEntry_viable_preserved_by_descendant {S : Store n} {e : StoreEntry n}
    {R : Block n}
    (hViable : S.isViableBool R = true) (hAnc : R ≼ e.block) :
    (S.addEntry e).isViableBool R = true := by
  have hparts : S.containsBlockBool R = true ∧
      S.entries.any (fun e =>
        decide (S.heightThreshold ≤ e.height) && Block.isAncestorOf R e.block) = true := by
    simpa [isViableBool, Bool.and_eq_true] using hViable
  have hR : Contains S R := contains_of_containsBlockBool hparts.1
  have hR' : (S.addEntry e).containsBlockBool R = true :=
    containsBlockBool_of_contains (addEntry_contains_of_contains hR)
  rcases highDescendant_of_isViableBool hViable with
    ⟨w, hw, hwHeight, hwAnc⟩
  by_cases hStillHigh : (S.addEntry e).heightThreshold ≤ w.height
  · exact isViableBool_of_entry_ancestor_height hR'
      (by simp [addEntry, hw]) hwAnc hStillHigh
  · have heHigh : (S.addEntry e).heightThreshold ≤ e.height := by
      by_cases hle : S.hmax ≤ e.height
      · simp [heightThreshold, addEntry, max_eq_right hle]
      · have hge : e.height ≤ S.hmax := Nat.le_of_lt (Nat.lt_of_not_ge hle)
        have hmax : max S.hmax e.height = S.hmax := max_eq_left hge
        have hStill : (S.addEntry e).heightThreshold ≤ w.height := by
          simpa [heightThreshold, addEntry, hmax] using hwHeight
        exact False.elim (hStillHigh hStill)
    exact isViableBool_of_entry_ancestor_height hR'
      (by simp [addEntry]) hAnc heHigh

lemma addEntry_viable_preserved_of_hmax_eq {S : Store n} {e : StoreEntry n}
    {R : Block n}
    (hViable : S.isViableBool R = true)
    (hHmax : (S.addEntry e).hmax = S.hmax) :
    (S.addEntry e).isViableBool R = true := by
  have hparts : S.containsBlockBool R = true ∧
      S.entries.any (fun e =>
        decide (S.heightThreshold ≤ e.height) && Block.isAncestorOf R e.block) = true := by
    simpa [isViableBool, Bool.and_eq_true] using hViable
  have hR : Contains S R := contains_of_containsBlockBool hparts.1
  have hR' : (S.addEntry e).containsBlockBool R = true :=
    containsBlockBool_of_contains (addEntry_contains_of_contains hR)
  rcases highDescendant_of_isViableBool hViable with
    ⟨w, hw, hwHeight, hwAnc⟩
  have hwHeight' : (S.addEntry e).heightThreshold ≤ w.height := by
    simpa [heightThreshold, hHmax] using hwHeight
  exact isViableBool_of_entry_ancestor_height hR'
    (by simp [addEntry, hw]) hwAnc hwHeight'

lemma addChild_ancestorClosed {S : Store n} {parent : Block n}
    {bid newSlot : ℕ} {votes : List (Vote n)}
    {entry : StoreEntry n}
    (hBlock : entry.block = Block.mk bid parent newSlot votes)
    (hClosed : AncestorClosed S) (hParent : Contains S parent) :
    AncestorClosed (S.addEntry entry) := by
  intro A B hB hAnc
  rcases hB with ⟨x, hx, hEq⟩
  have hxOr : x ∈ S.entries ∨ x = entry := by
    simpa [addEntry] using hx
  rcases hxOr with hxOld | hxNew
  · exact addEntry_contains_of_contains (hClosed ⟨x, hxOld, hEq⟩ hAnc)
  · subst x
    subst B
    rw [hBlock] at hAnc
    cases hAnc with
    | refl =>
        exact ⟨entry, by simp [addEntry], hBlock⟩
    | step hParentAnc =>
        exact addEntry_contains_of_contains (hClosed hParent hParentAnc)

/-- Genesis contains its justified root. -/
lemma genesis_contains_J : Contains (Store.genesis n) (Store.genesis n).J := by
  exact ⟨StoreEntry.genesis n, by simp [Store.genesis], by rfl⟩

/-- One successful `onBlock` step preserves the store invariant `F ≼ J`. -/
lemma onBlock_F_ancestor_J {S S' : Store n} {B : Block n}
    (h : S.F ≼ S.J) (hstep : S.onBlock B = some S') :
    S'.F ≼ S'.J := by
  unfold onBlock at hstep
  by_cases hContains : S.containsBlockBool B
  · simp [hContains] at hstep
    cases hstep
    exact h
  · simp [hContains] at hstep
    cases B with
    | genesis =>
        simp at hstep
    | mk bid parent newSlot votes =>
        cases hFind : S.findChain? parent with
        | none =>
            simp [hFind] at hstep
        | some parentChain =>
            by_cases hSlot : newSlot > parent.slot
            · simp [hFind, hSlot] at hstep
              let child := Block.mk bid parent newSlot votes
              by_cases hAnc : Block.isAncestorOf S.F child
              · simp [child, hAnc] at hstep
                let entry : StoreEntry n :=
                  { block := child
                    chain := Chain.extend parentChain bid newSlot votes hSlot }
                let σ' := entry.state
                let S1 := S.addEntry entry
                let S2 := S1.updateJustified σ'.J σ'.hj
                have hS1 : S1.F ≼ S1.J := addEntry_F_ancestor_J h
                have hS2 : S2.F ≼ S2.J :=
                  updateJustified_F_ancestor_J hS1
                cases hstep
                exact updateFinalized_F_ancestor_J hS2
              · simp [child, hAnc] at hstep
            · simp [hFind, hSlot] at hstep

/-- One successful `onBlock` step preserves executable viability of the
    store-finalized root. -/
lemma onBlock_F_viableBool {S S' : Store n} {B : Block n}
    (hF : S.isViableBool S.F = true) (hstep : S.onBlock B = some S') :
    S'.isViableBool S'.F = true := by
  unfold onBlock at hstep
  by_cases hContains : S.containsBlockBool B
  · simp [hContains] at hstep
    cases hstep
    exact hF
  · simp [hContains] at hstep
    cases B with
    | genesis =>
        simp at hstep
    | mk bid parent newSlot votes =>
        cases hFind : S.findChain? parent with
        | none =>
            simp [hFind] at hstep
        | some parentChain =>
            by_cases hSlot : newSlot > parent.slot
            · simp [hFind, hSlot] at hstep
              let child := Block.mk bid parent newSlot votes
              by_cases hAnc : Block.isAncestorOf S.F child
              · simp [child, hAnc] at hstep
                let entry : StoreEntry n :=
                  { block := child
                    chain := Chain.extend parentChain bid newSlot votes hSlot }
                let σ' := entry.state
                let S1 := S.addEntry entry
                let S2 := S1.updateJustified σ'.J σ'.hj
                have hAncEntry : S.F ≼ entry.block := by
                  simpa [entry, child] using
                    (Block.isAncestorOf_eq_true_iff _ _).mp hAnc
                have hS1 : S1.isViableBool S1.F = true := by
                  have h := addEntry_viable_preserved_by_descendant
                    (S := S) (e := entry) (R := S.F) hF hAncEntry
                  simpa [S1, addEntry] using h
                have hS2 : S2.isViableBool S2.F = true := by
                  have hF_eq : S2.F = S1.F := by
                    simp [S2, updateJustified_F_eq]
                  have h := updateJustified_viable_unchanged
                    (S := S1) (J' := σ'.J) (h' := σ'.hj) (R := S1.F) hS1
                  simpa [S2, hF_eq] using h
                have hFinal :
                    (S2.updateFinalized σ'.F).isViableBool
                      (S2.updateFinalized σ'.F).F = true := by
                  cases hFin : S2.shouldUpdateFinalized σ'.F
                  · simpa [updateFinalized, hFin] using hS2
                  · have hparts :
                        (Block.isStrictAncestorOf S2.F σ'.F = true ∧
                          Block.isAncestorOf σ'.F S2.J = true) ∧
                          S2.isViableBool σ'.F = true := by
                      simpa [shouldUpdateFinalized, Bool.and_eq_true] using hFin
                    simpa [updateFinalized, hFin] using hparts.2
                cases hstep
                exact hFinal
              · simp [child, hAnc] at hstep
            · simp [hFind, hSlot] at hstep

/-- One successful `onBlock` step preserves membership of the store justified
    root in the accepted tree. -/
lemma onBlock_contains_J {S S' : Store n} {B : Block n}
    (hJ : Contains S S.J) (hstep : S.onBlock B = some S') :
    Contains S' S'.J := by
  unfold onBlock at hstep
  by_cases hContains : S.containsBlockBool B
  · simp [hContains] at hstep
    cases hstep
    exact hJ
  · simp [hContains] at hstep
    cases B with
    | genesis =>
        simp at hstep
    | mk bid parent newSlot votes =>
        cases hFind : S.findChain? parent with
        | none =>
            simp [hFind] at hstep
        | some parentChain =>
            by_cases hSlot : newSlot > parent.slot
            · simp [hFind, hSlot] at hstep
              let child := Block.mk bid parent newSlot votes
              by_cases hAnc : Block.isAncestorOf S.F child
              · simp [child, hAnc] at hstep
                let entry : StoreEntry n :=
                  { block := child
                    chain := Chain.extend parentChain bid newSlot votes hSlot }
                let σ' := entry.state
                let S1 := S.addEntry entry
                let S2 := S1.updateJustified σ'.J σ'.hj
                have hS1 : Contains S1 S1.J := by
                  simpa [S1] using addEntry_contains_J (S := S) (e := entry) hJ
                have hS2 : Contains S2 S2.J := by
                  simpa [S2] using
                    updateJustified_contains_J
                      (S := S1) (J' := σ'.J) (h' := σ'.hj) hS1
                cases hstep
                simpa [S2] using
                  updateFinalized_contains_J (S := S2) (F' := σ'.F) hS2
              · simp [child, hAnc] at hstep
            · simp [hFind, hSlot] at hstep

/-- One successful `onBlock` step preserves accepted-tree ancestor closure. -/
lemma onBlock_ancestorClosed {S S' : Store n} {B : Block n}
    (hClosed : AncestorClosed S) (hstep : S.onBlock B = some S') :
    AncestorClosed S' := by
  unfold onBlock at hstep
  by_cases hContains : S.containsBlockBool B
  · simp [hContains] at hstep
    cases hstep
    exact hClosed
  · simp [hContains] at hstep
    cases B with
    | genesis =>
        simp at hstep
    | mk bid parent newSlot votes =>
        cases hFind : S.findChain? parent with
        | none =>
            simp [hFind] at hstep
        | some parentChain =>
            by_cases hSlot : newSlot > parent.slot
            · simp [hFind, hSlot] at hstep
              let child := Block.mk bid parent newSlot votes
              by_cases hAnc : Block.isAncestorOf S.F child
              · simp [child, hAnc] at hstep
                let entry : StoreEntry n :=
                  { block := child
                    chain := Chain.extend parentChain bid newSlot votes hSlot }
                let σ' := entry.state
                let S1 := S.addEntry entry
                let S2 := S1.updateJustified σ'.J σ'.hj
                have hParent : Contains S parent := findChain?_some_contains hFind
                have hBlock : entry.block = Block.mk bid parent newSlot votes := by
                  rfl
                have hS1 : AncestorClosed S1 := by
                  change AncestorClosed (S.addEntry entry)
                  exact addChild_ancestorClosed hBlock hClosed hParent
                have hS2 : AncestorClosed S2 :=
                  updateJustified_ancestorClosed hS1
                cases hstep
                exact updateFinalized_ancestorClosed hS2
              · simp [child, hAnc] at hstep
            · simp [hFind, hSlot] at hstep

/-- Reachable stores always maintain `F ≼ J`. -/
theorem reachable_F_ancestor_J {S : Store n}
    (hS : Reachable S) : S.F ≼ S.J := by
  induction hS with
  | genesis =>
      exact genesis_F_ancestor_J
  | onBlock hPrev hstep ih =>
      exact onBlock_F_ancestor_J ih hstep

/-- Reachable stores always keep the store-finalized root in the executable
    viable tree. -/
theorem reachable_F_viableBool {S : Store n}
    (hS : Reachable S) : S.isViableBool S.F = true := by
  induction hS with
  | genesis =>
      simp [Store.genesis, StoreEntry.genesis, isViableBool, containsBlockBool,
        findChain?, StoreEntry.chainAs?, heightThreshold, Block.isAncestorOf]
  | onBlock hPrev hstep ih =>
      exact onBlock_F_viableBool ih hstep

/-- Reachable stores keep the store-finalized root in the accepted tree. -/
theorem reachable_contains_F {S : Store n}
    (hS : Reachable S) : Contains S S.F := by
  have hViable := reachable_F_viableBool hS
  have hparts : S.containsBlockBool S.F = true ∧
      S.entries.any (fun e =>
        decide (S.heightThreshold ≤ e.height) && Block.isAncestorOf S.F e.block) = true := by
    simpa [isViableBool, Bool.and_eq_true] using hViable
  exact contains_of_containsBlockBool hparts.1

/-- Reachable stores keep the store-justified root in the accepted tree. -/
theorem reachable_contains_J {S : Store n}
    (hS : Reachable S) : Contains S S.J := by
  induction hS with
  | genesis =>
      exact genesis_contains_J
  | onBlock hPrev hstep ih =>
      exact onBlock_contains_J ih hstep

/-- Reachable stores have ancestor-closed accepted trees. -/
theorem reachable_ancestorClosed {S : Store n}
    (hS : Reachable S) : AncestorClosed S := by
  induction hS with
  | genesis =>
      exact genesis_ancestorClosed
  | onBlock hPrev hstep ih =>
      exact onBlock_ancestorClosed ih hstep

lemma addEntry_hj_succ_le_hmax {S : Store n} {e : StoreEntry n}
    (h : S.hj + 1 ≤ S.hmax) : (S.addEntry e).hj + 1 ≤ (S.addEntry e).hmax := by
  exact h.trans (addEntry_hmax_mono (S := S) (e := e))

lemma updateJustified_hj_succ_le_hmax {S : Store n} {J' : Block n} {h' : ℕ}
    (hOld : S.hj + 1 ≤ S.hmax) (hNew : h' + 1 ≤ S.hmax) :
    (S.updateJustified J' h').hj + 1 ≤ (S.updateJustified J' h').hmax := by
  cases hguard : S.shouldUpdateJustified J' h'
  · simpa [updateJustified, hguard] using hOld
  · simpa [updateJustified, hguard] using hNew

lemma updateFinalized_hj_succ_le_hmax {S : Store n} {F' : Block n}
    (h : S.hj + 1 ≤ S.hmax) :
    (S.updateFinalized F').hj + 1 ≤ (S.updateFinalized F').hmax := by
  cases hguard : S.shouldUpdateFinalized F' <;>
    simpa [updateFinalized, hguard] using h

/-- One successful `onBlock` step cannot move store finality away from the old
    finalized subtree. -/
lemma onBlock_F_monotone {S S' : Store n} {B : Block n}
    (hstep : S.onBlock B = some S') : S.F ≼ S'.F := by
  unfold onBlock at hstep
  by_cases hContains : S.containsBlockBool B
  · simp [hContains] at hstep
    cases hstep
    exact .refl _
  · simp [hContains] at hstep
    cases B with
    | genesis =>
        simp at hstep
    | mk bid parent newSlot votes =>
        cases hFind : S.findChain? parent with
        | none =>
            simp [hFind] at hstep
        | some parentChain =>
            by_cases hSlot : newSlot > parent.slot
            · simp [hFind, hSlot] at hstep
              let child := Block.mk bid parent newSlot votes
              by_cases hAnc : Block.isAncestorOf S.F child
              · simp [child, hAnc] at hstep
                let entry : StoreEntry n :=
                  { block := child
                    chain := Chain.extend parentChain bid newSlot votes hSlot }
                let σ' := entry.state
                let S1 := S.addEntry entry
                let S2 := S1.updateJustified σ'.J σ'.hj
                have hS2F : S2.F = S.F := by
                  simp [S2, S1, addEntry, updateJustified_F_eq]
                cases hstep
                simpa [hS2F] using
                  (updateFinalized_F_monotone (S := S2) (F' := σ'.F))
              · simp [child, hAnc] at hstep
            · simp [hFind, hSlot] at hstep

/-- Future execution from a reachable store remains reachable. -/
lemma Future.reachable_of_left {S T : Store n}
    (hS : Reachable S) (hFuture : Future S T) : Reachable T := by
  induction hFuture with
  | refl S =>
      exact hS
  | step hstep _ ih =>
      exact ih (Reachable.onBlock hS hstep)

/-- Local irreversibility of store finality across any future execution. -/
theorem future_F_ancestor {S T : Store n}
    (hFuture : Future S T) : S.F ≼ T.F := by
  induction hFuture with
  | refl S =>
      exact .refl _
  | step hstep _ ih =>
      exact Block.Ancestor.trans (onBlock_F_monotone hstep) ih

/-- Confirmed outputs in any future store stay below the earlier finalized
    root. This is the store-level fork-choice consistency statement: the
    boundary case roots confirmations at `J`, and reachable stores maintain
    `F ≼ J`. -/
theorem future_getConfirmed_descends_from_F {S T : Store n} {B : Block n}
    (hS : Reachable S) (hFuture : Future S T) (hB : B ∈ T.getConfirmed) :
    S.F ≼ B := by
  have hSF : S.F ≼ T.F := future_F_ancestor hFuture
  have hT : Reachable T := Future.reachable_of_left hS hFuture
  by_cases hBoundary : T.hmax = T.hj + 1
  · have hTJ : T.F ≼ T.J := reachable_F_ancestor_J hT
    have hJB : T.J ≼ B := getConfirmed_descends_from_J_of_boundary hBoundary hB
    exact Block.Ancestor.trans hSF (Block.Ancestor.trans hTJ hJB)
  · have hFB : T.F ≼ B := getConfirmed_descends_from_F_of_not_boundary hBoundary hB
    exact Block.Ancestor.trans hSF hFB

/-- In the non-boundary cascade branch, `F` viability gives at least one
    executable confirmed output. -/
theorem reachable_getConfirmed_nonempty_of_not_boundary {S : Store n}
    (hS : Reachable S) (hBoundary : S.hmax ≠ S.hj + 1) :
    ∃ B : Block n, B ∈ S.getConfirmed := by
  have hF : S.isViableBool S.F = true := reachable_F_viableBool hS
  have hRoot : S.isViableBool S.confirmationRoot = true := by
    simpa [confirmationRoot, hBoundary] using hF
  exact getConfirmed_nonempty_of_root_viableBool hRoot

/-- One successful `onBlock` step cannot decrease `hj`. -/
lemma onBlock_hj_mono {S S' : Store n} {B : Block n}
    (hstep : S.onBlock B = some S') : S.hj ≤ S'.hj := by
  unfold onBlock at hstep
  by_cases hContains : S.containsBlockBool B
  · simp [hContains] at hstep
    cases hstep
    exact le_rfl
  · simp [hContains] at hstep
    cases B with
    | genesis =>
        simp at hstep
    | mk bid parent newSlot votes =>
        cases hFind : S.findChain? parent with
        | none =>
            simp [hFind] at hstep
        | some parentChain =>
            by_cases hSlot : newSlot > parent.slot
            · simp [hFind, hSlot] at hstep
              let child := Block.mk bid parent newSlot votes
              by_cases hAnc : Block.isAncestorOf S.F child
              · simp [child, hAnc] at hstep
                let entry : StoreEntry n :=
                  { block := child
                    chain := Chain.extend parentChain bid newSlot votes hSlot }
                let σ' := entry.state
                let S1 := S.addEntry entry
                let S2 := S1.updateJustified σ'.J σ'.hj
                have hS1 : S1.hj = S.hj := by simp [S1, addEntry]
                have hS2 : S1.hj ≤ S2.hj := updateJustified_hj_mono
                cases hstep
                simpa [S2, S1, addEntry, updateFinalized_hj_eq, hS1] using hS2
              · simp [child, hAnc] at hstep
            · simp [hFind, hSlot] at hstep

/-- One successful `onBlock` step cannot decrease the lexicographic
    justification key `(hj, J.id)`. -/
lemma onBlock_key_mono {S S' : Store n} {B : Block n}
    (hstep : S.onBlock B = some S') : KeyLE S.hj S.J S'.hj S'.J := by
  unfold onBlock at hstep
  by_cases hContains : S.containsBlockBool B
  · simp [hContains] at hstep
    cases hstep
    exact KeyLE.refl _ _
  · simp [hContains] at hstep
    cases B with
    | genesis =>
        simp at hstep
    | mk bid parent newSlot votes =>
        cases hFind : S.findChain? parent with
        | none =>
            simp [hFind] at hstep
        | some parentChain =>
            by_cases hSlot : newSlot > parent.slot
            · simp [hFind, hSlot] at hstep
              let child := Block.mk bid parent newSlot votes
              by_cases hAnc : Block.isAncestorOf S.F child
              · simp [child, hAnc] at hstep
                let entry : StoreEntry n :=
                  { block := child
                    chain := Chain.extend parentChain bid newSlot votes hSlot }
                let σ' := entry.state
                let S1 := S.addEntry entry
                let S2 := S1.updateJustified σ'.J σ'.hj
                have hS1 : KeyLE S.hj S.J S1.hj S1.J := by
                  simp [S1, addEntry, KeyLE.refl]
                have hS2 : KeyLE S1.hj S1.J S2.hj S2.J :=
                  updateJustified_key_mono
                have hFinal :
                    KeyLE S2.hj S2.J
                      (S2.updateFinalized σ'.F).hj
                      (S2.updateFinalized σ'.F).J := by
                  cases hFin : S2.shouldUpdateFinalized σ'.F <;>
                    simp [updateFinalized, hFin, KeyLE.refl]
                cases hstep
                exact hS1.trans (hS2.trans hFinal)
              · simp [child, hAnc] at hstep
            · simp [hFind, hSlot] at hstep

/-- One successful `onBlock` step cannot decrease `hmax`. -/
lemma onBlock_hmax_mono {S S' : Store n} {B : Block n}
    (hstep : S.onBlock B = some S') : S.hmax ≤ S'.hmax := by
  unfold onBlock at hstep
  by_cases hContains : S.containsBlockBool B
  · simp [hContains] at hstep
    cases hstep
    exact le_rfl
  · simp [hContains] at hstep
    cases B with
    | genesis =>
        simp at hstep
    | mk bid parent newSlot votes =>
        cases hFind : S.findChain? parent with
        | none =>
            simp [hFind] at hstep
        | some parentChain =>
            by_cases hSlot : newSlot > parent.slot
            · simp [hFind, hSlot] at hstep
              let child := Block.mk bid parent newSlot votes
              by_cases hAnc : Block.isAncestorOf S.F child
              · simp [child, hAnc] at hstep
                let entry : StoreEntry n :=
                  { block := child
                    chain := Chain.extend parentChain bid newSlot votes hSlot }
                let σ' := entry.state
                let S1 := S.addEntry entry
                let S2 := S1.updateJustified σ'.J σ'.hj
                have hS1 : S.hmax ≤ S1.hmax := addEntry_hmax_mono
                cases hstep
                simpa [S2, S1, addEntry, updateJustified_hmax_eq,
                  updateFinalized_hmax_eq] using hS1
              · simp [child, hAnc] at hstep
            · simp [hFind, hSlot] at hstep

/-- Store justification height is monotone across any future execution. -/
theorem future_hj_mono {S T : Store n}
    (hFuture : Future S T) : S.hj ≤ T.hj := by
  induction hFuture with
  | refl _ =>
      exact le_rfl
  | step hstep _ ih =>
      exact (onBlock_hj_mono hstep).trans ih

/-- Store justification keys are lexicographically monotone across any future
    execution. -/
theorem future_key_mono {S T : Store n}
    (hFuture : Future S T) : KeyLE S.hj S.J T.hj T.J := by
  induction hFuture with
  | refl _ =>
      exact KeyLE.refl _ _
  | step hstep _ ih =>
      exact (onBlock_key_mono hstep).trans ih

/-- The store frontier `hmax` is monotone across any future execution. -/
theorem future_hmax_mono {S T : Store n}
    (hFuture : Future S T) : S.hmax ≤ T.hmax := by
  induction hFuture with
  | refl _ =>
      exact le_rfl
  | step hstep _ ih =>
      exact (onBlock_hmax_mono hstep).trans ih

/-- The store frontier height never outruns the maximum processed state
    height: every observed justified height came from a post-state whose height
    is at least one larger. -/
lemma onBlock_hj_succ_le_hmax {S S' : Store n} {B : Block n}
    (hGap : S.hj + 1 ≤ S.hmax) (hstep : S.onBlock B = some S') :
    S'.hj + 1 ≤ S'.hmax := by
  unfold onBlock at hstep
  by_cases hContains : S.containsBlockBool B
  · simp [hContains] at hstep
    cases hstep
    exact hGap
  · simp [hContains] at hstep
    cases B with
    | genesis =>
        simp at hstep
    | mk bid parent newSlot votes =>
        cases hFind : S.findChain? parent with
        | none =>
            simp [hFind] at hstep
        | some parentChain =>
            by_cases hSlot : newSlot > parent.slot
            · simp [hFind, hSlot] at hstep
              let child := Block.mk bid parent newSlot votes
              by_cases hAnc : Block.isAncestorOf S.F child
              · simp [child, hAnc] at hstep
                let entry : StoreEntry n :=
                  { block := child
                    chain := Chain.extend parentChain bid newSlot votes hSlot }
                let σ' := entry.state
                let S1 := S.addEntry entry
                let S2 := S1.updateJustified σ'.J σ'.hj
                have hS1 : S1.hj + 1 ≤ S1.hmax :=
                  addEntry_hj_succ_le_hmax hGap
                have hEntry : σ'.hj + 1 ≤ S1.hmax := by
                  have hlt : σ'.hj < entry.height := by
                    simpa [σ', StoreEntry.state, StoreEntry.height] using
                      chain_hj_lt_h entry.chain
                  have hle : entry.height ≤ S1.hmax := by
                    simpa [S1, addEntry] using Nat.le_max_right S.hmax entry.height
                  omega
                have hS2 : S2.hj + 1 ≤ S2.hmax :=
                  updateJustified_hj_succ_le_hmax hS1 hEntry
                cases hstep
                exact updateFinalized_hj_succ_le_hmax hS2
              · simp [child, hAnc] at hstep
            · simp [hFind, hSlot] at hstep

/-- One successful `onBlock` step preserves viability of `J` whenever the
    cascade boundary `hmax = hj + 1` holds. -/
lemma onBlock_J_viableBool_of_boundary {S S' : Store n} {B : Block n}
    (hClosed : AncestorClosed S)
    (hGap : S.hj + 1 ≤ S.hmax)
    (hJ : S.hmax = S.hj + 1 → S.isViableBool S.J = true)
    (hstep : S.onBlock B = some S')
    (hBoundary : S'.hmax = S'.hj + 1) :
    S'.isViableBool S'.J = true := by
  unfold onBlock at hstep
  by_cases hContains : S.containsBlockBool B
  · simp [hContains] at hstep
    cases hstep
    exact hJ hBoundary
  · simp [hContains] at hstep
    cases B with
    | genesis =>
        simp at hstep
    | mk bid parent newSlot votes =>
        cases hFind : S.findChain? parent with
        | none =>
            simp [hFind] at hstep
        | some parentChain =>
            by_cases hSlot : newSlot > parent.slot
            · simp [hFind, hSlot] at hstep
              let child := Block.mk bid parent newSlot votes
              by_cases hAnc : Block.isAncestorOf S.F child
              · simp [child, hAnc] at hstep
                let entry : StoreEntry n :=
                  { block := child
                    chain := Chain.extend parentChain bid newSlot votes hSlot }
                let σ' := entry.state
                let S1 := S.addEntry entry
                let S2 := S1.updateJustified σ'.J σ'.hj
                have hParent : Contains S parent := findChain?_some_contains hFind
                have hBlock : entry.block = Block.mk bid parent newSlot votes := by
                  rfl
                have hS1Closed : AncestorClosed S1 := by
                  change AncestorClosed (S.addEntry entry)
                  exact addChild_ancestorClosed hBlock hClosed hParent
                have hS1Boundary :
                    S1.hmax = S1.hj + 1 → S1.isViableBool S1.J = true := by
                  intro hBoundary1
                  have hOldLe : S.hmax ≤ S1.hmax := addEntry_hmax_mono
                  have hOldBoundary : S.hmax = S.hj + 1 := by
                    have hBoundary1' : S1.hmax = S.hj + 1 := by
                      simpa [S1, addEntry] using hBoundary1
                    omega
                  have hHmax : S1.hmax = S.hmax := by
                    have hBoundary1' : S1.hmax = S.hj + 1 := by
                      simpa [S1, addEntry] using hBoundary1
                    omega
                  have hOldV : S.isViableBool S.J = true := hJ hOldBoundary
                  have hPres := addEntry_viable_preserved_of_hmax_eq
                    (S := S) (e := entry) (R := S.J) hOldV hHmax
                  simpa [S1, addEntry] using hPres
                have hS2Boundary :
                    S2.hmax = S2.hj + 1 → S2.isViableBool S2.J = true := by
                  intro hBoundary2
                  cases hguard : S1.shouldUpdateJustified σ'.J σ'.hj
                  · have hBoundary1 : S1.hmax = S1.hj + 1 := by
                      simpa [S2, updateJustified, hguard] using hBoundary2
                    have hV := hS1Boundary hBoundary1
                    simpa [S2, updateJustified, hguard] using hV
                  · have hJAnc : σ'.J ≼ entry.block := by
                      simpa [σ', StoreEntry.state] using chain_J_le_L entry.chain
                    have hEntryContains : Contains S1 entry.block :=
                      ⟨entry, by simp [S1, addEntry], rfl⟩
                    have hJContains : Contains S1 σ'.J :=
                      hS1Closed hEntryContains hJAnc
                    have hJBool : S1.containsBlockBool σ'.J = true :=
                      containsBlockBool_of_contains hJContains
                    have hS1hmax : S1.hmax = σ'.hj + 1 := by
                      simpa [S2, updateJustified, hguard] using hBoundary2
                    have hHeight : S1.heightThreshold ≤ entry.height := by
                      have hlt : σ'.hj < entry.height := by
                        simpa [σ', StoreEntry.state, StoreEntry.height] using
                          chain_hj_lt_h entry.chain
                      simp [heightThreshold, hS1hmax]
                      omega
                    have hV : S1.isViableBool σ'.J = true :=
                      isViableBool_of_entry_ancestor_height hJBool
                        (by simp [S1, addEntry]) hJAnc hHeight
                    simpa [S2, updateJustified, hguard] using hV
                have hFinal :
                    (S2.updateFinalized σ'.F).hmax =
                        (S2.updateFinalized σ'.F).hj + 1 →
                    (S2.updateFinalized σ'.F).isViableBool
                        (S2.updateFinalized σ'.F).J = true := by
                  intro hBoundaryFinal
                  have hBoundary2 : S2.hmax = S2.hj + 1 := by
                    cases hFin : S2.shouldUpdateFinalized σ'.F <;>
                      simpa [updateFinalized, hFin] using hBoundaryFinal
                  have hV := hS2Boundary hBoundary2
                  cases hFin : S2.shouldUpdateFinalized σ'.F <;>
                    simpa [updateFinalized, hFin] using hV
                cases hstep
                exact hFinal hBoundary
              · simp [child, hAnc] at hstep
            · simp [hFind, hSlot] at hstep

/-- Reachable stores satisfy `hj + 1 ≤ hmax`. -/
theorem reachable_hj_succ_le_hmax {S : Store n}
    (hS : Reachable S) : S.hj + 1 ≤ S.hmax := by
  induction hS with
  | genesis =>
      simp [Store.genesis]
  | onBlock hPrev hstep ih =>
      exact onBlock_hj_succ_le_hmax ih hstep

/-- At the cascade boundary, reachable stores have viable `J`, so the
    `getConfirmed` walk-from root exists in the viable tree. -/
theorem reachable_J_viableBool_of_boundary {S : Store n}
    (hS : Reachable S) (hBoundary : S.hmax = S.hj + 1) :
    S.isViableBool S.J = true := by
  induction hS with
  | genesis =>
      simp [Store.genesis, StoreEntry.genesis, isViableBool, containsBlockBool,
        findChain?, StoreEntry.chainAs?, heightThreshold, Block.isAncestorOf]
  | onBlock hPrev hstep ih =>
      exact onBlock_J_viableBool_of_boundary
        (reachable_ancestorClosed hPrev)
        (reachable_hj_succ_le_hmax hPrev)
        ih hstep hBoundary

/-- Reachable stores always have at least one executable confirmed output. -/
theorem reachable_getConfirmed_nonempty {S : Store n}
    (hS : Reachable S) : ∃ B : Block n, B ∈ S.getConfirmed := by
  by_cases hBoundary : S.hmax = S.hj + 1
  · have hJ : S.isViableBool S.J = true :=
      reachable_J_viableBool_of_boundary hS hBoundary
    have hRoot : S.isViableBool S.confirmationRoot = true := by
      simpa [confirmationRoot, hBoundary] using hJ
    exact getConfirmed_nonempty_of_root_viableBool hRoot
  · exact reachable_getConfirmed_nonempty_of_not_boundary hS hBoundary

/-- Section-3 totality for the executable set-valued `getConfirmed`: every
    reachable store has at least one possible output, and any such output
    satisfies the candidate predicate. -/
theorem reachable_getConfirmed_total {S : Store n}
    (hS : Reachable S) :
    ∃ B : Block n, B ∈ S.getConfirmed ∧ ConfirmedCandidate S B := by
  obtain ⟨B, hB⟩ := reachable_getConfirmed_nonempty hS
  exact ⟨B, hB, getConfirmed_candidate hB⟩

end Store

end DecoupledConsensus
