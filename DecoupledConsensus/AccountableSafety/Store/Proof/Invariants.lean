import DecoupledConsensus.AccountableSafety.State.Proof.Facts
import DecoupledConsensus.AccountableSafety.Store.Proof.Facts

namespace AccountableSafety

/-! # Store Proofs: invariants

Reachability and local section-3 invariants for stores generated from
`Store.genesis` by `Store.onBlock`. -/

variable {n : ℕ}

open scoped Block

namespace Store

/-- Stores reachable by replaying successful `onBlock` calls from genesis. -/
inductive Reachable : Store n → Prop
  | genesis : Reachable (Store.genesis n)
  | onBlock {S S' : Store n} {B : Block n}
      (hS : Reachable S) (hstep : S.onBlock B = some S') : Reachable S'

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

lemma updateJustified_F_ancestor_J {S : Store n} {J' : Block n} {h' : ℕ}
    (h : S.F ≼ S.J) :
    (S.updateJustified J' h').F ≼ (S.updateJustified J' h').J := by
  cases hguard : S.shouldUpdateJustified J' h'
  · simpa [updateJustified, hguard] using h
  · have hparts : Block.isAncestorOf S.F J' = true ∧
        keyGreater h' J' S.hj S.J = true := by
      simpa [shouldUpdateJustified, Bool.and_eq_true] using hguard
    have hFJ' : S.F ≼ J' :=
      (Block.isAncestorOf_eq_true_iff _ _).mp hparts.1
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

lemma addEntry_hj_eq {S : Store n} {e : StoreEntry n} :
    (S.addEntry e).hj = S.hj := by
  rfl

lemma updateJustified_hj_mono {S : Store n} {J' : Block n} {h' : ℕ} :
    S.hj ≤ (S.updateJustified J' h').hj := by
  cases hguard : S.shouldUpdateJustified J' h'
  · simp [updateJustified, hguard]
  · have hparts : Block.isAncestorOf S.F J' = true ∧
        keyGreater h' J' S.hj S.J = true := by
      simpa [shouldUpdateJustified, Bool.and_eq_true] using hguard
    simpa [updateJustified, hguard] using keyGreater_height_ge hparts.2

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

/-- Reachable stores always maintain `F ≼ J`. -/
theorem reachable_F_ancestor_J {S : Store n}
    (hS : Reachable S) : S.F ≼ S.J := by
  induction hS with
  | genesis =>
      exact genesis_F_ancestor_J
  | onBlock hPrev hstep ih =>
      exact onBlock_F_ancestor_J ih hstep

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

/-- Transitive future relation generated by zero or more successful
    `onBlock` calls. -/
inductive Future : Store n → Store n → Prop
  | refl (S : Store n) : Future S S
  | step {S S' S'' : Store n} {B : Block n}
      (hstep : S.onBlock B = some S') (hFuture : Future S' S'') :
      Future S S''

/-- Local irreversibility of store finality across any future execution. -/
theorem future_F_ancestor {S T : Store n}
    (hFuture : Future S T) : S.F ≼ T.F := by
  induction hFuture with
  | refl S =>
      exact .refl _
  | step hstep _ ih =>
      exact Block.Ancestor.trans (onBlock_F_monotone hstep) ih

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

end Store

end AccountableSafety
