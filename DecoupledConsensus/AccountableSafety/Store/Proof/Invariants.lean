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

end Store

end AccountableSafety
