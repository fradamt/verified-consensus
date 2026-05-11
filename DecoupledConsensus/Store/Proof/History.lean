import DecoupledConsensus.Store.Proof.Invariants

namespace DecoupledConsensus

/-! # Store Proofs: processed-history facts

This module keeps proof-side history predicates for section-3 statements whose
premises mention blocks or descriptors that have already been processed. The
executable `Store` stays compact: history is recovered from accepted entries
and from the `Future` relation rather than stored in protocol state. -/

variable {n : ℕ}

open scoped Block

namespace Store

/-- A processed block has offered the justified checkpoint `(C, h)` as its
    post-state `(J, hj)`. -/
def ProcessedJustification (S : Store n) (C : Block n) (h : ℕ) : Prop :=
  ∃ e ∈ S.entries, e.state.J = C ∧ e.state.hj = h

/-- The scoped hash/id injectivity needed to compare an external finalization
    witness against every accepted entry in a store. -/
def IdInjectiveAgainstStore (tip : Block n) (S : Store n) : Prop :=
  ∀ e, e ∈ S.entries → Block.IdInjectiveOnAncestors tip e.block

/-- `hmax` is exactly the maximum entry height and is attained by some entry. -/
def HMaxOk (S : Store n) : Prop :=
  (∀ e ∈ S.entries, e.height ≤ S.hmax) ∧
    ∃ e ∈ S.entries, e.height = S.hmax

lemma updateJustified_entries_eq {S : Store n} {J' : Block n} {h' : ℕ} :
    (S.updateJustified J' h').entries = S.entries := by
  cases hguard : S.shouldUpdateJustified J' h' <;>
    simp [updateJustified, hguard]

lemma updateFinalized_entries_eq {S : Store n} {F' : Block n} :
    (S.updateFinalized F').entries = S.entries := by
  cases hguard : S.shouldUpdateFinalized F' <;>
    simp [updateFinalized, hguard]

lemma updateJustified_hmaxOk {S : Store n} {J' : Block n} {h' : ℕ}
    (h : HMaxOk S) : HMaxOk (S.updateJustified J' h') := by
  simpa [HMaxOk, updateJustified_entries_eq, updateJustified_hmax_eq] using h

lemma updateFinalized_hmaxOk {S : Store n} {F' : Block n}
    (h : HMaxOk S) : HMaxOk (S.updateFinalized F') := by
  simpa [HMaxOk, updateFinalized_entries_eq, updateFinalized_hmax_eq] using h

lemma addEntry_hmaxOk {S : Store n} {e : StoreEntry n}
    (h : HMaxOk S) : HMaxOk (S.addEntry e) := by
  rcases h with ⟨hUpper, eMax, heMax, hMax⟩
  constructor
  · intro x hx
    have hxOldOrNew : x ∈ S.entries ∨ x = e := by
      simpa [addEntry] using hx
    rcases hxOldOrNew with hxOld | rfl
    · have hxLe := hUpper x hxOld
      simp [addEntry]
      omega
    · simp [addEntry]
  · by_cases hOldLe : S.hmax ≤ e.height
    · refine ⟨e, ?_, ?_⟩
      · simp [addEntry]
      · simp [addEntry, max_eq_right hOldLe]
    · have hNewLe : e.height ≤ S.hmax := Nat.le_of_lt (Nat.lt_of_not_ge hOldLe)
      refine ⟨eMax, ?_, ?_⟩
      · simp [addEntry, heMax]
      · simp [addEntry, max_eq_left hNewLe, hMax]

lemma genesis_hmaxOk : HMaxOk (Store.genesis n) := by
  constructor
  · intro e he
    have heq : e = StoreEntry.genesis n := by
      simpa [Store.genesis] using he
    subst e
    simp [Store.genesis, StoreEntry.genesis, StoreEntry.height, StoreEntry.state,
      stateOf, State.genesis]
  · refine ⟨StoreEntry.genesis n, ?_, ?_⟩
    · simp [Store.genesis]
    · simp [Store.genesis, StoreEntry.genesis, StoreEntry.height, StoreEntry.state,
        stateOf, State.genesis]

lemma onBlock_hmaxOk {S S' : Store n} {B : Block n}
    (h : HMaxOk S) (hstep : S.onBlock B = some S') : HMaxOk S' := by
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
                have hS1 : HMaxOk S1 := addEntry_hmaxOk h
                have hS2 : HMaxOk S2 := updateJustified_hmaxOk hS1
                cases hstep
                exact updateFinalized_hmaxOk hS2
              · simp [child, hAnc] at hstep
            · simp [hFind, hSlot] at hstep

/-- Reachable stores have an accurate, attained `hmax`. -/
theorem reachable_hmaxOk {S : Store n}
    (hS : Reachable S) : HMaxOk S := by
  induction hS with
  | genesis =>
      exact genesis_hmaxOk
  | onBlock hPrev hstep ih =>
      exact onBlock_hmaxOk ih hstep

lemma reachable_entry_height_le_hmax {S : Store n} (hS : Reachable S)
    {e : StoreEntry n} (he : e ∈ S.entries) : e.height ≤ S.hmax :=
  (reachable_hmaxOk hS).1 e he

lemma reachable_hmax_witness {S : Store n} (hS : Reachable S) :
    ∃ e ∈ S.entries, e.height = S.hmax :=
  (reachable_hmaxOk hS).2

lemma addEntry_processedJustification {S : Store n} {e : StoreEntry n}
    {C : Block n} {h : ℕ}
    (hProc : ProcessedJustification S C h) :
    ProcessedJustification (S.addEntry e) C h := by
  rcases hProc with ⟨w, hw, hJ, hhj⟩
  exact ⟨w, by simp [addEntry, hw], hJ, hhj⟩

lemma updateJustified_processedJustification {S : Store n}
    {J' C : Block n} {h' h : ℕ}
    (hProc : ProcessedJustification S C h) :
    ProcessedJustification (S.updateJustified J' h') C h := by
  simpa [ProcessedJustification, updateJustified_entries_eq] using hProc

lemma updateFinalized_processedJustification {S : Store n}
    {F' C : Block n} {h : ℕ}
    (hProc : ProcessedJustification S C h) :
    ProcessedJustification (S.updateFinalized F') C h := by
  simpa [ProcessedJustification, updateFinalized_entries_eq] using hProc

lemma onBlock_processedJustification {S S' : Store n} {B C : Block n} {h : ℕ}
    (hProc : ProcessedJustification S C h)
    (hstep : S.onBlock B = some S') :
    ProcessedJustification S' C h := by
  unfold onBlock at hstep
  by_cases hContains : S.containsBlockBool B
  · simp [hContains] at hstep
    cases hstep
    exact hProc
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
                have hS1 : ProcessedJustification S1 C h :=
                  addEntry_processedJustification hProc
                have hS2 : ProcessedJustification S2 C h :=
                  updateJustified_processedJustification hS1
                cases hstep
                exact updateFinalized_processedJustification hS2
              · simp [child, hAnc] at hstep
            · simp [hFind, hSlot] at hstep

lemma Future.processedJustification_of_left {S T : Store n} {C : Block n} {h : ℕ}
    (hProc : ProcessedJustification S C h) (hFuture : Future S T) :
    ProcessedJustification T C h := by
  induction hFuture with
  | refl _ =>
      exact hProc
  | step hstep _ ih =>
      exact ih (onBlock_processedJustification hProc hstep)

end Store

end DecoupledConsensus
