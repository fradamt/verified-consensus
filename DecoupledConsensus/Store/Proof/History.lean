import DecoupledConsensus.Store.Proof.Invariants
import DecoupledConsensus.State.Proof.TargetHeight

namespace DecoupledConsensus

/-! # Store Proofs: processed-history facts

This module keeps proof-side history predicates for section-3 statements whose
premises mention blocks or descriptors that have already been processed. The
executable `Store` stays compact: history is recovered from accepted entries
and from the `Future` relation rather than stored in protocol state. -/

variable {n : ℕ}

open scoped Block

namespace Store

/-- The current store root is represented by some processed entry. -/
def CurrentProcessedJustification (S : Store n) : Prop :=
  ProcessedJustification S S.J S.hj

/-- Justification evidence derivable directly from an accepted store entry. -/
def JustificationEvidence (S : Store n) (C : Block n) (h : ℕ) : Prop :=
  ∃ entry : StoreEntry n, entry ∈ S.entries ∧
    entry.state.J = C ∧
    entry.state.hj = h ∧
    C ≼ entry.block ∧
    h < entry.height ∧
    ((h = 0 ∧ C = Block.genesis) ∨
      JustifyQuorumWitness (votesIncluded entry.chain) C h)

/-- A justification record also supplies the lighter processed-descriptor
    predicate used by basic store-history lemmas. -/
lemma JustificationRecord.processed {S : Store n} {C : Block n} {h : ℕ}
    (r : JustificationRecord S C h) : ProcessedJustification S C h :=
  ⟨r.entry, r.mem, r.target_eq, r.height_eq⟩

/-- A full justification record contains the entry-derived evidence. -/
lemma JustificationRecord.evidence {S : Store n} {C : Block n} {h : ℕ}
    (r : JustificationRecord S C h) : JustificationEvidence S C h :=
  ⟨r.entry, r.mem, r.target_eq, r.height_eq, r.target_ancestor,
    r.tip_height, r.witness⟩

/-- Every processed justification descriptor has all entry-derived evidence. -/
lemma ProcessedJustification.evidence {S : Store n} {C : Block n} {h : ℕ}
    (hProc : ProcessedJustification S C h) : JustificationEvidence S C h := by
  rcases hProc with ⟨e, he, hJ, hhj⟩
  have hJ_state : (stateOf e.chain).J = C := by
    simpa [StoreEntry.state] using hJ
  have hhj_state : (stateOf e.chain).hj = h := by
    simpa [StoreEntry.state] using hhj
  refine ⟨e, he, hJ, hhj, ?_, ?_, ?_⟩
  · simpa [hJ_state] using chain_J_le_L e.chain
  · have hlt := chain_hj_lt_h e.chain
    rw [hhj_state] at hlt
    simpa [StoreEntry.height, StoreEntry.state] using hlt
  · rcases chain_JWitness e.chain with hzero | hWit
    · left
      constructor
      · exact hhj_state.symm.trans hzero
      · have hJ_genesis := chain_HjZeroJGenesis e.chain hzero
        exact hJ_state.symm.trans hJ_genesis
    · right
      rcases hWit with ⟨Q, hQ, hVotes⟩
      refine ⟨Q, hQ, ?_⟩
      intro i hi
      obtain ⟨v, hv_mem, hv_val, hv_target, hv_height⟩ := hVotes i hi
      refine ⟨v, hv_mem, hv_val, ?_, ?_⟩
      · simpa [hJ_state] using hv_target
      · simpa [hhj_state] using hv_height

/-- Every processed justification descriptor can be upgraded to the
    certificate-level record expected by the Section 3 safety lemmas. The
    record is not extra protocol state; all fields are extracted from the
    accepted entry's chain.

    This is intentionally proof-side `noncomputable` witness extraction from a
    Prop-level existential; it has no effect on the executable store model. -/
noncomputable def ProcessedJustification.toRecord
    {S : Store n} {C : Block n} {h : ℕ}
    (hProc : ProcessedJustification S C h) : JustificationRecord S C h :=
  let entry := Classical.choose hProc.evidence
  let rest := Classical.choose_spec hProc.evidence
  { entry := entry
    mem := rest.1
    target_eq := rest.2.1
    height_eq := rest.2.2.1
    target_ancestor := rest.2.2.2.1
    tip_height := rest.2.2.2.2.1
    witness := rest.2.2.2.2.2 }

/-- Justification records expose the target-height fact derived from the
    Section-2 state-machine freshness invariant. -/
lemma JustificationRecord.target_height
    {S : Store n} {C : Block n} {h : ℕ}
    (r : JustificationRecord S C h) :
    (h = 0 ∧ C = Block.genesis) ∨
      (stateOf (r.entry.chain.subchain r.target_ancestor)).h = h := by
  exact chain_justified_target_height r.entry.chain
    (by simpa [StoreEntry.state] using r.target_eq)
    (by simpa [StoreEntry.state] using r.height_eq)
    r.target_ancestor

/-- Non-genesis justification records expose the target state-height fact used
    by the safety arguments. The genesis convention is kept separate because
    `stateOf genesis` has height `1` while the pre-justification height is `0`. -/
lemma JustificationRecord.target_height_of_ne_zero
    {S : Store n} {C : Block n} {h : ℕ}
    (r : JustificationRecord S C h) (h_ne : h ≠ 0) :
    (stateOf (r.entry.chain.subchain r.target_ancestor)).h = h := by
  rcases r.target_height with h_genesis | h_height
  · exact False.elim (h_ne h_genesis.1)
  · exact h_height

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

lemma genesis_currentProcessedJustification :
    CurrentProcessedJustification (Store.genesis n) := by
  refine ⟨StoreEntry.genesis n, ?_, ?_, ?_⟩
  · simp [Store.genesis]
  · simp [StoreEntry.state, StoreEntry.genesis, Store.genesis, stateOf,
      State.genesis]
  · simp [StoreEntry.state, StoreEntry.genesis, Store.genesis, stateOf,
      State.genesis]

lemma addEntry_currentProcessedJustification {S : Store n} {e : StoreEntry n}
    (hCur : CurrentProcessedJustification S) :
    CurrentProcessedJustification (S.addEntry e) := by
  simpa [CurrentProcessedJustification, addEntry] using
    addEntry_processedJustification (e := e) hCur

lemma addEntry_newProcessedJustification {S : Store n} {e : StoreEntry n} :
    ProcessedJustification (S.addEntry e) e.state.J e.state.hj := by
  exact ⟨e, by simp [addEntry], rfl, rfl⟩

lemma updateJustified_currentProcessedJustification {S : Store n}
    {J' : Block n} {h' : ℕ}
    (hCur : CurrentProcessedJustification S)
    (hNew : ProcessedJustification S J' h') :
    CurrentProcessedJustification (S.updateJustified J' h') := by
  cases hguard : S.shouldUpdateJustified J' h'
  · simpa [CurrentProcessedJustification, updateJustified, hguard] using hCur
  · simpa [CurrentProcessedJustification, updateJustified, hguard] using hNew

lemma updateFinalized_currentProcessedJustification {S : Store n}
    {F' : Block n}
    (hCur : CurrentProcessedJustification S) :
    CurrentProcessedJustification (S.updateFinalized F') := by
  cases hguard : S.shouldUpdateFinalized F' <;>
    simpa [CurrentProcessedJustification, updateFinalized, hguard] using hCur

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

lemma onBlock_currentProcessedJustification {S S' : Store n} {B : Block n}
    (hCur : CurrentProcessedJustification S)
    (hstep : S.onBlock B = some S') :
    CurrentProcessedJustification S' := by
  unfold onBlock at hstep
  by_cases hContains : S.containsBlockBool B
  · simp [hContains] at hstep
    cases hstep
    exact hCur
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
                have hS1 : CurrentProcessedJustification S1 :=
                  addEntry_currentProcessedJustification hCur
                have hNew : ProcessedJustification S1 σ'.J σ'.hj := by
                  simpa [S1, σ'] using
                    addEntry_newProcessedJustification (S := S) (e := entry)
                have hS2 : CurrentProcessedJustification S2 :=
                  updateJustified_currentProcessedJustification hS1 hNew
                cases hstep
                exact updateFinalized_currentProcessedJustification hS2
              · simp [child, hAnc] at hstep
            · simp [hFind, hSlot] at hstep

/-- Reachable stores have a processed entry witnessing the current `(J, hj)`. -/
theorem reachable_currentProcessedJustification {S : Store n}
    (hS : Reachable S) : CurrentProcessedJustification S := by
  induction hS with
  | genesis =>
      exact genesis_currentProcessedJustification
  | onBlock hPrev hstep ih =>
      exact onBlock_currentProcessedJustification ih hstep

/-- Reachable stores expose their current justified root as an entry-derived
    certificate record. Proof-side only: it chooses the entry promised by
    `reachable_currentProcessedJustification`. -/
noncomputable def reachable_currentJustificationRecord {S : Store n}
    (hS : Reachable S) : JustificationRecord S S.J S.hj :=
  (reachable_currentProcessedJustification hS).toRecord

/-- The entry-derived evidence for the current root is available on every
    reachable store. Target-height facts are derived from the witnessing
    entry chain when a full `JustificationRecord` is needed. -/
theorem reachable_currentJustificationEvidence {S : Store n}
    (hS : Reachable S) : JustificationEvidence S S.J S.hj :=
  (reachable_currentJustificationRecord hS).evidence

end Store

end DecoupledConsensus
