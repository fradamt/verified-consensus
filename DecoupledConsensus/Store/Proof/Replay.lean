import DecoupledConsensus.Store.Proof.Conditional

namespace DecoupledConsensus

/-! # Store Proofs: replay order surface

This module contains the replay-facing layer for Section 3 order independence.
The executable replay attempts every available block and leaves the store
unchanged when `onBlock` rejects. The remaining hard component lemmas should
prove `LiveComplete` for every valid parent-first replay of a fixed input.
-/

variable {n : ℕ}

open scoped Block

namespace Store

/-! ## Executable Replay Reachability -/

lemma tryOnBlock_reachable {S : Store n} {B : Block n}
    (hS : Reachable S) : Reachable (S.tryOnBlock B) := by
  cases hstep : S.onBlock B with
  | none =>
      simpa [tryOnBlock, hstep] using hS
  | some S' =>
      simpa [tryOnBlock, hstep] using Reachable.onBlock hS hstep

lemma replayBlocksFrom_reachable :
    ∀ (blocks : List (Block n)) (S : Store n),
      Reachable S → Reachable (blocks.foldl tryOnBlock S)
  | [], _, hS => hS
  | B :: blocks, S, hS =>
      replayBlocksFrom_reachable blocks (S.tryOnBlock B)
        (tryOnBlock_reachable hS)

lemma replayBlocks_reachable (blocks : List (Block n)) :
    Reachable (Store.replayBlocks (n := n) blocks) := by
  exact replayBlocksFrom_reachable blocks (Store.genesis n) Reachable.genesis

lemma ReplayOf.reachable {blocks : List (Block n)} {S : Store n}
    (hReplay : ReplayOf blocks S) : Reachable S := by
  rw [hReplay]
  exact replayBlocks_reachable blocks

lemma ReplayEntriesOf.reachable {input : List (StoreEntry n)} {S : Store n}
    (hReplay : ReplayEntriesOf input S) : Reachable S :=
  ReplayOf.reachable hReplay

/-! ## Basic Replay Provenance -/

lemma tryOnBlock_entries_old_or_new {S : Store n} {B : Block n}
    {e : StoreEntry n}
    (he : e ∈ (S.tryOnBlock B).entries) :
    e ∈ S.entries ∨ e.block = B := by
  cases hstep : S.onBlock B with
  | none =>
      left
      simpa [tryOnBlock, hstep] using he
  | some S' =>
      by_cases hFresh : S.containsBlockBool B = false
      · obtain
          ⟨bid, parent, newSlot, votes, _hBlockEq, parentChain, _hFind, hSlot,
            _hAnc, _hResult⟩ := freshOnBlockStep_of_onBlock hFresh hstep
        subst B
        subst S'
        have he' :
            e ∈
              (let entry : StoreEntry n :=
                { block := Block.mk bid parent newSlot votes
                  chain := Chain.extend parentChain bid newSlot votes hSlot }
              let σ := entry.state
              let S1 := S.addEntry entry
              let S2 := S1.updateJustified σ.J σ.hj
              S2.updateFinalized σ.F).entries := by
          simpa [tryOnBlock, hstep] using he
        let entry : StoreEntry n :=
          { block := Block.mk bid parent newSlot votes
            chain := Chain.extend parentChain bid newSlot votes hSlot }
        let σ := entry.state
        let S1 := S.addEntry entry
        let S2 := S1.updateJustified σ.J σ.hj
        have heOldOrNew : e ∈ S.entries ∨ e = entry := by
          have heS1' : e ∈ S1.entries := by
            simpa [S2, updateFinalized_entries_eq, updateJustified_entries_eq]
              using he'
          simpa [S1, addEntry] using heS1'
        rcases heOldOrNew with heOld | hNew
        · left
          exact heOld
        · right
          rw [hNew]
      · have hContains : S.containsBlockBool B = true := by
          cases h : S.containsBlockBool B
          · exact False.elim (hFresh h)
          · rfl
        have hEq : S' = S := by
          unfold onBlock at hstep
          simpa [hContains] using hstep.symm
        subst S'
        left
        simpa [tryOnBlock, hstep] using he

lemma replayBlocksFrom_entries_old_or_input :
    ∀ (blocks : List (Block n)) (S : Store n) {e : StoreEntry n},
      e ∈ (blocks.foldl tryOnBlock S).entries →
        e ∈ S.entries ∨ e.block ∈ blocks
  | [], S, e, he => Or.inl he
  | B :: blocks, S, e, he =>
      have hTail :=
        replayBlocksFrom_entries_old_or_input blocks (S.tryOnBlock B) he
      match hTail with
      | Or.inr hmem => Or.inr (by simp [hmem])
      | Or.inl hhead =>
          match tryOnBlock_entries_old_or_new hhead with
          | Or.inl hold => Or.inl hold
          | Or.inr hnew => Or.inr (by simp [hnew])

lemma replayBlocks_entries_genesis_or_input
    {blocks : List (Block n)} {e : StoreEntry n}
    (he : e ∈ (Store.replayBlocks (n := n) blocks).entries) :
    e.block = Block.genesis ∨ e.block ∈ blocks := by
  have h := replayBlocksFrom_entries_old_or_input blocks (Store.genesis n) he
  rcases h with hGenesis | hInput
  · left
    have hEq : e = StoreEntry.genesis n := by
      simpa [Store.genesis] using hGenesis
    rw [hEq]
    rfl
  · exact Or.inr hInput

/-! ## Live Completeness Combination -/

private lemma liveComplete_matching_forward
    {input : List (StoreEntry n)} {summary : LiveSummary n}
    {S T : Store n}
    (hS : LiveComplete input summary S)
    (hT : LiveComplete input summary T)
    {e : StoreEntry n}
    (he : e ∈ S.entries) (hLive : S.F ≼ e.block) :
    HasMatchingEntry S T e := by
  rcases hS.live_entries_from_input e he hLive with
    ⟨a, ha, hBlockA, hHeightA⟩
  have hLiveA : summary.F ≼ a.block := by
    rw [hBlockA]
    simpa [hS.F_eq] using hLive
  rcases hT.live_input_accepted a ha hLiveA with
    ⟨eT, heT, hBlockT, hHeightT⟩
  exact ⟨eT, heT, by rw [hBlockT, hBlockA], by rw [hHeightT, hHeightA]⟩

/-- Two stores that are complete for the same canonical live replay input are
    live-equivalent. This is the proof-composition point for the component
    lemmas about `F`, `J`, `hj`, `hmax`, and live-subtree acceptance. -/
theorem liveEquivalent_of_liveComplete
    {input : List (StoreEntry n)} {summary : LiveSummary n}
    {S T : Store n}
    (hS : LiveComplete input summary S)
    (hT : LiveComplete input summary T) :
    LiveEquivalent S T where
  F_eq := hS.F_eq.trans hT.F_eq.symm
  J_eq := hS.J_eq.trans hT.J_eq.symm
  hj_eq := hS.hj_eq.trans hT.hj_eq.symm
  hmax_eq := hS.hmax_eq.trans hT.hmax_eq.symm
  live_entries_forward := fun e he hLive =>
    liveComplete_matching_forward hS hT (e := e) he hLive
  live_entries_backward := fun e he hLive =>
    liveComplete_matching_forward hT hS (e := e) he hLive

/-- Shared live completeness is enough to make executable confirmed-output
    membership order-independent. -/
theorem liveComplete_getConfirmed
    {input : List (StoreEntry n)} {summary : LiveSummary n}
    {S T : Store n} {B : Block n}
    (hS : LiveComplete input summary S)
    (hT : LiveComplete input summary T) :
    B ∈ S.getConfirmed ↔ B ∈ T.getConfirmed := by
  exact liveEquivalent_getConfirmed hS.reachable hT.reachable
    (liveEquivalent_of_liveComplete hS hT)

end Store

end DecoupledConsensus
