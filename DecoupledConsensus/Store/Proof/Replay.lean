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

/-! ## Deterministic Entry Heights -/

/-- The derived state of a fixed block is independent of the particular `Chain`
    witness. `Chain` carries slot-order proofs; the executable transition does
    not depend on which proof term was used. -/
lemma chain_stateOf_eq {B : Block n} (c₁ c₂ : Chain n B) :
    stateOf c₁ = stateOf c₂ := by
  induction c₁ with
  | genesis =>
      cases c₂
      rfl
  | @extend parent c bid s vs hSlot ih =>
      cases c₂
      simp [stateOf]
      rw [ih]

lemma StoreEntry.height_eq_of_block_eq {e a : StoreEntry n}
    (hBlock : e.block = a.block) : e.height = a.height := by
  cases e with
  | mk eblock echain =>
      cases a with
      | mk ablock achain =>
          simp at hBlock
          subst ablock
          simp [StoreEntry.height, StoreEntry.state,
            chain_stateOf_eq echain achain]

lemma StoreEntry.height_eq_one_of_block_genesis {e : StoreEntry n}
    (hBlock : e.block = Block.genesis) : e.height = 1 := by
  cases e with
  | mk block chain =>
      cases chain
      · simp [StoreEntry.height, StoreEntry.state, stateOf, State.genesis]
      · simp at hBlock

lemma StoreEntry.slot_gt_of_block_eq_mk (e : StoreEntry n)
    {bid : BlockId} {parent : Block n} {s : ℕ} {vs : List (Vote n)}
    (hBlock : e.block = Block.mk bid parent s vs) : s > parent.slot := by
  cases e with
  | mk block chain =>
      cases chain with
      | genesis =>
          simp at hBlock
      | @extend parent₀ c bid₀ s₀ vs₀ hSlot =>
          injection hBlock with _ hParent hSlotEq _
          subst hParent
          subst hSlotEq
          exact hSlot

lemma Block.genesis_ancestor (B : Block n) : Block.genesis ≼ B := by
  induction B with
  | genesis => exact .refl _
  | mk _ parent _ _ ih => exact .step ih

lemma reachable_contains_genesis {S : Store n}
    (hS : Reachable S) : Contains S (Block.genesis : Block n) := by
  exact reachable_ancestorClosed hS (reachable_contains_F hS)
    (Block.genesis_ancestor S.F)

lemma reachable_entryAccepted_genesis {S : Store n}
    (hS : Reachable S) : EntryAcceptedIn S (StoreEntry.genesis n) := by
  rcases reachable_contains_genesis hS with ⟨e, he, hBlock⟩
  refine ⟨e, he, hBlock, ?_⟩
  have hHeight : e.height = 1 :=
    StoreEntry.height_eq_one_of_block_genesis hBlock
  simpa [StoreEntry.genesis, StoreEntry.height, StoreEntry.state, stateOf,
    State.genesis] using hHeight

/-! ## Executable Replay Reachability -/

lemma tryOnBlock_reachable {S : Store n} {B : Block n}
    (hS : Reachable S) : Reachable (S.tryOnBlock B) := by
  cases hstep : S.onBlock B with
  | none =>
      simpa [tryOnBlock, hstep] using hS
  | some S' =>
      simpa [tryOnBlock, hstep] using Reachable.onBlock hS hstep

lemma tryOnBlock_future {S : Store n} {B : Block n} :
    Future S (S.tryOnBlock B) := by
  cases hstep : S.onBlock B with
  | none =>
      simpa [tryOnBlock, hstep] using Future.refl S
  | some S' =>
      simpa [tryOnBlock, hstep] using
        Future.step hstep (Future.refl S')

lemma Future.trans {S T U : Store n}
    (hST : Future S T) (hTU : Future T U) : Future S U := by
  induction hST with
  | refl _ => exact hTU
  | step hstep _ ih => exact Future.step hstep (ih hTU)

lemma replayBlocksFrom_future :
    ∀ (blocks : List (Block n)) (S : Store n),
      Future S (blocks.foldl tryOnBlock S)
  | [], S => Future.refl S
  | B :: blocks, S =>
      Future.trans (tryOnBlock_future (S := S) (B := B))
        (replayBlocksFrom_future blocks (S.tryOnBlock B))

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

lemma tryOnBlock_entry_mem_of_mem {S : Store n} {B : Block n}
    {e : StoreEntry n} (he : e ∈ S.entries) :
    e ∈ (S.tryOnBlock B).entries := by
  cases hstep : S.onBlock B with
  | none =>
      simpa [tryOnBlock, hstep] using he
  | some S' =>
      by_cases hFresh : S.containsBlockBool B = false
      · obtain
          ⟨bid, parent, newSlot, votes, _hBlockEq, parentChain, _hFind, hSlot,
            _hAnc, _hResult⟩ := freshOnBlockStep_of_onBlock hFresh hstep
        subst B
        subst S'
        let entry : StoreEntry n :=
          { block := Block.mk bid parent newSlot votes
            chain := Chain.extend parentChain bid newSlot votes hSlot }
        let σ := entry.state
        let S1 := S.addEntry entry
        let S2 := S1.updateJustified σ.J σ.hj
        have heS1 : e ∈ S1.entries := by
          simpa [S1, addEntry] using Or.inl he
        have heFinal : e ∈ (S2.updateFinalized σ.F).entries := by
          simpa [S2, updateFinalized_entries_eq, updateJustified_entries_eq]
            using heS1
        simpa [tryOnBlock, hstep, entry, σ, S1, S2] using heFinal
      · have hContains : S.containsBlockBool B = true := by
          cases h : S.containsBlockBool B
          · exact False.elim (hFresh h)
          · rfl
        have hEq : S' = S := by
          unfold onBlock at hstep
          simpa [hContains] using hstep.symm
        subst S'
        simpa [tryOnBlock, hstep] using he

lemma tryOnBlock_contains_of_contains {S : Store n} {B A : Block n}
    (hA : Contains S A) : Contains (S.tryOnBlock B) A := by
  rcases hA with ⟨e, he, hBlock⟩
  exact ⟨e, tryOnBlock_entry_mem_of_mem he, hBlock⟩

lemma tryOnBlock_entryAccepted_of_contains {S : Store n} {B : Block n}
    (e : StoreEntry n) (hContains : Contains S e.block) :
    EntryAcceptedIn (S.tryOnBlock B) e := by
  rcases hContains with ⟨w, hw, hBlock⟩
  refine ⟨w, tryOnBlock_entry_mem_of_mem hw, hBlock, ?_⟩
  exact StoreEntry.height_eq_of_block_eq hBlock

lemma tryOnBlock_entryAccepted_of_ready {S : Store n}
    (hS : Reachable S) (e : StoreEntry n)
    (hParent : ∀ {bid : BlockId} {parent : Block n} {s : ℕ}
        {vs : List (Vote n)}, e.block = Block.mk bid parent s vs → Contains S parent)
    (hAnc : S.F ≼ e.block) :
    EntryAcceptedIn (S.tryOnBlock e.block) e := by
  by_cases hContainsBool : S.containsBlockBool e.block = true
  · exact tryOnBlock_entryAccepted_of_contains e
      (contains_of_containsBlockBool hContainsBool)
  · have hFresh : S.containsBlockBool e.block = false := by
      cases h : S.containsBlockBool e.block
      · rfl
      · exact False.elim (by simpa [h] using hContainsBool)
    cases hBlock : e.block with
    | genesis =>
        have hGenesis : S.containsBlockBool (Block.genesis : Block n) = true :=
          containsBlockBool_of_contains (reachable_contains_genesis hS)
        rw [hBlock] at hFresh
        rw [hGenesis] at hFresh
        cases hFresh
    | mk bid parent s vs =>
        have hParentContains : Contains S parent :=
          hParent hBlock
        have hParentBool : S.containsBlockBool parent = true :=
          containsBlockBool_of_contains hParentContains
        cases hFind : S.findChain? parent with
        | none =>
            simp [containsBlockBool, hFind] at hParentBool
        | some parentChain =>
            have hSlot : s > parent.slot :=
              StoreEntry.slot_gt_of_block_eq_mk e hBlock
            have hFreshConcrete :
                S.containsBlockBool (Block.mk bid parent s vs) = false := by
              simpa [hBlock] using hFresh
            have hAncConcrete : S.F ≼ Block.mk bid parent s vs := by
              simpa [hBlock] using hAnc
            have hAncBool : Block.isAncestorOf S.F (Block.mk bid parent s vs) = true :=
              (Block.isAncestorOf_eq_true_iff _ _).mpr hAncConcrete
            have hstep :
                S.onBlock e.block =
                  some
                    (let entry : StoreEntry n :=
                      { block := Block.mk bid parent s vs
                        chain := Chain.extend parentChain bid s vs hSlot }
                    let σ := entry.state
                    let S1 := S.addEntry entry
                    let S2 := S1.updateJustified σ.J σ.hj
                    S2.updateFinalized σ.F) := by
              simp [onBlock, hBlock, hFreshConcrete, hFind, hSlot, hAncBool]
            let entry : StoreEntry n :=
              { block := Block.mk bid parent s vs
                chain := Chain.extend parentChain bid s vs hSlot }
            let σ := entry.state
            let S1 := S.addEntry entry
            let S2 := S1.updateJustified σ.J σ.hj
            have hEntryMem : entry ∈ (S2.updateFinalized σ.F).entries := by
              have hMemS1 : entry ∈ S1.entries := by
                simp [S1, addEntry]
              simpa [S2, updateFinalized_entries_eq, updateJustified_entries_eq]
                using hMemS1
            refine ⟨entry, ?_, ?_, ?_⟩
            · have hEntries :
                  (S.tryOnBlock (Block.mk bid parent s vs)).entries =
                    (S2.updateFinalized σ.F).entries := by
                have hstepConcrete :
                    S.onBlock (Block.mk bid parent s vs) =
                      some (S2.updateFinalized σ.F) := by
                  simpa [hBlock, entry, σ, S1, S2] using hstep
                simp [tryOnBlock, hstepConcrete]
              rw [hEntries]
              exact hEntryMem
            · simp [entry, hBlock]
            · exact StoreEntry.height_eq_of_block_eq (by
                simpa [entry] using hBlock.symm)

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

lemma ReplayEntriesOf.entries_from_input
    {input : List (StoreEntry n)} {S : Store n}
    (hReplay : ReplayEntriesOf input S) :
    ∀ e : StoreEntry n, e ∈ S.entries → HasInputEntry input e := by
  intro e he
  rw [hReplay] at he
  have hProv := replayBlocks_entries_genesis_or_input
    (blocks := input.map StoreEntry.block) he
  rcases hProv with hGenesis | hInput
  · exact Or.inl hGenesis
  · rcases List.mem_map.mp hInput with ⟨a, ha, hBlock⟩
    right
    refine ⟨a, ha, ?_, ?_⟩
    · exact hBlock
    · exact StoreEntry.height_eq_of_block_eq hBlock

lemma ReplayEntriesOf.live_entries_from_input
    {input : List (StoreEntry n)} {S : Store n}
    (hReplay : ReplayEntriesOf input S) :
    ∀ e : StoreEntry n, e ∈ S.entries → S.F ≼ e.block → HasInputEntry input e :=
  fun e he _ => hReplay.entries_from_input e he

/-- Once component lemmas have identified the canonical store fields and shown
    that every common live input block is accepted, replay provenance supplies
    the reverse live-entry direction automatically. -/
theorem liveComplete_of_replay_components
    {input : List (StoreEntry n)} {summary : LiveSummary n} {S : Store n}
    (hReplay : ReplayEntriesOf input S)
    (hF : S.F = summary.F)
    (hJ : S.J = summary.J)
    (hhj : S.hj = summary.hj)
    (hhmax : S.hmax = summary.hmax)
    (hAccepted :
      ∀ e : StoreEntry n, e ∈ input → summary.F ≼ e.block → EntryAcceptedIn S e) :
    LiveComplete input summary S where
  reachable := hReplay.reachable
  F_eq := hF
  J_eq := hJ
  hj_eq := hhj
  hmax_eq := hhmax
  live_input_accepted := hAccepted
  live_entries_from_input := hReplay.live_entries_from_input

/-! ## Live Completeness Combination -/

private lemma liveComplete_matching_forward
    {input : List (StoreEntry n)} {summary : LiveSummary n}
    {S T : Store n}
    (hS : LiveComplete input summary S)
    (hT : LiveComplete input summary T)
    {e : StoreEntry n}
    (he : e ∈ S.entries) (hLive : S.F ≼ e.block) :
    HasMatchingEntry S T e := by
  rcases hS.live_entries_from_input e he hLive with hGenesis | hInput
  · rcases reachable_entryAccepted_genesis hT.reachable with
      ⟨eT, heT, hBlockT, hHeightT⟩
    refine ⟨eT, heT, ?_, ?_⟩
    · simpa [StoreEntry.genesis, hGenesis] using hBlockT
    · have hHeightE : e.height = (StoreEntry.genesis n).height := by
        exact StoreEntry.height_eq_of_block_eq (by
          simpa [StoreEntry.genesis, hGenesis])
      rw [hHeightT, hHeightE]
  · rcases hInput with ⟨a, ha, hBlockA, hHeightA⟩
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
