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

lemma StoreEntry.state_eq_of_block_eq {e a : StoreEntry n}
    (hBlock : e.block = a.block) : e.state = a.state := by
  cases e with
  | mk eblock echain =>
      cases a with
      | mk ablock achain =>
          simp at hBlock
          subst ablock
          simp [StoreEntry.state, chain_stateOf_eq echain achain]

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

private lemma list_findSome?_append_singleton_of_none {α β : Type}
    {l : List α} {f : α → Option β} {a : α}
    (h : l.findSome? f = none) :
    (l ++ [a]).findSome? f = f a := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      cases hx : f x with
      | none =>
          have hxs : xs.findSome? f = none := by
            simpa [hx] using h
          simp [hx, ih hxs]
      | some _ =>
          simp [hx] at h

lemma findChain?_addEntry_fresh {S : Store n} {e : StoreEntry n}
    (hFresh : S.containsBlockBool e.block = false) :
    (S.addEntry e).findChain? e.block = some e.chain := by
  unfold containsBlockBool at hFresh
  cases hFind : S.findChain? e.block with
  | none =>
      have hFindEntries :
          S.entries.findSome? (fun x : StoreEntry n => x.chainAs? e.block) = none := by
        simpa [findChain?] using hFind
      have hAppend := list_findSome?_append_singleton_of_none
        (l := S.entries) (f := fun x : StoreEntry n => x.chainAs? e.block)
        (a := e) hFindEntries
      simpa [findChain?, addEntry, StoreEntry.chainAs?] using hAppend
  | some _ =>
      simp [hFind] at hFresh

lemma findChain?_updateJustified {S : Store n} {B J' : Block n} {h' : ℕ} :
    (S.updateJustified J' h').findChain? B = S.findChain? B := by
  cases hguard : S.shouldUpdateJustified J' h' <;>
    simp [findChain?, updateJustified, hguard]

lemma findChain?_updateFinalized {S : Store n} {B F' : Block n} :
    (S.updateFinalized F').findChain? B = S.findChain? B := by
  cases hguard : S.shouldUpdateFinalized F' <;>
    simp [findChain?, updateFinalized, hguard]

lemma onBlock_acceptedBlockState_of_ready {S : Store n}
    (e : StoreEntry n)
    (hFresh : S.containsBlockBool e.block = false)
    (hParent : ∀ {bid : BlockId} {parent : Block n} {s : ℕ}
        {vs : List (Vote n)}, e.block = Block.mk bid parent s vs → Contains S parent)
    (hAnc : S.F ≼ e.block)
    (hNonGenesis : e.block ≠ Block.genesis) :
    ∃ S', S.onBlock e.block = some S' ∧ AcceptedBlockState S' e.block e.state := by
  cases hBlock : e.block with
  | genesis =>
      exact False.elim (hNonGenesis hBlock)
  | mk bid parent s vs =>
      have hParentContains : Contains S parent := hParent hBlock
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
          have hAncBool :
              Block.isAncestorOf S.F (Block.mk bid parent s vs) = true :=
            (Block.isAncestorOf_eq_true_iff _ _).mpr hAncConcrete
          let entry : StoreEntry n :=
            { block := Block.mk bid parent s vs
              chain := Chain.extend parentChain bid s vs hSlot }
          let σ := entry.state
          let S1 := S.addEntry entry
          let S2 := S1.updateJustified σ.J σ.hj
          let S' := S2.updateFinalized σ.F
          have hstep : S.onBlock e.block = some S' := by
            simp [onBlock, hBlock, hFreshConcrete, hFind, hSlot, hAncBool,
              S', entry, σ, S1, S2]
          refine ⟨S', by simpa [hBlock] using hstep, ?_⟩
          refine ⟨entry.chain, ?_, ?_⟩
          · have hLookupS1 : S1.findChain? entry.block = some entry.chain :=
              findChain?_addEntry_fresh (S := S) (e := entry)
                (by simpa [entry] using hFreshConcrete)
            have hLookupS' : S'.findChain? entry.block = some entry.chain := by
              simpa [S', S2, findChain?_updateFinalized,
                findChain?_updateJustified] using hLookupS1
            simpa [entry, hBlock] using hLookupS'
          · cases e with
            | mk block chain =>
                simp at hBlock
                subst block
                exact chain_stateOf_eq entry.chain chain

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

lemma tryOnBlock_F_old_or_entry (S : Store n) (e : StoreEntry n) :
    (S.tryOnBlock e.block).F = S.F ∨
      (S.tryOnBlock e.block).F = e.state.F := by
  cases hstep : S.onBlock e.block with
  | none =>
      left
      simp [tryOnBlock, hstep]
  | some S' =>
      by_cases hFresh : S.containsBlockBool e.block = false
      · obtain
          ⟨bid, parent, newSlot, votes, hBlockEq, parentChain, _hFind,
            hSlot, _hAnc, hResult⟩ := freshOnBlockStep_of_onBlock hFresh hstep
        let entry : StoreEntry n :=
          { block := Block.mk bid parent newSlot votes
            chain := Chain.extend parentChain bid newSlot votes hSlot }
        let σ := entry.state
        let S1 := S.addEntry entry
        let S2 := S1.updateJustified σ.J σ.hj
        have hS' : S' = S2.updateFinalized σ.F := by
          simpa [entry, σ, S1, S2] using hResult
        have hS2F : S2.F = S.F := by
          simp [S2, S1, addEntry, updateJustified_F_eq]
        have hStateF : σ.F = e.state.F := by
          have hState : entry.state = e.state := by
            apply StoreEntry.state_eq_of_block_eq
            simpa [entry] using hBlockEq.symm
          simpa [σ] using congrArg State.F hState
        cases hFin : S2.shouldUpdateFinalized σ.F
        · left
          simp [tryOnBlock, hstep, hS', updateFinalized, hFin, hS2F]
        · right
          have hFinal : (S2.updateFinalized σ.F).F = σ.F := by
            simp [updateFinalized, hFin]
          calc
            (S.tryOnBlock e.block).F = (S2.updateFinalized σ.F).F := by
              simp [tryOnBlock, hstep, hS']
            _ = σ.F := hFinal
            _ = e.state.F := hStateF
      · have hContains : S.containsBlockBool e.block = true := by
          cases h : S.containsBlockBool e.block
          · exact False.elim (hFresh h)
          · rfl
        have hEq : S' = S := by
          unfold onBlock at hstep
          simpa [hContains] using hstep.symm
        subst S'
        left
        simp [tryOnBlock, hstep]

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

lemma tryOnBlock_entryAccepted_preserved {S : Store n} {B : Block n}
    {e : StoreEntry n} (hAcc : EntryAcceptedIn S e) :
    EntryAcceptedIn (S.tryOnBlock B) e := by
  rcases hAcc with ⟨w, hw, hBlock, hHeight⟩
  exact ⟨w, tryOnBlock_entry_mem_of_mem hw, hBlock, hHeight⟩

lemma replayEntriesFrom_future :
    ∀ (input : List (StoreEntry n)) (S : Store n),
      Future S (input.foldl (fun S e => S.tryOnBlock e.block) S)
  | [], S => Future.refl S
  | e :: rest, S =>
      Future.trans (tryOnBlock_future (S := S) (B := e.block))
        (replayEntriesFrom_future rest (S.tryOnBlock e.block))

lemma replayEntriesFrom_entryAccepted_preserved :
    ∀ (input : List (StoreEntry n)) (S : Store n) (e : StoreEntry n),
      EntryAcceptedIn S e →
        EntryAcceptedIn (input.foldl (fun S a => S.tryOnBlock a.block) S) e
  | [], _, _, hAcc => hAcc
  | a :: rest, S, e, hAcc =>
      replayEntriesFrom_entryAccepted_preserved rest (S.tryOnBlock a.block) e
        (tryOnBlock_entryAccepted_preserved (B := a.block) hAcc)

lemma parent_relevant_of_child_relevant {F parent : Block n}
    {bid s : ℕ} {vs : List (Vote n)}
    (hRel : RelevantToFinal F (Block.mk bid parent s vs)) :
    RelevantToFinal F parent := by
  have hParentChild : parent ≼ Block.mk bid parent s vs :=
    Block.Ancestor.step (Block.Ancestor.refl parent)
  rcases hRel with hFChild | hChildF
  · rcases Block.Ancestor.linear hFChild hParentChild with hFParent | hParentF
    · exact Or.inl hFParent
    · exact Or.inr hParentF
  · exact Or.inr (Block.Ancestor.trans hParentChild hChildF)

private lemma Contains.of_entryAccepted {S : Store n} {e : StoreEntry n}
    (hAcc : EntryAcceptedIn S e) : Contains S e.block := by
  rcases hAcc with ⟨w, hw, hBlock, _⟩
  exact ⟨w, hw, hBlock⟩

lemma tryOnBlock_entryAccepted_of_parentReady_relevant {S T : Store n}
    {seen : List (StoreEntry n)} (hS : Reachable S) (hFuture : Future S T)
    (hSeen :
      ∀ p : StoreEntry n, p ∈ seen → RelevantToFinal T.F p.block →
        EntryAcceptedIn S p)
    (e : StoreEntry n)
    (hReady : ParentReadyIn (seen.map StoreEntry.block) e.block)
    (hRel : RelevantToFinal T.F e.block) :
    EntryAcceptedIn (S.tryOnBlock e.block) e := by
  cases hBlock : e.block with
  | genesis =>
      have hContains : Contains S e.block := by
        rw [hBlock]
        exact reachable_contains_genesis hS
      exact tryOnBlock_entryAccepted_of_contains e hContains
  | mk bid parent s vs =>
      have hReadyMk : parent = Block.genesis ∨
          parent ∈ seen.map StoreEntry.block := by
        simpa [ParentReadyIn, hBlock] using hReady
      have hParentContains : Contains S parent := by
        rcases hReadyMk with hGenesis | hSeenParent
        · rw [hGenesis]
          exact reachable_contains_genesis hS
        · rcases List.mem_map.mp hSeenParent with ⟨p, hp, hpBlock⟩
          have hRelParent :
              RelevantToFinal T.F parent := by
            have hRelChild :
                RelevantToFinal T.F (Block.mk bid parent s vs) := by
              simpa [hBlock] using hRel
            exact parent_relevant_of_child_relevant hRelChild
          have hAccParent : EntryAcceptedIn S p := hSeen p hp (by
            simpa [hpBlock] using hRelParent)
          have hContainsP : Contains S p.block :=
            Contains.of_entryAccepted hAccParent
          rcases hContainsP with ⟨w, hw, hWBlock⟩
          exact ⟨w, hw, by rw [hWBlock, hpBlock]⟩
      have hCurrentFinal : S.F ≼ T.F := future_F_ancestor hFuture
      have hChildRel :
          RelevantToFinal T.F (Block.mk bid parent s vs) := by
        simpa [hBlock] using hRel
      rcases hChildRel with hFinalChild | hChildFinal
      · have hAnc : S.F ≼ e.block := by
          rw [hBlock]
          exact Block.Ancestor.trans hCurrentFinal hFinalChild
        simpa [hBlock] using
          tryOnBlock_entryAccepted_of_ready hS e (fun h => by
          rw [hBlock] at h
          injection h with _ hParentEq _ _
          simpa [hParentEq] using hParentContains) hAnc
      · rcases Block.Ancestor.linear hCurrentFinal hChildFinal with
          hCurrentChild | hChildCurrent
        · have hAnc : S.F ≼ e.block := by
            rw [hBlock]
            exact hCurrentChild
          simpa [hBlock] using
            tryOnBlock_entryAccepted_of_ready hS e (fun h => by
            rw [hBlock] at h
            injection h with _ hParentEq _ _
            simpa [hParentEq] using hParentContains) hAnc
        · have hContains : Contains S e.block := by
            have hChildCurrent' : e.block ≼ S.F := by
              simpa [hBlock] using hChildCurrent
            exact reachable_ancestorClosed hS (reachable_contains_F hS)
              hChildCurrent'
          exact tryOnBlock_entryAccepted_of_contains e hContains

lemma replayEntriesFrom_eq_replayBlocksFrom_map
    (input : List (StoreEntry n)) (S : Store n) :
    (input.map StoreEntry.block).foldl tryOnBlock S =
      input.foldl (fun S e => S.tryOnBlock e.block) S := by
  induction input generalizing S with
  | nil => rfl
  | cons e rest ih =>
      simp [ih]

lemma replayEntriesFrom_accepts_relevant_aux :
    ∀ (todo seen : List (StoreEntry n)) (S : Store n),
      Reachable S →
        ParentFirstFrom (seen.map StoreEntry.block) (todo.map StoreEntry.block) →
          (∀ p : StoreEntry n, p ∈ seen →
            RelevantToFinal
              (todo.foldl (fun S e => S.tryOnBlock e.block) S).F p.block →
              EntryAcceptedIn S p) →
            ∀ e : StoreEntry n, e ∈ seen ++ todo →
              RelevantToFinal
                (todo.foldl (fun S e => S.tryOnBlock e.block) S).F e.block →
              EntryAcceptedIn
                (todo.foldl (fun S e => S.tryOnBlock e.block) S) e
  | [], seen, S, _hS, _hPF, hSeen, e, he, hRel => by
      have heSeen : e ∈ seen := by simpa using he
      exact hSeen e heSeen hRel
  | a :: rest, seen, S, hS, hPF, hSeen, e, he, hRel => by
      let S1 := S.tryOnBlock a.block
      have hHead : ParentReadyIn (seen.map StoreEntry.block) a.block := hPF.1
      have hTail :
          ParentFirstFrom ((seen ++ [a]).map StoreEntry.block)
            (rest.map StoreEntry.block) := by
        simpa using hPF.2
      have hS1 : Reachable S1 := tryOnBlock_reachable hS
      have hFuture : Future S
          (rest.foldl (fun S e => S.tryOnBlock e.block) S1) := by
        exact Future.trans (tryOnBlock_future (S := S) (B := a.block))
          (replayEntriesFrom_future rest S1)
      have hSeen' :
          ∀ p : StoreEntry n, p ∈ seen ++ [a] →
            RelevantToFinal
              (rest.foldl (fun S e => S.tryOnBlock e.block) S1).F p.block →
            EntryAcceptedIn S1 p := by
        intro p hp hRelP
        have hpCases : p ∈ seen ∨ p = a := by
          simpa using hp
        rcases hpCases with hpSeen | hpA
        · have hAcc : EntryAcceptedIn S p := hSeen p hpSeen hRelP
          exact tryOnBlock_entryAccepted_preserved (B := a.block) hAcc
        · subst p
          exact tryOnBlock_entryAccepted_of_parentReady_relevant hS hFuture
            hSeen a hHead hRelP
      exact replayEntriesFrom_accepts_relevant_aux rest (seen ++ [a]) S1
        hS1 hTail hSeen' e (by simpa [List.append_assoc] using he) hRel

theorem parentFirstReplay_accepts_relevant_input
    {input : List (StoreEntry n)} {S : Store n}
    (hReplay : ReplayEntriesOf input S) (hPF : ParentFirstEntries input) :
    ∀ e : StoreEntry n, e ∈ input → RelevantToFinal S.F e.block →
      EntryAcceptedIn S e := by
  intro e he hRel
  rw [hReplay] at hRel ⊢
  unfold Store.replayBlocks
  rw [replayEntriesFrom_eq_replayBlocksFrom_map]
  have hPF' :
      ParentFirstFrom (List.map StoreEntry.block [StoreEntry.genesis n])
        (List.map StoreEntry.block input) := by
    simpa [ParentFirstEntries, ParentFirst, StoreEntry.genesis] using hPF
  have hSeen :
      ∀ p : StoreEntry n, p ∈ [StoreEntry.genesis n] →
        RelevantToFinal
          (input.foldl (fun S e => S.tryOnBlock e.block) (Store.genesis n)).F
          p.block →
        EntryAcceptedIn (Store.genesis n) p := by
    intro p hp _hRelP
    have hpEq : p = StoreEntry.genesis n := by simpa using hp
    subst p
    exact reachable_entryAccepted_genesis Reachable.genesis
  have hRel' :
      RelevantToFinal
        (input.foldl (fun S e => S.tryOnBlock e.block) (Store.genesis n)).F
        e.block := by
    simpa [Store.replayBlocks, replayEntriesFrom_eq_replayBlocksFrom_map] using hRel
  exact replayEntriesFrom_accepts_relevant_aux input [StoreEntry.genesis n]
    (Store.genesis n) Reachable.genesis hPF' hSeen e
    (by simp [he]) hRel'

/-! ## Replay Finality Components -/

lemma FinalityCandidate.mono {input input' : List (StoreEntry n)}
    {F : Block n}
    (hSub : ∀ e, e ∈ input → e ∈ input')
    (h : FinalityCandidate input F) : FinalityCandidate input' F := by
  rcases h with hGen | hEntry
  · exact Or.inl hGen
  · rcases hEntry with ⟨e, he, hF⟩
    exact Or.inr ⟨e, hSub e he, hF⟩

lemma FinalityCandidate.mem_append_left
    {seen todo : List (StoreEntry n)} {F : Block n}
    (h : FinalityCandidate seen F) : FinalityCandidate (seen ++ todo) F := by
  exact FinalityCandidate.mono (fun e he => by simp [he]) h

lemma FinalityCandidate.mem_append_cons_last
    {seen : List (StoreEntry n)} (a : StoreEntry n) :
    FinalityCandidate (seen ++ [a]) a.state.F := by
  right
  exact ⟨a, by simp, rfl⟩

lemma replayEntriesFrom_F_candidate_aux :
    ∀ (todo seen : List (StoreEntry n)) (S : Store n),
      FinalityCandidate seen S.F →
        FinalityCandidate (seen ++ todo)
          ((todo.foldl (fun S e => S.tryOnBlock e.block) S).F)
  | [], _seen, _S, hCand => by
      simpa using hCand
  | a :: rest, seen, S, hCand => by
      let S1 := S.tryOnBlock a.block
      have hCandS1 : FinalityCandidate (seen ++ [a]) S1.F := by
        rcases tryOnBlock_F_old_or_entry S a with hOld | hNew
        · rw [hOld]
          exact FinalityCandidate.mem_append_left (todo := [a]) hCand
        · rw [hNew]
          exact FinalityCandidate.mem_append_cons_last (seen := seen) a
      have hTail := replayEntriesFrom_F_candidate_aux rest
        (seen ++ [a]) S1 hCandS1
      simpa [List.append_assoc, S1] using hTail

theorem replayEntries_F_candidate (input : List (StoreEntry n)) :
    FinalityCandidate input
      ((input.foldl (fun S e => S.tryOnBlock e.block) (Store.genesis n)).F) := by
  have h := replayEntriesFrom_F_candidate_aux input [] (Store.genesis n) (by
    left
    rfl : FinalityCandidate ([] : List (StoreEntry n)) (Store.genesis n).F)
  simpa [Store.genesis] using h

theorem ReplayEntriesOf.F_le_finalityMax
    {input : List (StoreEntry n)} {S : Store n} {Fmax : Block n}
    (hReplay : ReplayEntriesOf input S) (hMax : FinalityMax input Fmax) :
    S.F ≼ Fmax := by
  rw [hReplay]
  unfold Store.replayBlocks
  rw [replayEntriesFrom_eq_replayBlocksFrom_map]
  exact hMax.2 _ (replayEntries_F_candidate input)

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

lemma StoreEntry.state_F_le_block (e : StoreEntry n) : e.state.F ≼ e.block := by
  exact Block.Ancestor.trans
    (by simpa [StoreEntry.state] using chain_F_le_J e.chain)
    (by simpa [StoreEntry.state] using chain_J_le_L e.chain)

lemma StoreEntry.state_F_wellformed (e : StoreEntry n) :
    Block.WellFormed e.state.F := by
  exact (StoreEntry.state_F_le_block e).wellformed_of
    (chain_tip_wellformed e.chain)

lemma ParentFirstFrom.prefix :
    ∀ (seen pre post : List (Block n)),
      ParentFirstFrom seen (pre ++ post) → ParentFirstFrom seen pre
  | _seen, [], _post, _h => by
      simp [ParentFirstFrom]
  | seen, b :: pre, post, h => by
      constructor
      · exact h.1
      · exact ParentFirstFrom.prefix (seen ++ [b]) pre post h.2

lemma ParentFirstFrom.ready_of_split :
    ∀ (seen : List (Block n)) (pre : List (StoreEntry n))
      (e : StoreEntry n) (post : List (StoreEntry n)),
      ParentFirstFrom seen ((pre ++ e :: post).map StoreEntry.block) →
        ParentReadyIn (seen ++ pre.map StoreEntry.block) e.block
  | seen, [], _e, _post, h => by
      simpa using h.1
  | seen, p :: pre, e, post, h => by
      have hTail := h.2
      have hReady := ParentFirstFrom.ready_of_split
        (seen ++ [p.block]) pre e post hTail
      simpa [List.append_assoc] using hReady

lemma ParentFirstEntries.prefix_of_split {pre : List (StoreEntry n)}
    {e : StoreEntry n} {post : List (StoreEntry n)}
    (hPF : ParentFirstEntries (pre ++ e :: post)) :
    ParentFirstEntries pre := by
  change ParentFirstFrom [Block.genesis] (pre.map StoreEntry.block)
  exact ParentFirstFrom.prefix [Block.genesis] (pre.map StoreEntry.block)
    (e.block :: post.map StoreEntry.block) (by
      simpa [ParentFirstEntries, ParentFirst, List.map_append] using hPF)

lemma replayPrefix_contains_of_mem_relevant
    {pre : List (StoreEntry n)} {Spre : Store n} {p : StoreEntry n}
    (hReplayPre : ReplayEntriesOf pre Spre)
    (hPFPre : ParentFirstEntries pre)
    (hp : p ∈ pre)
    (hRel : RelevantToFinal Spre.F p.block) : Contains Spre p.block := by
  have hAcc := parentFirstReplay_accepts_relevant_input
    hReplayPre hPFPre p hp hRel
  rcases hAcc with ⟨w, hw, hBlock, _⟩
  exact ⟨w, hw, hBlock⟩

lemma replayPrefix_parent_contains_of_ready
    {input pre : List (StoreEntry n)} {e : StoreEntry n}
    {post : List (StoreEntry n)} {Spre : Store n} {Fmax : Block n}
    (hInputEq : input = pre ++ e :: post)
    (hReplayPre : ReplayEntriesOf pre Spre)
    (hPF : ParentFirstEntries input)
    (hSpreF : Spre.F ≼ Fmax)
    (heF : e.state.F = Fmax)
    (hReady : ParentReadyIn ([Block.genesis] ++ pre.map StoreEntry.block) e.block)
    {bid : BlockId} {parent : Block n} {s : ℕ} {vs : List (Vote n)}
    (hBlock : e.block = Block.mk bid parent s vs) : Contains Spre parent := by
  have hReadyMk :
      parent = Block.genesis ∨
        parent ∈ [Block.genesis] ++ pre.map StoreEntry.block := by
    simpa [ParentReadyIn, hBlock] using hReady
  rcases hReadyMk with hGenesis | hMem
  · rw [hGenesis]
    exact reachable_contains_genesis hReplayPre.reachable
  · have hMem' : parent = Block.genesis ∨
        parent ∈ pre.map StoreEntry.block := by
      simpa using hMem
    rcases hMem' with hGenesis | hParentPre
    · rw [hGenesis]
      exact reachable_contains_genesis hReplayPre.reachable
    · rcases List.mem_map.mp hParentPre with ⟨p, hpPre, hpBlock⟩
      have hParentE : parent ≼ e.block := by
        rw [hBlock]
        exact Block.Ancestor.step (Block.Ancestor.refl parent)
      have hFmaxE : Fmax ≼ e.block := by
        rw [← heF]
        exact StoreEntry.state_F_le_block e
      have hSpreE : Spre.F ≼ e.block :=
        Block.Ancestor.trans hSpreF hFmaxE
      have hParentRel : RelevantToFinal Spre.F p.block := by
        have hpE : p.block ≼ e.block := by simpa [hpBlock] using hParentE
        rcases Block.Ancestor.linear hSpreE hpE with hSP | hPS
        · exact Or.inl hSP
        · exact Or.inr hPS
      have hContP := replayPrefix_contains_of_mem_relevant hReplayPre
        (ParentFirstEntries.prefix_of_split (pre := pre) (e := e) (post := post)
          (by simpa [hInputEq] using hPF))
        hpPre hParentRel
      simpa [hpBlock] using hContP

lemma replay_prefix_F_le_finalityMax {input pre : List (StoreEntry n)}
    {Fmax : Block n}
    (hSub : ∀ a, a ∈ pre → a ∈ input)
    (hMax : FinalityMax input Fmax) :
    ((pre.foldl (fun S e => S.tryOnBlock e.block) (Store.genesis n)).F) ≼ Fmax := by
  have hCandPre := replayEntries_F_candidate (n := n) pre
  have hCandInput : FinalityCandidate input
      ((pre.foldl (fun S e => S.tryOnBlock e.block) (Store.genesis n)).F) :=
    FinalityCandidate.mono hSub hCandPre
  exact hMax.2 _ hCandInput

lemma fresh_of_prefix_nodup
    {input pre : List (StoreEntry n)} {e : StoreEntry n}
    {post : List (StoreEntry n)} {Spre : Store n}
    (hInputEq : input = pre ++ e :: post)
    (hReplayPre : ReplayEntriesOf pre Spre)
    (hNoDup : (input.map StoreEntry.block).Nodup)
    (hNoGenesis : Block.genesis ∉ input.map StoreEntry.block) :
    Spre.containsBlockBool e.block = false := by
  by_cases h : Spre.containsBlockBool e.block = true
  · have hContains : Contains Spre e.block := contains_of_containsBlockBool h
    rcases hContains with ⟨w, hw, hBlockW⟩
    rw [hReplayPre] at hw
    unfold Store.replayBlocks at hw
    rw [replayEntriesFrom_eq_replayBlocksFrom_map] at hw
    have hwReplay :
        w ∈ (Store.replayBlocks (n := n) (pre.map StoreEntry.block)).entries := by
      simpa [Store.replayBlocks, replayEntriesFrom_eq_replayBlocksFrom_map] using hw
    have hProv := replayBlocks_entries_genesis_or_input
      (blocks := pre.map StoreEntry.block) hwReplay
    have heInput : e.block ∈ input.map StoreEntry.block := by
      rw [hInputEq]
      simp
    rcases hProv with hGenesis | hPre
    · have : Block.genesis ∈ input.map StoreEntry.block := by
        simpa [← hBlockW, hGenesis] using heInput
      exact False.elim (hNoGenesis this)
    · have hDup : ¬ (input.map StoreEntry.block).Nodup := by
        intro hND
        have hPreInput : e.block ∈ pre.map StoreEntry.block := by
          simpa [hBlockW] using hPre
        have hNotMem : e.block ∉ pre.map StoreEntry.block := by
          have hND' :
              ((pre.map StoreEntry.block) ++
                e.block :: post.map StoreEntry.block).Nodup := by
            simpa [hInputEq, List.map_append] using hND
          intro hPreMem
          have hCross := (List.nodup_append.mp hND').2.2
          exact hCross e.block hPreMem e.block (by simp) rfl
        exact hNotMem hPreInput
      exact False.elim (hDup hNoDup)
  · cases hb : Spre.containsBlockBool e.block
    · rfl
    · exact False.elim (h hb)

lemma idInjectiveAgainstStore_of_input
    {input pre : List (StoreEntry n)} {e : StoreEntry n}
    {post : List (StoreEntry n)} {Spre Safter : Store n}
    (hInputEq : input = pre ++ e :: post)
    (hReplayPre : ReplayEntriesOf pre Spre)
    (hstep : Spre.onBlock e.block = some Safter)
    (hInputId : InputIdInjective input) :
    IdInjectiveAgainstStore e.block Safter := by
  intro a ha
  have haTry : a ∈ (Spre.tryOnBlock e.block).entries := by
    simpa [tryOnBlock, hstep] using ha
  have hOldOrNew := tryOnBlock_entries_old_or_new haTry
  have heInput : HasInputEntry input e := by
    right
    refine ⟨e, ?_, rfl, rfl⟩
    rw [hInputEq]
    simp
  have haInput : HasInputEntry input a := by
    rcases hOldOrNew with hOld | hNew
    · rw [hReplayPre] at hOld
      unfold Store.replayBlocks at hOld
      rw [replayEntriesFrom_eq_replayBlocksFrom_map] at hOld
      have hOldReplay :
          a ∈ (Store.replayBlocks (n := n) (pre.map StoreEntry.block)).entries := by
        simpa [Store.replayBlocks, replayEntriesFrom_eq_replayBlocksFrom_map] using hOld
      have hProv := replayBlocks_entries_genesis_or_input
        (blocks := pre.map StoreEntry.block) hOldReplay
      rcases hProv with hGenesis | hPre
      · exact Or.inl hGenesis
      · rcases List.mem_map.mp hPre with ⟨p, hp, hpBlock⟩
        right
        refine ⟨p, ?_, hpBlock, ?_⟩
        · rw [hInputEq]
          simp [hp]
        · exact StoreEntry.height_eq_of_block_eq hpBlock
    · right
      refine ⟨e, ?_, hNew.symm, ?_⟩
      · rw [hInputEq]
        simp
      · exact StoreEntry.height_eq_of_block_eq hNew.symm
  change Block.IdInjectiveOnAncestors e.block a.block
  exact hInputId e a heInput haInput

lemma parentFirstReplay_finalityMax_le_F_of_split {f : ℕ}
    (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {input pre : List (StoreEntry n)} {e : StoreEntry n}
    {post : List (StoreEntry n)} {S : Store n} {Fmax : Block n}
    (hInputEq : input = pre ++ e :: post)
    (hReplay : ReplayEntriesOf input S)
    (hPF : ParentFirstEntries input)
    (hNoDup : (input.map StoreEntry.block).Nodup)
    (hNoGenesis : Block.genesis ∉ input.map StoreEntry.block)
    (hInputId : InputIdInjective input)
    (hMax : FinalityMax input Fmax)
    (heF : e.state.F = Fmax) :
    Fmax ≼ S.F := by
  let Spre : Store n :=
    pre.foldl (fun S e => S.tryOnBlock e.block) (Store.genesis n)
  have hReplayPre : ReplayEntriesOf pre Spre := by
    unfold ReplayEntriesOf ReplayOf Store.replayBlocks Spre
    rw [replayEntriesFrom_eq_replayBlocksFrom_map]
  have hSubPre : ∀ a, a ∈ pre → a ∈ input := by
    intro a ha
    rw [hInputEq]
    simp [ha]
  have hSpreF : Spre.F ≼ Fmax :=
    replay_prefix_F_le_finalityMax hSubPre hMax
  have hFmaxE : Fmax ≼ e.block := by
    rw [← heF]
    exact StoreEntry.state_F_le_block e
  have hAnc : Spre.F ≼ e.block := Block.Ancestor.trans hSpreF hFmaxE
  have hFresh : Spre.containsBlockBool e.block = false :=
    fresh_of_prefix_nodup hInputEq hReplayPre hNoDup hNoGenesis
  have hReady :
      ParentReadyIn ([Block.genesis] ++ pre.map StoreEntry.block) e.block := by
    have hPF' :
        ParentFirstFrom [Block.genesis]
          ((pre ++ e :: post).map StoreEntry.block) := by
      simpa [ParentFirstEntries, ParentFirst, hInputEq] using hPF
    exact ParentFirstFrom.ready_of_split [Block.genesis] pre e post hPF'
  have hNonGenesis : e.block ≠ Block.genesis := by
    intro hEq
    have : Block.genesis ∈ input.map StoreEntry.block := by
      rw [hInputEq]
      simp [hEq]
    exact hNoGenesis this
  obtain ⟨Sstep, hstep, hAcc⟩ := onBlock_acceptedBlockState_of_ready
    (S := Spre) e hFresh
    (fun hBlock => replayPrefix_parent_contains_of_ready
      hInputEq hReplayPre hPF hSpreF heF hReady hBlock)
    hAnc hNonGenesis
  have hIdStore : IdInjectiveAgainstStore e.block Sstep :=
    idInjectiveAgainstStore_of_input hInputEq hReplayPre hstep hInputId
  have hComp :
      e.state.F ≼ Spre.F ∨ (Spre.F ≼ e.state.F ∧ Spre.F ≠ e.state.F) := by
    by_cases hEq : Spre.F = e.state.F
    · left
      rw [hEq]
      exact Block.Ancestor.refl _
    · right
      exact ⟨by simpa [heF] using hSpreF, hEq⟩
  have hDesc : e.state.F ≼ Sstep.F :=
    onBlock_descends_or_accepts_state_finalization hn hNoSlash
      hReplayPre.reachable hFresh hstep hAcc hIdStore hComp
  have hFuturePost : Future Sstep
      (post.foldl (fun S e => S.tryOnBlock e.block) Sstep) :=
    replayEntriesFrom_future post Sstep
  have hFinalEq :
      S = post.foldl (fun S e => S.tryOnBlock e.block) Sstep := by
    rw [hReplay, hInputEq]
    unfold Store.replayBlocks
    rw [replayEntriesFrom_eq_replayBlocksFrom_map]
    simp
    rw [show Spre.tryOnBlock e.block = Sstep by simp [tryOnBlock, hstep]]
  rw [hFinalEq]
  have hDescFmax : Fmax ≼ Sstep.F := by
    simpa [heF] using hDesc
  exact hDescFmax.trans (future_F_ancestor hFuturePost)

theorem parentFirstReplay_F_eq_finalityMax {f : ℕ}
    (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {input : List (StoreEntry n)} {S : Store n} {Fmax : Block n}
    (hReplay : ReplayEntriesOf input S)
    (hPF : ParentFirstEntries input)
    (hNoDup : (input.map StoreEntry.block).Nodup)
    (hNoGenesis : Block.genesis ∉ input.map StoreEntry.block)
    (hInputId : InputIdInjective input)
    (hMax : FinalityMax input Fmax) :
    S.F = Fmax := by
  have hUpper : S.F ≼ Fmax := hReplay.F_le_finalityMax hMax
  have hLower : Fmax ≼ S.F := by
    rcases hMax.1 with hGenesis | hWitness
    · rw [hGenesis]
      exact Block.genesis_ancestor S.F
    · rcases hWitness with ⟨e, he, heF⟩
      rcases (List.mem_iff_append.mp he) with ⟨pre, post, hInputEq⟩
      exact parentFirstReplay_finalityMax_le_F_of_split hn hNoSlash
        hInputEq hReplay hPF hNoDup hNoGenesis hInputId hMax heF
  have hWF : Block.WellFormed Fmax := by
    rcases hMax.1 with hGenesis | hWitness
    · rw [hGenesis]
      trivial
    · rcases hWitness with ⟨e, _he, heF⟩
      rw [← heF]
      exact StoreEntry.state_F_wellformed e
  exact Block.Ancestor.antisymm hUpper hLower hWF

/-! ## Replay Frontier-Height Components -/

lemma ReplayEntriesOf.hmax_le_heightMax
    {input : List (StoreEntry n)} {S : Store n} {hmax : ℕ}
    (hReplay : ReplayEntriesOf input S) (hMax : HeightMax input hmax) :
    S.hmax ≤ hmax := by
  rcases reachable_hmax_witness hReplay.reachable with ⟨e, he, heHeight⟩
  have hInput := hReplay.entries_from_input e he
  have hCand : HeightCandidate input e.height := by
    rcases hInput with hGenesis | hEntry
    · left
      exact StoreEntry.height_eq_one_of_block_genesis hGenesis
    · rcases hEntry with ⟨a, ha, _hBlock, hHeight⟩
      right
      exact ⟨a, ha, hHeight⟩
  rw [← heHeight]
  exact hMax.2 e.height hCand

lemma finalityMax_descends_heightMax_witness {f : ℕ}
    (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {input : List (StoreEntry n)} {Fmax : Block n} {hmax : ℕ}
    (hInputId : InputIdInjective input)
    (hFMax : FinalityMax input Fmax)
    (hHMax : HeightMax input hmax)
    {e : StoreEntry n} (he : e ∈ input) (heHeight : e.height = hmax) :
    Fmax ≼ e.block := by
  rcases hFMax.1 with hGenesis | hFWitness
  · rw [hGenesis]
    exact Block.genesis_ancestor e.block
  · rcases hFWitness with ⟨eF, heF, heFFinal⟩
    have hEqF : (stateOf eF.chain).F = Fmax := by
      simpa [StoreEntry.state] using heFFinal
    subst Fmax
    obtain ⟨h_f, hFAnc, hCert, hhf_le_hj_state⟩ :=
      FinalityEvidence.chain_finalizedCertificate_le_hj eF.chain
    have hhf_le_hj : h_f ≤ eF.state.hj := by
      simpa [StoreEntry.state] using hhf_le_hj_state
    have hhj_lt_height : eF.state.hj < eF.height := by
      simpa [StoreEntry.height, StoreEntry.state] using chain_hj_lt_h eF.chain
    have hEF_le_hmax : eF.height ≤ hmax :=
      hHMax.2 eF.height (Or.inr ⟨eF, heF, rfl⟩)
    have hHeightHigh : (stateOf e.chain).h > h_f := by
      have hlt : h_f < hmax := by omega
      have hEqHeight : (stateOf e.chain).h = hmax := by
        simpa [StoreEntry.height, StoreEntry.state] using heHeight
      omega
    have hId : Block.IdInjectiveOnAncestors eF.block e.block :=
      hInputId eF e
        (Or.inr ⟨eF, heF, rfl, rfl⟩)
        (Or.inr ⟨e, he, rfl, rfl⟩)
    rcases main_safety hn hId eF.chain rfl hCert e.chain hHeightHigh
        with hSlash | hDesc
    · exact False.elim (hNoSlash hSlash)
    · exact hDesc

theorem parentFirstReplay_heightMax_le_hmax {f : ℕ}
    (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {input : List (StoreEntry n)} {S : Store n} {Fmax : Block n} {hmax : ℕ}
    (hReplay : ReplayEntriesOf input S)
    (hPF : ParentFirstEntries input)
    (hNoDup : (input.map StoreEntry.block).Nodup)
    (hNoGenesis : Block.genesis ∉ input.map StoreEntry.block)
    (hInputId : InputIdInjective input)
    (hFMax : FinalityMax input Fmax)
    (hHMax : HeightMax input hmax) :
    hmax ≤ S.hmax := by
  have hFEq : S.F = Fmax :=
    parentFirstReplay_F_eq_finalityMax hn hNoSlash hReplay hPF
      hNoDup hNoGenesis hInputId hFMax
  rcases hHMax.1 with hGenesisHeight | hWitness
  · rw [hGenesisHeight]
    rcases reachable_entryAccepted_genesis hReplay.reachable with
      ⟨w, hw, _hBlock, hHeight⟩
    have hwLe := reachable_entry_height_le_hmax hReplay.reachable hw
    have hwLe' : (StoreEntry.genesis n).height ≤ S.hmax := by
      simpa [hHeight] using hwLe
    simpa [StoreEntry.genesis, StoreEntry.height, StoreEntry.state, stateOf,
      State.genesis] using hwLe'
  · rcases hWitness with ⟨e, he, heHeight⟩
    have hDesc : Fmax ≼ e.block :=
      finalityMax_descends_heightMax_witness hn hNoSlash hInputId
        hFMax hHMax he heHeight
    have hRel : RelevantToFinal S.F e.block := by
      left
      simpa [hFEq] using hDesc
    rcases parentFirstReplay_accepts_relevant_input hReplay hPF e he hRel with
      ⟨w, hw, _hBlock, hHeight⟩
    have hwLe := reachable_entry_height_le_hmax hReplay.reachable hw
    rw [← heHeight, ← hHeight]
    exact hwLe

theorem parentFirstReplay_hmax_eq_heightMax {f : ℕ}
    (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {input : List (StoreEntry n)} {S : Store n} {Fmax : Block n} {hmax : ℕ}
    (hReplay : ReplayEntriesOf input S)
    (hPF : ParentFirstEntries input)
    (hNoDup : (input.map StoreEntry.block).Nodup)
    (hNoGenesis : Block.genesis ∉ input.map StoreEntry.block)
    (hInputId : InputIdInjective input)
    (hFMax : FinalityMax input Fmax)
    (hHMax : HeightMax input hmax) :
    S.hmax = hmax := by
  exact le_antisymm
    (hReplay.hmax_le_heightMax hHMax)
    (parentFirstReplay_heightMax_le_hmax hn hNoSlash hReplay hPF
      hNoDup hNoGenesis hInputId hFMax hHMax)

/-! ## Replay Justification-Key Components -/

lemma keyGreater_false_keyLE {h' h : ℕ} {J' J : Block n}
    (hkey : keyGreater h' J' h J = false) : KeyLE h' J' h J := by
  by_cases hlt : h < h'
  · unfold keyGreater at hkey
    simp [hlt] at hkey
  · have hle : h' ≤ h := Nat.le_of_not_gt hlt
    by_cases heq : h' = h
    · right
      refine ⟨heq, ?_⟩
      by_contra hNotLe
      have hidLt : J.id < J'.id := Nat.lt_of_not_ge hNotLe
      have htrue : keyGreater h' J' h J = true := by
        unfold keyGreater
        simp [heq, hidLt]
      rw [hkey] at htrue
      cases htrue
    · left
      omega

lemma updateJustified_candidate_key_le {S : Store n} {J' : Block n} {h' : ℕ}
    (hContains : S.containsBlockBool J' = true)
    (hBelowF : Block.isAncestorOf S.F J' = true) :
    KeyLE h' J'
      (S.updateJustified J' h').hj
      (S.updateJustified J' h').J := by
  cases hguard : S.shouldUpdateJustified J' h'
  · have hkey : keyGreater h' J' S.hj S.J = false := by
      cases hkey : keyGreater h' J' S.hj S.J
      · rfl
      · have htrue : S.shouldUpdateJustified J' h' = true := by
          simp [shouldUpdateJustified, hContains, hBelowF, hkey]
        rw [hguard] at htrue
        cases htrue
    simpa [updateJustified, hguard] using keyGreater_false_keyLE hkey
  · simp [updateJustified, hguard, KeyLE.refl]

lemma onBlock_accepted_state_key_le {S S' : Store n} {B : Block n}
    {σB : State n}
    (hS : Reachable S)
    (hFresh : S.containsBlockBool B = false)
    (hstep : S.onBlock B = some S')
    (hAcc : AcceptedBlockState S' B σB)
    (hBelow : S.F ≼ σB.J) :
    KeyLE σB.hj σB.J S'.hj S'.J := by
  rcases hAcc with ⟨chainB, _hLookup, hStateEq⟩
  obtain
    ⟨bid, parent, newSlot, votes, _hBlockEq, parentChain, hFind, hSlot,
      _hAnc, hResult⟩ := freshOnBlockStep_of_onBlock hFresh hstep
  subst B
  let child := Block.mk bid parent newSlot votes
  let entry : StoreEntry n :=
    { block := child
      chain := Chain.extend parentChain bid newSlot votes hSlot }
  let σ' := entry.state
  let S1 := S.addEntry entry
  let S2 := S1.updateJustified σ'.J σ'.hj
  have hResult' : S' = S2.updateFinalized σ'.F := by
    simpa [child, entry, σ', S1, S2] using hResult
  subst S'
  have hState : σB = σ' := by
    rw [← hStateEq]
    simpa [σ', StoreEntry.state, entry, child] using
      (chain_unique chainB entry.chain)
  have hBelow' : S.F ≼ σ'.J := by
    simpa [hState] using hBelow
  have hParent : Contains S parent := findChain?_some_contains hFind
  have hSClosed : AncestorClosed S := reachable_ancestorClosed hS
  have hBlock : entry.block = Block.mk bid parent newSlot votes := by
    rfl
  have hS1Closed : AncestorClosed S1 := by
    change AncestorClosed (S.addEntry entry)
    exact addChild_ancestorClosed hBlock hSClosed hParent
  have hEntryMemS1 : entry ∈ S1.entries := by
    simp [S1, addEntry]
  have hJAnc : σ'.J ≼ entry.block := by
    simpa [σ', StoreEntry.state] using chain_J_le_L entry.chain
  have hJContains : Contains S1 σ'.J :=
    hS1Closed ⟨entry, hEntryMemS1, rfl⟩ hJAnc
  have hJBool : S1.containsBlockBool σ'.J = true :=
    containsBlockBool_of_contains hJContains
  have hBelowS1 : Block.isAncestorOf S1.F σ'.J = true := by
    have hProp : S1.F ≼ σ'.J := by
      simpa [S1, addEntry] using hBelow'
    exact (Block.isAncestorOf_eq_true_iff _ _).mpr hProp
  have hS2Key : KeyLE σ'.hj σ'.J S2.hj S2.J :=
    updateJustified_candidate_key_le hJBool hBelowS1
  simpa [hState, S2, updateFinalized_hj_eq, updateFinalized_J_eq] using hS2Key

lemma replayPrefix_parent_contains_of_ready_desc
    {input pre : List (StoreEntry n)} {e : StoreEntry n}
    {post : List (StoreEntry n)} {Spre : Store n} {Fmax : Block n}
    (hInputEq : input = pre ++ e :: post)
    (hReplayPre : ReplayEntriesOf pre Spre)
    (hPF : ParentFirstEntries input)
    (hSpreF : Spre.F ≼ Fmax)
    (hFmaxE : Fmax ≼ e.block)
    (hReady : ParentReadyIn ([Block.genesis] ++ pre.map StoreEntry.block) e.block)
    {bid : BlockId} {parent : Block n} {s : ℕ} {vs : List (Vote n)}
    (hBlock : e.block = Block.mk bid parent s vs) : Contains Spre parent := by
  have hReadyMk :
      parent = Block.genesis ∨
        parent ∈ [Block.genesis] ++ pre.map StoreEntry.block := by
    simpa [ParentReadyIn, hBlock] using hReady
  rcases hReadyMk with hGenesis | hMem
  · rw [hGenesis]
    exact reachable_contains_genesis hReplayPre.reachable
  · have hMem' : parent = Block.genesis ∨
        parent ∈ pre.map StoreEntry.block := by
      simpa using hMem
    rcases hMem' with hGenesis | hParentPre
    · rw [hGenesis]
      exact reachable_contains_genesis hReplayPre.reachable
    · rcases List.mem_map.mp hParentPre with ⟨p, hpPre, hpBlock⟩
      have hParentE : parent ≼ e.block := by
        rw [hBlock]
        exact Block.Ancestor.step (Block.Ancestor.refl parent)
      have hSpreE : Spre.F ≼ e.block :=
        Block.Ancestor.trans hSpreF hFmaxE
      have hParentRel : RelevantToFinal Spre.F p.block := by
        have hpE : p.block ≼ e.block := by simpa [hpBlock] using hParentE
        rcases Block.Ancestor.linear hSpreE hpE with hSP | hPS
        · exact Or.inl hSP
        · exact Or.inr hPS
      have hContP := replayPrefix_contains_of_mem_relevant hReplayPre
        (ParentFirstEntries.prefix_of_split (pre := pre) (e := e) (post := post)
          (by simpa [hInputEq] using hPF))
        hpPre hParentRel
      simpa [hpBlock] using hContP

lemma ReplayEntriesOf.genesis_key_le
    {input : List (StoreEntry n)} {S : Store n}
    (hReplay : ReplayEntriesOf input S) :
    KeyLE 0 (Block.genesis : Block n) S.hj S.J := by
  rw [hReplay]
  unfold Store.replayBlocks
  rw [replayEntriesFrom_eq_replayBlocksFrom_map]
  simpa [Store.genesis] using
    future_key_mono (replayEntriesFrom_future input (Store.genesis n))

lemma ReplayEntriesOf.current_justification_candidate
    {input : List (StoreEntry n)} {S : Store n} {Fmax : Block n}
    (hReplay : ReplayEntriesOf input S)
    (hF : S.F = Fmax) :
    JustificationCandidate input Fmax S.J S.hj := by
  refine ⟨?_, ?_⟩
  · simpa [← hF] using reachable_F_ancestor_J hReplay.reachable
  · have hProc : ProcessedJustification S S.J S.hj :=
      reachable_currentProcessedJustification hReplay.reachable
    rcases hProc with ⟨e, he, hJ, hhj⟩
    have hInput := hReplay.entries_from_input e he
    rcases hInput with hGenesis | hEntry
    · left
      have hState :
          e.state = (StoreEntry.genesis n).state :=
        StoreEntry.state_eq_of_block_eq (a := StoreEntry.genesis n)
          (by simpa [StoreEntry.genesis] using hGenesis)
      constructor
      · calc
          S.J = e.state.J := hJ.symm
          _ = (StoreEntry.genesis n).state.J := by rw [hState]
          _ = Block.genesis := by
            simp [StoreEntry.genesis, StoreEntry.state, stateOf, State.genesis]
      · calc
          S.hj = e.state.hj := hhj.symm
          _ = (StoreEntry.genesis n).state.hj := by rw [hState]
          _ = 0 := by
            simp [StoreEntry.genesis, StoreEntry.state, stateOf, State.genesis]
    · rcases hEntry with ⟨a, ha, hBlock, _hHeight⟩
      right
      refine ⟨a, ha, ?_, ?_⟩
      · have hState := StoreEntry.state_eq_of_block_eq hBlock
        rw [hState]
        exact hJ
      · have hState := StoreEntry.state_eq_of_block_eq hBlock
        rw [hState]
        exact hhj

lemma parentFirstReplay_justificationMax_le_key_of_split
    {input pre : List (StoreEntry n)} {e : StoreEntry n}
    {post : List (StoreEntry n)} {S : Store n}
    {Fmax Jmax : Block n} {hjmax : ℕ}
    (hInputEq : input = pre ++ e :: post)
    (hReplay : ReplayEntriesOf input S)
    (hPF : ParentFirstEntries input)
    (hNoDup : (input.map StoreEntry.block).Nodup)
    (hNoGenesis : Block.genesis ∉ input.map StoreEntry.block)
    (hFMax : FinalityMax input Fmax)
    (hJMax : JustificationMax input Fmax Jmax hjmax)
    (heJ : e.state.J = Jmax)
    (heHj : e.state.hj = hjmax) :
    KeyLE hjmax Jmax S.hj S.J := by
  let Spre : Store n :=
    pre.foldl (fun S e => S.tryOnBlock e.block) (Store.genesis n)
  have hReplayPre : ReplayEntriesOf pre Spre := by
    unfold ReplayEntriesOf ReplayOf Store.replayBlocks Spre
    rw [replayEntriesFrom_eq_replayBlocksFrom_map]
  have hSubPre : ∀ a, a ∈ pre → a ∈ input := by
    intro a ha
    rw [hInputEq]
    simp [ha]
  have hSpreF : Spre.F ≼ Fmax :=
    replay_prefix_F_le_finalityMax hSubPre hFMax
  have hFmaxJ : Fmax ≼ e.state.J := by
    have hCand : JustificationCandidate input Fmax e.state.J e.state.hj := by
      refine ⟨?_, Or.inr ?_⟩
      · simpa [heJ] using hJMax.1.1
      · refine ⟨e, ?_, rfl, rfl⟩
        rw [hInputEq]
        simp
    exact hCand.1
  have hJAnc : e.state.J ≼ e.block := by
    simpa [StoreEntry.state] using chain_J_le_L e.chain
  have hFmaxE : Fmax ≼ e.block := hFmaxJ.trans hJAnc
  have hAnc : Spre.F ≼ e.block := hSpreF.trans hFmaxE
  have hFresh : Spre.containsBlockBool e.block = false :=
    fresh_of_prefix_nodup hInputEq hReplayPre hNoDup hNoGenesis
  have hReady :
      ParentReadyIn ([Block.genesis] ++ pre.map StoreEntry.block) e.block := by
    have hPF' :
        ParentFirstFrom [Block.genesis]
          ((pre ++ e :: post).map StoreEntry.block) := by
      simpa [ParentFirstEntries, ParentFirst, hInputEq] using hPF
    exact ParentFirstFrom.ready_of_split [Block.genesis] pre e post hPF'
  have hNonGenesis : e.block ≠ Block.genesis := by
    intro hEq
    have : Block.genesis ∈ input.map StoreEntry.block := by
      rw [hInputEq]
      simp [hEq]
    exact hNoGenesis this
  obtain ⟨Sstep, hstep, hAcc⟩ := onBlock_acceptedBlockState_of_ready
    (S := Spre) e hFresh
    (fun hBlock => replayPrefix_parent_contains_of_ready_desc
      hInputEq hReplayPre hPF hSpreF hFmaxE hReady hBlock)
    hAnc hNonGenesis
  have hBelow : Spre.F ≼ e.state.J := hSpreF.trans hFmaxJ
  have hStepKey : KeyLE e.state.hj e.state.J Sstep.hj Sstep.J :=
    onBlock_accepted_state_key_le hReplayPre.reachable hFresh hstep hAcc hBelow
  have hFuturePost : Future Sstep
      (post.foldl (fun S e => S.tryOnBlock e.block) Sstep) :=
    replayEntriesFrom_future post Sstep
  have hFinalEq :
      S = post.foldl (fun S e => S.tryOnBlock e.block) Sstep := by
    rw [hReplay, hInputEq]
    unfold Store.replayBlocks
    rw [replayEntriesFrom_eq_replayBlocksFrom_map]
    simp
    rw [show Spre.tryOnBlock e.block = Sstep by simp [tryOnBlock, hstep]]
  rw [hFinalEq]
  have hStepKey' : KeyLE hjmax Jmax Sstep.hj Sstep.J := by
    simpa [heJ, heHj] using hStepKey
  exact hStepKey'.trans (future_key_mono hFuturePost)

theorem parentFirstReplay_justificationMax_le_key
    {input : List (StoreEntry n)} {S : Store n}
    {Fmax Jmax : Block n} {hjmax : ℕ}
    (hReplay : ReplayEntriesOf input S)
    (hPF : ParentFirstEntries input)
    (hNoDup : (input.map StoreEntry.block).Nodup)
    (hNoGenesis : Block.genesis ∉ input.map StoreEntry.block)
    (hFMax : FinalityMax input Fmax)
    (hJMax : JustificationMax input Fmax Jmax hjmax) :
    KeyLE hjmax Jmax S.hj S.J := by
  rcases hJMax.1.2 with hGenesis | hWitness
  · rcases hGenesis with ⟨hJ, hhj⟩
    simpa [hJ, hhj] using hReplay.genesis_key_le
  · rcases hWitness with ⟨e, he, heJ, heHj⟩
    rcases (List.mem_iff_append.mp he) with ⟨pre, post, hInputEq⟩
    exact parentFirstReplay_justificationMax_le_key_of_split
      hInputEq hReplay hPF hNoDup hNoGenesis hFMax hJMax heJ heHj

lemma KeyLE.antisymm_height {h₁ h₂ : ℕ} {J₁ J₂ : Block n}
    (h12 : KeyLE h₁ J₁ h₂ J₂) (h21 : KeyLE h₂ J₂ h₁ J₁) :
    h₁ = h₂ := by
  rcases h12 with hlt12 | ⟨heq, _⟩
  · rcases h21 with hlt21 | ⟨heq21, _⟩
    · omega
    · omega
  · exact heq

lemma KeyLE.antisymm_id {h₁ h₂ : ℕ} {J₁ J₂ : Block n}
    (h12 : KeyLE h₁ J₁ h₂ J₂) (h21 : KeyLE h₂ J₂ h₁ J₁) :
    J₁.id = J₂.id := by
  have hh : h₁ = h₂ := KeyLE.antisymm_height h12 h21
  rcases h12 with hlt12 | ⟨_heq12, hid12⟩
  · omega
  · rcases h21 with hlt21 | ⟨_heq21, hid21⟩
    · omega
    · exact le_antisymm hid12 hid21

lemma JustificationCandidate.support
    {input : List (StoreEntry n)} {F J : Block n} {h : ℕ}
    (hCand : JustificationCandidate input F J h) :
    ∃ e : StoreEntry n, HasInputEntry input e ∧ J ≼ e.block := by
  rcases hCand.2 with hGenesis | hEntry
  · rcases hGenesis with ⟨hJ, _hh⟩
    refine ⟨StoreEntry.genesis n, Or.inl rfl, ?_⟩
    rw [hJ]
    exact .refl _
  · rcases hEntry with ⟨e, he, hJ, _hh⟩
    refine ⟨e, Or.inr ⟨e, he, rfl, rfl⟩, ?_⟩
    rw [← hJ]
    simpa [StoreEntry.state] using chain_J_le_L e.chain

/-! ## Input-Equivalent Summary Transfer -/

lemma InputEquivalent.symm {input₁ input₂ : List (StoreEntry n)}
    (hEq : InputEquivalent input₁ input₂) :
    InputEquivalent input₂ input₁ := by
  intro e
  exact Iff.symm (hEq e)

lemma InputEquivalent.finalityCandidate
    {input₁ input₂ : List (StoreEntry n)} {F : Block n}
    (hEq : InputEquivalent input₁ input₂)
    (hCand : FinalityCandidate input₁ F) :
    FinalityCandidate input₂ F := by
  rcases hCand with hGenesis | hEntry
  · exact Or.inl hGenesis
  · rcases hEntry with ⟨e, he, hF⟩
    have hInput : HasInputEntry input₂ e :=
      (hEq e).1 (Or.inr ⟨e, he, rfl, rfl⟩)
    rcases hInput with hGenesis | hEntry₂
    · left
      have hState :
          e.state = (StoreEntry.genesis n).state :=
        StoreEntry.state_eq_of_block_eq (a := StoreEntry.genesis n)
          (by simpa [StoreEntry.genesis] using hGenesis)
      calc
        F = e.state.F := hF.symm
        _ = (StoreEntry.genesis n).state.F := by rw [hState]
        _ = Block.genesis := by
          simp [StoreEntry.genesis, StoreEntry.state, stateOf, State.genesis]
    · rcases hEntry₂ with ⟨a, ha, hBlock, _hHeight⟩
      right
      refine ⟨a, ha, ?_⟩
      have hState : a.state = e.state :=
        StoreEntry.state_eq_of_block_eq (e := a) (a := e) hBlock
      rw [hState]
      exact hF

lemma InputEquivalent.heightCandidate
    {input₁ input₂ : List (StoreEntry n)} {h : ℕ}
    (hEq : InputEquivalent input₁ input₂)
    (hCand : HeightCandidate input₁ h) :
    HeightCandidate input₂ h := by
  rcases hCand with hOne | hEntry
  · exact Or.inl hOne
  · rcases hEntry with ⟨e, he, hh⟩
    have hInput : HasInputEntry input₂ e :=
      (hEq e).1 (Or.inr ⟨e, he, rfl, rfl⟩)
    rcases hInput with hGenesis | hEntry₂
    · left
      calc
        h = e.height := hh.symm
        _ = 1 := StoreEntry.height_eq_one_of_block_genesis hGenesis
    · rcases hEntry₂ with ⟨a, ha, hBlock, _hHeight⟩
      right
      refine ⟨a, ha, ?_⟩
      have hHeight : a.height = e.height :=
        StoreEntry.height_eq_of_block_eq (e := a) (a := e) hBlock
      rw [hHeight]
      exact hh

lemma InputEquivalent.justificationCandidate
    {input₁ input₂ : List (StoreEntry n)} {F J : Block n} {h : ℕ}
    (hEq : InputEquivalent input₁ input₂)
    (hCand : JustificationCandidate input₁ F J h) :
    JustificationCandidate input₂ F J h := by
  refine ⟨hCand.1, ?_⟩
  rcases hCand.2 with hGenesis | hEntry
  · exact Or.inl hGenesis
  · rcases hEntry with ⟨e, he, hJ, hh⟩
    have hInput : HasInputEntry input₂ e :=
      (hEq e).1 (Or.inr ⟨e, he, rfl, rfl⟩)
    rcases hInput with hGenesis | hEntry₂
    · left
      have hState :
          e.state = (StoreEntry.genesis n).state :=
        StoreEntry.state_eq_of_block_eq (a := StoreEntry.genesis n)
          (by simpa [StoreEntry.genesis] using hGenesis)
      constructor
      · calc
          J = e.state.J := hJ.symm
          _ = (StoreEntry.genesis n).state.J := by rw [hState]
          _ = Block.genesis := by
            simp [StoreEntry.genesis, StoreEntry.state, stateOf, State.genesis]
      · calc
          h = e.state.hj := hh.symm
          _ = (StoreEntry.genesis n).state.hj := by rw [hState]
          _ = 0 := by
            simp [StoreEntry.genesis, StoreEntry.state, stateOf, State.genesis]
    · rcases hEntry₂ with ⟨a, ha, hBlock, _hHeight⟩
      right
      refine ⟨a, ha, ?_, ?_⟩
      · have hState : a.state = e.state :=
          StoreEntry.state_eq_of_block_eq (e := a) (a := e) hBlock
        rw [hState]
        exact hJ
      · have hState : a.state = e.state :=
          StoreEntry.state_eq_of_block_eq (e := a) (a := e) hBlock
        rw [hState]
        exact hh

lemma InputEquivalent.finalityMax
    {input₁ input₂ : List (StoreEntry n)} {Fmax : Block n}
    (hEq : InputEquivalent input₁ input₂)
    (hMax : FinalityMax input₁ Fmax) :
    FinalityMax input₂ Fmax := by
  refine ⟨hEq.finalityCandidate hMax.1, ?_⟩
  intro F hCand
  exact hMax.2 F ((InputEquivalent.symm hEq).finalityCandidate hCand)

lemma InputEquivalent.heightMax
    {input₁ input₂ : List (StoreEntry n)} {hmax : ℕ}
    (hEq : InputEquivalent input₁ input₂)
    (hMax : HeightMax input₁ hmax) :
    HeightMax input₂ hmax := by
  refine ⟨hEq.heightCandidate hMax.1, ?_⟩
  intro h hCand
  exact hMax.2 h ((InputEquivalent.symm hEq).heightCandidate hCand)

lemma InputEquivalent.justificationMax
    {input₁ input₂ : List (StoreEntry n)} {F Jmax : Block n} {hjmax : ℕ}
    (hEq : InputEquivalent input₁ input₂)
    (hMax : JustificationMax input₁ F Jmax hjmax) :
    JustificationMax input₂ F Jmax hjmax := by
  refine ⟨hEq.justificationCandidate hMax.1, ?_⟩
  intro J h hCand
  exact hMax.2 J h
    ((InputEquivalent.symm hEq).justificationCandidate hCand)

lemma InputEquivalent.liveSummaryMatches
    {input₁ input₂ : List (StoreEntry n)} {summary : LiveSummary n}
    (hEq : InputEquivalent input₁ input₂)
    (hSummary : LiveSummaryMatches input₁ summary) :
    LiveSummaryMatches input₂ summary := by
  refine ⟨hEq.finalityMax hSummary.1, ?_⟩
  exact ⟨hEq.justificationMax hSummary.2.1, hEq.heightMax hSummary.2.2⟩

theorem parentFirstReplay_justification_eq_justificationMax
    {input : List (StoreEntry n)} {S : Store n}
    {Fmax Jmax : Block n} {hjmax : ℕ}
    (hReplay : ReplayEntriesOf input S)
    (hPF : ParentFirstEntries input)
    (hNoDup : (input.map StoreEntry.block).Nodup)
    (hNoGenesis : Block.genesis ∉ input.map StoreEntry.block)
    (hInputId : InputIdInjective input)
    (hFMax : FinalityMax input Fmax)
    (hFEq : S.F = Fmax)
    (hJMax : JustificationMax input Fmax Jmax hjmax) :
    S.J = Jmax ∧ S.hj = hjmax := by
  have hCurrentCand : JustificationCandidate input Fmax S.J S.hj :=
    hReplay.current_justification_candidate hFEq
  have hUpper : KeyLE S.hj S.J hjmax Jmax :=
    hJMax.2 S.J S.hj hCurrentCand
  have hLower : KeyLE hjmax Jmax S.hj S.J :=
    parentFirstReplay_justificationMax_le_key hReplay hPF hNoDup
      hNoGenesis hFMax hJMax
  have hh : S.hj = hjmax := KeyLE.antisymm_height hUpper hLower
  have hid : S.J.id = Jmax.id := KeyLE.antisymm_id hUpper hLower
  have hJ : S.J = Jmax := by
    rcases hCurrentCand.support with ⟨eS, heSInput, hSJAnc⟩
    rcases hJMax.1.support with ⟨eM, heMInput, hJMAnc⟩
    exact hInputId eS eM heSInput heMInput
      (Or.inl hSJAnc) (Or.inr hJMAnc) hid
  exact ⟨hJ, hh⟩

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

private lemma liveComplete_matching_forward_of_input
    {inputS inputT : List (StoreEntry n)} {summary : LiveSummary n}
    {S T : Store n}
    (hInput : ∀ e : StoreEntry n, HasInputEntry inputS e → HasInputEntry inputT e)
    (hS : LiveComplete inputS summary S)
    (hT : LiveComplete inputT summary T)
    {e : StoreEntry n}
    (he : e ∈ S.entries) (hLive : S.F ≼ e.block) :
    HasMatchingEntry S T e := by
  have hInputE : HasInputEntry inputT e :=
    hInput e (hS.live_entries_from_input e he hLive)
  rcases hInputE with hGenesis | hEntry
  · rcases reachable_entryAccepted_genesis hT.reachable with
      ⟨eT, heT, hBlockT, hHeightT⟩
    refine ⟨eT, heT, ?_, ?_⟩
    · simpa [StoreEntry.genesis, hGenesis] using hBlockT
    · have hHeightE : e.height = (StoreEntry.genesis n).height := by
        exact StoreEntry.height_eq_of_block_eq (by
          simpa [StoreEntry.genesis, hGenesis])
      rw [hHeightT, hHeightE]
  · rcases hEntry with ⟨a, ha, hBlockA, hHeightA⟩
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
    liveComplete_matching_forward_of_input (fun _ h => h) hS hT (e := e) he hLive
  live_entries_backward := fun e he hLive =>
    liveComplete_matching_forward_of_input (fun _ h => h) hT hS (e := e) he hLive

/-- Live completeness over equivalent input sets is enough for live
    equivalence, allowing two different parent-first replay orders. -/
theorem liveEquivalent_of_liveComplete_inputEquivalent
    {inputS inputT : List (StoreEntry n)} {summary : LiveSummary n}
    {S T : Store n}
    (hInput : InputEquivalent inputS inputT)
    (hS : LiveComplete inputS summary S)
    (hT : LiveComplete inputT summary T) :
    LiveEquivalent S T where
  F_eq := hS.F_eq.trans hT.F_eq.symm
  J_eq := hS.J_eq.trans hT.J_eq.symm
  hj_eq := hS.hj_eq.trans hT.hj_eq.symm
  hmax_eq := hS.hmax_eq.trans hT.hmax_eq.symm
  live_entries_forward := fun e he hLive =>
    liveComplete_matching_forward_of_input
      (fun e h => (hInput e).1 h) hS hT (e := e) he hLive
  live_entries_backward := fun e he hLive =>
    liveComplete_matching_forward_of_input
      (fun e h => (hInput e).2 h) hT hS (e := e) he hLive

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

theorem liveComplete_getConfirmed_inputEquivalent
    {inputS inputT : List (StoreEntry n)} {summary : LiveSummary n}
    {S T : Store n} {B : Block n}
    (hInput : InputEquivalent inputS inputT)
    (hS : LiveComplete inputS summary S)
    (hT : LiveComplete inputT summary T) :
    B ∈ S.getConfirmed ↔ B ∈ T.getConfirmed := by
  exact liveEquivalent_getConfirmed hS.reachable hT.reachable
    (liveEquivalent_of_liveComplete_inputEquivalent hInput hS hT)

/-! ## Parent-First Replay Order Independence -/

theorem parentFirstReplay_liveComplete {f : ℕ}
    (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {input : List (StoreEntry n)} {summary : LiveSummary n} {S : Store n}
    (hReplay : ReplayEntriesOf input S)
    (hPF : ParentFirstEntries input)
    (hNoDup : (input.map StoreEntry.block).Nodup)
    (hNoGenesis : Block.genesis ∉ input.map StoreEntry.block)
    (hInputId : InputIdInjective input)
    (hSummary : LiveSummaryMatches input summary) :
    LiveComplete input summary S := by
  have hFMax : FinalityMax input summary.F := hSummary.1
  have hJMax : JustificationMax input summary.F summary.J summary.hj :=
    hSummary.2.1
  have hHMax : HeightMax input summary.hmax := hSummary.2.2
  have hF : S.F = summary.F :=
    parentFirstReplay_F_eq_finalityMax hn hNoSlash hReplay hPF
      hNoDup hNoGenesis hInputId hFMax
  have hJHj : S.J = summary.J ∧ S.hj = summary.hj :=
    parentFirstReplay_justification_eq_justificationMax
      hReplay hPF hNoDup hNoGenesis hInputId hFMax hF hJMax
  have hHmax : S.hmax = summary.hmax :=
    parentFirstReplay_hmax_eq_heightMax hn hNoSlash hReplay hPF
      hNoDup hNoGenesis hInputId hFMax hHMax
  have hAccepted :
      ∀ e : StoreEntry n, e ∈ input → summary.F ≼ e.block →
        EntryAcceptedIn S e := by
    intro e he hLive
    have hRel : RelevantToFinal S.F e.block := by
      left
      simpa [hF] using hLive
    exact parentFirstReplay_accepts_relevant_input hReplay hPF e he hRel
  exact liveComplete_of_replay_components hReplay hF hJHj.1 hJHj.2 hHmax hAccepted

theorem parentFirstReplay_getConfirmed_order_independent {f : ℕ}
    (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {input₁ input₂ : List (StoreEntry n)} {summary : LiveSummary n}
    {S T : Store n} {B : Block n}
    (hReplayS : ReplayEntriesOf input₁ S)
    (hReplayT : ReplayEntriesOf input₂ T)
    (hPFS : ParentFirstEntries input₁)
    (hPFT : ParentFirstEntries input₂)
    (hNoDupS : (input₁.map StoreEntry.block).Nodup)
    (hNoDupT : (input₂.map StoreEntry.block).Nodup)
    (hNoGenesisS : Block.genesis ∉ input₁.map StoreEntry.block)
    (hNoGenesisT : Block.genesis ∉ input₂.map StoreEntry.block)
    (hInputIdS : InputIdInjective input₁)
    (hInputIdT : InputIdInjective input₂)
    (hInputEq : InputEquivalent input₁ input₂)
    (hSummaryS : LiveSummaryMatches input₁ summary) :
    B ∈ S.getConfirmed ↔ B ∈ T.getConfirmed := by
  have hLiveS : LiveComplete input₁ summary S :=
    parentFirstReplay_liveComplete hn hNoSlash hReplayS hPFS hNoDupS
      hNoGenesisS hInputIdS hSummaryS
  have hSummaryT : LiveSummaryMatches input₂ summary :=
    hInputEq.liveSummaryMatches hSummaryS
  have hLiveT : LiveComplete input₂ summary T :=
    parentFirstReplay_liveComplete hn hNoSlash hReplayT hPFT hNoDupT
      hNoGenesisT hInputIdT hSummaryT
  exact liveComplete_getConfirmed_inputEquivalent hInputEq hLiveS hLiveT

end Store

end DecoupledConsensus
