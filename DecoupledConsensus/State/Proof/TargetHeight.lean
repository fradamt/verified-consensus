import DecoupledConsensus.State.Proof.Invariants

namespace DecoupledConsensus

/-! # Target-height invariant

This file proves the slot/freshness part of the state-machine model that is
needed to recover the paper's Remark 2 in its adjusted form: when a chain state
has justified checkpoint `(J, hj)`, the subchain ending at `J` is at state
height `hj` (except for the genesis convention `hj = 0`).

The executable state is unchanged. The extra predicates below are proof-only
invariants over a chain prefix and a state associated with that prefix.
-/

variable {n : ℕ}

open scoped Block

attribute [local instance] Classical.propDecidable

namespace Block

lemma Ancestor.slot_lt_of_ne {X Y : Block n} (hXY : X ≼ Y)
    (hWFY : WellFormed Y) (hne : X ≠ Y) : X.slot < Y.slot := by
  have hle : X.slot ≤ Y.slot := hXY.slot_le hWFY
  by_contra hnot
  have hge : Y.slot ≤ X.slot := Nat.le_of_not_gt hnot
  have hYX : Y ≼ X :=
    Ancestor.le_of_slot_le hWFY (Ancestor.refl Y) hXY hge
  exact hne (Ancestor.antisymm hXY hYX hWFY)

end Block

private lemma ancestor_parent_of_mk_slot_lt {T parent : Block n} {bid s : ℕ}
    {vs : List (Vote n)}
    (hT : T ≼ Block.mk bid parent s vs) (hlt : T.slot < s) :
    T ≼ parent := by
  cases hT with
  | refl =>
      simp [Block.slot] at hlt
  | step h =>
      exact h

/-- Prefix height boundary: every ancestor in the current height window
    `[sh, tip.slot]` has subchain state-height equal to the state's `h`. -/
def PrefixHeightInv {B : Block n} (chain : Chain n B) (σ : State n) : Prop :=
  ∀ {T : Block n} (hT : T ≼ B),
    σ.sh ≤ T.slot → (stateOf (chain.subchain hT)).h = σ.h

/-- Strict version used while processing a block: the block itself has not yet
    been closed by the final `processHeight`, so freshness only needs targets
    with slot strictly below the current `L` slot. -/
def StrictHeightInv {B : Block n} (chain : Chain n B) (σ : State n) : Prop :=
  ∀ {T : Block n} (hT : T ≼ B),
    σ.sh ≤ T.slot → T.slot < σ.L.slot →
      (stateOf (chain.subchain hT)).h = σ.h

/-- Every recorded target is at the current state height on this chain prefix. -/
def TargetsHeightInv {B : Block n} (chain : Chain n B) (σ : State n) : Prop :=
  ∀ i T, σ.targets i = some T →
    ∀ hT : T ≼ B, (stateOf (chain.subchain hT)).h = σ.h

/-- The current justified checkpoint has the right target-height fact. The
    left disjunct records the genesis convention, where `hj = 0`. -/
def JTargetHeightInv {B : Block n} (chain : Chain n B) (σ : State n) : Prop :=
  (σ.hj = 0 ∧ σ.J = Block.genesis) ∨
    ∃ C : Block n, C = σ.J ∧
      ∃ hJ : C ≼ B, (stateOf (chain.subchain hJ)).h = σ.hj

private lemma subchain_height_eq {B T : Block n} (chain : Chain n B)
    (h₁ h₂ : T ≼ B) :
    (stateOf (chain.subchain h₁)).h =
      (stateOf (chain.subchain h₂)).h := by
  exact congrArg State.h (chain_unique _ _)

private lemma JTargetHeightInv_of_eq {B : Block n} {chain : Chain n B}
    {σ τ : State n}
    (hJ_eq : τ.J = σ.J) (hhj_eq : τ.hj = σ.hj)
    (h : JTargetHeightInv chain σ) :
    JTargetHeightInv chain τ := by
  rcases h with hzero | ⟨C, hC, hAnc, hHeight⟩
  · left
    constructor
    · exact hhj_eq.trans hzero.1
    · exact hJ_eq.trans hzero.2
  · right
    refine ⟨C, hC.trans hJ_eq.symm, hAnc, ?_⟩
    rw [hhj_eq]
    exact hHeight

private lemma processVoteCore_targets_eq_cases_strict
    (σ : State n) (v : Vote n) (i : Validator n) :
    (processVoteCore σ v).targets i = σ.targets i ∨
    (i = v.validator ∧ ∃ T,
      v.target = some T.id ∧ v.height = σ.h ∧
        T ≼ σ.L ∧ T.slot ≥ σ.sh ∧ T.slot < σ.L.slot ∧
          (processVoteCore σ v).targets i = some T) := by
  match h_target : v.target with
  | none =>
      left
      simp [processVoteCore, h_target]
      split_ifs <;> rfl
  | some bid =>
      match h_find : σ.L.findById bid with
      | none =>
          left
          simp [processVoteCore, h_target, h_find]
      | some T_v =>
          by_cases h_fresh :
              v.height = σ.h ∧ T_v.slot ≥ σ.sh ∧ T_v.slot < σ.L.slot
          · by_cases hi : i = v.validator
            · right
              refine ⟨hi, T_v, ?_, h_fresh.1, Block.findById_ancestor h_find,
                h_fresh.2.1, h_fresh.2.2, ?_⟩
              · rw [← Block.findById_id h_find]
              · subst hi
                simp [processVoteCore, h_target, h_find, h_fresh]
            · left
              simp [processVoteCore, h_target, h_find, h_fresh, Function.update, hi]
          · left
            simp [processVoteCore, h_target, h_find, h_fresh]

lemma genesis_prefixHeight : PrefixHeightInv (Chain.genesis : Chain n Block.genesis)
    (State.genesis n) := by
  intro T hT hslot
  cases hT
  simp [stateOf, State.genesis]

lemma genesis_targetsHeight : TargetsHeightInv (Chain.genesis : Chain n Block.genesis)
    (State.genesis n) := by
  intro i T heq hT
  simp [State.genesis] at heq

lemma genesis_JTargetHeight : JTargetHeightInv (Chain.genesis : Chain n Block.genesis)
    (State.genesis n) := by
  left
  simp [State.genesis]

lemma PrefixHeightInv.set_s {B : Block n} {chain : Chain n B} {σ : State n}
    (h : PrefixHeightInv chain σ) (s' : ℕ) :
    PrefixHeightInv chain ({σ with s := s'} : State n) := by
  intro T hT hslot
  exact h hT hslot

lemma StrictHeightInv.set_s {B : Block n} {chain : Chain n B} {σ : State n}
    (h : StrictHeightInv chain σ) (s' : ℕ) :
    StrictHeightInv chain ({σ with s := s'} : State n) := by
  intro T hT hslot hlt
  exact h hT hslot hlt

lemma TargetsHeightInv.set_s {B : Block n} {chain : Chain n B} {σ : State n}
    (h : TargetsHeightInv chain σ) (s' : ℕ) :
    TargetsHeightInv chain ({σ with s := s'} : State n) := by
  intro i T heq hT
  exact h i T heq hT

lemma JTargetHeightInv.set_s {B : Block n} {chain : Chain n B} {σ : State n}
    (h : JTargetHeightInv chain σ) (s' : ℕ) :
    JTargetHeightInv chain ({σ with s := s'} : State n) := by
  simpa using h

lemma processVoteCore_strictHeight_pres {B : Block n} (chain : Chain n B)
    (σ : State n) (v : Vote n)
    (h : StrictHeightInv chain σ) :
    StrictHeightInv chain (processVoteCore σ v) := by
  intro T hT hslot hlt
  have hslot' : σ.sh ≤ T.slot := by simpa using hslot
  have hlt' : T.slot < σ.L.slot := by simpa using hlt
  simpa using h hT hslot' hlt'

lemma processVote_strictHeight_pres {B : Block n} (chain : Chain n B)
    (σ : State n) (v : Vote n)
    (h : StrictHeightInv chain σ) :
    StrictHeightInv chain (processVote σ v) := by
  intro T hT hslot hlt
  have hslot' : σ.sh ≤ T.slot := by simpa using hslot
  have hlt' : T.slot < σ.L.slot := by simpa using hlt
  simpa using h hT hslot' hlt'

lemma processVoteCore_targetsHeight_pres {B : Block n} (chain : Chain n B)
    (σ : State n) (v : Vote n)
    (hStrict : StrictHeightInv chain σ)
    (hTargets : TargetsHeightInv chain σ) :
    TargetsHeightInv chain (processVoteCore σ v) := by
  intro i T heq hT
  rw [processVoteCore_h]
  rcases processVoteCore_targets_eq_cases_strict σ v i with hOld |
      ⟨_, T_v, _, _, _, hslot, hstrict, hSet⟩
  · rw [hOld] at heq
    exact hTargets i T heq hT
  · rw [hSet] at heq
    injection heq with hEq
    subst hEq
    exact hStrict hT hslot hstrict

lemma processVote_targetsHeight_pres {B : Block n} (chain : Chain n B)
    (σ : State n) (v : Vote n)
    (hStrict : StrictHeightInv chain σ)
    (hTargets : TargetsHeightInv chain σ) :
    TargetsHeightInv chain (processVote σ v) := by
  intro i T heq hT
  rw [processVote_targets] at heq
  simpa [processVote_h, processVoteCore_h] using
    processVoteCore_targetsHeight_pres chain σ v hStrict hTargets i T heq hT

lemma processVoteCore_JTargetHeight_pres {B : Block n} (chain : Chain n B)
    (σ : State n) (v : Vote n)
    (h : JTargetHeightInv chain σ) :
    JTargetHeightInv chain (processVoteCore σ v) := by
  exact JTargetHeightInv_of_eq (chain := chain)
    (by simp [processVoteCore_J]) (by simp [processVoteCore_hj]) h

lemma processVote_JTargetHeight_pres {B : Block n} (chain : Chain n B)
    (σ : State n) (v : Vote n)
    (h : JTargetHeightInv chain σ) :
    JTargetHeightInv chain (processVote σ v) := by
  exact JTargetHeightInv_of_eq (chain := chain)
    (by simp [processVote_J]) (by simp [processVote_hj]) h

lemma fold_processVote_height_pres {B : Block n} (chain : Chain n B)
    (vs : List (Vote n)) (σ : State n)
    (hStrict : StrictHeightInv chain σ)
    (hTargets : TargetsHeightInv chain σ)
    (hJ : JTargetHeightInv chain σ) :
    StrictHeightInv chain (vs.foldl processVote σ) ∧
      TargetsHeightInv chain (vs.foldl processVote σ) ∧
        JTargetHeightInv chain (vs.foldl processVote σ) := by
  induction vs generalizing σ with
  | nil =>
      simp [hStrict, hTargets, hJ]
  | cons v vs ih =>
      simp only [List.foldl_cons]
      exact ih _ (processVote_strictHeight_pres chain σ v hStrict)
        (processVote_targetsHeight_pres chain σ v hStrict hTargets)
        (processVote_JTargetHeight_pres chain σ v hJ)

lemma processHeight_targetsHeight_pres {B : Block n} (chain : Chain n B)
    (σ : State n)
    (hTargets : TargetsHeightInv chain σ) :
    TargetsHeightInv chain (processHeight σ) := by
  intro i T heq hT
  unfold processHeight processHeightEvents at heq ⊢
  cases hFirst : firstJustifiedTarget (applyFinality σ) with
  | some T' =>
      simp [hFirst] at heq
  | none =>
      cases hTO : timeoutFiresBool (applyFinality σ) with
      | true =>
          simp [hFirst, hTO] at heq
      | false =>
          simp [hFirst, hTO] at heq ⊢
          exact hTargets i T heq hT

lemma processHeight_JTargetHeight_pres {B : Block n} (chain : Chain n B)
    (σ : State n)
    (hJ : JTargetHeightInv chain σ)
    (hTargets : TargetsHeightInv chain σ)
    (hTargetsAnc : TargetsAncInv σ)
    (hL : σ.L = B) :
    JTargetHeightInv chain (processHeight σ) := by
  unfold processHeight processHeightEvents
  cases hFirst : firstJustifiedTarget (applyFinality σ) with
  | some T =>
      simp [hFirst]
      right
      have hJust : Justified (applyFinality σ) T :=
        firstJustifiedTarget_sound hFirst
      obtain ⟨i, hi⟩ := justified_extract_witness hJust
      rw [applyFinality_targets] at hi
      have hAncB : T ≼ B := by
        simpa [hL] using hTargetsAnc i T hi
      refine ⟨T, rfl, hAncB, ?_⟩
      simpa [applyFinality_h] using hTargets i T hi hAncB
  | none =>
      cases hTO : timeoutFiresBool (applyFinality σ) with
      | true =>
          exact JTargetHeightInv_of_eq (chain := chain)
            (by simp [hFirst, hTO]) (by simp [hFirst, hTO]) hJ
      | false =>
          exact JTargetHeightInv_of_eq (chain := chain)
            (by simp [hFirst, hTO]) (by simp [hFirst, hTO]) hJ

lemma processHeight_prefix_empty_pres {B : Block n} (chain : Chain n B)
    (σ : State n)
    (hPrefix : PrefixHeightInv chain σ)
    (hEmpty : B.slot < σ.s) :
    PrefixHeightInv chain (processHeight σ) := by
  intro T hT hslot
  have hWF : Block.WellFormed B := chain_tip_wellformed chain
  have hTslot : T.slot ≤ B.slot := hT.slot_le hWF
  unfold processHeight processHeightEvents at hslot ⊢
  cases hFirst : firstJustifiedTarget (applyFinality σ) with
  | some T' =>
      simp [hFirst] at hslot ⊢
      omega
  | none =>
      cases hTO : timeoutFiresBool (applyFinality σ) with
      | true =>
          simp [hFirst, hTO] at hslot ⊢
          omega
      | false =>
          simp [hFirst, hTO] at hslot ⊢
          exact hPrefix hT hslot

lemma processSlot_prefixHeight_pres {B : Block n} (chain : Chain n B)
    (σ : State n)
    (hPrefix : PrefixHeightInv chain σ)
    (hL : σ.L = B) :
    PrefixHeightInv chain (processSlot σ) := by
  by_cases hEmpty : σ.L.slot < σ.s
  · have hEmptyB : B.slot < σ.s := by simpa [hL] using hEmpty
    simpa [processSlot, hEmpty] using
      PrefixHeightInv.set_s (processHeight_prefix_empty_pres chain σ hPrefix hEmptyB)
        (σ.s + 1)
  · simpa [processSlot, hEmpty] using PrefixHeightInv.set_s hPrefix (σ.s + 1)

lemma processSlot_targetsHeight_pres {B : Block n} (chain : Chain n B)
    (σ : State n)
    (hTargets : TargetsHeightInv chain σ) :
    TargetsHeightInv chain (processSlot σ) := by
  by_cases hEmpty : σ.L.slot < σ.s
  · simpa [processSlot, hEmpty] using
      TargetsHeightInv.set_s (processHeight_targetsHeight_pres chain σ hTargets)
        (σ.s + 1)
  · simpa [processSlot, hEmpty] using TargetsHeightInv.set_s hTargets (σ.s + 1)

lemma processSlot_JTargetHeight_pres {B : Block n} (chain : Chain n B)
    (σ : State n)
    (hJ : JTargetHeightInv chain σ)
    (hTargets : TargetsHeightInv chain σ)
    (hTargetsAnc : TargetsAncInv σ)
    (hL : σ.L = B) :
    JTargetHeightInv chain (processSlot σ) := by
  by_cases hEmpty : σ.L.slot < σ.s
  · simpa [processSlot, hEmpty] using
      JTargetHeightInv.set_s
        (processHeight_JTargetHeight_pres chain σ hJ hTargets hTargetsAnc hL)
        (σ.s + 1)
  · simpa [processSlot, hEmpty] using JTargetHeightInv.set_s hJ (σ.s + 1)

lemma iterateProcessSlot_height_pres {B : Block n} (chain : Chain n B)
    (σ : State n) (k : ℕ)
    (hPrefix : PrefixHeightInv chain σ)
    (hTargets : TargetsHeightInv chain σ)
    (hJ : JTargetHeightInv chain σ)
    (hTargetsAnc : TargetsAncInv σ)
    (hL : σ.L = B) :
    PrefixHeightInv chain (iterateProcessSlot σ k) ∧
      TargetsHeightInv chain (iterateProcessSlot σ k) ∧
        JTargetHeightInv chain (iterateProcessSlot σ k) := by
  induction k generalizing σ with
  | zero =>
      simp [iterateProcessSlot, hPrefix, hTargets, hJ]
  | succ k ih =>
      show PrefixHeightInv chain (iterateProcessSlot (processSlot σ) k) ∧
        TargetsHeightInv chain (iterateProcessSlot (processSlot σ) k) ∧
          JTargetHeightInv chain (iterateProcessSlot (processSlot σ) k)
      apply ih
      · exact processSlot_prefixHeight_pres chain σ hPrefix hL
      · exact processSlot_targetsHeight_pres chain σ hTargets
      · exact processSlot_JTargetHeight_pres chain σ hJ hTargets hTargetsAnc hL
      · exact processSlot_targets_anc_pres σ hTargetsAnc
      · rw [processSlot_L]
        exact hL

lemma extend_strictHeight_init {parent : Block n} (c : Chain n parent)
    (bid : BlockId) (newSlot : ℕ) (votes : List (Vote n))
    (hSlot : newSlot > parent.slot) (σ : State n)
    (hPrefix : PrefixHeightInv c σ) :
    StrictHeightInv (Chain.extend c bid newSlot votes hSlot)
      ({σ with L := Block.mk bid parent newSlot votes} : State n) := by
  intro T hT hslot hlt
  have hParent : T ≼ parent :=
    ancestor_parent_of_mk_slot_lt hT (by simpa [Block.slot] using hlt)
  have hOld := hPrefix hParent hslot
  have hEq :
      (stateOf ((Chain.extend c bid newSlot votes hSlot).subchain hT)).h =
        (stateOf (c.subchain hParent)).h :=
    congrArg State.h (chain_unique _ _)
  rw [hEq]
  exact hOld

lemma extend_targetsHeight_init {parent : Block n} (c : Chain n parent)
    (bid : BlockId) (newSlot : ℕ) (votes : List (Vote n))
    (hSlot : newSlot > parent.slot) (σ : State n)
    (hTargets : TargetsHeightInv c σ)
    (hTargetsAnc : TargetsAncInv σ)
    (hL : σ.L = parent) :
    TargetsHeightInv (Chain.extend c bid newSlot votes hSlot)
      ({σ with L := Block.mk bid parent newSlot votes} : State n) := by
  intro i T heq hT
  have hParent : T ≼ parent := by
    simpa [hL] using hTargetsAnc i T heq
  have hOld := hTargets i T heq hParent
  have hEq :
      (stateOf ((Chain.extend c bid newSlot votes hSlot).subchain hT)).h =
        (stateOf (c.subchain hParent)).h :=
    congrArg State.h (chain_unique _ _)
  rw [hEq]
  exact hOld

lemma extend_JTargetHeight_init {parent : Block n} (c : Chain n parent)
    (bid : BlockId) (newSlot : ℕ) (votes : List (Vote n))
    (hSlot : newSlot > parent.slot) (σ : State n)
    (hJ : JTargetHeightInv c σ) :
    JTargetHeightInv (Chain.extend c bid newSlot votes hSlot)
      ({σ with L := Block.mk bid parent newSlot votes} : State n) := by
  rcases hJ with hzero | ⟨C, hC, hAnc, hHeight⟩
  · left
    exact hzero
  · right
    refine ⟨C, hC, Block.Ancestor.step hAnc, ?_⟩
    have hEq :
        (stateOf ((Chain.extend c bid newSlot votes hSlot).subchain
          (Block.Ancestor.step hAnc))).h =
          (stateOf (c.subchain hAnc)).h :=
      congrArg State.h (chain_unique _ _)
    rw [hEq]
    exact hHeight

lemma processBlock_height_pres {B : Block n} (chain : Chain n B)
    (σ : State n)
    (hStrict : StrictHeightInv chain ({ σ with L := B } : State n))
    (hTargets : TargetsHeightInv chain ({ σ with L := B } : State n))
    (hJ : JTargetHeightInv chain ({ σ with L := B } : State n)) :
    StrictHeightInv chain (processBlock σ B) ∧
      TargetsHeightInv chain (processBlock σ B) ∧
        JTargetHeightInv chain (processBlock σ B) := by
  unfold processBlock
  exact fold_processVote_height_pres chain B.votes ({ σ with L := B } : State n)
    hStrict hTargets hJ

lemma processHeight_prefix_tip_pres {B : Block n} (chain : Chain n B)
    (σ : State n)
    (hStrict : StrictHeightInv chain σ)
    (hL : σ.L = B)
    (hs : σ.s = B.slot)
    (hState : stateOf chain = processHeight σ) :
    PrefixHeightInv chain (processHeight σ) := by
  intro T hT hslot
  have hWF : Block.WellFormed B := chain_tip_wellformed chain
  by_cases hEq : T = B
  · subst hEq
    have hSame :
        (stateOf (chain.subchain hT)).h = (stateOf chain).h :=
      congrArg State.h (chain_unique _ _)
    rw [hSame, hState]
  · have hlt : T.slot < B.slot :=
      hT.slot_lt_of_ne hWF hEq
    unfold processHeight processHeightEvents at hslot ⊢
    cases hFirst : firstJustifiedTarget (applyFinality σ) with
    | some T' =>
        simp [hFirst] at hslot ⊢
        omega
    | none =>
        cases hTO : timeoutFiresBool (applyFinality σ) with
        | true =>
            simp [hFirst, hTO] at hslot ⊢
            omega
        | false =>
            simp [hFirst, hTO] at hslot ⊢
            exact hStrict hT hslot (by simpa [hL] using hlt)

/-- Combined chain-level target-height invariants. -/
theorem chain_height_target_invs {B : Block n} (chain : Chain n B) :
    PrefixHeightInv chain (stateOf chain) ∧
      TargetsHeightInv chain (stateOf chain) ∧
        JTargetHeightInv chain (stateOf chain) := by
  induction chain with
  | genesis =>
      exact ⟨genesis_prefixHeight, genesis_targetsHeight, genesis_JTargetHeight⟩
  | @extend parent c bid newSlot votes hSlot ih =>
      let B' : Block n := Block.mk bid parent newSlot votes
      let chain' : Chain n B' := Chain.extend c bid newSlot votes hSlot
      let σ0 : State n := stateOf c
      let k : ℕ := B'.slot - σ0.s
      let σSlots : State n := iterateProcessSlot σ0 k
      let σBlock : State n := processBlock σSlots B'
      have hL0 : σ0.L = parent := by
        dsimp [σ0]
        exact chain_state_L_eq_tip c
      have hTargetsAnc0 : TargetsAncInv σ0 := by
        dsimp [σ0]
        exact chain_targets_anc c
      obtain ⟨hPrefix0, hTargets0, hJ0⟩ := ih
      have hIter := iterateProcessSlot_height_pres c σ0 k
        hPrefix0 hTargets0 hJ0 hTargetsAnc0 hL0
      have hPrefixSlots : PrefixHeightInv c σSlots := hIter.1
      have hTargetsSlots : TargetsHeightInv c σSlots := hIter.2.1
      have hJSlots : JTargetHeightInv c σSlots := hIter.2.2
      have hTargetsAncSlots : TargetsAncInv σSlots := by
        dsimp [σSlots, k, σ0]
        exact iterateProcessSlot_targets_anc_pres (stateOf c)
          (B'.slot - (stateOf c).s) (chain_targets_anc c)
      have hLSlots : σSlots.L = parent := by
        dsimp [σSlots, k, σ0]
        rw [iterateProcessSlot_L, chain_state_L_eq_tip]
      have hStrictInit :
          StrictHeightInv chain' ({σSlots with L := B'} : State n) :=
        extend_strictHeight_init c bid newSlot votes hSlot σSlots hPrefixSlots
      have hTargetsInit :
          TargetsHeightInv chain' ({σSlots with L := B'} : State n) :=
        extend_targetsHeight_init c bid newSlot votes hSlot σSlots
          hTargetsSlots hTargetsAncSlots hLSlots
      have hJInit :
          JTargetHeightInv chain' ({σSlots with L := B'} : State n) :=
        extend_JTargetHeight_init c bid newSlot votes hSlot σSlots hJSlots
      have hBlock := processBlock_height_pres chain' σSlots hStrictInit hTargetsInit hJInit
      have hStrictBlock : StrictHeightInv chain' σBlock := by
        dsimp [σBlock]
        exact hBlock.1
      have hTargetsBlock : TargetsHeightInv chain' σBlock := by
        dsimp [σBlock]
        exact hBlock.2.1
      have hJBlock : JTargetHeightInv chain' σBlock := by
        dsimp [σBlock]
        exact hBlock.2.2
      have hTargetsAncBlock : TargetsAncInv σBlock := by
        dsimp [σBlock]
        apply processBlock_targets_anc_pres
        · exact hTargetsAncSlots
        · rw [hLSlots]
          exact Block.Ancestor.step (Block.Ancestor.refl parent)
      have hsSlots : σSlots.s = B'.slot := by
        dsimp [σSlots, k, σ0, B']
        rw [iterateProcessSlot_s_eq]
        have hle : (stateOf c).s ≤ (Block.mk bid parent newSlot votes).slot := by
          rw [chain_state_s_eq_tip_slot]
          exact Nat.le_of_lt hSlot
        omega
      have hLBlock : σBlock.L = B' := by
        dsimp [σBlock]
        rw [processBlock_L]
      have hsBlock : σBlock.s = B'.slot := by
        dsimp [σBlock]
        rw [processBlock_s]
        exact hsSlots
      have hState : stateOf chain' = processHeight σBlock := by
        dsimp [chain', σBlock, σSlots, k, σ0, B', stateOf, stateTransition]
      have hPrefixFinal : PrefixHeightInv chain' (processHeight σBlock) :=
        processHeight_prefix_tip_pres chain' σBlock hStrictBlock hLBlock hsBlock hState
      have hTargetsFinal : TargetsHeightInv chain' (processHeight σBlock) :=
        processHeight_targetsHeight_pres chain' σBlock hTargetsBlock
      have hJFinal : JTargetHeightInv chain' (processHeight σBlock) :=
        processHeight_JTargetHeight_pres chain' σBlock hJBlock hTargetsBlock
          hTargetsAncBlock hLBlock
      show PrefixHeightInv chain' (stateOf chain') ∧
        TargetsHeightInv chain' (stateOf chain') ∧
          JTargetHeightInv chain' (stateOf chain')
      rw [hState]
      exact ⟨hPrefixFinal, hTargetsFinal, hJFinal⟩

theorem chain_J_target_height {B : Block n} (chain : Chain n B) :
    JTargetHeightInv chain (stateOf chain) :=
  (chain_height_target_invs chain).2.2

theorem chain_justified_target_height {B C : Block n} {h : ℕ}
    (chain : Chain n B)
    (hJ : (stateOf chain).J = C)
    (hhj : (stateOf chain).hj = h)
    (hAnc : C ≼ B) :
    (h = 0 ∧ C = Block.genesis) ∨
      (stateOf (chain.subchain hAnc)).h = h := by
  rcases chain_J_target_height chain with hzero | ⟨C₀, hC₀, hJAnc, hHeight⟩
  · left
    constructor
    · exact hhj.symm.trans hzero.1
    · exact hJ.symm.trans hzero.2
  · right
    subst C₀
    subst C
    subst h
    have hSame :
        (stateOf (chain.subchain hAnc)).h =
          (stateOf (chain.subchain hJAnc)).h :=
      subchain_height_eq chain hAnc hJAnc
    rw [hSame]
    exact hHeight

theorem chain_justified_target_height_of_ne_zero {B C : Block n} {h : ℕ}
    (chain : Chain n B)
    (hJ : (stateOf chain).J = C)
    (hhj : (stateOf chain).hj = h)
    (hAnc : C ≼ B)
    (h_ne : h ≠ 0) :
    (stateOf (chain.subchain hAnc)).h = h := by
  rcases chain_justified_target_height chain hJ hhj hAnc with hzero | hHeight
  · exact False.elim (h_ne hzero.1)
  · exact hHeight

end DecoupledConsensus
