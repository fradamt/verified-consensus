import DecoupledConsensus.State.Proof.Facts

namespace DecoupledConsensus

/-! # Accountable Safety Proofs: invariants

State and chain invariants for targets, checkpoint ordering, finality witnesses,
justification witnesses, and the genesis/height-zero relationship. -/

variable {n : ℕ}

open scoped Block

attribute [local instance] Classical.propDecidable

/-! ### Invariant 5: `hj ≤ h` -/

/-- `processHeight` preserves `hj ≤ h`. -/
lemma processHeight_hj_le_h (σ : State n) (h_inv : σ.hj ≤ σ.h) :
    (processHeight σ).hj ≤ (processHeight σ).h := by
  unfold processHeight processHeightEvents
  cases hFirst : firstJustifiedTarget (applyFinality σ) with
  | some T => simp [hFirst]
  | none =>
      cases hTO : timeoutFiresBool (applyFinality σ)
      · simpa [hFirst, hTO] using h_inv
      · simp [hFirst, hTO]; omega

/-- `processHeight` cannot decrease `hj`, assuming the standard `hj ≤ h`
    invariant for the justification branch. -/
lemma processHeight_hj_mono (σ : State n) (h_inv : σ.hj ≤ σ.h) :
    σ.hj ≤ (processHeight σ).hj := by
  unfold processHeight processHeightEvents
  cases hFirst : firstJustifiedTarget (applyFinality σ) with
  | some T => simp [hFirst, h_inv]
  | none =>
      cases hTO : timeoutFiresBool (applyFinality σ) <;> simp [hFirst, hTO]

/-- `processSlot` preserves `hj ≤ h`. -/
lemma processSlot_hj_le_h (σ : State n) (h_inv : σ.hj ≤ σ.h) :
    (processSlot σ).hj ≤ (processSlot σ).h := by
  by_cases hEmpty : σ.L.slot < σ.s
  · simpa [processSlot, hEmpty] using processHeight_hj_le_h σ h_inv
  · simpa [processSlot, hEmpty] using h_inv

/-- `iterateProcessSlot` preserves `hj ≤ h`. -/
lemma iterateProcessSlot_hj_le_h (σ : State n) (k : ℕ) (h_inv : σ.hj ≤ σ.h) :
    (iterateProcessSlot σ k).hj ≤ (iterateProcessSlot σ k).h := by
  induction k generalizing σ with
  | zero => simpa [iterateProcessSlot]
  | succ k ih =>
    change (iterateProcessSlot (processSlot σ) k).hj
        ≤ (iterateProcessSlot (processSlot σ) k).h
    exact ih _ (processSlot_hj_le_h σ h_inv)

/-- **Invariant 5**: `hj ≤ h` at every chain tip-state. -/
lemma chain_hj_le_h {B : Block n} (chain : Chain n B) :
    (stateOf chain).hj ≤ (stateOf chain).h := by
  induction chain with
  | genesis => simp [stateOf, State.genesis]
  | extend c bid newSlot votes hSlot ih =>
    change (stateTransition (stateOf c) (Block.mk bid _ newSlot votes)).hj
        ≤ (stateTransition (stateOf c) (Block.mk bid _ newSlot votes)).h
    unfold stateTransition
    apply processHeight_hj_le_h
    simp only [processBlock_hj, processBlock_h]
    exact iterateProcessSlot_hj_le_h _ _ ih

/-! ### Strengthening: justified heights are below `h` -/

lemma processHeight_hj_lt_h (σ : State n) (h_inv : σ.hj < σ.h) :
    (processHeight σ).hj < (processHeight σ).h := by
  unfold processHeight processHeightEvents
  cases hFirst : firstJustifiedTarget (applyFinality σ) with
  | some T => simp [hFirst]
  | none =>
      cases hTO : timeoutFiresBool (applyFinality σ)
      · simpa [hFirst, hTO] using h_inv
      · simp [hFirst, hTO]; omega

lemma processSlot_hj_lt_h (σ : State n) (h_inv : σ.hj < σ.h) :
    (processSlot σ).hj < (processSlot σ).h := by
  by_cases hEmpty : σ.L.slot < σ.s
  · simpa [processSlot, hEmpty] using processHeight_hj_lt_h σ h_inv
  · simpa [processSlot, hEmpty] using h_inv

lemma iterateProcessSlot_hj_lt_h (σ : State n) (k : ℕ) (h_inv : σ.hj < σ.h) :
    (iterateProcessSlot σ k).hj < (iterateProcessSlot σ k).h := by
  induction k generalizing σ with
  | zero => simpa [iterateProcessSlot]
  | succ k ih =>
    change (iterateProcessSlot (processSlot σ) k).hj
        < (iterateProcessSlot (processSlot σ) k).h
    exact ih _ (processSlot_hj_lt_h σ h_inv)

lemma chain_hj_lt_h {B : Block n} (chain : Chain n B) :
    (stateOf chain).hj < (stateOf chain).h := by
  induction chain with
  | genesis => simp [stateOf, State.genesis]
  | extend c bid newSlot votes hSlot ih =>
    change (stateTransition (stateOf c) (Block.mk bid _ newSlot votes)).hj
        < (stateTransition (stateOf c) (Block.mk bid _ newSlot votes)).h
    unfold stateTransition
    apply processHeight_hj_lt_h
    simp only [processBlock_hj, processBlock_h]
    exact iterateProcessSlot_hj_lt_h _ _ ih

/-! ### Invariant 6: `sh ≤ s` -/

/-- `processHeight` preserves `sh ≤ s`. -/
lemma processHeight_sh_le_s (σ : State n) (h_inv : σ.sh ≤ σ.s) :
    (processHeight σ).sh ≤ (processHeight σ).s := by
  unfold processHeight processHeightEvents
  cases hFirst : firstJustifiedTarget (applyFinality σ) with
  | some T => simp [hFirst]
  | none =>
      cases hTO : timeoutFiresBool (applyFinality σ)
      · simpa [hFirst, hTO] using h_inv
      · simp [hFirst, hTO]

/-- `processSlot` preserves `sh ≤ s`. -/
lemma processSlot_sh_le_s (σ : State n) (h_inv : σ.sh ≤ σ.s) :
    (processSlot σ).sh ≤ (processSlot σ).s := by
  by_cases hEmpty : σ.L.slot < σ.s
  · have h1 : (processHeight σ).sh ≤ (processHeight σ).s :=
      processHeight_sh_le_s σ h_inv
    rw [processHeight_s] at h1
    simpa [processSlot, hEmpty] using h1.trans (Nat.le_succ _)
  · simpa [processSlot, hEmpty] using h_inv.trans (Nat.le_succ _)

/-- `iterateProcessSlot` preserves `sh ≤ s`. -/
lemma iterateProcessSlot_sh_le_s (σ : State n) (k : ℕ) (h_inv : σ.sh ≤ σ.s) :
    (iterateProcessSlot σ k).sh ≤ (iterateProcessSlot σ k).s := by
  induction k generalizing σ with
  | zero => simpa [iterateProcessSlot]
  | succ k ih =>
    change (iterateProcessSlot (processSlot σ) k).sh
        ≤ (iterateProcessSlot (processSlot σ) k).s
    exact ih _ (processSlot_sh_le_s σ h_inv)

/-- **Invariant 6**: `sh ≤ tip.slot` at every chain tip-state. -/
lemma chain_sh_le_tip_slot {B : Block n} (chain : Chain n B) :
    (stateOf chain).sh ≤ B.slot := by
  induction chain with
  | genesis => simp [stateOf, State.genesis, Block.slot]
  | @extend parent c bid newSlot votes hSlot ih =>
    -- (stateTransition σ B).sh
    --   = (processBlock _ B).sh
    --   = (iterateProcessSlot σ k).sh    [processBlock_sh]
    -- iterate preserves sh ≤ s, and the iteration ends with s = B.slot.
    change (stateTransition (stateOf c) (Block.mk bid parent newSlot votes)).sh
        ≤ (Block.mk bid parent newSlot votes).slot
    unfold stateTransition
    set k := (Block.mk bid parent newSlot votes).slot - (stateOf c).s with hk
    have h1 : (stateOf c).sh ≤ (stateOf c).s := by
      rw [chain_state_s_eq_tip_slot]
      exact ih
    have h2 := iterateProcessSlot_sh_le_s (stateOf c) k h1
    have hs_iter : (iterateProcessSlot (stateOf c) k).s =
        (Block.mk bid parent newSlot votes).slot := by
      have hle : (stateOf c).s ≤ (Block.mk bid parent newSlot votes).slot := by
        rw [chain_state_s_eq_tip_slot]
        exact Nat.le_of_lt hSlot
      rw [iterateProcessSlot_s_eq, hk]
      exact Nat.add_sub_of_le hle
    have h_post :
        (processBlock (iterateProcessSlot (stateOf c) k)
          (Block.mk bid parent newSlot votes)).sh ≤
        (processBlock (iterateProcessSlot (stateOf c) k)
          (Block.mk bid parent newSlot votes)).s := by
      simpa [processBlock_sh, processBlock_s] using h2
    have h_closed :=
      processHeight_sh_le_s
        (processBlock (iterateProcessSlot (stateOf c) k)
          (Block.mk bid parent newSlot votes)) h_post
    rw [processHeight_s, processBlock_s, hs_iter] at h_closed
    simpa [hk] using h_closed

/-! ### Invariant 1: targets are ancestors of L

Whenever `σ.targets i = some T` for the chain-tip state `σ`, then `T ≼ σ.L`.
This is the freshness-of-targets invariant, the technical heart of safety. -/

/-- The "targets are ancestors of L" invariant on a state. -/
def TargetsAncInv (σ : State n) : Prop :=
  ∀ i T, σ.targets i = some T → T ≼ σ.L

/-- Genesis state trivially satisfies the invariant (all targets are `none`). -/
lemma genesis_targets_anc : TargetsAncInv (State.genesis n) := by
  intro i T heq
  simp [State.genesis] at heq

/-- `processVoteCore` preserves the invariant: it either leaves targets[i]
    unchanged (use IH) or sets it to a target whose freshness witness gives
    `T ≼ σ.L`. Since `processVoteCore` doesn't change `L`, the invariant
    holds in the post-state. -/
lemma processVoteCore_targets_anc_pres (σ : State n) (v : Vote n)
    (h : TargetsAncInv σ) : TargetsAncInv (processVoteCore σ v) := by
  intro i T heq
  rw [processVoteCore_L]
  rcases processVoteCore_targets_eq_cases σ v i with h_eq | ⟨_, T_v, _, _, h_anc, _, h_after⟩
  · rw [h_eq] at heq
    exact h _ _ heq
  · rw [h_after] at heq
    -- heq : some T_v = some T
    injection heq with hTT
    -- hTT : T_v = T
    rw [← hTT]; exact h_anc

/-- `processVote` preserves the invariant (the outer `P`-update doesn't
    touch `targets` or `L`). -/
lemma processVote_targets_anc_pres (σ : State n) (v : Vote n)
    (h : TargetsAncInv σ) : TargetsAncInv (processVote σ v) := by
  intro i T heq
  rw [processVote_L]
  rw [processVote_targets] at heq
  -- heq : (processVoteCore σ v).targets i = some T
  -- Use processVoteCore_targets_anc_pres which gives T ≼ (processVoteCore σ v).L = σ.L.
  have hC := processVoteCore_targets_anc_pres σ v h i T heq
  rwa [processVoteCore_L] at hC

/-- `processHeight` preserves the invariant. Either the height advances
    (targets get reset to `fun _ => none`, vacuous) or no advance
    (targets and L unchanged). -/
lemma processHeight_targets_anc_pres (σ : State n) (h : TargetsAncInv σ) :
    TargetsAncInv (processHeight σ) := by
  intro i T heq
  rw [processHeight_L]
  unfold processHeight processHeightEvents at heq
  cases hFirst : firstJustifiedTarget (applyFinality σ) with
  | some T' =>
      simp [hFirst] at heq
  | none =>
      cases hTO : timeoutFiresBool (applyFinality σ) with
      | true =>
          simp [hFirst, hTO] at heq
      | false =>
          simp [hFirst, hTO] at heq
          exact h _ _ heq

/-- `processSlot` preserves the invariant. -/
lemma processSlot_targets_anc_pres (σ : State n) (h : TargetsAncInv σ) :
    TargetsAncInv (processSlot σ) := by
  by_cases hEmpty : σ.L.slot < σ.s
  · intro i T heq
    have heq' : (processHeight σ).targets i = some T := by
      simpa [processSlot, hEmpty] using heq
    have hT := processHeight_targets_anc_pres σ h i T heq'
    simpa [processSlot, hEmpty] using hT
  · simpa [processSlot, hEmpty] using h

/-- `iterateProcessSlot` preserves the invariant. -/
lemma iterateProcessSlot_targets_anc_pres (σ : State n) (k : ℕ)
    (h : TargetsAncInv σ) : TargetsAncInv (iterateProcessSlot σ k) := by
  induction k generalizing σ with
  | zero => simpa [iterateProcessSlot]
  | succ k ih =>
    change TargetsAncInv (iterateProcessSlot (processSlot σ) k)
    exact ih _ (processSlot_targets_anc_pres σ h)

/-- `processBlock σ B` preserves the invariant under chain extension
    (the new `L = B` is a descendant of the old `L`). -/
lemma processBlock_targets_anc_pres (σ : State n) (B : Block n)
    (h : TargetsAncInv σ) (h_chain : σ.L ≼ B) :
    TargetsAncInv (processBlock σ B) := by
  unfold processBlock
  -- Show inv for {σ with L := B} (initial state of fold).
  have h_init : TargetsAncInv ({σ with L := B} : State n) := by
    intro i T heq
    have h1 : σ.targets i = some T := heq
    exact (h _ _ h1).trans h_chain
  -- Now induct on the fold: each processVote preserves the invariant.
  suffices ∀ τ : State n, TargetsAncInv τ → TargetsAncInv (B.votes.foldl processVote τ) by
    exact this _ h_init
  intro τ hτ
  induction B.votes generalizing τ with
  | nil => simpa
  | cons v vs ih =>
    simp only [List.foldl_cons]
    exact ih _ (processVote_targets_anc_pres τ v hτ)

/-- `stateTransition σ B` preserves the invariant under chain extension. -/
lemma stateTransition_targets_anc_pres (σ : State n) (B : Block n)
    (h : TargetsAncInv σ) (h_chain : σ.L ≼ B) :
    TargetsAncInv (stateTransition σ B) := by
  unfold stateTransition
  apply processHeight_targets_anc_pres
  apply processBlock_targets_anc_pres
  · exact iterateProcessSlot_targets_anc_pres _ _ h
  · rw [iterateProcessSlot_L]; exact h_chain

/-- **Invariant 1**: at every chain tip-state `(stateOf chain)`,
    `targets[i] = some T` implies `T ≼ B`. -/
lemma chain_targets_anc {B : Block n} (chain : Chain n B) :
    TargetsAncInv (stateOf chain) := by
  induction chain with
  | genesis => exact genesis_targets_anc
  | @extend parent c bid newSlot votes hSlot ih =>
    change TargetsAncInv (stateTransition (stateOf c) (Block.mk bid parent newSlot votes))
    apply stateTransition_targets_anc_pres _ _ ih
    rw [chain_state_L_eq_tip]
    exact .step (.refl _)

/-! ### Invariant 2: targets are slot-bounded by `sh`

Whenever `σ.targets i = some T`, then `T.slot ≥ σ.sh`. This comes from
the `T.slot ≥ σ.sh` clause of the freshness check. -/

/-- The "targets-slot-bound" invariant on a state. -/
def TargetsSlotInv (σ : State n) : Prop :=
  ∀ i T, σ.targets i = some T → T.slot ≥ σ.sh

lemma genesis_targets_slot : TargetsSlotInv (State.genesis n) := by
  intro i T heq; simp [State.genesis] at heq

lemma processVoteCore_targets_slot_pres (σ : State n) (v : Vote n)
    (h : TargetsSlotInv σ) : TargetsSlotInv (processVoteCore σ v) := by
  intro i T heq
  rw [processVoteCore_sh]
  rcases processVoteCore_targets_eq_cases σ v i with h_eq | ⟨_, T_v, _, _, _, h_slot, h_after⟩
  · rw [h_eq] at heq; exact h _ _ heq
  · rw [h_after] at heq
    injection heq with hTT
    rw [← hTT]; exact h_slot

lemma processVote_targets_slot_pres (σ : State n) (v : Vote n)
    (h : TargetsSlotInv σ) : TargetsSlotInv (processVote σ v) := by
  intro i T heq
  rw [processVote_sh]
  rw [processVote_targets] at heq
  have hC := processVoteCore_targets_slot_pres σ v h i T heq
  rwa [processVoteCore_sh] at hC

lemma processHeight_targets_slot_pres (σ : State n) (h : TargetsSlotInv σ) :
    TargetsSlotInv (processHeight σ) := by
  intro i T heq
  -- (processHeight σ).sh: either σ.sh (no advance) or σ.L.slot (advance + targets reset).
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
          exact h _ _ heq

lemma processSlot_targets_slot_pres (σ : State n) (h : TargetsSlotInv σ) :
    TargetsSlotInv (processSlot σ) := by
  by_cases hEmpty : σ.L.slot < σ.s
  · simpa [processSlot, hEmpty] using processHeight_targets_slot_pres σ h
  · simpa [processSlot, hEmpty] using h

lemma iterateProcessSlot_targets_slot_pres (σ : State n) (k : ℕ)
    (h : TargetsSlotInv σ) : TargetsSlotInv (iterateProcessSlot σ k) := by
  induction k generalizing σ with
  | zero => simpa [iterateProcessSlot]
  | succ k ih =>
    change TargetsSlotInv (iterateProcessSlot (processSlot σ) k)
    exact ih _ (processSlot_targets_slot_pres σ h)

lemma processBlock_targets_slot_pres (σ : State n) (B : Block n)
    (h : TargetsSlotInv σ) : TargetsSlotInv (processBlock σ B) := by
  unfold processBlock
  have h_init : TargetsSlotInv ({σ with L := B} : State n) := by
    intro i T heq
    have h1 : σ.targets i = some T := heq
    exact h _ _ h1
  suffices ∀ τ : State n, TargetsSlotInv τ → TargetsSlotInv (B.votes.foldl processVote τ) by
    exact this _ h_init
  intro τ hτ
  induction B.votes generalizing τ with
  | nil => simpa
  | cons v vs ih =>
    simp only [List.foldl_cons]
    exact ih _ (processVote_targets_slot_pres τ v hτ)

lemma stateTransition_targets_slot_pres (σ : State n) (B : Block n)
    (h : TargetsSlotInv σ) : TargetsSlotInv (stateTransition σ B) := by
  unfold stateTransition
  apply processHeight_targets_slot_pres
  apply processBlock_targets_slot_pres
  exact iterateProcessSlot_targets_slot_pres _ _ h

/-- **Invariant 2**: at every chain tip-state, `targets[i] = some T → T.slot ≥ sh`. -/
lemma chain_targets_slot {B : Block n} (chain : Chain n B) :
    TargetsSlotInv (stateOf chain) := by
  induction chain with
  | genesis => exact genesis_targets_slot
  | @extend parent c bid newSlot votes hSlot ih =>
    change TargetsSlotInv (stateTransition (stateOf c) (Block.mk bid parent newSlot votes))
    exact stateTransition_targets_slot_pres _ _ ih

/-! ### Invariant 3: `J ≼ L` -/

/-- The `J ≼ L` invariant. -/
def J_le_L_Inv (σ : State n) : Prop := σ.J ≼ σ.L

lemma genesis_J_le_L : J_le_L_Inv (State.genesis n) := by
  unfold J_le_L_Inv State.genesis; exact .refl _

lemma processVoteCore_J_le_L_pres (σ : State n) (v : Vote n)
    (h : J_le_L_Inv σ) : J_le_L_Inv (processVoteCore σ v) := by
  unfold J_le_L_Inv at h ⊢
  rw [processVoteCore_J, processVoteCore_L]
  exact h

lemma processVote_J_le_L_pres (σ : State n) (v : Vote n)
    (h : J_le_L_Inv σ) : J_le_L_Inv (processVote σ v) := by
  unfold J_le_L_Inv at h ⊢
  rw [processVote_J, processVote_L]
  exact h

/-- `processHeight` preserves `J ≼ L`. The justification branch is the
    interesting case: the new `J = T` is the chosen quorum target, and we
    need `T ≼ σ.L`. We use Invariant 1 (`TargetsAncInv σ`) to extract a
    witness `i` with `σ.targets i = some T`, hence `T ≼ σ.L`. -/
lemma processHeight_J_le_L_pres (σ : State n) (h_J : J_le_L_Inv σ)
    (h_targets : TargetsAncInv σ) :
    J_le_L_Inv (processHeight σ) := by
  unfold J_le_L_Inv at h_J ⊢
  rw [processHeight_L]
  unfold processHeight processHeightEvents
  cases hFirst : firstJustifiedTarget (applyFinality σ) with
  | some T =>
    simp [hFirst]
    -- Result.J = T. Need: T ≼ σ.L.
    have hJ_T : Justified (applyFinality σ) T := firstJustifiedTarget_sound hFirst
    obtain ⟨i, hi⟩ := justified_extract_witness hJ_T
    rw [applyFinality_targets] at hi
    exact h_targets _ _ hi
  | none =>
    cases hTO : timeoutFiresBool (applyFinality σ) <;> simp [hFirst, hTO, h_J]

lemma processSlot_J_le_L_pres (σ : State n) (h_J : J_le_L_Inv σ)
    (h_t : TargetsAncInv σ) : J_le_L_Inv (processSlot σ) := by
  by_cases hEmpty : σ.L.slot < σ.s
  · simpa [processSlot, hEmpty, J_le_L_Inv] using processHeight_J_le_L_pres σ h_J h_t
  · simpa [processSlot, hEmpty] using h_J

lemma iterateProcessSlot_J_le_L_pres (σ : State n) (k : ℕ)
    (h_J : J_le_L_Inv σ) (h_t : TargetsAncInv σ) :
    J_le_L_Inv (iterateProcessSlot σ k) := by
  induction k generalizing σ with
  | zero => simpa [iterateProcessSlot]
  | succ k ih =>
    change J_le_L_Inv (iterateProcessSlot (processSlot σ) k)
    apply ih
    · exact processSlot_J_le_L_pres σ h_J h_t
    · exact processSlot_targets_anc_pres σ h_t

lemma processBlock_J_le_L_pres (σ : State n) (B : Block n)
    (h : J_le_L_Inv σ) (h_chain : σ.L ≼ B) :
    J_le_L_Inv (processBlock σ B) := by
  unfold J_le_L_Inv at h ⊢
  rw [processBlock_J, processBlock_L]
  exact h.trans h_chain

lemma stateTransition_J_le_L_pres (σ : State n) (B : Block n)
    (h_J : J_le_L_Inv σ) (h_t : TargetsAncInv σ) (h_chain : σ.L ≼ B) :
    J_le_L_Inv (stateTransition σ B) := by
  unfold stateTransition
  apply processHeight_J_le_L_pres
  · apply processBlock_J_le_L_pres
    · exact iterateProcessSlot_J_le_L_pres _ _ h_J h_t
    · rw [iterateProcessSlot_L]; exact h_chain
  · apply processBlock_targets_anc_pres
    · exact iterateProcessSlot_targets_anc_pres _ _ h_t
    · rw [iterateProcessSlot_L]; exact h_chain

/-- **Invariant 3**: at every chain tip-state, `J ≼ B`. (Requires `n ≥ 2`
    so that quorums are non-empty.) -/
lemma chain_J_le_L {B : Block n} (chain : Chain n B) :
    (stateOf chain).J ≼ B := by
  suffices J_le_L_Inv (stateOf chain) by
    have := this
    unfold J_le_L_Inv at this
    rw [chain_state_L_eq_tip] at this
    exact this
  induction chain with
  | genesis => exact genesis_J_le_L
  | @extend parent c bid newSlot votes _ ih =>
    change J_le_L_Inv (stateTransition (stateOf c) (Block.mk bid parent newSlot votes))
    apply stateTransition_J_le_L_pres _ _ ih (chain_targets_anc c) _
    rw [chain_state_L_eq_tip]
    exact .step (.refl _)

/-! ### Auxiliary invariant: `J.slot ≤ sh`

When justification fires, the new `J = T` is set together with `sh = L.slot`.
Since `T ≼ L` (freshness), `T.slot ≤ L.slot = new sh`. So `J.slot ≤ sh`
holds at every state. This is needed for J monotonicity. -/

/-- The "J's slot is at most sh" invariant. -/
def J_slot_le_sh_Inv (σ : State n) : Prop := σ.J.slot ≤ σ.sh

/-- A chain's tip is well-formed by construction. -/
lemma chain_tip_wellformed {B : Block n} (chain : Chain n B) : Block.WellFormed B := by
  induction chain with
  | genesis => trivial
  | @extend parent c bid newSlot votes hSlot ih => exact ⟨hSlot, ih⟩

lemma genesis_J_slot_le_sh : J_slot_le_sh_Inv (State.genesis n) := by
  unfold J_slot_le_sh_Inv State.genesis Block.slot
  -- J = genesis, sh = 0, J.slot = 0
  simp

lemma processVoteCore_J_slot_le_sh_pres (σ : State n) (v : Vote n)
    (h : J_slot_le_sh_Inv σ) : J_slot_le_sh_Inv (processVoteCore σ v) := by
  unfold J_slot_le_sh_Inv at h ⊢
  rw [processVoteCore_J, processVoteCore_sh]; exact h

lemma processVote_J_slot_le_sh_pres (σ : State n) (v : Vote n)
    (h : J_slot_le_sh_Inv σ) : J_slot_le_sh_Inv (processVote σ v) := by
  unfold J_slot_le_sh_Inv at h ⊢
  rw [processVote_J, processVote_sh]; exact h

/-- `processHeight` preserves `J.slot ≤ sh`. The justification branch is the
    interesting case: new J = T (chosen), new sh = σ.L.slot. We need
    `T.slot ≤ σ.L.slot`. By Invariant 1, T ≼ σ.L. Since σ.L is well-formed
    (chain tip), T.slot ≤ σ.L.slot via `Ancestor.slot_le`. -/
lemma processHeight_J_slot_le_sh_pres (σ : State n) (h : J_slot_le_sh_Inv σ)
    (h_J_L : J_le_L_Inv σ) (h_targets : TargetsAncInv σ)
    (hWF : Block.WellFormed σ.L) (h_L_slot_s : σ.L.slot ≤ σ.s) :
    J_slot_le_sh_Inv (processHeight σ) := by
  unfold J_slot_le_sh_Inv at h ⊢
  unfold processHeight processHeightEvents
  cases hFirst : firstJustifiedTarget (applyFinality σ) with
  | some T =>
    simp [hFirst]
    have hJ_T : Justified (applyFinality σ) T := firstJustifiedTarget_sound hFirst
    obtain ⟨i, hi⟩ := justified_extract_witness hJ_T
    rw [applyFinality_targets] at hi
    have hT_anc : T ≼ σ.L := h_targets _ _ hi
    have hT_slot : T.slot ≤ σ.L.slot := hT_anc.slot_le hWF
    exact hT_slot.trans h_L_slot_s
  | none =>
    cases hTO : timeoutFiresBool (applyFinality σ) with
    | true =>
      -- timeout: J unchanged, sh ← σ.s. Need σ.J.slot ≤ σ.s.
      -- From J ≼ L and WF L, slot_le gives σ.J.slot ≤ σ.L.slot ≤ σ.s.
      simp [hFirst, hTO]
      exact ((h_J_L : σ.J ≼ σ.L).slot_le hWF).trans h_L_slot_s
    | false =>
      simp [hFirst, hTO, applyFinality_sh]
      exact h

lemma processSlot_J_slot_le_sh_pres (σ : State n) (h : J_slot_le_sh_Inv σ)
    (h_J_L : J_le_L_Inv σ) (h_targets : TargetsAncInv σ)
    (hWF : Block.WellFormed σ.L) (h_L_slot_s : σ.L.slot ≤ σ.s) :
    J_slot_le_sh_Inv (processSlot σ) := by
  by_cases hEmpty : σ.L.slot < σ.s
  · simpa [processSlot, hEmpty] using
      processHeight_J_slot_le_sh_pres σ h h_J_L h_targets hWF h_L_slot_s
  · simpa [processSlot, hEmpty] using h

lemma iterateProcessSlot_J_slot_le_sh_pres (σ : State n) (k : ℕ)
    (h : J_slot_le_sh_Inv σ) (h_J_L : J_le_L_Inv σ) (h_targets : TargetsAncInv σ)
    (hWF : Block.WellFormed σ.L) (h_L_slot_s : σ.L.slot ≤ σ.s) :
    J_slot_le_sh_Inv (iterateProcessSlot σ k) := by
  induction k generalizing σ with
  | zero => simpa [iterateProcessSlot]
  | succ k ih =>
    change J_slot_le_sh_Inv (iterateProcessSlot (processSlot σ) k)
    apply ih
    · exact processSlot_J_slot_le_sh_pres σ h h_J_L h_targets hWF h_L_slot_s
    · exact processSlot_J_le_L_pres σ h_J_L h_targets
    · exact processSlot_targets_anc_pres σ h_targets
    · rw [processSlot_L]; exact hWF
    · rw [processSlot_L, processSlot_s_eq]
      exact h_L_slot_s.trans (Nat.le_succ _)

lemma processBlock_J_slot_le_sh_pres (σ : State n) (B : Block n)
    (h : J_slot_le_sh_Inv σ) : J_slot_le_sh_Inv (processBlock σ B) := by
  unfold J_slot_le_sh_Inv at h ⊢
  rw [processBlock_J, processBlock_sh]; exact h

lemma stateTransition_J_slot_le_sh_pres (σ : State n) (B : Block n)
    (h : J_slot_le_sh_Inv σ) (h_J_L : J_le_L_Inv σ) (h_targets : TargetsAncInv σ)
    (h_chain : σ.L ≼ B)
    (hWF_L : Block.WellFormed σ.L) (h_L_slot_s : σ.L.slot ≤ σ.s)
    (hWF_B : Block.WellFormed B)
    (h_B_slot_s : B.slot ≤ (iterateProcessSlot σ (B.slot - σ.s)).s) :
    J_slot_le_sh_Inv (stateTransition σ B) := by
  unfold stateTransition
  apply processHeight_J_slot_le_sh_pres
  · apply processBlock_J_slot_le_sh_pres
    exact iterateProcessSlot_J_slot_le_sh_pres _ _ h h_J_L h_targets hWF_L h_L_slot_s
  · apply processBlock_J_le_L_pres
    · exact iterateProcessSlot_J_le_L_pres _ _ h_J_L h_targets
    · rw [iterateProcessSlot_L]
      exact h_chain
  · apply processBlock_targets_anc_pres
    · exact iterateProcessSlot_targets_anc_pres _ _ h_targets
    · rw [iterateProcessSlot_L]
      exact h_chain
  · simpa [processBlock_L] using hWF_B
  · simpa [processBlock_L, processBlock_s] using h_B_slot_s

/-- **Auxiliary Invariant**: at every chain tip-state, `J.slot ≤ sh`. -/
lemma chain_J_slot_le_sh {B : Block n} (chain : Chain n B) :
    (stateOf chain).J.slot ≤ (stateOf chain).sh := by
  suffices J_slot_le_sh_Inv (stateOf chain) from this
  induction chain with
  | genesis => exact genesis_J_slot_le_sh
  | @extend parent c bid newSlot votes hSlot ih =>
    change J_slot_le_sh_Inv (stateTransition (stateOf c) (Block.mk bid parent newSlot votes))
    have hWF_par : Block.WellFormed parent := chain_tip_wellformed c
    have hWF_L : Block.WellFormed (stateOf c).L := by
      rw [chain_state_L_eq_tip]; exact hWF_par
    have h_J_L_c : J_le_L_Inv (stateOf c) := by
      have := chain_J_le_L c
      unfold J_le_L_Inv; rw [chain_state_L_eq_tip]; exact this
    have h_L_slot_s : (stateOf c).L.slot ≤ (stateOf c).s := by
      rw [chain_state_L_eq_tip, chain_state_s_eq_tip_slot]
    have h_chain : (stateOf c).L ≼ Block.mk bid parent newSlot votes := by
      rw [chain_state_L_eq_tip]
      exact .step (.refl _)
    have hWF_B : Block.WellFormed (Block.mk bid parent newSlot votes) :=
      ⟨hSlot, chain_tip_wellformed c⟩
    have h_B_slot_s :
        (Block.mk bid parent newSlot votes).slot ≤
          (iterateProcessSlot (stateOf c)
            ((Block.mk bid parent newSlot votes).slot - (stateOf c).s)).s := by
      rw [iterateProcessSlot_s_eq]
      have hle : (stateOf c).s ≤ (Block.mk bid parent newSlot votes).slot := by
        rw [chain_state_s_eq_tip_slot]
        exact Nat.le_of_lt hSlot
      omega
    exact stateTransition_J_slot_le_sh_pres _ _ ih h_J_L_c
      (chain_targets_anc c) h_chain hWF_L h_L_slot_s hWF_B h_B_slot_s

/-! ### J monotonicity through one `processHeight` call. -/

lemma processHeight_J_monotone (σ : State n)
    (h_targets : TargetsAncInv σ) (h_targets_slot : TargetsSlotInv σ)
    (h_J_L : J_le_L_Inv σ) (h_J_slot : J_slot_le_sh_Inv σ)
    (hWF : Block.WellFormed σ.L) :
    σ.J ≼ (processHeight σ).J := by
  unfold processHeight processHeightEvents
  cases hFirst : firstJustifiedTarget (applyFinality σ) with
  | some T =>
    simp [hFirst]
    have hJ_T : Justified (applyFinality σ) T := firstJustifiedTarget_sound hFirst
    obtain ⟨i, hi⟩ := justified_extract_witness hJ_T
    rw [applyFinality_targets] at hi
    have hT_anc : T ≼ σ.L := h_targets _ _ hi
    have hT_slot : T.slot ≥ σ.sh := h_targets_slot _ _ hi
    have h_slot_chain : σ.J.slot ≤ T.slot := le_trans h_J_slot hT_slot
    exact Block.Ancestor.le_of_slot_le hWF h_J_L hT_anc h_slot_chain
  | none =>
    cases hTO : timeoutFiresBool (applyFinality σ) <;> simp [hFirst, hTO, Block.Ancestor.refl]

lemma processVote_J_monotone (σ : State n) (v : Vote n) :
    σ.J ≼ (processVote σ v).J := by
  rw [processVote_J]; exact .refl _

lemma processSlot_J_monotone (σ : State n)
    (h_targets : TargetsAncInv σ) (h_targets_slot : TargetsSlotInv σ)
    (h_J_L : J_le_L_Inv σ) (h_J_slot : J_slot_le_sh_Inv σ)
    (hWF : Block.WellFormed σ.L) :
    σ.J ≼ (processSlot σ).J := by
  by_cases hEmpty : σ.L.slot < σ.s
  · simpa [processSlot, hEmpty] using
      processHeight_J_monotone σ h_targets h_targets_slot h_J_L h_J_slot hWF
  · simpa [processSlot, hEmpty] using (Block.Ancestor.refl σ.J)

lemma iterateProcessSlot_J_monotone (σ : State n) (k : ℕ)
    (h_targets : TargetsAncInv σ) (h_targets_slot : TargetsSlotInv σ)
    (h_J_L : J_le_L_Inv σ) (h_J_slot : J_slot_le_sh_Inv σ)
    (hWF : Block.WellFormed σ.L) (h_L_slot_s : σ.L.slot ≤ σ.s) :
    σ.J ≼ (iterateProcessSlot σ k).J := by
  induction k generalizing σ with
  | zero => simp [iterateProcessSlot]; exact .refl _
  | succ k ih =>
    change σ.J ≼ (iterateProcessSlot (processSlot σ) k).J
    -- σ.J ≼ (processSlot σ).J ≼ (iterateProcessSlot ...).J
    have h1 : σ.J ≼ (processSlot σ).J :=
      processSlot_J_monotone σ h_targets h_targets_slot h_J_L h_J_slot hWF
    have h2 : (processSlot σ).J ≼ (iterateProcessSlot (processSlot σ) k).J := by
      apply ih
      · exact processSlot_targets_anc_pres σ h_targets
      · exact processSlot_targets_slot_pres σ h_targets_slot
      · exact processSlot_J_le_L_pres σ h_J_L h_targets
      · exact processSlot_J_slot_le_sh_pres σ h_J_slot h_J_L h_targets hWF h_L_slot_s
      · rw [processSlot_L]; exact hWF
      · rw [processSlot_L, processSlot_s_eq]
        exact h_L_slot_s.trans (Nat.le_succ _)
    exact h1.trans h2

lemma processBlock_J_monotone (σ : State n) (B : Block n) :
    σ.J ≼ (processBlock σ B).J := by
  rw [processBlock_J]; exact .refl _

lemma stateTransition_J_monotone (σ : State n) (B : Block n)
    (h_targets : TargetsAncInv σ) (h_targets_slot : TargetsSlotInv σ)
    (h_J_L : J_le_L_Inv σ) (h_J_slot : J_slot_le_sh_Inv σ)
    (h_chain : σ.L ≼ B)
    (hWF : Block.WellFormed σ.L) (h_L_slot_s : σ.L.slot ≤ σ.s)
    (hWF_B : Block.WellFormed B) :
    σ.J ≼ (stateTransition σ B).J := by
  unfold stateTransition
  have h1 := iterateProcessSlot_J_monotone σ (B.slot - σ.s)
    h_targets h_targets_slot h_J_L h_J_slot hWF h_L_slot_s
  have h_pb :
      σ.J ≼ (processBlock (iterateProcessSlot σ (B.slot - σ.s)) B).J := by
    rw [processBlock_J]
    exact h1
  exact h_pb.trans <|
    processHeight_J_monotone _
      (processBlock_targets_anc_pres _ _
        (iterateProcessSlot_targets_anc_pres _ _ h_targets)
        (by rw [iterateProcessSlot_L]; exact h_chain))
      (processBlock_targets_slot_pres _ _
        (iterateProcessSlot_targets_slot_pres _ _ h_targets_slot))
      (processBlock_J_le_L_pres _ _
        (iterateProcessSlot_J_le_L_pres _ _ h_J_L h_targets)
        (by rw [iterateProcessSlot_L]; exact h_chain))
      (processBlock_J_slot_le_sh_pres _ _
        (iterateProcessSlot_J_slot_le_sh_pres _ _ h_J_slot h_J_L h_targets
          hWF h_L_slot_s))
      (by simpa [processBlock_L] using hWF_B)

/-- **J monotonicity along chain extension**: extending a chain by one block can
    only advance `J` along `≼`. -/
lemma chain_J_monotone_step {parent : Block n} (c : Chain n parent)
    (bid : BlockId) (newSlot : ℕ) (votes : List (Vote n))
    (hSlot : newSlot > parent.slot) :
    (stateOf c).J ≼ (stateOf (Chain.extend c bid newSlot votes hSlot)).J := by
  change (stateOf c).J ≼
      (stateTransition (stateOf c) (Block.mk bid parent newSlot votes)).J
  have hWF_L : Block.WellFormed (stateOf c).L := by
    rw [chain_state_L_eq_tip]; exact chain_tip_wellformed c
  have h_J_L_c : J_le_L_Inv (stateOf c) := by
    have := chain_J_le_L c
    unfold J_le_L_Inv; rw [chain_state_L_eq_tip]; exact this
  have h_L_slot_s : (stateOf c).L.slot ≤ (stateOf c).s := by
    rw [chain_state_L_eq_tip, chain_state_s_eq_tip_slot]
  exact stateTransition_J_monotone _ _
    (chain_targets_anc c) (chain_targets_slot c)
    h_J_L_c (chain_J_slot_le_sh c)
    (by rw [chain_state_L_eq_tip]; exact .step (.refl _))
    hWF_L h_L_slot_s ⟨hSlot, chain_tip_wellformed c⟩

/-! ### Invariant 4: `F ≼ J` -/

/-- The "F ≼ J" invariant. -/
def F_le_J_Inv (σ : State n) : Prop := σ.F ≼ σ.J

lemma genesis_F_le_J : F_le_J_Inv (State.genesis n) := by
  unfold F_le_J_Inv State.genesis; exact .refl _

lemma applyFinality_F_le_J (σ : State n) (h : F_le_J_Inv σ) :
    (applyFinality σ).F ≼ (applyFinality σ).J := by
  unfold applyFinality
  split_ifs
  · -- finality fires: F ← σ.J. New F = σ.J = new J.
    change σ.J ≼ σ.J; exact .refl _
  · -- no finality: F unchanged. F ≼ J = h.
    exact h

@[simp] lemma processHeight_F (σ : State n) :
    (processHeight σ).F = (applyFinality σ).F := by
  unfold processHeight processHeightEvents
  cases hFirst : firstJustifiedTarget (applyFinality σ) with
  | some T => simp [hFirst]
  | none =>
      cases hTO : timeoutFiresBool (applyFinality σ) <;> simp [hFirst, hTO]

lemma processVoteCore_F_le_J_pres (σ : State n) (v : Vote n) (h : F_le_J_Inv σ) :
    F_le_J_Inv (processVoteCore σ v) := by
  unfold F_le_J_Inv at h ⊢
  rw [processVoteCore_F, processVoteCore_J]; exact h

lemma processVote_F_le_J_pres (σ : State n) (v : Vote n) (h : F_le_J_Inv σ) :
    F_le_J_Inv (processVote σ v) := by
  unfold F_le_J_Inv at h ⊢
  rw [processVote_F, processVote_J]; exact h

/-- `processHeight` preserves `F ≼ J`. F changes only via finality (F ← J),
    in which case new F ≼ new J via the J-monotonicity step. -/
lemma processHeight_F_le_J_pres (σ : State n) (h : F_le_J_Inv σ)
    (h_targets : TargetsAncInv σ) (h_targets_slot : TargetsSlotInv σ)
    (h_J_L : J_le_L_Inv σ) (h_J_slot : J_slot_le_sh_Inv σ)
    (hWF : Block.WellFormed σ.L) :
    F_le_J_Inv (processHeight σ) := by
  unfold F_le_J_Inv
  rw [processHeight_F]
  have h_aF : (applyFinality σ).F ≼ (applyFinality σ).J := applyFinality_F_le_J σ h
  rw [applyFinality_J] at h_aF
  have h_J_mono := processHeight_J_monotone σ h_targets h_targets_slot h_J_L h_J_slot hWF
  exact h_aF.trans h_J_mono

lemma processSlot_F_le_J_pres (σ : State n) (h : F_le_J_Inv σ)
    (h_targets : TargetsAncInv σ) (h_targets_slot : TargetsSlotInv σ)
    (h_J_L : J_le_L_Inv σ) (h_J_slot : J_slot_le_sh_Inv σ)
    (hWF : Block.WellFormed σ.L) :
    F_le_J_Inv (processSlot σ) := by
  by_cases hEmpty : σ.L.slot < σ.s
  · simpa [processSlot, hEmpty, F_le_J_Inv] using
      processHeight_F_le_J_pres σ h h_targets h_targets_slot h_J_L h_J_slot hWF
  · simpa [processSlot, hEmpty] using h

lemma iterateProcessSlot_F_le_J_pres (σ : State n) (k : ℕ)
    (h : F_le_J_Inv σ) (h_targets : TargetsAncInv σ) (h_targets_slot : TargetsSlotInv σ)
    (h_J_L : J_le_L_Inv σ) (h_J_slot : J_slot_le_sh_Inv σ)
    (hWF : Block.WellFormed σ.L) (h_L_slot_s : σ.L.slot ≤ σ.s) :
    F_le_J_Inv (iterateProcessSlot σ k) := by
  induction k generalizing σ with
  | zero => simpa [iterateProcessSlot]
  | succ k ih =>
    change F_le_J_Inv (iterateProcessSlot (processSlot σ) k)
    apply ih
    · exact processSlot_F_le_J_pres σ h h_targets h_targets_slot h_J_L h_J_slot hWF
    · exact processSlot_targets_anc_pres σ h_targets
    · exact processSlot_targets_slot_pres σ h_targets_slot
    · exact processSlot_J_le_L_pres σ h_J_L h_targets
    · exact processSlot_J_slot_le_sh_pres σ h_J_slot h_J_L h_targets hWF h_L_slot_s
    · rw [processSlot_L]; exact hWF
    · rw [processSlot_L, processSlot_s_eq]
      exact h_L_slot_s.trans (Nat.le_succ _)

lemma processBlock_F_le_J_pres (σ : State n) (B : Block n)
    (h : F_le_J_Inv σ) : F_le_J_Inv (processBlock σ B) := by
  unfold F_le_J_Inv at h ⊢
  rw [processBlock_F, processBlock_J]; exact h

lemma stateTransition_F_le_J_pres (σ : State n) (B : Block n)
    (h : F_le_J_Inv σ) (h_targets : TargetsAncInv σ) (h_targets_slot : TargetsSlotInv σ)
    (h_J_L : J_le_L_Inv σ) (h_J_slot : J_slot_le_sh_Inv σ)
    (h_chain : σ.L ≼ B)
    (hWF : Block.WellFormed σ.L) (h_L_slot_s : σ.L.slot ≤ σ.s)
    (hWF_B : Block.WellFormed B) :
    F_le_J_Inv (stateTransition σ B) := by
  unfold stateTransition
  apply processHeight_F_le_J_pres
  · apply processBlock_F_le_J_pres
    exact iterateProcessSlot_F_le_J_pres _ _ h h_targets h_targets_slot
      h_J_L h_J_slot hWF h_L_slot_s
  · apply processBlock_targets_anc_pres
    · exact iterateProcessSlot_targets_anc_pres _ _ h_targets
    · rw [iterateProcessSlot_L]; exact h_chain
  · apply processBlock_targets_slot_pres
    exact iterateProcessSlot_targets_slot_pres _ _ h_targets_slot
  · apply processBlock_J_le_L_pres
    · exact iterateProcessSlot_J_le_L_pres _ _ h_J_L h_targets
    · rw [iterateProcessSlot_L]; exact h_chain
  · apply processBlock_J_slot_le_sh_pres
    exact iterateProcessSlot_J_slot_le_sh_pres _ _ h_J_slot h_J_L h_targets
      hWF h_L_slot_s
  · simpa [processBlock_L] using hWF_B

/-- **Invariant 4**: at every chain tip-state, `F ≼ J`. -/
lemma chain_F_le_J {B : Block n} (chain : Chain n B) :
    (stateOf chain).F ≼ (stateOf chain).J := by
  suffices F_le_J_Inv (stateOf chain) from this
  induction chain with
  | genesis => exact genesis_F_le_J
  | @extend parent c bid newSlot votes hSlot ih =>
    change F_le_J_Inv (stateTransition (stateOf c) (Block.mk bid parent newSlot votes))
    have hWF_L : Block.WellFormed (stateOf c).L := by
      rw [chain_state_L_eq_tip]; exact chain_tip_wellformed c
    have h_J_L_c : J_le_L_Inv (stateOf c) := by
      have := chain_J_le_L c
      unfold J_le_L_Inv; rw [chain_state_L_eq_tip]; exact this
    have h_L_slot_s : (stateOf c).L.slot ≤ (stateOf c).s := by
      rw [chain_state_L_eq_tip, chain_state_s_eq_tip_slot]
    exact stateTransition_F_le_J_pres _ _ ih
      (chain_targets_anc c) (chain_targets_slot c)
      h_J_L_c (chain_J_slot_le_sh c)
      (by rw [chain_state_L_eq_tip]; exact .step (.refl _))
      hWF_L h_L_slot_s ⟨hSlot, chain_tip_wellformed c⟩

/-! ### Vote-witness invariant

`VoteWitnessInv votes σ` says: every active entry in `σ.targets` and
`σ.timeouts` is justified by a concrete vote in the prefix list `votes`,
with the vote's height matching `σ.h` and (for justification entries)
target lying within `σ.L`.

This is the bridge between the abstract state machine and the concrete
vote history. It is preserved by every transition: `processVote` may add
new entries (the new vote is appended to the prefix); height-advance
branches reset the arrays (invariant becomes vacuous); other transitions
preserve the arrays. -/

/-- The vote-witness invariant on a state, parameterized by the list of
    votes processed so far on this chain. -/
def VoteWitnessInv (votes : List (Vote n)) (σ : State n) : Prop :=
  (∀ i T, σ.targets i = some T →
    ∃ v ∈ votes, v.validator = i ∧ v.target = some T.id ∧ v.height = σ.h ∧
      T ≼ σ.L ∧ T.slot ≥ σ.sh) ∧
  (∀ i, σ.timeouts i = true →
    ∃ v ∈ votes, v.validator = i ∧ v.height = σ.h ∧
      (v.target = none ∨ ∃ T, v.target = some T.id ∧ T ≼ σ.L ∧ T.slot ≥ σ.sh))

/-- Genesis state trivially satisfies the invariant (all entries are inactive). -/
lemma genesis_voteWitness : VoteWitnessInv ([] : List (Vote n)) (State.genesis n) := by
  refine ⟨?_, ?_⟩
  · intro i T heq; simp [State.genesis] at heq
  · intro i heq; simp [State.genesis] at heq

/-- Extending the prefix list preserves the invariant. (Witnesses survive
    list extension since `v ∈ votes ⊆ votes ++ extra`.) -/
lemma VoteWitnessInv.mono (votes extra : List (Vote n)) (σ : State n)
    (h : VoteWitnessInv votes σ) : VoteWitnessInv (votes ++ extra) σ := by
  obtain ⟨h_t, h_to⟩ := h
  refine ⟨?_, ?_⟩
  · intro i T heq
    obtain ⟨v, hv_mem, hrest⟩ := h_t i T heq
    exact ⟨v, by simp [hv_mem], hrest⟩
  · intro i heq
    obtain ⟨v, hv_mem, hrest⟩ := h_to i heq
    exact ⟨v, by simp [hv_mem], hrest⟩

/-- Companion to `processVoteCore_targets_eq_cases` for the `timeouts` array. -/
lemma processVoteCore_timeouts_eq_cases (σ : State n) (v : Vote n) (i : Validator n) :
    (processVoteCore σ v).timeouts i = σ.timeouts i ∨
    (i = v.validator ∧ v.height = σ.h ∧
        (v.target = none ∨ ∃ T, v.target = some T.id ∧ T ≼ σ.L ∧ T.slot ≥ σ.sh) ∧
        (processVoteCore σ v).timeouts i = true) := by
  cases hKnown : voteReferencesKnown σ v
  · left
    simp [processVoteCore, hKnown]
  match h_target : v.target with
  | none =>
    by_cases h_height : v.height = σ.h
    · -- timeouts updated at v.validator.
      by_cases hi : i = v.validator
      · right
        refine ⟨hi, h_height, Or.inl rfl, ?_⟩
        subst hi
        simp [processVoteCore, hKnown, h_target, h_height]
      · left
        simp [processVoteCore, hKnown, h_target, h_height, hi]
    · -- not updated.
      left
      simp [processVoteCore, hKnown, h_target, h_height]
  | some bid =>
    match h_find : σ.L.findById bid with
    | none =>
      left
      simp [processVoteCore, hKnown, h_target, h_find]
    | some T_v =>
      by_cases h_fresh : v.height = σ.h ∧ T_v.slot ≥ σ.sh ∧ T_v.slot < σ.L.slot
      · -- updated at v.validator.
        by_cases hi : i = v.validator
        · right
          refine ⟨hi, h_fresh.1,
                  Or.inr ⟨T_v, ?_, Block.findById_ancestor h_find, h_fresh.2.1⟩, ?_⟩
          · rw [← Block.findById_id h_find]
          · subst hi
            simp [processVoteCore, hKnown, h_target, h_find, h_fresh]
        · left
          simp [processVoteCore, hKnown, h_target, h_find, h_fresh, hi]
      · -- not updated.
        left
        simp [processVoteCore, hKnown, h_target, h_find, h_fresh]

/-- `processVoteCore` preserves the invariant when extending `votes` with `v`.
    Either targets/timeouts at `i` is unchanged (use IH) or `v` itself is the
    fresh witness (and `v.height = σ.h`, `v.target ≼ σ.L`, ...). -/
lemma processVoteCore_voteWitness_pres (votes : List (Vote n)) (σ : State n) (v : Vote n)
    (h : VoteWitnessInv votes σ) :
    VoteWitnessInv (votes ++ [v]) (processVoteCore σ v) := by
  obtain ⟨h_t, h_to⟩ := h
  refine ⟨?_, ?_⟩
  · -- Targets clause.
    intro i T heq
    rw [processVoteCore_h, processVoteCore_L, processVoteCore_sh]
    rcases processVoteCore_targets_eq_cases σ v i with
        h_unchanged | ⟨hi_eq, T_v, hv_target, hv_height, hT_v_anc, hT_v_slot, h_after⟩
    · -- Targets at i unchanged — reuse IH.
      rw [h_unchanged] at heq
      obtain ⟨v', hv'_mem, hrest⟩ := h_t i T heq
      exact ⟨v', by simp [hv'_mem], hrest⟩
    · -- v itself is the fresh witness.
      rw [h_after] at heq
      injection heq with hTT
      subst hTT
      refine ⟨v, by simp, ?_, hv_target, hv_height, hT_v_anc, hT_v_slot⟩
      exact hi_eq.symm
  · -- Timeouts clause.
    intro i heq
    rw [processVoteCore_h, processVoteCore_L, processVoteCore_sh]
    rcases processVoteCore_timeouts_eq_cases σ v i with
        h_unchanged | ⟨hi_eq, hv_height, hv_target_opt, _h_after⟩
    · -- Timeouts at i unchanged — reuse IH.
      rw [h_unchanged] at heq
      obtain ⟨v', hv'_mem, hrest⟩ := h_to i heq
      exact ⟨v', by simp [hv'_mem], hrest⟩
    · -- v itself is the fresh witness.
      refine ⟨v, by simp, hi_eq.symm, hv_height, hv_target_opt⟩

/-- `processVote` preserves the invariant when extending `votes` with `v`. -/
lemma processVote_voteWitness_pres (votes : List (Vote n)) (σ : State n) (v : Vote n)
    (h : VoteWitnessInv votes σ) :
    VoteWitnessInv (votes ++ [v]) (processVote σ v) := by
  -- processVote = processVoteCore + maybe P-update; the P-update doesn't touch
  -- targets/timeouts/h/L/sh.
  obtain ⟨h_t, h_to⟩ := processVoteCore_voteWitness_pres votes σ v h
  refine ⟨?_, ?_⟩
  · intro i T heq
    rw [processVote_targets] at heq
    rw [processVote_h, processVote_L, processVote_sh]
    -- The post-state's targets/h/L/sh equal those of processVoteCore σ v.
    -- Use the corresponding processVoteCore-level conclusion.
    have hC := h_t i T heq
    obtain ⟨v', hv'_mem, hrest⟩ := hC
    refine ⟨v', hv'_mem, ?_⟩
    -- We need to convert the σ-level post-fields. processVote_h/_L/_sh equal σ.h/L/sh.
    -- processVoteCore_h/_L/_sh also equal σ.h/L/sh. So they match.
    convert hrest using 2
    all_goals simp
  · intro i heq
    rw [processVote_timeouts] at heq
    rw [processVote_h, processVote_L, processVote_sh]
    have hC := h_to i heq
    obtain ⟨v', hv'_mem, hrest⟩ := hC
    refine ⟨v', hv'_mem, ?_⟩
    convert hrest using 2
    all_goals simp

/-- `applyFinality` only changes `F`; targets/timeouts/h/L/sh are preserved. -/
lemma applyFinality_voteWitness_pres (votes : List (Vote n)) (σ : State n)
    (h : VoteWitnessInv votes σ) :
    VoteWitnessInv votes (applyFinality σ) := by
  obtain ⟨h_t, h_to⟩ := h
  refine ⟨?_, ?_⟩
  · intro i T heq
    rw [applyFinality_targets] at heq
    rw [applyFinality_L, applyFinality_h, applyFinality_sh]
    exact h_t i T heq
  · intro i heq
    rw [applyFinality_timeouts] at heq
    rw [applyFinality_L, applyFinality_h, applyFinality_sh]
    exact h_to i heq

/-- `processHeight` preserves the invariant. The justification/timeout branches
    reset `targets` and `timeouts` (so the invariant is vacuously satisfied),
    and the no-advance branch keeps everything else (just `applyFinality` change). -/
lemma processHeight_voteWitness_pres (votes : List (Vote n)) (σ : State n)
    (h : VoteWitnessInv votes σ) :
    VoteWitnessInv votes (processHeight σ) := by
  unfold processHeight processHeightEvents
  cases hFirst : firstJustifiedTarget (applyFinality σ) with
  | some T =>
    -- Justification branch: targets and timeouts are reset.
    simp [hFirst]
    refine ⟨?_, ?_⟩
    · intro i T heq; simp at heq
    · intro i heq; simp at heq
  | none =>
    cases hTO : timeoutFiresBool (applyFinality σ) with
    | true =>
      -- Timeout branch: targets and timeouts are reset.
      simp [hFirst, hTO]
      refine ⟨?_, ?_⟩
      · intro i T heq; simp at heq
      · intro i heq; simp at heq
    | false =>
      -- No advance: state is just (applyFinality σ).
      simp [hFirst, hTO]
      exact applyFinality_voteWitness_pres votes σ h

/-- `processSlot` preserves the invariant. -/
lemma processSlot_voteWitness_pres (votes : List (Vote n)) (σ : State n)
    (h : VoteWitnessInv votes σ) :
    VoteWitnessInv votes (processSlot σ) := by
  by_cases hEmpty : σ.L.slot < σ.s
  · obtain ⟨h_t, h_to⟩ := processHeight_voteWitness_pres votes σ h
    refine ⟨?_, ?_⟩
    · intro i T heq
      have heq' : (processHeight σ).targets i = some T := by
        simpa [processSlot, hEmpty] using heq
      have hW := h_t i T heq'
      simpa [processSlot, hEmpty] using hW
    · intro i heq
      have heq' : (processHeight σ).timeouts i = true := by
        simpa [processSlot, hEmpty] using heq
      have hW := h_to i heq'
      simpa [processSlot, hEmpty] using hW
  · simpa [processSlot, hEmpty] using h

/-- `iterateProcessSlot` preserves the invariant. -/
lemma iterateProcessSlot_voteWitness_pres (votes : List (Vote n)) (σ : State n) (k : ℕ)
    (h : VoteWitnessInv votes σ) :
    VoteWitnessInv votes (iterateProcessSlot σ k) := by
  induction k generalizing σ with
  | zero => simpa [iterateProcessSlot]
  | succ k ih =>
    change VoteWitnessInv votes (iterateProcessSlot (processSlot σ) k)
    exact ih _ (processSlot_voteWitness_pres votes σ h)

/-- `processBlock σ B` preserves the invariant when extending the prefix with
    `B.votes`. The outer `{σ with L := B}` doesn't impact the
    invariant once we observe that the targets/timeouts arrays may now point
    to ancestors of B (since σ.L ≼ B). -/
lemma processBlock_voteWitness_pres (votes : List (Vote n)) (σ : State n) (B : Block n)
    (h : VoteWitnessInv votes σ) (h_chain : σ.L ≼ B) :
    VoteWitnessInv (votes ++ B.votes) (processBlock σ B) := by
  unfold processBlock
  -- Initial state: {σ with L := B}.
  -- Show inv {σ with L := B} (same as inv σ but with L = B; T ≼ σ.L gets weakened
  -- to T ≼ B by transitivity, since σ.L ≼ B).
  have h_init : VoteWitnessInv votes ({σ with L := B} : State n) := by
    obtain ⟨h_t, h_to⟩ := h
    refine ⟨?_, ?_⟩
    · intro i T heq
      have h1 : σ.targets i = some T := heq
      obtain ⟨v', hv'_mem, hv'_val, hv'_target, hv'_height, hT_anc, hT_slot⟩ := h_t i T h1
      refine ⟨v', hv'_mem, hv'_val, hv'_target, hv'_height, ?_, hT_slot⟩
      -- T ≼ B follows from T ≼ σ.L ≼ B.
      exact hT_anc.trans h_chain
    · intro i heq
      have h1 : σ.timeouts i = true := heq
      obtain ⟨v', hv'_mem, hv'_val, hv'_height, h_or⟩ := h_to i h1
      refine ⟨v', hv'_mem, hv'_val, hv'_height, ?_⟩
      rcases h_or with h_none | ⟨T, hT_eq, hT_anc, hT_slot⟩
      · exact Or.inl h_none
      · exact Or.inr ⟨T, hT_eq, hT_anc.trans h_chain, hT_slot⟩
  -- Now induct on the fold. We use the abstract preservation lemma for processVote,
  -- carrying along the growing prefix.
  -- Key shape: for each prefix `pre` of `votes_blk`, the state after folding
  -- processVote over `pre` from {σ with L := B} satisfies VoteWitnessInv (votes ++ pre).
  -- We prove this by induction on B.votes.
  suffices ∀ (pre : List (Vote n)) (τ : State n), VoteWitnessInv (votes ++ pre) τ →
      VoteWitnessInv (votes ++ pre ++ B.votes) (B.votes.foldl processVote τ) by
    -- Then specialize pre := []:
    have h_spec := this [] _ (by simpa using h_init)
    -- h_spec : VoteWitnessInv (votes ++ [] ++ B.votes) (B.votes.foldl processVote {σ with L := B})
    -- = VoteWitnessInv (votes ++ B.votes) (...)
    simpa using h_spec
  -- Induction on B.votes.
  intro pre τ hτ
  induction B.votes generalizing pre τ with
  | nil => simpa
  | cons v vs ih =>
    simp only [List.foldl_cons]
    have h_step : VoteWitnessInv (votes ++ pre ++ [v]) (processVote τ v) :=
      processVote_voteWitness_pres _ _ _ hτ
    have ih' := ih (pre ++ [v]) (processVote τ v) (by simpa using h_step)
    -- ih' : VoteWitnessInv (votes ++ (pre ++ [v]) ++ vs) (vs.foldl processVote (processVote τ v))
    -- Goal: VoteWitnessInv (votes ++ pre ++ (v :: vs)) (vs.foldl processVote (processVote τ v))
    simpa [List.append_assoc] using ih'

/-- `stateTransition` preserves the invariant. -/
lemma stateTransition_voteWitness_pres (votes : List (Vote n)) (σ : State n) (B : Block n)
    (h : VoteWitnessInv votes σ) (h_chain : σ.L ≼ B) :
    VoteWitnessInv (votes ++ B.votes) (stateTransition σ B) := by
  unfold stateTransition
  apply processHeight_voteWitness_pres
  apply processBlock_voteWitness_pres
  · exact iterateProcessSlot_voteWitness_pres _ _ _ h
  · -- (iterateProcessSlot σ k).L = σ.L ≼ B
    rw [iterateProcessSlot_L]; exact h_chain

/-- **Chain-level invariant**: at every chain tip-state, `VoteWitnessInv` holds
    with `votesIncluded chain` as the prefix. -/
lemma chain_voteWitness {B : Block n} (chain : Chain n B) :
    VoteWitnessInv (votesIncluded chain) (stateOf chain) := by
  induction chain with
  | genesis =>
    show VoteWitnessInv (votesIncluded (Chain.genesis : Chain n _))
        (stateOf Chain.genesis)
    simp [votesIncluded]
    exact genesis_voteWitness
  | @extend parent c bid newSlot votes hSlot ih =>
    -- The new tip carries its own vote payload.
    set B' := Block.mk bid parent newSlot votes with hB'
    change VoteWitnessInv (votesIncluded c ++ B'.votes)
        (stateTransition (stateOf c) B')
    apply stateTransition_voteWitness_pres
    · exact ih
    · -- (stateOf c).L ≼ B'
      rw [chain_state_L_eq_tip]
      exact .step (.refl _)

/-! ### P-witness invariant

For each `i ∈ σ.P` during processing, there is a vote in the chain's
history with `v.validator = i` and `v.finalize = some (σ.hj, σ.J.id)`.
This is the operational analogue of the
"finalize-commit quorum" used to maintain the finalized-checkpoint certificate. -/

/-- The P-witness invariant on a state, parameterized by the list of
    votes processed so far on this chain. -/
def PWitnessInv (votes : List (Vote n)) (σ : State n) : Prop :=
  ∀ i ∈ σ.P,
    ∃ v ∈ votes, v.validator = i ∧
      v.finalize = some (σ.hj, σ.J.id)

/-- Genesis: P is empty, invariant vacuous. -/
lemma genesis_PWitness : PWitnessInv ([] : List (Vote n)) (State.genesis n) := by
  intro i hi
  simp [State.genesis] at hi

/-- `processVoteCore` doesn't touch P, J, hj. Direct passthrough. -/
lemma processVoteCore_PWitness_pres (votes : List (Vote n)) (σ : State n) (v : Vote n)
    (h : PWitnessInv votes σ) :
    PWitnessInv (votes ++ [v]) (processVoteCore σ v) := by
  intro i hi
  rw [processVoteCore_P] at hi
  rw [processVoteCore_hj, processVoteCore_J]
  obtain ⟨v', hv'_mem, hrest⟩ := h i hi
  exact ⟨v', by simp [hv'_mem], hrest⟩

/-- `processVote` may add `v.validator` to P (when the P-gate fires).
    In that case, `v` itself is the witness with the right finalize commitment. -/
lemma processVote_PWitness_pres (votes : List (Vote n)) (σ : State n) (v : Vote n)
    (h : PWitnessInv votes σ) :
    PWitnessInv (votes ++ [v]) (processVote σ v) := by
  intro i hi
  rw [processVote_eq_ite] at hi
  rw [processVote_hj, processVote_J]
  -- Two cases: P-gate fires or not.
  by_cases h_gate : finalizeGate (processVoteCore σ v) v
  · -- P-gate fires; (processVote σ v).P = insert v.validator (processVoteCore σ v).P.
    rw [if_pos h_gate] at hi
    have h_finalize :
        v.finalize = some ((processVoteCore σ v).hj, (processVoteCore σ v).J.id) := by
      have hparts :
          voteReferencesKnown (processVoteCore σ v) v = true ∧
            decide (v.finalize =
              some ((processVoteCore σ v).hj, (processVoteCore σ v).J.id)) = true := by
        simpa [finalizeGate, Bool.and_eq_true] using h_gate
      exact of_decide_eq_true hparts.2
    -- hi : i ∈ insert v.validator (processVoteCore σ v).P
    rw [Finset.mem_insert] at hi
    rcases hi with hi_v | hi_old
    · -- i = v.validator: v itself is the witness.
      refine ⟨v, by simp, hi_v.symm, ?_⟩
      simpa using h_finalize
    · -- i in old P; use IH.
      have hi_old_orig : i ∈ σ.P := by
        have := hi_old
        rwa [processVoteCore_P] at this
      obtain ⟨v', hv'_mem, hrest⟩ := h i hi_old_orig
      exact ⟨v', by simp [hv'_mem], hrest⟩
  · -- P-gate doesn't fire; P unchanged.
    rw [if_neg h_gate] at hi
    have hi_orig : i ∈ σ.P := by
      have := hi
      rwa [processVoteCore_P] at this
    obtain ⟨v', hv'_mem, hrest⟩ := h i hi_orig
    exact ⟨v', by simp [hv'_mem], hrest⟩

/-- `applyFinality` only changes F; J, hj, P are preserved. -/
lemma applyFinality_PWitness_pres (votes : List (Vote n)) (σ : State n)
    (h : PWitnessInv votes σ) :
    PWitnessInv votes (applyFinality σ) := by
  intro i hi
  rw [applyFinality_P] at hi
  rw [applyFinality_J, applyFinality_hj]
  exact h i hi

/-- `processHeight` preserves the invariant. The justification/timeout branches
    reset P (so the invariant is vacuous). The no-advance branch keeps P
    via applyFinality. -/
lemma processHeight_PWitness_pres (votes : List (Vote n)) (σ : State n)
    (h : PWitnessInv votes σ) :
    PWitnessInv votes (processHeight σ) := by
  unfold processHeight processHeightEvents
  cases hFirst : firstJustifiedTarget (applyFinality σ) with
  | some T =>
    -- Justification branch: P := ∅. Vacuous.
    simp [hFirst]
    intro i hi
    simp at hi
  | none =>
    cases hTO : timeoutFiresBool (applyFinality σ) with
    | true =>
      -- Timeout branch: P unchanged. (Reading the def: timeout doesn't reset P
      -- because P is reset on the JUSTIFICATION branch only.)
      simp [hFirst, hTO]
      -- The timeout branch only changes h, sh, targets, timeouts. P unchanged from
      -- (applyFinality σ).P which equals σ.P (applyFinality only changes F).
      intro i hi
      -- hi : i ∈ {(applyFinality σ) with h := ..., ... }.P = (applyFinality σ).P = σ.P
      have hi' : i ∈ σ.P := by
        simpa using hi
      obtain ⟨v, hv_mem, hv_val, hv_fin⟩ := h i hi'
      refine ⟨v, hv_mem, hv_val, ?_⟩
      simpa using hv_fin
    | false =>
      -- No advance: state = applyFinality σ.
      simp [hFirst, hTO]
      exact applyFinality_PWitness_pres votes σ h

/-- `processSlot` preserves the invariant. -/
lemma processSlot_PWitness_pres (votes : List (Vote n)) (σ : State n)
    (h : PWitnessInv votes σ) :
    PWitnessInv votes (processSlot σ) := by
  by_cases hEmpty : σ.L.slot < σ.s
  · simpa [processSlot, hEmpty] using processHeight_PWitness_pres votes σ h
  · simpa [processSlot, hEmpty] using h

/-- `iterateProcessSlot` preserves the invariant. -/
lemma iterateProcessSlot_PWitness_pres (votes : List (Vote n)) (σ : State n) (k : ℕ)
    (h : PWitnessInv votes σ) :
    PWitnessInv votes (iterateProcessSlot σ k) := by
  induction k generalizing σ with
  | zero => simpa [iterateProcessSlot]
  | succ k ih =>
    change PWitnessInv votes (iterateProcessSlot (processSlot σ) k)
    exact ih _ (processSlot_PWitness_pres votes σ h)

/-- `processBlock σ B` preserves the invariant when extending the prefix
    with `B.votes`. -/
lemma processBlock_PWitness_pres (votes : List (Vote n)) (σ : State n) (B : Block n)
    (h : PWitnessInv votes σ) :
    PWitnessInv (votes ++ B.votes) (processBlock σ B) := by
  unfold processBlock
  -- Initial state: {σ with L := B}.
  have h_init : PWitnessInv votes ({σ with L := B} : State n) := by
    intro i hi
    have h1 : i ∈ σ.P := hi
    obtain ⟨v', hv'_mem, hrest⟩ := h i h1
    exact ⟨v', hv'_mem, hrest⟩
  suffices ∀ (pre : List (Vote n)) (τ : State n), PWitnessInv (votes ++ pre) τ →
      PWitnessInv (votes ++ pre ++ B.votes) (B.votes.foldl processVote τ) by
    have h_spec := this [] _ (by simpa using h_init)
    simpa using h_spec
  intro pre τ hτ
  induction B.votes generalizing pre τ with
  | nil => simpa
  | cons v vs ih =>
    simp only [List.foldl_cons]
    have h_step : PWitnessInv (votes ++ pre ++ [v]) (processVote τ v) :=
      processVote_PWitness_pres _ _ _ hτ
    have ih' := ih (pre ++ [v]) (processVote τ v) (by simpa using h_step)
    simpa [List.append_assoc] using ih'

/-- `stateTransition` preserves the invariant. -/
lemma stateTransition_PWitness_pres (votes : List (Vote n)) (σ : State n) (B : Block n)
    (h : PWitnessInv votes σ) :
    PWitnessInv (votes ++ B.votes) (stateTransition σ B) := by
  unfold stateTransition
  apply processHeight_PWitness_pres
  apply processBlock_PWitness_pres
  exact iterateProcessSlot_PWitness_pres _ _ _ h

/-- **Chain-level P-witness invariant**: at every chain tip-state, the P-witness
    invariant holds with `votesIncluded chain` as the prefix. -/
lemma chain_PWitness {B : Block n} (chain : Chain n B) :
    PWitnessInv (votesIncluded chain) (stateOf chain) := by
  induction chain with
  | genesis =>
    show PWitnessInv (votesIncluded (Chain.genesis : Chain n _)) (stateOf Chain.genesis)
    simp [votesIncluded]
    exact genesis_PWitness
  | @extend parent c bid newSlot votes hSlot ih =>
    set B' := Block.mk bid parent newSlot votes with hB'
    change PWitnessInv (votesIncluded c ++ B'.votes)
        (stateTransition (stateOf c) B')
    apply stateTransition_PWitness_pres
    exact ih

/-! ### J-witness invariant: justification quorum recoverable from σ.J / σ.hj

When `σ.hj > 0`, a justification with target `σ.J` has fired at height
`σ.hj` on this chain. The vote-witness invariant on the pre-justification
state gives us a quorum of validators each having voted at `σ.hj` with
target `some σ.J.id`. This justification-quorum information persists in the
post-state via the `JWitnessInv` invariant tracked below. -/

/-- The J-witness invariant on a state, parameterized by votes. Either
    `σ.hj = 0` (no justification yet) or there's a quorum of validators
    each having a justification-vote in `votes` for `σ.J` at `σ.hj`. -/
def JWitnessInv (votes : List (Vote n)) (σ : State n) : Prop :=
  σ.hj = 0 ∨ ∃ Q : Finset (Validator n), IsQuorumStrict n Q ∧
    ∀ i ∈ Q, ∃ v ∈ votes, v.validator = i ∧ v.target = some σ.J.id ∧
      v.height = σ.hj

/-- Genesis: hj = 0, invariant via left disjunct. -/
lemma genesis_JWitness : JWitnessInv ([] : List (Vote n)) (State.genesis n) := by
  left; rfl

/-- `processVoteCore` doesn't change J/hj. -/
lemma processVoteCore_JWitness_pres (votes : List (Vote n)) (σ : State n) (v : Vote n)
    (h : JWitnessInv votes σ) :
    JWitnessInv (votes ++ [v]) (processVoteCore σ v) := by
  rcases h with h | ⟨Q, hQ_quorum, hQ_votes⟩
  · left; rw [processVoteCore_hj]; exact h
  · right; refine ⟨Q, hQ_quorum, ?_⟩
    intro i hi
    rw [processVoteCore_J, processVoteCore_hj]
    obtain ⟨v', hv'_mem, hrest⟩ := hQ_votes i hi
    exact ⟨v', by simp [hv'_mem], hrest⟩

/-- `processVote` doesn't change J/hj. -/
lemma processVote_JWitness_pres (votes : List (Vote n)) (σ : State n) (v : Vote n)
    (h : JWitnessInv votes σ) :
    JWitnessInv (votes ++ [v]) (processVote σ v) := by
  rcases h with h | ⟨Q, hQ_quorum, hQ_votes⟩
  · left; rw [processVote_hj]; exact h
  · right; refine ⟨Q, hQ_quorum, ?_⟩
    intro i hi
    rw [processVote_J, processVote_hj]
    obtain ⟨v', hv'_mem, hrest⟩ := hQ_votes i hi
    exact ⟨v', by simp [hv'_mem], hrest⟩

/-- `applyFinality` doesn't change J/hj. -/
lemma applyFinality_JWitness_pres (votes : List (Vote n)) (σ : State n)
    (h : JWitnessInv votes σ) :
    JWitnessInv votes (applyFinality σ) := by
  rcases h with h | ⟨Q, hQ_quorum, hQ_votes⟩
  · left; rw [applyFinality_hj]; exact h
  · right; refine ⟨Q, hQ_quorum, ?_⟩
    intro i hi
    rw [applyFinality_J, applyFinality_hj]
    exact hQ_votes i hi

/-- `processHeight` preserves the invariant: in the justification branch, we
    establish the new invariant (with new J, hj) using `VoteWitnessInv` on the
    pre-state to extract the justification quorum's witness votes. In the
    timeout/no-advance branches, J/hj are unchanged. -/
lemma processHeight_JWitness_pres (votes : List (Vote n)) (σ : State n)
    (h_J : JWitnessInv votes σ) (h_VW : VoteWitnessInv votes σ) :
    JWitnessInv votes (processHeight σ) := by
  unfold processHeight processHeightEvents
  cases hFirst : firstJustifiedTarget (applyFinality σ) with
  | some T =>
    -- Justification branch: new J = selected T, new hj = σ.h.
    simp [hFirst]
    right
    have hJ_T : Justified (applyFinality σ) T := firstJustifiedTarget_sound hFirst
    -- Justified σ T = IsQuorumStrict n (filter targets = some T).
    -- Note: applyFinality doesn't change targets, so this equals the σ-quorum.
    let Q := Finset.univ.filter (fun i : Validator n => σ.targets i = some T)
    have hQ_quorum : IsQuorumStrict n Q := by
      have h_eq : (Finset.univ.filter (fun i : Validator n =>
            (applyFinality σ).targets i = some T)) = Q := by
        simp [Q, applyFinality_targets]
      have : IsQuorumStrict n (Finset.univ.filter
            (fun i : Validator n => (applyFinality σ).targets i = some T)) := hJ_T
      rw [h_eq] at this
      exact this
    refine ⟨Q, hQ_quorum, ?_⟩
    intro i hi
    have hi_targets : σ.targets i = some T := by
      simp [Q, Finset.mem_filter] at hi
      exact hi
    -- Use VoteWitnessInv on σ to get the witness vote.
    obtain ⟨h_inv_t, _⟩ := h_VW
    obtain ⟨v, hv_mem, hv_val, hv_target, hv_height, _hT_anc, _hT_slot⟩ :=
      h_inv_t i T hi_targets
    -- The new state's σ.J = T and σ.hj = σ.h. Need v.target = some T and v.height = σ.h.
    refine ⟨v, hv_mem, hv_val, hv_target, ?_⟩
    -- v.height = σ.h. We have hv_height : v.height = σ.h.
    -- New σ.hj = σ.h (just after the "if" reduction). The post-state's hj is set to σ.h
    -- (which equals (applyFinality σ).h since applyFinality doesn't change h).
    -- We need v.height = (post state).hj = σ.h.
    simpa [applyFinality_h] using hv_height
  | none =>
    cases hTO : timeoutFiresBool (applyFinality σ) with
    | true =>
      -- Timeout branch: J/hj unchanged from applyFinality.
      simp [hFirst, hTO]
      rcases h_J with h | ⟨Q, hQ_quorum, hQ_votes⟩
      · left; simpa using h
      · right; refine ⟨Q, hQ_quorum, ?_⟩
        intro i hi
        obtain ⟨v, hv_mem, hv_val, hv_target, hv_height⟩ := hQ_votes i hi
        refine ⟨v, hv_mem, hv_val, ?_, ?_⟩
        · simpa using hv_target
        · simpa using hv_height
    | false =>
      -- No advance: state = applyFinality σ.
      simp [hFirst, hTO]
      exact applyFinality_JWitness_pres votes σ h_J

/-- JWitness on `{σ with s := σ.s + 1}` follows from JWitness on σ
    (J, hj, targets are unchanged). -/
private lemma JWitnessInv_set_s (votes : List (Vote n)) (σ : State n) (s' : ℕ)
    (h : JWitnessInv votes σ) :
    JWitnessInv votes ({σ with s := s'} : State n) := by
  rcases h with h | ⟨Q, hQ_quorum, hQ_votes⟩
  · left; exact h
  · right; refine ⟨Q, hQ_quorum, ?_⟩
    intro i hi
    exact hQ_votes i hi

/-- VoteWitnessInv on `{σ with s := σ.s + 1}` follows from VoteWitnessInv on σ. -/
private lemma VoteWitnessInv_set_s (votes : List (Vote n)) (σ : State n) (s' : ℕ)
    (h : VoteWitnessInv votes σ) :
    VoteWitnessInv votes ({σ with s := s'} : State n) := by
  obtain ⟨h_t, h_to⟩ := h
  refine ⟨?_, ?_⟩
  · intro i T heq; exact h_t i T heq
  · intro i heq; exact h_to i heq

/-- `processSlot` preserves the J-witness invariant (using VoteWitnessInv as
    aux to handle the justification branch). -/
lemma processSlot_JWitness_pres (votes : List (Vote n)) (σ : State n)
    (h_J : JWitnessInv votes σ) (h_VW : VoteWitnessInv votes σ) :
    JWitnessInv votes (processSlot σ) := by
  by_cases hEmpty : σ.L.slot < σ.s
  · simpa [processSlot, hEmpty] using processHeight_JWitness_pres votes σ h_J h_VW
  · simpa [processSlot, hEmpty] using h_J

/-- `iterateProcessSlot` preserves J-witness (using VoteWitness alongside). -/
lemma iterateProcessSlot_JWitness_pres (votes : List (Vote n)) (σ : State n) (k : ℕ)
    (h_J : JWitnessInv votes σ) (h_VW : VoteWitnessInv votes σ) :
    JWitnessInv votes (iterateProcessSlot σ k) := by
  induction k generalizing σ with
  | zero => simpa [iterateProcessSlot]
  | succ k ih =>
    change JWitnessInv votes (iterateProcessSlot (processSlot σ) k)
    apply ih
    · exact processSlot_JWitness_pres votes σ h_J h_VW
    · exact processSlot_voteWitness_pres votes σ h_VW

/-- `processBlock` preserves J-witness (with VoteWitness alongside). -/
lemma processBlock_JWitness_pres (votes : List (Vote n)) (σ : State n) (B : Block n)
    (h_J : JWitnessInv votes σ) (h_VW : VoteWitnessInv votes σ) (h_chain : σ.L ≼ B) :
    JWitnessInv (votes ++ B.votes) (processBlock σ B) := by
  unfold processBlock
  -- Initial state: {σ with L := B}.
  have h_J_init : JWitnessInv votes ({σ with L := B} : State n) := by
    rcases h_J with h | ⟨Q, hQ_quorum, hQ_votes⟩
    · left; exact h
    · right; refine ⟨Q, hQ_quorum, ?_⟩
      intro i hi
      exact hQ_votes i hi
  have h_VW_init : VoteWitnessInv votes ({σ with L := B} : State n) := by
    obtain ⟨h_t, h_to⟩ := h_VW
    refine ⟨?_, ?_⟩
    · intro i T heq
      have h1 : σ.targets i = some T := heq
      obtain ⟨v', hv'_mem, hv'_val, hv'_target, hv'_height, hT_anc, hT_slot⟩ :=
        h_t i T h1
      refine ⟨v', hv'_mem, hv'_val, hv'_target, hv'_height, ?_, hT_slot⟩
      exact hT_anc.trans h_chain
    · intro i heq
      have h1 : σ.timeouts i = true := heq
      obtain ⟨v', hv'_mem, hv'_val, hv'_height, h_or⟩ := h_to i h1
      refine ⟨v', hv'_mem, hv'_val, hv'_height, ?_⟩
      rcases h_or with h_none | ⟨T, hT_eq, hT_anc, hT_slot⟩
      · exact Or.inl h_none
      · exact Or.inr ⟨T, hT_eq, hT_anc.trans h_chain, hT_slot⟩
  suffices ∀ (pre : List (Vote n)) (τ : State n),
      JWitnessInv (votes ++ pre) τ → VoteWitnessInv (votes ++ pre) τ →
      JWitnessInv (votes ++ pre ++ B.votes) (B.votes.foldl processVote τ) by
    have h_spec := this [] _
      (by simpa using h_J_init) (by simpa using h_VW_init)
    simpa using h_spec
  intro pre τ hτ_J hτ_VW
  induction B.votes generalizing pre τ with
  | nil => simpa
  | cons v vs ih =>
    simp only [List.foldl_cons]
    have h_J_step : JWitnessInv (votes ++ pre ++ [v]) (processVote τ v) :=
      processVote_JWitness_pres _ _ _ hτ_J
    have h_VW_step : VoteWitnessInv (votes ++ pre ++ [v]) (processVote τ v) :=
      processVote_voteWitness_pres _ _ _ hτ_VW
    have ih' := ih (pre ++ [v]) (processVote τ v)
      (by simpa using h_J_step) (by simpa using h_VW_step)
    simpa [List.append_assoc] using ih'

/-- `stateTransition` preserves J-witness. -/
lemma stateTransition_JWitness_pres (votes : List (Vote n)) (σ : State n) (B : Block n)
    (h_J : JWitnessInv votes σ) (h_VW : VoteWitnessInv votes σ) (h_chain : σ.L ≼ B) :
    JWitnessInv (votes ++ B.votes) (stateTransition σ B) := by
  unfold stateTransition
  apply processHeight_JWitness_pres
  · apply processBlock_JWitness_pres
    · exact iterateProcessSlot_JWitness_pres _ _ _ h_J h_VW
    · exact iterateProcessSlot_voteWitness_pres _ _ _ h_VW
    · rw [iterateProcessSlot_L]; exact h_chain
  · apply processBlock_voteWitness_pres
    · exact iterateProcessSlot_voteWitness_pres _ _ _ h_VW
    · rw [iterateProcessSlot_L]; exact h_chain

/-- **Chain-level J-witness invariant**. -/
lemma chain_JWitness {B : Block n} (chain : Chain n B) :
    JWitnessInv (votesIncluded chain) (stateOf chain) := by
  induction chain with
  | genesis =>
    show JWitnessInv (votesIncluded (Chain.genesis : Chain n _)) (stateOf Chain.genesis)
    simp [votesIncluded]
    exact genesis_JWitness
  | @extend parent c bid newSlot votes hSlot ih =>
    set B' := Block.mk bid parent newSlot votes with hB'
    change JWitnessInv (votesIncluded c ++ B'.votes)
        (stateTransition (stateOf c) B')
    apply stateTransition_JWitness_pres
    · exact ih
    · exact chain_voteWitness c
    · rw [chain_state_L_eq_tip]; exact .step (.refl _)

/-! ### `hj = 0 ↔ J = genesis` invariant

When no justification has fired, `hj = 0` and `J = Block.genesis`. After
any justification, `hj ≥ 1` (since it's set to σ.h, which is always ≥ 1).
This invariant is also used when `applyFinality` writes `F ← J` at height 0,
which forces genesis finality. -/

/-- The "hj = 0 implies J = genesis" invariant. -/
def HjZeroJGenesisInv (σ : State n) : Prop := σ.hj = 0 → σ.J = Block.genesis

lemma genesis_HjZeroJGenesis : HjZeroJGenesisInv (State.genesis n) := fun _ => rfl

lemma processVoteCore_HjZeroJGenesis_pres (σ : State n) (v : Vote n)
    (h : HjZeroJGenesisInv σ) : HjZeroJGenesisInv (processVoteCore σ v) := by
  intro hhj
  rw [processVoteCore_J]
  apply h
  rwa [processVoteCore_hj] at hhj

lemma processVote_HjZeroJGenesis_pres (σ : State n) (v : Vote n)
    (h : HjZeroJGenesisInv σ) : HjZeroJGenesisInv (processVote σ v) := by
  intro hhj
  rw [processVote_J]
  apply h
  rwa [processVote_hj] at hhj

lemma applyFinality_HjZeroJGenesis_pres (σ : State n)
    (h : HjZeroJGenesisInv σ) : HjZeroJGenesisInv (applyFinality σ) := by
  intro hhj
  rw [applyFinality_J]
  apply h
  rwa [applyFinality_hj] at hhj

/-- The crucial invariant: `processHeight` preserves `hj = 0 → J = genesis`,
    using the assumption `σ.h ≥ 1` (which holds on every chain after genesis). -/
lemma processHeight_HjZeroJGenesis_pres (σ : State n)
    (h : HjZeroJGenesisInv σ) (h_h_pos : σ.h ≥ 1) :
    HjZeroJGenesisInv (processHeight σ) := by
  intro hhj
  unfold processHeight processHeightEvents at hhj ⊢
  cases hFirst : firstJustifiedTarget (applyFinality σ) with
  | some T =>
    -- Justification branch: new hj = σ.h. Hypothesis hhj : σ.h = 0 contradicts σ.h ≥ 1.
    simp [hFirst] at hhj ⊢
    omega
  | none =>
    cases hTO : timeoutFiresBool (applyFinality σ) with
    | true =>
      -- Timeout branch: hj, J unchanged from applyFinality.
      simp [hFirst, hTO] at hhj ⊢
      exact h hhj
    | false =>
      -- No advance: state = applyFinality σ.
      simp [hFirst, hTO] at hhj ⊢
      exact h hhj

lemma processSlot_HjZeroJGenesis_pres (σ : State n)
    (h : HjZeroJGenesisInv σ) (h_h_pos : σ.h ≥ 1) :
    HjZeroJGenesisInv (processSlot σ) := by
  by_cases hEmpty : σ.L.slot < σ.s
  · simpa [processSlot, hEmpty] using processHeight_HjZeroJGenesis_pres σ h h_h_pos
  · simpa [processSlot, hEmpty] using h

/-- σ.h is non-decreasing under processSlot, so σ.h ≥ 1 is preserved. -/
lemma processSlot_h_pos_pres (σ : State n) (h_h_pos : σ.h ≥ 1) :
    (processSlot σ).h ≥ 1 := by
  have : σ.h ≤ (processSlot σ).h := processSlot_h_le σ
  omega

lemma iterateProcessSlot_HjZeroJGenesis_pres (σ : State n) (k : ℕ)
    (h : HjZeroJGenesisInv σ) (h_h_pos : σ.h ≥ 1) :
    HjZeroJGenesisInv (iterateProcessSlot σ k) := by
  induction k generalizing σ with
  | zero => simpa [iterateProcessSlot]
  | succ k ih =>
    change HjZeroJGenesisInv (iterateProcessSlot (processSlot σ) k)
    apply ih
    · exact processSlot_HjZeroJGenesis_pres σ h h_h_pos
    · exact processSlot_h_pos_pres σ h_h_pos

lemma processBlock_HjZeroJGenesis_pres (σ : State n) (B : Block n)
    (h : HjZeroJGenesisInv σ) :
    HjZeroJGenesisInv (processBlock σ B) := by
  intro hhj
  rw [processBlock_J]
  apply h
  rwa [processBlock_hj] at hhj

lemma stateTransition_HjZeroJGenesis_pres (σ : State n) (B : Block n)
    (h : HjZeroJGenesisInv σ) (h_h_pos : σ.h ≥ 1) :
    HjZeroJGenesisInv (stateTransition σ B) := by
  unfold stateTransition
  apply processHeight_HjZeroJGenesis_pres
  · apply processBlock_HjZeroJGenesis_pres
    exact iterateProcessSlot_HjZeroJGenesis_pres _ _ h h_h_pos
  · have h_iter_pos :
        (iterateProcessSlot σ (B.slot - σ.s)).h ≥ 1 := by
      have h_le := iterateProcessSlot_h_le σ (B.slot - σ.s)
      omega
    simpa [processBlock_h] using h_iter_pos

/-- σ.h ≥ 1 at every chain tip-state. -/
lemma chain_h_pos {B : Block n} (chain : Chain n B) : (stateOf chain).h ≥ 1 := by
  induction chain with
  | genesis => simp [stateOf, State.genesis]
  | @extend parent c bid newSlot votes hSlot ih =>
    change (stateTransition (stateOf c) (Block.mk bid parent newSlot votes)).h ≥ 1
    have h_le : (stateOf c).h ≤ (stateTransition (stateOf c)
        (Block.mk bid parent newSlot votes)).h :=
      stateTransition_h_le _ _
    omega

/-- **Chain-level**: σ.hj = 0 → σ.J = Block.genesis. -/
lemma chain_HjZeroJGenesis {B : Block n} (chain : Chain n B) :
    HjZeroJGenesisInv (stateOf chain) := by
  induction chain with
  | genesis => exact genesis_HjZeroJGenesis
  | @extend parent c bid newSlot votes hSlot ih =>
    change HjZeroJGenesisInv (stateTransition (stateOf c) (Block.mk bid parent newSlot votes))
    apply stateTransition_HjZeroJGenesis_pres _ _ ih
    exact chain_h_pos c

end DecoupledConsensus
