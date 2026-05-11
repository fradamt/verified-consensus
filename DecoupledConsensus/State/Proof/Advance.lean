import DecoupledConsensus.State.Proof.Invariants

namespace DecoupledConsensus

/-! # Accountable Safety Proofs: advance witness

The first-crossing/advance-witness argument extracting the quorum responsible
for advancing past a finalized height. -/

variable {n : ℕ}

open scoped Block

attribute [local instance] Classical.propDecidable

/-! ### The `advance_witness` lemma

The chain-level statement: for any chain whose tip-state has `h > h_f` (with
`h_f ≥ 1`), there is a quorum `Q` and an ancestor `B_star ≼ B` of the tip
such that each `i ∈ Q` has an included vote at height `h_f` whose target is either
`none` (timeout vote) or some `T ≼ B_star` (fresh justification vote).

Proof sketch:
- Chain induction.
- Base case `chain = genesis`: `(stateOf chain).h = 1`, so `h_f < 1`,
  contradicting `h_f ≥ 1`. Vacuous.
- Inductive case `chain = extend c newSlot _ votes_blk`:
  - Subcase (stateOf c).h > h_f: IH on c gives the quorum on c. Lift via
    chain extension and `votesIncluded c ⊆ votesIncluded chain`.
  - Subcase (stateOf c).h ≤ h_f: the crossing either happens during
    `stateTransition`'s `iterateProcessSlot` loop, or in the final
    `processHeight` that closes events enabled by the new block's own votes.
    In both cases `height_progression` identifies the firing branch
    (justification or timeout), and `VoteWitnessInv` provides the concrete
    per-validator witness votes. -/

/-- Extract the responsible quorum from a single height-advance step.

    This packages the common justification/timeout case split used by
    `advance_witness`. The caller supplies the chain-vote witness invariant
    for `σ` and an ancestor bound for `σ.L`; the result is already phrased in
    the public `IsQuorum f` form. -/
private lemma advance_votes_from_height_step {f : ℕ} (hn : n = 3 * f + 1)
    {votes : List (Vote n)} {σ : State n} {B_star : Block n} {h_f : ℕ}
    (h_inv : VoteWitnessInv votes σ)
    (hσ_h : σ.h = h_f)
    (hL_anc : σ.L ≼ B_star)
    (h_step : (processHeight σ).h = σ.h + 1) :
    ∃ Q : Finset (Validator n),
      IsQuorum f Q ∧
      ∀ i ∈ Q, ∃ v ∈ votes, v.validator = i ∧ v.height = h_f ∧
        (v.target = none ∨ ∃ T, v.target = some T.id ∧ T ≼ B_star) := by
  obtain ⟨h_inv_t, h_inv_to⟩ := h_inv
  have h_advance_witness := (height_progression σ).2 h_step
  rcases h_advance_witness with ⟨T, hT_just⟩ | hTO
  · let Q := Finset.univ.filter (fun i : Validator n => σ.targets i = some T)
    have hQ_quorum : IsQuorum f Q :=
      (isQuorum_iff_strict hn Q).mpr hT_just
    refine ⟨Q, hQ_quorum, ?_⟩
    intro i hi
    have hi_targets : σ.targets i = some T := by
      simp [Q, Finset.mem_filter] at hi
      exact hi
    obtain ⟨v, hv_mem, hv_val, hv_target, hv_height, hT_anc, _hT_slot⟩ :=
      h_inv_t i T hi_targets
    refine ⟨v, hv_mem, hv_val, ?_, ?_⟩
    · rw [hv_height, hσ_h]
    · right
      exact ⟨T, hv_target, hT_anc.trans hL_anc⟩
  · let Q := Finset.univ.filter (fun i : Validator n => σ.timeouts i = true)
    have hQ_quorum : IsQuorum f Q :=
      (isQuorum_iff_strict hn Q).mpr hTO
    refine ⟨Q, hQ_quorum, ?_⟩
    intro i hi
    have hi_timeouts : σ.timeouts i = true := by
      simp [Q, Finset.mem_filter] at hi
      exact hi
    obtain ⟨v, hv_mem, hv_val, hv_height, h_or⟩ := h_inv_to i hi_timeouts
    refine ⟨v, hv_mem, hv_val, ?_, ?_⟩
    · rw [hv_height, hσ_h]
    · rcases h_or with h_none | ⟨T, hT_eq, hT_anc, _hT_slot⟩
      · exact Or.inl h_none
      · right
        exact ⟨T, hT_eq, hT_anc.trans hL_anc⟩

/-- **AdvanceWitness lemma** (proved). The conclusion uses the literal `IsQuorum f`
    form under the BFT convention `n = 3 * f + 1`. -/
lemma advance_witness {f : ℕ} (hn : n = 3 * f + 1)
    {B : Block n} (chain : Chain n B) (h_f : ℕ)
    (h_hf_ge : h_f ≥ 1) (h_height : (stateOf chain).h > h_f) :
    ∃ (Q : Finset (Validator n)) (B_star : Block n),
      B_star ≼ B ∧
      IsQuorum f Q ∧
      ∀ i ∈ Q, ∃ v ∈ votesIncluded chain, v.validator = i ∧ v.height = h_f ∧
        (v.target = none ∨ ∃ T, v.target = some T.id ∧ T ≼ B_star) := by
  -- Induction on chain.
  induction chain with
  | genesis =>
    -- (stateOf .genesis).h = 1, so h_f < 1 contradicts h_f ≥ 1.
    exfalso
    have h1 : (stateOf (Chain.genesis : Chain n _)).h = 1 := by
      simp [stateOf, State.genesis]
    rw [h1] at h_height; omega
  | @extend parent c bid newSlot votes hSlot ih =>
    -- Goal: find Q, B_star ≼ Block.mk bid parent newSlot votes satisfying the conjunction.
    -- Distinguish: either (stateOf c).h > h_f (use IH) or (stateOf c).h ≤ h_f
    -- (the crossing happens in this stateTransition).
    set B := Block.mk bid parent newSlot votes with hB
    by_cases h_c_h : (stateOf c).h > h_f
    · -- Subcase (a): IH on c.
      obtain ⟨Q, B_star, hB_star, hQ_quorum, hQ_votes⟩ := ih h_c_h
      refine ⟨Q, B_star, ?_, hQ_quorum, ?_⟩
      · -- B_star ≼ Block.mk parent newSlot via parent ≼ Block.mk parent newSlot.
        exact hB_star.trans (.step (.refl _))
      · -- Each i ∈ Q's vote is the same as in the IH; lift membership
        -- from the parent chain into the extended chain.
        intro i hi
        obtain ⟨v, hv_mem, hrest⟩ := hQ_votes i hi
        exact ⟨v, by simp [votesIncluded, hv_mem], hrest⟩
    · -- Subcase (b): the height crossing happens in stateTransition.
      have h_c_h : (stateOf c).h ≤ h_f := Nat.le_of_not_lt h_c_h
      set k := B.slot - (stateOf c).s with hk
      by_cases h_iter_h : (iterateProcessSlot (stateOf c) k).h > h_f
      · -- The crossing happened during an empty-slot transition before `B`.
        obtain ⟨k₀, _hk₀_lt, hk₀_h, hk₀_succ_h⟩ :=
          iterateProcessSlot_first_crossing (stateOf c) h_f k h_c_h h_iter_h
        -- σ_pre = iterateProcessSlot (stateOf c) k₀. σ_pre.h = h_f.
        set σ_pre := iterateProcessSlot (stateOf c) k₀ with hσ_pre
        -- σ_post = processSlot σ_pre. σ_post.h = h_f + 1.
        have h_post_eq : iterateProcessSlot (stateOf c) (k₀ + 1) = processSlot σ_pre := by
          rw [iterateProcessSlot_succ_apply]
        have hσ_post_h : (processSlot σ_pre).h = h_f + 1 := by
          rw [← h_post_eq]; exact hk₀_succ_h
        have h_step_advance :
            (processHeight σ_pre).h = σ_pre.h + 1 := by
          by_cases hEmpty : σ_pre.L.slot < σ_pre.s
          · have h_eq : (processSlot σ_pre).h = (processHeight σ_pre).h := by
              simp [processSlot, hEmpty]
            rw [h_eq] at hσ_post_h
            rw [hk₀_h]
            exact hσ_post_h
          · have h_eq : (processSlot σ_pre).h = σ_pre.h := by
              simp [processSlot, hEmpty]
            rw [h_eq, hk₀_h] at hσ_post_h
            omega
        -- VoteWitnessInv at σ_pre (preserved through iterateProcessSlot from chain_voteWitness c).
        have h_inv_pre : VoteWitnessInv (votesIncluded c) σ_pre := by
          have h_inv_c := chain_voteWitness c
          exact iterateProcessSlot_voteWitness_pres _ _ _ h_inv_c
        have hσ_pre_L : σ_pre.L = parent := by
          show (iterateProcessSlot (stateOf c) k₀).L = parent
          rw [iterateProcessSlot_L, chain_state_L_eq_tip]
        have hσ_pre_L_anc : σ_pre.L ≼ parent := by
          rw [hσ_pre_L]
          exact .refl _
        obtain ⟨Q, hQ_quorum, hQ_votes⟩ :=
          advance_votes_from_height_step hn h_inv_pre hk₀_h hσ_pre_L_anc h_step_advance
        refine ⟨Q, parent, ?_, hQ_quorum, ?_⟩
        · exact .step (.refl _)
        · intro i hi
          obtain ⟨v, hv_mem, hrest⟩ := hQ_votes i hi
          exact ⟨v, by simp [votesIncluded, hv_mem], hrest⟩
      · -- The iterate state is still at or below `h_f`; `B`'s own votes cause
        -- the final height-closing call in `stateTransition` to cross.
        have h_iter_le : (iterateProcessSlot (stateOf c) k).h ≤ h_f :=
          Nat.le_of_not_lt h_iter_h
        set σ_blk := processBlock (iterateProcessSlot (stateOf c) k) B with hσ_blk
        have h_final_gt : (processHeight σ_blk).h > h_f := by
          have h_state :
              (stateOf (Chain.extend c bid newSlot votes hSlot)).h = (processHeight σ_blk).h := by
            show (stateTransition (stateOf c) B).h = (processHeight σ_blk).h
            unfold stateTransition
            rw [← hk, ← hσ_blk]
          rwa [← h_state]
        have h_blk_le : σ_blk.h ≤ h_f := by
          rw [hσ_blk, processBlock_h]
          exact h_iter_le
        have h_step_advance : (processHeight σ_blk).h = σ_blk.h + 1 := by
          rcases (height_progression σ_blk).1 with h_no | h_adv
          · rw [h_no] at h_final_gt
            omega
          · exact h_adv
        have h_blk_h : σ_blk.h = h_f := by
          omega
        have h_inv_iter : VoteWitnessInv (votesIncluded c)
            (iterateProcessSlot (stateOf c) k) := by
          exact iterateProcessSlot_voteWitness_pres _ _ _ (chain_voteWitness c)
        have h_chain_iter :
            (iterateProcessSlot (stateOf c) k).L ≼ B := by
          rw [iterateProcessSlot_L, chain_state_L_eq_tip]
          exact .step (.refl _)
        have h_inv_blk :
            VoteWitnessInv (votesIncluded c ++ B.votes) σ_blk := by
          rw [hσ_blk]
          exact processBlock_voteWitness_pres (votesIncluded c)
            (iterateProcessSlot (stateOf c) k) B h_inv_iter h_chain_iter
        have hσ_blk_L : σ_blk.L = B := by
          rw [hσ_blk, processBlock_L]
        have hσ_blk_L_anc : σ_blk.L ≼ B := by
          rw [hσ_blk_L]
          exact .refl _
        obtain ⟨Q, hQ_quorum, hQ_votes⟩ :=
          advance_votes_from_height_step hn h_inv_blk h_blk_h hσ_blk_L_anc h_step_advance
        refine ⟨Q, B, ?_, hQ_quorum, ?_⟩
        · exact .refl _
        · intro i hi
          obtain ⟨v, hv_mem, hrest⟩ := hQ_votes i hi
          exact ⟨v, by simpa [votesIncluded, ← hB] using hv_mem, hrest⟩

end DecoupledConsensus
