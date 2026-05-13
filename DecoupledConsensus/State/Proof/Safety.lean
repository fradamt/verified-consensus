import DecoupledConsensus.State.Proof.Advance

namespace DecoupledConsensus

/-! # Accountable Safety Proofs: main theorems

The main-safety, finalized-chain, and accountable-safety statements from the
accountable-safety argument. The proof-free statement layer is
`State.Statements`; `State.Properties` gives the proved facade. -/

variable {n : ℕ}

open scoped Block

attribute [local instance] Classical.propDecidable

private lemma genesis_ancestor (B : Block n) : Block.genesis ≼ B := by
  induction B with
  | genesis => exact .refl _
  | mk _ parent _ _ ih => exact .step ih

private lemma finalized_zero_eq_genesis {C : Block n}
    {B : Block n} {chain : Chain n B} {hC : C ≼ B}
    (hCert : FinalizedCertificate chain C 0 hC) : C = Block.genesis := by
  rcases hCert with h_zero | h_pos
  · exact h_zero.2
  · omega

private lemma finalized_nonzero_parts {C : Block n} {h_f : ℕ}
    {B : Block n} {chain : Chain n B} {hC : C ≼ B}
    (h_ne : h_f ≠ 0) (hCert : FinalizedCertificate chain C h_f hC) :
    h_f > 0 ∧
      FinalizeQuorumWitness (votesIncluded chain) C h_f ∧
      JustifyQuorumWitness (votesIncluded chain) C h_f ∧
      (stateOf (chain.subchain hC)).h = h_f ∧
      (stateOf chain).h > h_f := by
  rcases hCert with h_zero | h_pos
  · exact False.elim (h_ne h_zero.1)
  · exact h_pos

private lemma finalized_finalize_witness {C : Block n} {h_f : ℕ}
    {B : Block n} {chain : Chain n B} {hC : C ≼ B}
    (h_ne : h_f ≠ 0) (hCert : FinalizedCertificate chain C h_f hC) :
    FinalizeQuorumWitness (votesIncluded chain) C h_f :=
  (finalized_nonzero_parts h_ne hCert).2.1

private lemma finalized_justify_witness {C : Block n} {h_f : ℕ}
    {B : Block n} {chain : Chain n B} {hC : C ≼ B}
    (h_ne : h_f ≠ 0) (hCert : FinalizedCertificate chain C h_f hC) :
    JustifyQuorumWitness (votesIncluded chain) C h_f :=
  (finalized_nonzero_parts h_ne hCert).2.2.1

private lemma finalized_subchain_height {C : Block n} {h_f : ℕ}
    {B : Block n} {chain : Chain n B} {hC : C ≼ B}
    (h_ne : h_f ≠ 0) (hCert : FinalizedCertificate chain C h_f hC) :
    (stateOf (chain.subchain hC)).h = h_f :=
  (finalized_nonzero_parts h_ne hCert).2.2.2.1

private lemma finalized_chain_height_gt {C : Block n} {h_f : ℕ}
    {B : Block n} {chain : Chain n B} {hC : C ≼ B}
    (h_ne : h_f ≠ 0) (hCert : FinalizedCertificate chain C h_f hC) :
    (stateOf chain).h > h_f :=
  (finalized_nonzero_parts h_ne hCert).2.2.2.2

private lemma idInjectiveOnAncestors_sym {B₁ B₂ : Block n}
    (hId : Block.IdInjectiveOnAncestors B₁ B₂) :
    Block.IdInjectiveOnAncestors B₂ B₁ := by
  intro A B hA hB hEq
  apply hId
  · rcases hA with hA | hA
    · exact Or.inr hA
    · exact Or.inl hA
  · rcases hB with hB | hB
    · exact Or.inr hB
    · exact Or.inl hB
  · exact hEq

/-! ### Main safety — using explicit finalization witnesses. -/

/-- **Main safety**. If `C` is finalized at height `h_f`, then
    every chain whose tip-state has `h > h_f` contains `C` as an ancestor of
    the tip — unless at least `f + 1` validators are slashable.

    The hash/no-collision assumption is scoped to ancestors of the two chain
    tips involved in this comparison. -/
lemma main_safety {f : ℕ} (hn : n = 3 * f + 1)
    {B₁ B₂ C : Block n} {h_f : ℕ}
    (hId : Block.IdInjectiveOnAncestors B₁ B₂)
    (chain₁ : Chain n B₁) {hC₁ : C ≼ B₁}
    (_hF₁ : (stateOf chain₁).F = C)
    (hCert₁ : FinalizedCertificate chain₁ C h_f hC₁)
    (chain₂ : Chain n B₂) (hHeight : (stateOf chain₂).h > h_f) :
    @AtLeastFThirdSlashable n f ∨ C ≼ B₂ := by
  by_cases h_hf_zero : h_f = 0
  · subst h_hf_zero
    have hC_genesis : C = Block.genesis := by
      rcases hCert₁ with h_zero | h_pos
      · exact h_zero.2
      · omega
    refine Or.inr ?_
    rw [hC_genesis]
    exact genesis_ancestor B₂
  have h_hf_ge : h_f ≥ 1 := Nat.one_le_iff_ne_zero.mpr h_hf_zero
  obtain ⟨Q_F, hQ_F_quorum_strict, hQ_F_votes⟩ :
      FinalizeQuorumWitness (votesIncluded chain₁) C h_f :=
    finalized_finalize_witness h_hf_zero hCert₁
  have hQ_F_quorum : IsQuorum f Q_F :=
    (isQuorum_iff_strict hn Q_F).mpr hQ_F_quorum_strict
  obtain ⟨Q_adv, B_star, hB_star, hQ_adv_quorum, hQ_adv_votes⟩ :=
    advance_witness hn chain₂ h_f h_hf_ge hHeight
  have h_inter : (Q_adv ∩ Q_F).card ≥ f + 1 :=
    quorum_intersection_f hn Q_adv Q_F hQ_adv_quorum hQ_F_quorum
  by_cases h_conclusion : C ≼ B₂
  · exact Or.inr h_conclusion
  · left
    refine ⟨Q_adv ∩ Q_F, h_inter, ?_⟩
    intro i hi
    have hi_adv : i ∈ Q_adv := (Finset.mem_inter.mp hi).1
    have hi_QF : i ∈ Q_F := (Finset.mem_inter.mp hi).2
    obtain ⟨v_a, hv_a_mem, hv_a_val, hv_a_height, hv_a_target⟩ := hQ_adv_votes i hi_adv
    obtain ⟨v_b, hv_b_mem, hv_b_val, hv_b_fin⟩ := hQ_F_votes i hi_QF
    have hv_a_neq : v_a.target ≠ some C.id := by
      intro h_eq
      rcases hv_a_target with h_none | ⟨T, hT_eq, hT_anc⟩
      · rw [h_none] at h_eq
        cases h_eq
      · rw [hT_eq] at h_eq
        injection h_eq with hTC
        have hT_tip : T ≼ B₂ := hT_anc.trans hB_star
        have hTC_block : T = C :=
          hId (Or.inr hT_tip) (Or.inl hC₁) hTC
        rw [hTC_block] at hT_anc
        exact h_conclusion (hT_anc.trans hB_star)
    have hVal_eq : v_a.validator = v_b.validator := by rw [hv_a_val, hv_b_val]
    refine ⟨B₂, chain₂, B₁, chain₁, v_a, hv_a_mem, v_b, hv_b_mem,
      hv_a_val, hv_b_val, ?_⟩
    refine ⟨hVal_eq, Or.inl ?_⟩
    refine ⟨h_f, C.id, hv_b_fin, ?_, hv_a_neq⟩
    exact hv_a_height

/-! ### Finalized blocks form a chain — using explicit witnesses. -/

private lemma finalized_chain_lt {f : ℕ} (hn : n = 3 * f + 1)
    {B₁ B₂ C C' : Block n} {h_f h_f' : ℕ}
    (hId : Block.IdInjectiveOnAncestors B₁ B₂)
    (chain₁ : Chain n B₁) {hC₁ : C ≼ B₁}
    (hF₁ : (stateOf chain₁).F = C)
    (hCert₁ : FinalizedCertificate chain₁ C h_f hC₁)
    (chain₂ : Chain n B₂) {hC₂ : C' ≼ B₂}
    (_hF₂ : (stateOf chain₂).F = C')
    (hCert₂ : FinalizedCertificate chain₂ C' h_f' hC₂)
    (h_lt : h_f < h_f') :
    @AtLeastFThirdSlashable n f ∨ C ≼ C' := by
  by_cases h_hf_zero : h_f = 0
  · have hCert₁0 : FinalizedCertificate chain₁ C 0 hC₁ := by
      simpa [h_hf_zero] using hCert₁
    have hC_genesis : C = Block.genesis := finalized_zero_eq_genesis hCert₁0
    exact Or.inr (by rw [hC_genesis]; exact genesis_ancestor C')
  have h_hf'_ne : h_f' ≠ 0 := by omega
  have h_state_gt : (stateOf chain₂).h > h_f := by
    have h_chain_gt := finalized_chain_height_gt h_hf'_ne hCert₂
    omega
  rcases main_safety hn hId chain₁ hF₁ hCert₁ chain₂ h_state_gt with hSlash | hC_anc
  · exact Or.inl hSlash
  rcases Block.Ancestor.linear hC_anc hC₂ with h_CC' | h_C'C
  · exact Or.inr h_CC'
  · by_cases h_eq : C = C'
    · rw [h_eq]
      exact Or.inr (.refl _)
    · exfalso
      have hC_height :
          (stateOf (chain₁.subchain hC₁)).h = h_f :=
        finalized_subchain_height h_hf_zero hCert₁
      have hC'_height :
          (stateOf (chain₂.subchain hC₂)).h = h_f' :=
        finalized_subchain_height h_hf'_ne hCert₂
      have hSubLe :
          (stateOf ((chain₁.subchain hC₁).subchain h_C'C)).h ≤
            (stateOf (chain₁.subchain hC₁)).h :=
        stateOf_subchain_h_le (chain₁.subchain hC₁) h_C'C
      have hSubC' :
          stateOf ((chain₁.subchain hC₁).subchain h_C'C) =
            stateOf (chain₂.subchain hC₂) :=
        chain_unique _ _
      have hSubLe' :
          (stateOf (chain₂.subchain hC₂)).h ≤
            (stateOf (chain₁.subchain hC₁)).h := by
        rwa [hSubC'] at hSubLe
      have h_le_hf : h_f' ≤ h_f := by
        rw [← hC'_height, ← hC_height]
        exact hSubLe'
      omega

private lemma finalized_chain_eq {f : ℕ} (hn : n = 3 * f + 1)
    {B₁ B₂ C C' : Block n} {h_f : ℕ}
    (hId : Block.IdInjectiveOnAncestors B₁ B₂)
    (chain₁ : Chain n B₁) {hC₁ : C ≼ B₁}
    (_hF₁ : (stateOf chain₁).F = C)
    (hCert₁ : FinalizedCertificate chain₁ C h_f hC₁)
    (chain₂ : Chain n B₂) {hC₂ : C' ≼ B₂}
    (_hF₂ : (stateOf chain₂).F = C')
    (hCert₂ : FinalizedCertificate chain₂ C' h_f hC₂) :
    @AtLeastFThirdSlashable n f ∨ C ≼ C' := by
  by_cases h_hf_zero : h_f = 0
  · subst h_hf_zero
    have hC_genesis : C = Block.genesis := finalized_zero_eq_genesis hCert₁
    have hC'_genesis : C' = Block.genesis := finalized_zero_eq_genesis hCert₂
    rw [hC_genesis, hC'_genesis]
    exact Or.inr (.refl _)
  obtain ⟨Q_F, hQ_F_quorum_strict, hQ_F_votes⟩ :
      FinalizeQuorumWitness (votesIncluded chain₁) C h_f :=
    finalized_finalize_witness h_hf_zero hCert₁
  have hQ_F_quorum : IsQuorum f Q_F :=
    (isQuorum_iff_strict hn Q_F).mpr hQ_F_quorum_strict
  obtain ⟨Q_just_C', hQ_just_C'_quorum, hQ_just_C'_votes⟩ :
      JustifyQuorumWitness (votesIncluded chain₂) C' h_f :=
    finalized_justify_witness h_hf_zero hCert₂
  have hQ_just_C'_quorum_f : IsQuorum f Q_just_C' :=
    (isQuorum_iff_strict hn Q_just_C').mpr hQ_just_C'_quorum
  have h_inter : (Q_F ∩ Q_just_C').card ≥ f + 1 :=
    quorum_intersection_f hn Q_F Q_just_C' hQ_F_quorum hQ_just_C'_quorum_f
  by_cases h_CC' : C = C'
  · exact Or.inr (h_CC' ▸ Block.Ancestor.refl C)
  · left
    refine ⟨Q_F ∩ Q_just_C', h_inter, ?_⟩
    intro i hi
    have hi_QF : i ∈ Q_F := (Finset.mem_inter.mp hi).1
    have hi_Qj : i ∈ Q_just_C' := (Finset.mem_inter.mp hi).2
    obtain ⟨v_F, hv_F_mem, hv_F_val, hv_F_fin⟩ := hQ_F_votes i hi_QF
    obtain ⟨v_J, hv_J_mem, hv_J_val, hv_J_target, hv_J_height⟩ :=
      hQ_just_C'_votes i hi_Qj
    have hVal_eq : v_J.validator = v_F.validator := by rw [hv_J_val, hv_F_val]
    refine ⟨B₂, chain₂, B₁, chain₁, v_J, hv_J_mem, v_F, hv_F_mem,
      hv_J_val, hv_F_val, ?_⟩
    refine ⟨hVal_eq, Or.inl ?_⟩
    refine ⟨h_f, C.id, hv_F_fin, ?_, ?_⟩
    · exact hv_J_height
    · rw [hv_J_target]
      intro h_inj
      injection h_inj with hCC
      exact h_CC' (hId (Or.inr hC₂) (Or.inl hC₁) hCC).symm

/-- **Finalized blocks form a chain**. Any two finalized
    checkpoints `(C, h_f)` and `(C', h_f')` with `h_f ≤ h_f'` are ordered
    as `C ≼ C'` (or at least `f + 1` validators are slashable). -/
lemma finalized_chain {f : ℕ} (hn : n = 3 * f + 1)
    {B₁ B₂ C C' : Block n} {h_f h_f' : ℕ}
    (hId : Block.IdInjectiveOnAncestors B₁ B₂)
    (chain₁ : Chain n B₁) {hC₁ : C ≼ B₁}
    (hF₁ : (stateOf chain₁).F = C)
    (hCert₁ : FinalizedCertificate chain₁ C h_f hC₁)
    (chain₂ : Chain n B₂) {hC₂ : C' ≼ B₂}
    (hF₂ : (stateOf chain₂).F = C')
    (hCert₂ : FinalizedCertificate chain₂ C' h_f' hC₂)
    (hLE : h_f ≤ h_f') :
    @AtLeastFThirdSlashable n f ∨ C ≼ C' := by
  rcases (Nat.lt_or_ge h_f h_f') with h_lt | h_ge
  · exact finalized_chain_lt hn hId chain₁ hF₁ hCert₁ chain₂ hF₂ hCert₂ h_lt
  · have hEq : h_f = h_f' := le_antisymm hLE h_ge
    subst h_f'
    exact finalized_chain_eq hn hId chain₁ hF₁ hCert₁ chain₂ hF₂ hCert₂

/-- **Accountable safety**. No two conflicting blocks can be
    finalized — unless at least `f + 1` validators are provably slashable
    (under the BFT convention `n = 3 * f + 1`).

    The id-injectivity premise is scoped to ancestors of the two chain tips
    that witness the finalization events. This models collision-free hashes
    only for the protocol histories under consideration, not for arbitrary raw
    `Block` syntax. -/
theorem accountable_safety {f : ℕ} (hn : n = 3 * f + 1)
    {B₁ B₂ C C' : Block n} {h_f h_f' : ℕ}
    (hId : Block.IdInjectiveOnAncestors B₁ B₂)
    (chain₁ : Chain n B₁) {hC₁ : C ≼ B₁}
    (hF₁ : (stateOf chain₁).F = C)
    (hCert₁ : FinalizedCertificate chain₁ C h_f hC₁)
    (chain₂ : Chain n B₂) {hC₂ : C' ≼ B₂}
    (hF₂ : (stateOf chain₂).F = C')
    (hCert₂ : FinalizedCertificate chain₂ C' h_f' hC₂) :
    @AtLeastFThirdSlashable n f ∨ C ~ C' := by
  by_cases h : h_f ≤ h_f'
  · rcases finalized_chain hn hId chain₁ hF₁ hCert₁ chain₂ hF₂ hCert₂ h with
      hslash | hcompat
    · exact Or.inl hslash
    · exact Or.inr (Or.inl hcompat)
  · have h' : h_f' ≤ h_f := Nat.le_of_lt (Nat.lt_of_not_le h)
    rcases finalized_chain hn (idInjectiveOnAncestors_sym hId)
        chain₂ hF₂ hCert₂ chain₁ hF₁ hCert₁ h' with hslash | hcompat
    · exact Or.inl hslash
    · exact Or.inr (Or.inr hcompat)


end DecoupledConsensus
