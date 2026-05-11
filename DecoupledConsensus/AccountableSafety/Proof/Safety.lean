import DecoupledConsensus.AccountableSafety.Proof.Advance

namespace AccountableSafety

/-! # Accountable Safety Proofs: main theorems

Lemma 3, Lemma 4, and Theorem 1 from the accountable-safety argument. -/

variable {n : ℕ}

open scoped Block

attribute [local instance] Classical.propDecidable

/-! ### Lemma 3 (Main safety) — using the chain-based `IsFinalizedAt`. -/

/-- **Lemma 3 (Main safety)**. If `C` is finalized at height `h_f`, then
    every chain whose tip-state has `h > h_f` contains `C` as an ancestor of
    the tip — unless at least `f + 1` validators are slashable.

    The finalization height is extracted from the `IsFinalizedAt` certificate;
    it is not read from protocol `State`. -/
lemma main_safety {f : ℕ} (hn : n = 3 * f + 1) (hId : Block.IdInjective n)
    {C : Block n} {h_f : ℕ}
    (hC : IsFinalizedAt f C h_f)
    {B : Block n} (chain : Chain n B) (hHeight : (stateOf chain).h > h_f) :
    @AtLeastFThirdSlashable n f ∨ C ≼ B := by
  obtain ⟨_B1, chain1, _hC_anc1, _hF_eq, hCert⟩ := hC
  by_cases h_hf_zero : h_f = 0
  · subst h_hf_zero
    have hC_genesis : C = Block.genesis := by
      rcases hCert with h_zero | h_pos
      · exact h_zero.2
      · omega
    refine Or.inr ?_
    rw [hC_genesis]
    have hgB : ∀ X : Block n, Block.genesis ≼ X := by
      intro X
      induction X with
      | genesis => exact .refl _
      | mk bid X' s vs ih => exact .step ih
    exact hgB B
  have h_hf_ge : h_f ≥ 1 := Nat.one_le_iff_ne_zero.mpr h_hf_zero
  obtain ⟨Q_F, hQ_F_quorum_strict, hQ_F_votes⟩ :
      FinalizeQuorumWitness (votesIncluded chain1) C h_f := by
    rcases hCert with h_zero | ⟨_hpos, hFin, _hJust, _hC_height, _hchain_gt⟩
    · exact False.elim (h_hf_zero h_zero.1)
    · exact hFin
  have hQ_F_quorum : IsQuorum f Q_F :=
    (isQuorum_iff_strict hn Q_F).mpr hQ_F_quorum_strict
  obtain ⟨Q_adv, B_star, hB_star, hQ_adv_quorum, hQ_adv_votes⟩ :=
    advance_witness hn chain h_f h_hf_ge hHeight
  have h_inter : (Q_adv ∩ Q_F).card ≥ f + 1 :=
    quorum_intersection_f hn Q_adv Q_F hQ_adv_quorum hQ_F_quorum
  by_cases h_conclusion : C ≼ B
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
        have hTC_block : T = C := hId hTC
        rw [hTC_block] at hT_anc
        exact h_conclusion (hT_anc.trans hB_star)
    have hVal_eq : v_a.validator = v_b.validator := by rw [hv_a_val, hv_b_val]
    refine ⟨B, chain, _B1, chain1, v_a, hv_a_mem, v_b, hv_b_mem,
      hv_a_val, hv_b_val, ?_⟩
    refine ⟨hVal_eq, Or.inl ?_⟩
    refine ⟨h_f, C.id, hv_b_fin, ?_, hv_a_neq⟩
    exact hv_a_height

/-! ### Lemma 4 (Finalized blocks form a chain) — using the chain-based
`IsFinalizedAt`. -/

/-- **Lemma 4 (Finalized blocks form a chain)**. Any two finalized
    checkpoints `(C, h_f)` and `(C', h_f')` with `h_f ≤ h_f'` are ordered
    as `C ≼ C'` (or at least `f + 1` validators are slashable). -/
lemma finalized_chain {f : ℕ} (hn : n = 3 * f + 1) (hId : Block.IdInjective n)
    {C C' : Block n} {h_f h_f' : ℕ}
    (hC : IsFinalizedAt f C h_f) (hC' : IsFinalizedAt f C' h_f')
    (hLE : h_f ≤ h_f') :
    @AtLeastFThirdSlashable n f ∨ C ≼ C' := by
  rcases (Nat.lt_or_ge h_f h_f') with h_lt | h_ge
  · by_cases h_hf_zero : h_f = 0
    · obtain ⟨_B1, _chain1, _hC_anc1, _hF_eq1, hCert1⟩ := hC
      have hC_genesis : C = Block.genesis := by
        rcases hCert1 with h_zero | h_pos
        · exact h_zero.2
        · exact False.elim (by omega)
      have h_genesis_anc : ∀ X : Block n, Block.genesis ≼ X := by
        intro X
        induction X with
        | genesis => exact .refl _
        | mk bid X' s vs ih => exact .step ih
      exact Or.inr (by rw [hC_genesis]; exact h_genesis_anc C')
    obtain ⟨_B', chain', hC'_anc, _hF'_eq, hCert'⟩ := hC'
    have h_state_gt : (stateOf chain').h > h_f := by
      rcases hCert' with h_zero | ⟨_hpos, _hFin, _hJust, _hC'_height, h_chain_gt⟩
      · have : h_f' = 0 := h_zero.1
        omega
      · omega
    rcases main_safety hn hId hC chain' h_state_gt with hSlash | hC_anc
    · exact Or.inl hSlash
    rcases Block.Ancestor.linear hC_anc hC'_anc with h_CC' | h_C'C
    · exact Or.inr h_CC'
    · by_cases h_eq : C = C'
      · rw [h_eq]
        exact Or.inr (.refl _)
      · exfalso
        obtain ⟨_B1, chain1, hC_anc1, _hF_eq1, hCert1⟩ := hC
        have hC_height :
            (stateOf (chain1.subchain hC_anc1)).h = h_f := by
          rcases hCert1 with h_zero | ⟨_hpos, _hFin, _hJust, h_height, _h_chain_gt⟩
          · exact False.elim (h_hf_zero h_zero.1)
          · exact h_height
        have hC'_height :
            (stateOf (chain'.subchain hC'_anc)).h = h_f' := by
          rcases hCert' with h_zero | ⟨_hpos, _hFin, _hJust, h_height, _h_chain_gt⟩
          · have : h_f' = 0 := h_zero.1
            omega
          · exact h_height
        have hSubLe :
            (stateOf ((chain1.subchain hC_anc1).subchain h_C'C)).h ≤
              (stateOf (chain1.subchain hC_anc1)).h :=
          stateOf_subchain_h_le (chain1.subchain hC_anc1) h_C'C
        have hSubC' :
            stateOf ((chain1.subchain hC_anc1).subchain h_C'C) =
              stateOf (chain'.subchain hC'_anc) :=
          chain_unique _ _
        have hSubLe' :
            (stateOf (chain'.subchain hC'_anc)).h ≤
              (stateOf (chain1.subchain hC_anc1)).h := by
          rwa [hSubC'] at hSubLe
        have h_le_hf : h_f' ≤ h_f :=
          by
            rw [← hC'_height, ← hC_height]
            exact hSubLe'
        omega
  · have hEq : h_f = h_f' := le_antisymm hLE h_ge
    subst h_f'
    by_cases h_hf_zero : h_f = 0
    · subst h_hf_zero
      obtain ⟨_B1, _chain1, _, _hF_eq1, hCert1⟩ := hC
      obtain ⟨_B2, _chain2, _, _hF_eq2, hCert2⟩ := hC'
      have hC_genesis : C = Block.genesis := by
        rcases hCert1 with h_zero | h_pos
        · exact h_zero.2
        · omega
      have hC'_genesis : C' = Block.genesis := by
        rcases hCert2 with h_zero | h_pos
        · exact h_zero.2
        · omega
      rw [hC_genesis, hC'_genesis]
      exact Or.inr (.refl _)
    obtain ⟨_B1, chain1, _hC_anc1, _hF_eq1, hCert1⟩ := hC
    obtain ⟨_B2, chain2, _hC'_anc2, _hF_eq2, hCert2⟩ := hC'
    obtain ⟨Q_F, hQ_F_quorum_strict, hQ_F_votes⟩ :
        FinalizeQuorumWitness (votesIncluded chain1) C h_f := by
      rcases hCert1 with h_zero | ⟨_hpos, hFin, _hJust, _hC_height, _hchain_gt⟩
      · exact False.elim (h_hf_zero h_zero.1)
      · exact hFin
    have hQ_F_quorum : IsQuorum f Q_F :=
      (isQuorum_iff_strict hn Q_F).mpr hQ_F_quorum_strict
    obtain ⟨Q_just_C', hQ_just_C'_quorum, hQ_just_C'_votes⟩ :
        JustifyQuorumWitness (votesIncluded chain2) C' h_f := by
      rcases hCert2 with h_zero | ⟨_hpos, _hFin, hJust, _hC'_height, _hchain_gt⟩
      · exact False.elim (h_hf_zero h_zero.1)
      · exact hJust
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
      refine ⟨_B2, chain2, _B1, chain1, v_J, hv_J_mem, v_F, hv_F_mem,
        hv_J_val, hv_F_val, ?_⟩
      refine ⟨hVal_eq, Or.inl ?_⟩
      refine ⟨h_f, C.id, hv_F_fin, ?_, ?_⟩
      · exact hv_J_height
      · rw [hv_J_target]
        intro h_inj
        injection h_inj with hCC
        exact h_CC' (hId hCC).symm

/-- **Theorem 1 (Accountable safety)**. No two conflicting blocks can be
    finalized — unless at least `f + 1` validators are provably slashable
    (under the BFT convention `n = 3 * f + 1`). -/
theorem accountable_safety {f : ℕ} (hn : n = 3 * f + 1)
    (hId : Block.IdInjective n)
    {C C' : Block n} {h_f h_f' : ℕ}
    (hC : IsFinalizedAt f C h_f) (hC' : IsFinalizedAt f C' h_f') :
    @AtLeastFThirdSlashable n f ∨ C ~ C' := by
  by_cases h : h_f ≤ h_f'
  · rcases finalized_chain hn hId hC hC' h with hslash | hcompat
    · exact Or.inl hslash
    · exact Or.inr (Or.inl hcompat)
  · have h' : h_f' ≤ h_f := Nat.le_of_lt (Nat.lt_of_not_le h)
    rcases finalized_chain hn hId hC' hC h' with hslash | hcompat
    · exact Or.inl hslash
    · exact Or.inr (Or.inr hcompat)


end AccountableSafety
