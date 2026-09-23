module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.WeakFGWitness
public import DecoupledConsensusProofs.Protocol.ChainState.FGRootWitness

@[expose] public section

/-!
# FG-root sources under core admissibility

A non-genesis selected FG root has a processed justification certificate.
An honest quorum member supplies its exact checkpoint witness. Both the
justified-root and finalized-root branches use this argument. No accountable
fault bound is needed for provenance. Safety of old witnesses remains a
bootstrap obligation; recent witnesses use the earlier-action induction.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakFG

open Internal Execution
open Proofs.Optimistic Protocol

variable {V : Type} [DecidableEq V] [Fintype V]



alias fgRoot_confirmationWitness_at_read :=
  DecoupledConsensusModel.Proofs.HealingSurface.fgRoot_confirmationWitness_at_read

alias fgRoot_confirmationWitness_at_action :=
  DecoupledConsensusModel.Proofs.HealingSurface.fgRoot_confirmationWitness_at_action

alias fgRoot_compatible_of_bootstrap_and_recentActions_at_read :=
  Proofs.HealingSurface.fgRoot_compatible_of_bootstrap_and_recentActions_at_read


/- /-- Both FG-root branches have a processed justification source. -/
/-- Both FG-root branches have a processed justification source. -/
theorem fgRoot_justificationSource_at_read
    (S: Setup V) {rho: Run V} (adm: AdmissibleCore S rho) (v: V) (time: Time):
    ∃ C ∈ (rho.storeBeforeTime S v time).T,
      (derived_state S.E S.cfg C).J =
        Protocol.get_fg_root (rho.storeBeforeTime S v time).toHealing.toFG:= by
  let st:= rho.storeBeforeTime S v time
  have hdep:= Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
    adm.toDeliveryWellFormed time v
  change ∃ C ∈ st.T, (derived_state S.E S.cfg C).J =
    Protocol.get_fg_root st.toHealing.toFG
  unfold Protocol.get_fg_root
  split_ifs
  · obtain ⟨C, hC, _, hJ⟩:=
      Proofs.Bridges.storeJustificationOnChain_depReachable S.E S.hc S.cfg (S.node v) hdep
    exact ⟨C, hC, hJ⟩
  · obtain ⟨C, hC, hF⟩:=
      Proofs.Bridges.storeFinalizationOnChain_depReachable S.E S.hc S.cfg (S.node v) hdep
    obtain ⟨D, hDC, hDJ⟩:=
      Protocol.derived_finalized_justificationAncestor S.E S.cfg C
    have hclosed: ParentClosed st:=
      parentClosed_depReachable S.E S.hc S.cfg (S.node v) st hdep
    exact ⟨D, Proofs.Records.mem_of_preceq ((parentClosed_iff st).mp hclosed).2
      D C hC hDC, hDJ.trans hF⟩
/-- A non-genesis justification is an earlier honest target action's witness. -/
theorem processedJustification_confirmationWitness
    (S: Setup V) {rho: Run V} (adm: AdmissibleCore S rho)
    (hmajority: HonestWeightMajority S rho.honest)
    {v: V} (hv: v ∈ rho.honest) {time: Time} {C: Block V}
    (hC: C ∈ (rho.storeBeforeTime S v time).T):
    (derived_state S.E S.cfg C).J = Block.genesis ∨
      ∃ (a: CombinedAttestation V) (ta: Time),
        a.val_index ∈ rho.honest ∧
        rho.emits S a.val_index (Object.attest a) ta ∧ ta < time ∧
        a.height_pair = HeightPair.target (derived_state S.E S.cfg C).h_j
          (derived_state S.E S.cfg C).J.root ∧
        fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
          some (derived_state S.E S.cfg C).J:= by
  by_cases hz: (derived_state S.E S.cfg C).h_j = 0
  · exact Or.inl (AlignedRoundLemmas.derived_state_J_of_h_j_zero S.E S.cfg C hz)
  obtain ⟨Q, hQ, hwit⟩:=
    AlignedRoundLemmas.justification_certificate S.E S.cfg C hz
  obtain ⟨i, hiQ, hiHon⟩:=
    Protocol.HonestWeightMajority.exists_honest_member_of_quorum hmajority hQ
  obtain ⟨a, haC, hai, hap⟩:= hwit i hiQ
  have haHon: a.val_index ∈ rho.honest:= by
    rw [hai]
    exact hiHon
  obtain ⟨ta, hta, hemit⟩:=
    carriedArePastEmissions_of_admissible S adm time v hC a haC haHon
  obtain ⟨Cfg, T, hwitness, hsource, _, _, _, hTCfg, hrow⟩:=
    honestHeightRow_confirmationWitness S adm haHon hemit
      (h:= (derived_state S.E S.cfg C).h_j) (by simp [hap, HeightPair.height?])
  have hroot: T.root = (derived_state S.E S.cfg C).J.root:= by
    rcases hrow with ht | ht
    · simpa [hap] using ht.symm
    · simp [hap] at ht
  have hT:= (actionSourceAncestor_mem_and_runBlock S adm haHon hsource hTCfg).2
  have hdep:= Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
    adm.toDeliveryWellFormed time v
  have hclosed: ParentClosed (rho.storeBeforeTime S v time):=
    parentClosed_depReachable S.E S.hc S.cfg (S.node v) _ hdep
  have hJmem: (derived_state S.E S.cfg C).J ∈ (rho.storeBeforeTime S v time).T:=
    Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hclosed).2 _ C hC
      (Proofs.Records.derived_state_J_preceq S.E S.cfg C)
  have hJ: RunBlock S rho (derived_state S.E S.cfg C).J:= by
    obtain ⟨n, hn, _⟩:=
      Proofs.Bridges.stateBeforeTime_eq_stateBefore S adm.toScheduleWellFormed time
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i:= n)
    rw [← hn]
    exact hJmem
  have hEq: T = (derived_state S.E S.cfg C).J:=
    adm.toRootCollisionFree.root_injective T _ hT hJ T _
      ⟨T, Finset.mem_insert_self _ _, Block.preceq_self T⟩
      ⟨_, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), Block.preceq_self _⟩
      hroot
  exact Or.inr ⟨a, ta, haHon, hemit, hta, hap, hEq ▸ hwitness⟩
/-- The selected FG root is genesis or an earlier honest checkpoint witness. -/
theorem fgRoot_confirmationWitness_at_read
    (S: Setup V) {rho: Run V} (adm: AdmissibleCore S rho)
    (hmajority: HonestWeightMajority S rho.honest)
    {v: V} (hv: v ∈ rho.honest) (time: Time):
    let R:= Protocol.get_fg_root (rho.storeBeforeTime S v time).toHealing.toFG
    R = Block.genesis ∨ ∃ (a: CombinedAttestation V) (ta: Time),
      a.val_index ∈ rho.honest ∧
      rho.emits S a.val_index (Object.attest a) ta ∧ ta < time ∧
      a.height_pair = HeightPair.target (derived_state S.E S.cfg R).h R.root ∧
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) = some R:= by
  obtain ⟨C, hC, hJ⟩:= fgRoot_justificationSource_at_read S adm v time
  rcases processedJustification_confirmationWitness S adm hmajority hv hC with
      hgen | ⟨a, ta, haHon, hemit, hta, hpair, hwitness⟩
  · exact Or.inl (hJ.symm.trans hgen)
  · rcases Protocol.derived_justified_height S.E S.cfg C with hz | hheight
    · exact Or.inl (hJ.symm.trans
        (AlignedRoundLemmas.derived_state_J_of_h_j_zero S.E S.cfg C hz))
    · refine Or.inr ⟨a, ta, haHon, hemit, hta, ?_, hJ ▸ hwitness⟩
      simpa only [← hJ, hheight] using hpair
/-- An action's selected FG root has a strictly earlier action source. -/
theorem fgRoot_confirmationWitness_at_action
    (S: Setup V) {rho: Run V} (adm: AdmissibleCore S rho)
    (hmajority: HonestWeightMajority S rho.honest)
    {v: V} (hv: v ∈ rho.honest) (r: Round):
    let R:= Protocol.get_fg_root (actionStoreAt S rho v r).toHealing.toFG
    R = Block.genesis ∨ ∃ a: CombinedAttestation V,
      a.val_index ∈ rho.honest ∧
      rho.emits S a.val_index (Object.attest a) (S.a a.round) ∧ a.round < r ∧
      a.height_pair = HeightPair.target (derived_state S.E S.cfg R).h R.root ∧
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) = some R:= by
  dsimp only
  rw [actionStoreAt_fgRoot_eq_storeBeforeTime]
  rcases fgRoot_confirmationWitness_at_read S adm hmajority hv (S.a r) with
      hgen | ⟨a, ta, ha, hemit, ht, hpair, hT⟩
  · exact Or.inl hgen
  · have htime:= (Proofs.Optimistic.emits_attest_shape S hemit).2
    have hlt: S.a a.round < S.a r:= by simpa only [htime] using ht
    have hr: a.round < r:= by
      by_contra hnot
      exact (not_lt_of_ge (Assembly.a_mono S (Nat.le_of_not_gt hnot))) hlt
    exact Or.inr ⟨a, ha, by simpa only [htime] using hemit, hr, hpair, hT⟩
/-- Recent witness safety and the previous-source bootstrap give FG-root compatibility. -/
theorem fgRoot_compatible_of_bootstrap_and_recentActions_at_read
    (S: Setup V) {rho: Run V} (adm: AdmissibleCore S rho)
    (hmajority: HonestWeightMajority S rho.honest)
    {v: V} (hv: v ∈ rho.honest) {time: Time} {cut: Round} {B: Block V}
    (hrecent: ∀ r, cut ≤ r → S.a r < time → ∀ w ∈ rho.honest, ∀ T,
      fgConfirmationWitness S (actionStoreAt S rho w r) = some T →
        Block.compatible B T = true)
    (hbootstrap: ∀ (a: CombinedAttestation V) (ta: Time),
      let R:= Protocol.get_fg_root (rho.storeBeforeTime S v time).toHealing.toFG
      a.val_index ∈ rho.honest → rho.emits S a.val_index (Object.attest a) ta →
      ta < time → a.round < cut →
      a.height_pair = HeightPair.target (derived_state S.E S.cfg R).h R.root →
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) = some R →
        Block.compatible B R = true):
    Block.compatible
      (Protocol.get_fg_root (rho.storeBeforeTime S v time).toHealing.toFG) B = true:= by
  rcases fgRoot_confirmationWitness_at_read S adm hmajority hv time with
      hgen | ⟨a, ta, ha, hemit, ht, hpair, hT⟩
  · rw [hgen]
    simp [Block.compatible, Protocol.preceq_genesis]
  · suffices h: Block.compatible B
        (Protocol.get_fg_root (rho.storeBeforeTime S v time).toHealing.toFG) = true by
      simpa only [Block.compatible, Bool.or_comm] using h
    by_cases hboot: a.round < cut
    · exact hbootstrap a ta ha hemit ht hboot hpair hT
    · exact hrecent a.round (Nat.le_of_not_gt hboot)
        (by simpa only [(Proofs.Optimistic.emits_attest_shape S hemit).2] using ht)
        a.val_index ha _ hT
-/

#print axioms fgRoot_confirmationWitness_at_read
#print axioms fgRoot_confirmationWitness_at_action
#print axioms fgRoot_compatible_of_bootstrap_and_recentActions_at_read

end WeakFG
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
