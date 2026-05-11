import DecoupledConsensus.State.Proof.Safety
import DecoupledConsensus.Store.Proof.History

namespace DecoupledConsensus

/-! # Store Proofs: section-3 conditional facts

These are the store-level facts that use the section-2 accountable-safety
surface. They are stated with explicit finalization witnesses and scoped
id-injectivity premises, matching the hash-assumption style of
`accountable_safety`.

The full paper upgrade/order-independence argument also needs certificate
history for the store-finalized root. This module proves the reusable pieces
that follow from the current executable store plus explicit witness premises. -/

variable {n : ℕ}

open scoped Block

attribute [local instance] Classical.propDecidable

namespace Store

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

private lemma finalized_target_height {C : Block n} {h_f : ℕ}
    {B : Block n} {chain : Chain n B} {hC : C ≼ B}
    (h_ne : h_f ≠ 0) (hCert : FinalizedCertificate chain C h_f hC) :
    (stateOf (chain.subchain hC)).h = h_f :=
  (finalized_nonzero_parts h_ne hCert).2.2.2.1

private lemma FinalizationRecord.target_height {F : Block n} {h_f : ℕ}
    (r : FinalizationRecord F h_f) (h_ne : h_f ≠ 0) :
    (stateOf (r.chain.subchain r.target_ancestor)).h = h_f :=
  finalized_target_height h_ne r.certificate

/-- A processed `(J, hj)` descriptor forces the store frontier `hmax` strictly
    above that descriptor height. -/
lemma processedJustification_height_lt_hmax {S : Store n} {C : Block n} {h : ℕ}
    (hS : Reachable S) (hProc : ProcessedJustification S C h) :
    h < S.hmax := by
  rcases hProc with ⟨e, he, _hJ, hhj⟩
  have hlt : h < e.height := by
    have hchain := chain_hj_lt_h e.chain
    have hhj' : (stateOf e.chain).hj = h := by
      simpa [StoreEntry.state] using hhj
    rw [hhj'] at hchain
    simpa [StoreEntry.height, StoreEntry.state] using hchain
  have hle : e.height ≤ S.hmax := reachable_entry_height_le_hmax hS he
  omega

/-- Section-3 `certchain`, compatibility form. If `F` is finalized at `h_f`
    and a processed chain's current justified checkpoint is `(C, h)` with
    `h ≥ h_f`, then `F` and `C` lie on one chain unless accountability has
    already found at least `f + 1` slashable validators. -/
theorem certchain_compatible {f : ℕ} (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {Bf Bj F C : Block n} {h_f h : ℕ}
    (hId : Block.IdInjectiveOnAncestors Bf Bj)
    (chainF : Chain n Bf) {hFanc : F ≼ Bf}
    (hFstate : (stateOf chainF).F = F)
    (hFCert : FinalizedCertificate chainF F h_f hFanc)
    (chainJ : Chain n Bj)
    (hJ : (stateOf chainJ).J = C)
    (hhj : (stateOf chainJ).hj = h)
    (hle : h_f ≤ h) :
    F ~ C := by
  have hTipHigh : (stateOf chainJ).h > h_f := by
    have hlt := chain_hj_lt_h chainJ
    rw [hhj] at hlt
    omega
  have hC_tip : C ≼ Bj := by
    simpa [hJ] using chain_J_le_L chainJ
  rcases main_safety hn hId chainF hFstate hFCert chainJ hTipHigh with
    hSlash | hF_tip
  · exact False.elim (hNoSlash hSlash)
  · exact Block.Ancestor.linear hF_tip hC_tip

/-- Record-based Section-3 `certchain`, compatibility form. -/
theorem certchain_record_compatible {f : ℕ} (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {S : Store n} {F C : Block n} {h_f h : ℕ}
    (rF : FinalizationRecord F h_f) (rJ : JustificationRecord S C h)
    (hId : rF.IdInjectiveAgainstStore S)
    (hle : h_f ≤ h) :
    F ~ C := by
  exact certchain_compatible hn hNoSlash (hId rJ.entry rJ.mem)
    rF.chain rF.final_state rF.certificate
    rJ.entry.chain
    (by simpa [StoreEntry.state] using rJ.target_eq)
    (by simpa [StoreEntry.state] using rJ.height_eq)
    hle

/-- At a positive finalized height, a same-height justification must target the
    finalized block unless accountable slashability has already occurred. -/
theorem finalized_eq_justified_same_height {f : ℕ} (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {S : Store n} {F C : Block n} {h_f : ℕ}
    (rF : FinalizationRecord F h_f) (rJ : JustificationRecord S C h_f)
    (hId : rF.IdInjectiveAgainstStore S) :
    C = F := by
  by_cases h_zero : h_f = 0
  · subst h_zero
    have hF_genesis : F = Block.genesis :=
      finalized_zero_eq_genesis rF.certificate
    have hJ_hj_zero : (stateOf rJ.entry.chain).hj = 0 := by
      simpa [StoreEntry.state] using rJ.height_eq
    have hC_genesis : C = Block.genesis := by
      have h := chain_HjZeroJGenesis rJ.entry.chain hJ_hj_zero
      have hTarget : (stateOf rJ.entry.chain).J = C := by
        simpa [StoreEntry.state] using rJ.target_eq
      exact hTarget.symm.trans h
    rw [hC_genesis, hF_genesis]
  obtain ⟨Q_F, hQ_F_quorum_strict, hQ_F_votes⟩ :
      FinalizeQuorumWitness (votesIncluded rF.chain) F h_f :=
    finalized_finalize_witness h_zero rF.certificate
  obtain ⟨Q_J, hQ_J_quorum_strict, hQ_J_votes⟩ :
      JustifyQuorumWitness (votesIncluded rJ.entry.chain) C h_f := by
    rcases rJ.witness with h_genesis | h_wit
    · omega
    · exact h_wit
  have hQ_F_quorum : IsQuorum f Q_F :=
    (isQuorum_iff_strict hn Q_F).mpr hQ_F_quorum_strict
  have hQ_J_quorum : IsQuorum f Q_J :=
    (isQuorum_iff_strict hn Q_J).mpr hQ_J_quorum_strict
  have h_inter : (Q_F ∩ Q_J).card ≥ f + 1 :=
    quorum_intersection_f hn Q_F Q_J hQ_F_quorum hQ_J_quorum
  by_cases hCF : C = F
  · exact hCF
  · exfalso
    apply hNoSlash
    refine ⟨Q_F ∩ Q_J, h_inter, ?_⟩
    intro i hi
    have hi_QF : i ∈ Q_F := (Finset.mem_inter.mp hi).1
    have hi_QJ : i ∈ Q_J := (Finset.mem_inter.mp hi).2
    obtain ⟨v_F, hv_F_mem, hv_F_val, hv_F_fin⟩ := hQ_F_votes i hi_QF
    obtain ⟨v_J, hv_J_mem, hv_J_val, hv_J_target, hv_J_height⟩ :=
      hQ_J_votes i hi_QJ
    have hVal_eq : v_J.validator = v_F.validator := by rw [hv_J_val, hv_F_val]
    refine ⟨rJ.entry.block, rJ.entry.chain, rF.tip, rF.chain,
      v_J, hv_J_mem, v_F, hv_F_mem, hv_J_val, hv_F_val, ?_⟩
    refine ⟨hVal_eq, Or.inl ?_⟩
    refine ⟨h_f, F.id, hv_F_fin, hv_J_height, ?_⟩
    rw [hv_J_target]
    intro hSome
    injection hSome with hIdEq
    exact hCF (hId rJ.entry rJ.mem (Or.inr rJ.target_ancestor)
      (Or.inl rF.target_ancestor) hIdEq)

/-- Positive-height strict form of `certchain`: if the processed justification
    is at a strictly higher height than the finalization certificate, the
    finalized block is a proper ancestor of the justified target. The `h_f ≠ 0`
    premise isolates the genesis convention, whose certificate height is `0`
    while the genesis state has height `1`. -/
theorem certchain_record_strict_of_positive {f : ℕ} (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {S : Store n} {F C : Block n} {h_f h : ℕ}
    (rF : FinalizationRecord F h_f) (rJ : JustificationRecord S C h)
    (hId : rF.IdInjectiveAgainstStore S)
    (hpos : h_f ≠ 0) (hlt : h_f < h) :
    F ≼ C ∧ F ≠ C := by
  have hCompat : F ~ C :=
    certchain_record_compatible hn hNoSlash rF rJ hId (Nat.le_of_lt hlt)
  have hFHeight := rF.target_height hpos
  have h_ne_h : h ≠ 0 := by omega
  have hJHeight := rJ.target_height_of_ne_zero h_ne_h
  rcases hCompat with hFC | hCF
  · refine ⟨hFC, ?_⟩
    intro hEq
    subst C
    have hSame :
        stateOf (rJ.entry.chain.subchain rJ.target_ancestor) =
          stateOf (rF.chain.subchain rF.target_ancestor) :=
      chain_unique _ _
    have h_eq_height : h = h_f := by
      rw [← hJHeight, hSame, hFHeight]
    omega
  · exfalso
    have hSubLe :
        (stateOf ((rF.chain.subchain rF.target_ancestor).subchain hCF)).h ≤
          (stateOf (rF.chain.subchain rF.target_ancestor)).h :=
      stateOf_subchain_h_le (rF.chain.subchain rF.target_ancestor) hCF
    have hSame :
        stateOf ((rF.chain.subchain rF.target_ancestor).subchain hCF) =
          stateOf (rJ.entry.chain.subchain rJ.target_ancestor) :=
      chain_unique _ _
    rw [hSame, hJHeight, hFHeight] at hSubLe
    omega

/-- Upgrade, stated against explicit certificate records: if the current store
    root is justified at height at least the finalization height, then it
    descends from the finalized block. -/
theorem upgrade_of_current_root_record {f : ℕ} (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {S : Store n} {F : Block n} {h_f : ℕ}
    (rF : FinalizationRecord F h_f)
    (rRoot : JustificationRecord S S.J S.hj)
    (hId : rF.IdInjectiveAgainstStore S)
    (hhj : h_f ≤ S.hj) :
    F ≼ S.J := by
  by_cases h_zero : h_f = 0
  · subst h_zero
    have hF_genesis : F = Block.genesis :=
      finalized_zero_eq_genesis rF.certificate
    rw [hF_genesis]
    induction S.J with
    | genesis => exact .refl _
    | mk _ parent _ _ ih => exact .step ih
  rcases lt_or_eq_of_le hhj with hlt | heq
  · exact (certchain_record_strict_of_positive hn hNoSlash rF rRoot hId h_zero hlt).1
  · subst heq
    have hEq : S.J = F :=
      finalized_eq_justified_same_height hn hNoSlash rF rRoot hId
    rw [hEq]
    exact .refl _

/-- If a store has processed a block whose post-state justifies `F` at the
    finalization height, then any later store containing that processed
    descriptor has `F` in the executable viable tree. -/
theorem finalized_viableBool_of_processedJustification {f : ℕ}
    (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {S : Store n} (hS : Reachable S)
    {Bf F : Block n} {h_f : ℕ}
    (hIdStore : IdInjectiveAgainstStore Bf S)
    (chainF : Chain n Bf) {hFanc : F ≼ Bf}
    (hFstate : (stateOf chainF).F = F)
    (hFCert : FinalizedCertificate chainF F h_f hFanc)
    (hProc : ProcessedJustification S F h_f) :
    S.isViableBool F = true := by
  rcases reachable_hmax_witness hS with ⟨eMax, heMax, hMax⟩
  have hProcHigh : h_f < S.hmax :=
    processedJustification_height_lt_hmax hS hProc
  have hEntryHigh : eMax.height > h_f := by
    rw [hMax]
    exact hProcHigh
  have hF_eMax : F ≼ eMax.block := by
    rcases main_safety hn (hIdStore eMax heMax) chainF hFstate hFCert
        eMax.chain hEntryHigh with hSlash | hAnc
    · exact False.elim (hNoSlash hSlash)
    · exact hAnc
  have hClosed : AncestorClosed S := reachable_ancestorClosed hS
  have hEntryContains : Contains S eMax.block := ⟨eMax, heMax, rfl⟩
  have hFContains : Contains S F := hClosed hEntryContains hF_eMax
  have hFBool : S.containsBlockBool F = true :=
    containsBlockBool_of_contains hFContains
  have hThreshold : S.heightThreshold ≤ eMax.height := by
    simp [heightThreshold, hMax]
  exact isViableBool_of_entry_ancestor_height hFBool heMax hF_eMax hThreshold

/-- Future-facing form of `finalized_viableBool_of_processedJustification`. -/
theorem future_finalized_viableBool_of_processedJustification {f : ℕ}
    (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {S T : Store n} (hS : Reachable S) (hFuture : Future S T)
    {Bf F : Block n} {h_f : ℕ}
    (hIdStore : IdInjectiveAgainstStore Bf T)
    (chainF : Chain n Bf) {hFanc : F ≼ Bf}
    (hFstate : (stateOf chainF).F = F)
    (hFCert : FinalizedCertificate chainF F h_f hFanc)
    (hProc : ProcessedJustification S F h_f) :
    T.isViableBool F = true := by
  have hT : Reachable T := Future.reachable_of_left hS hFuture
  have hProcT : ProcessedJustification T F h_f :=
    Future.processedJustification_of_left hProc hFuture
  exact finalized_viableBool_of_processedJustification hn hNoSlash hT
    hIdStore chainF hFstate hFCert hProcT

/-- If the store frontier is already more than one height above a finalized
    block, every executable confirmed output descends from that finalized
    block. This is the non-boundary/high-frontier half of lock-in. -/
theorem getConfirmed_descends_from_finalized_of_high_frontier {f : ℕ}
    (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {S : Store n} {Bf F B : Block n} {h_f : ℕ}
    (hIdStore : IdInjectiveAgainstStore Bf S)
    (chainF : Chain n Bf) {hFanc : F ≼ Bf}
    (hFstate : (stateOf chainF).F = F)
    (hFCert : FinalizedCertificate chainF F h_f hFanc)
    (hFrontier : h_f + 1 < S.hmax)
    (hB : B ∈ S.getConfirmed) :
    F ≼ B := by
  rcases getConfirmed_entry hB with ⟨e, he, hEq, hcand⟩
  subst B
  have hHeightBool : decide (S.heightThreshold ≤ e.height) = true := by
    have hparts :
        (S.isViableBool e.block = true ∧
          Block.isAncestorOf S.confirmationRoot e.block = true) ∧
          decide (S.heightThreshold ≤ e.height) = true := by
      simpa [isConfirmedCandidateEntryBool, Bool.and_eq_true] using hcand
    exact hparts.2
  have hHigh : e.height > h_f := by
    have hThreshold : S.heightThreshold ≤ e.height :=
      of_decide_eq_true hHeightBool
    simp [heightThreshold] at hThreshold
    omega
  rcases main_safety hn (hIdStore e he) chainF hFstate hFCert
      e.chain hHigh with hSlash | hAnc
  · exact False.elim (hNoSlash hSlash)
  · exact hAnc

/-- Lock-in target-selection form, assuming the upgrade facts needed by the
    paper proof: `F ≼ Σ.J` and `h_f ≤ Σ.h_j`. The boundary branch follows the
    cascade root; the non-boundary branch follows from the height filter and
    section-2 main safety. -/
theorem getConfirmed_descends_from_finalized_of_upgrade {f : ℕ}
    (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {S : Store n} (hS : Reachable S)
    {Bf F B : Block n} {h_f : ℕ}
    (hIdStore : IdInjectiveAgainstStore Bf S)
    (chainF : Chain n Bf) {hFanc : F ≼ Bf}
    (hFstate : (stateOf chainF).F = F)
    (hFCert : FinalizedCertificate chainF F h_f hFanc)
    (hFJ : F ≼ S.J)
    (hhj : h_f ≤ S.hj)
    (hB : B ∈ S.getConfirmed) :
    F ≼ B := by
  by_cases hBoundary : S.hmax = S.hj + 1
  · have hJB : S.J ≼ B :=
      getConfirmed_descends_from_J_of_boundary hBoundary hB
    exact hFJ.trans hJB
  · have hGap : S.hj + 1 ≤ S.hmax := reachable_hj_succ_le_hmax hS
    have hFrontier : h_f + 1 < S.hmax := by
      have hStrict : S.hj + 1 < S.hmax := lt_of_le_of_ne hGap (Ne.symm hBoundary)
      omega
    exact getConfirmed_descends_from_finalized_of_high_frontier hn hNoSlash
      hIdStore chainF hFstate hFCert hFrontier hB

/-- Executable finality-update acceptance: once the three guards are available
    propositionally, `updateFinalized` really writes the state variable `F`. -/
theorem updateFinalized_sets_of_guards {S : Store n} {F' : Block n}
    (hStrict : S.F ≼ F' ∧ S.F ≠ F')
    (hBelowJ : F' ≼ S.J)
    (hViable : S.isViableBool F' = true) :
    (S.updateFinalized F').F = F' := by
  have hStrictBool : Block.isStrictAncestorOf S.F F' = true :=
    (Block.isStrictAncestorOf_eq_true_iff _ _).mpr hStrict
  have hBelowJBool : Block.isAncestorOf F' S.J = true :=
    (Block.isAncestorOf_eq_true_iff _ _).mpr hBelowJ
  have hGuard : S.shouldUpdateFinalized F' = true := by
    simp [shouldUpdateFinalized, hStrictBool, hBelowJBool, hViable]
  simp [updateFinalized, hGuard]

/-- If finality has already reached or passed `F'`, the update result still
    descends from `F'`; otherwise, the proven guards force the update to set
    `F = F'`. This is the local finality-acceptance shape used by Section 3. -/
theorem updateFinalized_descends_or_sets_of_guards {S : Store n} {F' : Block n}
    (hAlreadyOrStrict : F' ≼ S.F ∨ (S.F ≼ F' ∧ S.F ≠ F'))
    (hBelowJ : F' ≼ S.J)
    (hViable : S.isViableBool F' = true) :
    F' ≼ (S.updateFinalized F').F := by
  rcases hAlreadyOrStrict with hAlready | hStrict
  · exact hAlready.trans updateFinalized_F_monotone
  · rw [updateFinalized_sets_of_guards hStrict hBelowJ hViable]
    exact .refl _

/-- Record-based finality liveness for the exposed finality mutator. The
    Section-3 proof supplies `F' ≼ J` through upgrade and `F'` viability
    through the finalized-viable lemma; this theorem wires those facts to the
    executable `updateFinalized` guard. -/
theorem updateFinalized_accepts_finalized_record {f : ℕ}
    (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {S : Store n} {F' : Block n} {h_f : ℕ}
    (rF : FinalizationRecord F' h_f)
    (rRoot : JustificationRecord S S.J S.hj)
    (hId : rF.IdInjectiveAgainstStore S)
    (hhj : h_f ≤ S.hj)
    (hStrict : S.F ≼ F' ∧ S.F ≠ F')
    (hViable : S.isViableBool F' = true) :
    (S.updateFinalized F').F = F' := by
  have hBelowJ : F' ≼ S.J :=
    upgrade_of_current_root_record hn hNoSlash rF rRoot hId hhj
  exact updateFinalized_sets_of_guards hStrict hBelowJ hViable

/-- Record-based lock-in. From a finalization certificate for `F`, a processed
    justification record for `(F, h_f)`, and a current-root justification
    record high enough to satisfy upgrade, every executable confirmed output in
    the future store descends from `F`; the theorem also returns the two
    intermediate Section-3 conclusions. -/
theorem lockin_of_records {f : ℕ}
    (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {S T : Store n} (hS : Reachable S) (hFuture : Future S T)
    {F B : Block n} {h_f : ℕ}
    (rF : FinalizationRecord F h_f)
    (rProcessed : JustificationRecord S F h_f)
    (rRoot : JustificationRecord T T.J T.hj)
    (hId : rF.IdInjectiveAgainstStore T)
    (hhj : h_f ≤ T.hj)
    (hB : B ∈ T.getConfirmed) :
    F ≼ T.J ∧ T.isViableBool F = true ∧ F ≼ B := by
  have hFJ : F ≼ T.J :=
    upgrade_of_current_root_record hn hNoSlash rF rRoot hId hhj
  have hViable : T.isViableBool F = true :=
    future_finalized_viableBool_of_processedJustification hn hNoSlash hS hFuture
      hId rF.chain rF.final_state rF.certificate rProcessed.processed
  have hDesc : F ≼ B :=
    getConfirmed_descends_from_finalized_of_upgrade hn hNoSlash
      (Future.reachable_of_left hS hFuture)
      hId rF.chain rF.final_state rF.certificate hFJ hhj hB
  exact ⟨hFJ, hViable, hDesc⟩

end Store

end DecoupledConsensus
