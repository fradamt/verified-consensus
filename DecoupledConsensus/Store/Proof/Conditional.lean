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
theorem finalized_viableBool_of_hmax_high {f : ℕ}
    (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {S : Store n}
    (hClosed : AncestorClosed S)
    (hHmax : HMaxOk S)
    {Bf F : Block n} {h_f : ℕ}
    (hIdStore : IdInjectiveAgainstStore Bf S)
    (chainF : Chain n Bf) {hFanc : F ≼ Bf}
    (hFstate : (stateOf chainF).F = F)
    (hFCert : FinalizedCertificate chainF F h_f hFanc)
    (hHigh : h_f < S.hmax) :
    S.isViableBool F = true := by
  rcases hHmax.2 with ⟨eMax, heMax, hMax⟩
  have hEntryHigh : eMax.height > h_f := by
    rw [hMax]
    exact hHigh
  have hF_eMax : F ≼ eMax.block := by
    rcases main_safety hn (hIdStore eMax heMax) chainF hFstate hFCert
        eMax.chain hEntryHigh with hSlash | hAnc
    · exact False.elim (hNoSlash hSlash)
    · exact hAnc
  have hEntryContains : Contains S eMax.block := ⟨eMax, heMax, rfl⟩
  have hFContains : Contains S F := hClosed hEntryContains hF_eMax
  have hFBool : S.containsBlockBool F = true :=
    containsBlockBool_of_contains hFContains
  have hThreshold : S.heightThreshold ≤ eMax.height := by
    simp [heightThreshold, hMax]
  exact isViableBool_of_entry_ancestor_height hFBool heMax hF_eMax hThreshold

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
  have hProcHigh : h_f < S.hmax :=
    processedJustification_height_lt_hmax hS hProc
  exact finalized_viableBool_of_hmax_high hn hNoSlash
    (reachable_ancestorClosed hS) (reachable_hmaxOk hS)
    hIdStore chainF hFstate hFCert hProcHigh

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

/-! ### No-high-justification invariant -/

private lemma ancestor_genesis_eq {B : Block n}
    (h : B ≼ Block.genesis) : B = Block.genesis := by
  cases h
  rfl

private lemma entry_justification_height_le_hj_of_below_F
    {S : Store n} (hS : Reachable S) (entry : StoreEntry n)
    (hFEntry : S.F ≼ entry.block)
    (hNotFJ : ¬ S.F ≼ entry.state.J) :
    entry.state.hj ≤ S.hj := by
  have hJEntry : entry.state.J ≼ entry.block := by
    simpa [StoreEntry.state] using chain_J_le_L entry.chain
  rcases Block.Ancestor.linear hJEntry hFEntry with hJF | hFJ'
  · by_cases hZero : entry.state.hj = 0
    · omega
    have hJHeight :
        (stateOf (entry.chain.subchain hJEntry)).h = entry.state.hj := by
      exact chain_justified_target_height_of_ne_zero entry.chain
        (by simp [StoreEntry.state])
        (by simp [StoreEntry.state])
        (by simpa [StoreEntry.state] using hJEntry)
        (by simpa [StoreEntry.state] using hZero)
    have hFJ : S.F ≼ S.J := reachable_F_ancestor_J hS
    let rRoot : JustificationRecord S S.J S.hj :=
      reachable_currentJustificationRecord hS
    let rootChain : Chain n S.J := rRoot.entry.chain.subchain rRoot.target_ancestor
    have hJSJ : entry.state.J ≼ S.J := hJF.trans hFJ
    have hJHeightRoot :
        (stateOf (rootChain.subchain hJSJ)).h = entry.state.hj := by
      have hSame :
          stateOf (rootChain.subchain hJSJ) =
            stateOf (entry.chain.subchain hJEntry) :=
        chain_unique _ _
      rw [hSame, hJHeight]
    have hJLeF :
        (stateOf (rootChain.subchain hJSJ)).h ≤
          (stateOf (rootChain.subchain hFJ)).h := by
      have hSub :
          (stateOf ((rootChain.subchain hFJ).subchain hJF)).h ≤
            (stateOf (rootChain.subchain hFJ)).h :=
        stateOf_subchain_h_le (rootChain.subchain hFJ) hJF
      have hSame :
          stateOf ((rootChain.subchain hFJ).subchain hJF) =
            stateOf (rootChain.subchain hJSJ) :=
        chain_unique _ _
      rwa [hSame] at hSub
    rcases rRoot.target_height with hRootZero | hRootHeight
    · have hF_genesis : S.F = Block.genesis := by
        have hSJ_genesis : S.J = Block.genesis := hRootZero.2
        rw [hSJ_genesis] at hFJ
        exact ancestor_genesis_eq hFJ
      have hFJ'_contradiction : S.F ≼ entry.state.J := by
        rw [hF_genesis]
        induction entry.state.J with
        | genesis => exact .refl _
        | mk _ parent _ _ ih => exact .step ih
      exact False.elim (hNotFJ hFJ'_contradiction)
    · have hFLeRoot :
          (stateOf (rootChain.subchain hFJ)).h ≤ S.hj := by
        have hSub := stateOf_subchain_h_le rootChain hFJ
        simpa [rootChain] using hSub.trans (le_of_eq hRootHeight)
      rw [← hJHeightRoot]
      exact hJLeF.trans hFLeRoot
  · exact False.elim (hNotFJ hFJ')

private lemma genesis_noHigh : NoHighJustifications (Store.genesis n) := by
  intro C h hProc
  rcases hProc with ⟨e, he, _hJ, hhj⟩
  have heq : e = StoreEntry.genesis n := by
    simpa [Store.genesis] using he
  subst e
  simp [StoreEntry.state, StoreEntry.genesis, stateOf, State.genesis] at hhj
  omega

private lemma updateFinalized_noHigh {S : Store n} {F' : Block n}
    (hNoHigh : NoHighJustifications S) :
    NoHighJustifications (S.updateFinalized F') := by
  intro C h hProc
  have hProcS : ProcessedJustification S C h := by
    simpa [ProcessedJustification, ProcessedCheckpoint,
      updateFinalized_entries_eq] using hProc
  have hle : h ≤ S.hj := hNoHigh hProcS
  simpa [updateFinalized_hj_eq] using hle

private lemma updateJustified_addEntry_noHigh
    {S : Store n} {entry : StoreEntry n}
    (hNoHigh : NoHighJustifications S)
    (hEntryHj :
      entry.state.hj ≤
        ((S.addEntry entry).updateJustified entry.state.J entry.state.hj).hj) :
    NoHighJustifications
      ((S.addEntry entry).updateJustified entry.state.J entry.state.hj) := by
  let S1 := S.addEntry entry
  let S2 := S1.updateJustified entry.state.J entry.state.hj
  intro C h hProc
  have hProcS1 : ProcessedJustification S1 C h := by
    simpa [S1, S2, ProcessedJustification, ProcessedCheckpoint,
      updateJustified_entries_eq] using hProc
  rcases hProcS1 with ⟨e, he, hJ, hhj⟩
  have heOldOrNew : e ∈ S.entries ∨ e = entry := by
    simpa [S1, addEntry] using he
  rcases heOldOrNew with heOld | heNew
  · have hProcOld : ProcessedJustification S C h := ⟨e, heOld, hJ, hhj⟩
    have hS1LeS2 : S1.hj ≤ S2.hj := updateJustified_hj_mono
    have hSLeS2 : S.hj ≤ S2.hj := by
      simpa [S1, addEntry] using hS1LeS2
    exact (hNoHigh hProcOld).trans hSLeS2
  · subst e
    rw [← hhj]
    simpa [S1, S2] using hEntryHj

private lemma added_entry_hj_le_after_updateJustified
    {S : Store n} (hS : Reachable S) (entry : StoreEntry n)
    (hFEntry : S.F ≼ entry.block)
    (hJContains :
      (S.addEntry entry).containsBlockBool entry.state.J = true) :
    entry.state.hj ≤
      ((S.addEntry entry).updateJustified entry.state.J entry.state.hj).hj := by
  let S1 := S.addEntry entry
  cases hFJBool : Block.isAncestorOf S1.F entry.state.J
  · have hNotFJ : ¬ S.F ≼ entry.state.J := by
      intro hFJ
      have hBool : Block.isAncestorOf S1.F entry.state.J = true := by
        have hS1F : S1.F = S.F := by
          simp [S1, addEntry]
        rw [hS1F]
        exact (Block.isAncestorOf_eq_true_iff _ _).mpr hFJ
      rw [hFJBool] at hBool
      cases hBool
    have hle : entry.state.hj ≤ S.hj :=
      entry_justification_height_le_hj_of_below_F hS entry hFEntry hNotFJ
    have hguard :
        S1.shouldUpdateJustified entry.state.J entry.state.hj = false := by
      simp [shouldUpdateJustified, hFJBool]
    have hUpdate :
        (S1.updateJustified entry.state.J entry.state.hj).hj = S1.hj := by
      simp [updateJustified, hguard]
    calc
      entry.state.hj ≤ S.hj := hle
      _ = S1.hj := by simp [S1, addEntry]
      _ = (S1.updateJustified entry.state.J entry.state.hj).hj := hUpdate.symm
  · exact updateJustified_candidate_height_le hJContains hFJBool

private lemma onBlock_noHigh {S S' : Store n} {B : Block n}
    (hS : Reachable S) (hNoHigh : NoHighJustifications S)
    (hstep : S.acceptBlock? B = some S') :
    NoHighJustifications S' := by
  unfold acceptBlock? at hstep
  by_cases hContains : S.containsBlockBool B
  · simp [hContains] at hstep
    cases hstep
    exact hNoHigh
  · simp [hContains] at hstep
    cases B with
    | genesis =>
        simp at hstep
    | mk bid parent newSlot votes =>
        cases hFind : S.findChain? parent with
        | none =>
            simp [hFind] at hstep
        | some parentChain =>
            by_cases hSlot : newSlot > parent.slot
            · simp [hFind, hSlot] at hstep
              let child := Block.mk bid parent newSlot votes
              by_cases hAnc : Block.isAncestorOf S.F child
              · simp [child, hAnc] at hstep
                let entry : StoreEntry n :=
                  { block := child
                    chain := Chain.extend parentChain bid newSlot votes hSlot }
                let σ' := entry.state
                let S1 := S.addEntry entry
                let S2 := S1.updateJustified σ'.J σ'.hj
                have hFEntry : S.F ≼ entry.block := by
                  have hAncProp : S.F ≼ child :=
                    (Block.isAncestorOf_eq_true_iff _ _).mp hAnc
                  simpa [entry, child]
                have hSClosed : AncestorClosed S := reachable_ancestorClosed hS
                have hParent : Contains S parent := findChain?_some_contains hFind
                have hBlock : entry.block = Block.mk bid parent newSlot votes := by
                  rfl
                have hS1Closed : AncestorClosed S1 := by
                  change AncestorClosed (S.addEntry entry)
                  exact addChild_ancestorClosed hBlock hSClosed hParent
                have hEntryMemS1 : entry ∈ S1.entries := by
                  simp [S1, addEntry]
                have hJAnc : σ'.J ≼ entry.block := by
                  simpa [σ', StoreEntry.state] using chain_J_le_L entry.chain
                have hJContains : Contains S1 σ'.J := by
                  exact hS1Closed ⟨entry, hEntryMemS1, rfl⟩ hJAnc
                have hJBool : S1.containsBlockBool σ'.J = true :=
                  containsBlockBool_of_contains hJContains
                cases hstep
                have hEntryHj :
                    entry.state.hj ≤
                      ((S.addEntry entry).updateJustified entry.state.J
                        entry.state.hj).hj := by
                  simpa [S1] using
                    added_entry_hj_le_after_updateJustified hS entry hFEntry
                    (by simpa [S1, σ', StoreEntry.state] using hJBool)
                have hNoHighRaw :
                    NoHighJustifications
                      ((S.addEntry entry).updateJustified entry.state.J
                        entry.state.hj) :=
                  updateJustified_addEntry_noHigh hNoHigh hEntryHj
                have hNoHighS2 : NoHighJustifications S2 := by
                  intro C h hProc
                  have hProcRaw :
                      ProcessedJustification
                        ((S.addEntry entry).updateJustified entry.state.J
                          entry.state.hj) C h := by
                    simpa [S1, S2, σ', StoreEntry.state] using hProc
                  have hle := hNoHighRaw hProcRaw
                  simpa [S1, S2, σ', StoreEntry.state] using hle
                exact updateFinalized_noHigh hNoHighS2
              · simp [child, hAnc] at hstep
            · simp [hFind, hSlot] at hstep

/-- Reachable stores satisfy the Section-3 no-high-justification invariant. -/
theorem reachable_noHighJustifications {S : Store n}
    (hS : Reachable S) : NoHighJustifications S := by
  induction hS with
  | genesis =>
      exact genesis_noHigh
  | onBlock hPrev hstep ih =>
      exact onBlock_noHigh hPrev ih hstep

/-- Section-3 `no-high-just`, stated against the explicit proof-side
    invariant. The nontrivial trace obligation is the invariant itself: the
    executable final store tuple stores entries and the current root, but not
    the chronological evidence that the root key was updated after every
    accepted descriptor. -/
theorem no_high_processed_justifications {S : Store n} {C : Block n} {h : ℕ}
    (hNoHigh : NoHighJustifications S) (hProc : ProcessedJustification S C h) :
    h ≤ S.hj :=
  hNoHigh hProc

/-- Record-facing wrapper for `no_high_processed_justifications`. -/
theorem no_high_justifications {S : Store n} {C : Block n} {h : ℕ}
    (hNoHigh : NoHighJustifications S) (r : JustificationRecord S C h) :
    h ≤ S.hj :=
  hNoHigh r.processed

/-- Future-facing no-high bound for a processed justification from an earlier
    store, using executable monotonicity of the store root height. -/
theorem future_no_high_processed_justification {S T : Store n}
    {C : Block n} {h : ℕ}
    (hNoHigh : NoHighJustifications S) (hFuture : Future S T)
    (hProc : ProcessedJustification S C h) :
    h ≤ T.hj :=
  (hNoHigh hProc).trans (future_hj_mono hFuture)

/-- Record-facing wrapper for the future no-high bound. -/
theorem future_no_high_justification {S T : Store n} {C : Block n} {h : ℕ}
    (hNoHigh : NoHighJustifications S) (hFuture : Future S T)
    (r : JustificationRecord S C h) :
    h ≤ T.hj :=
  future_no_high_processed_justification hNoHigh hFuture r.processed

/-- Cleaner finality-update acceptance surface. The caller supplies the
    executable store, a processed descriptor for the finalized block, and the
    strictness guard; the proof extracts the current-root record and viability
    facts internally before calling the record-level lemma. -/
theorem updateFinalized_accepts_processed_finalization {f : ℕ}
    (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {S : Store n} (hS : Reachable S)
    {F' : Block n} {h_f : ℕ}
    (rF : FinalizationRecord F' h_f)
    (hProc : ProcessedJustification S F' h_f)
    (hId : rF.IdInjectiveAgainstStore S)
    (hStrict : S.F ≼ F' ∧ S.F ≠ F') :
    (S.updateFinalized F').F = F' := by
  have rRoot : JustificationRecord S S.J S.hj :=
    reachable_currentJustificationRecord hS
  have hhj : h_f ≤ S.hj := reachable_noHighJustifications hS hProc
  have hViable : S.isViableBool F' = true :=
    finalized_viableBool_of_processedJustification hn hNoSlash hS
      hId rF.chain rF.final_state rF.certificate hProc
  exact updateFinalized_accepts_finalized_record hn hNoSlash
    rF rRoot hId hhj hStrict hViable

/-- Cleaner finality-update acceptance in monotone form. If finality is
    already at/past `F'`, the result remains at/past `F'`; otherwise the
    processed-finalization facts prove the guards needed to set `F = F'`. -/
theorem updateFinalized_descends_or_sets_processed_finalization {f : ℕ}
    (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {S : Store n} (hS : Reachable S)
    {F' : Block n} {h_f : ℕ}
    (rF : FinalizationRecord F' h_f)
    (hProc : ProcessedJustification S F' h_f)
    (hId : rF.IdInjectiveAgainstStore S)
    (hAlreadyOrStrict : F' ≼ S.F ∨ (S.F ≼ F' ∧ S.F ≠ F')) :
    F' ≼ (S.updateFinalized F').F := by
  have rRoot : JustificationRecord S S.J S.hj :=
    reachable_currentJustificationRecord hS
  have hhj : h_f ≤ S.hj := reachable_noHighJustifications hS hProc
  have hBelowJ : F' ≼ S.J :=
    upgrade_of_current_root_record hn hNoSlash rF rRoot hId hhj
  have hViable : S.isViableBool F' = true :=
    finalized_viableBool_of_processedJustification hn hNoSlash hS
      hId rF.chain rF.final_state rF.certificate hProc
  exact updateFinalized_descends_or_sets_of_guards
    hAlreadyOrStrict hBelowJ hViable

/-- Fresh-`onBlock` finality update acceptance, stated directly in terms of
    the processed block state `σ[B]`. The proof reconstructs the finalization
    certificate and height bound from the new entry's chain, then discharges
    the executable `updateFinalized` guards internally. -/
theorem onBlock_accepts_state_finalization {f : ℕ}
    (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {S S' : Store n} {B : Block n} {σB : State n}
    (hS : Reachable S)
    (hFresh : S.containsBlockBool B = false)
    (hstep : S.acceptBlock? B = some S')
    (hAcc : AcceptedBlockState S' B σB)
    (hId : IdInjectiveAgainstStore B S')
    (hStrict : S.F ≼ σB.F ∧ S.F ≠ σB.F) :
    S'.F = σB.F := by
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
  have hStateF : σB.F = σ'.F := by
    rw [hState]
  have hStrictσ : S.F ≼ σ'.F ∧ S.F ≠ σ'.F := by
    constructor
    · simpa [hStateF] using hStrict.1
    · intro hEq
      exact hStrict.2 (by simpa [hStateF] using hEq)
  have hParent : Contains S parent := findChain?_some_contains hFind
  have hSClosed : AncestorClosed S := reachable_ancestorClosed hS
  have hBlock : entry.block = Block.mk bid parent newSlot votes := by
    rfl
  have hS1Closed : AncestorClosed S1 := by
    change AncestorClosed (S.addEntry entry)
    exact addChild_ancestorClosed hBlock hSClosed hParent
  have hS2Closed : AncestorClosed S2 :=
    updateJustified_ancestorClosed hS1Closed
  have hEntryMemS1 : entry ∈ S1.entries := by
    simp [S1, addEntry]
  have hEntryMemS2 : entry ∈ S2.entries := by
    simpa [S2, updateJustified_entries_eq] using hEntryMemS1
  obtain ⟨h_f, hFanc, hFCert, hhf⟩ :=
    FinalityEvidence.chain_finalizedCertificate_le_hj entry.chain
  let rF : FinalizationRecord σ'.F h_f :=
    { tip := entry.block
      chain := entry.chain
      target_ancestor := by
        simpa [σ', StoreEntry.state] using hFanc
      final_state := by
        simp [σ', StoreEntry.state]
      certificate := by
        simpa [σ', StoreEntry.state] using hFCert }
  have hIdS2 : rF.IdInjectiveAgainstStore S2 := by
    intro e he
    have heFinal : e ∈ (S2.updateFinalized σ'.F).entries := by
      simpa [updateFinalized_entries_eq] using he
    change Block.IdInjectiveOnAncestors entry.block e.block
    intro A C hA hC hEq
    exact (hId e heFinal)
      (by simpa [entry, child] using hA)
      (by simpa [entry, child] using hC)
      hEq
  have hJAnc : σ'.J ≼ entry.block := by
    simpa [σ', StoreEntry.state] using chain_J_le_L entry.chain
  have hJContains : Contains S1 σ'.J :=
    hS1Closed ⟨entry, hEntryMemS1, rfl⟩ hJAnc
  have hJBool : S1.containsBlockBool σ'.J = true :=
    containsBlockBool_of_contains hJContains
  have hS1FBelowJ : Block.isAncestorOf S1.F σ'.J = true := by
    have hFJ : σ'.F ≼ σ'.J := by
      simpa [σ', StoreEntry.state] using chain_F_le_J entry.chain
    have hProp : S1.F ≼ σ'.J := by
      have hS1F : S1.F = S.F := by
        simp [S1, addEntry]
      rw [hS1F]
      exact hStrictσ.1.trans hFJ
    exact (Block.isAncestorOf_eq_true_iff _ _).mpr hProp
  have hCandidateHjLe : σ'.hj ≤ S2.hj :=
    updateJustified_candidate_height_le
      (S := S1) (J' := σ'.J) (h' := σ'.hj)
      hJBool hS1FBelowJ
  have hhfσ : h_f ≤ σ'.hj := by
    simpa [σ', StoreEntry.state] using hhf
  have hhfS2 : h_f ≤ S2.hj := hhfσ.trans hCandidateHjLe
  have hCurS1 : CurrentProcessedJustification S1 :=
    addEntry_currentProcessedJustification
      (reachable_currentProcessedJustification hS)
  have hNew : ProcessedJustification S1 σ'.J σ'.hj := by
    simpa [S1, σ'] using
      addEntry_newProcessedJustification (S := S) (e := entry)
  have hCurS2 : CurrentProcessedJustification S2 :=
    updateJustified_currentProcessedJustification hCurS1 hNew
  let rRoot : JustificationRecord S2 S2.J S2.hj := hCurS2.toRecord
  have hBelowJ : σ'.F ≼ S2.J :=
    upgrade_of_current_root_record hn hNoSlash rF rRoot hIdS2 hhfS2
  have hHmaxS2 : HMaxOk S2 :=
    updateJustified_hmaxOk (addEntry_hmaxOk (reachable_hmaxOk hS))
  have hHigh : h_f < S2.hmax := by
    have hlt : σ'.hj < entry.height := by
      simpa [σ', StoreEntry.state, StoreEntry.height] using
        chain_hj_lt_h entry.chain
    have hEntryLe : entry.height ≤ S2.hmax :=
      hHmaxS2.1 entry hEntryMemS2
    omega
  have hViable : S2.isViableBool σ'.F = true :=
    finalized_viableBool_of_hmax_high hn hNoSlash
      hS2Closed hHmaxS2 hIdS2 rF.chain rF.final_state
      rF.certificate hHigh
  have hS2F_eq : S2.F = S.F := by
    simp [S2, S1, addEntry, updateJustified_F_eq]
  have hStrictS2 : S2.F ≼ σ'.F ∧ S2.F ≠ σ'.F := by
    constructor
    · simpa [hS2F_eq] using hStrictσ.1
    · intro hEq
      exact hStrictσ.2 (by simpa [hS2F_eq] using hEq)
  have hSet : (S2.updateFinalized σ'.F).F = σ'.F :=
    updateFinalized_sets_of_guards hStrictS2 hBelowJ hViable
  simpa [hStateF] using hSet

/-- Monotone fresh-`onBlock` form of finality update acceptance. -/
theorem onBlock_descends_or_accepts_state_finalization {f : ℕ}
    (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {S S' : Store n} {B : Block n} {σB : State n}
    (hS : Reachable S)
    (hFresh : S.containsBlockBool B = false)
    (hstep : S.acceptBlock? B = some S')
    (hAcc : AcceptedBlockState S' B σB)
    (hId : IdInjectiveAgainstStore B S')
    (hAlreadyOrStrict : σB.F ≼ S.F ∨ (S.F ≼ σB.F ∧ S.F ≠ σB.F)) :
    σB.F ≼ S'.F := by
  rcases hAlreadyOrStrict with hAlready | hStrict
  · exact hAlready.trans (onBlock_F_monotone hstep)
  · have hSet : S'.F = σB.F :=
      onBlock_accepts_state_finalization hn hNoSlash hS hFresh hstep hAcc hId hStrict
    rw [hSet]
    exact .refl _

/-- Upgrade with a clean processed-descriptor surface. The proof-side
    `JustificationRecord` for the future store's root is extracted internally
    from executable reachability. -/
theorem upgrade_of_processed {f : ℕ}
    (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {S T : Store n} (hS : Reachable S) (hFuture : Future S T)
    {F : Block n} {h_f : ℕ}
    (rF : FinalizationRecord F h_f)
    (hProc : ProcessedJustification S F h_f)
    (hId : rF.IdInjectiveAgainstStore T) :
    F ≼ T.J := by
  have hT : Reachable T := Future.reachable_of_left hS hFuture
  have rRoot : JustificationRecord T T.J T.hj :=
    reachable_currentJustificationRecord hT
  have hhj : h_f ≤ T.hj :=
    future_no_high_processed_justification
      (reachable_noHighJustifications hS) hFuture hProc
  exact upgrade_of_current_root_record hn hNoSlash rF rRoot hId hhj

/-- Lock-in with a clean processed-descriptor surface. The record-level theorem
    remains the proof engine, but callers no longer provide justification
    records for the processed descriptor or current root. -/
theorem lockin_of_processed {f : ℕ}
    (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {S T : Store n} (hS : Reachable S) (hFuture : Future S T)
    {F B : Block n} {h_f : ℕ}
    (rF : FinalizationRecord F h_f)
    (hProc : ProcessedJustification S F h_f)
    (hId : rF.IdInjectiveAgainstStore T)
    (hB : B ∈ T.getConfirmed) :
    F ≼ T.J ∧ T.isViableBool F = true ∧ F ≼ B := by
  have hT : Reachable T := Future.reachable_of_left hS hFuture
  have rProcessed : JustificationRecord S F h_f := hProc.toRecord
  have rRoot : JustificationRecord T T.J T.hj :=
    reachable_currentJustificationRecord hT
  have hhj : h_f ≤ T.hj :=
    future_no_high_processed_justification
      (reachable_noHighJustifications hS) hFuture hProc
  exact lockin_of_records hn hNoSlash hS hFuture
    rF rProcessed rRoot hId hhj hB

/-! ### Order-independent views of executable stores -/

/-- Internal extensional equality for all store components that affect
    `viableTree` and `getConfirmed`. This is useful as a proof helper, but it
    is not the public replay-order theorem: raw stores can legitimately differ
    outside the finality subtree. -/
structure OrderEquivalent (S T : Store n) : Prop where
  entries_iff : ∀ e : StoreEntry n, e ∈ S.entries ↔ e ∈ T.entries
  F_eq : S.F = T.F
  J_eq : S.J = T.J
  hj_eq : S.hj = T.hj
  hmax_eq : S.hmax = T.hmax

lemma OrderEquivalent.symm {S T : Store n}
    (hEq : OrderEquivalent S T) : OrderEquivalent T S where
  entries_iff := fun e => (hEq.entries_iff e).symm
  F_eq := hEq.F_eq.symm
  J_eq := hEq.J_eq.symm
  hj_eq := hEq.hj_eq.symm
  hmax_eq := hEq.hmax_eq.symm

/-- Processed justification descriptors transfer across order-equivalent
    stores because they depend only on membership in the accepted entry set,
    not list order. -/
lemma ProcessedJustification.transfer_orderEquivalent {S T : Store n}
    {C : Block n} {h : ℕ} (hEq : OrderEquivalent S T)
    (hProc : ProcessedJustification S C h) :
    ProcessedJustification T C h := by
  rcases hProc with ⟨e, he, hJ, hhj⟩
  exact ⟨e, (hEq.entries_iff e).mp he, hJ, hhj⟩

/-- A justification record transfers across order-equivalent stores because it
    depends only on membership in the accepted entry set, not list order. -/
def JustificationRecord.transfer_orderEquivalent {S T : Store n}
    {C : Block n} {h : ℕ} (hEq : OrderEquivalent S T)
    (r : JustificationRecord S C h) : JustificationRecord T C h :=
  { r with mem := (hEq.entries_iff r.entry).mp r.mem }

/-- The no-high invariant is itself order-independent under the extensional
    equality used for stores. -/
theorem orderindep_noHighJustifications {S T : Store n}
    (hEq : OrderEquivalent S T)
    (hNoHigh : NoHighJustifications S) :
    NoHighJustifications T := by
  intro C h hProc
  have hProcS : ProcessedJustification S C h :=
    ProcessedJustification.transfer_orderEquivalent hEq.symm hProc
  have hle : h ≤ S.hj := hNoHigh hProcS
  simpa [hEq.hj_eq] using hle

private lemma heightThreshold_eq_of_orderEquivalent {S T : Store n}
    (hEq : OrderEquivalent S T) :
    S.heightThreshold = T.heightThreshold := by
  simp [heightThreshold, hEq.hmax_eq]

private lemma confirmationRoot_eq_of_orderEquivalent {S T : Store n}
    (hEq : OrderEquivalent S T) :
    S.confirmationRoot = T.confirmationRoot := by
  simp [confirmationRoot, hEq.hmax_eq, hEq.hj_eq, hEq.J_eq, hEq.F_eq]

private lemma getConfirmed_mem_of_orderEquivalent {S T : Store n} {B : Block n}
    (hEq : OrderEquivalent S T) (hB : B ∈ S.getConfirmed) :
    B ∈ T.getConfirmed := by
  rcases getConfirmed_entry hB with ⟨e, heS, hBlock, hcandS⟩
  subst B
  have heT : e ∈ T.entries := (hEq.entries_iff e).mp heS
  have hparts :
      (S.isViableBool e.block = true ∧
        Block.isAncestorOf S.confirmationRoot e.block = true) ∧
        decide (S.heightThreshold ≤ e.height) = true := by
    simpa [isConfirmedCandidateEntryBool, Bool.and_eq_true] using hcandS
  have hViableT : T.isViableBool e.block = true := by
    rcases highDescendant_of_isViableBool hparts.1.1 with
      ⟨w, hwS, hwHeightS, hAnc⟩
    have hwT : w ∈ T.entries := (hEq.entries_iff w).mp hwS
    have hContainsT : T.containsBlockBool e.block = true :=
      containsBlockBool_of_entry_mem heT
    have hHeightT : T.heightThreshold ≤ w.height := by
      simpa [← heightThreshold_eq_of_orderEquivalent hEq] using hwHeightS
    exact isViableBool_of_entry_ancestor_height hContainsT hwT hAnc hHeightT
  have hRootT : Block.isAncestorOf T.confirmationRoot e.block = true := by
    simpa [← confirmationRoot_eq_of_orderEquivalent hEq] using hparts.1.2
  have hHeightT : decide (T.heightThreshold ≤ e.height) = true := by
    simpa [← heightThreshold_eq_of_orderEquivalent hEq] using hparts.2
  have hcandT : T.isConfirmedCandidateEntryBool e = true := by
    simp [isConfirmedCandidateEntryBool, hViableT, hRootT, hHeightT]
  exact mem_getConfirmed_of_entry_candidate heT hcandT

/-- Order-independence for executable confirmed-output sets. The result is
    stated extensionally because `getConfirmed` is represented as a finite list
    of all possible outputs, and list order follows the store-entry order. -/
theorem orderindep_getConfirmed {S T : Store n} {B : Block n}
    (hEq : OrderEquivalent S T) :
    B ∈ S.getConfirmed ↔ B ∈ T.getConfirmed := by
  constructor
  · exact getConfirmed_mem_of_orderEquivalent hEq
  · exact getConfirmed_mem_of_orderEquivalent hEq.symm

private lemma viableTree_mem_of_orderEquivalent {S T : Store n} {B : Block n}
    (hEq : OrderEquivalent S T) (hB : B ∈ S.viableTree) :
    B ∈ T.viableTree := by
  rcases (by
    simpa [viableTree] using hB :
      ∃ e ∈ S.entries, S.isViableBool e.block = true ∧ e.block = B) with
    ⟨e, heS, hViableS, hBlock⟩
  subst B
  have heT : e ∈ T.entries := (hEq.entries_iff e).mp heS
  have hViableT : T.isViableBool e.block = true := by
    rcases highDescendant_of_isViableBool hViableS with
      ⟨w, hwS, hwHeightS, hAnc⟩
    have hwT : w ∈ T.entries := (hEq.entries_iff w).mp hwS
    have hContainsT : T.containsBlockBool e.block = true :=
      containsBlockBool_of_entry_mem heT
    have hHeightT : T.heightThreshold ≤ w.height := by
      simpa [← heightThreshold_eq_of_orderEquivalent hEq] using hwHeightS
    exact isViableBool_of_entry_ancestor_height hContainsT hwT hAnc hHeightT
  simpa [viableTree] using
    (show ∃ x ∈ T.entries, T.isViableBool x.block = true ∧ x.block = e.block from
      ⟨e, heT, hViableT, rfl⟩)

/-- Order-independence for viable-tree membership, again stated extensionally
    over the executable finite-list representation. -/
theorem orderindep_viableTree {S T : Store n} {B : Block n}
    (hEq : OrderEquivalent S T) :
    B ∈ S.viableTree ↔ B ∈ T.viableTree := by
  constructor
  · exact viableTree_mem_of_orderEquivalent hEq
  · exact viableTree_mem_of_orderEquivalent hEq.symm

/-! ### Live-view output invariance -/

lemma LiveEquivalent.symm {S T : Store n}
    (hEq : LiveEquivalent S T) : LiveEquivalent T S where
  F_eq := hEq.F_eq.symm
  J_eq := hEq.J_eq.symm
  hj_eq := hEq.hj_eq.symm
  hmax_eq := hEq.hmax_eq.symm
  live_entries_forward := hEq.live_entries_backward
  live_entries_backward := hEq.live_entries_forward

private lemma heightThreshold_eq_of_liveEquivalent {S T : Store n}
    (hEq : LiveEquivalent S T) :
    S.heightThreshold = T.heightThreshold := by
  simp [heightThreshold, hEq.hmax_eq]

private lemma confirmationRoot_eq_of_liveEquivalent {S T : Store n}
    (hEq : LiveEquivalent S T) :
    S.confirmationRoot = T.confirmationRoot := by
  simp [confirmationRoot, hEq.hmax_eq, hEq.hj_eq, hEq.J_eq, hEq.F_eq]

private lemma getConfirmed_mem_of_liveEquivalent {S T : Store n} {B : Block n}
    (hS : Reachable S) (hEq : LiveEquivalent S T)
    (hB : B ∈ S.getConfirmed) :
    B ∈ T.getConfirmed := by
  rcases getConfirmed_entry hB with ⟨e, heS, hBlock, hcandS⟩
  subst B
  have hLive : S.F ≼ e.block :=
    future_getConfirmed_descends_from_F hS (Future.refl S)
      (mem_getConfirmed_of_entry_candidate heS hcandS)
  rcases hEq.live_entries_forward e heS hLive with
    ⟨eT, heT, hBlockT, hHeightT_eq⟩
  have hparts :
      (S.isViableBool e.block = true ∧
        Block.isAncestorOf S.confirmationRoot e.block = true) ∧
        decide (S.heightThreshold ≤ e.height) = true := by
    simpa [isConfirmedCandidateEntryBool, Bool.and_eq_true] using hcandS
  have hViableT : T.isViableBool eT.block = true := by
    rcases highDescendant_of_isViableBool hparts.1.1 with
      ⟨w, hwS, hwHeightS, hAnc⟩
    have hLiveW : S.F ≼ w.block := Block.Ancestor.trans hLive hAnc
    rcases hEq.live_entries_forward w hwS hLiveW with
      ⟨wT, hwT, hBlockWT, hHeightWT_eq⟩
    have hContainsT : T.containsBlockBool eT.block = true :=
      containsBlockBool_of_entry_mem heT
    have hAncT : eT.block ≼ wT.block := by
      simpa [hBlockT, hBlockWT] using hAnc
    have hHeightT : T.heightThreshold ≤ wT.height := by
      rw [hHeightWT_eq]
      simpa [← heightThreshold_eq_of_liveEquivalent hEq] using hwHeightS
    exact isViableBool_of_entry_ancestor_height hContainsT hwT hAncT hHeightT
  have hRootT : Block.isAncestorOf T.confirmationRoot eT.block = true := by
    have hRootS : Block.isAncestorOf S.confirmationRoot e.block = true := hparts.1.2
    simpa [← confirmationRoot_eq_of_liveEquivalent hEq, hBlockT] using hRootS
  have hHeightT : decide (T.heightThreshold ≤ eT.height) = true := by
    have hHeightS : S.heightThreshold ≤ e.height := of_decide_eq_true hparts.2
    apply decide_eq_true
    rw [hHeightT_eq]
    simpa [← heightThreshold_eq_of_liveEquivalent hEq] using hHeightS
  have hcandT : T.isConfirmedCandidateEntryBool eT = true := by
    simp [isConfirmedCandidateEntryBool, hViableT, hRootT, hHeightT]
  have hmemT := mem_getConfirmed_of_entry_candidate heT hcandT
  simpa [hBlockT] using hmemT

/-- Reachable stores with the same finalized live view have the same
    executable confirmed-output set. This is the output-level order
    independence principle used when full accepted-entry equality is false. -/
theorem liveEquivalent_getConfirmed {S T : Store n} {B : Block n}
    (hS : Reachable S) (hT : Reachable T)
    (hEq : LiveEquivalent S T) :
    B ∈ S.getConfirmed ↔ B ∈ T.getConfirmed := by
  constructor
  · exact getConfirmed_mem_of_liveEquivalent hS hEq
  · exact getConfirmed_mem_of_liveEquivalent hT hEq.symm

end Store

end DecoupledConsensus
