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

namespace Store

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

end Store

end DecoupledConsensus
