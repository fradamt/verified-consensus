module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Store.RecoveryG1AfterCutoffPersistence

@[expose] public section

/-!
# Same-reader G1 reflection after a fixed cutoff

These are the arbitrary-read converse forms of the grade-1 cutoff transports.
Once both reads are at or after `Γ₀(q)`, a later grade-1 predicate reflects to
the earlier read for the same honest reader.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Fixed-cutoff source blocks -/

theorem block_reflects_after_cutoff
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {q : Round}
    {early later : Time}
    (hcut : S.hc.Γ_0 S.E.Δ q ≤ early)
    (hlater : early ≤ later) {B : Block V}
    (hB : B ∈ (rho.storeBeforeTime S v later).T)
    (hstamp : stampedBefore
      (rho.storeBeforeTime S v later).timestamp_block
      (S.hc.Γ_0 S.E.Δ q) B = true) :
    B ∈ (rho.storeBeforeTime S v early).T ∧
      stampedBefore
        (rho.storeBeforeTime S v early).timestamp_block
        (S.hc.Γ_0 S.E.Δ q) B = true := by
  have _hcutLater : S.hc.Γ_0 S.E.Δ q ≤ later := le_trans hcut hlater
  have hpub : PublicTime S (S.hc.Γ_0 S.E.Δ q) :=
    GradeDeliveryRun.publicTime_Gamma_0 S q
  obtain hgen | ⟨D, i, ta, hDerase, hacc, hta⟩ :=
    GradeDeliveryRun.accepted_block_of_mem_stamp_before
      S adm hv hpub hB hstamp
  · subst B
    exact Protocol.genesis_mem_and_stamp_storeBeforeTime
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v early
      (S.hc.Γ_0 S.E.Δ q)
  · have hadmit : Protocol.AdmittedBefore S rho v B
        (S.hc.Γ_0 S.E.Δ q) := ⟨D, hDerase, i, ta, hacc, hta⟩
    exact Protocol.admittedBefore_mem_and_stamp_at
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hadmit hcut

/-! ## The arbitrary-read grade-1 theorem -/

/-- A same-reader grade-1 supporter at a later read reflects to every earlier
read at or after the fixed `Γ₀(q)` cutoff. -/
theorem G1_reflects_after_cutoff
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {q : Round}
    {early later : Time} (hcut : S.hc.Γ_0 S.E.Δ q ≤ early)
    (hlater : early ≤ later) {B : Block V}
    (hG1 : Protocol.G1 S.E
      ((rho.storeBeforeTime S v later).toHealing.gradeView) S.hc q B = true) :
    Protocol.G1 S.E
      ((rho.storeBeforeTime S v early).toHealing.gradeView) S.hc q B = true := by
  by_cases hq : q = 0
  · subst q
    simp at hG1
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq
  let source := (rho.storeBeforeTime S v early).toHealing.gradeView
  let laterView := (rho.storeBeforeTime S v later).toHealing.gradeView
  have hG1' : S.E.m ≤ Protocol.direct_support S.E laterView q
      (S.hc.Γ_0 S.E.Δ q) (S.hc.Γ_0 S.E.Δ q) B := by
    simpa only [laterView, Protocol.G1, decide_eq_true_eq] using hG1
  have hsupport : S.E.m ≤ Protocol.direct_support S.E source q
      (S.hc.Γ_0 S.E.Δ q) (S.hc.Γ_0 S.E.Δ q) B := by
    simp only [Protocol.direct_support] at hG1' ⊢
    refine le_trans hG1' ?_
    apply Proofs.HealingLemmas.weightOf_filter_mono S.E
    intro x hx
    rcases hx with ⟨ht, hcov, he⟩
    obtain ⟨u, hu, hC, htu⟩ :=
      GradeDeliveryRun.vote_of_summary_support laterView q x B
        (S.hc.Γ_0 S.E.Δ q) ht hcov
    have huv : u.val_index = x := (Finset.mem_filter.mp hu).2
    have huLater : u ∈
        (rho.storeBeforeTime S v later).toHealing.sg_votes (q - 1) := by
      simpa only [laterView, Protocol.round_batch, if_neg hq,
        Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using
        (Finset.mem_filter.mp hu).1
    have hutLater : occurrenceBefore
        (Protocol.sg_resolution_time laterView.T laterView.timestamp_block
          laterView.timestamp_sg_vote u) (S.hc.Γ_0 S.E.Δ q) = true := by
      rw [← htu]
      exact ht
    have huLaterReceipt : occurrenceBefore (laterView.timestamp_sg_vote u)
        (S.hc.Γ_0 S.E.Δ q) = true :=
      GradeDeliveryRun.receipt_before_of_resolution_before hutLater
    have huLaterStamp : occurrenceBefore
        ((rho.storeBeforeTime S v later).timestamp_sg_vote u)
          (S.hc.Γ_0 S.E.Δ q) = true := by
      simpa only [laterView, Protocol.HealingStore.gradeView,
        Protocol.Store.toHealing] using huLaterReceipt
    have huEarly := projected_vote_reflects_after_cutoff S adm hv (q := q)
      hcut hlater huLater huLaterStamp
    have hucovLater : Protocol.head_covers laterView.T B u.confirmed = true := by
      rw [← hC]
      exact hcov
    obtain ⟨root, H, huRoot, hfindLater, hHLater, hBH⟩ :=
      Proofs.HealingLemmas.exists_head_of_head_covers hucovLater
    have hmaxLater : occurrenceBefore
        (occurrenceMax (laterView.timestamp_sg_vote u)
          (laterView.timestamp_block H)) (S.hc.Γ_0 S.E.Δ q) = true := by
      simpa only [Protocol.sg_resolution_time, huRoot, hfindLater] using hutLater
    have hBlockLater : stampedBefore laterView.timestamp_block
        (S.hc.Γ_0 S.E.Δ q) H = true := by
      simpa only [stampedBefore_eq_occurrenceBefore] using
        (GradeDeliveryRun.occurrenceBefore_of_max_right hmaxLater)
    have hHLaterStore : H ∈
        (rho.storeBeforeTime S v later).T := by
      simpa only [laterView, Protocol.HealingStore.gradeView,
        Protocol.Store.toHealing] using hHLater
    have hBlockLaterStore : stampedBefore
        (rho.storeBeforeTime S v later).timestamp_block
          (S.hc.Γ_0 S.E.Δ q) H = true := by
      simpa only [laterView, Protocol.HealingStore.gradeView,
        Protocol.Store.toHealing, stampedBefore_eq_occurrenceBefore] using
        hBlockLater
    have hHEarly := block_reflects_after_cutoff S adm hv (q := q)
      hcut hlater hHLaterStore hBlockLaterStore
    have hfindEarly := GradeDeliveryRun.find_target_of_source_find_and_mem
      S adm hv hfindLater hHEarly.1
    have hfindEarly' : Block.find? source.T root = some H := by
      simpa only [source, Protocol.HealingStore.gradeView,
        Protocol.Store.toHealing] using hfindEarly
    have hucovEarly : Protocol.head_covers source.T B u.confirmed = true := by
      simp only [Protocol.head_covers, huRoot]
      rw [hfindEarly']
      exact hBH
    have huEarlyReceipt : occurrenceBefore (source.timestamp_sg_vote u)
        (S.hc.Γ_0 S.E.Δ q) = true := by
      simpa only [source, Protocol.HealingStore.gradeView,
        Protocol.Store.toHealing] using huEarly.2
    have hHEarlyStamp : stampedBefore source.timestamp_block
        (S.hc.Γ_0 S.E.Δ q) H = true := by
      simpa only [source, Protocol.HealingStore.gradeView,
        Protocol.Store.toHealing, stampedBefore_eq_occurrenceBefore] using
        hHEarly.2
    have hearlyTime : occurrenceBefore
        (Protocol.sg_resolution_time source.T source.timestamp_block
          source.timestamp_sg_vote u) (S.hc.Γ_0 S.E.Δ q) = true := by
      simp only [Protocol.sg_resolution_time, huRoot]
      rw [hfindEarly']
      exact occurrenceBefore_max huEarlyReceipt
        (by simpa only [stampedBefore_eq_occurrenceBefore] using hHEarlyStamp)
    have hsourceRounds : ∀ k : Round, ∀ y ∈ source.sg_votes k, y.round = k := by
      intro k y hy
      exact GradeDeliveryRun.projected_rounds_storeBeforeTime
        S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v early k y (by
          simpa only [source, Protocol.HealingStore.gradeView,
            Protocol.Store.toHealing] using hy)
    have huEarlyBatch : u ∈ Protocol.sg_votes_by
        (Protocol.round_batch source q) x := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, huv⟩
      simpa only [source, Protocol.round_batch, if_neg hq,
        Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using huEarly.1
    have hearlySelected := GradeDeliveryRun.summary_support_or_equivocation_of_vote
      source q x B (S.hc.Γ_0 S.E.Δ q) hsourceRounds huEarlyBatch
        hearlyTime hucovEarly
    have hlaterClean : occurrenceBefore
        (Protocol.summary laterView q x).e_v
          (S.hc.Γ_0 S.E.Δ q) = false := by
      simpa only [occurrenceAtLeast, Bool.not_eq_true'] using he
    have hearlyClean : occurrenceAtLeast
        (Protocol.summary source q x).e_v
          (S.hc.Γ_0 S.E.Δ q) = true := by
      cases hbefore : occurrenceBefore
          (Protocol.summary source q x).e_v
            (S.hc.Γ_0 S.E.Δ q) with
      | false => simp [occurrenceAtLeast, hbefore]
      | true =>
          have hlaterEq := summary_equivocation_persists_after_cutoff
            S adm hv hqpos (q := q) hcut hlater
            (by simpa only [source] using hbefore)
          rw [hlaterClean] at hlaterEq
          simp at hlaterEq
    rcases hearlySelected with hearlySupport | hearlyEquiv
    · exact ⟨hearlySupport.1, hearlySupport.2, hearlyClean⟩
    · exact False.elim (by
        have hlaterEq := summary_equivocation_persists_after_cutoff
          S adm hv hqpos (q := q) hcut hlater
          (by simpa only [source] using hearlyEquiv)
        rw [hlaterClean] at hlaterEq
        simp at hlaterEq)
  simpa only [source, Protocol.G1, decide_eq_true_eq] using hsupport


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
