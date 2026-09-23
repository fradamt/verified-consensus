module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Store.RecoveryG1CutoffFreeze

@[expose] public section

/-!
# Same-reader G1 persistence after a fixed cutoff

This is the arbitrary-read form of `G1_persists_from_opening`. The source
read need not be the round opening: once the source read is at or after
`Γ₀(q)`, every vote or block which is used with the grade-1 cutoff was
accepted before that cutoff and therefore persists to every later read.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The two object transports at an arbitrary source read -/

theorem projected_vote_persists_after_cutoff
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {q : Round}
    {early later : Time}
    (hcut : S.hc.Γ_0 S.E.Δ q ≤ early)
    (hlater : early ≤ later) {k : Round}
    {u : Protocol.SGVote V}
    (hu : u ∈ (rho.storeBeforeTime S v early).toHealing.sg_votes k)
    (hstamp : occurrenceBefore
      ((rho.storeBeforeTime S v early).timestamp_sg_vote u)
        (S.hc.Γ_0 S.E.Δ q) = true) :
    u ∈ (rho.storeBeforeTime S v later).toHealing.sg_votes k ∧
      occurrenceBefore
        ((rho.storeBeforeTime S v later).timestamp_sg_vote u)
          (S.hc.Γ_0 S.E.Δ q) = true := by
  have hpub : PublicTime S (S.hc.Γ_0 S.E.Δ q) :=
    GradeDeliveryRun.publicTime_Gamma_0 S q
  obtain ⟨a, i, ta, hau, hacc, hta⟩ :=
    GradeDeliveryRun.accepted_attestation_of_projected_stamp_before
      S adm hv hpub hu hstamp
  subst u
  have haround : a.round = k := by
    have hround := GradeDeliveryRun.projected_rounds_storeBeforeTime
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v early k
      (Protocol.sgVote a.erase) hu
    simpa only [Protocol.sgVote] using hround
  obtain ⟨hhandle, -, hpost⟩ := hacc
  obtain ⟨-, e, he, -, htime⟩ := hhandle
  have heEarly : e.time < early := by
    rw [htime]
    exact lt_of_lt_of_le hta hcut
  have heLater : e.time < later := lt_of_lt_of_le heEarly hlater
  have hown : a ∈ (rho.stateBefore S (i + 1) v).st.sg_rows a.round := by
    simpa only [NamedReceipt.processed, decide_eq_true_eq] using hpost
  have hpool := NamedAdmission.pool_view_mem (rho.stateBefore S (i + 1) v).st
    (Proofs.NamedRuntime.stateBefore_invariants S rho (i + 1) v).1.1.1.2.2.2.1 _ hown
  have hpostProj : Protocol.sgVote a.erase ∈
      (rho.stateBefore S (i + 1) v).st.toHealing.sg_votes a.round := by
    change Protocol.sgVote a.erase ∈
      ((rho.stateBefore S (i + 1) v).st.sg_pool a.round).image
        Protocol.sgVote
    exact Finset.mem_image_of_mem Protocol.sgVote hpool
  have hlaterMem := Protocol.sgVote_mem_stateBeforeTime_of_post
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed he heLater hpostProj
  have hsourceStamp :=
    GradeDeliveryRun.timestamp_sg_vote_stateBeforeTime_of_post
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed he heEarly hpostProj
  have hlaterStamp :=
    GradeDeliveryRun.timestamp_sg_vote_stateBeforeTime_of_post
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed he heLater hpostProj
  refine ⟨?_, ?_⟩
  · simpa only [Run.storeBeforeTime, haround] using hlaterMem
  · rw [hlaterStamp]
    rw [hsourceStamp] at hstamp
    exact hstamp

theorem projected_vote_reflects_after_cutoff
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {q : Round}
    {early later : Time}
    (hcut : S.hc.Γ_0 S.E.Δ q ≤ early)
    (hlater : early ≤ later) {k : Round}
    {u : Protocol.SGVote V}
    (hu : u ∈ (rho.storeBeforeTime S v later).toHealing.sg_votes k)
    (hstamp : occurrenceBefore
      ((rho.storeBeforeTime S v later).timestamp_sg_vote u)
        (S.hc.Γ_0 S.E.Δ q) = true) :
    u ∈ (rho.storeBeforeTime S v early).toHealing.sg_votes k ∧
      occurrenceBefore
        ((rho.storeBeforeTime S v early).timestamp_sg_vote u)
          (S.hc.Γ_0 S.E.Δ q) = true := by
  have hpub : PublicTime S (S.hc.Γ_0 S.E.Δ q) :=
    GradeDeliveryRun.publicTime_Gamma_0 S q
  obtain ⟨a, i, ta, hau, hacc, hta⟩ :=
    GradeDeliveryRun.accepted_attestation_of_projected_stamp_before
      S adm hv hpub hu hstamp
  subst u
  have haround : a.round = k := by
    have hround := GradeDeliveryRun.projected_rounds_storeBeforeTime
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v later k
      (Protocol.sgVote a.erase) hu
    simpa only [Protocol.sgVote] using hround
  obtain ⟨hhandle, -, hpost⟩ := hacc
  obtain ⟨-, e, he, -, htime⟩ := hhandle
  have heEarly : e.time < early := by
    rw [htime]
    exact lt_of_lt_of_le hta hcut
  have heLater : e.time < later := lt_of_lt_of_le heEarly hlater
  have hown : a ∈ (rho.stateBefore S (i + 1) v).st.sg_rows a.round := by
    simpa only [NamedReceipt.processed, decide_eq_true_eq] using hpost
  have hpool := NamedAdmission.pool_view_mem (rho.stateBefore S (i + 1) v).st
    (Proofs.NamedRuntime.stateBefore_invariants S rho (i + 1) v).1.1.1.2.2.2.1 _ hown
  have hpostProj : Protocol.sgVote a.erase ∈
      (rho.stateBefore S (i + 1) v).st.toHealing.sg_votes a.round := by
    change Protocol.sgVote a.erase ∈
      ((rho.stateBefore S (i + 1) v).st.sg_pool a.round).image
        Protocol.sgVote
    exact Finset.mem_image_of_mem Protocol.sgVote hpool
  have hsourceMem := Protocol.sgVote_mem_stateBeforeTime_of_post
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed he heEarly hpostProj
  have hsourceStamp :=
    GradeDeliveryRun.timestamp_sg_vote_stateBeforeTime_of_post
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed he heEarly hpostProj
  have hlaterStamp :=
    GradeDeliveryRun.timestamp_sg_vote_stateBeforeTime_of_post
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed he heLater hpostProj
  refine ⟨?_, ?_⟩
  · simpa only [Run.storeBeforeTime, haround] using hsourceMem
  · rw [hsourceStamp]
    rw [hlaterStamp] at hstamp
    exact hstamp

theorem block_persists_after_cutoff
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {q : Round}
    {early later : Time}
    (hcut : S.hc.Γ_0 S.E.Δ q ≤ early)
    (hlater : early ≤ later) {B : Block V}
    (hB : B ∈ (rho.storeBeforeTime S v early).T)
    (hstamp : stampedBefore
      (rho.storeBeforeTime S v early).timestamp_block
        (S.hc.Γ_0 S.E.Δ q) B = true) :
    B ∈ (rho.storeBeforeTime S v later).T ∧
      stampedBefore
        (rho.storeBeforeTime S v later).timestamp_block
          (S.hc.Γ_0 S.E.Δ q) B = true := by
  have hpub : PublicTime S (S.hc.Γ_0 S.E.Δ q) :=
    GradeDeliveryRun.publicTime_Gamma_0 S q
  obtain hgen | ⟨D, i, ta, hDerase, hacc, hta⟩ :=
    GradeDeliveryRun.accepted_block_of_mem_stamp_before
      S adm hv hpub hB hstamp
  · subst B
    exact Protocol.genesis_mem_and_stamp_storeBeforeTime
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v later (S.hc.Γ_0 S.E.Δ q)
  · have hadmit : Protocol.AdmittedBefore S rho v B
      (S.hc.Γ_0 S.E.Δ q) :=
      ⟨D, hDerase, i, ta, hacc, hta⟩
    exact Protocol.admittedBefore_mem_and_stamp_at
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hadmit
      (le_trans hcut hlater)

/-! ## Equivocation transport -/

theorem summary_equivocation_persists_after_cutoff
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {q : Round} (hq : 0 < q)
    {early later : Time}
    (hcut : S.hc.Γ_0 S.E.Δ q ≤ early)
    (hlater : early ≤ later) {x : V}
    (hearly : occurrenceBefore
      (Protocol.summary
        (rho.storeBeforeTime S v early).toHealing.gradeView q x).e_v
          (S.hc.Γ_0 S.E.Δ q) = true) :
    occurrenceBefore
      (Protocol.summary
        (rho.storeBeforeTime S v later).toHealing.gradeView q x).e_v
          (S.hc.Γ_0 S.E.Δ q) = true := by
  let source := (rho.storeBeforeTime S v early).toHealing.gradeView
  let laterView := (rho.storeBeforeTime S v later).toHealing.gradeView
  let sourceBatch := Protocol.sg_votes_by
    (Protocol.round_batch source q) x
  have hearly' : occurrenceBefore
      (Protocol.equivocation_instant source.timestamp_sg_vote sourceBatch)
        (S.hc.Γ_0 S.E.Δ q) = true := by
    simpa only [source, sourceBatch, Proofs.Optimistic.summary_e_v_eq] using hearly
  obtain ⟨u, hu, c, hc, hne, hut, hct⟩ :=
    GradeDeliveryRun.witnesses_of_equivocation_before
      source.timestamp_sg_vote hearly'
  have huData := Finset.mem_filter.mp hu
  have hcData := Finset.mem_filter.mp hc
  have huSource : u ∈
      (rho.storeBeforeTime S v early).toHealing.sg_votes (q - 1) := by
    simpa only [sourceBatch, source, Protocol.round_batch,
      if_neg (Nat.ne_of_gt hq), Protocol.HealingStore.gradeView,
      Protocol.Store.toHealing] using huData.1
  have hcSource : c ∈
      (rho.storeBeforeTime S v early).toHealing.sg_votes (q - 1) := by
    simpa only [sourceBatch, source, Protocol.round_batch,
      if_neg (Nat.ne_of_gt hq), Protocol.HealingStore.gradeView,
      Protocol.Store.toHealing] using hcData.1
  have huPersist := projected_vote_persists_after_cutoff S adm hv (q := q)
    hcut hlater
    huSource (by simpa only [source, Protocol.HealingStore.gradeView,
      Protocol.Store.toHealing] using hut)
  have hcPersist := projected_vote_persists_after_cutoff S adm hv (q := q)
    hcut hlater
    hcSource (by simpa only [source, Protocol.HealingStore.gradeView,
      Protocol.Store.toHealing] using hct)
  let laterBatch := Protocol.sg_votes_by
    (Protocol.round_batch laterView q) x
  have huLater : u ∈ laterBatch := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, huData.2⟩
    simpa only [laterBatch, laterView, Protocol.round_batch,
      if_neg (Nat.ne_of_gt hq), Protocol.HealingStore.gradeView,
      Protocol.Store.toHealing] using huPersist.1
  have hcLater : c ∈ laterBatch := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, hcData.2⟩
    simpa only [laterBatch, laterView, Protocol.round_batch,
      if_neg (Nat.ne_of_gt hq), Protocol.HealingStore.gradeView,
      Protocol.Store.toHealing] using hcPersist.1
  have hfibre : ∀ y ∈ laterBatch, y.val_index = x ∧ y.round = q - 1 := by
    intro y hy
    have hyData := Finset.mem_filter.mp hy
    refine ⟨hyData.2, ?_⟩
    have hyRaw : y ∈
        (rho.storeBeforeTime S v later).toHealing.sg_votes (q - 1) := by
      simpa only [laterBatch, laterView, Protocol.round_batch,
        if_neg (Nat.ne_of_gt hq), Protocol.HealingStore.gradeView,
        Protocol.Store.toHealing] using hyData.1
    exact GradeDeliveryRun.projected_rounds_storeBeforeTime
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v later (q - 1) y hyRaw
  have heq := GradeDeliveryRun.equivocation_before_of_two
    laterView.timestamp_sg_vote hfibre huLater hcLater hne
    (by simpa only [laterView, Protocol.HealingStore.gradeView,
      Protocol.Store.toHealing] using huPersist.2)
    (by simpa only [laterView, Protocol.HealingStore.gradeView,
      Protocol.Store.toHealing] using hcPersist.2)
  simpa only [laterView, laterBatch, Proofs.Optimistic.summary_e_v_eq] using heq

theorem summary_equivocation_reflects_after_cutoff
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {q : Round} (hq : 0 < q)
    {early later : Time}
    (hcut : S.hc.Γ_0 S.E.Δ q ≤ early)
    (hlater : early ≤ later) {x : V}
    (hlaterEq : occurrenceBefore
      (Protocol.summary
        (rho.storeBeforeTime S v later).toHealing.gradeView q x).e_v
          (S.hc.Γ_0 S.E.Δ q) = true) :
    occurrenceBefore
      (Protocol.summary
        (rho.storeBeforeTime S v early).toHealing.gradeView q x).e_v
          (S.hc.Γ_0 S.E.Δ q) = true := by
  let source := (rho.storeBeforeTime S v early).toHealing.gradeView
  let laterView := (rho.storeBeforeTime S v later).toHealing.gradeView
  let laterBatch := Protocol.sg_votes_by
    (Protocol.round_batch laterView q) x
  have hlater' : occurrenceBefore
      (Protocol.equivocation_instant laterView.timestamp_sg_vote laterBatch)
        (S.hc.Γ_0 S.E.Δ q) = true := by
    simpa only [laterView, laterBatch, Proofs.Optimistic.summary_e_v_eq] using hlaterEq
  obtain ⟨u, hu, c, hc, hne, hut, hct⟩ :=
    GradeDeliveryRun.witnesses_of_equivocation_before
      laterView.timestamp_sg_vote hlater'
  have huData := Finset.mem_filter.mp hu
  have hcData := Finset.mem_filter.mp hc
  have huLater : u ∈
      (rho.storeBeforeTime S v later).toHealing.sg_votes (q - 1) := by
    simpa only [laterBatch, laterView, Protocol.round_batch,
      if_neg (Nat.ne_of_gt hq), Protocol.HealingStore.gradeView,
      Protocol.Store.toHealing] using huData.1
  have hcLater : c ∈
      (rho.storeBeforeTime S v later).toHealing.sg_votes (q - 1) := by
    simpa only [laterBatch, laterView, Protocol.round_batch,
      if_neg (Nat.ne_of_gt hq), Protocol.HealingStore.gradeView,
      Protocol.Store.toHealing] using hcData.1
  have huSource := projected_vote_reflects_after_cutoff S adm hv (q := q)
    hcut hlater
    huLater (by simpa only [laterView, Protocol.HealingStore.gradeView,
      Protocol.Store.toHealing] using hut)
  have hcSource := projected_vote_reflects_after_cutoff S adm hv (q := q)
    hcut hlater
    hcLater (by simpa only [laterView, Protocol.HealingStore.gradeView,
      Protocol.Store.toHealing] using hct)
  let sourceBatch := Protocol.sg_votes_by
    (Protocol.round_batch source q) x
  have huOpen : u ∈ sourceBatch := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, huData.2⟩
    simpa only [sourceBatch, source, Protocol.round_batch,
      if_neg (Nat.ne_of_gt hq), Protocol.HealingStore.gradeView,
      Protocol.Store.toHealing] using huSource.1
  have hcOpen : c ∈ sourceBatch := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, hcData.2⟩
    simpa only [sourceBatch, source, Protocol.round_batch,
      if_neg (Nat.ne_of_gt hq), Protocol.HealingStore.gradeView,
      Protocol.Store.toHealing] using hcSource.1
  have hfibre : ∀ y ∈ sourceBatch, y.val_index = x ∧ y.round = q - 1 := by
    intro y hy
    have hyData := Finset.mem_filter.mp hy
    refine ⟨hyData.2, ?_⟩
    have hyRaw : y ∈
        (rho.storeBeforeTime S v early).toHealing.sg_votes (q - 1) := by
      simpa only [sourceBatch, source, Protocol.round_batch,
        if_neg (Nat.ne_of_gt hq), Protocol.HealingStore.gradeView,
        Protocol.Store.toHealing] using hyData.1
    exact GradeDeliveryRun.projected_rounds_storeBeforeTime
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v early (q - 1) y hyRaw
  have heq := GradeDeliveryRun.equivocation_before_of_two
    source.timestamp_sg_vote hfibre huOpen hcOpen hne
    (by simpa only [source, Protocol.HealingStore.gradeView,
      Protocol.Store.toHealing] using huSource.2)
    (by simpa only [source, Protocol.HealingStore.gradeView,
      Protocol.Store.toHealing] using hcSource.2)
  simpa only [source, sourceBatch, Proofs.Optimistic.summary_e_v_eq] using heq

/-! ## The arbitrary-read grade-1 theorem -/

/-- A same-reader grade-1 supporter persists from any read at or after the
fixed `Γ₀(q)` cutoff to every later read. -/
theorem G1_persists_after_cutoff
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {q : Round}
    {early later : Time} (hcut : S.hc.Γ_0 S.E.Δ q ≤ early)
    (hlater : early ≤ later) {B : Block V}
    (hG1 : Protocol.G1 S.E
      ((rho.storeBeforeTime S v early).toHealing.gradeView) S.hc q B = true) :
    Protocol.G1 S.E
      ((rho.storeBeforeTime S v later).toHealing.gradeView) S.hc q B = true := by
  by_cases hq : q = 0
  · subst q
    simp at hG1 ⊢
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq
  let source := (rho.storeBeforeTime S v early).toHealing.gradeView
  let laterView := (rho.storeBeforeTime S v later).toHealing.gradeView
  have hG1' : S.E.m ≤ Protocol.direct_support S.E source q
      (S.hc.Γ_0 S.E.Δ q) (S.hc.Γ_0 S.E.Δ q) B := by
    simpa only [source, Protocol.G1, decide_eq_true_eq] using hG1
  have hsupport : S.E.m ≤ Protocol.direct_support S.E laterView q
      (S.hc.Γ_0 S.E.Δ q) (S.hc.Γ_0 S.E.Δ q) B := by
    simp only [Protocol.direct_support] at hG1' ⊢
    refine le_trans hG1' ?_
    apply Proofs.HealingLemmas.weightOf_filter_mono S.E
    intro x hx
    rcases hx with ⟨ht, hcov, he⟩
    obtain ⟨u, hu, hC, htu⟩ :=
      GradeDeliveryRun.vote_of_summary_support source q x B
        (S.hc.Γ_0 S.E.Δ q) ht hcov
    have huv : u.val_index = x := (Finset.mem_filter.mp hu).2
    have huSource : u ∈
        (rho.storeBeforeTime S v early).toHealing.sg_votes (q - 1) := by
      simpa only [source, Protocol.round_batch, if_neg hq,
        Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using
        (Finset.mem_filter.mp hu).1
    have hutSource : occurrenceBefore
        (Protocol.sg_resolution_time source.T source.timestamp_block
          source.timestamp_sg_vote u) (S.hc.Γ_0 S.E.Δ q) = true := by
      rw [← htu]
      exact ht
    have huSourceReceipt : occurrenceBefore (source.timestamp_sg_vote u)
        (S.hc.Γ_0 S.E.Δ q) = true :=
      GradeDeliveryRun.receipt_before_of_resolution_before hutSource
    have huPersist := projected_vote_persists_after_cutoff S adm hv (q := q)
      hcut hlater huSource (by simpa only [source,
        Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using huSourceReceipt)
    have hucovSource : Protocol.head_covers source.T B u.confirmed = true := by
      rw [← hC]
      exact hcov
    obtain ⟨root, H, huRoot, hfindSource, hHSource, hBH⟩ :=
      Proofs.HealingLemmas.exists_head_of_head_covers hucovSource
    have hmaxSource : occurrenceBefore
        (occurrenceMax (source.timestamp_sg_vote u)
          (source.timestamp_block H)) (S.hc.Γ_0 S.E.Δ q) = true := by
      simpa only [Protocol.sg_resolution_time, huRoot, hfindSource] using hutSource
    have hBlockSource : stampedBefore source.timestamp_block
        (S.hc.Γ_0 S.E.Δ q) H = true := by
      simpa only [stampedBefore_eq_occurrenceBefore] using
        (GradeDeliveryRun.occurrenceBefore_of_max_right hmaxSource)
    have hHSourceStore : H ∈
        (rho.storeBeforeTime S v early).T := by
      simpa only [source, Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using
        hHSource
    have hBlockSourceStore : stampedBefore
        (rho.storeBeforeTime S v early).timestamp_block
          (S.hc.Γ_0 S.E.Δ q) H = true := by
      simpa only [source, Protocol.HealingStore.gradeView, Protocol.Store.toHealing,
        stampedBefore_eq_occurrenceBefore] using hBlockSource
    have hHLater := block_persists_after_cutoff S adm hv (q := q) hcut hlater
      hHSourceStore hBlockSourceStore
    have hfindLater := GradeDeliveryRun.find_target_of_source_find_and_mem
      S adm hv hfindSource hHLater.1
    have hfindLater' : Block.find? laterView.T root = some H := by
      simpa only [laterView, Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using
        hfindLater
    have hucovLater : Protocol.head_covers laterView.T B u.confirmed = true := by
      simp only [Protocol.head_covers, huRoot]
      rw [hfindLater']
      exact hBH
    have huLaterBatch : u ∈ Protocol.sg_votes_by
        (Protocol.round_batch laterView q) x := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, huv⟩
      simpa only [laterView, Protocol.round_batch, if_neg hq,
        Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using huPersist.1
    have huLaterTime : occurrenceBefore
        (Protocol.sg_resolution_time laterView.T laterView.timestamp_block
          laterView.timestamp_sg_vote u) (S.hc.Γ_0 S.E.Δ q) = true := by
      simp only [Protocol.sg_resolution_time, huRoot]
      rw [hfindLater']
      exact occurrenceBefore_max huPersist.2
        (by simpa only [laterView, Protocol.HealingStore.gradeView,
          Protocol.Store.toHealing, stampedBefore_eq_occurrenceBefore] using
          hHLater.2)
    have hselected := GradeDeliveryRun.summary_support_or_equivocation_of_vote
      laterView q x B (S.hc.Γ_0 S.E.Δ q)
      (by
        intro k y hy
        exact GradeDeliveryRun.projected_rounds_storeBeforeTime
          S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v later k y hy)
      huLaterBatch huLaterTime hucovLater
    have hsourceClean : occurrenceBefore
        (Protocol.summary source q x).e_v
          (S.hc.Γ_0 S.E.Δ q) = false := by
      simpa only [occurrenceAtLeast, Bool.not_eq_true'] using he
    rcases hselected with hlaterSupport | hlaterEquiv
    · have hlaterClean : occurrenceAtLeast
          (Protocol.summary laterView q x).e_v
            (S.hc.Γ_0 S.E.Δ q) = true := by
        cases hbefore : occurrenceBefore
            (Protocol.summary laterView q x).e_v
              (S.hc.Γ_0 S.E.Δ q) with
        | false => simp [occurrenceAtLeast, hbefore]
        | true =>
            have hsourceEq := summary_equivocation_reflects_after_cutoff
              S adm hv hqpos (q := q) hcut hlater
                (by simpa only [laterView] using hbefore)
            rw [hsourceClean] at hsourceEq
            simp at hsourceEq
      exact ⟨hlaterSupport.1, hlaterSupport.2, hlaterClean⟩
    · have hsourceEq := summary_equivocation_reflects_after_cutoff
        S adm hv hqpos (q := q) hcut hlater
          (by simpa only [laterView] using hlaterEquiv)
      rw [hsourceClean] at hsourceEq
      simp at hsourceEq
  simpa only [laterView, Protocol.G1, decide_eq_true_eq] using hsupport


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
