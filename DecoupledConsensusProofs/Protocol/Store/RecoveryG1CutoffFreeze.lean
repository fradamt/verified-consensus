module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeDelivery
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RoundZero

@[expose] public section

/-!
# Same-reader G1 cutoff source preservation

These execution-prefix facts prove the same-reader grade-1 freeze. A projected
vote or processed block that is stamped before the fixed opening cutoff was
already accepted before the opening action. It is present at both reads and
keeps its original stamp. The final theorem lifts these object facts through
the summaries and weighted support. It does not claim that filtered-tree
membership or fresh-anchor selection is frozen.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Fixed-cutoff source votes -/

/-- A projected vote in a later same-reader store, stamped before `Γ₀(q)`, was
already present at the opening read and has the same receipt stamp there. -/
theorem projected_vote_reflects_to_opening
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {q : Round} {read : Time}
    (hread : S.a q ≤ read) {k : Round}
    {u : Protocol.SGVote V}
    (hu : u ∈ (rho.storeBeforeTime S v read).toHealing.sg_votes k)
    (hstamp : occurrenceBefore
      ((rho.storeBeforeTime S v read).timestamp_sg_vote u)
        (S.hc.Γ_0 S.E.Δ q) = true) :
    u ∈ (rho.storeBeforeTime S v (S.a q)).toHealing.sg_votes k ∧
      occurrenceBefore
        ((rho.storeBeforeTime S v (S.a q)).timestamp_sg_vote u)
          (S.hc.Γ_0 S.E.Δ q) = true := by
  have hpub : PublicTime S (S.hc.Γ_0 S.E.Δ q) :=
    GradeDeliveryRun.publicTime_Gamma_0 S q
  obtain ⟨a, i, ta, hau, hacc, hta⟩ :=
    GradeDeliveryRun.accepted_attestation_of_projected_stamp_before
      S adm hv hpub hu hstamp
  subst u
  have haround : a.round = k := by
    have hround := GradeDeliveryRun.projected_rounds_storeBeforeTime
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v read k
      (Protocol.sgVote a.erase) hu
    simpa only [Protocol.sgVote] using hround
  have hΓa : S.hc.Γ_0 S.E.Δ q < S.a q :=
    lt_of_lt_of_le
      (lt_trans
        (Proofs.HealingLemmas.Γ_0_lt_Γ_1 S.hc S.E.Δ_pos q)
        (Proofs.HealingLemmas.Γ_1_lt_Γ_2 S.hc S.E.Δ_pos q))
      (Proofs.HealingSurface.Γ_2_le_a S.hc S.E.Δ_pos q)
  obtain ⟨hhandle, hpre, hpost⟩ := hacc
  obtain ⟨hindex, e, he, hnode, htime⟩ := hhandle
  have heOpen : e.time < S.a q := by
    rw [htime]
    exact lt_trans hta hΓa
  have heRead : e.time < read := lt_of_lt_of_le heOpen hread
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
  have hopen := Protocol.sgVote_mem_stateBeforeTime_of_post
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed he heOpen hpostProj
  have hreadStamp :=
    GradeDeliveryRun.timestamp_sg_vote_stateBeforeTime_of_post
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed he heRead hpostProj
  have hopenStamp :=
    GradeDeliveryRun.timestamp_sg_vote_stateBeforeTime_of_post
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed he heOpen hpostProj
  refine ⟨?_, ?_⟩
  · simpa only [Run.storeBeforeTime, haround] using hopen
  · rw [hopenStamp]
    rw [hreadStamp] at hstamp
    exact hstamp

/-- A projected vote present at the opening read with a receipt stamp before
`Γ₀(q)` remains present at a later same-reader read with the same cutoff
stamp. -/
theorem projected_vote_persists_from_opening
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {q : Round} {read : Time}
    (hread : S.a q ≤ read) {k : Round}
    {u : Protocol.SGVote V}
    (hu : u ∈ (rho.storeBeforeTime S v (S.a q)).toHealing.sg_votes k)
    (hstamp : occurrenceBefore
      ((rho.storeBeforeTime S v (S.a q)).timestamp_sg_vote u)
        (S.hc.Γ_0 S.E.Δ q) = true) :
    u ∈ (rho.storeBeforeTime S v read).toHealing.sg_votes k ∧
      occurrenceBefore
        ((rho.storeBeforeTime S v read).timestamp_sg_vote u)
          (S.hc.Γ_0 S.E.Δ q) = true := by
  have hpub : PublicTime S (S.hc.Γ_0 S.E.Δ q) :=
    GradeDeliveryRun.publicTime_Gamma_0 S q
  obtain ⟨a, i, ta, hau, hacc, hta⟩ :=
    GradeDeliveryRun.accepted_attestation_of_projected_stamp_before
      S adm hv hpub hu hstamp
  subst u
  have haround : a.round = k := by
    have hround := GradeDeliveryRun.projected_rounds_storeBeforeTime
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v (S.a q) k
      (Protocol.sgVote a.erase) hu
    simpa only [Protocol.sgVote] using hround
  have hΓa : S.hc.Γ_0 S.E.Δ q < S.a q :=
    lt_of_lt_of_le
      (lt_trans
        (Proofs.HealingLemmas.Γ_0_lt_Γ_1 S.hc S.E.Δ_pos q)
        (Proofs.HealingLemmas.Γ_1_lt_Γ_2 S.hc S.E.Δ_pos q))
      (Proofs.HealingSurface.Γ_2_le_a S.hc S.E.Δ_pos q)
  obtain ⟨hhandle, -, hpost⟩ := hacc
  obtain ⟨-, e, he, -, htime⟩ := hhandle
  have heOpen : e.time < S.a q := by
    rw [htime]
    exact lt_trans hta hΓa
  have heRead : e.time < read := lt_of_lt_of_le heOpen hread
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
  have hlater := Protocol.sgVote_mem_stateBeforeTime_of_post
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed he heRead hpostProj
  have hopenStamp :=
    GradeDeliveryRun.timestamp_sg_vote_stateBeforeTime_of_post
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed he heOpen hpostProj
  have hlaterStamp :=
    GradeDeliveryRun.timestamp_sg_vote_stateBeforeTime_of_post
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed he heRead hpostProj
  refine ⟨?_, ?_⟩
  · simpa only [Run.storeBeforeTime, haround] using hlater
  · rw [hlaterStamp]
    rw [hopenStamp] at hstamp
    exact hstamp

/-! The converse receipt-only reflection is also needed when proving that a
clean opening grade cannot acquire an early later equivocation. -/

theorem summary_equivocation_reflects_to_opening
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {q : Round} (hq : 0 < q)
    {read : Time} (hread : S.a q ≤ read) {x : V}
    (hlater : occurrenceBefore
      (Protocol.summary
        ((rho.storeBeforeTime S v read).toHealing.gradeView) q x).e_v
        (S.hc.Γ_0 S.E.Δ q) = true) :
    occurrenceBefore
      (Protocol.summary (gradeViewAt S rho v q) q x).e_v
        (S.hc.Γ_0 S.E.Δ q) = true := by
  let opening := gradeViewAt S rho v q
  let later := (rho.storeBeforeTime S v read).toHealing.gradeView
  let laterBatch := Protocol.sg_votes_by
    (Protocol.round_batch later q) x
  have hlater' : occurrenceBefore
      (Protocol.equivocation_instant later.timestamp_sg_vote laterBatch)
        (S.hc.Γ_0 S.E.Δ q) = true := by
    simpa only [later, laterBatch, Proofs.Optimistic.summary_e_v_eq] using hlater
  obtain ⟨u, hu, c, hc, hne, hut, hct⟩ :=
    GradeDeliveryRun.witnesses_of_equivocation_before
      later.timestamp_sg_vote hlater'
  have huData := Finset.mem_filter.mp hu
  have hcData := Finset.mem_filter.mp hc
  have huLater : u ∈
      (rho.storeBeforeTime S v read).toHealing.sg_votes (q - 1) := by
    simpa only [laterBatch, later, Protocol.round_batch,
      if_neg (Nat.ne_of_gt hq), Protocol.HealingStore.gradeView,
      Protocol.Store.toHealing] using huData.1
  have hcLater : c ∈
      (rho.storeBeforeTime S v read).toHealing.sg_votes (q - 1) := by
    simpa only [laterBatch, later, Protocol.round_batch,
      if_neg (Nat.ne_of_gt hq), Protocol.HealingStore.gradeView,
      Protocol.Store.toHealing] using hcData.1
  have huOpening := projected_vote_reflects_to_opening S adm hv hread huLater
    (by simpa only [later, Protocol.HealingStore.gradeView,
      Protocol.Store.toHealing] using hut)
  have hcOpening := projected_vote_reflects_to_opening S adm hv hread hcLater
    (by simpa only [later, Protocol.HealingStore.gradeView,
      Protocol.Store.toHealing] using hct)
  let openingBatch := Protocol.sg_votes_by
    (Protocol.round_batch opening q) x
  have huOpen : u ∈ openingBatch := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, huData.2⟩
    simpa only [openingBatch, opening, Protocol.round_batch,
      if_neg (Nat.ne_of_gt hq), gradeViewAt, healStoreAt,
      Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using huOpening.1
  have hcOpen : c ∈ openingBatch := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, hcData.2⟩
    simpa only [openingBatch, opening, Protocol.round_batch,
      if_neg (Nat.ne_of_gt hq), gradeViewAt, healStoreAt,
      Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hcOpening.1
  have hfibre : ∀ y ∈ openingBatch, y.val_index = x ∧ y.round = q - 1 := by
    intro y hy
    have hyData := Finset.mem_filter.mp hy
    refine ⟨hyData.2, ?_⟩
    have hyRaw : y ∈
        (rho.storeBeforeTime S v (S.a q)).toHealing.sg_votes (q - 1) := by
      simpa only [openingBatch, opening, Protocol.round_batch,
        if_neg (Nat.ne_of_gt hq), gradeViewAt, healStoreAt,
        Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hyData.1
    exact GradeDeliveryRun.projected_rounds_storeBeforeTime
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v (S.a q) (q - 1) y hyRaw
  have heq := GradeDeliveryRun.equivocation_before_of_two
    opening.timestamp_sg_vote hfibre huOpen hcOpen hne
    (by simpa only [opening, gradeViewAt, healStoreAt,
      Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using huOpening.2)
    (by simpa only [opening, gradeViewAt, healStoreAt,
      Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hcOpening.2)
  simpa only [opening, openingBatch, Proofs.Optimistic.summary_e_v_eq] using heq

/-! ## Fixed-cutoff source blocks -/


/-- A block already present and stamped before `Γ₀(q)` at the opening read
remains present with the same cutoff stamp at every later same-reader read. -/
theorem block_persists_from_opening
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {q : Round} {read : Time}
    (hread : S.a q ≤ read) {B : Block V}
    (hB : B ∈ (rho.storeBeforeTime S v (S.a q)).T)
    (hstamp : stampedBefore
      (rho.storeBeforeTime S v (S.a q)).timestamp_block
      (S.hc.Γ_0 S.E.Δ q) B = true) :
    B ∈ (rho.storeBeforeTime S v read).T ∧
      stampedBefore
        (rho.storeBeforeTime S v read).timestamp_block
        (S.hc.Γ_0 S.E.Δ q) B = true := by
  have hpub : PublicTime S (S.hc.Γ_0 S.E.Δ q) :=
    GradeDeliveryRun.publicTime_Gamma_0 S q
  obtain hgen | ⟨D, i, ta, hDerase, hacc, hta⟩ :=
    GradeDeliveryRun.accepted_block_of_mem_stamp_before
      S adm hv hpub hB hstamp
  · subst B
    exact Protocol.genesis_mem_and_stamp_storeBeforeTime
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v read (S.hc.Γ_0 S.E.Δ q)
  · have hΓa : S.hc.Γ_0 S.E.Δ q ≤ S.a q :=
      le_of_lt
        (lt_of_lt_of_le
          (lt_trans
            (Proofs.HealingLemmas.Γ_0_lt_Γ_1 S.hc S.E.Δ_pos q)
            (Proofs.HealingLemmas.Γ_1_lt_Γ_2 S.hc S.E.Δ_pos q))
          (Proofs.HealingSurface.Γ_2_le_a S.hc S.E.Δ_pos q))
    have hadmit : Protocol.AdmittedBefore S rho v B
        (S.hc.Γ_0 S.E.Δ q) := ⟨D, hDerase, i, ta, hacc, hta⟩
    exact Protocol.admittedBefore_mem_and_stamp_at
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hadmit (le_trans hΓa hread)

/-! ## The grade-1 summary/cardinality join -/

/-- A grade-1 supporter at the opening read remains a grade-1 supporter at a
later read by the same honest reader. -/
theorem G1_persists_from_opening
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {q : Round} {read : Time}
    (hread : S.a q ≤ read) {B : Block V}
    (hG1 : Protocol.G1 S.E (gradeViewAt S rho v q) S.hc q B = true) :
    Protocol.G1 S.E
      ((rho.storeBeforeTime S v read).toHealing.gradeView) S.hc q B = true := by
  by_cases hq : q = 0
  · subst q
    simp at hG1 ⊢
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq
  let opening := gradeViewAt S rho v q
  let later := (rho.storeBeforeTime S v read).toHealing.gradeView
  have hG1' : S.E.m ≤ Protocol.direct_support S.E opening q
      (S.hc.Γ_0 S.E.Δ q) (S.hc.Γ_0 S.E.Δ q) B := by
    simpa only [opening, Protocol.G1, decide_eq_true_eq] using hG1
  have hsupport : S.E.m ≤ Protocol.direct_support S.E later q
      (S.hc.Γ_0 S.E.Δ q) (S.hc.Γ_0 S.E.Δ q) B := by
    simp only [Protocol.direct_support] at hG1' ⊢
    refine le_trans hG1' ?_
    apply Proofs.HealingLemmas.weightOf_filter_mono S.E
    intro x hx
    rcases hx with ⟨ht, hcov, he⟩
    obtain ⟨u, hu, hC, htu⟩ :=
      GradeDeliveryRun.vote_of_summary_support opening q x B
        (S.hc.Γ_0 S.E.Δ q) ht hcov
    have huv : u.val_index = x := (Finset.mem_filter.mp hu).2
    have huOpening : u ∈
        (rho.storeBeforeTime S v (S.a q)).toHealing.sg_votes (q - 1) := by
      simpa only [opening, gradeViewAt, healStoreAt,
        Protocol.HealingStore.gradeView, Protocol.Store.toHealing,
        Protocol.round_batch, if_neg hq] using (Finset.mem_filter.mp hu).1
    have hutOpen : occurrenceBefore
        (Protocol.sg_resolution_time opening.T opening.timestamp_block
          opening.timestamp_sg_vote u) (S.hc.Γ_0 S.E.Δ q) = true := by
      rw [← htu]
      exact ht
    have huOpenReceipt : occurrenceBefore (opening.timestamp_sg_vote u)
        (S.hc.Γ_0 S.E.Δ q) = true :=
      GradeDeliveryRun.receipt_before_of_resolution_before hutOpen
    have huPersist := projected_vote_persists_from_opening S adm hv hread
      huOpening (by simpa only [opening, gradeViewAt, healStoreAt,
        Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using huOpenReceipt)
    have hucovOpen : Protocol.head_covers opening.T B u.confirmed = true := by
      rw [← hC]
      exact hcov
    obtain ⟨root, H, huRoot, hfindOpen, hHOpen, hBH⟩ :=
      Proofs.HealingLemmas.exists_head_of_head_covers hucovOpen
    have hmaxOpen : occurrenceBefore
        (occurrenceMax (opening.timestamp_sg_vote u)
          (opening.timestamp_block H)) (S.hc.Γ_0 S.E.Δ q) = true := by
      simpa only [Protocol.sg_resolution_time, huRoot, hfindOpen] using hutOpen
    have hBlockOpen : stampedBefore opening.timestamp_block
        (S.hc.Γ_0 S.E.Δ q) H = true := by
      simpa only [stampedBefore_eq_occurrenceBefore] using
        (GradeDeliveryRun.occurrenceBefore_of_max_right hmaxOpen)
    have hHOpening : H ∈
        (rho.storeBeforeTime S v (S.a q)).T := by
      simpa only [opening, gradeViewAt, healStoreAt,
        Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hHOpen
    have hBlockOpening : stampedBefore
        (rho.storeBeforeTime S v (S.a q)).timestamp_block
          (S.hc.Γ_0 S.E.Δ q) H = true := by
      simpa only [opening, gradeViewAt, healStoreAt,
        Protocol.HealingStore.gradeView, Protocol.Store.toHealing,
        stampedBefore_eq_occurrenceBefore] using hBlockOpen
    have hHLater := block_persists_from_opening S adm hv hread
      hHOpening hBlockOpening
    have hfindLater := GradeDeliveryRun.find_target_of_source_find_and_mem
      S adm hv hfindOpen hHLater.1
    have hfindLater' : Block.find? later.T root = some H := by
      simpa only [later, Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using
        hfindLater
    have hucovLater : Protocol.head_covers later.T B u.confirmed = true := by
      simp only [Protocol.head_covers, huRoot]
      rw [hfindLater']
      exact hBH
    have huLater : u ∈
        (rho.storeBeforeTime S v read).toHealing.sg_votes (q - 1) := huPersist.1
    have huLaterBatch : u ∈ Protocol.sg_votes_by
        (Protocol.round_batch later q) x := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, huv⟩
      simpa only [later, Protocol.round_batch, if_neg hq,
        Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using huLater
    have huLaterReceipt : occurrenceBefore (later.timestamp_sg_vote u)
        (S.hc.Γ_0 S.E.Δ q) = true := by
      simpa only [later, Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using
        huPersist.2
    have huLaterTime : occurrenceBefore
        (Protocol.sg_resolution_time later.T later.timestamp_block
          later.timestamp_sg_vote u) (S.hc.Γ_0 S.E.Δ q) = true := by
      simp only [Protocol.sg_resolution_time, huRoot]
      rw [hfindLater']
      exact occurrenceBefore_max huLaterReceipt
        (by simpa only [later, Protocol.HealingStore.gradeView, Protocol.Store.toHealing,
          stampedBefore_eq_occurrenceBefore] using hHLater.2)
    have hselected := GradeDeliveryRun.summary_support_or_equivocation_of_vote
      later q x B (S.hc.Γ_0 S.E.Δ q)
      (by
        intro k y hy
        exact GradeDeliveryRun.projected_rounds_storeBeforeTime
          S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v read k y hy)
      huLaterBatch huLaterTime hucovLater
    have hcleanOpen : occurrenceAtLeast
        (Protocol.summary opening q x).e_v (S.hc.Γ_0 S.E.Δ q) = true := by
      -- The opening support predicate already supplies its cleanliness arm.
      exact he
    rcases hselected with hlaterSupport | hlaterEquiv
    · have hopenClean : occurrenceBefore
          (Protocol.summary opening q x).e_v
            (S.hc.Γ_0 S.E.Δ q) = false := by
        simpa only [occurrenceAtLeast, Bool.not_eq_true'] using he
      have hlaterClean : occurrenceAtLeast
          (Protocol.summary later q x).e_v
            (S.hc.Γ_0 S.E.Δ q) = true := by
        cases hbefore : occurrenceBefore
            (Protocol.summary later q x).e_v
              (S.hc.Γ_0 S.E.Δ q) with
        | false => simp [occurrenceAtLeast, hbefore]
        | true =>
            have hopenEquiv := summary_equivocation_reflects_to_opening
              S adm hv hqpos hread (by simpa only [later] using hbefore)
            rw [hopenClean] at hopenEquiv
            simp at hopenEquiv
      exact ⟨hlaterSupport.1, hlaterSupport.2, hlaterClean⟩
    · have hopenEquiv := summary_equivocation_reflects_to_opening
          S adm hv hqpos hread (by
            simpa only [later] using hlaterEquiv)
      have hopenClean : occurrenceBefore
          (Protocol.summary opening q x).e_v
            (S.hc.Γ_0 S.E.Δ q) = false := by
        simpa only [occurrenceAtLeast, Bool.not_eq_true'] using he
      rw [hopenClean] at hopenEquiv
      simp at hopenEquiv
  simpa only [later, Protocol.G1, decide_eq_true_eq] using hsupport



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
