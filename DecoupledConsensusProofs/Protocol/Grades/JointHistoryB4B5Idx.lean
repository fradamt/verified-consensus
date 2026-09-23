module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.LayerAHistoryIndices
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.JointHistoryProducersIndices
public import DecoupledConsensusProofs.Protocol.Store.JointHistoryB4B5
public import DecoupledConsensusProofs.Protocol.Handlers.SGArrivalStampCarrier
public import DecoupledConsensusProofs.Execution.OutageActionInputs
public import DecoupledConsensusProofs.Protocol.Grades.HealthyHeadReady

@[expose] public section

/-!
# Index form of B4 (delivery/open) and B5 (provenance) (
, task 2)

Only `capture_ready_token` and `graded_root_below_of_positive` actually take
the time-based joint history (`LayerAJointHistoryOn`/`SGVoteOnHistory`) as a
hypothesis; `healthy_emitted_sg_raw_at_index`, `honest_awake_emits`,
`awake_window_row_head` and `gradeView_vote_row` have no history argument at
all and are reused verbatim from `JointHistoryB4B5.lean`.

Both restated theorems replace their single TIME bound against the witness
(`domain ….g2 < t` / `S.a k < t`) with an INDEX bound against `n`
(`j < n` / `ii < n`), where the bounded quantity is now the tick event's own
position in `rho.events`, not its time. The two places that serves to need the
witness time only to compare it against a schedule-derived time bound
(`hSaklt`, `hlt`) now instead compare two EVENT TIMES directly and lift that
strict time inequality to an index inequality via `index_lt_of_time_lt`
(general sortedness, no tick-vs-deliver phase trick needed since here the two
times are already strictly ordered, not tied): the row's own action-tick time
`S.a k` is always strictly below the capture/reading tick's time by pure
schedule arithmetic (`action_delta_le_early_g2`/`early_g2_lt_domain_g2`), so
`index_lt_of_time_lt` alone gives the index order, with no provenance/
delivery step required.

The one place that still needs a strict-prefix INDEX (the clause-(3) renewal
at the confirmed head's own arrival deadline `d = S.a k + Δ`, inside
`capture_ready_token`'s ancestor branch) is simpler than the time-based
original: the index form of clause (3) (`LayerAHistoryIdx`'s third clause)
takes a bare `i ≤ n`, not a `PrefixThrough`, so the existing
`Proofs.NamedRuntime.stateBeforeTime_eq_prefix` witness `nd` only needs `nd ≤ n`
(from `nd ≤ j ≤ n`), with no prefix-membership proof to reconstruct at all.
-/


namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.JointHistoryB4B5
open Execution Internal.NamedOutageEntry Protocol
open Internal.NamedOutageEntry.History
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open JointHistoryProducersTime JointHistoryB4B5Time
variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
private theorem time_le_of_key_le {e f : NamedEvent V} (h : e.key ≤ f.key) :
    e.time ≤ f.time := by
  rcases Prod.Lex.le_iff.mp h with hlt | ⟨heq, _⟩
  · exact hlt.le
  · exact heq.le

/-- Two events with a strict time gap sit at indices in the same strict
order: no phase tie-break is needed here (unlike `tick_lt_of_deliver_index`),
since the time inequality is already strict. -/
theorem index_lt_of_time_lt (rho : NamedRun V)
    (sorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    {i j : Nat} {e f : NamedEvent V}
    (hi : rho.events[i]? = some e) (hj : rho.events[j]? = some f)
    (ht : e.time < f.time) : i < j := by
  by_contra hcon
  push_neg at hcon
  rcases lt_or_eq_of_le hcon with hlt | heq
  · obtain ⟨hjLen, hjGet⟩ := List.getElem?_eq_some_iff.mp hj
    obtain ⟨hiLen, hiGet⟩ := List.getElem?_eq_some_iff.mp hi
    have hkey := (List.pairwise_iff_getElem.mp sorted) j i hjLen hiLen hlt
    rw [hjGet, hiGet] at hkey
    exact absurd (time_le_of_key_le hkey) (not_le.mpr ht)
  · subst heq
    rw [hi] at hj
    injection hj with hef
    exact absurd (hef ▸ ht) (lt_irrefl _)

/-- Index form of `JointHistoryB4B5Time.capture_ready_token`. -/
theorem capture_ready_token
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (cap : Time) (healthy : NamedHealthyPrefixDelivery S rho cap) (hR : 3 ≤ S.hc.R)
    (n : Nat) (C : NamedBlock V) (hhistory : LayerAJointHistoryIdx S rho n C)
    (j : Nat) (v : V) (hv : v ∈ rho.honest) (r : Round)
    (hje : rho.events[j]? = some (.tick v (domain S.E S.hc r .g2)))
    (hjn : j < n)
    (hcapd : domain S.E S.hc r .g2 ≤ cap)
    (w : V) (hw : w ∈ rho.honest) (k : Round)
    (hkw : k ∈ Protocol.latest_window S.hc.η_SG r)
    (i : Nat) (a : NamedAttestation V) (H : NamedBlock V)
    (hie : rho.events[i]? = some (.tick w (S.a k)))
    (hem : NamedRun.emits S rho w (.attest a) (S.a k))
    (hval : a.val_index = w) (har : a.round = k)
    (hH : H ∈ (NamedRun.stateBefore S rho i w).st.bodies)
    (hkey : a.confirmed = some H.root) :
    (readyView (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
      (NamedRun.stateBefore S rho j v).st.core.F S.hc.η_SG r
      (early S.E S.hc r .g2) w).Nonempty := by
  have hkr : k < r := (OutageInputs.window_bounds hkw).2
  have hdead : S.a k + S.E.Δ ≤ early S.E S.hc r .g2 := action_delta_le_early_g2 S hkr hR
  have hearlylt : early S.E S.hc r .g2 < domain S.E S.hc r .g2 := early_g2_lt_domain_g2 S r
  have hcapk : S.a k + S.E.Δ ≤ cap := hdead.trans (hearlylt.le.trans hcapd)
  have hemA : NamedRun.emits S rho a.val_index (.attest a) (S.a a.round) := by
    rw [hval, har]; exact hem
  obtain ⟨-, hrawA⟩ := healthy_emitted_sg_raw_at_index S rho core cap healthy
    (by rw [hval]; exact hw) hemA r (by rw [har]; exact hkw)
    (by rw [har]; exact hdead) (by rw [har]; exact hcapk) v hv j
    (.tick v (domain S.E S.hc r .g2)) hje hearlylt.le
  have hraw : Protocol.sgVote a.erase ∈ DecoupledConsensusModel.Protocol.rawInputs
      (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
      S.hc.η_SG r (early S.E S.hc r .g2) w := by rw [← hval]; exact hrawA
  have hHrun : NamedRun.blockInRun S rho H :=
    Proofs.NamedRuntime.blockInRun_of_direct S rho
      (Proofs.NamedRuntime.directBlock_of_prefix S rho hw i hH)
  -- `i'` (w's own action-tick index for row `a`) sits strictly below `j`: its
  -- time `S.a k` is strictly below `j`'s time by schedule arithmetic alone,
  -- so `index_lt_of_time_lt` gives the index order with no provenance step.
  obtain ⟨i', hi', hobj⟩ := hem
  have hSaklt : S.a k < domain S.E S.hc r .g2 :=
    (lt_add_of_pos_right (S.a k) S.E.Δ_pos).trans_le (hdead.trans hearlylt.le)
  have hi'j : i' < j := index_lt_of_time_lt rho core.sorted hi' hje hSaklt
  have hi'n : i' < n := lt_trans hi'j hjn
  obtain ⟨K, -, -, hKroot, hKC⟩ :=
    hhistory.2.1 i' w (S.a k) a hw hi' hobj hi'n H.root hkey
  have hHC : NamedBlock.Preceq H C := by
    have heq : K = H := core.root_injective C H hhistory.1.1 hHrun K H
      (Or.inl hKC) (Or.inr (named_preceq_self H)) hKroot
    exact heq ▸ hKC
  -- The reader's own finalized body at the same read is below the same
  -- witness (clause (3), index form: a bare `j ≤ n`).
  obtain ⟨Fv, -, hFvmem, hFve, hFvC⟩ := hhistory.1.2.2.2 j v hv hjn.le
  rcases ViabilityHistoryTime.named_common_chain hHC hFvC with hHFv | hFvH
  · -- The confirmed head is already an ancestor of the reader's own
    -- finalized body: renew clause (3) a second time, at the confirmed
    -- head's own arrival DEADLINE `d = S.a k + Δ`, using the index form's
    -- bare `nd ≤ n` (from `nd ≤ j ≤ n`) in place of a rebuilt prefix.
    have hpc := (Proofs.NamedRuntime.stateBefore_invariants S rho j v).1.1.1.2.2.1
    have hHmem : H ∈ (NamedRun.stateBefore S rho j v).st.bodies :=
      ViabilityHistoryTime.ancestor_body_mem hpc hFvmem hHFv
    have hcohj := (Proofs.NamedRuntime.stateBefore_invariants S rho j v).1.1.1
    have hlookup : Block.find? (NamedRun.stateBefore S rho j v).st.core.T H.root =
        some H.erase := by
      rw [← Proofs.NamedWire.erase_root H]
      have hHraw : H.erase ∈ (NamedRun.stateBefore S rho j v).st.core.T := by
        rw [hcohj.1]; exact Finset.mem_image_of_mem NamedBlock.erase hHmem
      apply Proofs.Optimistic.find?_eq_some_of_unique hHraw
      intro Y hY hrootY
      rw [hcohj.1] at hY
      obtain ⟨other, hother, rfl⟩ := Finset.mem_image.mp hY
      have hotherScope := Proofs.NamedRuntime.blockInRun_of_direct S rho
        (Proofs.NamedRuntime.directBlock_of_prefix S rho hv j hother)
      have hroots : other.root = H.root :=
        (Proofs.NamedWire.erase_root other).symm.trans (hrootY.trans (Proofs.NamedWire.erase_root H))
      have heq : other = H := core.root_injective other H hotherScope hHrun other H
        (Or.inl (named_preceq_self other)) (Or.inr (named_preceq_self H)) hroots
      exact congrArg NamedBlock.erase heq
    have hStampedMono : ∀ (ts : TimestampMap (Block V)) (x : Block V),
        stampedBefore ts (S.a k + S.E.Δ) x = true →
        stampedBefore ts (early S.E S.hc r .g2) x = true := by
      intro ts x hx
      unfold stampedBefore at hx ⊢
      cases hts : ts x with
      | none => simp only [hts, Bool.false_eq_true] at hx
      | some u =>
        simp only [hts, decide_eq_true_eq] at hx ⊢
        exact hx.trans_le (WithBot.coe_le_coe.mpr hdead)
    have hstamp : stampedBefore (NamedRun.stateBefore S rho j v).st.core.timestamp_block
        (early S.E S.hc r .g2) H.erase = true := by
      obtain ⟨nd, hndEq, hndStrict⟩ :=
        Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho core.sorted (S.a k + S.E.Δ)
      have hndj : nd ≤ j := by
        by_contra hcon
        have hjlt : j < nd := by omega
        have hcontra := hndStrict j (.tick v (domain S.E S.hc r .g2)) hjlt hje
        simp only [NamedEvent.time] at hcontra
        exact absurd hcontra (not_lt.mpr (hdead.trans hearlylt.le))
      have hndn : nd ≤ n := hndj.trans hjn.le
      obtain ⟨Fd, -, hFdmem, hFde, hFdC⟩ := hhistory.1.2.2.2 nd v hv hndn
      rcases ViabilityHistoryTime.named_common_chain hHC hFdC with hHFd | hFdH
      · have hpcNd := (Proofs.NamedRuntime.stateBefore_invariants S rho nd v).1.1.1.2.2.1
        have hHmemNd : H ∈ (NamedRun.stateBefore S rho nd v).st.bodies :=
          ViabilityHistoryTime.ancestor_body_mem hpcNd hFdmem hHFd
        have hHmemD : H ∈
            (NamedRun.stateBeforeTime S rho (S.a k + S.E.Δ) v).st.bodies := by
          rw [hndEq]; exact hHmemNd
        have hstampD := NamedBlockStamp.held_body_stampedBefore_stateBeforeTime S rho
          core.toNamedScheduleWellFormed v (S.a k + S.E.Δ) H hHmemD
        have hNdStamped : stampedBefore
            (NamedRun.stateBefore S rho nd v).st.core.timestamp_block
            (S.a k + S.E.Δ) H.erase = true := by rw [hndEq] at hstampD; exact hstampD
        have hNd := hStampedMono _ _ hNdStamped
        obtain ⟨-, hstampEq⟩ :=
          NamedBlockStamp.stateBefore_body_stamp_mono S rho v hndj hHmemNd
        unfold stampedBefore at hNd ⊢
        rw [hstampEq]
        exact hNd
      · have hieq := Proofs.NamedRuntime.tick_prefix_eq_strict S rho core.sorted core.nodup hie
        have hFtimeD : Block.Preceq
            (NamedRun.stateBeforeTime S rho (S.a k + S.E.Δ) v).st.core.F H.erase := by
          rw [hndEq, ← hFde]
          exact Proofs.NamedWire.erase_preceq hFdH
        have hHsrc : H ∈ (NamedRun.stateBeforeTime S rho (S.a k) w).st.bodies := by
          rw [← hieq]; exact hH
        obtain ⟨hHeldD, hstampD, -⟩ := NamedHealthyHeadReady.healthy_head_body_at_read
          S rho core cap healthy w hw v hv H (S.a k) (S.a k + S.E.Δ) (S.a k + S.E.Δ)
          hHsrc (le_refl _) (le_refl _) hcapk hFtimeD
        have hHmemNd : H ∈ (NamedRun.stateBefore S rho nd v).st.bodies := by
          rw [← hndEq]; exact hHeldD
        have hNdStamped : stampedBefore
            (NamedRun.stateBefore S rho nd v).st.core.timestamp_block
            (S.a k + S.E.Δ) H.erase = true := by rw [hndEq] at hstampD; exact hstampD
        have hNd := hStampedMono _ _ hNdStamped
        obtain ⟨-, hstampEq⟩ :=
          NamedBlockStamp.stateBefore_body_stamp_mono S rho v hndj hHmemNd
        unfold stampedBefore at hNd ⊢
        rw [hstampEq]
        exact hNd
    have hbody : DecoupledConsensusModel.Protocol.bodyReady
        (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
        (NamedRun.stateBefore S rho j v).st.core.F (early S.E S.hc r .g2)
        (Protocol.sgVote a.erase) = true := by
      have hconf : (Protocol.sgVote a.erase).confirmed = some H.root := hkey
      simp only [DecoupledConsensusModel.Protocol.bodyReady, hconf]
      change (match Block.find? (NamedRun.stateBefore S rho j v).st.core.T H.root with
        | none => false
        | some head => stampedBefore (NamedRun.stateBefore S rho j v).st.core.timestamp_block
            (early S.E S.hc r .g2) head &&
          Block.compatible head (NamedRun.stateBefore S rho j v).st.core.F) = true
      rw [hlookup, Bool.and_eq_true]
      refine ⟨hstamp, ?_⟩
      simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inl (by rw [← hFve]; exact Proofs.NamedWire.erase_preceq hHFv)
    exact ⟨DecoupledConsensusModel.Protocol.token (Protocol.sgVote a.erase),
      Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hraw, hbody⟩)⟩
  · -- The reader's own finalized body is an ancestor of the confirmed head:
    -- the original delivery route through the healthy prefix, unchanged.
    have hF : Block.Preceq (NamedRun.stateBefore S rho j v).st.core.F H.erase := by
      rw [← hFve]; exact Proofs.NamedWire.erase_preceq hFvH
    have hjeq : NamedRun.stateBefore S rho j v =
        NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v :=
      Proofs.NamedRuntime.tick_prefix_eq_strict S rho core.sorted core.nodup hje
    have hieq : NamedRun.stateBefore S rho i w =
        NamedRun.stateBeforeTime S rho (S.a k) w :=
      Proofs.NamedRuntime.tick_prefix_eq_strict S rho core.sorted core.nodup hie
    have hHsrc : H ∈ (NamedRun.stateBeforeTime S rho (S.a k) w).st.bodies := by
      rw [← hieq]; exact hH
    have hFtime : Block.Preceq
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.F H.erase := by
      rw [← hjeq]; exact hF
    obtain ⟨-, hstampT, hlookupT⟩ := NamedHealthyHeadReady.healthy_head_body_at_read
      S rho core cap healthy w hw v hv H (S.a k) (early S.E S.hc r .g2)
      (domain S.E S.hc r .g2) hHsrc hdead hearlylt.le (hearlylt.le.trans hcapd) hFtime
    have hstamp : stampedBefore (NamedRun.stateBefore S rho j v).st.core.timestamp_block
        (early S.E S.hc r .g2) H.erase = true := by rw [hjeq]; exact hstampT
    have hlookup : Block.find? (NamedRun.stateBefore S rho j v).st.core.T H.root =
        some H.erase := by
      rw [hjeq, ← Proofs.NamedWire.erase_root H]; exact hlookupT
    have hbody : DecoupledConsensusModel.Protocol.bodyReady
        (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
        (NamedRun.stateBefore S rho j v).st.core.F (early S.E S.hc r .g2)
        (Protocol.sgVote a.erase) = true := by
      have hconf : (Protocol.sgVote a.erase).confirmed = some H.root := hkey
      simp only [DecoupledConsensusModel.Protocol.bodyReady, hconf]
      change (match Block.find? (NamedRun.stateBefore S rho j v).st.core.T H.root with
        | none => false
        | some head => stampedBefore (NamedRun.stateBefore S rho j v).st.core.timestamp_block
            (early S.E S.hc r .g2) head &&
          Block.compatible head (NamedRun.stateBefore S rho j v).st.core.F) = true
      rw [hlookup, Bool.and_eq_true]
      refine ⟨hstamp, ?_⟩
      simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr hF
    exact ⟨DecoupledConsensusModel.Protocol.token (Protocol.sgVote a.erase),
      Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hraw, hbody⟩)⟩

/-- Index form of `JointHistoryB4B5Time.graded_root_below_of_positive`:
`hsgv` becomes `SGVoteIdx`, and the schedule bound `hbound` now compares each
window round's action time against the CAPTURE EVENT's own time `e.time`
(still a time comparison; `j`/`n` supply the index side via
`index_lt_of_time_lt`). -/
theorem graded_root_below_of_positive
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (n : Nat) (C : NamedBlock V) (hsgv : SGVoteIdx S rho n C)
    (j : Nat) (v : V) (hv : v ∈ rho.honest) (e : NamedEvent V)
    (hje : rho.events[j]? = some e) (hjn : j < n)
    (r : Round) (raw : Block V) (w : V) (hw : w ∈ rho.honest)
    (hbound : ∀ k ∈ Protocol.latest_window S.hc.η_SG r, S.a k < e.time)
    (hpos : positive (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
      (NamedRun.stateBefore S rho j v).st.core.F S.hc.η_SG r
      (early S.E S.hc r .g2) (late S.E S.hc r .g2) w raw = true) :
    ∃ K : NamedBlock V,
      NamedRun.blockInRun S rho K ∧ NamedBlock.Preceq K C ∧ Block.Preceq raw K.erase := by
  have hsupport := (of_decide_eq_true hpos :
    DecoupledConsensusModel.Protocol.Supports
      (fun key b => localCovers (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
        key b = true)
      (readyView (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
        (NamedRun.stateBefore S rho j v).st.core.F S.hc.η_SG r (early S.E S.hc r .g2) w)
      (readyView (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
        (NamedRun.stateBefore S rho j v).st.core.F S.hc.η_SG r (late S.E S.hc r .g2) w)
      (rawView (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
        S.hc.η_SG r (late S.E S.hc r .g2) w) raw)
  obtain ⟨tok, htok, -, hcov, -, -⟩ := hsupport
  obtain ⟨u, hu, htoken⟩ := Finset.mem_image.mp htok
  obtain ⟨hrawmem, -⟩ := Finset.mem_filter.mp hu
  obtain ⟨hpool, hvalocc⟩ := Finset.mem_filter.mp hrawmem
  obtain ⟨k, hk, huk⟩ := Finset.mem_biUnion.mp hpool
  obtain ⟨named, hnamed, hne⟩ := gradeView_vote_row S rho j v k huk
  have hdata := (SGArrival.data_at_event S rho core.toNamedScheduleWellFormed hje v).1
  have hround : named.round = k := (hdata.2 k named hnamed).1
  have hownrow : named ∈ (NamedRun.stateBefore S rho j v).st.sg_rows named.round := by
    rw [hround]; exact hnamed
  have hvalw : named.val_index = w := by
    have hproj : named.val_index = u.val_index := congrArg Protocol.SGVote.val_index hne
    exact hproj.trans hvalocc.1
  have hhon : named.val_index ∈ rho.honest := by rw [hvalw]; exact hw
  obtain ⟨-, -, -, -, -, hemit⟩ :=
    NamedOutageProvenance.honest_held_row_emission S rho core.toNamedUnforgeable j v hownrow hhon
  obtain ⟨ii, hii, hobj⟩ := hemit
  have hltT : S.a named.round < e.time := by
    rw [hround]; exact hbound k (List.mem_toFinset.mp hk)
  have hiij : ii < j := index_lt_of_time_lt rho core.sorted hii hje hltT
  have hiin : ii < n := lt_trans hiij hjn
  have hkey : tok.key = u.confirmed := by rw [← htoken]; rfl
  have hconfsame : named.confirmed = u.confirmed :=
    congrArg Protocol.SGVote.confirmed hne
  rw [hkey] at hcov
  change Protocol.head_covers
    (NamedRun.stateBefore S rho j v).st.core.T raw u.confirmed = true at hcov
  cases hc : u.confirmed with
  | none => rw [hc] at hcov; exact absurd hcov (by simp [Protocol.head_covers])
  | some key =>
    rw [hc] at hcov
    cases hfind : Block.find? (NamedRun.stateBefore S rho j v).st.core.T key with
    | none =>
      simp only [Protocol.head_covers, hfind] at hcov
      exact absurd hcov (by simp)
    | some head =>
      have hpreceq : Block.Preceq raw head := by
        simpa only [Protocol.head_covers, hfind] using hcov
      obtain ⟨K, hKrun, -, hKroot, hKC⟩ :=
        hsgv ii named.val_index (S.a named.round) named hhon hii hobj hiin key
          (hconfsame.trans hc)
      have hcohj := (Proofs.NamedRuntime.stateBefore_invariants S rho j v).1.1.1
      have hheadmem : head ∈ (NamedRun.stateBefore S rho j v).st.core.T :=
        Proofs.HealingLemmas.find?_mem hfind
      rw [hcohj.1] at hheadmem
      obtain ⟨K', hK'body, hK'e⟩ := Finset.mem_image.mp hheadmem
      have hK'run := Proofs.NamedRuntime.blockInRun_of_direct S rho
        (Proofs.NamedRuntime.directBlock_of_prefix S rho hv j hK'body)
      have hheadroot : head.root = key := Proofs.HealingLemmas.find?_root hfind
      have hroots : K'.root = K.root := by
        rw [← Proofs.NamedWire.erase_root K', hK'e]
        exact hheadroot.trans hKroot.symm
      have heqK : K' = K := core.root_injective K' K hK'run hKrun K' K
        (Or.inl (named_preceq_self K')) (Or.inr (named_preceq_self K)) hroots
      have hheadK : head = K.erase := by rw [← hK'e, heqK]
      exact ⟨K, hKrun, hKC, by rw [← hheadK]; exact hpreceq⟩

#print axioms index_lt_of_time_lt
end DecoupledConsensusModel.Proofs.NamedOutageHistory.JointHistoryB4B5

end
