module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.LayerAHistoryIndices
public import DecoupledConsensusProofs.Protocol.Grades.JointHistoryB4B5Idx
public import DecoupledConsensusProofs.Protocol.Grades.JointHistoryGapsIdx
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.JustificationHistoryIndices
public import DecoupledConsensusProofs.Protocol.Grades.SGVoteHistory
public import DecoupledConsensusProofs.Protocol.Grades.GuardedGradeHelpers

@[expose] public section


namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.SGVoteOnHistory
open Execution Internal.NamedOutageEntry Protocol
open Internal.NamedOutageEntry.History
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open JointHistoryProducersTime JointHistoryB4B5Time SGVoteOnHistoryTime
open JointHistoryB4B5 JointHistoryGaps
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The g1 twin of the B4/B5 index proof -/

/-- Index form of `SGVoteOnHistoryTime.capture_ready_token_g1`. Mirrors
`JointHistoryB4B5.capture_ready_token` with `.g2 →.g1`. -/
theorem capture_ready_token_g1
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (cap : Time) (healthy : NamedHealthyPrefixDelivery S rho cap) (hR : 3 ≤ S.hc.R)
    (n : Nat) (C : NamedBlock V) (hhistory : LayerAJointHistoryIdx S rho n C)
    (j : Nat) (v : V) (hv : v ∈ rho.honest) (r : Round)
    (hje : rho.events[j]? = some (.tick v (domain S.E S.hc r .g1)))
    (hjn : j < n)
    (hcapd : domain S.E S.hc r .g1 ≤ cap)
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
      (early S.E S.hc r .g1) w).Nonempty := by
  have hkr : k < r := (OutageInputs.window_bounds hkw).2
  have hdead : S.a k + S.E.Δ ≤ early S.E S.hc r .g1 := action_delta_le_early_g1 S hkr hR
  have hearlylt : early S.E S.hc r .g1 < domain S.E S.hc r .g1 := early_g1_lt_domain_g1 S r
  have hcapk : S.a k + S.E.Δ ≤ cap := hdead.trans (hearlylt.le.trans hcapd)
  have hemA : NamedRun.emits S rho a.val_index (.attest a) (S.a a.round) := by
    rw [hval, har]; exact hem
  obtain ⟨-, hrawA⟩ := healthy_emitted_sg_raw_at_index_g1 S rho core cap healthy
    (by rw [hval]; exact hw) hemA r (by rw [har]; exact hkw)
    (by rw [har]; exact hdead) (by rw [har]; exact hcapk) v hv j
    (.tick v (domain S.E S.hc r .g1)) hje hearlylt.le
  have hraw : Protocol.sgVote a.erase ∈ DecoupledConsensusModel.Protocol.rawInputs
      (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
      S.hc.η_SG r (early S.E S.hc r .g1) w := by rw [← hval]; exact hrawA
  have hHrun : NamedRun.blockInRun S rho H :=
    Proofs.NamedRuntime.blockInRun_of_direct S rho
      (Proofs.NamedRuntime.directBlock_of_prefix S rho hw i hH)
  obtain ⟨i', hi', hobj⟩ := hem
  have hSaklt : S.a k < domain S.E S.hc r .g1 :=
    (lt_add_of_pos_right (S.a k) S.E.Δ_pos).trans_le (hdead.trans hearlylt.le)
  have hi'j : i' < j := index_lt_of_time_lt rho core.sorted hi' hje hSaklt
  have hi'n : i' < n := lt_trans hi'j hjn
  obtain ⟨K, -, -, hKroot, hKC⟩ :=
    hhistory.2.1 i' w (S.a k) a hw hi' hobj hi'n H.root hkey
  have hHC : NamedBlock.Preceq H C := by
    have heq : K = H := core.root_injective C H hhistory.1.1 hHrun K H
      (Or.inl hKC) (Or.inr (named_preceq_self H)) hKroot
    exact heq ▸ hKC
  obtain ⟨Fv, -, hFvmem, hFve, hFvC⟩ := hhistory.1.2.2.2 j v hv hjn.le
  rcases ViabilityHistoryTime.named_common_chain hHC hFvC with hHFv | hFvH
  · have hpc := (Proofs.NamedRuntime.stateBefore_invariants S rho j v).1.1.1.2.2.1
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
        stampedBefore ts (early S.E S.hc r .g1) x = true := by
      intro ts x hx
      unfold stampedBefore at hx ⊢
      cases hts : ts x with
      | none => simp only [hts, Bool.false_eq_true] at hx
      | some u =>
        simp only [hts, decide_eq_true_eq] at hx ⊢
        exact hx.trans_le (WithBot.coe_le_coe.mpr hdead)
    have hstamp : stampedBefore (NamedRun.stateBefore S rho j v).st.core.timestamp_block
        (early S.E S.hc r .g1) H.erase = true := by
      obtain ⟨nd, hndEq, hndStrict⟩ :=
        Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho core.sorted (S.a k + S.E.Δ)
      have hndj : nd ≤ j := by
        by_contra hcon
        have hjlt : j < nd := by omega
        have hcontra := hndStrict j (.tick v (domain S.E S.hc r .g1)) hjlt hje
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
        (NamedRun.stateBefore S rho j v).st.core.F (early S.E S.hc r .g1)
        (Protocol.sgVote a.erase) = true := by
      have hconf : (Protocol.sgVote a.erase).confirmed = some H.root := hkey
      simp only [DecoupledConsensusModel.Protocol.bodyReady, hconf]
      change (match Block.find? (NamedRun.stateBefore S rho j v).st.core.T H.root with
        | none => false
        | some head => stampedBefore (NamedRun.stateBefore S rho j v).st.core.timestamp_block
            (early S.E S.hc r .g1) head &&
          Block.compatible head (NamedRun.stateBefore S rho j v).st.core.F) = true
      rw [hlookup, Bool.and_eq_true]
      refine ⟨hstamp, ?_⟩
      simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inl (by rw [← hFve]; exact Proofs.NamedWire.erase_preceq hHFv)
    exact ⟨DecoupledConsensusModel.Protocol.token (Protocol.sgVote a.erase),
      Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hraw, hbody⟩)⟩
  · have hF : Block.Preceq (NamedRun.stateBefore S rho j v).st.core.F H.erase := by
      rw [← hFve]; exact Proofs.NamedWire.erase_preceq hFvH
    have hjeq : NamedRun.stateBefore S rho j v =
        NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) v :=
      Proofs.NamedRuntime.tick_prefix_eq_strict S rho core.sorted core.nodup hje
    have hieq : NamedRun.stateBefore S rho i w =
        NamedRun.stateBeforeTime S rho (S.a k) w :=
      Proofs.NamedRuntime.tick_prefix_eq_strict S rho core.sorted core.nodup hie
    have hHsrc : H ∈ (NamedRun.stateBeforeTime S rho (S.a k) w).st.bodies := by
      rw [← hieq]; exact hH
    have hFtime : Block.Preceq
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) v).st.core.F H.erase := by
      rw [← hjeq]; exact hF
    obtain ⟨-, hstampT, hlookupT⟩ := NamedHealthyHeadReady.healthy_head_body_at_read
      S rho core cap healthy w hw v hv H (S.a k) (early S.E S.hc r .g1)
      (domain S.E S.hc r .g1) hHsrc hdead hearlylt.le (hearlylt.le.trans hcapd) hFtime
    have hstamp : stampedBefore (NamedRun.stateBefore S rho j v).st.core.timestamp_block
        (early S.E S.hc r .g1) H.erase = true := by rw [hjeq]; exact hstampT
    have hlookup : Block.find? (NamedRun.stateBefore S rho j v).st.core.T H.root =
        some H.erase := by
      rw [hjeq, ← Proofs.NamedWire.erase_root H]; exact hlookupT
    have hbody : DecoupledConsensusModel.Protocol.bodyReady
        (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
        (NamedRun.stateBefore S rho j v).st.core.F (early S.E S.hc r .g1)
        (Protocol.sgVote a.erase) = true := by
      have hconf : (Protocol.sgVote a.erase).confirmed = some H.root := hkey
      simp only [DecoupledConsensusModel.Protocol.bodyReady, hconf]
      change (match Block.find? (NamedRun.stateBefore S rho j v).st.core.T H.root with
        | none => false
        | some head => stampedBefore (NamedRun.stateBefore S rho j v).st.core.timestamp_block
            (early S.E S.hc r .g1) head &&
          Block.compatible head (NamedRun.stateBefore S rho j v).st.core.F) = true
      rw [hlookup, Bool.and_eq_true]
      refine ⟨hstamp, ?_⟩
      simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr hF
    exact ⟨DecoupledConsensusModel.Protocol.token (Protocol.sgVote a.erase),
      Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hraw, hbody⟩)⟩

/-- Index form of `SGVoteOnHistoryTime.graded_root_below_of_positive_g1`.
Mirrors `JointHistoryB4B5.graded_root_below_of_positive` with
`.g2 →.g1`. -/
theorem graded_root_below_of_positive_g1
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (n : Nat) (C : NamedBlock V) (hsgv : SGVoteIdx S rho n C)
    (j : Nat) (v : V) (hv : v ∈ rho.honest) (e : NamedEvent V)
    (hje : rho.events[j]? = some e) (hjn : j < n)
    (r : Round) (raw : Block V) (w : V) (hw : w ∈ rho.honest)
    (hbound : ∀ k ∈ Protocol.latest_window S.hc.η_SG r, S.a k < e.time)
    (hpos : positive (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
      (NamedRun.stateBefore S rho j v).st.core.F S.hc.η_SG r
      (early S.E S.hc r .g1) (late S.E S.hc r .g1) w raw = true) :
    ∃ K : NamedBlock V,
      NamedRun.blockInRun S rho K ∧ NamedBlock.Preceq K C ∧ Block.Preceq raw K.erase := by
  have hsupport := (of_decide_eq_true hpos :
    DecoupledConsensusModel.Protocol.Supports
      (fun key b => localCovers (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
        key b = true)
      (readyView (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
        (NamedRun.stateBefore S rho j v).st.core.F S.hc.η_SG r (early S.E S.hc r .g1) w)
      (readyView (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
        (NamedRun.stateBefore S rho j v).st.core.F S.hc.η_SG r (late S.E S.hc r .g1) w)
      (rawView (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
        S.hc.η_SG r (late S.E S.hc r .g1) w) raw)
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

/-- Index form of `SGVoteOnHistoryTime.GradedRootOnHistoryG1`. -/
def GradedRootOnHistoryG1Idx (S : Setup V) (rho : NamedRun V) (n : Nat)
    (C : NamedBlock V) : Prop :=
  ∀ (j : Nat) (v : V) (r : Round) (raw : Block V), v ∈ rho.honest →
    rho.events[j]? = some (.tick v (domain S.E S.hc r .g1)) →
    j < n →
    gradeBool S.E (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
      (NamedRun.stateBefore S rho j v).st.core.F S.hc.η_SG r
      (early S.E S.hc r .g1) (late S.E S.hc r .g1) raw = true →
    ∃ K : NamedBlock V,
      NamedRun.blockInRun S rho K ∧ NamedBlock.Preceq K C ∧ Block.Preceq raw K.erase

/-- Index form of `SGVoteOnHistoryTime.graded_root_on_history_g1`. -/
theorem graded_root_on_history_g1
    (S : Setup V) (rho : NamedRun V) (cap : Time)
    (core : NamedAdmissibleCore S rho)
    (healthy : NamedHealthyPrefixDelivery S rho cap)
    (committees : HonestCommittees S rho.honest) (hR : 3 ≤ S.hc.R)
    (hcap : cap ≤ rho.horizon)
    (windows : ∀ k, 0 < k → domain S.E S.hc k .g2 ≤ cap →
      AwakeWindowMajority S.E (fun v => (S.node v).awake) rho.honest S.hc.η_SG k)
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q)
    (n : Nat) (C : NamedBlock V) (hhistory : LayerAJointHistoryIdx S rho n C)
    (hcapn : ∀ i, i < n → ∀ e : NamedEvent V, rho.events[i]? = some e → e.time ≤ cap) :
    GradedRootOnHistoryG1Idx S rho n C := by
  intro j v r raw hv hje hjn hgb
  have hearlylt : early S.E S.hc r .g1 < domain S.E S.hc r .g1 := early_g1_lt_domain_g1 S r
  have hcapd : domain S.E S.hc r .g1 ≤ cap := by
    have h := hcapn j hjn (.tick v (domain S.E S.hc r .g1)) hje
    simpa only [NamedEvent.time] using h
  have hwindowTime : ∀ k ∈ Protocol.latest_window S.hc.η_SG r,
      S.a k + S.E.Δ ≤ early S.E S.hc r .g1 := fun k hk =>
    action_delta_le_early_g1 S (OutageInputs.window_bounds hk).2 hR
  by_cases hr : 0 < r
  · have hcapd2 : domain S.E S.hc r .g2 ≤ cap :=
      (GuardedHelpers.domain_g2_le_domain_g1 S r).trans hcapd
    have hwin := windows r hr hcapd2
    have hready : ∀ u ∈ honestAwakeWindow (fun x => (S.node x).awake) rho.honest S.hc.η_SG r,
        (readyView (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
          (NamedRun.stateBefore S rho j v).st.core.F S.hc.η_SG r
          (early S.E S.hc r .g1) u).Nonempty := by
      intro u hu
      obtain ⟨huHon, huAwake⟩ := Finset.mem_filter.mp hu
      obtain ⟨k, hk, hka⟩ := List.any_eq_true.mp huAwake
      have hdead := hwindowTime k hk
      have hhor : S.a k ≤ rho.horizon :=
        (le_add_of_nonneg_right S.E.Δ_pos.le).trans
          (hdead.trans ((hearlylt.le.trans hcapd).trans hcap))
      obtain ⟨i, a, H, hie, hem, hval, har, hH, hkey⟩ :=
        awake_window_row_head S rho core.toNamedScheduleWellFormed u huHon k hka hhor
      exact capture_ready_token_g1 S rho core cap healthy hR n C hhistory j v hv r hje hjn hcapd
        u huHon k hk i a H hie hem hval har hH hkey
    obtain ⟨w, hwHon, hpos⟩ := honest_positive_of_gradeBool_ready_g1 S rho.honest
      (fun x => (S.node x).awake) r
      (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
      (NamedRun.stateBefore S rho j v).st.core.F raw hgb hwin hready
    refine graded_root_below_of_positive_g1 S rho core n C hhistory.2.1 j v hv
      (.tick v (domain S.E S.hc r .g1)) hje hjn r raw w hwHon (fun k hk => ?_) hpos
    exact ((lt_add_of_pos_right (S.a k) S.E.Δ_pos).trans_le (hwindowTime k hk)).trans hearlylt
  · exfalso
    have hr0 : r = 0 := Nat.eq_zero_of_not_pos hr
    subst hr0
    have hempty : ∀ (u : V) (x : DecoupledConsensusModel.Protocol.Token (Option BlockId)),
        x ∉ readyView (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
          (NamedRun.stateBefore S rho j v).st.core.F S.hc.η_SG 0
          (early S.E S.hc 0 .g1) u := by
      intro u x hx
      obtain ⟨y, hy, -⟩ := Finset.mem_image.mp hx
      obtain ⟨hyraw, -⟩ := Finset.mem_filter.mp hy
      obtain ⟨hpool, -⟩ := Finset.mem_filter.mp hyraw
      obtain ⟨k, hk, -⟩ := Finset.mem_biUnion.mp hpool
      exact absurd (OutageInputs.window_bounds (List.mem_toFinset.mp hk)).2
        (Nat.not_lt_zero k)
    have hposfalse : (Finset.univ.filter fun u =>
        positive (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
          (NamedRun.stateBefore S rho j v).st.core.F S.hc.η_SG 0
          (early S.E S.hc 0 .g1) (late S.E S.hc 0 .g1) u raw = true) = (∅ : Finset V) := by
      refine Finset.filter_false_of_mem ?_
      intro u _
      simp only [positive, decide_eq_true_eq]
      rintro ⟨tok, htok, -⟩
      exact hempty u tok htok
    have hltw : S.E.electorate.weightOf
        (Finset.univ.filter fun u =>
          opposing (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
            (NamedRun.stateBefore S rho j v).st.core.F S.hc.η_SG 0
            (early S.E S.hc 0 .g1) (late S.E S.hc 0 .g1) u raw = true) <
        S.E.electorate.weightOf
          (Finset.univ.filter fun u =>
            positive (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
              (NamedRun.stateBefore S rho j v).st.core.F S.hc.η_SG 0
              (early S.E S.hc 0 .g1) (late S.E S.hc 0 .g1) u raw = true) := by
      simpa only [gradeBool, decide_eq_true_eq] using hgb
    rw [hposfalse] at hltw
    exact Nat.not_lt_zero _ (by simpa only [Electorate.weightOf, Finset.sum_empty] using hltw)

/-! ## The earlier theorem, index form -/

/-- Index form of `SGVoteOnHistoryTime.sg_vote_on_history`. The outer
joint-history bound is named `m` (the theorem's own local `let n:=
actionReadFrom …` already claims `n`). `hconf4` is a one-shot
`ConfirmationAtTick` at the theorem's own acting tick `i`. -/
theorem sg_vote_on_history
    (S : Setup V) (rho : NamedRun V) (cap : Time)
    (core : NamedAdmissibleCore S rho)
    (healthy : NamedHealthyPrefixDelivery S rho cap)
    (committees : HonestCommittees S rho.honest) (hR : 3 ≤ S.hc.R)
    (hcap : cap ≤ rho.horizon)
    (windows : ∀ k, 0 < k → domain S.E S.hc k .g2 ≤ cap →
      AwakeWindowMajority S.E (fun v => (S.node v).awake) rho.honest S.hc.η_SG k)
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q)
    (m : Nat) (C : NamedBlock V) (hhistory : LayerAJointHistoryIdx S rho m C)
    (hcapm : ∀ j, j < m → ∀ e : NamedEvent V, rho.events[j]? = some e → e.time ≤ cap)
    (i : Nat) (v : V) (r : Round) (hv : v ∈ rho.honest)
    (hi : rho.events[i]? = some (.tick v (S.a r)))
    (him : i ≤ m)
    (hconf4 : ConfirmationAtTick S rho i C) :
    let n := actionReadFrom S (NamedRun.stateBefore S rho i v) r
    let key := Protocol.get_sg_vote_with (NamedProfile.gradeContract n.cache) S.E S.hc
      n.st.core.toHealing r
      (Protocol.grade2_block_with (NamedProfile.gradeContract n.cache) S.E S.hc
        n.st.core.toHealing r)
    ∃ K : NamedBlock V, NamedRun.blockInRun S rho K ∧ K ∈ n.st.bodies ∧ K.erase = key ∧
      (NamedBlock.Preceq K C ∨ NamedBlock.Preceq C K) := by
  intro n key
  set before := NamedRun.stateBefore S rho i v with hbefore
  have hgraded := JointHistoryGaps.graded_root_on_history S rho cap core healthy
    committees hR hcap windows hbad m C hhistory hcapm
  have hgradedG1 := graded_root_on_history_g1 S rho cap core healthy committees hR hcap windows
    hbad m C hhistory hcapm
  have hkeyeq : key = DecoupledConsensusModel.Protocol.selectedSGVote S.E S.hc n.st.core.toHealing r
      (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r) := sgvote_key_eq S n r
  rw [hkeyeq]
  set frame := DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r with hframe
  rw [sgVote_cases S.E S.hc n.st.core.toHealing r frame]
  set A := DecoupledConsensusModel.Protocol.anchor S.E S.hc n.st.core.toHealing r frame.g1 with hA
  cases hd : Protocol.deepest_clear (some A) n.st.core.toHealing.live_confirmed
      (DecoupledConsensusModel.Protocol.clear frame) with
  | some B =>
    -- Arm 1: the `deepest_clear` walk off the anchor. `B ≼ live_confirmed`,
    -- and the one-shot `ConfirmationAtTick` at `i` gives a held `L` below `C`
    -- with `L.erase = live_confirmed`; lift `B` to a named ancestor of `L`.
    have hpre : Block.Preceq B n.st.core.toHealing.live_confirmed :=
      Proofs.Engine.deepest_clear_preceq hd
    obtain ⟨L, hLrun, hLbody, hLe, hLC⟩ := hconf4 v r hv hi
    obtain ⟨K, hKL, hKe⟩ := ReadyHeadReturnTime.named_ancestor_of_erase B L
      (by rw [hLe]; exact hpre)
    have hpc : NamedStore.NamedParentClosed n.st :=
      (Proofs.NamedRuntime.stateBefore_invariants S rho i v).1.1.1.2.2.1
    have hKmem : K ∈ n.st.bodies := ViabilityHistoryTime.ancestor_body_mem hpc hLbody hKL
    have hKrun : NamedRun.blockInRun S rho K :=
      Proofs.NamedRuntime.blockInRun_of_direct S rho (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hKmem)
    exact ⟨K, hKrun, hKmem, hKe, Or.inl (named_preceq_trans hKL hLC)⟩
  | none =>
    cases hq2 : DecoupledConsensusModel.Protocol.grade2Block n.st.core.toHealing frame with
    | some Q =>
      -- Arm 2: the Q2 fallback. `Q` is held (`runtime_Q2_mem`); its provenance
      -- (`q2_capture_at_action_read` + `graded_root_on_history`) places it
      -- below a run block `K` below `C`.
      have hQ2mem : Q ∈ n.st.core.toHealing.T :=
        Proofs.NamedConfirmationMembership.runtime_Q2_mem n.cache S.E S.hc
          n.st.core.toHealing r Q hq2
      have hcohn : Proofs.NamedStore.Coherent S.E S.cfg n.st :=
        (Proofs.NamedRuntime.stateBefore_invariants S rho i v).1.1.1
      have hQimg : Q ∈ n.st.bodies.image NamedBlock.erase := hcohn.1 ▸ hQ2mem
      obtain ⟨K'', hK''mem, hK''e⟩ := Finset.mem_image.mp hQimg
      have hK''run : NamedRun.blockInRun S rho K'' :=
        Proofs.NamedRuntime.blockInRun_of_direct S rho
          (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hK''mem)
      obtain ⟨j, raw, hj, hjev, hfreeze, hqraw⟩ := q2_capture_at_action_read S rho i v r hq2
      have hgb : gradeBool S.E (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
          (NamedRun.stateBefore S rho j v).st.core.F S.hc.η_SG r
          (early S.E S.hc r .g2) (late S.E S.hc r .g2) raw = true := by
        have hmem := Proofs.Engine.deepest?_mem (by simpa only [freezeRoot] using hfreeze)
        exact (Finset.mem_filter.mp hmem).2
      have hjm : j < m := lt_of_lt_of_le hj him
      obtain ⟨K, hKrun, hKC, hrawK⟩ := hgraded j v r raw hv hjev hjm hgb
      have hqK : Block.Preceq Q K.erase := Block.preceq_trans hqraw hrawK
      have hK''K : NamedBlock.Preceq K'' K :=
        named_of_erase_preceq S rho core hK''run hKrun (by rw [hK''e]; exact hqK)
      exact ⟨K'', hK''run, hK''mem, hK''e, Or.inl (named_preceq_trans hK''K hKC)⟩
    | none =>
      -- The FG-root fallback, `key = get_fg_root n.st.core.toHealing.toFG`; used
      -- both by arm 3 directly and by three of arm 4's four sub-cases. Both
      -- sub-arms now read directly at the acting tick's own index `i`: no
      -- `stateBefore_strict_prefix`/`PrefixThrough` reconstruction is needed,
      -- since the index forms of `justification_on_history_chain` and clause
      -- (3) both already take a bare `i ≤ m`.
      have hgetFgRoot : ∃ K : NamedBlock V, NamedRun.blockInRun S rho K ∧ K ∈ n.st.bodies ∧
          K.erase = Protocol.get_fg_root n.st.core.toHealing.toFG ∧
          (NamedBlock.Preceq K C ∨ NamedBlock.Preceq C K) := by
        by_cases hmaxj : n.st.core.toHealing.h_max = n.st.core.toHealing.h_j + 1
        · have hfgroot : Protocol.get_fg_root n.st.core.toHealing.toFG =
              n.st.core.toHealing.J := by
            unfold Protocol.get_fg_root
            exact if_pos hmaxj
          rw [hfgroot]
          obtain ⟨J, hJrun, hJbody, hJe, hJC⟩ :=
            HistoryProofs.justification_on_history_chain S rho core m C hhistory.1
              i v hv him hbad
          exact ⟨J, hJrun, hJbody, hJe, Or.inl hJC⟩
        · have hfgroot : Protocol.get_fg_root n.st.core.toHealing.toFG =
              n.st.core.toHealing.F := by
            unfold Protocol.get_fg_root
            exact if_neg hmaxj
          rw [hfgroot]
          obtain ⟨F, hFrun, hFmem, hFe, hFC⟩ := hhistory.1.2.2.2 i v hv him
          exact ⟨F, hFrun, hFmem, hFe, Or.inl hFC⟩
      by_cases hg2some : (frame.g2.bind id).isSome
      · -- Arm 3: the FG-root fallback.
        rw [if_pos hg2some]
        exact hgetFgRoot
      · -- Arm 4: `key = A`, the raw anchor.
        rw [if_neg hg2some, hA]
        cases hg1 : frame.g1 with
        | none => exact hgetFgRoot
        | some g1opt =>
          cases g1opt with
          | none => exact hgetFgRoot
          | some root =>
            cases hap : DecoupledConsensusModel.Protocol.activePrefix
                (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG) root with
            | none =>
              have haval : DecoupledConsensusModel.Protocol.anchor S.E S.hc n.st.core.toHealing r
                  (some (some root)) = Protocol.get_fg_root n.st.core.toHealing.toFG := by
                simp only [DecoupledConsensusModel.Protocol.anchor, hap, Option.getD_none]
              rw [haval]
              exact hgetFgRoot
            | some AP =>
              -- The genuinely new case: the active prefix of the frozen G1
              -- root. `AP` is a member of the raw tree (`activePrefix_mem` +
              -- `get_filtered_block_tree_subset`); its provenance
              -- (`g1_capture_at_action_read` + `graded_root_on_history_g1`)
              -- places `root`, hence `AP`, below a run block `K` below `C`.
              have haval : DecoupledConsensusModel.Protocol.anchor S.E S.hc n.st.core.toHealing r
                  (some (some root)) = AP := by
                simp only [DecoupledConsensusModel.Protocol.anchor, hap, Option.getD_some]
              rw [haval]
              have hAPmem : AP ∈ n.st.core.toHealing.T :=
                Proofs.Records.get_filtered_block_tree_subset n.st.core.toHealing.toFG
                  (NamedProposalParent.activePrefix_mem _ root AP hap)
              have hcohn : Proofs.NamedStore.Coherent S.E S.cfg n.st :=
                (Proofs.NamedRuntime.stateBefore_invariants S rho i v).1.1.1
              have hAPimg : AP ∈ n.st.bodies.image NamedBlock.erase := hcohn.1 ▸ hAPmem
              obtain ⟨K'', hK''mem, hK''e⟩ := Finset.mem_image.mp hAPimg
              have hK''run : NamedRun.blockInRun S rho K'' :=
                Proofs.NamedRuntime.blockInRun_of_direct S rho
                  (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hK''mem)
              have hAProot : Block.Preceq AP root :=
                (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hap)).2
              obtain ⟨j, raw, hj, hjev, hfreeze, hrootraw⟩ :=
                g1_capture_at_action_read S rho i v r hg1
              have hgb : gradeBool S.E (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
                  (NamedRun.stateBefore S rho j v).st.core.F S.hc.η_SG r
                  (early S.E S.hc r .g1) (late S.E S.hc r .g1) raw = true := by
                have hmem := Proofs.Engine.deepest?_mem (by simpa only [freezeRoot] using hfreeze)
                exact (Finset.mem_filter.mp hmem).2
              have hjm : j < m := lt_of_lt_of_le hj him
              obtain ⟨K, hKrun, hKC, hrawK⟩ := hgradedG1 j v r raw hv hjev hjm hgb
              have hAPK : Block.Preceq AP K.erase :=
                Block.preceq_trans hAProot (Block.preceq_trans hrootraw hrawK)
              have hK''K : NamedBlock.Preceq K'' K :=
                named_of_erase_preceq S rho core hK''run hKrun (by rw [hK''e]; exact hAPK)
              exact ⟨K'', hK''run, hK''mem, hK''e, Or.inl (named_preceq_trans hK''K hKC)⟩

end DecoupledConsensusModel.Proofs.NamedOutageHistory.SGVoteOnHistory

end
