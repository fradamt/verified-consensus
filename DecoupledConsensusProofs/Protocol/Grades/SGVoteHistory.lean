module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.JointHistoryGaps
public import DecoupledConsensusProofs.Execution.PrefixThroughHistory
public import DecoupledConsensusProofs.Protocol.Handlers.PrefixCarrier
public import DecoupledConsensusProofs.Protocol.ChainState.JustificationCertificates
public import DecoupledConsensusProofs.Execution.OutageProvenance
public import DecoupledConsensusProofs.Protocol.Handlers.ReceiptCallsGF
public import DecoupledConsensusProofs.Protocol.Grades.GuardedGradeHelpers

@[expose] public section


namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.SGVoteOnHistoryTime
open Execution Internal.NamedOutageEntry Protocol
open Internal.NamedOutageEntry.History
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open JointHistoryProducersTime JointHistoryB4B5Time JointHistoryGapsTime
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 0. Two more `actionReadFrom` field equalities (mirroring `action_read_F`) -/




/-! ## 1. Private plumbing copied from `JointHistoryProducers.lean`
(there `private`, hence not visible here). Generic in the phase argument. -/

omit [Fintype V] in
private theorem clip_preceq' (g F : Block V) : Block.Preceq (clipGrade g F) g := by
  induction g with
  | genesis => exact Block.preceq_self _
  | node p s root gv gsv ats v ih =>
    simp only [clipGrade]
    split
    · exact Block.preceq_self _
    · apply Block.preceq_trans ih
      simp only [Block.preceq, Bool.or_eq_true]
      exact Or.inr (Block.preceq_self p)

omit [Fintype V] in
private theorem clip_result_prefix' (F P root : Block V)
    (result : Option (Option (Block V)))
    (hresult : clipResult F result = some (some root)) (hP : Block.Preceq P root) :
    ∃ old : Block V, result = some (some old) ∧ Block.Preceq P old := by
  cases result with
  | none => simp only [clipResult, Option.map_none, reduceCtorEq] at hresult
  | some result =>
    cases result with
    | none =>
      change (some none : Option (Option (Block V))) = some (some root) at hresult
      have hbad : (none : Option (Block V)) = some root := Option.some.inj hresult
      cases hbad
    | some old =>
      have he : clipGrade old F = root := by
        simpa only [clipResult, Option.map_some, Option.some.injEq] using hresult
      exact ⟨old, rfl, Block.preceq_trans hP (by rw [← he]; exact clip_preceq' old F)⟩

omit [DecidableEq V] [Fintype V] in
private theorem align_current' (c : Cache V) (s : Round) :
    (alignRound c s).current = cacheAtRound c s ∧ (alignRound c s).round = s := by
  unfold alignRound
  split_ifs with hs hn
  · exact ⟨by simp only [cacheAtRound, if_pos hs], hs.symm⟩
  · exact ⟨by simp only [cacheAtRound, if_neg hs, if_pos hn], rfl⟩
  · exact ⟨by simp only [cacheAtRound, if_neg hs, if_neg hn], rfl⟩

private theorem complete_one_other' (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) (t : Time) (p q : Phase) (f : Frame V) (h : q ≠ p) :
    phaseResult (completeOne E hc st r t p f) q = phaseResult f q := by
  unfold completeOne
  split
  · rfl
  · split
    · cases p <;> cases q <;> simp_all only [putPhase, phaseResult, ne_eq, not_true_eq_false]
    · rfl

/-! ## 2. The g1-phase schedule arithmetic -/

/-- The G1 domain of a round is strictly before that round's action
(mirrors `action_after_g2`: `S.a s = domain.g1 + 6Δ`). -/
theorem action_after_g1 (S : Setup V) (s : Round) : domain S.E S.hc s .g1 < S.a s := by
  have he : S.a s = domain S.E S.hc s .g1 + 6 * S.E.Δ := by
    unfold Setup.a Protocol.HealConfig.a domain opening Phase.domainOffset
      Protocol.proposal_time Env.t slotStart
    ring
  rw [he]
  exact lt_add_of_pos_right _
    (Int.mul_pos (by decide : (0 : Int) < 6) S.E.Δ_pos)

/-- Mirrors `JointHistoryB4B5Time.early_g2_lt_domain_g2` with the g1
offsets `(-4, 0)` in place of `(-5, -1)`. -/
theorem early_g1_lt_domain_g1 (S : Setup V) (r : Round) :
    early S.E S.hc r .g1 < domain S.E S.hc r .g1 := by
  change DecoupledConsensusModel.Protocol.opening S.E S.hc r + (-4) * S.E.Δ <
    DecoupledConsensusModel.Protocol.opening S.E S.hc r + (0) * S.E.Δ
  refine Int.add_lt_add_left ?_ _
  calc (-4 : Time) * S.E.Δ = (0 : Time) * S.E.Δ - 4 * S.E.Δ := by ring
    _ < (0 : Time) * S.E.Δ := sub_lt_self _ (Int.mul_pos (by norm_num) S.E.Δ_pos)

/-- The g2 schedule bound (`action_delta_le_early_g2`) shifted one `Δ` later
via `GuardedHelpers.early_g2_add_delta`; no fresh arithmetic needed. -/
theorem action_delta_le_early_g1 (S : Setup V) {k r : Round} (hkr : k < r)
    (hR : 3 ≤ S.hc.R) : S.a k + S.E.Δ ≤ early S.E S.hc r .g1 := by
  rw [← GuardedHelpers.early_g2_add_delta S r]
  exact (action_delta_le_early_g2 S hkr hR).trans (le_add_of_nonneg_right S.E.Δ_pos.le)

/-! ## 3. `frame.g1`'s capture provenance (mirrors `q2_capture_at_action_read`,
but with no `activePrefix` step baked in: `anchor` applies that separately). -/

private theorem complete_frame_g1' (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (s : Round) (t : Time) (f : Frame V)
    (ht : t ≠ domain E hc s .g1) : (completeFrame E hc st s t f).g1 = f.g1 := by
  change phaseResult (completeFrame E hc st s t f) .g1 = phaseResult f .g1
  unfold completeFrame
  rw [complete_one_other' E hc st s t .g0 .g1 _ (by decide)]
  have hY : phaseResult (completeOne E hc st s t .g2 f) .g1 = phaseResult f .g1 :=
    complete_one_other' E hc st s t .g2 .g1 f (by decide)
  generalize hYdef : completeOne E hc st s t .g2 f = Y at hY ⊢
  unfold completeOne
  split
  · exact hY
  · split
    · exact absurd ‹t = domain E hc s .g1› ht
    · exact hY

private theorem prepared_g1_from_old' (S : Setup V) (before : NamedNodeState V) (s : Round) :
    (cacheAtRound (preparedCache S before (S.a s)) s).g1 =
      clipResult before.st.core.F (cacheAtRound before.cache s).g1 := by
  let aligned := alignRound before.cache s
  have hcurrent : aligned.current = cacheAtRound before.cache s := (align_current' before.cache s).1
  have hround : aligned.round = s := (align_current' before.cache s).2
  have htime : S.a s ≠ domain S.E S.hc s .g1 := ne_of_gt (action_after_g1 S s)
  unfold preparedCache NamedActionReads.preparedCache onPhaseTick
  rw [Proofs.HealingLemmas.round_of_slotOf_a S s]
  change (cacheAtRound (clipCache before.st.core.F
    ⟨aligned.round,
      completeFrame S.E S.hc before.st.core.toHealing aligned.round (S.a s) aligned.current,
      completeFrame S.E S.hc before.st.core.toHealing (aligned.round + 1) (S.a s)
        aligned.next⟩) s).g1 = _
  simp only [cacheAtRound, clipCache, hround]
  change clipResult before.st.core.F
    (completeFrame S.E S.hc before.st.core.toHealing s (S.a s) aligned.current).g1 = _
  rw [complete_frame_g1' S.E S.hc before.st.core.toHealing s (S.a s) aligned.current htime,
    hcurrent]
  rfl

/-- The g1 twin of `q2_capture_at_action_read`: the raw `frame.g1` root this
validator's own action read holds is below a G1 root it froze at its own
strictly earlier G1-domain tick. No `activePrefix` step: `anchor` applies that
separately, outside `frame.g1`. -/
theorem g1_capture_at_action_read (S : Setup V) (rho : NamedRun V)
    (i : Nat) (v : V) (r : Round) {root : Block V}
    (hg1 : (DecoupledConsensusModel.Protocol.readFrame
        (actionReadFrom S (NamedRun.stateBefore S rho i v) r).cache
        (actionReadFrom S (NamedRun.stateBefore S rho i v) r).st.core.toHealing r).g1 =
      some (some root)) :
    ∃ (j : Nat) (raw : Block V),
      j < i ∧
      rho.events[j]? = some (.tick v (domain S.E S.hc r .g1)) ∧
      freezeRoot S.E (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
        (NamedRun.stateBefore S rho j v).st.core.F S.hc.η_SG r
        (early S.E S.hc r .g1) (late S.E S.hc r .g1) = some raw ∧
      Block.Preceq root raw := by
  set before := NamedRun.stateBefore S rho i v with hbefore
  set n := actionReadFrom S before r with hn
  change clipResult before.st.core.F (cacheAtRound n.cache r).g1 = some (some root) at hg1
  obtain ⟨prepared, hprepared, hrootprep⟩ :=
    clip_result_prefix' before.st.core.F root root _ hg1 (Block.preceq_self root)
  change (cacheAtRound (preparedCache S before (S.a r)) r).g1 = some (some prepared) at hprepared
  rw [prepared_g1_from_old' S before r] at hprepared
  obtain ⟨old, hold, hrootold⟩ :=
    clip_result_prefix' before.st.core.F root prepared _ hprepared hrootprep
  have hphase : phaseResult (cacheAtRound (NamedRun.stateBefore S rho i v).cache r) .g1 =
      some (some old) := hold
  rcases NamedCacheProvenance.completed_phase_origin S rho i v r .g1 (some old) hphase with
    ⟨_, hzero⟩ | ⟨j, tt, hj, he, ht, hroot⟩
  · exact absurd hzero (by simp)
  · subst tt
    obtain ⟨raw, hraw, hclip⟩ := Option.map_eq_some_iff.mp hroot.symm
    refine ⟨j, raw, hj, he, hraw, ?_⟩
    exact Block.preceq_trans hrootold (by rw [← hclip]; exact clip_preceq' raw _)

/-! ## 4. B4/B5 for the g1 phase (mirrors `JointHistoryB4B5.lean`'s
`capture_ready_token` and `graded_root_below_of_positive`, `.g2 →.g1`).
`awake_window_row_head` and `honest_awake_emits` are already phase-free and are
reused verbatim. -/



/-- Mirrors `healthy_emitted_sg_raw_at_index` with `.g2 →.g1`. -/
theorem healthy_emitted_sg_raw_at_index_g1
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (cap : Time) (healthy : NamedHealthyPrefixDelivery S rho cap)
    {a : NamedAttestation V} (ha : a.val_index ∈ rho.honest)
    (hem : NamedRun.emits S rho a.val_index (.attest a) (S.a a.round))
    (r : Round) (hwindow : a.round ∈ Protocol.latest_window S.hc.η_SG r)
    (hearly : S.a a.round + S.E.Δ ≤ early S.E S.hc r .g1)
    (hcap : S.a a.round + S.E.Δ ≤ cap)
    (reader : V) (hreader : reader ∈ rho.honest)
    (j : Nat) (e : NamedEvent V) (hj : rho.events[j]? = some e)
    (hjt : early S.E S.hc r .g1 ≤ e.time) :
    a ∈ (NamedRun.stateBefore S rho j reader).st.sg_rows a.round ∧
      Protocol.sgVote a.erase ∈ DecoupledConsensusModel.Protocol.rawInputs
        (NamedRun.stateBefore S rho j reader).st.core.toHealing.gradeView
        S.hc.η_SG r (early S.E S.hc r .g1) a.val_index := by
  obtain ⟨td, hlo, hhi, i, hcall⟩ :=
    healthy.broadcast a.val_index ha (.attest a) (S.a a.round) hem reader hreader hcap rfl
  have hpost := SGArrival.honest_row_after_call S rho
    core.toNamedScheduleWellFormed core.toNamedUnforgeable ha hem hcall hlo hhi
  obtain ⟨e', he', _, het⟩ := hcall.2
  have hdata : SGArrival.Data td (NamedRun.stateBefore S rho (i + 1) reader).st := by
    simpa only [het] using
      (SGArrival.data_at_event S rho core.toNamedScheduleWellFormed he' reader).2
  obtain ⟨_, stamp, hstampBound, hstamp⟩ := hdata.2 a.round a hpost
  have htdEarly : td < early S.E S.hc r .g1 := hhi.trans_le hearly
  have hij : i + 1 ≤ j := by
    by_contra hcon
    have hji : j ≤ i := by omega
    have hle := SGArrival.event_time_le rho core.sorted hj he' hji
    rw [het] at hle
    exact absurd (hjt.trans hle) (not_le.mpr htdEarly)
  obtain ⟨hheld, hstampEq⟩ :=
    SGArrival.stateBefore_sg_row_stamp_mono S rho reader hij hpost
  have hstampJ : (NamedRun.stateBefore S rho j reader).st.core.timestamp_sg_vote
      (Protocol.sgVote a.erase) = some (stamp : Stamp) := hstampEq.trans hstamp
  have hoccur : occurrenceBefore
      ((NamedRun.stateBefore S rho j reader).st.core.timestamp_sg_vote (Protocol.sgVote a.erase))
      (early S.E S.hc r .g1) = true := by
    simp only [hstampJ, occurrenceBefore, decide_eq_true_eq]
    exact WithBot.coe_lt_coe.mpr (hstampBound.trans_lt htdEarly)
  have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho j reader).1.1.1
  have hrawPool : a.erase ∈ (NamedRun.stateBefore S rho j reader).st.core.sg_pool a.round :=
    NamedAdmission.pool_view_mem _ hcoh.2.2.2.1 a hheld
  have hsg : Protocol.sgVote a.erase ∈
      (NamedRun.stateBefore S rho j reader).st.core.toHealing.gradeView.sg_votes a.round :=
    Finset.mem_image_of_mem Protocol.sgVote hrawPool
  refine ⟨hheld, ?_⟩
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_biUnion.mpr ⟨a.round, List.mem_toFinset.mpr hwindow, hsg⟩, rfl, hoccur⟩



/-! ## 5. The g1 twin of `GradedRootOnHistory`/`graded_root_on_history` -/


/-- Mirrors `honest_positive_of_gradeBool_ready` with `.g2 →.g1`: the
underlying `honest_positive_of_gradeBool` (`JointHistoryProducers.lean`)
is already generic in the two cutoff times, so only the cover derivation
(`positive_or_opposing` against `readyView_mono` monotonicity) needs the g1
schedule fact. -/
theorem honest_positive_of_gradeBool_ready_g1
    (S : Setup V) (Hon : Finset V) (awake : V → Round → Bool) (r : Round)
    (gv : Protocol.GradeView V) (F B : Block V)
    (hgrade : gradeBool S.E gv F S.hc.η_SG r
      (early S.E S.hc r .g1) (late S.E S.hc r .g1) B = true)
    (hwin : AwakeWindowMajority S.E awake Hon S.hc.η_SG r)
    (hready : ∀ v ∈ honestAwakeWindow awake Hon S.hc.η_SG r,
      (readyView gv F S.hc.η_SG r (early S.E S.hc r .g1) v).Nonempty) :
    ∃ w ∈ Hon, positive gv F S.hc.η_SG r
      (early S.E S.hc r .g1) (late S.E S.hc r .g1) w B = true :=
  honest_positive_of_gradeBool S.E Hon awake S.hc.η_SG r gv F _ _ B hgrade hwin
    (fun v hv => positive_or_opposing gv F S.hc.η_SG r _ _ v B
      (readyView_mono gv F S.hc.η_SG r (GuardedHelpers.early_g1_le_late_g1 S r) v)
      (hready v hv))


/-! ## 6. The `key` unfolding to `DecoupledConsensusModel.Protocol.selectedSGVote` -/

theorem sgvote_key_eq (S : Setup V) (n : NamedNodeState V) (r : Round) :
    Protocol.get_sg_vote_with (NamedProfile.gradeContract n.cache) S.E S.hc
        n.st.core.toHealing r
        (Protocol.grade2_block_with (NamedProfile.gradeContract n.cache) S.E S.hc
          n.st.core.toHealing r) =
      DecoupledConsensusModel.Protocol.selectedSGVote S.E S.hc n.st.core.toHealing r
        (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r) := rfl

/-- A fully abstract case-split lemma for `selectedSGVote`, kept separate from any
concrete `n`/`actionReadFrom` term so that `unfold` never has to look inside
those large definitional chains. -/
theorem sgVote_cases (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V) (r : Round)
    (frame : Frame V) :
    DecoupledConsensusModel.Protocol.selectedSGVote E hc st r frame =
      match Protocol.deepest_clear
          (some (DecoupledConsensusModel.Protocol.anchor E hc st r frame.g1))
          st.live_confirmed (DecoupledConsensusModel.Protocol.clear frame) with
      | some B => B
      | none => match DecoupledConsensusModel.Protocol.grade2Block st frame with
        | some Q => Q
        | none => if (frame.g2.bind id).isSome then
            Protocol.get_fg_root st.toFG
          else DecoupledConsensusModel.Protocol.anchor E hc st r frame.g1 := by
  rfl

/-! ## 7. The earlier theorem -/


#print axioms g1_capture_at_action_read
#print axioms sgVote_cases
end DecoupledConsensusModel.Proofs.NamedOutageHistory.SGVoteOnHistoryTime

end
