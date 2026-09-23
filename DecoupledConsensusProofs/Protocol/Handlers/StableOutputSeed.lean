module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.StableOpeningConfirmationSafety
public import DecoupledConsensusProofs.Execution.OutputSeedCore
public import DecoupledConsensusProofs.Protocol.Schedule.StableOutputCanonicityStep1
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.StableOutputCanonicityStep2
public import DecoupledConsensusProofs.Protocol.Grades.PrefixConfirmationSafety
public import DecoupledConsensusProofs.Protocol.Grades.StableOpeningCarrierFloor
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.JustificationHistoryIndices
public import DecoupledConsensusProofs.Protocol.Grades.CacheProvenance
public import DecoupledConsensusProofs.Protocol.Handlers.FGProtection
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.CrossReaderHealthyPrefix

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedOutageEntry.History
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. Sources of a record prefix -/

/-- A G2 grade held by an honest node at round `r` has an honest SG carrier at
an earlier round: an honest node emitted its round-`k` attestation, `k < r`, and
its SG vote block extends the graded block. -/
theorem g2Grade_honestCarrier_before
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (r : Round) (hr : 0 < r) (hmargin : FormationMargin S r b0)
    (v : V) (hv : v ∈ rho.honest) (raw : Block V)
    (hgrade : storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc r .g2) v).st r .g2 raw = true) :
    ∃ k, k < r ∧ ∃ u ∈ rho.honest,
      NamedRun.emits S rho u (.attest (actionAttestationAt S rho u k)) (S.a k) ∧
      Block.Preceq raw (actionSGBlockAt S rho u k) := by
  have hcapHor : b0 ≤ rho.horizon :=
    hexec.interval.2.1.trans hexec.interval.2.2
  have hasCap : S.a r ≤ b0 :=
    (Assembly.a_mono S (Nat.le_succ r)).trans
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin)
  have hdomainCap : domain S.E S.hc r .g2 ≤ b0 :=
    (FrameForward.domain_le_a S r .g2).trans hasCap
  have hcovered : RoundCovered S rho r :=
    Or.inr ⟨.g2, NamedOutageHistory.OutageEnv.domain_g2_nonneg S hr,
      hdomainCap.trans hcapHor⟩
  have hawake : AwakeWindowMajority S.E (fun u => (S.node u).awake)
      rho.honest S.hc.η_SG r :=
    hsleep r hr hcovered
  have hroundOne : domain S.E S.hc 1 .g2 ≤ b0 := by
    exact (FrameForward.domain_le_a S 1 .g2).trans
      ((Assembly.a_mono S (Nat.succ_le_succ (Nat.zero_le r))).trans
        ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin))
  have hT1 := protectedVoteSlots_before
    S rho b0 b1 hexec hcom hsleep hroundOne
  obtain ⟨x, hx⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
  let d := S.hc.opening_slot r + 1
  have hd : 1 ≤ d := by
    dsimp only [d]
    exact Nat.succ_le_succ (Nat.zero_le _)
  have hdCap : Protocol.vote_time S.E d + S.E.Δ ≤ b0 := by
    dsimp only [d]
    rw [Protocol.vote_time_succ_add_delta_eq_confirmation_time,
      ← Protocol.a_eq_confirmation_time S.hc S.E r]
    exact hasCap
  have hsNext : S.a r < Protocol.vote_time S.E (d + 1) := by
    rw [Setup.a, Protocol.a_eq_confirmation_time]
    exact Proofs.HealingSurface.confirmationTime_lt_nextVote_of_lt S.E
      (show S.hc.opening_slot r < d by
        dsimp only [d]
        exact Nat.lt_succ_self _)
  have hsources := actionSources_preceq_voteDutyHead_before_of_T1
    S rho b0 b1 hexec hcom hsleep hroundOne hT1 hd hdCap hx
  have htransport :=
    Proofs.HealingSurface.WeakJoint.relativeCarrierWindowAt_of_awakeWindowHistory_of_delivery
      S hexec.core hexec.healthy hcapHor (base := 0) (r := r)
      (D := Protocol.voteDutyHead S rho x d) hr (Nat.zero_le _) hawake
      (by
        intro k hkbase hklt u hu hemit
        exact (hsources k ((action_strictMono S) hklt |>.trans hsNext)).1
          u hu hemit)
      (by
        intro w hw
        exact ((hsources r hsNext).2 w hw).1)
      .g2 hdomainCap
  have hcarrierAt := Proofs.HealingSurface.relativeGradeCarrierAt_of_awakeWindowMajority
    S hexec.core hr hawake htransport
  obtain ⟨k, hk, u, hu, hemit, hrawCarrier⟩ :=
    hcarrierAt v hv raw (by
      simpa only [storeGrade, phaseGrade, PhaseGrades.readAt] using hgrade)
  exact ⟨k, Proofs.HealingSurface.mem_latestWindow_lt hk, u, hu, hemit, hrawCarrier⟩

#print axioms g2Grade_honestCarrier_before


/-- The strict-read index at `t ≤ cap` is at most the boundary index of `cap`,
and the strict read is that indexed prefix. -/
theorem strictRead_index_le_boundaryIdx
    (S : Setup V) (rho : NamedRun V)
    (sorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    {t cap : Time} (ht : t ≤ cap) :
    NamedRun.stateBeforeTime S rho t =
        NamedRun.stateBefore S rho
          (rho.events.filter (fun e => decide (e.time < t))).length ∧
      (rho.events.filter (fun e => decide (e.time < t))).length ≤ boundaryIdx rho cap :=
  ⟨strict_read_eq_index S rho sorted t, strict_length_le_boundary rho ht⟩

/-- A saved G2 root in the frame of a staged confirmation read at a support
cutoff of round `r > 0` is the clipped freeze of the reader's own G2-domain
tick, and that freeze root carries the store grade. -/
theorem stagedRead_g2_root_graded
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} (hr : 0 < r) {u : Time}
    (hu0 : (0 : Time) ≤ u) (hcut : u = Protocol.support_cutoff S.E (S.E.slotOf u))
    (hround : S.hc.round_of (S.E.slotOf u) = r)
    (hhor : domain S.E S.hc r .g2 ≤ rho.horizon)
    {raw : Block V}
    (hframe : (DecoupledConsensusModel.Protocol.readFrame
        (confirmationReadAt S rho v u).cache
        (confirmationReadAt S rho v u).st.core.toHealing r).g2 = some (some raw)) :
    ∃ raw0 : Block V,
      storeGrade S.E S.hc (readAt S rho (domain S.E S.hc r .g2) v).st r .g2 raw0 = true ∧
      Block.Preceq raw raw0 := by
  have hopen : opening S.E S.hc r < u := by
    have h := opening_lt_support_cutoff S u hu0 hcut
    simpa only [clockRoundAt, hround] using h
  have hstrict : u ≤ opening S.E S.hc (r + 1) := by
    have h := clockRound_lt_opening_succ S u
    simpa only [clockRoundAt, hround] using h.le
  have hg2dom : domain S.E S.hc r .g2 < opening S.E S.hc r := by
    have hd : domain S.E S.hc r .g2 = opening S.E S.hc r + (-1) * S.E.Δ := rfl
    rw [hd]
    have := S.E.Δ_pos
    linarith
  have hstrictFrame := FrameCompleted.frame_g2_completed_in_round S rho core v hv r hr u
    (lt_trans hg2dom hopen) hstrict hhor
  have hprep : phaseResult (DecoupledConsensusModel.Protocol.readFrame
      (confirmationReadAt S rho v u).cache
      (confirmationReadAt S rho v u).st.core.toHealing r) .g2 = some _ :=
    frame_phase_prepared_eq S rho v r .g2 u hround _ hstrictFrame
  have hg2 : some (some raw) = some ((freezeRoot S.E
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.F S.hc.η_SG r
      (early S.E S.hc r .g2) (late S.E S.hc r .g2)).map
        (fun B => clipGrade B (NamedRun.stateBeforeTime S rho u v).st.core.F)) := by
    rw [← hframe]
    exact hprep
  obtain ⟨raw0, hraw0, hclip⟩ := Option.map_eq_some_iff.mp (Option.some_inj.mp hg2).symm
  refine ⟨raw0, ?_, ?_⟩
  · have hmem := Proofs.Engine.deepest?_mem hraw0
    have hgraded := (Finset.mem_filter.mp hmem).2
    simpa only [storeGrade, phaseGrade, PhaseGrades.readAt] using hgraded
  · have h := clip_preceq raw0 (NamedRun.stateBeforeTime S rho u v).st.core.F
    rw [hclip] at h
    exact h

#print axioms stagedRead_g2_root_graded


/-- The height-pair row of an honest tick names that tick's FG witness. -/
theorem fgWitness_of_actionRow
    (S : Setup V) (rho : NamedRun V) (sch : NamedScheduleWellFormed S rho)
    {k : Nat} {a : NamedAttestation V} {J source : NamedBlock V}
    (hk : rho.events[k]? = some (.tick a.val_index (S.a a.round)))
    (hsel : Protocol.fg_source_with
        (NamedProfile.gradeContract
          (Internal.NamedOutageEntry.actionReadFrom S
            (NamedRun.stateBefore S rho k a.val_index) a.round).cache)
        S.E S.hc
        (Internal.NamedOutageEntry.actionReadFrom S
          (NamedRun.stateBefore S rho k a.val_index) a.round).st.core.toHealing
        a.round
        (Protocol.grade2_block_with
          (NamedProfile.gradeContract
            (Internal.NamedOutageEntry.actionReadFrom S
              (NamedRun.stateBefore S rho k a.val_index) a.round).cache)
          S.E S.hc
          (Internal.NamedOutageEntry.actionReadFrom S
            (NamedRun.stateBefore S rho k a.val_index) a.round).st.core.toHealing
          a.round) = some source.erase)
    (herase : J.erase = ((Internal.NamedOutageEntry.actionReadFrom S
        (NamedRun.stateBefore S rho k a.val_index) a.round).st.core.σ
        source.erase).T_h) :
    fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) = some J.erase := by
  have hstate : NamedRun.stateBefore S rho k a.val_index =
      NamedRun.stateBeforeTime S rho (S.a a.round) a.val_index :=
    Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S sch hk
  rw [hstate] at hsel herase
  have hround : S.hc.round_of
      (Internal.NamedOutageEntry.actionReadFrom S
        (NamedRun.stateBeforeTime S rho (S.a a.round) a.val_index)
          a.round).st.core.toHealing.s = a.round :=
    Proofs.HealingLemmas.round_of_slotOf_a S a.round
  show (Protocol.fg_source_with
      (NamedProfile.gradeContract
        (Internal.NamedOutageEntry.actionReadFrom S
          (NamedRun.stateBeforeTime S rho (S.a a.round) a.val_index) a.round).cache)
      S.E S.hc
      (Internal.NamedOutageEntry.actionReadFrom S
        (NamedRun.stateBeforeTime S rho (S.a a.round) a.val_index)
          a.round).st.core.toHealing
      (S.hc.round_of
        (Internal.NamedOutageEntry.actionReadFrom S
          (NamedRun.stateBeforeTime S rho (S.a a.round) a.val_index)
            a.round).st.core.toHealing.s)
      (Protocol.grade2_block_with
        (NamedProfile.gradeContract
          (Internal.NamedOutageEntry.actionReadFrom S
            (NamedRun.stateBeforeTime S rho (S.a a.round) a.val_index) a.round).cache)
        S.E S.hc
        (Internal.NamedOutageEntry.actionReadFrom S
          (NamedRun.stateBeforeTime S rho (S.a a.round) a.val_index)
            a.round).st.core.toHealing
        (S.hc.round_of
          (Internal.NamedOutageEntry.actionReadFrom S
            (NamedRun.stateBeforeTime S rho (S.a a.round) a.val_index)
              a.round).st.core.toHealing.s))).map
      (fun Cfg => ((Internal.NamedOutageEntry.actionReadFrom S
        (NamedRun.stateBeforeTime S rho (S.a a.round) a.val_index)
          a.round).st.core.σ Cfg).T_h) = some J.erase
  rw [hround, hsel, Option.map_some, herase]

#print axioms fgWitness_of_actionRow

/-- An honest action source of `X` before round `s`: an honest round-`k` SG
vote block (emitted) or FG witness extending `X`, with `k < s`. -/
def SourceBefore (S : Setup V) (rho : NamedRun V) (s : Round) (X : Block V) : Prop :=
  ∃ k, k < s ∧ ∃ x ∈ rho.honest,
    (NamedRun.emits S rho x (.attest (actionAttestationAt S rho x k)) (S.a k) ∧
      Block.Preceq X (actionSGBlockAt S rho x k)) ∨
    (∃ T, fgConfirmationWitness S (actionStoreAt S rho x k) = some T ∧ Block.Preceq X T)

/-- Every honest Goldfish head at the opening slot of round `s` extends an
honest action source of an earlier round. -/
theorem sourceBefore_preceq_openingHeads
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (s : Round) (hs : 0 < s) (hmargin : FormationMargin S s b0)
    {X : Block V} (hsrc : SourceBefore S rho s X) :
    ∀ y ∈ rho.honest, Block.Preceq X (voterHeadAt S rho y (S.hc.opening_slot s)) := by
  intro y hy
  have hasCap : S.a s ≤ b0 :=
    (Assembly.a_mono S (Nat.le_succ s)).trans
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin)
  have hroundOne : domain S.E S.hc 1 .g2 ≤ b0 := by
    exact (FrameForward.domain_le_a S 1 .g2).trans
      ((Assembly.a_mono S (Nat.succ_le_succ (Nat.zero_le s))).trans
        ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin))
  have hT1 := protectedVoteSlots_before S rho b0 b1 hexec hcom hsleep hroundOne
  let d := S.hc.opening_slot s
  have hd : 1 ≤ d := by
    dsimp only [d, Protocol.HealConfig.opening_slot]
    exact Nat.mul_pos hs (Nat.zero_lt_of_lt S.hc.R_ge_two)
  have hdCap : Protocol.vote_time S.E d + S.E.Δ ≤ b0 := by
    rw [Proofs.Optimistic.vote_time_add_delta]
    exact (Protocol.support_cutoff_le_confirmation_time S.E d).trans
      (by simpa only [d, Proofs.HealingSurface.opening_confirmation_time_eq_action] using hasCap)
  have hsources := actionSources_preceq_voteDutyHead_before_of_T1
    S rho b0 b1 hexec hcom hsleep hroundOne hT1 hd hdCap hy
  obtain ⟨k, hk, x, hx, hsrc⟩ := hsrc
  have hkTime : S.a k < Protocol.vote_time S.E (d + 1) := by
    have hk' : k ≤ s - 1 := Nat.le_sub_one_of_lt hk
    have h1 : S.a k ≤ S.a (s - 1) := Assembly.a_mono S hk'
    have h2 : S.a (s - 1) < Protocol.vote_time S.E (d + 1) := by
      rw [Setup.a, Protocol.a_eq_confirmation_time]
      exact Proofs.HealingSurface.confirmationTime_lt_nextVote_of_lt S.E
        (show S.hc.opening_slot (s - 1) < d by
          dsimp only [d, Protocol.HealConfig.opening_slot]
          exact Nat.mul_lt_mul_of_pos_right (Nat.sub_lt hs Nat.one_pos)
            (Nat.zero_lt_of_lt S.hc.R_ge_two))
    exact lt_of_le_of_lt h1 h2
  rcases hsrc with ⟨hemit, hX⟩ | ⟨T, hT, hX⟩
  · exact Block.preceq_trans hX ((hsources k hkTime).1 x hx hemit)
  · exact Block.preceq_trans hX (((hsources k hkTime).2 x hx).2 T hT)

#print axioms sourceBefore_preceq_openingHeads


omit [DecidableEq V] [Fintype V] in
/-- Events before the strict-read index at `t` happen before `t`. -/
theorem time_lt_of_lt_strictIdx (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (t : Time)
    {j : Nat} {e : NamedEvent V}
    (hj : j < (rho.events.filter (fun e => decide (e.time < t))).length)
    (he : rho.events[j]? = some e) : e.time < t := by
  have hdown : ∀ e f : NamedEvent V, e.key ≤ f.key →
      decide (f.time < t) = true → decide (e.time < t) = true := by
    intro e f hkey hf
    simp only [decide_eq_true_eq] at hf ⊢
    have hle : e.time ≤ f.time := by
      rcases Prod.Lex.le_iff.mp hkey with hlt | ⟨heq, _⟩
      · exact hlt.le
      · exact heq.le
    exact hle.trans_lt hf
  have hf : rho.events.filter (fun e => decide (e.time < t)) =
      rho.events.take (rho.events.filter (fun e => decide (e.time < t))).length := by
    refine List.prefix_iff_eq_take.mp ?_
    rw [Proofs.Bridges.filter_eq_takeWhile_of_pairwise hdown _ hsorted]
    exact List.takeWhile_prefix _
  have hm : e ∈ rho.events.filter (fun e => decide (e.time < t)) := by
    rw [hf]
    exact List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hj]; exact he)
  simpa only [decide_eq_true_eq] using (List.mem_filter.mp hm).2

/-! ## 2. The stable output has a source before its round -/

/-- A prefix of an honest node's stable output at the round-`s` action is on the
joint history chain, and is genesis or extends an honest action source of an
earlier round. -/
theorem stableOutput_sourceBefore_at
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (v : V) (hv : v ∈ rho.honest) (s : Round) (T : Time) (hTs : T ≤ S.a s)
    (hmargin : FormationMargin S s b0)
    (C : NamedBlock V)
    (hhistory : LayerAJointHistoryIdxEmitted S rho (boundaryIdx rho b0) C)
    (P : Block V)
    (hP : Block.Preceq P (Protocol.get_stable (Run.storeAt S rho v T).core)) :
    Block.Preceq P C.erase ∧ (P = Block.genesis ∨ SourceBefore S rho s P) := by
  have hcap : b0 ≤ rho.horizon := hexec.interval.2.1.trans hexec.interval.2.2
  have hasCap : S.a s ≤ b0 :=
    (Assembly.a_mono S (Nat.le_succ s)).trans
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin)
  have hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q :=
    Proofs.NamedOutageInputs.boundary_faulty_lt_quorum S rho b0 b1 s hexec hmargin hsleep
  have sorted := hexec.core.sorted
  have sch := hexec.core.toNamedScheduleWellFormed
  have hgen : ∀ {X : Block V}, Block.Preceq X Block.genesis → X = Block.genesis := by
    intro X h
    simpa only [Block.Preceq, Block.preceq, decide_eq_true_eq] using h
  have hgenC : Block.Preceq Block.genesis C.erase := Protocol.preceq_genesis _
  have hcases : Block.Preceq P (Run.storeAt S rho v T).core.latest_stable ∨
      Block.Preceq P (Run.storeAt S rho v T).core.F := by
    unfold Protocol.get_stable at hP
    split_ifs at hP with hFL
    · exact Or.inl hP
    · exact Or.inr hP
  -- the round bound of a source tick strictly before a time `≤ S.a s`
  have hroundLt : ∀ {k : Round} {t : Time}, S.a k < t → t ≤ S.a s → k < s := by
    intro k t hkt hts
    by_contra hnot
    have hle : s ≤ k := Nat.le_of_not_lt hnot
    have := Assembly.a_mono S hle
    linarith
  rcases hcases with hrec | hfin
  · -- record arm
    obtain ⟨n, hstore, horigin⟩ :=
      stableOutput_inclusive_record_origin_at S rho v T sorted
    rw [hstore] at hrec
    rcases horigin with hgenesis | ⟨i, hi, time, hiTime, hTimeT, hpos, hcut, hroot⟩
    · have hPg : P = Block.genesis := hgen (by rw [← hgenesis]; exact hrec)
      exact ⟨by rw [hPg]; exact hgenC, Or.inl hPg⟩
    have hTime : time ≤ S.a s := hTimeT.trans hTs
    obtain ⟨r, hrdef⟩ : ∃ r : Round, r = S.hc.round_of (S.E.slotOf time) := ⟨_, rfl⟩
    have hr : r ≤ s := by
      rw [hrdef]
      exact stableRoot_origin_round_le S s hTime hpos hcut
    obtain ⟨time', hiTime', -, -, harms⟩ := stableOutput_frameStableRoot_split S rho v i hroot
    have htt : time' = time := by
      have h := hiTime'.symm.trans hiTime
      exact (NamedEvent.tick.inj (Option.some.inj h)).2
    subst htt
    have hstate : Run.stateBefore S rho i v = NamedRun.stateBeforeTime S rho time' v :=
      Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S sch hiTime
    rw [hstate] at harms
    have ht0 : (0 : Time) ≤ time' := (sch.in_horizon _ (List.mem_of_getElem? hiTime)).1
    have hround : S.hc.round_of (S.E.slotOf time') = r := hrdef.symm
    have htb0 : time' ≤ b0 := hTime.trans hasCap
    rcases harms with ⟨raw, hg2, hactive⟩ | hfg
    · -- a frozen G2 root: its freeze has the store grade at the origin round
      have hs' : (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBeforeTime S rho time' v) time').st.core.s = S.E.slotOf time' := rfl
      have hg2' : (DecoupledConsensusModel.Protocol.readFrame
          (confirmationReadAt S rho v time').cache
          (confirmationReadAt S rho v time').st.core.toHealing r).g2 = some (some raw) := by
        have h := hg2
        rw [hs', hround] at h
        exact h
      rcases Nat.eq_zero_or_pos r with hr0 | hrpos
      · exfalso
        subst hr0
        exact stagedRead_g2_round_zero_no_root S hexec.core v time' ht0 hround hg2'
      have hhor : domain S.E S.hc r .g2 ≤ rho.horizon :=
        (FrameForward.domain_le_a S r .g2).trans
          ((Assembly.a_mono S hr).trans (hasCap.trans hcap))
      obtain ⟨raw0, hgrade, hrawraw0⟩ :=
        stagedRead_g2_root_graded S rho hexec.core hv hrpos ht0 hcut hround hhor hg2'
      have hmarginR : FormationMargin S r b0 :=
        (Int.add_le_add_right (Assembly.a_mono S (Nat.succ_le_succ hr)) _).trans hmargin
      have hG : Block.Preceq
          (rho.stateBefore S n v).st.core.latest_stable raw :=
        (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).2
      have hPraw0 : Block.Preceq P raw0 :=
        Block.preceq_trans (Block.preceq_trans hrec hG) hrawraw0
      have hC := stableRaw_preceq_prefixHistory S rho b0 b1 hexec hcom hsleep
        r hrpos hmarginR v hv raw0 hgrade C hhistory
      obtain ⟨k, hkr, x, hx, hemit, hcar⟩ :=
        g2Grade_honestCarrier_before S rho b0 b1 hexec hcom hsleep r hrpos hmarginR v hv raw0 hgrade
      exact ⟨Block.preceq_trans hPraw0 hC,
        Or.inr ⟨k, lt_of_lt_of_le hkr hr, x, hx, Or.inl ⟨hemit, Block.preceq_trans hPraw0 hcar⟩⟩⟩
    · -- the FG root: below the justified block of the strict read
      have hrec' : Block.Preceq P (Run.stateBefore S rho n v).st.latest_stable := hrec
      rw [hfg] at hrec'
      have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho time' v
      have hPJ : Block.Preceq P (NamedRun.stateBeforeTime S rho time' v).st.core.J := by
        change Block.Preceq P
          (if (NamedRun.stateBeforeTime S rho time' v).st.core.h_max =
              (NamedRun.stateBeforeTime S rho time' v).st.core.h_j + 1 then
            (NamedRun.stateBeforeTime S rho time' v).st.core.J
          else (NamedRun.stateBeforeTime S rho time' v).st.core.F) at hrec'
        have hPG := hrec'
        split_ifs at hPG with hcase
        · exact hPG
        · exact Block.preceq_trans hPG (by
            simpa only [Protocol.Store.toHealing] using hFJ)
      have hidx := strict_read_eq_index S rho sorted time'
      have hi'n : (rho.events.filter (fun e => decide (e.time < time'))).length ≤
          boundaryIdx rho b0 := strict_length_le_boundary rho htb0
      rw [hidx] at hPJ
      rcases NamedOutageHistory.HistoryProofs.justification_honest_fgRow S rho hexec.core
          (boundaryIdx rho b0) C hhistory.1.1 _ v hv hi'n hbad with
        hJgen | ⟨k, a, J, source, ha, hki, hk, hemit, -, hJe, hJC, hsel, herase⟩
      · have hPg : P = Block.genesis := hgen (by rw [← hJgen]; exact hPJ)
        exact ⟨by rw [hPg]; exact hgenC, Or.inl hPg⟩
      have hPJe : Block.Preceq P J.erase := by rw [hJe]; exact hPJ
      refine ⟨Block.preceq_trans hPJe (Proofs.NamedWire.erase_preceq hJC), Or.inr ?_⟩
      have hwit := fgWitness_of_actionRow S rho sch hk hsel herase
      have htk : S.a a.round < time' := by
        have h := time_lt_of_lt_strictIdx rho sorted time' hki hk
        simpa only [NamedEvent.time] using h
      exact ⟨a.round, hroundLt htk hTime, a.val_index, ha, Or.inr ⟨J.erase, hwit, hPJe⟩⟩
  · -- finalized arm: the inclusive read is the strict read one instant later
    have hincl : Run.storeAt S rho v T =
        (NamedRun.stateBeforeTime S rho (T + 1) v).st := by
      unfold Run.storeAt
      rw [readAt_eq_succ]
    rw [hincl] at hfin
    have hsb : T + 1 ≤ b0 := by
      have h1 : S.a s < S.a (s + 1) := action_strictMono S (Nat.lt_succ_self s)
      have h2 := S.E.Δ_pos
      have h3 : S.a (s + 1) + S.E.Δ ≤ b0 := hmargin
      have h4 : T + 1 ≤ S.a (s + 1) := Int.add_one_le_iff.mpr (hTs.trans_lt h1)
      exact h4.trans ((lt_add_of_pos_right _ h2).le.trans h3)
    have hidx := strict_read_eq_index S rho sorted (T + 1)
    have hi'n : (rho.events.filter (fun e => decide (e.time < T + 1))).length ≤
        boundaryIdx rho b0 := strict_length_le_boundary rho hsb
    rw [hidx] at hfin
    rcases NamedOutageHistory.HistoryProofs.finalized_honest_fgRow S rho hexec.core
        (boundaryIdx rho b0) C hhistory.1.1 _ v hv hi'n hbad with
      hFgen | ⟨k, a, J, source, ha, hki, hk, hemit, -, hJe, hJC, hsel, herase,
        ka, xa, ra, hka, hkaTick, hlt⟩
    · have hPg : P = Block.genesis := hgen (by rw [← hFgen]; exact hfin)
      exact ⟨by rw [hPg]; exact hgenC, Or.inl hPg⟩
    have hPJe : Block.Preceq P J.erase := by rw [hJe]; exact hfin
    refine ⟨Block.preceq_trans hPJe (Proofs.NamedWire.erase_preceq hJC), Or.inr ?_⟩
    have hwit := fgWitness_of_actionRow S rho sch hk hsel herase
    have hra : S.a ra < T + 1 := by
      have h := time_lt_of_lt_strictIdx rho sorted (T + 1) hka hkaTick
      simpa only [NamedEvent.time] using h
    have hks : a.round < s := by
      by_contra hnot
      have hle : s ≤ a.round := Nat.le_of_not_lt hnot
      have hsa : S.a s ≤ S.a a.round := Assembly.a_mono S hle
      have hras : S.a ra ≤ T := Int.lt_add_one_iff.mp hra
      exact absurd (hsa.trans_lt (hlt.trans_le (hras.trans hTs))) (lt_irrefl _)
    exact ⟨a.round, hks, a.val_index, ha, Or.inr ⟨J.erase, hwit, hPJe⟩⟩

#print axioms stableOutput_sourceBefore_at

/-- The round-action instance: the output at the round-`s` action itself. -/
theorem stableOutput_sourceBefore
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (v : V) (hv : v ∈ rho.honest) (s : Round)
    (hmargin : FormationMargin S s b0)
    (C : NamedBlock V)
    (hhistory : LayerAJointHistoryIdxEmitted S rho (boundaryIdx rho b0) C)
    (P : Block V)
    (hP : Block.Preceq P (Protocol.get_stable (Run.storeAt S rho v (S.a s)).core)) :
    Block.Preceq P C.erase ∧ (P = Block.genesis ∨ SourceBefore S rho s P) :=
  stableOutput_sourceBefore_at S rho b0 b1 hexec hcom hsleep v hv s (S.a s) (le_refl _)
    hmargin C hhistory P hP

#print axioms stableOutput_sourceBefore


/-! ## 3. The seed: carriers, no conflict, and heads from the stable output -/

/-- No honest conflict above any block on the joint history chain. -/
theorem noHonestConflictAbove_of_preceq_history
    (S : Setup V) (rho : NamedRun V) (b0 : Time)
    (core : NamedAdmissibleCore S rho) (C : NamedBlock V)
    (hhistory : LayerAJointHistoryIdxEmitted S rho (boundaryIdx rho b0) C)
    (P : Block V) (hPC : Block.Preceq P C.erase) :
    NoHonestConflictAbove S rho b0 P := by
  obtain ⟨Pn, hPnC, hPnErase⟩ :=
    NamedOutageHistory.ReadyHeadReturn.named_ancestor_of_erase P C hPC
  have hPnRun : NamedRun.blockInRun S rho Pn :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hhistory.1.1.1 hPnC
  have hno := noHonestConflictAbove_of_commonPrefixHistory
    S rho b0 core C Pn hhistory.1 hPnRun hPnC
  simpa only [hPnErase] using hno

theorem outputSeed_of_stableAt
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s : Round) (P : Block V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : NamedOutageEntry.SlashableBound S rho)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hstable : stableAt S rho v s P) (hs : 0 < s) :
    OutputSeed S rho b0 s P := by
  have hcarriers := stableAt_honestCarriersAbove_sameRound
    S rho b0 b1 v s P hexec hslash hcom hsleep hforming hv hmargin hstable hs
  have hno := noHonestConflictAbove_of_carrierFloor_export
    S rho b0 b1 v s P hexec hcom hsleep hforming hv hmargin hstable hcarriers
  have hanchor := stableAt_raw_preceq_actionAnchor
    S rho b0 b1 v s P hexec hslash hcom hsleep hforming hv hmargin hstable hs
  obtain ⟨G, raw, hPG, hGraw, hrawAnchor⟩ := hanchor
  have hheads : ∀ w ∈ rho.honest,
      Block.Preceq P (voterHeadAt S rho w (S.hc.opening_slot s)) := by
    have hopen := stableAt_openingHeads_above_confirmationAnchors
      S rho b0 b1 v s P hexec hslash hcom hsleep hforming hv hmargin hstable hs
    intro w hw
    have hPA : Block.Preceq P
        (nodeAnchor S (Proofs.HealingSurface.actionReadAt S rho w s) s) :=
      Block.preceq_trans hPG (Block.preceq_trans hGraw (hrawAnchor w hw))
    have hAnchorHead := hopen w hw w hw
    rw [actionAnchor_eq_openingConfirmationAnchor_export] at hPA
    exact Block.preceq_trans hPA hAnchorHead
  have hheld := held_of_preceq_openingHeads S rho b0 b1 s hexec P hheads
  have hhor : S.a s ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_succ s)).trans
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
        (hmargin.trans (hexec.interval.2.1.trans hexec.interval.2.2)))
  have hhistory : ∀ C : NamedBlock V,
      LayerAJointHistoryIdxEmitted S rho (boundaryIdx rho b0) C →
        Block.Preceq P C.erase := by
    intro C hC
    obtain ⟨G', raw', -, hgrade, hPG', hGraw'⟩ :=
      stableAt_rawG2_grade S rho v s P hexec.core hv hs hhor hstable
    have hrawC := stableRaw_preceq_prefixHistory
      S rho b0 b1 hexec hcom hsleep s hs hmargin v hv raw' hgrade C hC
    exact Block.preceq_trans (Block.preceq_trans hPG' hGraw') hrawC
  exact ⟨hheads, hno, hcarriers, hheld, hhistory⟩

#print axioms outputSeed_of_stableAt

/-- **T_out seed.** Every block below an honest node's stable output at the
round-`s` action carries the seed. -/
theorem stableOutput_seed_at
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (v : V) (hv : v ∈ rho.honest) (s : Round) (hs : 0 < s) (T : Time) (hTs : T ≤ S.a s)
    (hmargin : FormationMargin S s b0)
    (P : Block V)
    (hP : Block.Preceq P (Protocol.get_stable (Run.storeAt S rho v T).core)) :
    OutputSeed S rho b0 s P := by
  have hroundOne : domain S.E S.hc 1 .g2 ≤ b0 :=
    (FrameForward.domain_le_a S 1 .g2).trans
      ((Assembly.a_mono S (Nat.succ_le_succ (Nat.zero_le s))).trans
        ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin))
  have hT1 := protectedVoteSlots_before S rho b0 b1 hexec hcom hsleep hroundOne
  have hconf := namedConfirmationIdxQueryEmitted_of_healthyPrefix_of_T1
    S rho b0 b1 hexec hcom hsleep hroundOne hT1
  obtain ⟨C, hhistory⟩ :=
    NamedOutageHistory.OutageEnv.layerA_joint_history_idx_emitted_of_outage
      S rho b0 b1 s hexec hsleep hmargin hcom hconf (boundaryIdx rho b0) (le_refl _)
  obtain ⟨hPC, hsrc⟩ :=
    stableOutput_sourceBefore_at S rho b0 b1 hexec hcom hsleep v hv s T hTs hmargin C hhistory P hP
  have hno := noHonestConflictAbove_of_preceq_history S rho b0 hexec.core C hhistory P hPC
  have hheads : ∀ w ∈ rho.honest,
      Block.Preceq P (voterHeadAt S rho w (S.hc.opening_slot s)) := by
    rcases hsrc with hgen | hsrc
    · subst hgen
      exact fun w _ => Protocol.preceq_genesis _
    · exact sourceBefore_preceq_openingHeads S rho b0 b1 hexec hcom hsleep s hs hmargin hsrc
  refine ⟨hheads, hno, ?_, held_of_preceq_openingHeads S rho b0 b1 s hexec P hheads, ?_⟩
  · exact honestCarriersAbove_of_preceq_openingHeads S rho b0 b1 s hexec hcom hsleep hforming
      hmargin hs P hno hheads
  · intro C' hhistory'
    exact (stableOutput_sourceBefore_at S rho b0 b1 hexec hcom hsleep v hv s T hTs hmargin
      C' hhistory' P hP).1

#print axioms stableOutput_seed_at

/-- The round-action instance of the seed. -/
theorem stableOutput_seed
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (v : V) (hv : v ∈ rho.honest) (s : Round) (hs : 0 < s)
    (hmargin : FormationMargin S s b0)
    (P : Block V)
    (hP : Block.Preceq P (Protocol.get_stable (Run.storeAt S rho v (S.a s)).core)) :
    OutputSeed S rho b0 s P :=
  stableOutput_seed_at S rho b0 b1 hexec hcom hsleep hforming v hv s hs (S.a s) (le_refl _)
    hmargin P hP

/-! ## 4. The schedule in time terms -/

theorem a_eq_roundLength (S : Setup V) (s : Round) :
    S.a s = 6 * S.E.Δ + roundLength S * (s : Time) := by
  simp only [Setup.a, Protocol.HealConfig.a, Protocol.HealConfig.opening_slot, slotStart,
    roundLength]
  push_cast
  ring

theorem roundLength_pos (S : Setup V) : 0 < roundLength S := by
  unfold roundLength
  have hR : (0 : Time) < (S.hc.R : Time) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two
  have hΔ := S.E.Δ_pos
  positivity

theorem a_succ_roundLength (S : Setup V) (s : Round) :
    S.a (s + 1) = S.a s + roundLength S := by
  rw [a_eq_roundLength, a_eq_roundLength]
  push_cast
  ring

theorem early_g2_eq (S : Setup V) (r : Round) :
    early S.E S.hc r .g2 = S.a r - 11 * S.E.Δ := by
  simp only [early, opening, Protocol.proposal_time, Env.t, slotStart, Setup.a,
    Protocol.HealConfig.a, Protocol.HealConfig.opening_slot, Phase.earlyOffset]
  push_cast
  ring

/-- `T` is at or before the first round action at or after it. -/
theorem le_nextAction (S : Setup V) (T : Time) : T ≤ nextAction S T := by
  unfold nextAction roundAfter
  rw [a_eq_roundLength]
  have hL := roundLength_pos S
  set L := roundLength S with hLdef
  set x := T - 6 * S.E.Δ + L - 1 with hx
  set q := Int.ediv x L with hq
  have hlt : x < (q + 1) * L := Int.lt_ediv_add_one_mul_self x hL
  rcases le_or_gt 0 q with hq0 | hq0
  · have hcast : ((q.toNat : Nat) : Time) = q := Int.toNat_of_nonneg hq0
    rw [hcast]
    have : x < q * L + L := by rw [add_mul, one_mul] at hlt; exact hlt
    have h1 : T - 6 * S.E.Δ + L - 1 < q * L + L := this
    have h2 : T - 6 * S.E.Δ - 1 < q * L := by linarith
    have h3 : T - 6 * S.E.Δ ≤ q * L := Int.lt_add_one_iff.mp (by linarith)
    linarith [mul_comm q L]
  · have hcast : ((q.toNat : Nat) : Time) = 0 := by
      rw [Int.toNat_eq_zero.mpr hq0.le]
      rfl
    rw [hcast]
    have hxneg : x < 0 := by
      by_contra hnn
      have hnn' : 0 ≤ x := not_lt.mp hnn
      exact absurd (Int.ediv_nonneg hnn' hL.le) (not_le.mpr hq0)
    have hL1 : (1 : Time) ≤ L := hL
    simp only [mul_zero, add_zero]
    linarith

theorem formationMargin_of_time (S : Setup V) (T b0 : Time)
    (h : nextAction S T + roundLength S + S.E.Δ ≤ b0) :
    FormationMargin S (roundAfter S T) b0 := by
  unfold FormationMargin
  rw [a_succ_roundLength]
  exact h

theorem retentionDuration_of_time (S : Setup V) (rho : NamedRun V) (T b1 : Time)
    (h1 : b1 + S.E.Δ ≤ nextAction S T + ((S.hc.η_SG : Time) + 1) * roundLength S - 11 * S.E.Δ)
    (h2 : b1 + S.E.Δ ≤ rho.horizon) :
    RetentionDuration S rho (roundAfter S T) b1 := by
  refine ⟨?_, h2⟩
  rw [early_g2_eq, a_eq_roundLength]
  unfold nextAction at h1
  rw [a_eq_roundLength] at h1
  push_cast at h1 ⊢
  linarith

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
