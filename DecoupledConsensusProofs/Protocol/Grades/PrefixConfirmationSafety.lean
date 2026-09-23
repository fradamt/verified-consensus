module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.BoundedChainPrebuild
public import DecoupledConsensusProofs.Protocol.Grades.ClaimOneClauseProducers
public import DecoupledConsensusProofs.Protocol.Grades.OutageEnvEmitted

@[expose] public section

/-!
# Confirmation safety in the healthy outage prefix

This module follows the GST-zero selection-chain argument in
`HealingSurface/WeakGenesisSelectionChainRun.lean`, but uses the outage's
healthy-prefix delivery and sleepy-window majority. The first theorem closes
the protocol-selection part of S1. The read-field lift is kept separate
because `latest_confirmed` also absorbs the stable write and the optional
frame-Q2 candidate.
-/

namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Internal Execution Internal.NamedOutageEntry
open Internal.HealingSurface Internal.PhaseGrades
open Internal.NamedOutageEntry.History Internal.NamedStableChainOutage
open DecoupledConsensusModel.Protocol
open Proofs.HealingSurface Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]





/-- S2 in history form: every nonempty height target and every finality target
of an honest row before the boundary is a prefix of the healthy confirmation
history endpoint. Timeout height rows use the same source entry as target
rows, so both Boolean arms are covered by the height clause. -/
theorem prefixHonestRowTargets_preceq_history
    (S : Setup V) (rho : NamedRun V) (b0 : Time) (C : NamedBlock V)
    (core : NamedAdmissibleCore S rho)
    (hhistory : LayerAJointHistoryIdx S rho (boundaryIdx rho b0) C) :
    (forall (a : NamedAttestation V) (t : Time),
      a.val_index ∈ rho.honest → NamedRun.emits S rho a.val_index (.attest a) t →
      t < b0 → forall h root timeout, a.height_pair = .vote h root timeout →
      forall entry : NamedBlock V, NamedRun.blockInRun S rho entry →
        entry.root = root → NamedBlock.Preceq entry C) ∧
    (forall (a : NamedAttestation V) (t : Time),
      a.val_index ∈ rho.honest → NamedRun.emits S rho a.val_index (.attest a) t →
      t < b0 → forall h root, a.finality_pair = some ⟨h, root⟩ →
      forall entry : NamedBlock V, NamedRun.blockInRun S rho entry →
        entry.root = root → NamedBlock.Preceq entry C) := by
  constructor
  · intro a t ha hemit ht h root timeout hpair entry hentry hroot
    obtain ⟨i, hi, himem⟩ := hemit
    have hib : i < boundaryIdx rho b0 :=
      tick_index_lt_boundaryIdx rho core.sorted hi (by
          simpa only [NamedEvent.time] using ht)
    obtain ⟨source, entry', -, -, hentryRun, -, -, -, -, -, -, -, -, -, -, _,
        hentryRoot, hentryC⟩ :=
      hhistory.1.2.2.1 i a.val_index t a ha hi himem hib h root timeout hpair
    have hentryEq : entry = entry' := by
      exact core.toNamedRootCollisionFree.root_injective entry C hentry
        hhistory.1.1 entry entry'
          (Or.inl (Proofs.NamedAncestry.named_self entry)) (Or.inr hentryC)
          (hroot.trans hentryRoot.symm)
    simpa only [hentryEq] using hentryC
  · intro a t ha hemit ht h root hpair entry hentry hroot
    obtain ⟨i, hi, himem⟩ := hemit
    have hib : i < boundaryIdx rho b0 :=
      tick_index_lt_boundaryIdx rho core.sorted hi (by
        simpa only [NamedEvent.time] using ht)
    obtain ⟨H, entry', -, -, -, hentryRun, -, -, -, -, -, -, -, -, -, _,
        hentryRoot, hentryC⟩ :=
      hhistory.1.2.1 i a.val_index t a ha hi himem hib ⟨h, root⟩ hpair
    have hentryEq : entry = entry' := by
      exact core.toNamedRootCollisionFree.root_injective entry C hentry
        hhistory.1.1 entry entry'
          (Or.inl (Proofs.NamedAncestry.named_self entry)) (Or.inr hentryC)
          (hroot.trans hentryRoot)
    simpa only [hentryEq] using hentryC

#print axioms prefixHonestRowTargets_preceq_history

set_option maxHeartbeats 400000 in
/-- The stable raw G2 root is a prefix of the healthy confirmation-history
endpoint. The grade's honest supporter supplies an emitted SG confirmed head;
the emission-backed history puts that head below its endpoint. -/
theorem stableRaw_preceq_prefixHistory
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (s : Round) (hs : 0 < s) (hmargin : FormationMargin S s b0)
    (v : V) (hv : v ∈ rho.honest) (raw : Block V)
    (hgrade : storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc s .g2) v).st s .g2 raw = true)
    (C : NamedBlock V)
    (hhistory : LayerAJointHistoryIdxEmitted S rho (boundaryIdx rho b0) C) :
    Block.Preceq raw C.erase := by
  have hcapHor : b0 ≤ rho.horizon :=
    hexec.interval.2.1.trans hexec.interval.2.2
  have hasCap : S.a s ≤ b0 :=
    (Assembly.a_mono S (Nat.le_succ s)).trans
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin)
  have hdomainCap : domain S.E S.hc s .g2 ≤ b0 :=
    (FrameForward.domain_le_a S s .g2).trans hasCap
  have hcovered : RoundCovered S rho s :=
    Or.inr ⟨.g2, NamedOutageHistory.OutageEnv.domain_g2_nonneg S hs,
      hdomainCap.trans hcapHor⟩
  have hawake : AwakeWindowMajority S.E (fun u => (S.node u).awake)
      rho.honest S.hc.η_SG s :=
    hsleep s hs hcovered
  have hroundOne : domain S.E S.hc 1 .g2 ≤ b0 := by
    exact (FrameForward.domain_le_a S 1 .g2).trans
      ((Assembly.a_mono S (Nat.succ_le_succ (Nat.zero_le s))).trans
        ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin))
  have hT1 := protectedVoteSlots_before
    S rho b0 b1 hexec hcom hsleep hroundOne
  obtain ⟨x, hx⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
  let d := S.hc.opening_slot s + 1
  have hd : 1 ≤ d := by
    dsimp only [d]
    exact Nat.succ_le_succ (Nat.zero_le _)
  have hdCap : Protocol.vote_time S.E d + S.E.Δ ≤ b0 := by
    dsimp only [d]
    rw [Protocol.vote_time_succ_add_delta_eq_confirmation_time,
      ← Protocol.a_eq_confirmation_time S.hc S.E s]
    exact hasCap
  have hsNext : S.a s < Protocol.vote_time S.E (d + 1) := by
    rw [Setup.a, Protocol.a_eq_confirmation_time]
    exact Proofs.HealingSurface.confirmationTime_lt_nextVote_of_lt S.E
      (show S.hc.opening_slot s < d by
        dsimp only [d]
        exact Nat.lt_succ_self _)
  have hsources := actionSources_preceq_voteDutyHead_before_of_T1
    S rho b0 b1 hexec hcom hsleep hroundOne hT1 hd hdCap hx
  have htransport :=
    Proofs.HealingSurface.WeakJoint.relativeCarrierWindowAt_of_awakeWindowHistory_of_delivery
      S hexec.core hexec.healthy hcapHor (base := 0) (r := s)
      (D := Protocol.voteDutyHead S rho x d) hs (Nat.zero_le _) hawake
      (by
        intro k hkbase hklt u hu hemit
        exact (hsources k ((action_strictMono S) hklt |>.trans hsNext)).1
          u hu hemit)
      (by
        intro w hw
        exact ((hsources s hsNext).2 w hw).1)
      .g2 hdomainCap
  have hcarrierAt := Proofs.HealingSurface.relativeGradeCarrierAt_of_awakeWindowMajority
    S hexec.core hs hawake htransport
  obtain ⟨k, hk, u, hu, hemit, hrawCarrier⟩ :=
    hcarrierAt v hv raw (by
      simpa only [storeGrade, phaseGrade, PhaseGrades.readAt] using hgrade)
  obtain ⟨i, hi, himem⟩ := hemit
  have hks : k < s := Proofs.HealingSurface.mem_latestWindow_lt hk
  have hasb0 : S.a s < b0 :=
    (NamedOutageHistory.JointHistoryGapsTime.setup_a_strictMono S
      (Nat.lt_succ_self s)).trans_le
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin)
  have hkCap : S.a k < b0 := ((action_strictMono S) hks).trans hasb0
  have hibound : i < boundaryIdx rho b0 :=
    tick_index_lt_boundaryIdx rho hexec.core.sorted hi
      (by simpa only [NamedEvent.time] using hkCap)
  let a := actionAttestationAt S rho u k
  have hconfirmed : a.confirmed = some (actionSGBlockAt S rho u k).root := by
    exact (actionAttestationAt_shape S rho u k).2.2
  obtain ⟨K, hKrun, hKbody, hKroot, hKC⟩ :=
    hhistory.1.2.1 i u (S.a k) a hu hi himem hibound
      (actionSGBlockAt S rho u k).root hconfirmed
  have hcarrierMem : actionSGBlockAt S rho u k ∈
      (NamedRun.stateBeforeTime S rho (S.a k) u).st.core.T :=
    actionSGBlockAt_mem_storeBeforeTime S rho u k
  obtain ⟨D, hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (S.a k) u hcarrierMem
  obtain ⟨m, hm, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
    S rho hexec.core.sorted (S.a k)
  have hDprefix : D ∈ (NamedRun.stateBefore S rho m u).st.bodies := by
    rw [← hm]
    exact hDbody
  have hDrun : NamedRun.blockInRun S rho D :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hu hDprefix
  have hDKroot : D.root = K.root := by
    rw [← Proofs.NamedWire.erase_root D, hDerase]
    exact hKroot.symm
  have hDK : D = K :=
    hexec.core.toNamedRootCollisionFree.root_injective D K hDrun hKrun D K
      (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (NamedOutageHistory.JointHistoryProducersTime.named_preceq_self K))
      hDKroot
  have hKe : K.erase = actionSGBlockAt S rho u k := by
    rw [← hDK, hDerase]
  exact Block.preceq_trans (by simpa only [hKe] using hrawCarrier)
    (Proofs.NamedWire.erase_preceq hKC)

#print axioms stableRaw_preceq_prefixHistory

set_option maxHeartbeats 400000 in
/-- S3 from a common prefix-confirmation endpoint. Both the protected block
and each honest row target are prefixes of `C`; compatibility follows from
`Block.compatible_of_preceq_common` and root-collision-free lifting. -/
theorem noHonestConflictAbove_of_commonPrefixHistory
    (S : Setup V) (rho : NamedRun V) (b0 : Time)
    (core : NamedAdmissibleCore S rho) (C Pn : NamedBlock V)
    (hhistory : LayerAJointHistoryIdx S rho (boundaryIdx rho b0) C)
    (hPnrun : NamedRun.blockInRun S rho Pn)
    (hPnC : NamedBlock.Preceq Pn C) :
    NoHonestConflictAbove S rho b0 Pn.erase := by
  have hrows := prefixHonestRowTargets_preceq_history
    S rho b0 C core hhistory
  have compatible_of_common {entry : NamedBlock V}
      (hentryRun : NamedRun.blockInRun S rho entry)
      (hentryC : NamedBlock.Preceq entry C) :
      NamedBlock.compatible Pn entry = true := by
    have hraw : Block.compatible Pn.erase entry.erase = true :=
      Block.compatible_of_preceq_common
        (Proofs.NamedWire.erase_preceq hPnC) (Proofs.NamedWire.erase_preceq hentryC)
    simp only [Block.compatible, Bool.or_eq_true] at hraw
    simp only [NamedBlock.compatible, Bool.or_eq_true]
    rcases hraw with hPnEntry | hEntryPn
    · exact Or.inl
        (NamedOutageHistory.JointHistoryProducersTime.named_of_erase_preceq
          S rho core hPnrun hentryRun hPnEntry)
    · exact Or.inr
        (NamedOutageHistory.JointHistoryProducersTime.named_of_erase_preceq
          S rho core hentryRun hPnrun hEntryPn)
  constructor
  · intro Pn' hPn' hErase a t ha hemit ht h root timeout hpair entry hentry hroot
    have hrootEq : Pn'.root = Pn.root := by
      simpa only [Proofs.NamedWire.erase_root] using congrArg Block.root hErase
    have hPnEq : Pn' = Pn :=
      core.toNamedRootCollisionFree.root_injective Pn' Pn hPn' hPnrun Pn' Pn
        (Or.inl (Proofs.NamedAncestry.named_self Pn'))
        (Or.inr (Proofs.NamedAncestry.named_self Pn)) hrootEq
    rw [hPnEq]
    exact compatible_of_common hentry
      (hrows.1 a t ha hemit ht h root timeout hpair entry hentry hroot)
  · intro Pn' hPn' hErase a t ha hemit ht h root hpair entry hentry hroot
    have hrootEq : Pn'.root = Pn.root := by
      simpa only [Proofs.NamedWire.erase_root] using congrArg Block.root hErase
    have hPnEq : Pn' = Pn :=
      core.toNamedRootCollisionFree.root_injective Pn' Pn hPn' hPnrun Pn' Pn
        (Or.inl (Proofs.NamedAncestry.named_self Pn'))
        (Or.inr (Proofs.NamedAncestry.named_self Pn)) hrootEq
    rw [hPnEq]
    exact compatible_of_common hentry
      (hrows.2 a t ha hemit ht h root hpair entry hentry hroot)

#print axioms noHonestConflictAbove_of_commonPrefixHistory

set_option maxHeartbeats 400000 in
/-- A raw G2 root graded in the stable round has no conflict with any honest
row emitted before the healthy-prefix boundary. The raw root itself, rather
than only the stable prefix below it, is an ancestor of the common
confirmation-history endpoint. -/
theorem stableRaw_noHonestConflictAbove_of_grade
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (s : Round) (raw : Block V)
    (hexec : OutageExecution S rho b0 b1)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hmargin : FormationMargin S s b0)
    (v : V) (hv : v ∈ rho.honest) (hs : 0 < s)
    (hgrade : storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc s .g2) v).st s .g2 raw = true) :
    NoHonestConflictAbove S rho b0 raw := by
  have hroundOne : domain S.E S.hc 1 .g2 ≤ b0 := by
    exact (FrameForward.domain_le_a S 1 .g2).trans
      ((Assembly.a_mono S (Nat.succ_le_succ (Nat.zero_le s))).trans
        ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin))
  have hT1 := protectedVoteSlots_before
    S rho b0 b1 hexec hcom hsleep hroundOne
  have hconf := namedConfirmationIdxQueryEmitted_of_healthyPrefix_of_T1
    S rho b0 b1 hexec hcom hsleep hroundOne hT1
  obtain ⟨C, hhistory⟩ :=
    NamedOutageHistory.OutageEnv.layerA_joint_history_idx_emitted_of_outage
      S rho b0 b1 s hexec hsleep hmargin hcom hconf
      (boundaryIdx rho b0) (le_refl _)
  have hrawC : Block.Preceq raw C.erase :=
    stableRaw_preceq_prefixHistory S rho b0 b1 hexec hcom hsleep
      s hs hmargin v hv raw hgrade C hhistory
  obtain ⟨Raw, hRawC, hRawErase⟩ :=
    NamedOutageHistory.ReadyHeadReturn.named_ancestor_of_erase raw C hrawC
  have hRawRun : NamedRun.blockInRun S rho Raw :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hhistory.1.1.1 hRawC
  have hno := noHonestConflictAbove_of_commonPrefixHistory
    S rho b0 hexec.core C Raw hhistory.1 hRawRun hRawC
  simpa only [hRawErase] using hno

#print axioms stableRaw_noHonestConflictAbove_of_grade

omit [Fintype V] in
private theorem prefixCacheAtRound_clip_local
    (F : Block V) (c : DecoupledConsensusModel.Protocol.Cache V) (r : Round) :
    DecoupledConsensusModel.Protocol.cacheAtRound (DecoupledConsensusModel.Protocol.clipCache F c) r =
      DecoupledConsensusModel.Protocol.clipFrame F (DecoupledConsensusModel.Protocol.cacheAtRound c r) := by
  unfold DecoupledConsensusModel.Protocol.cacheAtRound DecoupledConsensusModel.Protocol.clipCache
  split_ifs <;> rfl

omit [Fintype V] in
private theorem prefixReadFrame_eq_cacheAtRound_of_clipped
    (st : Protocol.HealingStore V) (c : DecoupledConsensusModel.Protocol.Cache V) (r : Round)
    (hclip : DecoupledConsensusModel.Protocol.clipCache st.F c = c) :
    DecoupledConsensusModel.Protocol.readFrame c st r =
      DecoupledConsensusModel.Protocol.cacheAtRound c r := by
  unfold DecoupledConsensusModel.Protocol.readFrame
  have h := congrArg (fun c' => DecoupledConsensusModel.Protocol.cacheAtRound c' r) hclip
  change DecoupledConsensusModel.Protocol.cacheAtRound (DecoupledConsensusModel.Protocol.clipCache st.F c) r =
    DecoupledConsensusModel.Protocol.cacheAtRound c r at h
  rw [prefixCacheAtRound_clip_local] at h
  exact h

private theorem prefixCompleteOne_other
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (r : Round) (t : Time) (p q : Phase)
    (f : DecoupledConsensusModel.Protocol.Frame V) (hpq : q ≠ p) :
    DecoupledConsensusModel.Protocol.phaseResult
        (DecoupledConsensusModel.Protocol.completeOne E hc st r t p f) q =
      DecoupledConsensusModel.Protocol.phaseResult f q := by
  unfold DecoupledConsensusModel.Protocol.completeOne
  split
  · rfl
  · split
    · cases p <;> cases q <;>
        simp_all [DecoupledConsensusModel.Protocol.putPhase, DecoupledConsensusModel.Protocol.phaseResult]
    · rfl

private theorem prefixCompleteFrame_g2_eq
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (r : Round) (t : Time) (f : DecoupledConsensusModel.Protocol.Frame V)
    (ht : t ≠ domain E hc r .g2) :
    (DecoupledConsensusModel.Protocol.completeFrame E hc st r t f).g2 = f.g2 := by
  change DecoupledConsensusModel.Protocol.phaseResult
      (DecoupledConsensusModel.Protocol.completeFrame E hc st r t f) .g2 =
    DecoupledConsensusModel.Protocol.phaseResult f .g2
  have h2 : DecoupledConsensusModel.Protocol.phaseResult
      (DecoupledConsensusModel.Protocol.completeOne E hc st r t .g2 f) .g2 =
      DecoupledConsensusModel.Protocol.phaseResult f .g2 := by
    unfold DecoupledConsensusModel.Protocol.completeOne
    split
    · rfl
    · simp [ht, DecoupledConsensusModel.Protocol.phaseResult]
  unfold DecoupledConsensusModel.Protocol.completeFrame
  rw [prefixCompleteOne_other E hc st r t .g0 .g2 _ (by decide),
    prefixCompleteOne_other E hc st r t .g1 .g2 _ (by decide), h2]

private theorem prefixAction_zero_ne_domain_g2 (S : Setup V) :
    S.a 0 ≠ domain S.E S.hc 0 .g2 := by
  have ha : S.a 0 = 6 * S.E.Δ := by
    unfold Setup.a Protocol.HealConfig.a
    simp [Protocol.HealConfig.opening_slot, slotStart]
  have hdomain : domain S.E S.hc 0 .g2 = -S.E.Δ := by
    unfold domain opening DecoupledConsensusModel.Protocol.Phase.domainOffset
      Protocol.proposal_time Env.t slotStart Protocol.HealConfig.opening_slot
    norm_num
  rw [ha, hdomain]
  nlinarith [S.E.Δ_pos]

private theorem prefixReadFrame_g2_round_zero_no_root
    (S : Setup V) {rho : NamedRun V} (core : NamedAdmissibleCore S rho)
    (v : V) (t : Time) {root : Block V} :
    (DecoupledConsensusModel.Protocol.readFrame
      (NamedRun.stateBeforeTime S rho t v).cache
      (NamedRun.stateBeforeTime S rho t v).st.core.toHealing 0).g2 ≠
        some (some root) := by
  let n := NamedRun.stateBeforeTime S rho t v
  have hclip : DecoupledConsensusModel.Protocol.clipCache n.st.core.F n.cache = n.cache :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t v).2.2
  have hframe := prefixReadFrame_eq_cacheAtRound_of_clipped
    n.st.core.toHealing n.cache 0
      (by simpa only [Protocol.Store.toHealing] using hclip)
  intro hroot
  have hphase : DecoupledConsensusModel.Protocol.phaseResult
      (DecoupledConsensusModel.Protocol.cacheAtRound n.cache 0) .g2 = some (some root) := by
    rw [← hframe]
    exact hroot
  have horigin := NamedCacheProvenance.completed_phase_before_read S rho
    core.sorted core.nodup t v 0 .g2 (some root) (by simpa only [n] using hphase)
  rcases horigin with hzero | ⟨j, tau, hj, _, htau, _⟩
  · simpa using hzero.2
  · have hnonneg :=
      (core.toNamedScheduleWellFormed.in_horizon
        _ (List.mem_of_getElem? hj)).1
    rw [htau] at hnonneg
    have hdomain : domain S.E S.hc 0 .g2 = -S.E.Δ := by
      unfold domain opening DecoupledConsensusModel.Protocol.Phase.domainOffset
        Protocol.proposal_time Env.t slotStart Protocol.HealConfig.opening_slot
      norm_num
    rw [hdomain] at hnonneg
    simp only [NamedEvent.time] at hnonneg
    nlinarith [S.E.Δ_pos]

private theorem prefixPreparedFrame_g2_round_zero_no_root
    (S : Setup V) (before : NamedNodeState V)
    (hround : S.hc.round_of (S.E.slotOf (S.a 0)) = 0)
    (htime : S.a 0 ≠ domain S.E S.hc 0 .g2) {root : Block V}
    (hclip : DecoupledConsensusModel.Protocol.clipCache before.st.core.F before.cache = before.cache)
    (hraw : (DecoupledConsensusModel.Protocol.readFrame before.cache
      before.st.core.toHealing 0).g2 ≠ some (some root)) :
    (DecoupledConsensusModel.Protocol.readFrame
      (NamedActionReads.preparedCache S before (S.a 0))
      (Protocol.NamedDuties.update_confirmation_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S before (S.a 0)).cache)
        S.E S.hc (NamedActionReads.confirmationReadFrom S before (S.a 0)).st
        (S.E.slotOf (S.a 0) - 1)).core.toHealing 0).g2 ≠
      some (some root) := by
  intro hroot
  have hF :
      (Protocol.NamedDuties.update_confirmation_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S before (S.a 0)).cache)
        S.E S.hc (NamedActionReads.confirmationReadFrom S before (S.a 0)).st
        (S.E.slotOf (S.a 0) - 1)).core.toHealing.F =
      before.st.core.toHealing.F := rfl
  change (DecoupledConsensusModel.Protocol.clipFrame
    (Protocol.NamedDuties.update_confirmation_with
      (NamedProfile.gradeContract
        (NamedActionReads.confirmationReadFrom S before (S.a 0)).cache)
      S.E S.hc (NamedActionReads.confirmationReadFrom S before (S.a 0)).st
      (S.E.slotOf (S.a 0) - 1)).core.toHealing.F
    (DecoupledConsensusModel.Protocol.cacheAtRound
      (NamedActionReads.preparedCache S before (S.a 0)) 0)).g2 =
      some (some root) at hroot
  rw [hF] at hroot
  change (DecoupledConsensusModel.Protocol.clipFrame before.st.core.toHealing.F
    (DecoupledConsensusModel.Protocol.cacheAtRound
      (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc before.st.core.toHealing
        (S.a 0) before.cache) 0)).g2 = some (some root) at hroot
  unfold DecoupledConsensusModel.Protocol.onPhaseTick at hroot
  simp only [hround] at hroot
  let a := DecoupledConsensusModel.Protocol.alignRound before.cache 0
  have ha : a.round = 0 := by
    dsimp [a]
    unfold DecoupledConsensusModel.Protocol.alignRound
    split_ifs <;> simp_all
  change (DecoupledConsensusModel.Protocol.clipFrame before.st.core.toHealing.F
    (DecoupledConsensusModel.Protocol.cacheAtRound
      (DecoupledConsensusModel.Protocol.clipCache before.st.core.toHealing.F
        { round := a.round,
          current := DecoupledConsensusModel.Protocol.completeFrame S.E S.hc
            before.st.core.toHealing a.round (S.a 0) a.current,
          next := DecoupledConsensusModel.Protocol.completeFrame S.E S.hc
            before.st.core.toHealing (a.round + 1) (S.a 0) a.next }) 0)).g2 =
      some (some root) at hroot
  rw [prefixCacheAtRound_clip_local] at hroot
  simp only [ha, DecoupledConsensusModel.Protocol.cacheAtRound, if_pos] at hroot
  have htime' : S.a 0 ≠ domain S.E S.hc a.round .g2 := by
    simpa [ha] using htime
  have hcomp := prefixCompleteFrame_g2_eq S.E S.hc
    before.st.core.toHealing a.round (S.a 0) a.current htime'
  have hcomp0 :
      (DecoupledConsensusModel.Protocol.completeFrame S.E S.hc before.st.core.toHealing
        0 (S.a 0) a.current).g2 = a.current.g2 := by
    simpa [ha] using hcomp
  change DecoupledConsensusModel.Protocol.clipResult before.st.core.toHealing.F
      (DecoupledConsensusModel.Protocol.clipResult before.st.core.toHealing.F
        (DecoupledConsensusModel.Protocol.completeFrame S.E S.hc before.st.core.toHealing
          0 (S.a 0) a.current).g2) = some (some root) at hroot
  rw [hcomp0] at hroot
  by_cases hc0 : before.cache.round = 0
  · have hacurrent : a.current = before.cache.current := by
      simp [a, DecoupledConsensusModel.Protocol.alignRound, hc0]
    rw [hacurrent] at hroot
    have hcur := congrArg (fun c => c.current) hclip
    change DecoupledConsensusModel.Protocol.clipFrame before.st.core.toHealing.F
        before.cache.current = before.cache.current at hcur
    have hcur2 := congrArg (fun f => f.g2) hcur
    change DecoupledConsensusModel.Protocol.clipResult before.st.core.toHealing.F
        before.cache.current.g2 = before.cache.current.g2 at hcur2
    rw [hcur2] at hroot
    have hraw' := hraw
    change (DecoupledConsensusModel.Protocol.clipFrame before.st.core.toHealing.F
      (DecoupledConsensusModel.Protocol.cacheAtRound before.cache 0)).g2 ≠
        some (some root) at hraw'
    have hc0' : 0 = before.cache.round := hc0.symm
    simp only [DecoupledConsensusModel.Protocol.cacheAtRound, if_pos hc0'] at hraw'
    change DecoupledConsensusModel.Protocol.clipResult before.st.core.toHealing.F
        before.cache.current.g2 ≠ some (some root) at hraw'
    exact hraw' hroot
  · have hacurrent : a.current = DecoupledConsensusModel.Protocol.pendingFrame := by
      dsimp [a]
      unfold DecoupledConsensusModel.Protocol.alignRound
      split_ifs <;> simp_all
    rw [hacurrent] at hroot
    simp [DecoupledConsensusModel.Protocol.pendingFrame, DecoupledConsensusModel.Protocol.clipResult] at hroot

private theorem prefixActionRead_g2_round_zero_no_root
    (S : Setup V) {rho : NamedRun V} (core : NamedAdmissibleCore S rho)
    (v : V) {root : Block V} :
    (DecoupledConsensusModel.Protocol.readFrame (Proofs.HealingSurface.actionReadAt S rho v 0).cache
      (Proofs.HealingSurface.actionReadAt S rho v 0).st.core.toHealing 0).g2 ≠
        some (some root) := by
  let before := NamedRun.stateBeforeTime S rho (S.a 0) v
  exact prefixPreparedFrame_g2_round_zero_no_root S before
    (Proofs.HealingLemmas.round_of_slotOf_a S 0)
    (prefixAction_zero_ne_domain_g2 S)
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a 0) v).2.2
    (prefixReadFrame_g2_round_zero_no_root S core v (S.a 0))

/-- General-time form of `prefixPreparedFrame_g2_round_zero_no_root` for the
staged confirmation read: no saved G2 root exists in round zero at any
nonnegative read time. -/
theorem stagedRead_g2_round_zero_no_root
    (S : Setup V) {rho : NamedRun V} (core : NamedAdmissibleCore S rho)
    (v : V) (t : Time) (ht0 : (0 : Time) ≤ t)
    (hround : S.hc.round_of (S.E.slotOf t) = 0) {root : Block V} :
    (DecoupledConsensusModel.Protocol.readFrame
      (Internal.NamedOutageEntry.confirmationReadAt S rho v t).cache
      (Internal.NamedOutageEntry.confirmationReadAt S rho v t).st.core.toHealing 0).g2 ≠
        some (some root) := by
  let before := NamedRun.stateBeforeTime S rho t v
  have hclip : DecoupledConsensusModel.Protocol.clipCache before.st.core.F before.cache = before.cache :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t v).2.2
  have hraw := prefixReadFrame_g2_round_zero_no_root S core v t (root := root)
  have htime : t ≠ domain S.E S.hc 0 .g2 := by
    have hdomain : domain S.E S.hc 0 .g2 = -S.E.Δ := by
      unfold domain opening DecoupledConsensusModel.Protocol.Phase.domainOffset
        Protocol.proposal_time Env.t slotStart Protocol.HealConfig.opening_slot
      norm_num
    rw [hdomain]
    have := S.E.Δ_pos
    intro h
    linarith
  intro hroot
  change (DecoupledConsensusModel.Protocol.clipFrame before.st.core.toHealing.F
    (DecoupledConsensusModel.Protocol.cacheAtRound
      (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc before.st.core.toHealing
        t before.cache) 0)).g2 = some (some root) at hroot
  unfold DecoupledConsensusModel.Protocol.onPhaseTick at hroot
  simp only [hround] at hroot
  let a := DecoupledConsensusModel.Protocol.alignRound before.cache 0
  have ha : a.round = 0 := by
    dsimp [a]
    unfold DecoupledConsensusModel.Protocol.alignRound
    split_ifs <;> simp_all
  change (DecoupledConsensusModel.Protocol.clipFrame before.st.core.toHealing.F
    (DecoupledConsensusModel.Protocol.cacheAtRound
      (DecoupledConsensusModel.Protocol.clipCache before.st.core.toHealing.F
        { round := a.round,
          current := DecoupledConsensusModel.Protocol.completeFrame S.E S.hc
            before.st.core.toHealing a.round t a.current,
          next := DecoupledConsensusModel.Protocol.completeFrame S.E S.hc
            before.st.core.toHealing (a.round + 1) t a.next }) 0)).g2 =
      some (some root) at hroot
  rw [prefixCacheAtRound_clip_local] at hroot
  simp only [ha, DecoupledConsensusModel.Protocol.cacheAtRound, if_pos] at hroot
  have htime' : t ≠ domain S.E S.hc a.round .g2 := by
    simpa [ha] using htime
  have hcomp := prefixCompleteFrame_g2_eq S.E S.hc
    before.st.core.toHealing a.round t a.current htime'
  have hcomp0 :
      (DecoupledConsensusModel.Protocol.completeFrame S.E S.hc before.st.core.toHealing
        0 t a.current).g2 = a.current.g2 := by
    simpa [ha] using hcomp
  change DecoupledConsensusModel.Protocol.clipResult before.st.core.toHealing.F
      (DecoupledConsensusModel.Protocol.clipResult before.st.core.toHealing.F
        (DecoupledConsensusModel.Protocol.completeFrame S.E S.hc before.st.core.toHealing
          0 t a.current).g2) = some (some root) at hroot
  rw [hcomp0] at hroot
  by_cases hc0 : before.cache.round = 0
  · have hacurrent : a.current = before.cache.current := by
      simp [a, DecoupledConsensusModel.Protocol.alignRound, hc0]
    rw [hacurrent] at hroot
    have hcur := congrArg (fun c => c.current) hclip
    change DecoupledConsensusModel.Protocol.clipFrame before.st.core.toHealing.F
        before.cache.current = before.cache.current at hcur
    have hcur2 := congrArg (fun f => f.g2) hcur
    change DecoupledConsensusModel.Protocol.clipResult before.st.core.toHealing.F
        before.cache.current.g2 = before.cache.current.g2 at hcur2
    rw [hcur2] at hroot
    have hraw' := hraw
    change (DecoupledConsensusModel.Protocol.clipFrame before.st.core.toHealing.F
      (DecoupledConsensusModel.Protocol.cacheAtRound before.cache 0)).g2 ≠
        some (some root) at hraw'
    have hc0' : 0 = before.cache.round := hc0.symm
    simp only [DecoupledConsensusModel.Protocol.cacheAtRound, if_pos hc0'] at hraw'
    change DecoupledConsensusModel.Protocol.clipResult before.st.core.toHealing.F
        before.cache.current.g2 ≠ some (some root) at hraw'
    exact hraw' hroot
  · have hacurrent : a.current = DecoupledConsensusModel.Protocol.pendingFrame := by
      dsimp [a]
      unfold DecoupledConsensusModel.Protocol.alignRound
      split_ifs <;> simp_all
    rw [hacurrent] at hroot
    simp [DecoupledConsensusModel.Protocol.pendingFrame, DecoupledConsensusModel.Protocol.clipResult] at hroot

#print axioms stagedRead_g2_round_zero_no_root

/-- A stable frame candidate cannot occur in round zero. -/
theorem stableAt_round_pos
    (S : Setup V) {rho : NamedRun V} (core : NamedAdmissibleCore S rho)
    {v : V} {s : Round} {P : Block V} (hstable : stableAt S rho v s P) :
    0 < s := by
  cases s with
  | succ s => exact Nat.zero_lt_succ s
  | zero =>
      obtain ⟨G, hG, -⟩ := hstable
      have hG' := hG
      unfold activeG2 DecoupledConsensusModel.Protocol.frameSGCandidate at hG'
      have hround : S.hc.round_of
          (roundConfirmationRead S rho v 0).st.core.toHealing.s = 0 := by
        exact Proofs.HealingLemmas.round_of_slotOf_a S 0
      simp only [hround] at hG'
      cases hframe : (DecoupledConsensusModel.Protocol.readFrame
          (roundConfirmationRead S rho v 0).cache
          (roundConfirmationRead S rho v 0).st.core.toHealing 0).g2 with
      | none => simp [hframe] at hG'
      | some value =>
          cases value with
          | none => simp [hframe] at hG'
          | some raw =>
              have hframeAction : (DecoupledConsensusModel.Protocol.readFrame
                  (Proofs.HealingSurface.actionReadAt S rho v 0).cache
                  (Proofs.HealingSurface.actionReadAt S rho v 0).st.core.toHealing 0).g2 =
                    some (some raw) := by
                simpa only [roundConfirmationRead, Internal.NamedOutageEntry.confirmationReadAt,
                  Proofs.HealingSurface.actionReadAt, NamedActionReads.actionReadAt,
                  NamedActionReads.actionReadFrom,
                  NamedActionReads.confirmationReadAt,
                  NamedActionReads.confirmationReadFrom,
                  NamedActionReads.preparedCache,
                  Protocol.NamedDuties.update_confirmation_with] using hframe
              exact False.elim
                (prefixActionRead_g2_round_zero_no_root S core v hframeAction)

#print axioms stableAt_round_pos







end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
