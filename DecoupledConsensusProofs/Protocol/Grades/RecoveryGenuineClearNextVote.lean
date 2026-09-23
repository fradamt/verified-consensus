module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoverySelectedActionG2VoteCone
public import DecoupledConsensusProofs.Execution.RecoverySelectedG2PrefixVisibility
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightRegimeFrame
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FinalityFilterRetention
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityComparison
public import DecoupledConsensusProofs.Protocol.Handlers.JustificationCarrier
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.PreparedReadBridge
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.Grades.RelativeCrossReader
public import DecoupledConsensusProofs.Protocol.Grades.HealthyHeadReady
public import DecoupledConsensusProofs.Generic.SuffixHistory
public import DecoupledConsensusProofs.Protocol.Grades.FrameCompleted
public import DecoupledConsensusProofs.Protocol.Grades.SGFromSupport
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryFinalityFilterRetainedVoteConeSeed
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.GoldfishCone
public import DecoupledConsensusProofs.Protocol.Schedule.WeakProcessedTree
public import DecoupledConsensusProofs.Execution.RecoveryActionLiveSourceSplit
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryProposalConfirmationRead

@[expose] public section

/-!
# Genuine-clear next-vote seed

the prior module is not restated by erasing its rows. The runtime now uses named
attestations and named blocks, and vote cones use `NamedHonestVotesCone`.

The named-height handover, exact selected-body relay, filtered retention, and
source relative G2 grade are proved below. The cross-reader algebra is now in
`RelativeCrossReaderRun`. Its current delivery interface is stronger than the
windowed delivery that this recovery theorem can derive, so the final seed
constructors remain recorded at the exact Open boundary below.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open DecoupledConsensusModel.Protocol
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Inputs used only when the action FG source is the selected Q2. -/
structure VoterAnchorSourceQ2Inputs
    (S : Setup V) (rho : Run V) (r : Round) (p : V) (B : Block V) : Prop where
  g1Target : ∀ w ∈ rho.honest,
    B ∈ filteredTree (readAt S rho (domain S.E S.hc r .g1) w)
  openingTarget : ∀ w ∈ rho.honest,
    B ∈ filteredTree (voteDutyRead S rho w (S.hc.opening_slot r))

/-- Inputs used only when the action FG source comes from a genuine clear. -/
structure VoterAnchorSourceClearInputs
    (S : Setup V) (rho : Run V) (r : Round) (p : V) (B : Block V) : Prop where
  nextTarget : ∀ w ∈ rho.honest,
    B ∈ filteredTree (voteDutyRead S rho w (S.hc.opening_slot r + 1))
  anchor : ∀ w ∈ rho.honest, ∀ L,
    voterAnchorAt S rho w (S.hc.opening_slot r + 1) = L →
    ¬ Block.Preceq L B →
      L ∈ filteredTree (readAt S rho (domain S.E S.hc r .g0) p) ∧
      L ∈ filteredTree (actionDutyRead S rho p r)

/-- earlier-shaped inputs for the genuine-clear next-vote consumer. The
pre-rewrite proof uses target retention and compatibility of the prepared
anchor with the source. It does not require a common action frontier. -/
structure VoterAnchorSourceClearInputsMain
    (S : Setup V) (rho : Run V) (r : Round) (p : V) (B : Block V) : Prop where
  nextTarget : ∀ w ∈ rho.honest,
    B ∈ filteredTree (voteDutyRead S rho w (S.hc.opening_slot r + 1))
  anchorCompatible : ∀ w ∈ rho.honest, ∀ L,
    voterAnchorAt S rho w (S.hc.opening_slot r + 1) = L →
    Block.compatible L B = true

/-! ## Named-height handover -/



private theorem actionBody_runBlock_genuine
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionStoreAt S rho v r).st.bodies) :
    RunBlock S rho D := by
  have hDpre : D ∈ (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    simpa only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
      NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hD
  obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted (S.a r)
  change D ∈ (NamedRun.stateBeforeTime S rho (S.a r) v).st.bodies at hDpre
  rw [congrFun hi v] at hDpre
  exact Proofs.Bridges.runBlock_of_stateBefore_mem S hv hDpre

omit [Fintype V] in
private theorem named_self_genuine (D : NamedBlock V) :
    NamedBlock.Preceq D D := by
  cases D <;> simp [NamedBlock.Preceq, NamedBlock.preceq]

theorem actionBody_at_voteDuty_of_filtered
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {p : V} (hp : p ∈ rho.honest)
    {B : NamedBlock V}
    (hBmem : B ∈ (actionStoreAt S rho p r).st.bodies)
    {w : V} (hw : w ∈ rho.honest) {s : Slot}
    (hfiltered : B.erase ∈ filteredTree
      (voteDutyRead S rho w s)) :
    B ∈ (voteDutyRead S rho w s).st.bodies := by
  let vote := Protocol.vote_time S.E s
  have hrawRead : B.erase ∈
      (voteDutyRead S rho w s).st.core.T :=
    Proofs.Records.get_filtered_block_tree_subset _ hfiltered
  have hrawPre : B.erase ∈
      (NamedRun.stateBeforeTime S rho vote w).st.core.T := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      vote] using hrawRead
  obtain ⟨D, hD, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
      S rho vote w hrawPre
  obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
    S rho adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted vote
  have hDprefix : D ∈ (NamedRun.stateBefore S rho n w).st.bodies := by
    rw [← hn]
    exact hD
  have hDrun : RunBlock S rho D :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hw hDprefix
  have hBrun : RunBlock S rho B :=
    actionBody_runBlock_genuine S adm hp hBmem
  have hroot : D.root = B.root := by
    rw [← Proofs.NamedWire.erase_root D, hDerase, Proofs.NamedWire.erase_root]
  have hDB : D = B :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      D B hDrun hBrun D B (Or.inl (named_self_genuine D))
        (Or.inr (named_self_genuine B)) hroot
  subst D
  simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom,
    NamedActionReads.preparedCache, Protocol.NamedStore.setClock,
    vote] using hD

/-- Activity at the opening vote carries an exact named source body to the
same reader's action read. -/
theorem actionBody_at_action_of_openingVoteFiltered
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {p : V} (hp : p ∈ rho.honest)
    {B : NamedBlock V}
    (hBmem : B ∈ (actionStoreAt S rho p r).st.bodies)
    {w : V} (hw : w ∈ rho.honest)
    (hfiltered : B.erase ∈ filteredTree
      (voteDutyRead S rho w (S.hc.opening_slot r))) :
    B ∈ (actionStoreAt S rho w r).st.bodies := by
  let vote := Protocol.vote_time S.E (S.hc.opening_slot r)
  have hvote := actionBody_at_voteDuty_of_filtered
    S adm hp hBmem hw hfiltered
  have hvotePre : B ∈ (NamedRun.stateBeforeTime S rho vote w).st.bodies := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, Protocol.NamedStore.setClock,
      vote] using hvote
  have heqVote := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed vote) w
  have heqAction := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.a r)) w
  rw [heqVote] at hvotePre
  have hactionPre : B ∈
      (NamedRun.stateBeforeTime S rho (S.a r) w).st.bodies := by
    rw [heqAction]
    exact NamedBodyRetention.stateBefore_bodies_mono S rho w
      (strictEventIndex_mono rho
        ((Protocol.vote_time_le_confirmation_time S.E _).trans
          (by rw [opening_confirmation_time_eq_action]))) hvotePre
  simpa only [actionStoreAt, actionReadAt,
    NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
    NamedActionReads.confirmationReadFrom,
    NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hactionPre

/-- K6 target activity at the next vote carries the exact named source body
to every honest action read of the same round. -/
theorem actionBody_at_action_of_nextVoteFiltered
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {p : V} (hp : p ∈ rho.honest)
    {B : NamedBlock V}
    (hBmem : B ∈ (actionStoreAt S rho p r).st.bodies)
    {w : V} (hw : w ∈ rho.honest)
    (hfiltered : B.erase ∈ filteredTree
      (voteDutyRead S rho w (S.hc.opening_slot r + 1))) :
    B ∈ (actionStoreAt S rho w r).st.bodies := by
  let vote := Protocol.vote_time S.E (S.hc.opening_slot r + 1)
  have hvote := actionBody_at_voteDuty_of_filtered
    S adm hp hBmem hw hfiltered
  have hvotePre : B ∈ (NamedRun.stateBeforeTime S rho vote w).st.bodies := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, Protocol.NamedStore.setClock,
      vote] using hvote
  have heqVote := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed vote) w
  have heqAction := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.a r)) w
  rw [heqVote] at hvotePre
  have hactionPre : B ∈
      (NamedRun.stateBeforeTime S rho (S.a r) w).st.bodies := by
    rw [heqAction]
    exact NamedBodyRetention.stateBefore_bodies_mono S rho w
      (strictEventIndex_mono rho (next_vote_time_lt_action S r).le)
      hvotePre
  simpa only [actionStoreAt, actionReadAt,
    NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
    NamedActionReads.confirmationReadFrom,
    NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hactionPre

/-- The named selected Q2 body is already present at its capture-domain read.
The statement keeps the exact body, not only another body with the same
erasure. -/
theorem selectedQ2_body_at_capture
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {p : V} (hp : p ∈ rho.honest) {Q : NamedBlock V}
    (hselected : PhaseGrades.nodeQ2 S (actionReadAt S rho p r) r =
      some Q.erase)
    (hQmem : Q ∈ (actionStoreAt S rho p r).st.bodies) :
    Q ∈ (rho.stateBeforeTime S (domain S.E S.hc r .g2) p).st.bodies := by
  let i := strictEventIndex rho (S.a r)
  have hread := stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.a r)
  have hreadp := congrFun hread p
  have hselected0 := hselected
  simp only [PhaseGrades.nodeQ2, PhaseGrades.nodeRead,
    NamedProfile.gradeContract, DecoupledConsensusModel.Protocol.frameContract] at hselected0
  unfold actionReadAt NamedActionReads.actionReadAt at hselected0
  rw [hreadp] at hselected0
  have hselected' : Protocol.grade2_block_with
      (NamedProfile.gradeContract
        (NamedActionReads.actionReadFrom S
          (NamedRun.stateBefore S rho i p) r).cache)
      S.E S.hc
      (NamedActionReads.actionReadFrom S
        (NamedRun.stateBefore S rho i p) r).st.core.toHealing r =
        some Q.erase := by
    simpa only [i] using hselected0
  obtain ⟨j, raw, -, hj, hfreeze, hQraw⟩ :=
    contractQ2_capture_at_action_index S rho i p r hselected'
  have hrawTree : raw ∈ (rho.stateBefore S j p).st.core.T := by
    exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hfreeze)).1
  have hQTree : Q.erase ∈ (rho.stateBefore S j p).st.core.T := by
    have hpc := Proofs.NamedStoreBridge.parentClosed_stateBefore S rho j p
    exact Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
      Q.erase raw hrawTree hQraw
  obtain ⟨D, hD, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho j p hQTree
  have hDrun : RunBlock S rho D :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hp hD
  have hQrun : RunBlock S rho Q :=
    actionBody_runBlock_genuine S adm hp hQmem
  have hroot : D.root = Q.root := by
    rw [← Proofs.NamedWire.erase_root D, hDerase, Proofs.NamedWire.erase_root]
  have hDQ : D = Q :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      D Q hDrun hQrun D Q (Or.inl (named_self_genuine D))
        (Or.inr (named_self_genuine Q)) hroot
  have hjState := Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hj
  subst D
  rw [hjState] at hD
  exact hD

/-- A selected named Q2 body reaches every honest opening-vote read. Its
named derivation supplies the exact recovery height used by the receiver's
finite finality floor. -/
theorem selectedQ2_body_at_action_and_openingVote_of_floor
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (ready : GradeRoundReady S rho r)
    {p : V} (hp : p ∈ rho.honest) {Q : NamedBlock V}
    (hselected : PhaseGrades.nodeQ2 S (actionReadAt S rho p r) r =
      some Q.erase)
    (hQmem : Q ∈ (actionStoreAt S rho p r).st.bodies)
    {stop : Nat} {blocked : Height} {Tprev : Block V}
    (hfloor : FinalityFloorAt S rho blocked stop Tprev)
    (hQheight : (Protocol.derive_named S.E S.cfg Q).h = blocked + 1)
    (hTQ : Block.Preceq Tprev Q.erase)
    (hactionPrefix : strictEventIndex rho (S.a r) ≤ stop)
    {reader : V} (hreader : reader ∈ rho.honest) :
    Q ∈ (actionStoreAt S rho reader r).st.bodies ∧
      Q ∈ (voteDutyRead S rho reader (S.hc.opening_slot r)).st.bodies := by
  let sourceCut := domain S.E S.hc r .g2
  let earlyCut := domain S.E S.hc r .g1
  let voteRead := Protocol.vote_time S.E (S.hc.opening_slot r)
  have hQsource : Q ∈
      (rho.stateBeforeTime S sourceCut p).st.bodies := by
    simpa only [sourceCut] using
      selectedQ2_body_at_capture S adm hp hselected hQmem
  have hQrun : RunBlock S rho Q :=
    actionBody_runBlock_genuine S adm hp hQmem
  have hpostSource : S.E.t_GST ≤ sourceCut := by
    exact ready.1.trans (NamedOutageClosure.early_le_domain S r)
  have hdeadline : max sourceCut S.E.t_GST + S.E.Δ ≤ earlyCut := by
    rw [max_eq_left hpostSource]
    dsimp only [sourceCut, earlyCut]
    change domain S.E S.hc r .g2 + S.E.Δ ≤
      domain S.E S.hc r .g1
    apply le_of_eq
    simp only [domain, Phase.domainOffset]
    ring
  have horder : earlyCut ≤ voteRead := by
    dsimp only [earlyCut, voteRead]
    rw [NamedOutageClosure.domain_g1_eq_opening]
    change Protocol.proposal_time S.E (S.hc.opening_slot r) ≤
      Protocol.vote_time S.E (S.hc.opening_slot r)
    exact (Protocol.proposal_time_lt_vote_time S.E _).le
  have hcut : earlyCut ≤ rho.horizon := by
    have hdomain : domain S.E S.hc r .g1 ≤ domain S.E S.hc r .g0 := by
      simp only [domain, Phase.domainOffset]
      exact Int.add_le_add_left
        (Int.mul_le_mul_of_nonneg_right (by norm_num) S.E.Δ_pos.le) _
    exact (by simpa only [earlyCut] using hdomain.trans ready.2)
  have hvoteAction : voteRead ≤ S.a r := by
    dsimp only [voteRead]
    calc
      Protocol.vote_time S.E (S.hc.opening_slot r) ≤
          Protocol.confirmation_time S.E (S.hc.opening_slot r) :=
        Protocol.vote_time_le_confirmation_time S.E _
      _ = S.a r := opening_confirmation_time_eq_action S r
  have hvotePrefix : strictEventIndex rho voteRead ≤ stop :=
    (strictEventIndex_mono rho hvoteAction).trans hactionPrefix
  have hFvote : Block.Preceq
      (rho.stateBeforeTime S voteRead reader).st.core.F Q.erase := by
    change Block.Preceq
      (NamedRun.stateBeforeTime S rho voteRead reader).st.core.F Q.erase
    rw [congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed voteRead) reader]
    exact hfloor.storeF_preceq_sourceHeightBlock hreader hvotePrefix
      hQrun hQheight hTQ
  have hQvote := NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
    S rho adm.toNamedAdmissibleCore p hp reader hreader Q
      sourceCut earlyCut voteRead hQsource hdeadline horder hcut hFvote
  have hQvoteIndex := hQvote.1
  rw [congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed voteRead) reader]
    at hQvoteIndex
  have hQaction : Q ∈
      (rho.stateBeforeTime S (S.a r) reader).st.bodies := by
    change Q ∈
      (NamedRun.stateBeforeTime S rho (S.a r) reader).st.bodies
    rw [congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.a r)) reader]
    exact NamedBodyRetention.stateBefore_bodies_mono S rho reader
      (strictEventIndex_mono rho hvoteAction) hQvoteIndex
  constructor
  · simpa only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
      NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hQaction
  · simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      Protocol.NamedStore.setClock, voteRead] using hQvote.1

#print axioms selectedQ2_body_at_action_and_openingVote_of_floor

omit [Fintype V] in
private theorem localCovers_of_preceq_genuine
    {A B : Block V} {gv : Protocol.GradeView V}
    {key : Option BlockId} (hAB : Block.Preceq A B)
    (hB : DecoupledConsensusModel.Protocol.localCovers gv key B = true) :
    DecoupledConsensusModel.Protocol.localCovers gv key A = true := by
  unfold DecoupledConsensusModel.Protocol.localCovers at hB ⊢
  unfold Protocol.head_covers at hB ⊢
  cases key with
  | none => exact hB
  | some root =>
      dsimp only at hB ⊢
      cases hfind : Block.find? gv.T root with
      | none =>
          rw [hfind] at hB
          exact absurd hB (by simp)
      | some head =>
          rw [hfind] at hB
          dsimp only at hB ⊢
          exact Block.preceq_trans hAB hB

omit [Fintype V] in
private theorem positive_of_preceq_genuine
    {A B : Block V} (hAB : Block.Preceq A B)
    (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    (early late : Time) (v : V)
    (hB : DecoupledConsensusModel.Protocol.positive gv F eta r early late v B = true) :
    DecoupledConsensusModel.Protocol.positive gv F eta r early late v A = true := by
  simp only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq] at hB ⊢
  rcases hB with ⟨u, hu, hmax, hcov, hclean, hlate⟩
  refine ⟨u, hu, hmax, localCovers_of_preceq_genuine hAB hcov, hclean, ?_⟩
  intro x hx hlt
  exact localCovers_of_preceq_genuine hAB (hlate x hx hlt)

omit [Fintype V] in
private theorem opposing_of_preceq_genuine
    {A B : Block V} (hAB : Block.Preceq A B)
    (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    (early late : Time) (v : V)
    (hA : DecoupledConsensusModel.Protocol.opposing gv F eta r early late v A = true) :
    DecoupledConsensusModel.Protocol.opposing gv F eta r early late v B = true := by
  simp only [DecoupledConsensusModel.Protocol.opposing, decide_eq_true_eq] at hA ⊢
  rcases hA with ⟨x, hx, hmax, hnot⟩ |
      ⟨x, hx, y, hy, hmax, heq, hkey⟩
  · left
    refine ⟨x, hx, hmax, ?_⟩
    intro hcov
    exact hnot (localCovers_of_preceq_genuine hAB hcov)
  · exact Or.inr ⟨x, hx, y, hy, hmax, heq, hkey⟩

private theorem phaseGrade_of_preceq_genuine
    (E : Env V) (hc : Protocol.HealConfig) (gv : Protocol.GradeView V)
    (F : Block V) (r : Round) (phase : Phase) {A B : Block V}
    (hAB : Block.Preceq A B)
    (hB : PhaseGrades.phaseGrade E hc gv F r phase B = true) :
    PhaseGrades.phaseGrade E hc gv F r phase A = true := by
  simp only [PhaseGrades.phaseGrade, DecoupledConsensusModel.Protocol.gradeBool,
    decide_eq_true_eq] at hB ⊢
  have hOpp : (Finset.univ.filter fun v =>
      DecoupledConsensusModel.Protocol.opposing gv F hc.η_SG r
        (early E hc r phase) (late E hc r phase) v A = true) ⊆
      Finset.univ.filter fun v =>
        DecoupledConsensusModel.Protocol.opposing gv F hc.η_SG r
          (early E hc r phase) (late E hc r phase) v B = true := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v,
      opposing_of_preceq_genuine hAB gv F hc.η_SG r
        (early E hc r phase) (late E hc r phase) v
        (Finset.mem_filter.mp hv).2⟩
  have hPos : (Finset.univ.filter fun v =>
      DecoupledConsensusModel.Protocol.positive gv F hc.η_SG r
        (early E hc r phase) (late E hc r phase) v B = true) ⊆
      Finset.univ.filter fun v =>
        DecoupledConsensusModel.Protocol.positive gv F hc.η_SG r
          (early E hc r phase) (late E hc r phase) v A = true := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v,
      positive_of_preceq_genuine hAB gv F hc.η_SG r
        (early E hc r phase) (late E hc r phase) v
        (Finset.mem_filter.mp hv).2⟩
  exact lt_of_le_of_lt (E.electorate.weightOf_mono hOpp)
    (lt_of_lt_of_le hB (E.electorate.weightOf_mono hPos))

/-- An active prepared voter anchor inherits the G1 grade of the raw root
frozen at that reader's G1 domain. -/
theorem activeVoterAnchor_storeGrade_g1
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (hr : 0 < r) (ready : GradeRoundReady S rho r)
    {w : V} (hw : w ∈ rho.honest) {root L : Block V}
    (hframe :
      (DecoupledConsensusModel.Protocol.readFrame
        (voteDutyRead S rho w (S.hc.opening_slot r + 1)).cache
        (voteDutyRead S rho w
          (S.hc.opening_slot r + 1)).st.core.toHealing r).g1 =
        some (some root))
    (hactive : DecoupledConsensusModel.Protocol.activePrefix
      (filteredTree (voteDutyRead S rho w (S.hc.opening_slot r + 1)))
      root = some L) :
    storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc r .g1) w).st r .g1 L = true := by
  let t := Protocol.vote_time S.E (S.hc.opening_slot r + 1)
  let before := NamedRun.stateBeforeTime S rho t w
  let read := voteDutyRead S rho w (S.hc.opening_slot r + 1)
  have hround : S.hc.round_of (S.E.slotOf t) = r := by
    simpa only [t, Proofs.Optimistic.slotOf_vote_time] using
      Proofs.HealingLemmas.round_of_opening_succ S.hc r
  have hdomainVote : domain S.E S.hc r .g1 < t := by
    dsimp only [t]
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact (Protocol.proposal_time_mono S.E (Nat.le_succ _)).trans_lt
      (Protocol.proposal_time_lt_vote_time S.E _)
  have hvoteAction : t ≤ S.a r := by
    exact (next_vote_time_lt_action S r).le
  have hg1Horizon : domain S.E S.hc r .g1 ≤ rho.horizon := by
    have hle : domain S.E S.hc r .g1 ≤ domain S.E S.hc r .g0 := by
      simp only [domain, Phase.domainOffset]
      linarith [S.E.Δ_pos]
    exact hle.trans ready.2
  have hbase := FrameCompleted.frame_phase_completed
    S rho adm.toNamedAdmissibleCore w hw r hr .g1 t hdomainVote
      hvoteAction hg1Horizon
  have hbase' :
      (DecoupledConsensusModel.Protocol.readFrame before.cache
        before.st.core.toHealing r).g1 =
        some ((storeRoot S.E S.hc
          (readAt S rho (domain S.E S.hc r .g1) w).st r .g1).map
            (fun X => DecoupledConsensusModel.Protocol.clipGrade X
              before.st.core.F)) := by
    simpa only [before, storeRoot, phaseRoot, PhaseGrades.readAt] using hbase
  have hprepared := NamedOutageClosure.frame_phase_prepared_eq
    S rho w r .g1 t hround _ hbase'
  have hreadFrame :
      (DecoupledConsensusModel.Protocol.readFrame read.cache
        read.st.core.toHealing r).g1 =
        some ((storeRoot S.E S.hc
          (readAt S rho (domain S.E S.hc r .g1) w).st r .g1).map
            (fun X => DecoupledConsensusModel.Protocol.clipGrade X
              read.st.core.F)) := by
    simpa only [read, before, t, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom] using hprepared
  cases hstore : storeRoot S.E S.hc
      (readAt S rho (domain S.E S.hc r .g1) w).st r .g1 with
  | none =>
      simp only [hstore, Option.map_none] at hreadFrame
      rw [hframe] at hreadFrame
      cases hreadFrame
  | some raw =>
      have hrootEq : root =
          DecoupledConsensusModel.Protocol.clipGrade raw read.st.core.F := by
        have hopt : some (some root) = some
            (some (DecoupledConsensusModel.Protocol.clipGrade raw read.st.core.F)) :=
          hframe.symm.trans (by
            simpa only [hstore, Option.map_some] using hreadFrame)
        exact Option.some.inj (Option.some.inj hopt)
      have hLroot : Block.Preceq L root := by
        unfold DecoupledConsensusModel.Protocol.activePrefix at hactive
        exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).2
      have hLraw : Block.Preceq L raw := by
        rw [hrootEq] at hLroot
        exact Block.preceq_trans hLroot
          (NamedOutageClosure.q10_clip_preceq raw read.st.core.F)
      have hrawGrade : phaseGrade S.E S.hc
          (readAt S rho (domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
          (readAt S rho (domain S.E S.hc r .g1) w).st.core.F
          r .g1 raw = true := by
        exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hstore)).2
      exact phaseGrade_of_preceq_genuine S.E S.hc _ _ r .g1
        hLraw hrawGrade


/-- Q2 capture yields the selected block's relative G2 grade at the source
domain. The active-prefix projection can only move down the captured raw
root, and relative grades are closed under ancestors. -/
theorem selectedQ2_storeGrade_at_g2Domain
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {p : V} {Q : Block V}
    (hselected : PhaseGrades.nodeQ2 S (actionReadAt S rho p r) r = some Q) :
    PhaseGrades.storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc r .g2) p).st r .g2 Q = true := by
  let i := strictEventIndex rho (S.a r)
  have hread := stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.a r)
  have hreadp := congrFun hread p
  have hselected0 := hselected
  simp only [PhaseGrades.nodeQ2, PhaseGrades.nodeRead,
    NamedProfile.gradeContract, DecoupledConsensusModel.Protocol.frameContract] at hselected0
  unfold actionReadAt NamedActionReads.actionReadAt at hselected0
  rw [hreadp] at hselected0
  have hselected' : Protocol.grade2_block_with
      (NamedProfile.gradeContract
        (NamedActionReads.actionReadFrom S
          (NamedRun.stateBefore S rho i p) r).cache)
      S.E S.hc
      (NamedActionReads.actionReadFrom S
        (NamedRun.stateBefore S rho i p) r).st.core.toHealing r = some Q := by
    simpa only [i] using hselected0
  obtain ⟨j, raw, -, hj, hfreeze, hQraw⟩ :=
    contractQ2_capture_at_action_index S rho i p r hselected'
  have hrawGrade : PhaseGrades.phaseGrade S.E S.hc
      (NamedRun.stateBefore S rho j p).st.core.toHealing.gradeView
      (NamedRun.stateBefore S rho j p).st.core.F r .g2 raw = true := by
    simpa only [PhaseGrades.phaseGrade, DecoupledConsensusModel.Protocol.freezeRoot]
      using (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hfreeze)).2
  have hQgrade := phaseGrade_of_preceq_genuine S.E S.hc
    (NamedRun.stateBefore S rho j p).st.core.toHealing.gradeView
    (NamedRun.stateBefore S rho j p).st.core.F r .g2 hQraw hrawGrade
  have hjState := Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hj
  change PhaseGrades.phaseGrade S.E S.hc
    (Run.stateBefore S rho j p).st.core.toHealing.gradeView
    (Run.stateBefore S rho j p).st.core.F r .g2 Q = true at hQgrade
  rw [hjState] at hQgrade
  simpa only [PhaseGrades.storeGrade, PhaseGrades.readAt] using hQgrade

#print axioms selectedQ2_storeGrade_at_g2Domain


/-- The finite recovery cap retains the selected named Q2 body in both exact
filtered reads used by the opening vote. -/
theorem selectedQ2_filtered_at_action_and_openingVote_of_prefixCap
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {r : Round} (ready : GradeRoundReady S rho r)
    {p : V} (hp : p ∈ rho.honest) {Q : NamedBlock V}
    (hselected : PhaseGrades.nodeQ2 S (actionReadAt S rho p r) r =
      some Q.erase)
    (hQmem : Q ∈ (actionStoreAt S rho p r).st.bodies)
    {stop : Nat} {hF0 blocked : Height}
    (hcap : HonestPrefixFinalityCap S rho stop hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (hQheight : (Protocol.derive_named S.E S.cfg Q).h = blocked + 1)
    (hactionPrefix : strictEventIndex rho (S.a r) ≤ stop)
    (hfrontier : honestHMaxBeforeIndex S rho stop < blocked + 2)
    {reader : V} (hreader : reader ∈ rho.honest) :
    Q.erase ∈ filteredTree (actionDutyRead S rho reader r) ∧
      Q.erase ∈ filteredTree
        (voteDutyRead S rho reader (S.hc.opening_slot r)) := by
  let voteRead := Protocol.vote_time S.E (S.hc.opening_slot r)
  let frame := heightRegimeFrame_of_recovery S adm hbelow hcap hrec hfrontier
  have hbodies := selectedQ2_body_at_action_and_openingVote_of_floor
    S adm ready hp hselected hQmem frame.floor hQheight
      (Protocol.preceq_genesis Q.erase) hactionPrefix hreader
  have hvoteAction : voteRead ≤ S.a r := by
    dsimp only [voteRead]
    calc
      Protocol.vote_time S.E (S.hc.opening_slot r) ≤
          Protocol.confirmation_time S.E (S.hc.opening_slot r) :=
        Protocol.vote_time_le_confirmation_time S.E _
      _ = S.a r := opening_confirmation_time_eq_action S r
  have filteredAt : ∀ t : Time, strictEventIndex rho t ≤ stop →
      Q ∈ (rho.stateBeforeTime S t reader).st.bodies →
      Q.erase ∈ Protocol.get_filtered_block_tree
        (rho.stateBeforeTime S t reader).st.core.toHealing.toFG := by
    intro t ht hbody
    have heq := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed t) reader
    have hbodyIndex := hbody
    change Q ∈ (NamedRun.stateBeforeTime S rho t reader).st.bodies at hbodyIndex
    rw [heq] at hbodyIndex
    have hcoh :=
      (Proofs.NamedRuntime.stateBefore_invariants S rho
        (strictEventIndex rho t) reader).1.1.1
    have htree : Q.erase ∈
        (rho.stateBefore S (strictEventIndex rho t) reader).st.core.T := by
      rw [hcoh.1]
      exact Finset.mem_image_of_mem NamedBlock.erase hbodyIndex
    have hview := Proofs.NamedStoreBridge.derivedView_stateBefore S rho
      (strictEventIndex rho t) reader Q hbodyIndex
    have hstored :
        ((rho.stateBefore S (strictEventIndex rho t) reader).st.core.σ
          Q.erase).h = blocked + 1 := by
      rw [hview, hQheight]
    have hfiltered := frame.fgRoot_preceq_and_filteredMem adm hfrontier
      hreader ht htree hstored (Protocol.preceq_genesis Q.erase)
    rw [← heq] at hfiltered
    exact hfiltered.2
  have hactionFiltered := filteredAt (S.a r) hactionPrefix (by
    simpa only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
      NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hbodies.1)
  have hvoteFiltered := filteredAt voteRead
    ((strictEventIndex_mono rho hvoteAction).trans hactionPrefix) (by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
        Protocol.NamedStore.setClock, voteRead] using hbodies.2)
  constructor
  · simpa only [filteredTree, actionDutyRead, actionReadAt] using
      hactionFiltered
  · simpa only [filteredTree, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      voteRead] using hvoteFiltered

/-! ## Named selector split -/

theorem actionFGSource_genuineClear_or_selectedG2_named
    (S : Setup V) (rho : Run V) (v : V) (r : Round)
    {Q B : Block V}
    (hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r = some Q)
    (hB : actionFGSource S (actionStoreAt S rho v r) = some B) :
    (∃ C : Block V,
      GenuineConfirmationWith
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadAt S rho v (S.a r)).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r))
          (S.hc.opening_slot r) C ∧
      C = (actionStoreAt S rho v r).st.core.live_confirmed ∧
      Protocol.deepest_clear (some Q)
        (actionStoreAt S rho v r).st.core.live_confirmed
        ((NamedProfile.gradeContract
          (actionStoreAt S rho v r).cache).read S.E S.hc
          (actionStoreAt S rho v r).st.core.toHealing r).clear = some B ∧
      Block.Preceq Q B ∧ Block.Preceq B C) ∨
    B = Q := by
  let ast := actionStoreAt S rho v r
  let gc := NamedProfile.gradeContract ast.cache
  let st := ast.st.core.toHealing
  have hQ' : Protocol.grade2_block_with gc S.E S.hc st r = some Q := by
    simpa only [ast, gc, st, PhaseGrades.nodeQ2, PhaseGrades.nodeRead,
      Protocol.grade2_block_with, NamedProfile.gradeContract,
      DecoupledConsensusModel.Protocol.frameContract] using hQ
  have hB' : Protocol.fg_source_with gc S.E S.hc st r
      (Protocol.grade2_block_with gc S.E S.hc st r) = some B := by
    have hround : S.hc.round_of st.s = r := by
      simpa only [st, ast, Protocol.Store.toHealing] using
        actionStoreAt_round S rho v r
    have h := hB
    change Protocol.fg_source_with
        (NamedProfile.gradeContract ast.cache) S.E S.hc st
        (S.hc.round_of st.s)
        (Protocol.grade2_block_with
          (NamedProfile.gradeContract ast.cache) S.E S.hc st
          (S.hc.round_of st.s)) = some B at h
    rw [hround] at h
    simpa only [gc] using h
  rw [hQ'] at hB'
  change (match Protocol.deepest_clear (some Q) st.live_confirmed
      (gc.read S.E S.hc st r).clear with
    | some X => some X
    | none => some Q) = some B at hB'
  cases hwalk : Protocol.deepest_clear (some Q) st.live_confirmed
      (gc.read S.E S.hc st r).clear with
  | none =>
      right
      exact (Option.some.inj (by simpa [hwalk] using hB')).symm
  | some W =>
      have hWB : W = B := Option.some.inj (by simpa [hwalk] using hB')
      have hmem := Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hwalk)
      have hQW : Block.Preceq Q W := hmem.2.1
      rcases actionStoreAt_liveConfirmed_genuine_or_fgRoot S rho v r with
        hconfirmed | hroot
      · rcases hconfirmed with ⟨C, hC, hClive⟩
        left
        refine ⟨C, ?_, ?_, ?_, hWB ▸ hQW, ?_⟩
        · simpa only [ast, gc] using hC
        · simpa only [ast] using hClive
        · simpa only [hWB, ast, gc, st] using hwalk
        · have hWC : Block.Preceq W C := by
            rw [hClive]
            exact Proofs.Engine.deepest_clear_preceq hwalk
          exact hWB ▸ hWC
      · rcases hroot with ⟨R, hRroot, hRlive⟩
        have hRast : R = Protocol.get_fg_root ast.st.core.toHealing.toFG := by
          calc
            R = Protocol.get_fg_root
                (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r)).toHealing.toFG :=
              hRroot
            _ = Protocol.get_fg_root ast.st.core.toHealing.toFG := by
              rw [actionStoreAt_eq_update_confirmation_confStore]
              rfl
        have hQfiltered : Q ∈ PhaseGrades.filteredTree
            (actionReadAt S rho v r) := by
          exact actionQ2_mem_filteredTree S rho v r hQ
        have hRQ : Block.Preceq R Q := by
          rw [hRast]
          exact Proofs.Records.preceq_get_fg_root_of_mem_filtered hQfiltered
        have hWR : Block.Preceq W R := by
          have hRlive' : R = ast.st.core.live_confirmed := by
            simpa only [ast] using hRlive
          simpa only [hWB, hRlive', st] using
            Proofs.Engine.deepest_clear_preceq hwalk
        have hWQ : Block.Preceq W Q := Block.preceq_trans hWR hRQ
        have hWQeq : W = Q := Block.preceq_antisymm hWQ hQW
        right
        exact hWB ▸ hWQeq

#print axioms actionFGSource_genuineClear_or_selectedG2_named





omit [Fintype V] in
private theorem named_ancestor_body_mem_genuine
    {st : Protocol.NamedStore V} (hpc : NamedStore.NamedParentClosed st)
    {A B : NamedBlock V} (hB : B ∈ st.bodies)
    (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq,
        decide_eq_true_eq] at hAB
      exact hAB ▸ hB
  | node parent slot root votes support rows proposer ih =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hparent
      · exact hB
      · exact ih (hpc.2 _ hB) hparent

/-- A genuine opening confirmation relays its named ancestor into every
honest first-interior vote read. -/
theorem ancestorGenuineConfirmation_body_at_nextVote_of_floor
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (ready : GradeRoundReady S rho r)
    {p : V} (hp : p ∈ rho.honest) {B : NamedBlock V} {C : Block V}
    {contract : Protocol.GradeContract V}
    (hgenuine : GenuineConfirmationWith contract S.E S.hc
      (Proofs.Optimistic.confStore S rho p (S.hc.opening_slot r))
      (S.hc.opening_slot r) C)
    (hBC : Block.Preceq B.erase C)
    (hBmem : B ∈ (actionStoreAt S rho p r).st.bodies)
    {stop : Nat} {blocked : Height} {Tprev : Block V}
    (hfloor : FinalityFloorAt S rho blocked stop Tprev)
    (hBheight :
      (Protocol.derive_named S.E S.cfg B).h = blocked + 1)
    (hTB : Block.Preceq Tprev B.erase)
    (hactionPrefix : strictEventIndex rho (S.a r) ≤ stop)
    (hactionHor : S.a r ≤ rho.horizon)
    {reader : V} (hreader : reader ∈ rho.honest) :
    B ∈ (voteDutyRead S rho reader
      (S.hc.opening_slot r + 1)).st.bodies := by
  let s := S.hc.opening_slot r
  let support := Protocol.support_cutoff S.E s
  let view := Protocol.view_freeze S.E s
  let vote := Protocol.vote_time S.E (s + 1)
  have hBscope : NamedRun.blockInRun S rho B :=
    actionBody_runBlock_genuine S adm hp hBmem
  have hvoteAction : vote ≤ S.a r := by
    dsimp only [vote, s]
    exact (next_vote_time_lt_action S r).le
  have hvotePrefix : strictEventIndex rho vote ≤ stop :=
    (strictEventIndex_mono rho hvoteAction).trans hactionPrefix
  have hFvote : Block.Preceq
      (NamedRun.stateBeforeTime S rho vote reader).st.core.F B.erase := by
    rw [congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed vote) reader]
    exact hfloor.storeF_preceq_sourceHeightBlock hreader hvotePrefix
      hBscope hBheight hTB
  have hordinary : GenuineConfirmation (contract := contract) S.E S.hc
      (Proofs.Optimistic.confStore S rho p s) s C :=
    ⟨hgenuine.selected, hgenuine.genuine⟩
  have hN := confNumerator S.E (Proofs.Optimistic.confStore S rho p s) s
  have hpositive : 0 <
      (Protocol.goldfishSupporters S.E (Proofs.Optimistic.confStore S rho p s).T
        (confVotes S.E (Proofs.Optimistic.confStore S rho p s) s)
        (confVotes S.E (Proofs.Optimistic.confStore S rho p s) s) s C).card := by
    have heligible := hordinary.eligible
    rw [hN.score_eq_supporters] at heligible
    by_contra hnot
    have hzero :
        (Protocol.goldfishSupporters S.E (Proofs.Optimistic.confStore S rho p s).T
          (confVotes S.E (Proofs.Optimistic.confStore S rho p s) s)
          (confVotes S.E (Proofs.Optimistic.confStore S rho p s) s) s C).card = 0 :=
      Nat.eq_zero_of_not_pos hnot
    rw [hzero] at heligible
    simp at heligible
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpositive
  rw [mem_supporters_iff] at hu
  obtain ⟨-, u, huBy, -, htargets⟩ := hu
  rw [Protocol.votes_by, Finset.mem_filter] at huBy
  obtain ⟨head, hfind, hChead⟩ := targets_under_iff.mp htargets
  by_cases hgen : head = Block.genesis
  · subst head
    have hCgen : C = Block.genesis :=
      Block.preceq_antisymm hChead.2 (Protocol.preceq_genesis C)
    subst C
    have hBgen : B.erase = Block.genesis :=
      Block.preceq_antisymm hBC (Protocol.preceq_genesis B.erase)
    have hBeq : B = NamedBlock.genesis := by
      cases B <;> simp_all [NamedBlock.erase]
    subst B
    exact (Proofs.NamedRuntime.stateBeforeTime_invariants
      S rho vote reader).1.1.1.2.2.1.1
  · have hheadSource : head ∈ (Proofs.Optimistic.confStore S rho p s).T :=
      Proofs.HealingLemmas.find?_mem hfind
    have hearly : u ∈ confEarly S.E (Proofs.Optimistic.confStore S rho p s) s :=
      (Finset.mem_filter.mp huBy.1).1
    have hresolved : stampedBefore
        (Proofs.Optimistic.confStore S rho p s).tau support u = true := by
      rw [confEarly, beforeCutoff, Finset.mem_filter] at hearly
      exact hearly.2
    have hheadStamp : stampedBefore
        (Proofs.Optimistic.confStore S rho p s).timestamp_block support head = true :=
      HonestWeightMajority.stampedBefore_block_of_resolution hfind hresolved
    have hheadPre : head ∈
        (NamedRun.stateBeforeTime S rho
          (Protocol.confirmation_time S.E s) p).st.core.T := by
      simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
        Run.storeBeforeTime] using hheadSource
    obtain ⟨Hn, hHnPre, hHnErase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
        S rho (Protocol.confirmation_time S.E s) p hheadPre
    have hstampPre : stampedBefore
        (NamedRun.stateBeforeTime S rho
          (Protocol.confirmation_time S.E s) p).st.core.timestamp_block
        support Hn.erase = true := by
      simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
        Run.storeBeforeTime, hHnErase] using hheadStamp
    have hsupportPublic : PublicTime S support := by
      dsimp only [support]
      exact Protocol.publicTime_support_cutoff S s
    have hHsupport : Hn ∈
        (NamedRun.stateBeforeTime S rho support p).st.bodies :=
      NamedPublicCutBody.body_mem_stateBeforeTime_of_public_stampedBefore
        S rho adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
          hsupportPublic hHnPre hstampPre
    have hpostSupport : S.E.t_GST ≤ support := by
      apply ready.1.trans
      dsimp only [support, s]
      unfold early opening Phase.earlyOffset Protocol.proposal_time
        Protocol.support_cutoff Env.t Protocol.HealConfig.opening_slot
        slotStart
      linarith [S.E.Δ_pos]
    have hdeadline : max support S.E.t_GST + S.E.Δ ≤ view := by
      rw [max_eq_left hpostSupport]
      dsimp only [support, view]
      exact le_of_eq
        (Protocol.support_cutoff_add_delta_eq_view_freeze S.E s)
    have hviewVote : view ≤ vote := by
      dsimp only [view, vote]
      exact (Protocol.view_freeze_lt_vote_time_succ S.E s).le
    have hviewHorizon : view ≤ rho.horizon :=
      hviewVote.trans (hvoteAction.trans hactionHor)
    have hFhead : Block.Preceq
        (NamedRun.stateBeforeTime S rho vote reader).st.core.F Hn.erase :=
      Block.preceq_trans hFvote (by
        rw [hHnErase]
        exact Block.preceq_trans hBC hChead.2)
    obtain ⟨hHvote, -, -⟩ :=
      NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
        S rho adm.toNamedAdmissibleCore p hp reader hreader Hn
          support view vote hHsupport hdeadline hviewVote
          hviewHorizon hFhead
    have hHscope : NamedRun.blockInRun S rho Hn := by
      obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
        S rho adm.toNamedAdmissibleCore.sorted vote
      rw [hn] at hHvote
      exact Proofs.Bridges.runBlock_of_stateBefore_mem S hreader hHvote
    have hBH : NamedBlock.Preceq B Hn :=
      Protocol.namedPreceq_of_runBlock_erase_preceq
        adm hBscope hHscope (by
          rw [hHnErase]
          exact Block.preceq_trans hBC hChead.2)
    have hpc := (Proofs.NamedRuntime.stateBeforeTime_invariants
      S rho vote reader).1.1.1.2.2.1
    have hBvote := named_ancestor_body_mem_genuine hpc hHvote hBH
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, Protocol.NamedStore.setClock,
      vote] using hBvote

#print axioms ancestorGenuineConfirmation_body_at_nextVote_of_floor




private theorem voteDuty_hMax_le_of_noHeightProgress_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {H : Height} {through : Time} {w : V} (hw : w ∈ rho.honest)
    {s : Slot}
    (hno : ¬ HonestHeightFilterProgressAboveThrough S rho H through)
    (hread : Protocol.vote_time S.E s ≤ through) :
    (voteDutyRead S rho w s).st.core.h_max ≤ H + 1 := by
  let read := Protocol.vote_time S.E s
  have hstrict : rho.storeBeforeTime S w read =
      rho.storeAt S w (read - 1) :=
    storeBeforeTime_eq_storeAt_sub_one_recovery S rho w read
  have hlocal : (rho.storeBeforeTime S w read).core.h_max ≤
      (rho.storeAt S w read).core.h_max := by
    rw [hstrict]
    exact stateAt_h_max_mono S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed w
      (sub_le_self read (by norm_num : (0 : Time) ≤ 1))
  by_contra hnot
  have hgt : H + 1 < (voteDutyRead S rho w s).st.core.h_max :=
    Nat.lt_of_not_ge hnot
  have hgtAt : H + 1 < (rho.storeAt S w read).core.h_max := by
    apply lt_of_lt_of_le hgt
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, Protocol.NamedStore.setClock, read]
      using hlocal
  apply hno
  exact ⟨w, hw, read, hread, Nat.succ_le_iff.mpr hgtAt⟩

/-- In the no-progress branch, the relayed genuine descendant makes the
protected named ancestor a candidate in the exact prepared vote read. -/
private theorem ancestorGenuineConfirmation_candidate_at_nextVote
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (ready : GradeRoundReady S rho r)
    (hactionHor : S.a r ≤ rho.horizon)
    {p : V} (hp : p ∈ rho.honest)
    {B : NamedBlock V} {C : Block V}
    {contract : Protocol.GradeContract V}
    (hgenuine : GenuineConfirmationWith contract S.E S.hc
      (Proofs.Optimistic.confStore S rho p (S.hc.opening_slot r))
      (S.hc.opening_slot r) C)
    (hBC : Block.Preceq B.erase C)
    (hBheight : (Protocol.derive_named S.E S.cfg B).h = H + 1)
    {through : Time}
    (hno : ¬ HonestHeightFilterProgressAboveThrough S rho (H + 1) through)
    (hvoteThrough :
      Protocol.vote_time S.E (S.hc.opening_slot r + 1) ≤ through)
    {w : V} (hw : w ∈ rho.honest)
    (hBbody : B ∈
      (voteDutyRead S rho w (S.hc.opening_slot r + 1)).st.bodies)
    (hBfiltered : B.erase ∈
      filteredTree (voteDutyRead S rho w (S.hc.opening_slot r + 1))) :
    B.erase ∈ Proofs.Optimistic.voter_candidate_tree S.E
      (voteDutyRead S rho w
        (S.hc.opening_slot r + 1)).st.core.toHealing := by
  let s := S.hc.opening_slot r
  let read := voteDutyRead S rho w (s + 1)
  let duty := Proofs.Optimistic.voteDutyStore S rho w (s + 1)
  have hrootC : Block.Preceq
      (Protocol.get_fg_root duty.toHealing.toFG) C := by
    apply Block.preceq_trans _ hBC
    have hrootB := Proofs.Records.preceq_get_fg_root_of_mem_filtered hBfiltered
    simpa only [duty, read, s, filteredTree, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
      Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hrootB
  have hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s := by
    apply ready.1.trans
    simp only [s, early, opening, Phase.earlyOffset,
      Protocol.proposal_time]
    linarith [S.E.Δ_pos]
  have hsourceHor : Protocol.confirmation_time S.E s ≤ rho.horizon := by
    simpa only [s, opening_confirmation_time_eq_action S r] using hactionHor
  have hCprocessed : C ∈ Protocol.voter_processed_block_tree S.E
      duty.toHealing.toFG.toSG.toGoldfishStore duty.toHealing.s := by
    have hg : GenuineConfirmation (contract := contract) S.E S.hc
        (Proofs.Optimistic.confStore S rho p s) s C :=
      ⟨hgenuine.selected, hgenuine.genuine⟩
    exact Protocol.voterProcessedTarget_of_genuineConfirmation_after_gst
      S adm hp hw hpost hsourceHor hg hrootC
  have hBprocessedDuty : B.erase ∈ Protocol.voter_processed_block_tree S.E
      duty.toHealing.toFG.toSG.toGoldfishStore duty.toHealing.s :=
    WeakGoldfish.ancestorProcessed_of_voterProcessed
      S adm.toNamedAdmissibleCore hw hCprocessed B.erase hBC
  have hBprocessed : B.erase ∈ Protocol.voter_processed_block_tree S.E
      read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.toHealing.s := by
    simpa only [duty, read, s, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
      Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hBprocessedDuty
  have hBpre : B ∈ (NamedRun.stateBeforeTime S rho
      (Protocol.vote_time S.E (s + 1)) w).st.bodies := by
    simpa only [read, s, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, Protocol.NamedStore.setClock] using hBbody
  have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho
    (Protocol.vote_time S.E (s + 1)) w B hBpre
  have hstored : (read.st.core.σ B.erase).h = H + 1 := by
    have hheight := congrArg (fun st => st.h) hview
    calc
      (read.st.core.σ B.erase).h =
          (Protocol.derive_named S.E S.cfg B).h := by
        simpa only [read, voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock] using hheight
      _ = H + 1 := hBheight
  have hmax : read.st.core.h_max ≤ H + 2 := by
    simpa only [read, s] using
      (voteDuty_hMax_le_of_noHeightProgress_named
        S adm hw hno hvoteThrough)
  apply Protocol.voterCandidate_of_processed_self_and_filtered
    S.E read.st.core.toHealing hBprocessed
  · change read.st.core.h_max - 1 ≤ (read.st.core.σ B.erase).h
    rw [hstored]
    exact Nat.sub_le_iff_le_add.mpr (by simpa [Nat.add_assoc] using hmax)
  · exact hBfiltered

/-- The prepared adoption bundle drives the exact runtime head above its
target. This is the contract-carrying twin of the previous bare-duty head step. -/
private theorem preceq_voterHeadAt_of_namedNextVoteAdoption
    (S : Setup V) {rho : Run V} {source : Protocol.Store V}
    {s : Slot} {B : Block V} {w : V}
    (heligible : Protocol.voters_count S.E (confLate S.E source s) s <
      2 * Protocol.goldfish_score S.E source.T
        (confVotes S.E source s) (confVotes S.E source s) s B)
    (hadopt : NamedNextVoteAdoption S rho source s B w) :
    Block.Preceq B (voterHeadAt S rho w (s + 1)) := by
  let read := voteDutyRead S rho w (s + 1)
  let st := read.st.core
  let tree := voterCandidateTreeAt S rho w (s + 1)
  let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  have hslot : st.s = s + 1 := by
    simpa only [st, read] using Proofs.Optimistic.voteDutyRead_slot S rho w (s + 1)
  have hprev : st.s - 1 = s := by
    rw [hslot]
    simp
  change Block.Preceq B
    (Protocol.get_head_in_tree_with_layer
      (NamedProfile.gradeContract read.cache) S.E S.hc st.toHealing
      tree votes support (st.s - 1))
  rw [Proofs.Optimistic.get_head_in_tree_split_with]
  rw [hprev]
  simpa only [Protocol.Store.toHealing, read, st] using
    (Protocol.goldfish_fork_choice_captures_of_confirmation
      S.E st.σ st.h_max source.T st.T tree st.s
      (confEarly S.E source s) (confLate S.E source s)
      (confVotes S.E source s) votes support s
      (confNumerator S.E source s) hadopt.transport heligible
        hadopt.support_subset hadopt.anchor hadopt.path)

private theorem ancestorConfirmation_eligible_with_of_preceq
    (E : Env V) (hc : Protocol.HealConfig) (source : Protocol.Store V)
    (s : Slot) {T C : Block V} {contract : Protocol.GradeContract V}
    (hTC : Block.Preceq T C)
    (hC : GenuineConfirmationWith contract E hc source s C) :
    Protocol.voters_count E (confLate E source s) s <
      2 * Protocol.goldfish_score E source.T
        (confVotes E source s) (confVotes E source s) s T := by
  have hN := confNumerator E source s
  have hsupport := supporters_mono E source.T
    (confVotes E source s) (confVotes E source s) s hTC
  have hcard := Finset.card_le_card hsupport
  have hCg : GenuineConfirmation E hc source s C (contract := contract) :=
    ⟨hC.selected, hC.genuine⟩
  have hCeligible := hCg.eligible
  rw [hN.score_eq_supporters] at hCeligible ⊢
  exact lt_of_lt_of_le hCeligible (Nat.mul_le_mul_left 2 hcard)


/-- The genuine-clear next-vote consumer with earlier's contract. Unlike the
older K6 form, the active-anchor case consumes compatibility directly and
does not reconstruct it from common action-frontier data. -/
theorem genuineClear_nextVoteCone_or_heightProgressThrough_of_mainInputs
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (ready : GradeRoundReady S rho r)
    {p : V} (hp : p ∈ rho.honest) {B : NamedBlock V} {C : Block V}
    {contract : Protocol.GradeContract V}
    (hgenuine : GenuineConfirmationWith contract S.E S.hc
      (Proofs.Optimistic.confStore S rho p (S.hc.opening_slot r))
      (S.hc.opening_slot r) C)
    (hBC : Block.Preceq B.erase C)
    (hBmem : B ∈ (actionStoreAt S rho p r).st.bodies)
    {H : Height}
    (hBheight : (Protocol.derive_named S.E S.cfg B).h = H + 1)
    (hactionHor : S.a r ≤ rho.horizon)
    (hmain : VoterAnchorSourceClearInputsMain S rho r p B.erase)
    {through : Time}
    (hvoteThrough :
      Protocol.vote_time S.E (S.hc.opening_slot r + 1) ≤ through) :
    HonestHeightFilterProgressAboveThrough S rho (H + 1) through ∨
      ((∀ w ∈ rho.honest,
        Block.Preceq B.erase
          (voterHeadAt S rho w (S.hc.opening_slot r + 1))) ∧
        NamedHonestVotesCone S rho (S.hc.opening_slot r + 1)
          (fun X => Block.Preceq B.erase X)) := by
  let s := S.hc.opening_slot r
  have hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s := by
    apply ready.1.trans
    simp only [s, early, opening, Phase.earlyOffset,
      Protocol.proposal_time]
    linarith [S.E.Δ_pos]
  have hsourceHor : Protocol.confirmation_time S.E s ≤ rho.horizon := by
    simpa only [s, opening_confirmation_time_eq_action S r] using hactionHor
  have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon :=
    (next_vote_time_lt_action S r).le.trans hactionHor
  by_cases hprogress :
      HonestHeightFilterProgressAboveThrough S rho (H + 1) through
  · exact Or.inl hprogress
  · right
    have hfiltered : ∀ w ∈ rho.honest, B.erase ∈
        filteredTree (voteDutyRead S rho w (s + 1)) := by
      intro w hw
      simpa only [s] using hmain.nextTarget w hw
    have hbody : ∀ w ∈ rho.honest, B ∈
        (voteDutyRead S rho w (s + 1)).st.bodies := by
      intro w hw
      exact actionBody_at_voteDuty_of_filtered S adm hp hBmem hw
        (hfiltered w hw)
    have hheads : ∀ w ∈ rho.honest,
        Block.Preceq B.erase (voterHeadAt S rho w (s + 1)) := by
      intro w hw
      have adopt (hanchor : Block.Preceq
          (voterAnchorAt S rho w (s + 1)) B.erase) :
          Block.Preceq B.erase (voterHeadAt S rho w (s + 1)) := by
        have hcandidate := ancestorGenuineConfirmation_candidate_at_nextVote
          S adm ready hactionHor hp hgenuine hBC hBheight hprogress
            hvoteThrough hw (hbody w hw) (hfiltered w hw)
        have hanchor' : Block.Preceq
            (Protocol.get_sg_root_with
              (NamedProfile.gradeContract
                (voteDutyRead S rho w (s + 1)).cache)
              S.E S.hc
              (voteDutyRead S rho w (s + 1)).st.core.toHealing
              (S.hc.round_of
                (voteDutyRead S rho w (s + 1)).st.core.s)) B.erase := by
          simpa only [voterAnchorAt, nodeAnchor, nodeRead] using hanchor
        have hadopt := nextVoteAdoption_of_frozenCandidateAtRead
          S adm hp hpost hsourceHor hw hcandidate hanchor'
        exact preceq_voterHeadAt_of_namedNextVoteAdoption S
          (ancestorConfirmation_eligible_with_of_preceq S.E S.hc
            (Proofs.Optimistic.confStore S rho p s) s hBC hgenuine) hadopt
      have hcompat := hmain.anchorCompatible w hw
        (voterAnchorAt S rho w (s + 1)) (by rfl)
      simp only [Block.compatible, Bool.or_eq_true] at hcompat
      rcases hcompat with hanchor | hsourceAnchor
      · exact adopt hanchor
      · exact Block.preceq_trans hsourceAnchor
          (voterAnchorAt_preceq_voterHeadAt S rho w (s + 1))
    refine ⟨hheads, ?_⟩
    intro w hw hcommittee
    obtain ⟨X, hXhead, hXrun, hXemit⟩ := named_voter_head_emits
      S adm hw (s := s + 1) (Nat.succ_pos s) hcommittee hvoteHor
    exact ⟨X, by rw [hXhead]; exact hheads w hw, hXrun, hXemit⟩

#print axioms genuineClear_nextVoteCone_or_heightProgressThrough_of_mainInputs


















/-- A transported G0 anchor is compatible with the action's clear source.
K6 keeps the anchor below the clipped G0 root read by the action. -/
private theorem activeVoterAnchor_compatible_clearSource
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (hr : 0 < r) (ready : GradeRoundReady S rho r)
    (hactionHor : S.a r ≤ rho.horizon)
    {p : V} (hp : p ∈ rho.honest) {L B : Block V}
    (hLgrade : storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc r .g0) p).st r .g0 L = true)
    (hLsource : L ∈
      filteredTree (readAt S rho (domain S.E S.hc r .g0) p))
    (hLaction : L ∈ filteredTree (actionDutyRead S rho p r))
    (hBclear : nodeClear S (actionReadAt S rho p r) r B = true) :
    Block.compatible L B = true := by
  have hLtree : L ∈
      (readAt S rho (domain S.E S.hc r .g0) p).st.core.T :=
    Proofs.Records.get_filtered_block_tree_subset _ hLsource
  obtain ⟨raw, hraw, hLraw⟩ := NamedOutageClosure.q10_freeze_of_graded
    S.E
    (readAt S rho (domain S.E S.hc r .g0) p).st.core.toHealing.gradeView
    (readAt S rho (domain S.E S.hc r .g0) p).st.core.F
    S.hc.η_SG r (e := early S.E S.hc r .g0)
    (l := late S.E S.hc r .g0)
    (by simp only [early, late, Phase.earlyOffset, Phase.lateOffset]; exact le_rfl)
    hLtree (by simpa only [storeGrade] using hLgrade)
  have hactionFrame := actionFrame_g0 S adm.toNamedAdmissibleCore
    hp hr hactionHor
  have hframe :
      (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho p r).cache
        (actionReadAt S rho p r).st.core.toHealing r).g0 =
        some (some (DecoupledConsensusModel.Protocol.clipGrade raw
          (actionReadAt S rho p r).st.core.F)) := by
    simpa only [storeRoot, phaseRoot, hraw, Option.map_some] using hactionFrame
  have hFL : Block.Preceq (actionReadAt S rho p r).st.core.F L :=
    (Finset.mem_filter.mp
      (Finset.mem_filter.mp
        (Finset.mem_filter.mp hLaction).1).1).2
  have hLclip : Block.Preceq L
      (DecoupledConsensusModel.Protocol.clipGrade raw
        (actionReadAt S rho p r).st.core.F) := by
    have hcompat : Block.compatible L
        (actionReadAt S rho p r).st.core.F = true := by
      simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr hFL
    exact (NamedOutageClosure.q10_retained_prefix raw
      (actionReadAt S rho p r).st.core.F L hcompat).mpr hLraw
  have hBclip : Block.compatible B
      (DecoupledConsensusModel.Protocol.clipGrade raw
        (actionReadAt S rho p r).st.core.F) = true := by
    simpa only [nodeClear, nodeRead, NamedProfile.gradeContract,
      DecoupledConsensusModel.Protocol.frameContract, DecoupledConsensusModel.Protocol.frameGradeRead,
      DecoupledConsensusModel.Protocol.clear, hframe] using hBclear
  simp only [Block.compatible, Bool.or_eq_true] at hBclip ⊢
  rcases hBclip with hBclip | hclipB
  · exact (Block.preceq_linear hLclip hBclip).elim Or.inl Or.inr
  · exact Or.inl (Block.preceq_trans hLclip hclipB)
private theorem honestOpeningVotesCone_of_selectedG2_K6
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {r : Round} (hr : 0 < r) (ready : GradeRoundReady S rho r)
    {p : V} (hp : p ∈ rho.honest) {Q : NamedBlock V}
    (hselected : nodeQ2 S (actionReadAt S rho p r) r = some Q.erase)
    (hK6 : VoterAnchorSourceQ2Inputs S rho r p Q.erase) :
    NamedHonestVotesCone S rho (S.hc.opening_slot r)
      (fun X => Block.Preceq Q.erase X) := by
  have hopenPos : 0 < S.hc.opening_slot r := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos hr
      (Nat.lt_of_lt_of_le (by decide : 0 < 2) S.hc.R_ge_two)
  have hround : S.hc.round_of (S.hc.opening_slot r) = r := by
    simp only [Protocol.HealConfig.round_of, Protocol.HealConfig.opening_slot]
    have hR : 0 < S.hc.R :=
      lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two
    simpa only [Nat.mul_comm] using Nat.mul_div_cancel_left r hR
  have hread : domain S.E S.hc r .g1 <
      Protocol.vote_time S.E (S.hc.opening_slot r) := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact Protocol.proposal_time_lt_vote_time S.E _
  have hvoteAction : Protocol.vote_time S.E (S.hc.opening_slot r) ≤
      S.a r :=
    (Protocol.vote_time_le_confirmation_time S.E _).trans (by
      rw [opening_confirmation_time_eq_action])
  have hvoteHorizon : Protocol.vote_time S.E (S.hc.opening_slot r) ≤
      rho.horizon := by
    simpa only [domain, Phase.domainOffset, opening,
      Protocol.vote_time, one_mul] using ready.2
  have hsource : Protocol.grade2_block_with
      (NamedProfile.gradeContract (actionDutyRead S rho p r).cache)
      S.E S.hc (actionDutyRead S rho p r).st.core.toHealing r =
        some Q.erase := by
    simpa only [nodeQ2, nodeRead, actionDutyRead] using hselected
  have hG2 := selectedQ2_storeGrade_at_g2Domain S adm hselected
  apply honestVotesCone_of_selectedActionG2_of_readDisposition
    S adm hr ready hp hsource hopenPos hround hread hvoteAction hvoteHorizon
  · intro w hw _
    have htarget := hK6.g1Target w hw
    have hforward : ∀ sender u root Head,
        u ∈ DecoupledConsensusModel.Protocol.interpretedInputs
          (readAt S rho (domain S.E S.hc r .g2) p).st.core.toHealing.gradeView
          (readAt S rho (domain S.E S.hc r .g2) p).st.core.F
          S.hc.η_SG r (early S.E S.hc r .g2) sender →
        DecoupledConsensusModel.Protocol.localCovers
          (readAt S rho (domain S.E S.hc r .g2) p).st.core.toHealing.gradeView
          u.confirmed Q.erase = true →
        u.confirmed = some root →
        Block.find?
          (readAt S rho (domain S.E S.hc r .g2) p).st.core.T root =
            some Head →
        Block.Preceq
          (readAt S rho (domain S.E S.hc r .g1) w).st.core.F Head := by
      intro sender u root Head _ hcover hconf hfind
      have hFQ := GradeDeliveryRun.finalized_preceq_of_mem_filtered_at_read
        S rho htarget
      apply Block.preceq_trans hFQ
      unfold DecoupledConsensusModel.Protocol.localCovers at hcover
      unfold Protocol.head_covers at hcover
      simp only [Protocol.HealingStore.gradeView, Protocol.Store.toHealing,
        hconf] at hcover
      rw [hfind] at hcover
      exact hcover
    have hbelow := crossReaderFinalizedBelow_of_finalitySafety_and_relay
      S adm hsb ready.1 ready.2 hp hw hforward
    have hguard := crossReaderBodyReadyGuard_of_finalizedBelow
      S adm.toNamedAdmissibleCore hr ready.1 ready.2 hp hw hbelow
    have hG1 := storeGrade_g1_of_storeGrade_g2_cross_reader
      S rho adm.toNamedAdmissibleCore r
        (twoCutoffDelivery_of_core S adm.toNamedAdmissibleCore ready.1)
        ready.2 p w hp hw Q.erase hG2 hguard
    exact ⟨htarget, hG1, hK6.openingTarget w hw⟩
  · intro w hw _
    exact Or.inr (hK6.openingTarget w hw)

private theorem genuineClear_nextVoteCone_or_heightProgressThrough_of_regimeFrame
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {r : Round} (hr : 0 < r) (ready : GradeRoundReady S rho r)
    {p : V} (hp : p ∈ rho.honest) {B : NamedBlock V} {C : Block V}
    {contract : Protocol.GradeContract V}
    (hgenuine : GenuineConfirmationWith contract S.E S.hc
      (Proofs.Optimistic.confStore S rho p (S.hc.opening_slot r))
      (S.hc.opening_slot r) C)
    (hBC : Block.Preceq B.erase C)
    (hBmem : B ∈ (actionStoreAt S rho p r).st.bodies)
    (hBclear : nodeClear S (actionReadAt S rho p r) r B.erase = true)
    {H : Height}
    (hBheight : (Protocol.derive_named S.E S.cfg B).h = H + 1)
    (hactionHor : S.a r ≤ rho.horizon)
    (hK6 : VoterAnchorSourceClearInputs S rho r p B.erase)
    {through : Time}
    (hvoteThrough :
      Protocol.vote_time S.E (S.hc.opening_slot r + 1) ≤ through) :
    HonestHeightFilterProgressAboveThrough S rho (H + 1) through ∨
      ((∀ w ∈ rho.honest,
        Block.Preceq B.erase
          (voterHeadAt S rho w (S.hc.opening_slot r + 1))) ∧
        NamedHonestVotesCone S rho (S.hc.opening_slot r + 1)
          (fun X => Block.Preceq B.erase X)) := by
  let s := S.hc.opening_slot r
  have hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s := by
    apply ready.1.trans
    simp only [s, early, opening, Phase.earlyOffset,
      Protocol.proposal_time]
    linarith [S.E.Δ_pos]
  have hsourceHor : Protocol.confirmation_time S.E s ≤ rho.horizon := by
    simpa only [s, opening_confirmation_time_eq_action S r] using hactionHor
  have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon :=
    (next_vote_time_lt_action S r).le.trans hactionHor
  by_cases hprogress :
      HonestHeightFilterProgressAboveThrough S rho (H + 1) through
  · exact Or.inl hprogress
  · right
    have hfiltered : ∀ w ∈ rho.honest, B.erase ∈
        filteredTree (voteDutyRead S rho w (s + 1)) := by
      intro w hw
      simpa only [s] using hK6.nextTarget w hw
    have hbody : ∀ w ∈ rho.honest, B ∈
        (voteDutyRead S rho w (s + 1)).st.bodies := by
      intro w hw
      exact actionBody_at_voteDuty_of_filtered S adm hp hBmem hw
        (hfiltered w hw)
    have hheads : ∀ w ∈ rho.honest,
        Block.Preceq B.erase (voterHeadAt S rho w (s + 1)) := by
      intro w hw
      have adopt (hanchor : Block.Preceq
          (voterAnchorAt S rho w (s + 1)) B.erase) :
          Block.Preceq B.erase (voterHeadAt S rho w (s + 1)) := by
        have hcandidate := ancestorGenuineConfirmation_candidate_at_nextVote
          S adm ready hactionHor hp hgenuine hBC hBheight hprogress
            hvoteThrough hw (hbody w hw) (hfiltered w hw)
        have hanchor' : Block.Preceq
            (Protocol.get_sg_root_with
              (NamedProfile.gradeContract
                (voteDutyRead S rho w (s + 1)).cache)
              S.E S.hc
              (voteDutyRead S rho w (s + 1)).st.core.toHealing
              (S.hc.round_of
                (voteDutyRead S rho w (s + 1)).st.core.s)) B.erase := by
          simpa only [voterAnchorAt, nodeAnchor, nodeRead] using hanchor
        have hadopt := nextVoteAdoption_of_frozenCandidateAtRead
          S adm hp hpost hsourceHor hw hcandidate hanchor'
        exact preceq_voterHeadAt_of_namedNextVoteAdoption S
          (ancestorConfirmation_eligible_with_of_preceq S.E S.hc
            (Proofs.Optimistic.confStore S rho p s) s hBC hgenuine) hadopt
      rcases voterAnchorAt_cases S rho w (s + 1) with hroot | hactive
      · apply adopt
        rw [hroot]
        exact Proofs.Records.preceq_get_fg_root_of_mem_filtered (hfiltered w hw)
      · obtain ⟨root, L, hframeL, hactiveL, hanchorL⟩ := hactive
        have hroundDuty : S.hc.round_of
            (voteDutyRead S rho w (s + 1)).st.core.s = r := by
          simpa only [Proofs.Optimistic.voteDutyRead_slot] using
            Proofs.HealingLemmas.round_of_opening_succ S.hc r
        rw [hroundDuty] at hframeL
        by_cases hLB : Block.Preceq L B.erase
        · exact adopt (by simpa only [hanchorL] using hLB)
        · obtain ⟨hLsource, hLaction⟩ := hK6.anchor w hw L
            (by simpa only [s] using hanchorL) hLB
          have hLgrade1 := activeVoterAnchor_storeGrade_g1
            S adm hr ready hw (by simpa only [s] using hframeL)
              (by simpa only [s] using hactiveL)
          have hgstG1 : S.E.t_GST ≤ early S.E S.hc r .g1 := by
            exact ready.1.trans (by
              simp only [early, Phase.earlyOffset]
              linarith [S.E.Δ_pos])
          have hforward : ∀ sender u root' Head,
              u ∈ DecoupledConsensusModel.Protocol.interpretedInputs
                (readAt S rho (domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
                (readAt S rho (domain S.E S.hc r .g1) w).st.core.F
                S.hc.η_SG r (early S.E S.hc r .g1) sender →
              DecoupledConsensusModel.Protocol.localCovers
                (readAt S rho (domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
                u.confirmed L = true →
              u.confirmed = some root' →
              Block.find?
                (readAt S rho (domain S.E S.hc r .g1) w).st.core.T root' =
                  some Head →
              Block.Preceq
                (readAt S rho (domain S.E S.hc r .g0) p).st.core.F Head := by
            intro sender u root' Head _ hcover hconf hfind
            have hFL := GradeDeliveryRun.finalized_preceq_of_mem_filtered_at_read
              S rho hLsource
            apply Block.preceq_trans hFL
            unfold DecoupledConsensusModel.Protocol.localCovers at hcover
            unfold Protocol.head_covers at hcover
            simp only [Protocol.HealingStore.gradeView, Protocol.Store.toHealing,
              hconf] at hcover
            rw [hfind] at hcover
            exact hcover
          have hbelow :=
            g1G0CrossReaderFinalizedBelow_of_finalitySafety_and_relay
              S adm hsb hgstG1 ready.2 hw hp hforward
          have hguard := g1G0CrossReaderBodyReadyGuard_of_finalizedBelow
            S adm.toNamedAdmissibleCore hr hgstG1 ready.2 hw hp hbelow
          have hLgrade0 := storeGrade_g0_of_storeGrade_g1_cross_reader
            S rho adm.toNamedAdmissibleCore r
              (g1G0TwoCutoffDelivery_of_core
                S adm.toNamedAdmissibleCore hgstG1)
              ready.2 w p hw hp L hLgrade1 hguard
          have hcompat := activeVoterAnchor_compatible_clearSource
            S adm hr ready hactionHor hp hLgrade0 hLsource hLaction hBclear
          simp only [Block.compatible, Bool.or_eq_true] at hcompat
          exact Block.preceq_trans (hcompat.resolve_left hLB)
            (by simpa only [hanchorL] using
              voterAnchorAt_preceq_voterHeadAt S rho w (s + 1))
    refine ⟨hheads, ?_⟩
    intro w hw hcommittee
    obtain ⟨X, hXhead, hXrun, hXemit⟩ := named_voter_head_emits
      S adm hw (s := s + 1) (Nat.succ_pos s) hcommittee hvoteHor
    exact ⟨X, by rw [hXhead]; exact hheads w hw, hXrun, hXemit⟩
theorem recoveryFGSelectorSeed_beforeAction_of_sourceInputs
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {r : Round} (hr : 0 < r) (ready : GradeRoundReady S rho r)
    {p : V} (hp : p ∈ rho.honest) {A : Block V} {B : NamedBlock V}
    (hselected : nodeQ2 S (actionReadAt S rho p r) r = some A)
    (hsource : actionFGSource S (actionStoreAt S rho p r) = some B.erase)
    (hBmem : B ∈ (actionStoreAt S rho p r).st.bodies)
    {H : Height}
    (hBheight : (Protocol.derive_named S.E S.cfg B).h = H + 1)
    (hactionHor : S.a r ≤ rho.horizon)
    (hK6Q2 : nodeQ2 S (actionReadAt S rho p r) r = some B.erase →
      VoterAnchorSourceQ2Inputs S rho r p B.erase)
    (hK6Clear : nodeQ2 S (actionReadAt S rho p r) r ≠ some B.erase →
      VoterAnchorSourceClearInputs S rho r p B.erase) :
    NamedHonestVotesCone S rho (S.hc.opening_slot r)
        (fun X => Block.Preceq B.erase X) ∨
      HonestHeightFilterProgressAboveThrough S rho (H + 1)
        (Protocol.vote_time S.E (S.hc.opening_slot r + 1)) ∨
      NamedHonestVotesCone S rho (S.hc.opening_slot r + 1)
        (fun X => Block.Preceq B.erase X) := by
  by_cases hlocal : nodeQ2 S (actionReadAt S rho p r) r = some B.erase
  · exact Or.inl
      (honestOpeningVotesCone_of_selectedG2_K6
        S adm hsb hr ready hp hlocal (hK6Q2 hlocal))
  · rcases actionFGSource_genuineClear_or_selectedG2_named
        S rho p r hselected hsource with hclear | hsourceQ2
    · obtain ⟨C, hgenuine, -, hwalk, -, hBC⟩ := hclear
      have hBclear : nodeClear S (actionReadAt S rho p r) r B.erase = true := by
        unfold Protocol.deepest_clear at hwalk
        have htest := (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hwalk)).2.2
        simpa only [nodeClear, nodeRead, actionStoreAt] using htest
      rcases genuineClear_nextVoteCone_or_heightProgressThrough_of_regimeFrame
          S adm hsb hr ready hp hgenuine hBC hBmem hBclear hBheight
            hactionHor (hK6Clear hlocal) (le_refl _) with hprogress | hcone
      · exact Or.inr (Or.inl hprogress)
      · exact Or.inr (Or.inr hcone.2)
    · exact (hlocal (hsourceQ2 ▸ hselected)).elim

#print axioms selectedQ2_body_at_capture
#print axioms activeVoterAnchor_storeGrade_g1

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
