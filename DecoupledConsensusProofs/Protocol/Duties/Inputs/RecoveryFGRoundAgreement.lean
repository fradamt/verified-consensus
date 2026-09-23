module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryFGSourceFrame
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.RecoveryTimeoutHistory
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGCompatibleHistory
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryHandoffCore
public import DecoupledConsensusProofs.Protocol.Schedule.WeakGoldfishCone
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordFresh
public import DecoupledConsensusProofs.Objects.FGConfirmationHistory
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.FirstProgressFGWitness
public import DecoupledConsensusProofs.Execution.RecurringArithmeticCore
public import DecoupledConsensusProofs.Protocol.ChainState.NamedNjGap
public import DecoupledConsensusProofs.Generic.SuffixHistory
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.Actions
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.ValidatorClient.Record
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeDelivery
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryG1AfterCutoffReflection
public import DecoupledConsensusProofs.Protocol.Store.RecoveryG1AfterCutoffPersistence
public import DecoupledConsensusProofs.Protocol.Grades.Grades
public import DecoupledConsensusInternal.HealingSurface
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Objects.HealingDirectedHistory
public import DecoupledConsensusProofs.Protocol.Grades.RelativeOneChain
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryGenuineClearNextVote
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.WeakConfirmationSupport
public import DecoupledConsensusProofs.Protocol.Grades.RelativeSeedK3
public import DecoupledConsensusProofs.Protocol.Grades.VoterAnchorSourceInputs

@[expose] public section


/-!
# Same-round agreement of recovery FG witnesses

Two genuine opening confirmations are compatible. A selected G2 at the
recovery height also bounds the honest opening vote heads, so it is
compatible with every genuine opening confirmation. Two selected G2 blocks
are compatible by grade delivery. These cases give exact checkpoint equality
for same-height FG sources in one round, including timeout witnesses.

This does not assert agreement between different source rounds or permanent
canonicality after the height crossing.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]


































private theorem compatible_ancestors {B C X Y : Block V}
    (hBX : Block.Preceq B X) (hCY : Block.Preceq C Y)
    (hXY : Block.compatible X Y = true) : Block.compatible B C = true := by
  rcases (show Block.Preceq X Y ∨ Block.Preceq Y X by
    simpa only [Block.compatible, Bool.or_eq_true] using hXY) with h | h
  · exact Block.compatible_of_preceq_common (Block.preceq_trans hBX h) hCY
  · exact Block.compatible_of_preceq_common hBX (Block.preceq_trans hCY h)


private theorem relative_gradeBool_zero_local
    (E : Env V) (gv : Protocol.GradeView V) (F : Block V)
    (eta : Round) (early late : Time) (B : Block V) :
    DecoupledConsensusModel.Protocol.gradeBool E gv F eta 0 early late B = false := by
  simp [DecoupledConsensusModel.Protocol.gradeBool,
    DecoupledConsensusModel.Protocol.positive, DecoupledConsensusModel.Protocol.opposing,
    DecoupledConsensusModel.Protocol.readyView, DecoupledConsensusModel.Protocol.rawView,
    DecoupledConsensusModel.Protocol.interpretedInputs, DecoupledConsensusModel.Protocol.rawInputs,
    Protocol.latest_window_zero, DecoupledConsensusModel.Protocol.Supports,
    DecoupledConsensusModel.Protocol.Opposes, DecoupledConsensusModel.Protocol.CleanFrom]

private theorem selectedQ2_round_pos_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} {r : Round} {Q : Block V}
    (hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r = some Q) :
    0 < r := by
  apply Nat.pos_of_ne_zero
  intro hzero
  subst r
  have hgrade := selectedQ2_storeGrade_at_g2Domain S adm hQ
  simp only [PhaseGrades.storeGrade, PhaseGrades.phaseGrade] at hgrade
  rw [relative_gradeBool_zero_local] at hgrade
  cases hgrade

private theorem actionBody_runBlock_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionStoreAt S rho v r).st.bodies) :
    RunBlock S rho D := by
  have hDpre : D ∈ (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hD
  obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted (S.a r)
  have hDi : D ∈ (rho.stateBefore S i v).st.bodies := by
    change D ∈ (NamedRun.stateBefore S rho i v).st.bodies
    rw [← hi]
    exact hDpre
  exact Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hDi)

private theorem actionStoreDerived_named_local
    (S : Setup V) {rho : Run V} {v : V} {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionStoreAt S rho v r).st.bodies) :
    (actionStoreAt S rho v r).st.core.σ D.erase =
      Protocol.derive_named S.E S.cfg D := by
  have hDpre : D ∈ (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hD
  have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime
    S rho (S.a r) v D hDpre
  simpa only [actionStoreAt, actionReadAt,
    NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
    NamedActionReads.confirmationReadFrom,
    NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hview

private theorem nodeQ2_of_nodeFGSource
    (S : Setup V) (rho : Run V) (v : V) (r : Round) {B : Block V}
    (hB : PhaseGrades.nodeFGSource S
      (actionReadAt S rho v r) r = some B) :
    ∃ Q, PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r = some Q := by
  cases hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r with
  | none =>
      have hQ' : Protocol.grade2_block_with
          (NamedProfile.gradeContract (actionReadAt S rho v r).cache)
          S.E S.hc (actionReadAt S rho v r).st.core.toHealing r = none := by
        simpa only [PhaseGrades.nodeQ2, PhaseGrades.nodeRead,
          Protocol.grade2_block_with] using hQ
      rw [PhaseGrades.nodeFGSource, Protocol.fg_source_with.eq_def, hQ'] at hB
      cases hB
  | some Q => exact ⟨Q, rfl⟩

theorem selectedQ2_g1Domain_data_of_frame
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {r : Round} (hr : 0 < r) (ready : GradeRoundReady S rho r)
    {p : V} (hp : p ∈ rho.honest) {Q : NamedBlock V}
    (hselected : PhaseGrades.nodeQ2 S (actionReadAt S rho p r) r =
      some Q.erase)
    (hQmem : Q ∈ (actionStoreAt S rho p r).st.bodies)
    {stop : Nat} {blocked : Height} {Tprev : Block V} {c0 : Round}
    (hframe : HeightRegimeFrame S rho blocked stop Tprev c0)
    (hQheight : (Protocol.derive_named S.E S.cfg Q).h = blocked + 1)
    (hTQ : Block.Preceq Tprev Q.erase)
    (hactionPrefix : strictEventIndex rho (S.a r) ≤ stop)
    (hfrontier : honestHMaxBeforeIndex S rho stop < blocked + 2)
    {w : V} (hw : w ∈ rho.honest) :
    Q.erase ∈ PhaseGrades.filteredTree
        (PhaseGrades.readAt S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w) ∧
      PhaseGrades.storeGrade S.E S.hc
        (PhaseGrades.readAt S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st
        r .g1 Q.erase = true := by
  let core := adm.toNamedAdmissibleCore
  have hQrun : RunBlock S rho Q :=
    actionBody_runBlock_named S adm hp hQmem
  have hdomainAction : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 ≤ S.a r := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact (Protocol.proposal_time_lt_vote_time S.E _).le.trans
      ((Protocol.vote_time_le_confirmation_time S.E _).trans (by
        rw [opening_confirmation_time_eq_action]))
  have hdomainPrefix : strictEventIndex rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) ≤ stop :=
    (strictEventIndex_mono rho hdomainAction).trans hactionPrefix
  have htargetFQ : Block.Preceq
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.F Q.erase := by
    rw [congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
      S core.toNamedScheduleWellFormed
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)) w]
    exact hframe.floor.storeF_preceq_sourceHeightBlock hw hdomainPrefix
      hQrun hQheight hTQ
  have hQsource : Q ∈
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) p).st.bodies :=
    selectedQ2_body_at_capture S adm hp hselected hQmem
  have hgstDomain : S.E.t_GST ≤
      DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2 := by
    exact ready.1.trans (NamedOutageClosure.early_le_domain S r)
  have hdeadline : max (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) S.E.t_GST +
      S.E.Δ ≤ DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 := by
    rw [max_eq_left hgstDomain]
    apply le_of_eq
    simp only [DecoupledConsensusModel.Protocol.domain, DecoupledConsensusModel.Protocol.Phase.domainOffset]
    ring
  have hg1Horizon : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 ≤ rho.horizon := by
    have hle : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 ≤
        DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0 := by
      simp only [DecoupledConsensusModel.Protocol.domain, DecoupledConsensusModel.Protocol.Phase.domainOffset]
      linarith [S.E.Δ_pos]
    exact hle.trans ready.2
  obtain ⟨hQtarget, -, -⟩ :=
    NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
      S rho core p hp w hw Q
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) hQsource hdeadline (le_refl _)
      hg1Horizon htargetFQ
  have hreadEq := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S core.toNamedScheduleWellFormed
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)) w
  have hQtargetIndex : Q ∈
      (NamedRun.stateBefore S rho
        (strictEventIndex rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)) w).st.bodies := by
    have h := hQtarget
    rw [hreadEq] at h
    exact h
  have hQrawIndex : Q.erase ∈
      (NamedRun.stateBefore S rho
        (strictEventIndex rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)) w).st.core.T := by
    have hco := (Proofs.NamedRuntime.stateBefore_invariants S rho
      (strictEventIndex rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)) w).1.1.1
    rw [hco.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hQtargetIndex
  have hQstoredHeight :
      ((NamedRun.stateBefore S rho
        (strictEventIndex rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)) w).st.core.σ
          Q.erase).h = blocked + 1 := by
    rw [Proofs.NamedStoreBridge.derivedView_stateBefore S rho
      (strictEventIndex rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)) w Q hQtargetIndex]
    exact hQheight
  have hfilteredIndex := hframe.fgRoot_preceq_and_filteredMem
    adm hfrontier hw hdomainPrefix hQrawIndex hQstoredHeight
      hTQ
  have hfiltered : Q.erase ∈ PhaseGrades.filteredTree
      (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w) := by
    change Q.erase ∈ Protocol.get_filtered_block_tree
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.toHealing.toFG
    rw [hreadEq]
    exact hfilteredIndex.2
  have hforward : ∀ sender u root H,
      u ∈ DecoupledConsensusModel.Protocol.interpretedInputs
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) p).st.core.toHealing.gradeView
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) p).st.core.F
        S.hc.η_SG r (DecoupledConsensusModel.Protocol.early S.E S.hc r .g2) sender →
      DecoupledConsensusModel.Protocol.localCovers
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) p).st.core.toHealing.gradeView
        u.confirmed Q.erase = true →
      u.confirmed = some root →
      Block.find?
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) p).st.core.T root = some H →
      Block.Preceq
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.F H := by
    intro sender u root H _ hcover hconf hfind
    exact Block.preceq_trans htargetFQ (by
      unfold DecoupledConsensusModel.Protocol.localCovers at hcover
      unfold Protocol.head_covers at hcover
      simp only [Protocol.HealingStore.gradeView, Protocol.Store.toHealing, hconf]
        at hcover
      rw [hfind] at hcover
      exact hcover)
  have hbelowReaders := crossReaderFinalizedBelow_of_finalitySafety_and_relay
    S adm hsb ready.1 ready.2 hp hw hforward
  have hguard := crossReaderBodyReadyGuard_of_finalizedBelow
    S core hr ready.1 ready.2 hp hw hbelowReaders
  have hG2 := selectedQ2_storeGrade_at_g2Domain S adm hselected
  have hdelivery := twoCutoffDelivery_of_core S core ready.1
  refine ⟨hfiltered, ?_⟩
  exact storeGrade_g1_of_storeGrade_g2_cross_reader
    S rho core r hdelivery ready.2 p w hp hw Q.erase hG2 hguard

private theorem selectedQ2_g1Domain_data_of_recoveryPrefix
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {r : Round} (hr : 0 < r) (ready : GradeRoundReady S rho r)
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
    {w : V} (hw : w ∈ rho.honest) :
    Q.erase ∈ PhaseGrades.filteredTree
        (PhaseGrades.readAt S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w) ∧
      PhaseGrades.storeGrade S.E S.hc
        (PhaseGrades.readAt S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st
        r .g1 Q.erase = true := by
  exact selectedQ2_g1Domain_data_of_frame S adm
    (slashableBound_of_admissible_belowOneThird S adm hbelow) hr ready hp
      hselected hQmem
      (heightRegimeFrame_of_recovery S adm hbelow hcap hrec hfrontier)
      hQheight (Protocol.preceq_genesis Q.erase) hactionPrefix hfrontier hw

#print axioms selectedQ2_g1Domain_data_of_frame

theorem selectedQ2_g1Domain_data_of_frameN
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {r : Round} (hr : 0 < r) (ready : GradeRoundReady S rho r)
    {p : V} (hp : p ∈ rho.honest) {Q : NamedBlock V}
    (hselected : PhaseGrades.nodeQ2 S (actionReadAt S rho p r) r =
      some Q.erase)
    (hQmem : Q ∈ (actionStoreAt S rho p r).st.bodies)
    {stop : Nat} {blocked : Height} {Tprev : NamedBlock V} {c0 : Round}
    (hframe : HeightRegimeFrameN S rho blocked stop Tprev c0)
    (hQheight : (Protocol.derive_named S.E S.cfg Q).h = blocked + 1)
    (hTQ : Block.Preceq Tprev.erase Q.erase)
    (hactionPrefix : strictEventIndex rho (S.a r) ≤ stop)
    (hfrontier : honestHMaxBeforeIndex S rho stop < blocked + 2)
    {w : V} (hw : w ∈ rho.honest) :
    Q.erase ∈ PhaseGrades.filteredTree
        (PhaseGrades.readAt S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w) ∧
      PhaseGrades.storeGrade S.E S.hc
        (PhaseGrades.readAt S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st
        r .g1 Q.erase = true := by
  let core := adm.toNamedAdmissibleCore
  have hQrun : RunBlock S rho Q :=
    actionBody_runBlock_named S adm hp hQmem
  have hdomainAction : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 ≤ S.a r := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact (Protocol.proposal_time_lt_vote_time S.E _).le.trans
      ((Protocol.vote_time_le_confirmation_time S.E _).trans (by
        rw [opening_confirmation_time_eq_action]))
  have hdomainPrefix : strictEventIndex rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) ≤ stop :=
    (strictEventIndex_mono rho hdomainAction).trans hactionPrefix
  have htargetFQ : Block.Preceq
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.F Q.erase := by
    rw [congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
      S core.toNamedScheduleWellFormed
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)) w]
    exact hframe.floor.storeF_preceq_sourceHeightBlock hw hdomainPrefix
      hQrun hQheight hTQ
  have hQsource : Q ∈
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) p).st.bodies :=
    selectedQ2_body_at_capture S adm hp hselected hQmem
  have hgstDomain : S.E.t_GST ≤
      DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2 := by
    exact ready.1.trans (NamedOutageClosure.early_le_domain S r)
  have hdeadline : max (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) S.E.t_GST +
      S.E.Δ ≤ DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 := by
    rw [max_eq_left hgstDomain]
    apply le_of_eq
    simp only [DecoupledConsensusModel.Protocol.domain, DecoupledConsensusModel.Protocol.Phase.domainOffset]
    ring
  have hg1Horizon : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 ≤ rho.horizon := by
    have hle : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 ≤
        DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0 := by
      simp only [DecoupledConsensusModel.Protocol.domain, DecoupledConsensusModel.Protocol.Phase.domainOffset]
      linarith [S.E.Δ_pos]
    exact hle.trans ready.2
  obtain ⟨hQtarget, -, -⟩ :=
    NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
      S rho core p hp w hw Q
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) hQsource hdeadline (le_refl _)
      hg1Horizon htargetFQ
  have hreadEq := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S core.toNamedScheduleWellFormed
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)) w
  have hQtargetIndex : Q ∈
      (NamedRun.stateBefore S rho
        (strictEventIndex rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)) w).st.bodies := by
    have h := hQtarget
    rw [hreadEq] at h
    exact h
  have hQrawIndex : Q.erase ∈
      (NamedRun.stateBefore S rho
        (strictEventIndex rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)) w).st.core.T := by
    have hco := (Proofs.NamedRuntime.stateBefore_invariants S rho
      (strictEventIndex rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)) w).1.1.1
    rw [hco.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hQtargetIndex
  have hQstoredHeight :
      ((NamedRun.stateBefore S rho
        (strictEventIndex rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)) w).st.core.σ
          Q.erase).h = blocked + 1 := by
    rw [Proofs.NamedStoreBridge.derivedView_stateBefore S rho
      (strictEventIndex rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)) w Q hQtargetIndex]
    exact hQheight
  have hfilteredIndex := hframe.fgRoot_preceq_and_filteredMem
    adm hfrontier hw hdomainPrefix hQrawIndex hQstoredHeight
      hTQ
  have hfiltered : Q.erase ∈ PhaseGrades.filteredTree
      (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w) := by
    change Q.erase ∈ Protocol.get_filtered_block_tree
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.toHealing.toFG
    rw [hreadEq]
    exact hfilteredIndex.2
  have hforward : ∀ sender u root H,
      u ∈ DecoupledConsensusModel.Protocol.interpretedInputs
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) p).st.core.toHealing.gradeView
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) p).st.core.F
        S.hc.η_SG r (DecoupledConsensusModel.Protocol.early S.E S.hc r .g2) sender →
      DecoupledConsensusModel.Protocol.localCovers
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) p).st.core.toHealing.gradeView
        u.confirmed Q.erase = true →
      u.confirmed = some root →
      Block.find?
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) p).st.core.T root = some H →
      Block.Preceq
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.F H := by
    intro sender u root H _ hcover hconf hfind
    exact Block.preceq_trans htargetFQ (by
      unfold DecoupledConsensusModel.Protocol.localCovers at hcover
      unfold Protocol.head_covers at hcover
      simp only [Protocol.HealingStore.gradeView, Protocol.Store.toHealing, hconf]
        at hcover
      rw [hfind] at hcover
      exact hcover)
  have hbelowReaders := crossReaderFinalizedBelow_of_finalitySafety_and_relay
    S adm hsb ready.1 ready.2 hp hw hforward
  have hguard := crossReaderBodyReadyGuard_of_finalizedBelow
    S core hr ready.1 ready.2 hp hw hbelowReaders
  have hG2 := selectedQ2_storeGrade_at_g2Domain S adm hselected
  have hdelivery := twoCutoffDelivery_of_core S core ready.1
  refine ⟨hfiltered, ?_⟩
  exact storeGrade_g1_of_storeGrade_g2_cross_reader
    S rho core r hdelivery ready.2 p w hp hw Q.erase hG2 hguard

#print axioms selectedQ2_g1Domain_data_of_frameN

private theorem selectedQ2_preceq_voteDutyHead_of_frame
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {r : Round} (ready : GradeRoundReady S rho r)
    {p : V} (hp : p ∈ rho.honest) {Q : NamedBlock V}
    (hselected : PhaseGrades.nodeQ2 S (actionReadAt S rho p r) r =
      some Q.erase)
    (hQmem : Q ∈ (actionStoreAt S rho p r).st.bodies)
    {stop : Nat} {blocked : Height} {Tprev : Block V} {c0 : Round}
    (hframe : HeightRegimeFrame S rho blocked stop Tprev c0)
    (hQheight : (Protocol.derive_named S.E S.cfg Q).h = blocked + 1)
    (hTQ : Block.Preceq Tprev Q.erase)
    (hactionPrefix : strictEventIndex rho (S.a r) ≤ stop)
    (hfrontier : honestHMaxBeforeIndex S rho stop < blocked + 2)
    {w : V} (hw : w ∈ rho.honest) :
    Block.Preceq Q.erase (voterHeadAt S rho w (S.hc.opening_slot r)) := by
  have hr := selectedQ2_round_pos_named S adm hselected
  have hdomain := selectedQ2_g1Domain_data_of_frame
    S adm hsb hr ready hp hselected hQmem hframe hQheight hTQ
      hactionPrefix hfrontier hw
  have hQvote := voterAnchorSourceQ2Inputs_of_frame
    S adm ready hp hselected hQmem hframe hQheight hTQ hactionPrefix hfrontier
  have hread : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 <
      Protocol.vote_time S.E (S.hc.opening_slot r) := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact Protocol.proposal_time_lt_vote_time S.E _
  have hta : Protocol.vote_time S.E (S.hc.opening_slot r) ≤ S.a r :=
    (Protocol.vote_time_le_confirmation_time S.E _).trans
      (by rw [opening_confirmation_time_eq_action])
  have hhor : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 ≤ rho.horizon := by
    have hle : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 ≤
        DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0 := by
      simp only [DecoupledConsensusModel.Protocol.domain, DecoupledConsensusModel.Protocol.Phase.domainOffset]
      linarith [S.E.Δ_pos]
    exact hle.trans ready.2
  have hround : S.hc.round_of (S.hc.opening_slot r) = r := by
    unfold Protocol.HealConfig.round_of Protocol.HealConfig.opening_slot
    exact Nat.mul_div_cancel r
      (Nat.lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hsource : Protocol.grade2_block_with
      (NamedProfile.gradeContract (actionReadAt S rho p r).cache)
      S.E S.hc (actionReadAt S rho p r).st.core.toHealing r = some Q.erase := by
    simpa only [PhaseGrades.nodeQ2, PhaseGrades.nodeRead,
      Internal.NamedRecoveryRead.actionDutyRead] using hselected
  have hQread : Q.erase ∈ PhaseGrades.filteredTree
      (PhaseGrades.readAt S rho
        (Protocol.vote_time S.E (S.hc.opening_slot r)) w) := by
    simpa only [PhaseGrades.filteredTree, PhaseGrades.readAt,
      Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, Protocol.NamedStore.setClock] using
      hQvote.openingTarget w hw
  have hactiveVote : Q.erase ∈ Protocol.get_filtered_block_tree
      (Internal.NamedRecoveryRead.voteDutyRead S rho w
        (S.hc.opening_slot r)).st.core.toHealing.toFG := by
    simpa only [PhaseGrades.filteredTree] using hQvote.openingTarget w hw
  exact selectedActionG2_preceq_sameRoundVoteDutyHead_of_activeAtVote
    S adm.toNamedAdmissibleCore hr hp hsource hround hw hread hta hhor
      hdomain.1 hdomain.2 hQread hactiveVote

private theorem selectedQ2_preceq_voteDutyHead_of_frameN
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {r : Round} (ready : GradeRoundReady S rho r)
    {p : V} (hp : p ∈ rho.honest) {Q : NamedBlock V}
    (hselected : PhaseGrades.nodeQ2 S (actionReadAt S rho p r) r =
      some Q.erase)
    (hQmem : Q ∈ (actionStoreAt S rho p r).st.bodies)
    {stop : Nat} {blocked : Height} {Tprev : NamedBlock V} {c0 : Round}
    (hframe : HeightRegimeFrameN S rho blocked stop Tprev c0)
    (hQheight : (Protocol.derive_named S.E S.cfg Q).h = blocked + 1)
    (hTQ : Block.Preceq Tprev.erase Q.erase)
    (hactionPrefix : strictEventIndex rho (S.a r) ≤ stop)
    (hfrontier : honestHMaxBeforeIndex S rho stop < blocked + 2)
    {w : V} (hw : w ∈ rho.honest) :
    Block.Preceq Q.erase (voterHeadAt S rho w (S.hc.opening_slot r)) := by
  have hr := selectedQ2_round_pos_named S adm hselected
  have hdomain := selectedQ2_g1Domain_data_of_frameN
    S adm hsb hr ready hp hselected hQmem hframe hQheight hTQ
      hactionPrefix hfrontier hw
  have hQvote := voterAnchorSourceQ2Inputs_of_frameN
    S adm ready hp hselected hQmem hframe hQheight hTQ hactionPrefix hfrontier
  have hread : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 <
      Protocol.vote_time S.E (S.hc.opening_slot r) := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact Protocol.proposal_time_lt_vote_time S.E _
  have hta : Protocol.vote_time S.E (S.hc.opening_slot r) ≤ S.a r :=
    (Protocol.vote_time_le_confirmation_time S.E _).trans
      (by rw [opening_confirmation_time_eq_action])
  have hhor : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 ≤ rho.horizon := by
    have hle : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 ≤
        DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0 := by
      simp only [DecoupledConsensusModel.Protocol.domain, DecoupledConsensusModel.Protocol.Phase.domainOffset]
      linarith [S.E.Δ_pos]
    exact hle.trans ready.2
  have hround : S.hc.round_of (S.hc.opening_slot r) = r := by
    unfold Protocol.HealConfig.round_of Protocol.HealConfig.opening_slot
    exact Nat.mul_div_cancel r
      (Nat.lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hsource : Protocol.grade2_block_with
      (NamedProfile.gradeContract (actionReadAt S rho p r).cache)
      S.E S.hc (actionReadAt S rho p r).st.core.toHealing r = some Q.erase := by
    simpa only [PhaseGrades.nodeQ2, PhaseGrades.nodeRead,
      Internal.NamedRecoveryRead.actionDutyRead] using hselected
  have hQread : Q.erase ∈ PhaseGrades.filteredTree
      (PhaseGrades.readAt S rho
        (Protocol.vote_time S.E (S.hc.opening_slot r)) w) := by
    simpa only [PhaseGrades.filteredTree, PhaseGrades.readAt,
      Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, Protocol.NamedStore.setClock] using
      hQvote.openingTarget w hw
  have hactiveVote : Q.erase ∈ Protocol.get_filtered_block_tree
      (Internal.NamedRecoveryRead.voteDutyRead S rho w
        (S.hc.opening_slot r)).st.core.toHealing.toFG := by
    simpa only [PhaseGrades.filteredTree] using hQvote.openingTarget w hw
  exact selectedActionG2_preceq_sameRoundVoteDutyHead_of_activeAtVote
    S adm.toNamedAdmissibleCore hr hp hsource hround hw hread hta hhor
      hdomain.1 hdomain.2 hQread hactiveVote

private theorem selectedQ2_preceq_voteDutyHead_of_recoveryPrefix
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
    {w : V} (hw : w ∈ rho.honest) :
    Block.Preceq Q.erase (voterHeadAt S rho w (S.hc.opening_slot r)) := by
  exact selectedQ2_preceq_voteDutyHead_of_frame S adm
    (slashableBound_of_admissible_belowOneThird S adm hbelow) ready hp
      hselected hQmem
      (heightRegimeFrame_of_recovery S adm hbelow hcap hrec hfrontier)
      hQheight (Protocol.preceq_genesis Q.erase) hactionPrefix hfrontier hw

private theorem nodeQ2_of_actionFGSource_local
    (S : Setup V) (rho : Run V) (v : V) (r : Round) {B : Block V}
    (hB : actionFGSource S (actionStoreAt S rho v r) = some B) :
    ∃ Q, PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r = some Q := by
  have hround : S.hc.round_of
      (actionReadAt S rho v r).st.core.toHealing.s = r := by
    simpa only [Protocol.Store.toHealing] using actionStoreAt_round S rho v r
  have hsource : Protocol.fg_source_with
      (NamedProfile.gradeContract (actionReadAt S rho v r).cache) S.E S.hc
      (actionReadAt S rho v r).st.core.toHealing r
      (Protocol.grade2_block_with
        (NamedProfile.gradeContract (actionReadAt S rho v r).cache) S.E S.hc
        (actionReadAt S rho v r).st.core.toHealing r) = some B := by
    simpa only [actionFGSource, actionStoreAt, hround] using hB
  cases hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r with
  | none =>
      have hQ' : Protocol.grade2_block_with
          (NamedProfile.gradeContract (actionReadAt S rho v r).cache) S.E S.hc
          (actionReadAt S rho v r).st.core.toHealing r = none := by
        simpa only [PhaseGrades.nodeQ2, PhaseGrades.nodeRead,
          Protocol.grade2_block_with] using hQ
      rw [hQ'] at hsource
      simp only [Protocol.fg_source_with.eq_def] at hsource
      cases hsource
  | some Q => exact ⟨Q, rfl⟩

private theorem nodeFGSource_of_actionFGSource_local
    (S : Setup V) (rho : Run V) (v : V) (r : Round) {B : Block V}
    (hsource : actionFGSource S (actionStoreAt S rho v r) = some B) :
    PhaseGrades.nodeFGSource S (actionReadAt S rho v r) r = some B := by
  unfold actionFGSource at hsource
  dsimp only at hsource
  have hround : S.hc.round_of
      (actionStoreAt S rho v r).st.core.toHealing.s = r := by
    simpa only [Protocol.Store.toHealing] using actionStoreAt_round S rho v r
  rw [hround] at hsource
  simpa only [PhaseGrades.nodeFGSource, PhaseGrades.nodeRead,
    actionStoreAt] using hsource

private theorem selectedQ2_g0_grade_local
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho) {r : Round} (hr : 0 < r)
    (ready : GradeRoundReady S rho r)
    {p w : V} (hp : p ∈ rho.honest) (hw : w ∈ rho.honest)
    {Q : Block V}
    (hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho p r) r = some Q)
    (hQg1 : Q ∈ PhaseGrades.filteredTree
      (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w))
    (hQg0 : Q ∈ PhaseGrades.filteredTree
      (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) w)) :
    PhaseGrades.storeGrade S.E S.hc
      (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) w).st r .g0 Q = true := by
  have hFg1Q := NamedOutageClosure.q10_filtered_F hQg1
  have hbelow := crossReaderFinalizedBelow_of_finalitySafety_and_relay
    S adm hsb ready.1 ready.2 hp hw (by
      intro sender u root H _ hcover hconf hfind
      exact Block.preceq_trans hFg1Q (by
        unfold DecoupledConsensusModel.Protocol.localCovers at hcover
        unfold Protocol.head_covers at hcover
        simp only [Protocol.HealingStore.gradeView, Protocol.Store.toHealing, hconf]
          at hcover
        have hfind' : Block.find?
            (PhaseGrades.readAt S rho
              (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) p).st.core.T root =
            some H := by
          simpa only [Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hfind
        rw [hfind'] at hcover
        exact hcover))
  have hguard := crossReaderBodyReadyGuard_of_finalizedBelow
    S adm.toNamedAdmissibleCore hr ready.1 ready.2 hp hw hbelow
  have hG2 := selectedQ2_storeGrade_at_g2Domain S adm hQ
  have hG1 := storeGrade_g1_of_storeGrade_g2_cross_reader
    S rho adm.toNamedAdmissibleCore r
      (twoCutoffDelivery_of_core S adm.toNamedAdmissibleCore ready.1)
      ready.2 p w hp hw Q hG2 hguard
  have hgstG1 : S.E.t_GST ≤
      DecoupledConsensusModel.Protocol.early S.E S.hc r .g1 :=
    ready.1.trans (GradeCutoffMono.early_g2_le_early_g1 S.E S.hc r)
  have hFg0Q := NamedOutageClosure.q10_filtered_F hQg0
  have hbelow0 :=
    g1G0CrossReaderFinalizedBelow_of_finalitySafety_and_relay
      S adm hsb hgstG1 ready.2 hw hw (by
        intro sender u root H _ hcover hconf hfind
        exact Block.preceq_trans hFg0Q (by
          unfold DecoupledConsensusModel.Protocol.localCovers at hcover
          unfold Protocol.head_covers at hcover
          simp only [Protocol.HealingStore.gradeView, Protocol.Store.toHealing, hconf]
            at hcover
          have hfind' : Block.find?
              (PhaseGrades.readAt S rho
                (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.T root =
              some H := by
            simpa only [Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hfind
          rw [hfind'] at hcover
          exact hcover))
  have hguard0 := g1G0CrossReaderBodyReadyGuard_of_finalizedBelow
    S adm.toNamedAdmissibleCore hr hgstG1 ready.2 hw hw hbelow0
  have hG0 := storeGrade_g0_of_storeGrade_g1_cross_reader
    S rho adm.toNamedAdmissibleCore r
      (g1G0TwoCutoffDelivery_of_core S adm.toNamedAdmissibleCore hgstG1)
      ready.2 w w hw hw Q hG1 hguard0
  simpa only [PhaseGrades.storeGrade, PhaseGrades.phaseGrade] using hG0

private theorem graded_oneChain_storeGrade_local
    (E : Env V) (hc : Protocol.HealConfig) (n : NamedNodeState V)
    (r : Round) {B C : Block V}
    (hB : PhaseGrades.storeGrade E hc n.st r .g0 B = true)
    (hC : PhaseGrades.storeGrade E hc n.st r .g0 C = true) :
    Block.compatible B C = true := by
  exact Proofs.HealingLemmas.phaseGrade_g0_compatible E hc
    n.st.core.toHealing.gradeView n.st.core.F r B C hB hC

/-- A selected named Q2 at the recovery height is compatible with every honest
genuine opening confirmation. The recovery prefix supplies the relative G1
and vote-read data needed by the prepared vote-head theorem. -/
theorem selectedG2_compatible_genuineOpening_of_recoveryPrefix
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {r : Round} (ready : GradeRoundReady S rho r)
    {p v : V} (hp : p ∈ rho.honest) (hv : v ∈ rho.honest)
    {Q : NamedBlock V} {C : Block V}
    (hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho p r) r = some Q.erase)
    (hQmem : Q ∈ (actionStoreAt S rho p r).st.bodies)
    (hgenuine : GenuineConfirmationWith
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v
          (S.hc.opening_slot r)).cache)
      S.E S.hc (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r))
        (S.hc.opening_slot r) C)
    {stop : Nat} {hF0 blocked : Height}
    (hcap : HonestPrefixFinalityCap S rho stop hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (hQheight : (Protocol.derive_named S.E S.cfg Q).h = blocked + 1)
    (hactionPrefix : strictEventIndex rho (S.a r) ≤ stop)
    (hfrontier : honestHMaxBeforeIndex S rho stop < blocked + 2)
    (hhor : S.a r ≤ rho.horizon) :
    Block.compatible Q.erase C = true := by
  have hr := selectedQ2_round_pos_named S adm hQ
  have hopenPos : 0 < S.hc.opening_slot r := Nat.mul_pos hr
    (Nat.lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hpost : S.E.t_GST ≤ Protocol.vote_time S.E (S.hc.opening_slot r) := by
    rw [← Protocol.Γ_1_eq_vote_time]
    exact ready.1.trans
      ((early_g2_lt_Γ_0 S r).le.trans
        (le_of_lt (Proofs.HealingLemmas.Γ_0_lt_Γ_1 S.hc S.E.Δ_pos r)))
  have hconfHor : Protocol.confirmation_time S.E (S.hc.opening_slot r) ≤ rho.horizon := by
    rwa [opening_confirmation_time_eq_action]
  apply DecoupledConsensusModel.Proofs.HealingSurface.WeakGoldfish.genuineConfirmation_compatible_of_priorProtectedHeads
    S adm.toNamedAdmissibleCore hcom hv hopenPos hpost hconfHor hgenuine
  intro w hw hcommittee
  exact selectedQ2_preceq_voteDutyHead_of_recoveryPrefix
    S adm hbelow ready hp hQ hQmem hcap hrec hQheight hactionPrefix
      hfrontier hw

/-- A selected named Q2 at the source height is compatible with every honest
genuine opening confirmation of its round, from the height-regime frame. -/
theorem selectedG2_compatible_genuineOpening_of_frame
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {r : Round} (ready : GradeRoundReady S rho r)
    {p v : V} (hp : p ∈ rho.honest) (hv : v ∈ rho.honest)
    {Q : NamedBlock V} {C : Block V}
    (hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho p r) r = some Q.erase)
    (hQmem : Q ∈ (actionStoreAt S rho p r).st.bodies)
    (hgenuine : GenuineConfirmationWith
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v
          (S.hc.opening_slot r)).cache)
      S.E S.hc (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r))
        (S.hc.opening_slot r) C)
    {stop : Nat} {blocked : Height} {Tprev : Block V} {c0 : Round}
    (hframe : HeightRegimeFrame S rho blocked stop Tprev c0)
    (hQheight : (Protocol.derive_named S.E S.cfg Q).h = blocked + 1)
    (hTQ : Block.Preceq Tprev Q.erase)
    (hactionPrefix : strictEventIndex rho (S.a r) ≤ stop)
    (hfrontier : honestHMaxBeforeIndex S rho stop < blocked + 2)
    (hhor : S.a r ≤ rho.horizon) :
    Block.compatible Q.erase C = true := by
  have hr := selectedQ2_round_pos_named S adm hQ
  have hopenPos : 0 < S.hc.opening_slot r := Nat.mul_pos hr
    (Nat.lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hpost : S.E.t_GST ≤ Protocol.vote_time S.E (S.hc.opening_slot r) := by
    rw [← Protocol.Γ_1_eq_vote_time]
    exact ready.1.trans
      ((early_g2_lt_Γ_0 S r).le.trans
        (le_of_lt (Proofs.HealingLemmas.Γ_0_lt_Γ_1 S.hc S.E.Δ_pos r)))
  have hconfHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r) ≤ rho.horizon := by
    rwa [opening_confirmation_time_eq_action]
  apply DecoupledConsensusModel.Proofs.HealingSurface.WeakGoldfish.genuineConfirmation_compatible_of_priorProtectedHeads
    S adm.toNamedAdmissibleCore hcom hv hopenPos hpost hconfHor hgenuine
  intro w hw _
  exact selectedQ2_preceq_voteDutyHead_of_frame S adm
    (slashableBound_of_admissible_belowOneThird S adm hbelow) ready hp
      hQ hQmem hframe hQheight hTQ hactionPrefix hfrontier hw

#print axioms selectedG2_compatible_genuineOpening_of_frame

/-- A selected named Q2 is compatible with every honest genuine opening
confirmation, using a named-predecessor regime frame. -/
theorem selectedG2_compatible_genuineOpening_of_frameN
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {r : Round} (ready : GradeRoundReady S rho r)
    {p v : V} (hp : p ∈ rho.honest) (hv : v ∈ rho.honest)
    {Q : NamedBlock V} {C : Block V}
    (hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho p r) r = some Q.erase)
    (hQmem : Q ∈ (actionStoreAt S rho p r).st.bodies)
    (hgenuine : GenuineConfirmationWith
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v
          (S.hc.opening_slot r)).cache)
      S.E S.hc (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r))
        (S.hc.opening_slot r) C)
    {stop : Nat} {blocked : Height} {Tprev : NamedBlock V} {c0 : Round}
    (hframe : HeightRegimeFrameN S rho blocked stop Tprev c0)
    (hQheight : (Protocol.derive_named S.E S.cfg Q).h = blocked + 1)
    (hTQ : Block.Preceq Tprev.erase Q.erase)
    (hactionPrefix : strictEventIndex rho (S.a r) ≤ stop)
    (hfrontier : honestHMaxBeforeIndex S rho stop < blocked + 2)
    (hhor : S.a r ≤ rho.horizon) :
    Block.compatible Q.erase C = true := by
  have hr := selectedQ2_round_pos_named S adm hQ
  have hopenPos : 0 < S.hc.opening_slot r := Nat.mul_pos hr
    (Nat.lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hpost : S.E.t_GST ≤ Protocol.vote_time S.E (S.hc.opening_slot r) := by
    rw [← Protocol.Γ_1_eq_vote_time]
    exact ready.1.trans
      ((early_g2_lt_Γ_0 S r).le.trans
        (le_of_lt (Proofs.HealingLemmas.Γ_0_lt_Γ_1 S.hc S.E.Δ_pos r)))
  have hconfHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r) ≤ rho.horizon := by
    rwa [opening_confirmation_time_eq_action]
  apply DecoupledConsensusModel.Proofs.HealingSurface.WeakGoldfish.genuineConfirmation_compatible_of_priorProtectedHeads
    S adm.toNamedAdmissibleCore hcom hv hopenPos hpost hconfHor hgenuine
  intro w hw _
  exact selectedQ2_preceq_voteDutyHead_of_frameN S adm
    (slashableBound_of_admissible_belowOneThird S adm hbelow) ready hp
      hQ hQmem hframe hQheight hTQ hactionPrefix hfrontier hw

#print axioms selectedG2_compatible_genuineOpening_of_frameN

/-- Same-height FG sources at honest actions in one recovery round are
compatible. The finite prefix derives the activity needed in each G2 case;
the genuine/genuine case uses same-slot confirmation safety. -/
theorem actionFGSources_compatible_of_recoveryPrefix
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {r : Round} (ready : GradeRoundReady S rho r)
    {p v : V} (hp : p ∈ rho.honest) (hv : v ∈ rho.honest)
    {B C : NamedBlock V}
    (hB : actionFGSource S (actionStoreAt S rho p r) = some B.erase)
    (hBmem : B ∈ (actionStoreAt S rho p r).st.bodies)
    (hC : actionFGSource S (actionStoreAt S rho v r) = some C.erase)
    (hCmem : C ∈ (actionStoreAt S rho v r).st.bodies)
    {stop : Nat} {hF0 blocked : Height}
    (hcap : HonestPrefixFinalityCap S rho stop hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (hBheight : (Protocol.derive_named S.E S.cfg B).h = blocked + 1)
    (hCheight : (Protocol.derive_named S.E S.cfg C).h = blocked + 1)
    (hactionPrefix : strictEventIndex rho (S.a r) ≤ stop)
    (hfrontier : honestHMaxBeforeIndex S rho stop < blocked + 2)
    (hhor : S.a r ≤ rho.horizon) :
    Block.compatible B.erase C.erase = true := by
  obtain ⟨Qp, hQp⟩ := nodeQ2_of_actionFGSource_local
    S rho p r hB
  obtain ⟨Qw, hQw⟩ := nodeQ2_of_actionFGSource_local
    S rho v r hC
  rcases actionFGSource_genuineClear_or_selectedG2_named
      S rho p r hQp hB with hBgenuine | hBselected
  · rcases actionFGSource_genuineClear_or_selectedG2_named
        S rho v r hQw hC with hCgenuine | hCselected
    · obtain ⟨X, hX, -, -, -, hBX⟩ := hBgenuine
      obtain ⟨Y, hY, -, -, -, hCY⟩ := hCgenuine
      have hpost : S.E.t_GST ≤ Protocol.proposal_time S.E
          (S.hc.opening_slot r) := by
        rw [← Protocol.Γ_0_eq_proposal_time]
        exact ready.1.trans (NamedOutageClosure.early_le_opening S r)
      have hconfHor : Protocol.confirmation_time S.E
          (S.hc.opening_slot r) ≤ rho.horizon := by
        rwa [opening_confirmation_time_eq_action]
      have hXY := Protocol.sameSlot_genuine_compatible_after_gst
        S adm hp hv hpost hconfHor hX hY
      exact compatible_ancestors hBX hCY hXY
    · obtain ⟨X, hX, -, -, -, hBX⟩ := hBgenuine
      have hCnode : PhaseGrades.nodeQ2
          S (actionReadAt S rho v r) r = some C.erase := by
        simpa only [hCselected] using hQw
      have hX' : GenuineConfirmationWith
          (NamedProfile.gradeContract
          (Internal.NamedRecoveryRead.confirmationInputRead S rho p
              (S.hc.opening_slot r)).cache)
          S.E S.hc (Proofs.Optimistic.confStore S rho p
            (S.hc.opening_slot r)) (S.hc.opening_slot r) X := by
        simpa only [Internal.NamedRecoveryRead.confirmationInputRead,
          opening_confirmation_time_eq_action] using hX
      have hcompat := selectedG2_compatible_genuineOpening_of_recoveryPrefix
        S adm hcom hbelow ready hv hp (Q := C) (C := X) hCnode hCmem hX'
          hcap hrec hCheight hactionPrefix hfrontier hhor
      exact compatible_ancestors hBX (Block.preceq_self C.erase)
        (by simpa only [Block.compatible, Bool.or_comm] using hcompat)
  · have hBnode : PhaseGrades.nodeQ2
        S (actionReadAt S rho p r) r = some B.erase := by
      simpa only [hBselected] using hQp
    rcases actionFGSource_genuineClear_or_selectedG2_named
        S rho v r hQw hC with hCgenuine | hCselected
    · obtain ⟨Y, hY, -, -, -, hCY⟩ := hCgenuine
      have hY' : GenuineConfirmationWith
          (NamedProfile.gradeContract
          (Internal.NamedRecoveryRead.confirmationInputRead S rho v
              (S.hc.opening_slot r)).cache)
          S.E S.hc (Proofs.Optimistic.confStore S rho v
            (S.hc.opening_slot r)) (S.hc.opening_slot r) Y := by
        simpa only [Internal.NamedRecoveryRead.confirmationInputRead,
          opening_confirmation_time_eq_action] using hY
      have hcompat := selectedG2_compatible_genuineOpening_of_recoveryPrefix
        S adm hcom hbelow ready hp hv (Q := B) (C := Y) hBnode hBmem hY'
          hcap hrec hBheight hactionPrefix hfrontier hhor
      exact compatible_ancestors (Block.preceq_self B.erase) hCY hcompat
    · have hCnode : PhaseGrades.nodeQ2
          S (actionReadAt S rho v r) r = some C.erase := by
        simpa only [hCselected] using hQw
      have hBheight' := selectedQ2_g1Domain_data_of_recoveryPrefix
        S adm hbelow (selectedQ2_round_pos_named S adm hQp)
          ready hp hBnode hBmem hcap hrec hBheight hactionPrefix
            hfrontier (w := v) hv
      have hCheight' := selectedQ2_g1Domain_data_of_recoveryPrefix
        S adm hbelow (selectedQ2_round_pos_named S adm hQw)
          ready hv hCnode hCmem hcap hrec hCheight hactionPrefix
            hfrontier (w := v) hv
      have hBfiltered := selectedQ2_filtered_at_action_and_openingVote_of_prefixCap
        S adm hbelow ready hp hBnode hBmem hcap hrec hBheight
          hactionPrefix hfrontier (reader := v)
      have hCfiltered := selectedQ2_filtered_at_action_and_openingVote_of_prefixCap
        S adm hbelow ready hv hCnode hCmem hcap hrec hCheight
          hactionPrefix hfrontier (reader := v)
      have hBQg0' : B.erase ∈ PhaseGrades.filteredTree
          (PhaseGrades.readAt S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) v) := by
        rw [domain_g0_eq_Γ_1, Protocol.Γ_1_eq_vote_time]
        simpa only [PhaseGrades.filteredTree, PhaseGrades.readAt,
          Internal.NamedRecoveryRead.voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          NamedActionReads.preparedCache, Protocol.NamedStore.setClock] using
          (hBfiltered hv).2
      have hBQg0 : Qp ∈ PhaseGrades.filteredTree
          (PhaseGrades.readAt S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) v) :=
        hBselected ▸ hBQg0'
      have hCQg0' : C.erase ∈ PhaseGrades.filteredTree
          (PhaseGrades.readAt S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) v) := by
        rw [domain_g0_eq_Γ_1, Protocol.Γ_1_eq_vote_time]
        simpa only [PhaseGrades.filteredTree, PhaseGrades.readAt,
          Internal.NamedRecoveryRead.voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          NamedActionReads.preparedCache, Protocol.NamedStore.setClock] using
          (hCfiltered hv).2
      have hCQg0 : Qw ∈ PhaseGrades.filteredTree
          (PhaseGrades.readAt S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) v) :=
        hCselected ▸ hCQg0'
      have hBQg1 : Qp ∈ PhaseGrades.filteredTree
          (PhaseGrades.readAt S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) v) :=
        hBselected ▸ hBheight'.1
      have hCQg1 : Qw ∈ PhaseGrades.filteredTree
          (PhaseGrades.readAt S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) v) :=
        hCselected ▸ hCheight'.1
      have hsb : SlashableBound S rho :=
        slashableBound_of_admissible_belowOneThird S adm hbelow
      have hBgrade := selectedQ2_g0_grade_local S adm hsb
        (selectedQ2_round_pos_named S adm hQp) ready hp hv hQp
          hBQg1 hBQg0
      have hCgrade := selectedQ2_g0_grade_local S adm hsb
        (selectedQ2_round_pos_named S adm hQw) ready hv hv hQw
          hCQg1 hCQg0
      let n := PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) v
      have hcompat := graded_oneChain_storeGrade_local S.E S.hc n r
        hBgrade hCgrade
      simpa only [hBselected, hCselected] using hcompat

/-- Same-height named FG sources at honest actions in one frame are
compatible. The frame supplies pointwise Q2 retention, so no global
same-round retention record is required. -/
theorem actionFGSources_compatible_of_frame
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {r : Round} (ready : GradeRoundReady S rho r)
    {p v : V} (hp : p ∈ rho.honest) (hv : v ∈ rho.honest)
    {Bn Cn : NamedBlock V}
    (hB : PhaseGrades.nodeFGSource S
      (actionReadAt S rho p r) r = some Bn.erase)
    (hC : PhaseGrades.nodeFGSource S
      (actionReadAt S rho v r) r = some Cn.erase)
    (hBmem : Bn ∈ (actionStoreAt S rho p r).st.bodies)
    (hCmem : Cn ∈ (actionStoreAt S rho v r).st.bodies)
    {stop : Nat} {blocked : Height}
    {Tprev : Block V} {c0 : Round}
    (hframe : HeightRegimeFrame S rho blocked stop Tprev c0)
    (hBheight : (Protocol.derive_named S.E S.cfg Bn).h = blocked + 1)
    (hCheight : (Protocol.derive_named S.E S.cfg Cn).h = blocked + 1)
    (hTB : Block.Preceq Tprev Bn.erase)
    (hTC : Block.Preceq Tprev Cn.erase)
    (hactionPrefix : strictEventIndex rho (S.a r) ≤ stop)
    (hfrontier : honestHMaxBeforeIndex S rho stop < blocked + 2)
    (hhor : S.a r ≤ rho.horizon) :
    Block.compatible Bn.erase Cn.erase = true := by
  have hBsource : actionFGSource S
      (actionStoreAt S rho p r) = some Bn.erase := by
    unfold actionFGSource
    dsimp only
    have hround : S.hc.round_of
        (actionStoreAt S rho p r).st.core.toHealing.s = r := by
      simpa only [Protocol.Store.toHealing] using actionStoreAt_round S rho p r
    rw [hround]
    simpa only [PhaseGrades.nodeFGSource, PhaseGrades.nodeRead,
      actionStoreAt] using hB
  have hCsource : actionFGSource S
      (actionStoreAt S rho v r) = some Cn.erase := by
    unfold actionFGSource
    dsimp only
    have hround : S.hc.round_of
        (actionStoreAt S rho v r).st.core.toHealing.s = r := by
      simpa only [Protocol.Store.toHealing] using actionStoreAt_round S rho v r
    rw [hround]
    simpa only [PhaseGrades.nodeFGSource, PhaseGrades.nodeRead,
      actionStoreAt] using hC
  obtain ⟨Qp, hQp⟩ := nodeQ2_of_nodeFGSource S rho p r hB
  obtain ⟨Qv, hQv⟩ := nodeQ2_of_nodeFGSource S rho v r hC
  rcases actionFGSource_genuineClear_or_selectedG2_named
      S rho p r hQp hBsource with hBgenuine | hBselected
  · rcases actionFGSource_genuineClear_or_selectedG2_named
        S rho v r hQv hCsource with hCgenuine | hCselected
    · obtain ⟨X, hX, -, -, -, hBX⟩ := hBgenuine
      obtain ⟨Y, hY, -, -, -, hCY⟩ := hCgenuine
      have hpost : S.E.t_GST ≤ Protocol.proposal_time S.E
          (S.hc.opening_slot r) := by
        rw [← Protocol.Γ_0_eq_proposal_time]
        exact ready.1.trans (NamedOutageClosure.early_le_opening S r)
      have hconfHor : Protocol.confirmation_time S.E
          (S.hc.opening_slot r) ≤ rho.horizon := by
        rwa [opening_confirmation_time_eq_action]
      have hXY := Protocol.sameSlot_genuine_compatible_after_gst
        S adm hp hv hpost hconfHor hX hY
      exact compatible_ancestors hBX hCY hXY
    · obtain ⟨X, hX, -, -, -, hBX⟩ := hBgenuine
      have hCnode : PhaseGrades.nodeQ2
          S (actionReadAt S rho v r) r = some Cn.erase := by
        simpa only [hCselected] using hQv
      have hX' : GenuineConfirmationWith
          (NamedProfile.gradeContract
            (Internal.NamedRecoveryRead.confirmationInputRead S rho p
              (S.hc.opening_slot r)).cache)
          S.E S.hc (Proofs.Optimistic.confStore S rho p
            (S.hc.opening_slot r)) (S.hc.opening_slot r) X := by
        simpa only [Internal.NamedRecoveryRead.confirmationInputRead,
          opening_confirmation_time_eq_action] using hX
      have hcompat := selectedG2_compatible_genuineOpening_of_frame
        S adm hcom hbelow ready hv hp hCnode hCmem hX' hframe hCheight
          hTC hactionPrefix hfrontier hhor
      exact compatible_ancestors hBX (Block.preceq_self Cn.erase)
        (by simpa only [Block.compatible, Bool.or_comm] using hcompat)
  · have hBnode : PhaseGrades.nodeQ2
        S (actionReadAt S rho p r) r = some Bn.erase := by
      simpa only [hBselected] using hQp
    rcases actionFGSource_genuineClear_or_selectedG2_named
        S rho v r hQv hCsource with hCgenuine | hCselected
    · obtain ⟨Y, hY, -, -, -, hCY⟩ := hCgenuine
      have hY' : GenuineConfirmationWith
          (NamedProfile.gradeContract
            (Internal.NamedRecoveryRead.confirmationInputRead S rho v
              (S.hc.opening_slot r)).cache)
          S.E S.hc (Proofs.Optimistic.confStore S rho v
            (S.hc.opening_slot r)) (S.hc.opening_slot r) Y := by
        simpa only [Internal.NamedRecoveryRead.confirmationInputRead,
          opening_confirmation_time_eq_action] using hY
      have hcompat := selectedG2_compatible_genuineOpening_of_frame
        S adm hcom hbelow ready hp hv hBnode hBmem hY' hframe hBheight
          hTB hactionPrefix hfrontier hhor
      exact compatible_ancestors (Block.preceq_self Bn.erase) hCY hcompat
    · have hCnode : PhaseGrades.nodeQ2
          S (actionReadAt S rho v r) r = some Cn.erase := by
        simpa only [hCselected] using hQv
      have hsb : SlashableBound S rho :=
        slashableBound_of_admissible_belowOneThird S adm hbelow
      have hBdata := selectedQ2_g1Domain_data_of_frame S adm hsb
        (selectedQ2_round_pos_named S adm hBnode) ready hp hBnode hBmem
          hframe hBheight hTB hactionPrefix hfrontier hv
      have hCdata := selectedQ2_g1Domain_data_of_frame S adm hsb
        (selectedQ2_round_pos_named S adm hCnode) ready hv hCnode hCmem
          hframe hCheight hTC hactionPrefix hfrontier hv
      exact relativeSeed_sameReaderG1_compatible S rho r v hBdata.2 hCdata.2

#print axioms actionFGSources_compatible_of_frame

/-- Same-height named FG sources are compatible with a named-predecessor
regime frame. -/
theorem actionFGSources_compatible_of_frameN
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {r : Round} (ready : GradeRoundReady S rho r)
    {p v : V} (hp : p ∈ rho.honest) (hv : v ∈ rho.honest)
    {Bn Cn : NamedBlock V}
    (hB : PhaseGrades.nodeFGSource S
      (actionReadAt S rho p r) r = some Bn.erase)
    (hC : PhaseGrades.nodeFGSource S
      (actionReadAt S rho v r) r = some Cn.erase)
    (hBmem : Bn ∈ (actionStoreAt S rho p r).st.bodies)
    (hCmem : Cn ∈ (actionStoreAt S rho v r).st.bodies)
    {stop : Nat} {blocked : Height}
    {Tprev : NamedBlock V} {c0 : Round}
    (hframe : HeightRegimeFrameN S rho blocked stop Tprev c0)
    (hBheight : (Protocol.derive_named S.E S.cfg Bn).h = blocked + 1)
    (hCheight : (Protocol.derive_named S.E S.cfg Cn).h = blocked + 1)
    (hTB : Block.Preceq Tprev.erase Bn.erase)
    (hTC : Block.Preceq Tprev.erase Cn.erase)
    (hactionPrefix : strictEventIndex rho (S.a r) ≤ stop)
    (hfrontier : honestHMaxBeforeIndex S rho stop < blocked + 2)
    (hhor : S.a r ≤ rho.horizon) :
    Block.compatible Bn.erase Cn.erase = true := by
  have hBsource : actionFGSource S
      (actionStoreAt S rho p r) = some Bn.erase := by
    unfold actionFGSource
    dsimp only
    have hround : S.hc.round_of
        (actionStoreAt S rho p r).st.core.toHealing.s = r := by
      simpa only [Protocol.Store.toHealing] using actionStoreAt_round S rho p r
    rw [hround]
    simpa only [PhaseGrades.nodeFGSource, PhaseGrades.nodeRead,
      actionStoreAt] using hB
  have hCsource : actionFGSource S
      (actionStoreAt S rho v r) = some Cn.erase := by
    unfold actionFGSource
    dsimp only
    have hround : S.hc.round_of
        (actionStoreAt S rho v r).st.core.toHealing.s = r := by
      simpa only [Protocol.Store.toHealing] using actionStoreAt_round S rho v r
    rw [hround]
    simpa only [PhaseGrades.nodeFGSource, PhaseGrades.nodeRead,
      actionStoreAt] using hC
  obtain ⟨Qp, hQp⟩ := nodeQ2_of_nodeFGSource S rho p r hB
  obtain ⟨Qv, hQv⟩ := nodeQ2_of_nodeFGSource S rho v r hC
  rcases actionFGSource_genuineClear_or_selectedG2_named
      S rho p r hQp hBsource with hBgenuine | hBselected
  · rcases actionFGSource_genuineClear_or_selectedG2_named
        S rho v r hQv hCsource with hCgenuine | hCselected
    · obtain ⟨X, hX, -, -, -, hBX⟩ := hBgenuine
      obtain ⟨Y, hY, -, -, -, hCY⟩ := hCgenuine
      have hpost : S.E.t_GST ≤ Protocol.proposal_time S.E
          (S.hc.opening_slot r) := by
        rw [← Protocol.Γ_0_eq_proposal_time]
        exact ready.1.trans (NamedOutageClosure.early_le_opening S r)
      have hconfHor : Protocol.confirmation_time S.E
          (S.hc.opening_slot r) ≤ rho.horizon := by
        rwa [opening_confirmation_time_eq_action]
      have hXY := Protocol.sameSlot_genuine_compatible_after_gst
        S adm hp hv hpost hconfHor hX hY
      exact compatible_ancestors hBX hCY hXY
    · obtain ⟨X, hX, -, -, -, hBX⟩ := hBgenuine
      have hCnode : PhaseGrades.nodeQ2
          S (actionReadAt S rho v r) r = some Cn.erase := by
        simpa only [hCselected] using hQv
      have hX' : GenuineConfirmationWith
          (NamedProfile.gradeContract
            (Internal.NamedRecoveryRead.confirmationInputRead S rho p
              (S.hc.opening_slot r)).cache)
          S.E S.hc (Proofs.Optimistic.confStore S rho p
            (S.hc.opening_slot r)) (S.hc.opening_slot r) X := by
        simpa only [Internal.NamedRecoveryRead.confirmationInputRead,
          opening_confirmation_time_eq_action] using hX
      have hcompat := selectedG2_compatible_genuineOpening_of_frameN
        S adm hcom hbelow ready hv hp hCnode hCmem hX' hframe hCheight
          hTC hactionPrefix hfrontier hhor
      exact compatible_ancestors hBX (Block.preceq_self Cn.erase)
        (by simpa only [Block.compatible, Bool.or_comm] using hcompat)
  · have hBnode : PhaseGrades.nodeQ2
        S (actionReadAt S rho p r) r = some Bn.erase := by
      simpa only [hBselected] using hQp
    rcases actionFGSource_genuineClear_or_selectedG2_named
        S rho v r hQv hCsource with hCgenuine | hCselected
    · obtain ⟨Y, hY, -, -, -, hCY⟩ := hCgenuine
      have hY' : GenuineConfirmationWith
          (NamedProfile.gradeContract
            (Internal.NamedRecoveryRead.confirmationInputRead S rho v
              (S.hc.opening_slot r)).cache)
          S.E S.hc (Proofs.Optimistic.confStore S rho v
            (S.hc.opening_slot r)) (S.hc.opening_slot r) Y := by
        simpa only [Internal.NamedRecoveryRead.confirmationInputRead,
          opening_confirmation_time_eq_action] using hY
      have hcompat := selectedG2_compatible_genuineOpening_of_frameN
        S adm hcom hbelow ready hp hv hBnode hBmem hY' hframe hBheight
          hTB hactionPrefix hfrontier hhor
      exact compatible_ancestors (Block.preceq_self Bn.erase) hCY hcompat
    · have hCnode : PhaseGrades.nodeQ2
          S (actionReadAt S rho v r) r = some Cn.erase := by
        simpa only [hCselected] using hQv
      have hsb : SlashableBound S rho :=
        slashableBound_of_admissible_belowOneThird S adm hbelow
      have hBdata := selectedQ2_g1Domain_data_of_frameN S adm hsb
        (selectedQ2_round_pos_named S adm hBnode) ready hp hBnode hBmem
          hframe hBheight hTB hactionPrefix hfrontier hv
      have hCdata := selectedQ2_g1Domain_data_of_frameN S adm hsb
        (selectedQ2_round_pos_named S adm hCnode) ready hv hCnode hCmem
          hframe hCheight hTC hactionPrefix hfrontier hv
      exact relativeSeed_sameReaderG1_compatible S rho r v hBdata.2 hCdata.2

/-- Exact same-round checkpoints agree for the actual first-crossing seeds.
The source blocks need not be equal. The result also covers two timeouts or
a target and a timeout, since it uses the retained confirmation witnesses. -/
theorem PrefixFGSelectorConeAt.checkpoint_eq_of_sameRound_beforeFirst
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {start start' first : Nat} {blocked hF0 : Height}
    {i j : Nat} {a b : NamedAttestation V} {ta tb : Time}
    {Cfg Cfg' : NamedBlock V} {T T' : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hseed' : PrefixFGSelectorConeAt S rho start' first blocked j b tb Cfg' T')
    (hfirst : FirstHeightProgressAt S rho (blocked + 1) first)
    (hcap : HonestPrefixFinalityCap S rho first hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (ready : GradeRoundReady S rho a.round)
    (hround : a.round = b.round) : T = T' := by
  let cut := strictEventIndex rho (S.a a.round)
  have hcut : cut < first := hseed.actionPrefix_lt adm.toNamedScheduleWellFormed
  have hcapCut := honestPrefixFinalityCap_of_le
    S adm.toNamedScheduleWellFormed (Nat.le_of_lt hcut) hcap
  have hfrontier : honestHMaxBeforeIndex S rho cut < blocked + 2 :=
    (hfirst.before cut hcut).trans_lt (Nat.lt_succ_self (blocked + 1))
  have hhor : S.a a.round ≤ rho.horizon := by
    have hin := (adm.in_horizon (Event.tick a.val_index ta)
      (List.mem_of_getElem? hseed.exactTick)).2
    simpa only [Event.time, hseed.actionTime_eq] using hin
  have hsource' : actionFGSource S
      (actionStoreAt S rho b.val_index a.round) = some Cfg'.erase := by
    simpa only [hround] using hseed'.exactFGSource
  have hsourceMem' : Cfg' ∈
      (actionStoreAt S rho b.val_index a.round).st.bodies := by
    simpa only [hround] using hseed'.sourceMem
  have hcompat := actionFGSources_compatible_of_recoveryPrefix
    S adm hcom hbelow ready hseed.signerHonest hseed'.signerHonest
      hseed.exactFGSource hseed.sourceMem hsource' hsourceMem'
      hcapCut hrec hseed.sourceDerivedHeight hseed'.sourceDerivedHeight
        (Nat.le_refl cut) hfrontier hhor
  have hCfgRun := actionBody_runBlock_named S adm hseed.signerHonest hseed.sourceMem
  have hCfg'Run := actionBody_runBlock_named S adm hseed'.signerHonest hseed'.sourceMem
  have hnamedCompat : NamedBlock.compatible Cfg Cfg' = true := by
    simp only [Block.compatible, Bool.or_eq_true] at hcompat
    simp only [NamedBlock.compatible, Bool.or_eq_true]
    rcases hcompat with hpre | hpre
    · exact Or.inl (Protocol.namedPreceq_of_runBlock_erase_preceq
        adm hCfgRun hCfg'Run hpre)
    · exact Or.inr (Protocol.namedPreceq_of_runBlock_erase_preceq
        adm hCfg'Run hCfgRun hpre)
  apply fgConfirmationWitness_eq_of_compatible_of_height_eq S
    hnamedCompat
    (hseed.sourceDerivedHeight.trans hseed'.sourceDerivedHeight.symm)
    hseed.checkpointDerived hseed'.checkpointDerived

/-- An actual honest height row from the source round has the seed's exact
witness. No second cone seed is required: the row's source is extracted from
its actual emission. This is the interface for quorum contributors. -/
theorem PrefixFGSelectorConeAt.confirmationWitness_of_sameRound_honestHeightRow
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked hF0 : Height}
    {i : Nat} {a b : NamedAttestation V} {ta tb : Time}
      {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : FirstHeightProgressAt S rho (blocked + 1) first)
    (hcap : HonestPrefixFinalityCap S rho first hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (ready : GradeRoundReady S rho a.round)
    (hb : b.val_index ∈ rho.honest)
    (hemit : rho.emits S b.val_index (Object.attest b) tb)
    (hrow : b.height_pair.erase.height? = some (blocked + 1))
    (hround : a.round = b.round) :
    fgConfirmationWitness S (actionStoreAt S rho b.val_index b.round) = some T := by
  obtain ⟨Cfg', T', htime', ha', hsource', hCfgMem', hstoredHeight',
      hheight', hT', hshape'⟩ :=
    honestEmittedHeightRow_exactFGSelectorWitness S adm hb hemit hrow
  have hselected' : fgConfirmationWitness S
      (actionStoreAt S rho b.val_index b.round) = some T' := by
    have hderived' := actionStoreDerived_named_local S hCfgMem'
    simp only [fgConfirmationWitness, hsource', Option.map_some]
    rw [hderived']
    exact congrArg some hT'.symm
  let cut := strictEventIndex rho (S.a a.round)
  have hcut : cut < first := hseed.actionPrefix_lt adm.toNamedScheduleWellFormed
  have hcapCut := honestPrefixFinalityCap_of_le
    S adm.toNamedScheduleWellFormed (Nat.le_of_lt hcut) hcap
  have hfrontier : honestHMaxBeforeIndex S rho cut < blocked + 2 :=
    (hfirst.before cut hcut).trans_lt (Nat.lt_succ_self (blocked + 1))
  have hhor : S.a a.round ≤ rho.horizon := by
    have hin := (adm.in_horizon (Event.tick a.val_index ta)
      (List.mem_of_getElem? hseed.exactTick)).2
    simpa only [Event.time, hseed.actionTime_eq] using hin
  have hsourceAtRound : actionFGSource S
      (actionStoreAt S rho b.val_index a.round) = some Cfg'.erase := by
    simpa only [hround] using hsource'
  have hsourceMemAtRound : Cfg' ∈
      (actionStoreAt S rho b.val_index a.round).st.bodies := by
    simpa only [hround] using hCfgMem'
  have hcompat := actionFGSources_compatible_of_recoveryPrefix
    S adm hcom hbelow ready hseed.signerHonest hb hseed.exactFGSource
      hseed.sourceMem hsourceAtRound hsourceMemAtRound hcapCut hrec
      hseed.sourceDerivedHeight hheight' (Nat.le_refl cut) hfrontier hhor
  have hCfgRun := actionBody_runBlock_named S adm hseed.signerHonest hseed.sourceMem
  have hCfg'Run := actionBody_runBlock_named S adm hb hCfgMem'
  have hnamedCompat : NamedBlock.compatible Cfg Cfg' = true := by
    simp only [Block.compatible, Bool.or_eq_true] at hcompat
    simp only [NamedBlock.compatible, Bool.or_eq_true]
    rcases hcompat with hpre | hpre
    · exact Or.inl (Protocol.namedPreceq_of_runBlock_erase_preceq
        adm hCfgRun hCfg'Run hpre)
    · exact Or.inr (Protocol.namedPreceq_of_runBlock_erase_preceq
        adm hCfg'Run hCfgRun hpre)
  have heq : T = T' := by
    apply fgConfirmationWitness_eq_of_compatible_of_height_eq S
      hnamedCompat (hseed.sourceDerivedHeight.trans hheight'.symm)
      hseed.checkpointDerived hT'
  exact heq ▸ hselected'

/-- An honest source-height row in the seed round has the seed's exact
checkpoint witness, using only the current height-regime frame. -/
theorem PrefixFGSelectorConeAt.confirmationWitness_of_sameRound_honestHeightRow_of_frame
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a b : NamedAttestation V} {ta tb : Time}
      {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    {Tprev : Block V} {c0 : Round}
    (hframe : HeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (ready : GradeRoundReady S rho a.round)
    (hb : b.val_index ∈ rho.honest)
    (hemit : rho.emits S b.val_index (Object.attest b) tb)
    (hrow : b.height_pair.erase.height? = some (blocked + 1))
    (hround : a.round = b.round) :
    fgConfirmationWitness S
      (actionStoreAt S rho b.val_index b.round) = some T := by
  obtain ⟨Cfg', T', _, _, hsource', hCfgMem', _, hheight', hT', _⟩ :=
    honestEmittedHeightRow_exactFGSelectorWitness S adm hb hemit hrow
  have hselected' : fgConfirmationWitness S
      (actionStoreAt S rho b.val_index b.round) = some T' := by
    have hderived' := actionStoreDerived_named_local S hCfgMem'
    simp only [fgConfirmationWitness, hsource', Option.map_some]
    rw [hderived']
    exact congrArg some hT'.symm
  let cut := strictEventIndex rho (S.a a.round)
  have hcut : cut < first :=
    hseed.actionPrefix_lt adm.toNamedScheduleWellFormed
  have hframeCut : HeightRegimeFrame S rho blocked cut Tprev c0 :=
    hframe.mono (Nat.le_sub_one_of_lt hcut)
  have hfrontier : honestHMaxBeforeIndex S rho cut < blocked + 2 :=
    (hfirst.before cut hcut).trans_lt (Nat.lt_succ_self (blocked + 1))
  have hhor : S.a a.round ≤ rho.horizon := hseed.actionHorizon adm
  have hsourceAtRound : actionFGSource S
      (actionStoreAt S rho b.val_index a.round) = some Cfg'.erase := by
    simpa only [hround] using hsource'
  have hsourceMemAtRound : Cfg' ∈
      (actionStoreAt S rho b.val_index a.round).st.bodies := by
    simpa only [hround] using hCfgMem'
  have hTCfg0 : Block.Preceq Tprev Cfg.erase :=
    hframe.namedSourceAbove a.val_index hseed.signerHonest a.round
      (Nat.le_sub_one_of_lt hcut) hhor Cfg hseed.sourceMem
        hseed.exactFGSource hseed.sourceDerivedHeight
  have hTCfg1 : Block.Preceq Tprev Cfg'.erase :=
    hframe.namedSourceAbove b.val_index hb a.round
      (Nat.le_sub_one_of_lt hcut) hhor Cfg' hsourceMemAtRound
        hsourceAtRound hheight'
  have hsourceNode := nodeFGSource_of_actionFGSource_local
    S rho a.val_index a.round hseed.exactFGSource
  have hsourceNode' := nodeFGSource_of_actionFGSource_local
    S rho b.val_index a.round hsourceAtRound
  have hcompat := actionFGSources_compatible_of_frame
    S adm hcom hbelow ready hseed.signerHonest hb hsourceNode hsourceNode'
      hseed.sourceMem hsourceMemAtRound hframeCut hseed.sourceDerivedHeight
        hheight' hTCfg0 hTCfg1 (Nat.le_refl cut) hfrontier hhor
  have hCfgRun := actionBody_runBlock_named
    S adm hseed.signerHonest hseed.sourceMem
  have hCfg'Run := actionBody_runBlock_named S adm hb hCfgMem'
  have hnamedCompat : NamedBlock.compatible Cfg Cfg' = true := by
    simp only [Block.compatible, Bool.or_eq_true] at hcompat
    simp only [NamedBlock.compatible, Bool.or_eq_true]
    rcases hcompat with hpre | hpre
    · exact Or.inl (Protocol.namedPreceq_of_runBlock_erase_preceq
        adm hCfgRun hCfg'Run hpre)
    · exact Or.inr (Protocol.namedPreceq_of_runBlock_erase_preceq
        adm hCfg'Run hCfgRun hpre)
  have heq : T = T' := by
    apply fgConfirmationWitness_eq_of_compatible_of_height_eq S
      hnamedCompat (hseed.sourceDerivedHeight.trans hheight'.symm)
      hseed.checkpointDerived hT'
  exact heq ▸ hselected'

#print axioms PrefixFGSelectorConeAt.confirmationWitness_of_sameRound_honestHeightRow_of_frame

/-- An honest source-height row has the seed checkpoint witness, using a
named-predecessor regime frame. -/
theorem PrefixFGSelectorConeAt.confirmationWitness_of_sameRound_honestHeightRow_of_frameN
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a b : NamedAttestation V} {ta tb : Time}
      {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    {Tprev : NamedBlock V} {c0 : Round}
    (hframe : HeightRegimeFrameN S rho blocked (first - 1) Tprev c0)
    (ready : GradeRoundReady S rho a.round)
    (hb : b.val_index ∈ rho.honest)
    (hemit : rho.emits S b.val_index (Object.attest b) tb)
    (hrow : b.height_pair.erase.height? = some (blocked + 1))
    (hround : a.round = b.round) :
    fgConfirmationWitness S
      (actionStoreAt S rho b.val_index b.round) = some T := by
  obtain ⟨Cfg', T', _, _, hsource', hCfgMem', _, hheight', hT', _⟩ :=
    honestEmittedHeightRow_exactFGSelectorWitness S adm hb hemit hrow
  have hselected' : fgConfirmationWitness S
      (actionStoreAt S rho b.val_index b.round) = some T' := by
    have hderived' := actionStoreDerived_named_local S hCfgMem'
    simp only [fgConfirmationWitness, hsource', Option.map_some]
    rw [hderived']
    exact congrArg some hT'.symm
  let cut := strictEventIndex rho (S.a a.round)
  have hcut : cut < first :=
    hseed.actionPrefix_lt adm.toNamedScheduleWellFormed
  have hframeCut : HeightRegimeFrameN S rho blocked cut Tprev c0 :=
    hframe.mono (Nat.le_sub_one_of_lt hcut)
  have hfrontier : honestHMaxBeforeIndex S rho cut < blocked + 2 :=
    (hfirst.before cut hcut).trans_lt (Nat.lt_succ_self (blocked + 1))
  have hhor : S.a a.round ≤ rho.horizon := hseed.actionHorizon adm
  have hsourceAtRound : actionFGSource S
      (actionStoreAt S rho b.val_index a.round) = some Cfg'.erase := by
    simpa only [hround] using hsource'
  have hsourceMemAtRound : Cfg' ∈
      (actionStoreAt S rho b.val_index a.round).st.bodies := by
    simpa only [hround] using hCfgMem'
  have hTCfg0 : Block.Preceq Tprev.erase Cfg.erase :=
    hframe.namedSourceAbove a.val_index hseed.signerHonest a.round
      (Nat.le_sub_one_of_lt hcut) hhor Cfg hseed.sourceMem
        hseed.exactFGSource hseed.sourceDerivedHeight
  have hTCfg1 : Block.Preceq Tprev.erase Cfg'.erase :=
    hframe.namedSourceAbove b.val_index hb a.round
      (Nat.le_sub_one_of_lt hcut) hhor Cfg' hsourceMemAtRound
        hsourceAtRound hheight'
  have hsourceNode := nodeFGSource_of_actionFGSource_local
    S rho a.val_index a.round hseed.exactFGSource
  have hsourceNode' := nodeFGSource_of_actionFGSource_local
    S rho b.val_index a.round hsourceAtRound
  have hcompat := actionFGSources_compatible_of_frameN
    S adm hcom hbelow ready hseed.signerHonest hb hsourceNode hsourceNode'
      hseed.sourceMem hsourceMemAtRound hframeCut hseed.sourceDerivedHeight
        hheight' hTCfg0 hTCfg1 (Nat.le_refl cut) hfrontier hhor
  have hCfgRun := actionBody_runBlock_named
    S adm hseed.signerHonest hseed.sourceMem
  have hCfg'Run := actionBody_runBlock_named S adm hb hCfgMem'
  have hnamedCompat : NamedBlock.compatible Cfg Cfg' = true := by
    simp only [Block.compatible, Bool.or_eq_true] at hcompat
    simp only [NamedBlock.compatible, Bool.or_eq_true]
    rcases hcompat with hpre | hpre
    · exact Or.inl (Protocol.namedPreceq_of_runBlock_erase_preceq
        adm hCfgRun hCfg'Run hpre)
    · exact Or.inr (Protocol.namedPreceq_of_runBlock_erase_preceq
        adm hCfg'Run hCfgRun hpre)
  have heq : T = T' := by
    apply fgConfirmationWitness_eq_of_compatible_of_height_eq S
      hnamedCompat (hseed.sourceDerivedHeight.trans hheight'.symm)
      hseed.checkpointDerived hT'
  exact heq ▸ hselected'

#print axioms PrefixFGSelectorConeAt.confirmationWitness_of_sameRound_honestHeightRow_of_frameN



/-- For a same-round honest row actually carried by the crossing block,
source provenance supplies the emission and therefore the common witness.
The row's SG output is compatible with that same exact checkpoint. -/
theorem PrefixFGSelectorConeAt.carriedRow_sameRound_witness
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked hF0 : Height}
    {i : Nat} {a b : NamedAttestation V} {ta : Time}
      {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : FirstHeightProgressAt S rho (blocked + 1) first)
    (hcap : HonestPrefixFinalityCap S rho first hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (ready : GradeRoundReady S rho a.round)
    {holder : V} {carrier : NamedBlock V}
    (hcarrier : carrier ∈ (rho.stateBefore S first holder).st.bodies)
    (hbCarrier : b ∈ Protocol.named_chain_attestations carrier)
    (hb : b.val_index ∈ rho.honest)
    (hrow : b.height_pair.erase.height? = some (blocked + 1))
    (hround : a.round = b.round) :
    fgConfirmationWitness S (actionStoreAt S rho b.val_index b.round) = some T ∧
      Block.compatible (actionSGBlockAt S rho b.val_index b.round) T = true := by
  obtain ⟨_, tb, _, _, _, hemit⟩ :=
    honestCarriedAttestation_emittedBeforeIndex S adm hcarrier hbCarrier hb
  have hwitness := hseed.confirmationWitness_of_sameRound_honestHeightRow
    adm hcom hbelow hfirst hcap hrec ready hb hemit hrow hround
  refine ⟨hwitness, ?_⟩
  obtain ⟨Q, hQ⟩ := nodeQ2_of_actionFGSource_local S rho
    a.val_index a.round hseed.exactFGSource
  have hr : 0 < b.round := by
    rw [← hround]
    exact selectedQ2_round_pos_named S adm hQ
  have hhor : S.a b.round ≤ rho.horizon := by
    rw [← hround]
    exact hseed.actionHorizon adm
  exact fgConfirmationWitness_compatible_sgVote S adm hb hr hhor hwitness

/-- A same-round honest target contributor identifies the crossing
certificate's chain checkpoint with the common confirmation witness. This
uses the target root in the actual row; a timeout alone has no such root. -/
theorem PrefixFGSelectorConeAt.preceq_carrier_of_sameRound_honestTarget
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked hF0 : Height}
    {i : Nat} {a b : NamedAttestation V} {ta : Time}
      {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : FirstHeightProgressAt S rho (blocked + 1) first)
    (hcap : HonestPrefixFinalityCap S rho first hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (ready : GradeRoundReady S rho a.round)
    {holder : V} {carrier : NamedBlock V} {X : Block V}
    (hcarrier : carrier ∈ (rho.stateBefore S first holder).st.bodies)
    (hcarrierRun : RunBlock S rho carrier)
    (hX : Block.Preceq X carrier.erase)
    (hbCarrier : b ∈ Protocol.named_chain_attestations carrier)
    (hb : b.val_index ∈ rho.honest)
    (htarget : b.height_pair.erase = HeightPair.target (blocked + 1) X.root)
    (hround : a.round = b.round) : Block.Preceq T carrier.erase := by
  have hrow : b.height_pair.erase.height? = some (blocked + 1) := htarget ▸ rfl
  have hwitness := (hseed.carriedRow_sameRound_witness adm hcom hbelow
    hfirst hcap hrec ready hcarrier hbCarrier hb hrow hround).1
  obtain ⟨_, tb, _, _, _, hemit⟩ :=
    honestCarriedAttestation_emittedBeforeIndex S adm hcarrier hbCarrier hb
  obtain ⟨D, K, hselected', hD, hDsource, hDheight, hK, hKentry,
      hKheight, hKpre, hshapes⟩ :=
    honestHeightRow_confirmationWitness S adm hb hemit hrow
  have hTeq : (Protocol.derive_named S.E S.cfg K).T_h = T :=
    Option.some.inj (hselected'.symm.trans hwitness)
  have hDrun := actionBody_runBlock_named S adm hb hD
  have hKrun := actionBody_runBlock_named S adm hb hK
  have hKpreNamed : NamedBlock.Preceq K D :=
    Protocol.namedPreceq_of_runBlock_erase_preceq adm hKrun hDrun hKpre
  have hKtarget : (Protocol.derive_named S.E S.cfg K).T_h = K.erase :=
    (Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hKpreNamed
      (hKheight.trans hDheight.symm)).trans hKentry.symm
  have hKeraseT : K.erase = T := hKtarget.symm.trans hTeq
  have hroot : X.root = T.root := by
    rcases hshapes with ht | ht
    · exact (HeightPair.target.inj (htarget.symm.trans ht)).2.trans
        (congrArg Block.root hKeraseT)
    · rw [htarget] at ht
      cases ht
  obtain ⟨A, hAcarrier, hAerase⟩ :=
    Proofs.NamedAncestry.erased_ancestor_lift carrier hX
  have hArun : RunBlock S rho A :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hcarrierRun hAcarrier
  have hrootAK : A.root = K.root := by
    rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root K, hAerase, hKeraseT]
    exact hroot
  have hAK : A = K :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      A K hArun hKrun A K
      (Or.inl (Proofs.NamedAncestry.named_self A))
      (Or.inr (Proofs.NamedAncestry.named_self K)) hrootAK
  have hAcarrier : Block.Preceq A.erase carrier.erase := by
    simpa only [hAerase] using hX
  have hKcarrier : Block.Preceq K.erase carrier.erase := by
    simpa only [hAK] using hAcarrier
  simpa only [hKeraseT] using hKcarrier





def namedCrossingWitness (S : Setup V) (carrier : NamedBlock V)
    (h : Height) : Prop :=
  ∃ X : NamedBlock V, NamedBlock.Preceq X carrier ∧
    (Protocol.derive_named S.E S.cfg X).h = h ∧
    ∃ Q : Finset V, S.E.electorate.IsQuorum Q ∧
      ∀ signer ∈ Q, ∃ carrier' : NamedBlock V, ∃ a : NamedAttestation V,
        NamedBlock.Preceq carrier' carrier ∧ a ∈ carrier'.attestations ∧
        a.val_index = signer ∧
          a.height_pair.matchesEntry h X.root = true

omit [Fintype V] in
private theorem named_row_mem_chain_of_ancestor_local
    {A B : NamedBlock V} {a : NamedAttestation V}
    (hAB : NamedBlock.Preceq A B) (ha : a ∈ A.attestations) :
    a ∈ Protocol.named_chain_attestations B := by
  induction B generalizing A with
  | genesis =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
      subst A
      simp [NamedBlock.attestations] at ha
  | node parent slot root votes support rows proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      simp only [Protocol.named_chain_attestations, Finset.mem_union,
        List.mem_toFinset]
      rcases hAB with rfl | hparent
      · exact Or.inr ha
      · exact Or.inl (ih hparent ha)

omit [DecidableEq V] [Fintype V] in
private theorem named_heightPair_shape_of_matches_local
    {a : NamedAttestation V} {h : Height} {root : BlockId}
    (hm : a.height_pair.matchesEntry h root = true) :
    a.height_pair.erase = HeightPair.target h root ∨
      a.height_pair.erase = HeightPair.timeout h := by
  cases hp : a.height_pair with
  | empty =>
      simp [hp, NamedHeightPair.matchesEntry] at hm
  | vote height entry timeout =>
      simp only [hp, NamedHeightPair.matchesEntry, decide_eq_true_eq] at hm
      cases timeout with
      | false =>
          left
          simp [NamedHeightPair.erase, hm.1, hm.2]
      | true =>
          right
          simp [NamedHeightPair.erase, hm.1]

/-- Classify an actual crossing certificate without assuming its source
rounds agree or that its carrier extends the confirmation witness. If no
same-round honest target identifies the carrier, retain a different-round
honest source or an actual quorum of same-round honest timeout rows. Those
timeout rows still have the exact common witness and compatible SG outputs. -/
theorem PrefixFGSelectorConeAt.crossingCertificate_cases
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked hF0 : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
      {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : FirstHeightProgressAt S rho (blocked + 1) first)
    (hcap : HonestPrefixFinalityCap S rho first hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (ready : GradeRoundReady S rho a.round)
    {holder : V} {carrier : NamedBlock V}
    (hcarrier : carrier ∈ (rho.stateBefore S first holder).st.bodies)
    (hcarrierRun : RunBlock S rho carrier)
    (hcertificate : namedCrossingWitness S carrier (blocked + 1)) :
    Block.Preceq T carrier.erase ∨
      (∃ b ∈ Protocol.named_chain_attestations carrier,
        b.val_index ∈ rho.honest ∧
        b.height_pair.erase.height? = some (blocked + 1) ∧ b.round ≠ a.round) ∨
      (∃ Q : Finset V, S.E.electorate.IsQuorum Q ∧
        ∀ v ∈ Q, v ∈ rho.honest →
          ∃ b ∈ Protocol.named_chain_attestations carrier,
          b.val_index = v ∧ b.round = a.round ∧
          b.height_pair.erase = HeightPair.timeout (blocked + 1) ∧
          fgConfirmationWitness S (actionStoreAt S rho b.val_index b.round) = some T ∧
          Block.compatible (actionSGBlockAt S rho b.val_index b.round) T = true) := by
  classical
  by_cases hbound : Block.Preceq T carrier.erase
  · exact Or.inl hbound
  right
  by_cases hother : ∃ b ∈ Protocol.named_chain_attestations carrier,
      b.val_index ∈ rho.honest ∧
      b.height_pair.erase.height? = some (blocked + 1) ∧ b.round ≠ a.round
  · exact Or.inl hother
  right
  obtain ⟨X, hX, hXheight, Q, hQ, hrows⟩ := hcertificate
  refine ⟨Q, hQ, ?_⟩
  intro v hv hvHon
  obtain ⟨carrier', b, hcarrier', hbCarrier', hbval, hmatch⟩ := hrows v hv
  have hbCarrier : b ∈ Protocol.named_chain_attestations carrier :=
    named_row_mem_chain_of_ancestor_local hcarrier' hbCarrier'
  have hbHon : b.val_index ∈ rho.honest := hbval ▸ hvHon
  have hshape := named_heightPair_shape_of_matches_local hmatch
  have hrow : b.height_pair.erase.height? = some (blocked + 1) := by
    rcases hshape with ht | ht <;> exact ht ▸ rfl
  have hround : b.round = a.round := by
    by_contra hne
    exact hother ⟨b, hbCarrier, hbHon, hrow, hne⟩
  rcases hshape with htarget | htimeout
  · exact False.elim (hbound (hseed.preceq_carrier_of_sameRound_honestTarget
      adm hcom hbelow hfirst hcap hrec ready hcarrier hcarrierRun
      (Proofs.NamedWire.erase_preceq hX) hbCarrier hbHon
      (by simpa only [Proofs.NamedWire.erase_root] using htarget) hround.symm))
  · have htmo : b.height_pair.erase = HeightPair.timeout (blocked + 1) := htimeout
    obtain ⟨hwitness, hsg⟩ := hseed.carriedRow_sameRound_witness
      adm hcom hbelow hfirst hcap hrec ready hcarrier hbCarrier hbHon hrow
        hround.symm
    exact ⟨b, hbCarrier, hbval, hround, htmo, hwitness, hsg⟩

/-- An earlier attestation time gives an earlier emission index. This is a
schedule fact and does not require an honest sender. -/
theorem attestationIndex_lt_of_time_lt
    {S : Setup V} {rho : Run V} (sch : ScheduleWellFormed S rho)
    {i j : Nat} {u v : V} {ti tj : Time}
    (hi : rho.events[i]? = some (Event.tick u ti))
    (hj : rho.events[j]? = some (Event.tick v tj)) (ht : ti < tj) : i < j := by
  by_contra hnot
  rcases lt_or_eq_of_le (Nat.le_of_not_gt hnot) with hji | rfl
  · have hkey := Proofs.Optimistic.key_le_of_index_lt S sch hji hj hi
    exact (not_le_of_gt ht) (Proofs.Bridges.time_le_of_key_le hkey)
  · have heq := Option.some.inj (hi.symm.trans hj)
    have htime : ti = tj := congrArg Event.time heq
    exact (lt_irrefl ti) (htime ▸ ht)

/-- A crossing carrier either extends the selected witness, or there is an
actual earlier-prefix honest height row from a different round. In the
same-round timeout-quorum case, record history supplies a strictly earlier
local target. That target need not occur on the carrier chain.

Every retained source was emitted at local `h_max = blocked + 1`. Thus the
remaining branch needs a proof relating different source rounds, not a
record-freshness or common-height assumption. -/
theorem PrefixFGSelectorConeAt.crossingCertificate_preceq_or_differentRoundSource
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked hF0 : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
      {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : FirstHeightProgressAt S rho (blocked + 1) first)
    (hcap : HonestPrefixFinalityCap S rho first hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (ready : GradeRoundReady S rho a.round)
    {holder : V} {carrier : NamedBlock V}
    (hcarrier : carrier ∈ (rho.stateBefore S first holder).st.bodies)
    (hcarrierRun : RunBlock S rho carrier)
    (hcertificate : namedCrossingWitness S carrier (blocked + 1)) :
    Block.Preceq T carrier.erase ∨
      ∃ (b : NamedAttestation V) (j : Nat) (tb : Time),
        b.val_index ∈ rho.honest ∧ j < first ∧
          rho.events[j]? = some (Event.tick b.val_index tb) ∧
          rho.emits S b.val_index (Object.attest b) tb ∧
          b.height_pair.erase.height? = some (blocked + 1) ∧ b.round ≠ a.round ∧
          (actionStoreAt S rho b.val_index b.round).st.core.h_max = blocked + 1 := by
  rcases hseed.crossingCertificate_cases adm hcom hbelow hfirst hcap hrec
      ready hcarrier hcarrierRun hcertificate with hbound | hother | htimeouts
  · exact Or.inl hbound
  · obtain ⟨b, hbCarrier, hbHon, hrow, hround⟩ := hother
    obtain ⟨j, tb, hj, hevent, _, hemit⟩ :=
      honestCarriedAttestation_emittedBeforeIndex S adm hcarrier hbCarrier hbHon
    exact Or.inr ⟨b, j, tb, hbHon, hj, hevent, hemit, hrow, hround,
      hfirst.action_hMax adm hj hbHon hevent hemit hrow⟩
  · obtain ⟨Q, hQ, hrows⟩ := htimeouts
    obtain ⟨v, hv, hvHon⟩ := HonestWeightMajority.exists_honest_member_of_quorum
      (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow) hQ
    obtain ⟨b, hbCarrier, hbval, hbr, hbtimeout, _, _⟩ := hrows v hv hvHon
    have hbHon : b.val_index ∈ rho.honest := hbval ▸ hvHon
    obtain ⟨j, tb, hj, hbevent, _, hbemit⟩ :=
      honestCarriedAttestation_emittedBeforeIndex S adm hcarrier hbCarrier hbHon
    obtain ⟨c, tc, U, hcval, hcr, hct, hcemit, hctarget⟩ :=
      recoverySuccessorTimeout_has_earlier_target S adm hrec.1 hbHon hbemit hbtimeout
    have hcHon : c.val_index ∈ rho.honest := hcval ▸ hbHon
    have hcemitCopy := hcemit
    obtain ⟨k, hcevent, _⟩ := hcemitCopy
    have hk : k < first :=
      (attestationIndex_lt_of_time_lt adm.toNamedScheduleWellFormed hcevent hbevent hct).trans hj
    have hrow0 : c.erase.height_pair.height? = some (blocked + 1) :=
      hctarget ▸ rfl
    have hrow : c.height_pair.erase.height? = some (blocked + 1) := by
      simpa only [NamedAttestation.erase] using hrow0
    have hround : c.round ≠ a.round := (hbr ▸ hcr).ne
    exact Or.inr ⟨c, k, tc, hcHon, hk, hcevent, hcemit, hrow, hround,
      hfirst.action_hMax adm hk hcHon hcevent hcemit hrow⟩







/-
/-- Exact same-round checkpoints agree, from the regime frame. -/
theorem PrefixFGSelectorConeAt.confirmationWitness_of_sameRound_honestHeightRow_of_frame
    {S: Setup V} {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    {start first: Nat} {blocked: Height}
    {i: Nat} {a b: NamedAttestation V} {ta tb: Time}
      {Cfg: NamedBlock V} {T: Block V}
    (hseed: PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst: HeightWindowAt S rho (blocked + 1) first)
    {Tprev: Block V} {c0: Round}
    (hframe: HeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (ready: GradeRoundReady S rho a.round)
    (hb: b.val_index ∈ rho.honest)
    (hemit: rho.emits S b.val_index (Object.attest b) tb)
    (hrow: b.height_pair.erase.height? = some (blocked + 1))
    (hround: a.round = b.round):
    fgConfirmationWitness S (actionStoreAt S rho b.val_index b.round) = some T:= by
  obtain ⟨Cfg', T', _, _, hsource', _, _, hheight', _, hT', _⟩:=
    honestEmittedHeightRow_exactFGSelectorWitness S adm hb hemit hrow
  have hselected': fgConfirmationWitness S
      (actionStoreAt S rho b.val_index b.round) = some T':= by
    simp only [fgConfirmationWitness, actionStoreAt_round, hsource', Option.map_some]
    exact congrArg some hT'.symm
  let cut:= strictEventIndex rho (S.a a.round)
  have hcut: cut < first:= hseed.actionPrefix_lt adm.toNamedScheduleWellFormed
  have hframeCut: HeightRegimeFrame S rho blocked cut Tprev c0:= hframe.mono (Nat.le_sub_one_of_lt hcut)
  have hfrontier: honestHMaxBeforeIndex S rho cut < blocked + 2:=
    (hfirst.before cut hcut).trans_lt (Nat.lt_succ_self (blocked + 1))
  have hhor: S.a a.round ≤ rho.horizon:= by
    have hin:= (adm.in_horizon (Event.tick a.val_index ta)
      (List.mem_of_getElem? hseed.exactTick)).2
    simpa only [Event.time, hseed.actionTime_eq] using hin
  have hsourceAtRound: Protocol.fg_source S.E S.hc
      (actionStoreAt S rho b.val_index a.round).toHealing a.round
      (Protocol.grade2_block S.E S.hc
        (actionStoreAt S rho b.val_index a.round).toHealing a.round) = some Cfg':= by
    simpa only [hround] using hsource'
  have hTCfg0: Block.Preceq Tprev Cfg:=
    hframe.sourceAbove a.val_index hseed.signerHonest a.round (Nat.le_sub_one_of_lt hcut)
      (hseed.actionHorizon adm) Cfg
      hseed.exactFGSource hseed.sourceDerivedHeight
  have hTCfg1: Block.Preceq Tprev Cfg':=
    hframe.sourceAbove b.val_index hb a.round (Nat.le_sub_one_of_lt hcut)
      (hseed.actionHorizon adm) Cfg' hsourceAtRound hheight'
  have hcompat:= actionFGSources_compatible_of_frame
    S adm hcom ready hseed.signerHonest hb hseed.exactFGSource
      hsourceAtRound hframeCut hseed.sourceDerivedHeight hheight' hTCfg0 hTCfg1
        (Nat.le_refl cut) hfrontier hhor
  have hTCfg: Block.Preceq T Cfg:= by
    rw [hseed.checkpointDerived]
    exact Proofs.Records.derived_state_T_h_preceq S.E S.cfg Cfg
  have hTCfg': Block.Preceq T' Cfg':= by
    rw [hT']
    exact Proofs.Records.derived_state_T_h_preceq S.E S.cfg Cfg'
  have heq: T = T':= by
    apply fgConfirmationWitness_eq_of_compatible_of_height_eq S
      hseed.confirmationWitness hselected' (compatible_ancestors hTCfg hTCfg' hcompat)
    rw [hseed.checkpointDerived, hT', Protocol.derived_target_height,
      Protocol.derived_target_height, hseed.sourceDerivedHeight, hheight']
  exact heq ▸ hselected'
-/

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
