module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.RecoveryFGRoundAgreement

@[expose] public section

/-!
# Same-round Q2 retention audit

The selected action Q2 is captured at the source G2-domain read. Healthy
delivery moves its exact named body to each honest reader. A height-regime
frame then keeps a source-height selected Q2 in the reader's filtered tree.

The global `SameRoundQ2Retained` predicate quantifies over every selected Q2,
including blocks for which the frame supplies neither the source height nor
the predecessor relation. The source-specific theorem below records the
delivery result that the recovery source-agreement proof can use.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Internal.NamedRecoveryRead Protocol
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]




/-- A selected source-height Q2 remains in every honest reader's exact G1
domain, G0 domain, and prepared action tree, from the fully named regime
frame. -/
theorem sameRoundSourceQ2Retained_of_namedFrame
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (ready : GradeRoundReady S rho r)
    {p : V} (hp : p ∈ rho.honest) {Q : NamedBlock V}
    (hselected : nodeQ2 S (actionReadAt S rho p r) r = some Q.erase)
    (hsource : actionFGSource S (actionStoreAt S rho p r) = some Q.erase)
    (hQmem : Q ∈ (actionStoreAt S rho p r).st.bodies)
    {stop : Nat} {H : Height} {Prev : NamedBlock V} {c0 : Round}
    (hframe : NamedHeightRegimeFrame S rho H stop Prev c0)
    (hQheight : (Protocol.derive_named S.E S.cfg Q).h = H + 1)
    (hactionPrefix : strictEventIndex rho (S.a r) ≤ stop)
    (hfrontier : honestHMaxBeforeIndex S rho stop < H + 2)
    (hactionHor : S.a r ≤ rho.horizon) :
    ∀ w, w ∈ rho.honest →
      Q.erase ∈ filteredTree
          (readAt S rho (domain S.E S.hc r .g1) w) ∧
      Q.erase ∈ filteredTree
          (readAt S rho (domain S.E S.hc r .g0) w) ∧
      Q.erase ∈ filteredTree (actionReadAt S rho w r) := by
  have hinputs := voterAnchorSourceQ2Inputs_of_namedHeightRegimeFrame_at_source
    S adm ready hframe hactionPrefix hfrontier hactionHor hp Q hselected
      hsource hQmem hQheight
  intro w hw
  have hG1 := hinputs.g1Target w hw
  have hG0 : Q.erase ∈ filteredTree
      (readAt S rho (domain S.E S.hc r .g0) w) := by
    rw [domain_g0_eq_Γ_1, Protocol.Γ_1_eq_vote_time]
    simpa only [filteredTree, PhaseGrades.readAt, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, Protocol.NamedStore.setClock] using
      hinputs.openingTarget w hw
  have hPrevQ : NamedBlock.Preceq Prev Q :=
    hframe.sourceAbove p hp r hactionPrefix hactionHor Q hQmem hsource
      hQheight
  have hfloor : FinalityFloorAt S rho H stop Prev.erase := by
    intro v hv n hn X hXrun hXheight hPrevX
    exact hframe.floor v hv n hn X hXrun hXheight
      (Protocol.namedPreceq_of_runBlock_erase_preceq
        adm hframe.prevRun hXrun hPrevX)
  have hbodies := selectedQ2_body_at_action_and_openingVote_of_floor
    S adm ready hp hselected hQmem hfloor hQheight
      (Proofs.NamedWire.erase_preceq hPrevQ) hactionPrefix hw
  have hbody : Q ∈
      (NamedRun.stateBeforeTime S rho (S.a r) w).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hbodies.1
  have heq := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedScheduleWellFormed (S.a r)) w
  have hbody' := hbody
  rw [heq] at hbody'
  have hfiltered := hframe.fgRoot_preceq_and_filteredMem
    adm hfrontier hw hactionPrefix hbody' hQheight hPrevQ
  have haction : Q.erase ∈ filteredTree (actionReadAt S rho w r) := by
    have hpre : Q.erase ∈ Protocol.get_filtered_block_tree
        (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.toHealing.toFG := by
      rw [heq]
      exact hfiltered.2
    simpa only [filteredTree, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hpre
  exact ⟨hG1, hG0, haction⟩

omit [Fintype V] in
private theorem finalized_preceq_of_filteredTree_pointwise
    {n : NamedNodeState V} {B : Block V}
    (hB : B ∈ filteredTree n) : Block.Preceq n.st.core.F B := by
  exact (Finset.mem_filter.mp
    (Finset.mem_filter.mp (Finset.mem_filter.mp hB).1).1).2

omit [Fintype V] in
private theorem cover_preceq_pointwise
    {gv : Protocol.GradeView V} {u : Protocol.SGVote V}
    {root : BlockId} {Q H : Block V}
    (hcover : DecoupledConsensusModel.Protocol.localCovers gv u.confirmed Q = true)
    (hconf : u.confirmed = some root)
    (hfind : Block.find? gv.T root = some H) : Block.Preceq Q H := by
  unfold DecoupledConsensusModel.Protocol.localCovers Protocol.head_covers at hcover
  simp only [hconf] at hcover
  rw [hfind] at hcover
  exact hcover

private theorem selectedQ2_g1_g0_at_reader_pointwise
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho) {r : Round} (hr : 0 < r)
    (ready : GradeRoundReady S rho r)
    {p w : V} (hp : p ∈ rho.honest) (hw : w ∈ rho.honest)
    {Q : Block V}
    (hQ : nodeQ2 S (actionReadAt S rho p r) r = some Q)
    (hQg1 : Q ∈ filteredTree (readAt S rho (domain S.E S.hc r .g1) w))
    (hQg0 : Q ∈ filteredTree (readAt S rho (domain S.E S.hc r .g0) w)) :
    storeGrade S.E S.hc (readAt S rho (domain S.E S.hc r .g1) w).st
        r .g1 Q = true ∧
      storeGrade S.E S.hc (readAt S rho (domain S.E S.hc r .g0) w).st
        r .g0 Q = true := by
  have hFg1Q := finalized_preceq_of_filteredTree_pointwise hQg1
  have hbelowReaders := crossReaderFinalizedBelow_of_finalitySafety_and_relay
    S adm hsb ready.1 ready.2 hp hw (by
      intro sender u root H _ hcover hconf hfind
      exact Block.preceq_trans hFg1Q
        (cover_preceq_pointwise hcover hconf hfind))
  have hguard := crossReaderBodyReadyGuard_of_finalizedBelow
    S adm.toNamedAdmissibleCore hr ready.1 ready.2 hp hw hbelowReaders
  have hG2 := selectedQ2_storeGrade_at_g2Domain S adm hQ
  have hG1 := storeGrade_g1_of_storeGrade_g2_cross_reader
    S rho adm.toNamedAdmissibleCore r
      (twoCutoffDelivery_of_core S adm.toNamedAdmissibleCore ready.1)
      ready.2 p w hp hw Q hG2 hguard
  have hgstG1 : S.E.t_GST ≤ early S.E S.hc r .g1 :=
    ready.1.trans (GradeCutoffMono.early_g2_le_early_g1 S.E S.hc r)
  have hFg0Q := finalized_preceq_of_filteredTree_pointwise hQg0
  have hbelow0 :=
    g1G0CrossReaderFinalizedBelow_of_finalitySafety_and_relay
      S adm hsb hgstG1 ready.2 hw hw (by
        intro sender u root H _ hcover hconf hfind
        exact Block.preceq_trans hFg0Q
          (cover_preceq_pointwise hcover hconf hfind))
  have hguard0 := g1G0CrossReaderBodyReadyGuard_of_finalizedBelow
    S adm.toNamedAdmissibleCore hr hgstG1 ready.2 hw hw hbelow0
  refine ⟨hG1, ?_⟩
  exact storeGrade_g0_of_storeGrade_g1_cross_reader
    S rho adm.toNamedAdmissibleCore r
      (g1G0TwoCutoffDelivery_of_core S adm.toNamedAdmissibleCore hgstG1)
      ready.2 w w hw hw Q hG1 hguard0

private theorem g0Grade_compatible_clearSource_pointwise
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (hr : 0 < r) (hactionHor : S.a r ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) {Q C : Block V}
    (hQgrade : storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc r .g0) w).st r .g0 Q = true)
    (hQg0 : Q ∈ filteredTree (readAt S rho (domain S.E S.hc r .g0) w))
    (hQaction : Q ∈ filteredTree (actionReadAt S rho w r))
    (hCclear : nodeClear S (actionReadAt S rho w r) r C = true) :
    Block.compatible Q C = true := by
  have hQtree : Q ∈
      (readAt S rho (domain S.E S.hc r .g0) w).st.core.T :=
    Proofs.Records.get_filtered_block_tree_subset _ hQg0
  obtain ⟨raw, hraw, hQraw⟩ := NamedOutageClosure.q10_freeze_of_graded
    S.E (readAt S rho (domain S.E S.hc r .g0) w).st.core.toHealing.gradeView
    (readAt S rho (domain S.E S.hc r .g0) w).st.core.F
    S.hc.η_SG r (e := early S.E S.hc r .g0) (l := late S.E S.hc r .g0)
    (by simp only [early, late, Phase.earlyOffset, Phase.lateOffset]; exact le_rfl)
    hQtree (by simpa only [storeGrade] using hQgrade)
  have hactionFrame := actionFrame_g0 S adm.toNamedAdmissibleCore
    hw hr hactionHor
  have hframe :
      (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho w r).cache
        (actionReadAt S rho w r).st.core.toHealing r).g0 =
        some (some (DecoupledConsensusModel.Protocol.clipGrade raw
          (actionReadAt S rho w r).st.core.F)) := by
    simpa only [storeRoot, phaseRoot, hraw, Option.map_some] using hactionFrame
  have hFQ : Block.Preceq (actionReadAt S rho w r).st.core.F Q :=
    finalized_preceq_of_filteredTree_pointwise hQaction
  have hQclip : Block.Preceq Q
      (DecoupledConsensusModel.Protocol.clipGrade raw
        (actionReadAt S rho w r).st.core.F) := by
    apply (NamedOutageClosure.q10_retained_prefix raw
      (actionReadAt S rho w r).st.core.F Q ?_).mpr hQraw
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr hFQ
  have hCclip : Block.compatible C
      (DecoupledConsensusModel.Protocol.clipGrade raw
        (actionReadAt S rho w r).st.core.F) = true := by
    simpa only [nodeClear, nodeRead, NamedProfile.gradeContract,
      DecoupledConsensusModel.Protocol.frameContract, DecoupledConsensusModel.Protocol.frameGradeRead,
      DecoupledConsensusModel.Protocol.clear, hframe] using hCclear
  simp only [Block.compatible, Bool.or_eq_true] at hCclip ⊢
  rcases hCclip with hCclip | hclipC
  · exact (Block.preceq_linear hQclip hCclip).elim Or.inl Or.inr
  · exact Or.inl (Block.preceq_trans hQclip hclipC)

private theorem nodeQ2_of_nodeFGSource_pointwise
    (S : Setup V) (rho : Run V) (v : V) (r : Round) {B : Block V}
    (hB : nodeFGSource S (actionReadAt S rho v r) r = some B) :
    ∃ Q, nodeQ2 S (actionReadAt S rho v r) r = some Q := by
  cases hQ : nodeQ2 S (actionReadAt S rho v r) r with
  | none =>
      have hQ' : Protocol.grade2_block_with
          (NamedProfile.gradeContract (actionReadAt S rho v r).cache)
          S.E S.hc (actionReadAt S rho v r).st.core.toHealing r = none := by
        simpa only [nodeQ2, nodeRead, Protocol.grade2_block_with] using hQ
      rw [nodeFGSource, Protocol.fg_source_with.eq_def, hQ'] at hB
      cases hB
  | some Q => exact ⟨Q, rfl⟩

private theorem relative_gradeBool_zero_pointwise
    (E : Env V) (gv : Protocol.GradeView V) (F : Block V)
    (eta : Round) (earlyTime lateTime : Time) (B : Block V) :
    DecoupledConsensusModel.Protocol.gradeBool E gv F eta 0 earlyTime lateTime B =
      false := by
  simp [DecoupledConsensusModel.Protocol.gradeBool,
    DecoupledConsensusModel.Protocol.positive, DecoupledConsensusModel.Protocol.opposing,
    DecoupledConsensusModel.Protocol.readyView, DecoupledConsensusModel.Protocol.rawView,
    DecoupledConsensusModel.Protocol.interpretedInputs, DecoupledConsensusModel.Protocol.rawInputs,
    Protocol.latest_window_zero, DecoupledConsensusModel.Protocol.Supports,
    DecoupledConsensusModel.Protocol.Opposes, DecoupledConsensusModel.Protocol.CleanFrom]

private theorem nodeQ2_round_pos_pointwise
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} {r : Round} {Q : Block V}
    (hQ : nodeQ2 S (actionReadAt S rho v r) r = some Q) : 0 < r := by
  apply Nat.pos_of_ne_zero
  intro hzero
  subst r
  have hgrade := selectedQ2_storeGrade_at_g2Domain S adm hQ
  simp only [storeGrade, phaseGrade] at hgrade
  rw [relative_gradeBool_zero_pointwise] at hgrade
  cases hgrade

private theorem selectedQ2_compatible_genuineSource_pointwise
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho) {r : Round} (hr : 0 < r)
    (ready : GradeRoundReady S rho r) (hhor : S.a r ≤ rho.horizon)
    {p w : V} (hp : p ∈ rho.honest) (hw : w ∈ rho.honest)
    {Q C X : Block V}
    (hQ : nodeQ2 S (actionReadAt S rho p r) r = some Q)
    (hretained : ∀ z, z ∈ rho.honest →
      Q ∈ filteredTree (readAt S rho (domain S.E S.hc r .g1) z) ∧
      Q ∈ filteredTree (readAt S rho (domain S.E S.hc r .g0) z) ∧
      Q ∈ filteredTree (actionReadAt S rho z r))
    (hwalk : Protocol.deepest_clear (some C)
      (actionStoreAt S rho w r).st.core.live_confirmed
      ((NamedProfile.gradeContract
        (actionStoreAt S rho w r).cache).read S.E S.hc
          (actionStoreAt S rho w r).st.core.toHealing r).clear = some X) :
    Block.compatible Q X = true := by
  obtain ⟨-, hQG0⟩ := selectedQ2_g1_g0_at_reader_pointwise
    S adm hsb hr ready hp hw hQ (hretained w hw).1
      (hretained w hw).2.1
  have hXclear : nodeClear S (actionReadAt S rho w r) r X = true := by
    unfold Protocol.deepest_clear at hwalk
    have htest := (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hwalk)).2.2
    simpa only [nodeClear, nodeRead, actionStoreAt] using htest
  exact g0Grade_compatible_clearSource_pointwise S adm hr hhor hw hQG0
    (hretained w hw).2.1 (hretained w hw).2.2 hXclear

/-- Honest prepared FG sources in one ready round are compatible when the
retention carrier is supplied only for either source if that source is the
selected Q2. -/
theorem actionFGSources_compatible_sameRound_pointwise
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho) {r : Round}
    (ready : GradeRoundReady S rho r)
    {p w : V} (hp : p ∈ rho.honest) (hw : w ∈ rho.honest)
    {B C : Block V}
    (hB : nodeFGSource S (actionReadAt S rho p r) r = some B)
    (hC : nodeFGSource S (actionReadAt S rho w r) r = some C)
    (hBretained : nodeQ2 S (actionReadAt S rho p r) r = some B →
      ∀ z, z ∈ rho.honest →
        B ∈ filteredTree (readAt S rho (domain S.E S.hc r .g1) z) ∧
        B ∈ filteredTree (readAt S rho (domain S.E S.hc r .g0) z) ∧
        B ∈ filteredTree (actionReadAt S rho z r))
    (hCretained : nodeQ2 S (actionReadAt S rho w r) r = some C →
      ∀ z, z ∈ rho.honest →
        C ∈ filteredTree (readAt S rho (domain S.E S.hc r .g1) z) ∧
        C ∈ filteredTree (readAt S rho (domain S.E S.hc r .g0) z) ∧
        C ∈ filteredTree (actionReadAt S rho z r))
    (hhor : S.a r ≤ rho.horizon) : Block.compatible B C = true := by
  obtain ⟨Qp, hQp⟩ := nodeQ2_of_nodeFGSource_pointwise S rho p r hB
  obtain ⟨Qw, hQw⟩ := nodeQ2_of_nodeFGSource_pointwise S rho w r hC
  have hr := nodeQ2_round_pos_pointwise S adm hQp
  have hBsource : actionFGSource S (actionStoreAt S rho p r) = some B := by
    unfold actionFGSource
    dsimp only
    have hround : S.hc.round_of
        (actionStoreAt S rho p r).st.core.toHealing.s = r := by
      simpa only [Protocol.Store.toHealing] using actionStoreAt_round S rho p r
    rw [hround]
    simpa only [nodeFGSource, nodeRead, actionStoreAt] using hB
  have hCsource : actionFGSource S (actionStoreAt S rho w r) = some C := by
    unfold actionFGSource
    dsimp only
    have hround : S.hc.round_of
        (actionStoreAt S rho w r).st.core.toHealing.s = r := by
      simpa only [Protocol.Store.toHealing] using actionStoreAt_round S rho w r
    rw [hround]
    simpa only [nodeFGSource, nodeRead, actionStoreAt] using hC
  rcases actionFGSource_genuineClear_or_selectedG2_named
      S rho p r hQp hBsource with hBgenuine | hBQ
  · rcases actionFGSource_genuineClear_or_selectedG2_named
        S rho w r hQw hCsource with hCgenuine | hCQ
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
        S adm hp hw hpost hconfHor hX hY
      simp only [Block.compatible, Bool.or_eq_true] at hXY
      rcases hXY with hXY | hYX
      · exact Block.compatible_of_preceq_common
          (Block.preceq_trans hBX hXY) hCY
      · exact Block.compatible_of_preceq_common
          hBX (Block.preceq_trans hCY hYX)
    · subst C
      obtain ⟨X, -, -, hwalk, -, -⟩ := hBgenuine
      have hQB := selectedQ2_compatible_genuineSource_pointwise
        S adm hsb hr ready hhor hw hp hQw (hCretained hQw) hwalk
      simpa only [Block.compatible, Bool.or_comm] using hQB
  · subst B
    have hQpRetained := hBretained hQp
    rcases actionFGSource_genuineClear_or_selectedG2_named
        S rho w r hQw hCsource with hCgenuine | hCQ
    · obtain ⟨Y, -, -, hwalk, -, -⟩ := hCgenuine
      exact selectedQ2_compatible_genuineSource_pointwise
        S adm hsb hr ready hhor hp hw hQp hQpRetained hwalk
    · subst C
      have hQwRetained := hCretained hQw
      obtain ⟨-, hQpG0⟩ := selectedQ2_g1_g0_at_reader_pointwise
        S adm hsb hr ready hp hw hQp (hQpRetained w hw).1
          (hQpRetained w hw).2.1
      obtain ⟨-, hQwG0⟩ := selectedQ2_g1_g0_at_reader_pointwise
        S adm hsb hr ready hw hw hQw (hQwRetained w hw).1
          (hQwRetained w hw).2.1
      exact graded_oneChain_at_reader S.E
        (readAt S rho (domain S.E S.hc r .g0) w).st.core.toHealing.gradeView
        (readAt S rho (domain S.E S.hc r .g0) w).st.core.F
        S.hc.η_SG r le_rfl
        (by simpa only [storeGrade, phaseGrade] using hQpG0)
        (by simpa only [storeGrade, phaseGrade] using hQwG0)

/-- Same-height named FG sources at honest actions are compatible from the
fully named regime frame. The frame supplies retention only for a source when
that source is the selected Q2; the same-round proof consumes exactly those
two pointwise carriers. -/
theorem actionFGSources_compatible_of_namedFrame
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {r : Round} (ready : GradeRoundReady S rho r)
    {p v : V} (hp : p ∈ rho.honest) (hv : v ∈ rho.honest)
    {Bn Cn : NamedBlock V}
    (hB : nodeFGSource S (actionReadAt S rho p r) r = some Bn.erase)
    (hC : nodeFGSource S (actionReadAt S rho v r) r = some Cn.erase)
    (hBmem : Bn ∈ (actionStoreAt S rho p r).st.bodies)
    (hCmem : Cn ∈ (actionStoreAt S rho v r).st.bodies)
    {stop : Nat} {H : Height} {Prev : NamedBlock V} {c0 : Round}
    (hframe : NamedHeightRegimeFrame S rho H stop Prev c0)
    (hBheight : (Protocol.derive_named S.E S.cfg Bn).h = H + 1)
    (hCheight : (Protocol.derive_named S.E S.cfg Cn).h = H + 1)
    (_hPrevB : NamedBlock.Preceq Prev Bn)
    (_hPrevC : NamedBlock.Preceq Prev Cn)
    (hactionPrefix : strictEventIndex rho (S.a r) ≤ stop)
    (hfrontier : honestHMaxBeforeIndex S rho stop < H + 2)
    (hhor : S.a r ≤ rho.horizon) :
    Block.compatible Bn.erase Cn.erase = true := by
  have _ := hcom
  have hBsource : actionFGSource S
      (actionStoreAt S rho p r) = some Bn.erase := by
    unfold actionFGSource
    dsimp only
    have hround : S.hc.round_of
        (actionStoreAt S rho p r).st.core.toHealing.s = r := by
      simpa only [Protocol.Store.toHealing] using actionStoreAt_round S rho p r
    rw [hround]
    simpa only [nodeFGSource, nodeRead, actionStoreAt] using hB
  have hCsource : actionFGSource S
      (actionStoreAt S rho v r) = some Cn.erase := by
    unfold actionFGSource
    dsimp only
    have hround : S.hc.round_of
        (actionStoreAt S rho v r).st.core.toHealing.s = r := by
      simpa only [Protocol.Store.toHealing] using actionStoreAt_round S rho v r
    rw [hround]
    simpa only [nodeFGSource, nodeRead, actionStoreAt] using hC
  apply actionFGSources_compatible_sameRound_pointwise S adm
    (slashableBound_of_admissible_belowOneThird S adm hbelow)
      ready hp hv hB hC
  · intro hselected
    exact sameRoundSourceQ2Retained_of_namedFrame
      S adm ready hp hselected hBsource hBmem hframe hBheight
        hactionPrefix hfrontier hhor
  · intro hselected
    exact sameRoundSourceQ2Retained_of_namedFrame
      S adm ready hv hselected hCsource hCmem hframe hCheight
        hactionPrefix hfrontier hhor
  · exact hhor


#print axioms sameRoundSourceQ2Retained_of_namedFrame
#print axioms actionFGSources_compatible_sameRound_pointwise
#print axioms actionFGSources_compatible_of_namedFrame

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
