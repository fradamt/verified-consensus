module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryGenuineClearNextVote
public import DecoupledConsensusProofs.Protocol.Grades.RelativeCarrierWindowGateOff
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainNextEntry
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightRegimeFrameBase

@[expose] public section

/-!
# Branch-specific voter-anchor source inputs

The selected-Q2 branch receives its body from the frozen G2-domain read.
Healthy delivery moves that exact named body to each honest G1-domain and
opening-vote read. The height-regime frame then proves that the body remains
in the finality-filtered tree.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Internal.NamedRecoveryRead Protocol
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem actionBody_runBlock_k6
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionStoreAt S rho v r).st.bodies) :
    RunBlock S rho D := by
  have hDpre : D ∈ (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hD
  obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
    S rho adm.toNamedScheduleWellFormed.sorted (S.a r)
  have hDi : D ∈ (rho.stateBefore S i v).st.bodies := by
    change D ∈ (NamedRun.stateBefore S rho i v).st.bodies
    rw [← hi]
    exact hDpre
  exact Proofs.Bridges.runBlock_of_stateBefore_mem S hv hDi


private theorem filtered_at_named_read_of_frame
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {blocked : Height} {stop : Nat} {Tprev : Block V} {c0 : Round}
    (hframe : HeightRegimeFrame S rho blocked stop Tprev c0)
    (hfrontier : honestHMaxBeforeIndex S rho stop < blocked + 2)
    {reader : V} (hreader : reader ∈ rho.honest) {read : Time}
    (hreadPrefix : strictEventIndex rho read ≤ stop)
    {Q : NamedBlock V}
    (hQbody : Q ∈ (NamedRun.stateBeforeTime S rho read reader).st.bodies)
    (hQheight : (Protocol.derive_named S.E S.cfg Q).h = blocked + 1)
    (hTQ : Block.Preceq Tprev Q.erase) :
    Q.erase ∈ Protocol.get_filtered_block_tree
      (NamedRun.stateBeforeTime S rho read reader).st.core.toHealing.toFG := by
  have heq := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedScheduleWellFormed read) reader
  have hbody := hQbody
  rw [heq] at hbody
  have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho
    (strictEventIndex rho read) reader).1.1.1
  have hraw : Q.erase ∈
      (rho.stateBefore S (strictEventIndex rho read) reader).st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hbody
  have hstored :
      ((rho.stateBefore S (strictEventIndex rho read) reader).st.core.σ
        Q.erase).h = blocked + 1 := by
    rw [Proofs.NamedStoreBridge.derivedView_stateBefore S rho
      (strictEventIndex rho read) reader Q hbody, hQheight]
  have hfiltered := hframe.fgRoot_preceq_and_filteredMem
    adm hfrontier hreader hreadPrefix hraw hstored hTQ
  rw [← heq] at hfiltered
  exact hfiltered.2

private theorem filtered_at_named_read_of_frameN
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {blocked : Height} {stop : Nat} {Tprev : NamedBlock V} {c0 : Round}
    (hframe : HeightRegimeFrameN S rho blocked stop Tprev c0)
    (hfrontier : honestHMaxBeforeIndex S rho stop < blocked + 2)
    {reader : V} (hreader : reader ∈ rho.honest) {read : Time}
    (hreadPrefix : strictEventIndex rho read ≤ stop)
    {Q : NamedBlock V}
    (hQbody : Q ∈ (NamedRun.stateBeforeTime S rho read reader).st.bodies)
    (hQheight : (Protocol.derive_named S.E S.cfg Q).h = blocked + 1)
    (hTQ : Block.Preceq Tprev.erase Q.erase) :
    Q.erase ∈ Protocol.get_filtered_block_tree
      (NamedRun.stateBeforeTime S rho read reader).st.core.toHealing.toFG := by
  have heq := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedScheduleWellFormed read) reader
  have hbody := hQbody
  rw [heq] at hbody
  have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho
    (strictEventIndex rho read) reader).1.1.1
  have hraw : Q.erase ∈
      (rho.stateBefore S (strictEventIndex rho read) reader).st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hbody
  have hstored :
      ((rho.stateBefore S (strictEventIndex rho read) reader).st.core.σ
        Q.erase).h = blocked + 1 := by
    rw [Proofs.NamedStoreBridge.derivedView_stateBefore S rho
      (strictEventIndex rho read) reader Q hbody, hQheight]
  have hfiltered := hframe.fgRoot_preceq_and_filteredMem
    adm hfrontier hreader hreadPrefix hraw hstored hTQ
  rw [← heq] at hfiltered
  exact hfiltered.2

/-- The source G0-domain finality is below every block active at an honest
first-interior vote. The one-delay finality relay reaches the anchor reader
before that vote. -/
theorem sourceG0Finalized_preceq_firstInteriorActive
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {r : Round} (ready : GradeRoundReady S rho r)
    (hactionHor : S.a r ≤ rho.horizon)
    {p w : V} (hp : p ∈ rho.honest) (hw : w ∈ rho.honest)
    {L : Block V}
    (hL : L ∈ filteredTree
      (voteDutyRead S rho w (S.hc.opening_slot r + 1))) :
    Block.Preceq
      (readAt S rho (domain S.E S.hc r .g0) p).st.core.F L := by
  let source := domain S.E S.hc r .g0
  let out := source + S.E.Δ
  let vote := Protocol.vote_time S.E (S.hc.opening_slot r + 1)
  have hpost : S.E.t_GST ≤ source := by
    apply ready.1.trans
    dsimp only [source]
    simp only [early, domain, Phase.earlyOffset, Phase.domainOffset]
    linarith [S.E.Δ_pos]
  have houtVote : out ≤ vote := by
    dsimp only [out, source, vote, domain, opening, Phase.domainOffset,
      Protocol.vote_time, Protocol.proposal_time, Env.t, slotStart,
      Protocol.HealConfig.opening_slot]
    push_cast
    nlinarith [S.E.Δ_pos, S.hc.R_ge_three]
  have hvoteHor : vote ≤ rho.horizon := by
    dsimp only [vote]
    exact (next_vote_time_lt_action S r).le.trans hactionHor
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hbelow
  have hrelay : Block.Preceq
      (NamedRun.stateBeforeTime S rho source p).st.core.F
      (NamedRun.stateBeforeTime S rho out w).st.core.F :=
    finalized_preceq_of_evidence_delivered
      S adm hsb hp hw hpost rfl (houtVote.trans hvoteHor)
  have hmono : Block.Preceq
      (NamedRun.stateBeforeTime S rho out w).st.core.F
      (NamedRun.stateBeforeTime S rho vote w).st.core.F := by
    rw [NamedOutageClosure.strict_read_eq_index S rho
        adm.toNamedScheduleWellFormed.sorted out,
      NamedOutageClosure.strict_read_eq_index S rho
        adm.toNamedScheduleWellFormed.sorted vote]
    exact Proofs.NamedRuntime.stateBefore_F_mono S rho w
      (NamedOutageClosure.strict_lengths_mono rho houtVote)
  have hvoteL : Block.Preceq
      (NamedRun.stateBeforeTime S rho vote w).st.core.F L := by
    apply GradeDeliveryRun.finalized_preceq_of_mem_filtered_at_read S rho
    simpa only [filteredTree, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      vote] using hL
  exact Block.preceq_trans hrelay (Block.preceq_trans hmono hvoteL)

#print axioms sourceG0Finalized_preceq_firstInteriorActive

/-- An active prepared voter anchor has an exact named body in the G1-domain
read that formed its cached root. -/
theorem activeVoterAnchor_namedBody_at_g1Domain
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
    ∃ Ln : NamedBlock V, Ln.erase = L ∧
      Ln ∈ (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc r .g1) w).st.bodies ∧ RunBlock S rho Ln := by
  let t := Protocol.vote_time S.E (S.hc.opening_slot r + 1)
  let before := NamedRun.stateBeforeTime S rho t w
  let read := voteDutyRead S rho w (S.hc.opening_slot r + 1)
  let domainRead := readAt S rho (domain S.E S.hc r .g1) w
  have hround : S.hc.round_of (S.E.slotOf t) = r := by
    simpa only [t, Proofs.Optimistic.slotOf_vote_time] using
      Proofs.HealingLemmas.round_of_opening_succ S.hc r
  have hdomainVote : domain S.E S.hc r .g1 < t := by
    dsimp only [t]
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact (Protocol.proposal_time_mono S.E (Nat.le_succ _)).trans_lt
      (Protocol.proposal_time_lt_vote_time S.E _)
  have hvoteAction : t ≤ S.a r := (next_vote_time_lt_action S r).le
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
        some ((storeRoot S.E S.hc domainRead.st r .g1).map
          (fun X => DecoupledConsensusModel.Protocol.clipGrade X
            before.st.core.F)) := by
    simpa only [before, domainRead, storeRoot, phaseRoot, PhaseGrades.readAt] using hbase
  have hprepared := NamedOutageClosure.frame_phase_prepared_eq
    S rho w r .g1 t hround _ hbase'
  have hreadFrame :
      (DecoupledConsensusModel.Protocol.readFrame read.cache
        read.st.core.toHealing r).g1 =
        some ((storeRoot S.E S.hc domainRead.st r .g1).map
          (fun X => DecoupledConsensusModel.Protocol.clipGrade X
            read.st.core.F)) := by
    simpa only [read, before, t, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom] using hprepared
  cases hstore : storeRoot S.E S.hc domainRead.st r .g1 with
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
      have hrawTree : raw ∈ domainRead.st.core.T :=
        (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hstore)).1
      have hLtree : L ∈ domainRead.st.core.T := by
        have hpc := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
          (domain S.E S.hc r .g1) w
        exact Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
          L raw hrawTree hLraw
      obtain ⟨Ln, hLn, hLnErase⟩ :=
        Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
          S rho (domain S.E S.hc r .g1) w (by
            simpa only [domainRead, PhaseGrades.readAt] using hLtree)
      have hLnRun : RunBlock S rho Ln := by
        obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
          S rho adm.toNamedScheduleWellFormed.sorted
            (domain S.E S.hc r .g1)
        apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw
        change Ln ∈ (NamedRun.stateBefore S rho i w).st.bodies
        rw [← hi]
        exact hLn
      exact ⟨Ln, hLnErase, hLn, hLnRun⟩

#print axioms activeVoterAnchor_namedBody_at_g1Domain

/-- The exact named body of an active prepared anchor reaches the source
G0-domain and remains present through the source action read. -/
theorem activeVoterAnchor_namedBody_at_sourceG0_and_action
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {r : Round} (hr : 0 < r) (ready : GradeRoundReady S rho r)
    (hactionHor : S.a r ≤ rho.horizon)
    {p w : V} (hp : p ∈ rho.honest) (hw : w ∈ rho.honest)
    {root L : Block V}
    (hframe :
      (DecoupledConsensusModel.Protocol.readFrame
        (voteDutyRead S rho w (S.hc.opening_slot r + 1)).cache
        (voteDutyRead S rho w
          (S.hc.opening_slot r + 1)).st.core.toHealing r).g1 =
        some (some root))
    (hactive : DecoupledConsensusModel.Protocol.activePrefix
      (filteredTree (voteDutyRead S rho w (S.hc.opening_slot r + 1)))
      root = some L) :
    ∃ Ln : NamedBlock V, Ln.erase = L ∧
      Ln ∈ (readAt S rho (domain S.E S.hc r .g0) p).st.bodies ∧
      Ln ∈ (actionDutyRead S rho p r).st.bodies ∧ RunBlock S rho Ln := by
  obtain ⟨Ln, hLnErase, hLnG1, hLnRun⟩ :=
    activeVoterAnchor_namedBody_at_g1Domain
      S adm hr ready hw hframe hactive
  have hLvote : L ∈ filteredTree
      (voteDutyRead S rho w (S.hc.opening_slot r + 1)) := by
    unfold DecoupledConsensusModel.Protocol.activePrefix at hactive
    exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).1
  have htargetF : Block.Preceq
      (readAt S rho (domain S.E S.hc r .g0) p).st.core.F Ln.erase := by
    rw [hLnErase]
    exact sourceG0Finalized_preceq_firstInteriorActive
      S adm hbelow ready hactionHor hp hw hLvote
  have hpost : S.E.t_GST ≤ domain S.E S.hc r .g1 := by
    apply ready.1.trans
    simp only [early, domain, Phase.earlyOffset, Phase.domainOffset]
    linarith [S.E.Δ_pos]
  have hdeadline :
      max (domain S.E S.hc r .g1) S.E.t_GST + S.E.Δ ≤
        domain S.E S.hc r .g0 := by
    rw [max_eq_left hpost]
    apply le_of_eq
    simp only [domain, Phase.domainOffset]
    ring
  obtain ⟨hLnG0, -, -⟩ :=
    NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
      S rho adm.toNamedAdmissibleCore w hw p hp Ln
        (domain S.E S.hc r .g1) (domain S.E S.hc r .g0)
        (domain S.E S.hc r .g0) hLnG1 hdeadline (le_refl _)
        ready.2 htargetF
  have hdomainAction : domain S.E S.hc r .g0 ≤ S.a r :=
    FrameForward.domain_le_a S r .g0
  have heqG0 := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedScheduleWellFormed (domain S.E S.hc r .g0)) p
  have heqAction := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedScheduleWellFormed (S.a r)) p
  have hLnG0Index := hLnG0
  rw [heqG0] at hLnG0Index
  have hLnAction : Ln ∈
      (NamedRun.stateBeforeTime S rho (S.a r) p).st.bodies := by
    rw [heqAction]
    exact NamedBodyRetention.stateBefore_bodies_mono S rho p
      (strictEventIndex_mono rho hdomainAction) hLnG0Index
  refine ⟨Ln, hLnErase, ?_, ?_, hLnRun⟩
  · simpa only [PhaseGrades.readAt] using hLnG0
  · simpa only [actionDutyRead, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hLnAction

#print axioms activeVoterAnchor_namedBody_at_sourceG0_and_action












/-- A preceding honest action carrier above an active voter anchor reaches the
source G0-domain read and remains present through the source action. This is
the delivery half of the SG-window viability argument; it does not assert the
height needed by `Protocol.viable`. -/
private theorem activeVoterAnchor_carrierBody_at_sourceG0_and_action
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {r : Round} (hr : 0 < r) (ready : GradeRoundReady S rho r)
    (hactionHor : S.a r ≤ rho.horizon)
    {M : Height}
    (hprevFrontier : ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (r - 1))).h_max = M)
    {p w u : V} (hp : p ∈ rho.honest) (hw : w ∈ rho.honest)
    (hu : u ∈ rho.honest) {L : Block V}
    (hLvote : L ∈ filteredTree
      (voteDutyRead S rho w (S.hc.opening_slot r + 1)))
    (hcarrier : Block.Preceq L (actionSGBlockAt S rho u (r - 1))) :
    ∃ W : NamedBlock V,
      Block.Preceq L W.erase ∧
      W ∈ (readAt S rho (domain S.E S.hc r .g0) p).st.bodies ∧
      W ∈ (actionDutyRead S rho p r).st.bodies ∧ RunBlock S rho W ∧
      M - 1 ≤ (Protocol.derive_named S.E S.cfg W).h := by
  obtain ⟨W, hWbody, hcarrierW, hWheight⟩ :=
    actionSGBlockAt_frontierWitness S adm (hprevFrontier u hu)
  have hWsource : W ∈
      (NamedRun.stateBeforeTime S rho (S.a (r - 1)) u).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hWbody
  have hWrun : RunBlock S rho W := by
    obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
      S rho adm.toNamedScheduleWellFormed.sorted (S.a (r - 1))
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hu
    change W ∈ (NamedRun.stateBefore S rho i u).st.bodies
    rw [← hi]
    exact hWsource
  have hdeadline : max (S.a (r - 1)) S.E.t_GST + S.E.Δ ≤
      domain S.E S.hc r .g0 := by
    rcases le_total (S.a (r - 1)) S.E.t_GST with hsourceGST | hGSTsource
    · rw [max_eq_right hsourceGST]
      calc
        S.E.t_GST + S.E.Δ ≤ early S.E S.hc r .g2 + S.E.Δ :=
          Int.add_le_add_right ready.1 S.E.Δ
        _ ≤ domain S.E S.hc r .g0 := by
          simp only [early, domain, Phase.earlyOffset, Phase.domainOffset]
          linarith [S.E.Δ_pos]
    · rw [max_eq_left hGSTsource]
      exact (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
        (Nat.sub_lt hr (by decide))).trans
          ((NamedOutageClosure.early_le_domain S r).trans
            (by simp only [domain, Phase.domainOffset]; linarith [S.E.Δ_pos]))
  have htargetF : Block.Preceq
      (readAt S rho (domain S.E S.hc r .g0) p).st.core.F W.erase := by
    exact Block.preceq_trans
      (sourceG0Finalized_preceq_firstInteriorActive
        S adm hbelow ready hactionHor hp hw hLvote)
      (Block.preceq_trans hcarrier hcarrierW)
  obtain ⟨hWG0, -, -⟩ :=
    NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
      S rho adm.toNamedAdmissibleCore u hu p hp W
        (S.a (r - 1)) (domain S.E S.hc r .g0)
        (domain S.E S.hc r .g0) hWsource hdeadline (le_refl _)
        ready.2 htargetF
  have hdomainAction : domain S.E S.hc r .g0 ≤ S.a r :=
    FrameForward.domain_le_a S r .g0
  have heqG0 := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedScheduleWellFormed (domain S.E S.hc r .g0)) p
  have heqAction := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedScheduleWellFormed (S.a r)) p
  have hWG0Index := hWG0
  rw [heqG0] at hWG0Index
  have hWAction : W ∈
      (NamedRun.stateBeforeTime S rho (S.a r) p).st.bodies := by
    rw [heqAction]
    exact NamedBodyRetention.stateBefore_bodies_mono S rho p
      (strictEventIndex_mono rho hdomainAction) hWG0Index
  refine ⟨W, Block.preceq_trans hcarrier hcarrierW, ?_, ?_, hWrun, hWheight⟩
  · simpa only [PhaseGrades.readAt] using hWG0
  · simpa only [actionDutyRead, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hWAction
/-- A prepared G1 anchor remains viable at the source G0 read and source
action under the fully named height-regime frame. -/
theorem activeVoterAnchor_filtered_at_sourceReads_of_sgWindowNamed
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {r : Round} (hr : 0 < r) (ready : GradeRoundReady S rho r)
    {M : Height}
    (hprevFrontier : ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (r - 1))).h_max = M)
    (hsourceFrontier : ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a r)).h_max = M)
    (hsourceGateOff : ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a r)).h_j + 2 ≤ M)
    {p w : V} (hp : p ∈ rho.honest) (hw : w ∈ rho.honest)
    {stop : Nat} {blocked : Height} {Tprev : NamedBlock V} {c0 : Round}
    (hframe : NamedHeightRegimeFrame S rho blocked stop Tprev c0)
    (hfrontier : honestHMaxBeforeIndex S rho stop < blocked + 2)
    (hactionPrefix : strictEventIndex rho (S.a r) ≤ stop)
    {B : NamedBlock V}
    (hBmem : B ∈ (actionStoreAt S rho p r).st.bodies)
    (hBheight : (Protocol.derive_named S.E S.cfg B).h = blocked + 1)
    (hTB : NamedBlock.Preceq Tprev B)
    (hactionHor : S.a r ≤ rho.horizon)
    (hmajority : Internal.NamedOutageEntry.GradeFormingMajority S rho r)
    (hwindow : RelativeCarrierWindowAt S rho (r - 1) .g1)
    {Ln : NamedBlock V} {L : Block V}
    (hLnErase : Ln.erase = L)
    (hLnG0 : Ln ∈ (readAt S rho (domain S.E S.hc r .g0) p).st.bodies)
    (hLnAction : Ln ∈ (actionDutyRead S rho p r).st.bodies)
    (hLnRun : RunBlock S rho Ln)
    (hgrade : storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc r .g1) w).st r .g1 L = true)
    (hLvote : L ∈ filteredTree
      (voteDutyRead S rho w (S.hc.opening_slot r + 1)))
    (hLB : ¬ Block.Preceq L B.erase) :
    L ∈ filteredTree (readAt S rho (domain S.E S.hc r .g0) p) ∧
      L ∈ filteredTree (actionDutyRead S rho p r) := by
  have hpred : r - 1 + 1 = r :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hr)
  have hmajority' : Internal.NamedOutageEntry.GradeFormingMajority
      S rho (r - 1 + 1) := by
    simpa only [hpred] using hmajority
  have hgrade' : DecoupledConsensusModel.Protocol.gradeBool S.E
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r - 1 + 1) .g1) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r - 1 + 1) .g1) w).st.core.F
      S.hc.η_SG (r - 1 + 1) (early S.E S.hc (r - 1 + 1) .g1)
      (late S.E S.hc (r - 1 + 1) .g1) L = true := by
    simpa only [storeGrade, phaseGrade, PhaseGrades.readAt, hpred] using hgrade
  obtain ⟨u, huVoter, hLcarrier⟩ := relativeGrade_has_roundCarrier
    S adm.toNamedAdmissibleCore hwindow hmajority' hw hgrade'
  have hu : u ∈ rho.honest :=
    ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u (r - 1)).mp huVoter).1
  obtain ⟨W, hLW, hWG0, hWAction, hWrun, hWheight⟩ :=
    activeVoterAnchor_carrierBody_at_sourceG0_and_action
      S adm hbelow hr ready hactionHor hprevFrontier hp hw hu hLvote hLcarrier
  have hBpre : B ∈
      (NamedRun.stateBeforeTime S rho (S.a r) p).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hBmem
  have hBLower : blocked + 1 ≤
      (rho.storeBeforeTime S p (S.a r)).h_max := by
    rw [← hBheight]
    exact Proofs.NamedStoreBridge.heights_le_hMax_stateBeforeTime
      S rho (S.a r) p B hBpre
  have hactionUpper : (rho.storeBeforeTime S p (S.a r)).h_max ≤
      blocked + 1 := by
    have hfrontierLe : honestHMaxBeforeIndex S rho stop ≤ blocked + 1 := by
      exact Nat.lt_succ_iff.mp (by
        simpa only [Nat.add_assoc] using hfrontier)
    rw [storeBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedScheduleWellFormed]
    exact (localHMax_le_honestHMaxBeforeIndex S rho _ hp).trans
      ((honestHMaxBeforeIndex_mono S rho hactionPrefix).trans hfrontierLe)
  have hM : M = blocked + 1 := by
    apply Nat.le_antisymm
    · rw [← hsourceFrontier p hp]
      exact hactionUpper
    · rw [← hsourceFrontier p hp]
      exact hBLower
  have hprevDomain : S.a (r - 1) ≤ domain S.E S.hc r .g0 := by
    exact (NamedOutageClosure.action_le_domain S S.hc.R_ge_three
      (Nat.sub_lt hr (by decide))).trans (by
        simp only [domain, Phase.domainOffset]
        linarith [S.E.Δ_pos])
  have hdomainAction : domain S.E S.hc r .g0 ≤ S.a r :=
    FrameForward.domain_le_a S r .g0
  have hsourceHMax :
      (rho.storeBeforeTime S p (domain S.E S.hc r .g0)).h_max = M := by
    apply Nat.le_antisymm
    · exact (storeBeforeTime_hMax_mono S adm.toNamedScheduleWellFormed p
        hdomainAction).trans_eq (hsourceFrontier p hp)
    · rw [← hprevFrontier p hp]
      exact storeBeforeTime_hMax_mono S adm.toNamedScheduleWellFormed p
        hprevDomain
  have hsourceHJ :
      (rho.storeBeforeTime S p (domain S.E S.hc r .g0)).h_j + 2 ≤ M := by
    have hmono :
        (rho.storeBeforeTime S p (domain S.E S.hc r .g0)).h_j ≤
          (rho.storeBeforeTime S p (S.a r)).h_j := by
      rw [storeBeforeTime_eq_stateBefore_strictEventIndex
          S adm.toNamedScheduleWellFormed,
        storeBeforeTime_eq_stateBefore_strictEventIndex
          S adm.toNamedScheduleWellFormed]
      exact stateBefore_h_j_mono S rho p
        (strictEventIndex_mono rho hdomainAction)
    exact (Nat.add_le_add_right hmono 2).trans (hsourceGateOff p hp)
  have hsourceGate : ¬
      (rho.storeBeforeTime S p (domain S.E S.hc r .g0)).h_max =
        (rho.storeBeforeTime S p (domain S.E S.hc r .g0)).h_j + 1 := by
    intro hgate
    have hEq : M =
        (rho.storeBeforeTime S p (domain S.E S.hc r .g0)).h_j + 1 :=
      hsourceHMax.symm.trans hgate
    rw [hEq] at hsourceHJ
    exact Nat.not_succ_le_self
      ((rho.storeBeforeTime S p (domain S.E S.hc r .g0)).h_j + 1)
      (by simpa only [Nat.add_assoc] using hsourceHJ)
  have hrootSourceL : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S p
          (domain S.E S.hc r .g0)).toHealing.toFG) L := by
    have hFL := sourceG0Finalized_preceq_firstInteriorActive
      S adm hbelow ready hactionHor hp hw hLvote
    simpa only [PhaseGrades.readAt, Protocol.get_fg_root,
      Protocol.Store.toHealing, if_neg hsourceGate] using hFL
  have hrootActionW : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S p (S.a r)).toHealing.toFG) W.erase :=
    frontierRoot_preceq_of_gateOff S adm
      (slashableBound_of_admissible_belowOneThird S adm hbelow) hp
      (X := W.erase) (Xn := W) rfl hWrun hWheight
      (hsourceFrontier p hp) (hsourceGateOff p hp)
  have heqAction := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedScheduleWellFormed (S.a r)) p
  have hBpre' := hBpre
  rw [heqAction] at hBpre'
  have hBfiltered' := hframe.fgRoot_preceq_and_filteredMem
    adm hfrontier hp hactionPrefix hBpre' hBheight hTB
  rw [← heqAction] at hBfiltered'
  have hBfiltered : B.erase ∈ Protocol.get_filtered_block_tree
      (rho.storeBeforeTime S p (S.a r)).toHealing.toFG := by
    simpa only [Run.storeBeforeTime] using hBfiltered'.2
  have hrootActionB : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S p (S.a r)).toHealing.toFG) B.erase :=
    Proofs.Records.preceq_get_fg_root_of_mem_filtered hBfiltered
  have hrootActionL : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S p (S.a r)).toHealing.toFG) L := by
    rcases Block.preceq_linear hrootActionW hLW with hrootL | hLroot
    · exact hrootL
    · exact False.elim (hLB (Block.preceq_trans hLroot hrootActionB))
  have hWActionPre : W ∈
      (rho.storeBeforeTime S p (S.a r)).bodies := by
    simpa only [actionDutyRead, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hWAction
  constructor
  · have hpath := storeBeforeTime_path_mem_filtered_of_band S adm
      (t := domain S.E S.hc r .g0) (v := p) (A := W) (D := Ln)
      hWG0 (by
        change (rho.storeBeforeTime S p
          (domain S.E S.hc r .g0)).h_max - 1 ≤ _
        rw [hsourceHMax]
        exact hWheight)
      (by simpa only [hLnErase] using hrootSourceL)
      (by simpa only [hLnErase] using hLW)
    simpa only [filteredTree, PhaseGrades.readAt, hLnErase] using hpath
  · have hpath := storeBeforeTime_path_mem_filtered_of_band S adm
      (t := S.a r) (v := p) (A := W) (D := Ln)
      hWActionPre (by
        change (rho.storeBeforeTime S p (S.a r)).h_max - 1 ≤ _
        rw [hsourceFrontier p hp]
        exact hWheight)
      (by simpa only [hLnErase] using hrootActionL)
      (by simpa only [hLnErase] using hLW)
    simpa only [filteredTree, actionDutyRead, actionReadAt, hLnErase]
      using hpath

/-- The selected-Q2 branch from the fully named regime frame and the exact
named action source. -/
theorem voterAnchorSourceQ2Inputs_of_namedHeightRegimeFrame_at_source
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (ready : GradeRoundReady S rho r)
    {stop : Nat} {H : Height} {Prev : NamedBlock V} {c0 : Round}
    (hframe : NamedHeightRegimeFrame S rho H stop Prev c0)
    (hactionPrefix : strictEventIndex rho (S.a r) ≤ stop)
    (hfrontier : honestHMaxBeforeIndex S rho stop < H + 2)
    (hactionHor : S.a r ≤ rho.horizon)
    {p : V} (hp : p ∈ rho.honest) (Q : NamedBlock V)
    (hselected : nodeQ2 S (actionReadAt S rho p r) r = some Q.erase)
    (hsource : actionFGSource S (actionStoreAt S rho p r) = some Q.erase)
    (hQmem : Q ∈ (actionStoreAt S rho p r).st.bodies)
    (hQheight : (Protocol.derive_named S.E S.cfg Q).h = H + 1) :
    VoterAnchorSourceQ2Inputs S rho r p Q.erase := by
  have hPrevQ : NamedBlock.Preceq Prev Q :=
    hframe.sourceAbove p hp r hactionPrefix hactionHor Q hQmem
      hsource hQheight
  have hPrevQErase : Block.Preceq Prev.erase Q.erase :=
    Proofs.NamedWire.erase_preceq hPrevQ
  have hQrun : RunBlock S rho Q := actionBody_runBlock_k6 S adm hp hQmem
  have hfloor : FinalityFloorAt S rho H stop Prev.erase := by
    intro v hv n hn X hXrun hXheight hPrevX
    exact hframe.floor v hv n hn X hXrun hXheight
      (Protocol.namedPreceq_of_runBlock_erase_preceq
        adm hframe.prevRun hXrun hPrevX)
  have hQsource : Q ∈ (NamedRun.stateBeforeTime S rho
      (domain S.E S.hc r .g2) p).st.bodies :=
    selectedQ2_body_at_capture S adm hp hselected hQmem
  refine ⟨?_, ?_⟩
  · intro w hw
    have hdomainAction : domain S.E S.hc r .g1 ≤ S.a r := by
      rw [NamedOutageClosure.domain_g1_eq_opening]
      exact (Protocol.proposal_time_lt_vote_time S.E _).le.trans
        ((Protocol.vote_time_le_confirmation_time S.E _).trans
          (by rw [opening_confirmation_time_eq_action]))
    have hdomainPrefix :
        strictEventIndex rho (domain S.E S.hc r .g1) ≤ stop :=
      (strictEventIndex_mono rho hdomainAction).trans hactionPrefix
    have htargetFQ : Block.Preceq
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc r .g1) w).st.core.F Q.erase := by
      rw [congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
        S adm.toNamedScheduleWellFormed (domain S.E S.hc r .g1)) w]
      exact hframe.floor w hw _ hdomainPrefix Q hQrun
        (by rw [hQheight]; exact Nat.le_succ H) hPrevQ
    have hpost : S.E.t_GST ≤ domain S.E S.hc r .g2 :=
      ready.1.trans (NamedOutageClosure.early_le_domain S r)
    have hdeadline :
        max (domain S.E S.hc r .g2) S.E.t_GST + S.E.Δ ≤
          domain S.E S.hc r .g1 := by
      rw [max_eq_left hpost]
      apply le_of_eq
      simp only [domain, Phase.domainOffset]
      ring
    have hg1Hor : domain S.E S.hc r .g1 ≤ rho.horizon := by
      have hle : domain S.E S.hc r .g1 ≤ domain S.E S.hc r .g0 := by
        simp only [domain, Phase.domainOffset]
        linarith [S.E.Δ_pos]
      exact hle.trans ready.2
    obtain ⟨hbody, -, -⟩ :=
      NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
        S rho adm.toNamedAdmissibleCore p hp w hw Q
          (domain S.E S.hc r .g2) (domain S.E S.hc r .g1)
          (domain S.E S.hc r .g1) hQsource hdeadline (le_refl _)
          hg1Hor htargetFQ
    have heq := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedScheduleWellFormed (domain S.E S.hc r .g1)) w
    have hbody' := hbody
    rw [heq] at hbody'
    have hfiltered := hframe.fgRoot_preceq_and_filteredMem
      adm hfrontier hw hdomainPrefix hbody' hQheight hPrevQ
    rw [← heq] at hfiltered
    simpa only [filteredTree, PhaseGrades.readAt] using hfiltered.2
  · intro w hw
    let vote := Protocol.vote_time S.E (S.hc.opening_slot r)
    have hbodies := selectedQ2_body_at_action_and_openingVote_of_floor
      S adm ready hp hselected hQmem hfloor hQheight hPrevQErase
        hactionPrefix hw
    have hvoteAction : vote ≤ S.a r := by
      dsimp only [vote]
      exact (Protocol.vote_time_le_confirmation_time S.E _).trans
        (by rw [opening_confirmation_time_eq_action])
    have hvotePrefix : strictEventIndex rho vote ≤ stop :=
      (strictEventIndex_mono rho hvoteAction).trans hactionPrefix
    have hbody : Q ∈
        (NamedRun.stateBeforeTime S rho vote w).st.bodies := by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, Protocol.NamedStore.setClock,
        vote] using hbodies.2
    have heq := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedScheduleWellFormed vote) w
    have hbody' := hbody
    rw [heq] at hbody'
    have hfiltered := hframe.fgRoot_preceq_and_filteredMem
      adm hfrontier hw hvotePrefix hbody' hQheight hPrevQ
    rw [← heq] at hfiltered
    simpa only [filteredTree, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      vote] using hfiltered.2

#print axioms voterAnchorSourceQ2Inputs_of_namedHeightRegimeFrame_at_source


/-- The selected-Q2 branch supplies exactly the two reads that consume it. -/
theorem voterAnchorSourceQ2Inputs_of_frame
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (ready : GradeRoundReady S rho r)
    {p : V} (hp : p ∈ rho.honest) {Q : NamedBlock V}
    (hselected : nodeQ2 S (actionReadAt S rho p r) r = some Q.erase)
    (hQmem : Q ∈ (actionStoreAt S rho p r).st.bodies)
    {stop : Nat} {blocked : Height} {Tprev : Block V} {c0 : Round}
    (hframe : HeightRegimeFrame S rho blocked stop Tprev c0)
    (hQheight : (Protocol.derive_named S.E S.cfg Q).h = blocked + 1)
    (hTQ : Block.Preceq Tprev Q.erase)
    (hactionPrefix : strictEventIndex rho (S.a r) ≤ stop)
    (hfrontier : honestHMaxBeforeIndex S rho stop < blocked + 2) :
    VoterAnchorSourceQ2Inputs S rho r p Q.erase := by
  have hQrun : RunBlock S rho Q := actionBody_runBlock_k6 S adm hp hQmem
  have hQsource : Q ∈ (NamedRun.stateBeforeTime S rho
      (domain S.E S.hc r .g2) p).st.bodies :=
    selectedQ2_body_at_capture S adm hp hselected hQmem
  refine ⟨?_, ?_⟩
  · intro w hw
    have hdomainAction : domain S.E S.hc r .g1 ≤ S.a r := by
      rw [NamedOutageClosure.domain_g1_eq_opening]
      exact (Protocol.proposal_time_lt_vote_time S.E _).le.trans
        ((Protocol.vote_time_le_confirmation_time S.E _).trans
          (by rw [opening_confirmation_time_eq_action]))
    have hdomainPrefix :
        strictEventIndex rho (domain S.E S.hc r .g1) ≤ stop :=
      (strictEventIndex_mono rho hdomainAction).trans hactionPrefix
    have htargetFQ : Block.Preceq
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc r .g1) w).st.core.F Q.erase := by
      rw [congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
        S adm.toNamedScheduleWellFormed (domain S.E S.hc r .g1)) w]
      exact hframe.floor.storeF_preceq_sourceHeightBlock
        hw hdomainPrefix hQrun hQheight hTQ
    have hpost : S.E.t_GST ≤ domain S.E S.hc r .g2 :=
      ready.1.trans (NamedOutageClosure.early_le_domain S r)
    have hdeadline :
        max (domain S.E S.hc r .g2) S.E.t_GST + S.E.Δ ≤
          domain S.E S.hc r .g1 := by
      rw [max_eq_left hpost]
      apply le_of_eq
      simp only [domain, Phase.domainOffset]
      ring
    have hg1Hor : domain S.E S.hc r .g1 ≤ rho.horizon := by
      have hle : domain S.E S.hc r .g1 ≤ domain S.E S.hc r .g0 := by
        simp only [domain, Phase.domainOffset]
        linarith [S.E.Δ_pos]
      exact hle.trans ready.2
    obtain ⟨hbody, -, -⟩ :=
      NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
        S rho adm.toNamedAdmissibleCore p hp w hw Q
          (domain S.E S.hc r .g2) (domain S.E S.hc r .g1)
          (domain S.E S.hc r .g1) hQsource hdeadline (le_refl _)
          hg1Hor htargetFQ
    exact filtered_at_named_read_of_frame S adm hframe hfrontier hw
      hdomainPrefix hbody hQheight hTQ
  · intro w hw
    let vote := Protocol.vote_time S.E (S.hc.opening_slot r)
    have hbodies := selectedQ2_body_at_action_and_openingVote_of_floor
      S adm ready hp hselected hQmem hframe.floor hQheight hTQ
        hactionPrefix hw
    have hvoteAction : vote ≤ S.a r := by
      dsimp only [vote]
      exact (Protocol.vote_time_le_confirmation_time S.E _).trans
        (by rw [opening_confirmation_time_eq_action])
    have hvotePrefix : strictEventIndex rho vote ≤ stop :=
      (strictEventIndex_mono rho hvoteAction).trans hactionPrefix
    have hbody : Q ∈
        (NamedRun.stateBeforeTime S rho vote w).st.bodies := by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, Protocol.NamedStore.setClock,
        vote] using hbodies.2
    have hfiltered := filtered_at_named_read_of_frame
      S adm hframe hfrontier hw hvotePrefix hbody hQheight hTQ
    simpa only [filteredTree, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      vote] using hfiltered

/-- The selected-Q2 branch with a named predecessor frame. -/
theorem voterAnchorSourceQ2Inputs_of_frameN
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (ready : GradeRoundReady S rho r)
    {p : V} (hp : p ∈ rho.honest) {Q : NamedBlock V}
    (hselected : nodeQ2 S (actionReadAt S rho p r) r = some Q.erase)
    (hQmem : Q ∈ (actionStoreAt S rho p r).st.bodies)
    {stop : Nat} {blocked : Height} {Tprev : NamedBlock V} {c0 : Round}
    (hframe : HeightRegimeFrameN S rho blocked stop Tprev c0)
    (hQheight : (Protocol.derive_named S.E S.cfg Q).h = blocked + 1)
    (hTQ : Block.Preceq Tprev.erase Q.erase)
    (hactionPrefix : strictEventIndex rho (S.a r) ≤ stop)
    (hfrontier : honestHMaxBeforeIndex S rho stop < blocked + 2) :
    VoterAnchorSourceQ2Inputs S rho r p Q.erase := by
  have hQrun : RunBlock S rho Q := actionBody_runBlock_k6 S adm hp hQmem
  have hQsource : Q ∈ (NamedRun.stateBeforeTime S rho
      (domain S.E S.hc r .g2) p).st.bodies :=
    selectedQ2_body_at_capture S adm hp hselected hQmem
  refine ⟨?_, ?_⟩
  · intro w hw
    have hdomainAction : domain S.E S.hc r .g1 ≤ S.a r := by
      rw [NamedOutageClosure.domain_g1_eq_opening]
      exact (Protocol.proposal_time_lt_vote_time S.E _).le.trans
        ((Protocol.vote_time_le_confirmation_time S.E _).trans
          (by rw [opening_confirmation_time_eq_action]))
    have hdomainPrefix :
        strictEventIndex rho (domain S.E S.hc r .g1) ≤ stop :=
      (strictEventIndex_mono rho hdomainAction).trans hactionPrefix
    have htargetFQ : Block.Preceq
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc r .g1) w).st.core.F Q.erase := by
      rw [congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
        S adm.toNamedScheduleWellFormed (domain S.E S.hc r .g1)) w]
      exact hframe.floor.storeF_preceq_sourceHeightBlock
        hw hdomainPrefix hQrun hQheight hTQ
    have hpost : S.E.t_GST ≤ domain S.E S.hc r .g2 :=
      ready.1.trans (NamedOutageClosure.early_le_domain S r)
    have hdeadline :
        max (domain S.E S.hc r .g2) S.E.t_GST + S.E.Δ ≤
          domain S.E S.hc r .g1 := by
      rw [max_eq_left hpost]
      apply le_of_eq
      simp only [domain, Phase.domainOffset]
      ring
    have hg1Hor : domain S.E S.hc r .g1 ≤ rho.horizon := by
      have hle : domain S.E S.hc r .g1 ≤ domain S.E S.hc r .g0 := by
        simp only [domain, Phase.domainOffset]
        linarith [S.E.Δ_pos]
      exact hle.trans ready.2
    obtain ⟨hbody, -, -⟩ :=
      NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
        S rho adm.toNamedAdmissibleCore p hp w hw Q
          (domain S.E S.hc r .g2) (domain S.E S.hc r .g1)
          (domain S.E S.hc r .g1) hQsource hdeadline (le_refl _)
          hg1Hor htargetFQ
    exact filtered_at_named_read_of_frameN S adm hframe hfrontier hw
      hdomainPrefix hbody hQheight hTQ
  · intro w hw
    let vote := Protocol.vote_time S.E (S.hc.opening_slot r)
    have hbodies := selectedQ2_body_at_action_and_openingVote_of_floor
      S adm ready hp hselected hQmem hframe.floor hQheight hTQ
        hactionPrefix hw
    have hvoteAction : vote ≤ S.a r := by
      dsimp only [vote]
      exact (Protocol.vote_time_le_confirmation_time S.E _).trans
        (by rw [opening_confirmation_time_eq_action])
    have hvotePrefix : strictEventIndex rho vote ≤ stop :=
      (strictEventIndex_mono rho hvoteAction).trans hactionPrefix
    have hbody : Q ∈
        (NamedRun.stateBeforeTime S rho vote w).st.bodies := by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, Protocol.NamedStore.setClock,
        vote] using hbodies.2
    have hfiltered := filtered_at_named_read_of_frameN
      S adm hframe hfrontier hw hvotePrefix hbody hQheight hTQ
    simpa only [filteredTree, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      vote] using hfiltered








end HealingSurface
end Proofs
end DecoupledConsensusModel

end
