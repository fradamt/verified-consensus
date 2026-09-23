module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGTargetCanonicality
public import DecoupledConsensusProofs.Protocol.Grades.SGTargetCanonicalityQuiet
public import DecoupledConsensusProofs.Protocol.StoreBase.RecoverySelectedG2ReadVisibility
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryGenuineClearNextVote
public import DecoupledConsensusProofs.Protocol.Grades.RelativeCrossReader
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.GoldfishCone

@[expose] public section

/-!
# Fixed-root SG-target canonicality

This file derives the Claim-1 target cone directly from a common grade, exact
FG-root reads, and one-step local height caps. It does not construct the
stronger `SGTargetCanonicalityBase` interface.
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




private theorem fixedRoot_runBlock_unique_of_erase_eq
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {A B : NamedBlock V} (hA : RunBlock S rho A) (hB : RunBlock S rho B)
    (herase : A.erase = B.erase) : A = B :=
  adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective A B hA hB A B
    (Or.inl (Proofs.NamedAncestry.named_self A)) (Or.inr (Proofs.NamedAncestry.named_self B))
    (by rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root B, herase])

private theorem fixedRoot_runBlock_of_body_at_read
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {read : Time} {B : NamedBlock V}
    (hB : B ∈ (rho.storeBeforeTime S w read).bodies) :
    RunBlock S rho B := by
  obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted read
  apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw
  have hB' := hB
  change B ∈ (NamedRun.stateBeforeTime S rho read w).st.bodies at hB'
  rw [congrFun hi w] at hB'
  exact hB'

private theorem fixedRoot_selectedQ2_body_at_capture
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {p : V} (hp : p ∈ rho.honest) {Q : Block V}
    (hselected : PhaseGrades.nodeQ2 S (actionReadAt S rho p r) r = some Q) :
    ∃ Qn : NamedBlock V,
      Qn ∈ (rho.storeBeforeTime S p
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)).bodies ∧
      Qn.erase = Q ∧ RunBlock S rho Qn := by
  have hQaction : Q ∈ (actionStoreAt S rho p r).st.core.T :=
    mem_T_of_mem_filteredTree (actionQ2_mem_filteredTree S rho p r hselected)
  obtain ⟨Qn, hQnAction, hQnErase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho (S.a r) p (by
      simpa only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
        NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hQaction)
  have hQnRun := fixedRoot_runBlock_of_body_at_read S adm hp hQnAction
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
        some Qn.erase := by
    simpa only [i, hQnErase] using hselected0
  obtain ⟨j, raw, -, hj, hfreeze, hQraw⟩ :=
    contractQ2_capture_at_action_index S rho i p r hselected'
  have hrawTree : raw ∈ (rho.stateBefore S j p).st.core.T :=
    (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hfreeze)).1
  have hQTree : Qn.erase ∈ (rho.stateBefore S j p).st.core.T := by
    have hpc := Proofs.NamedStoreBridge.parentClosed_stateBefore S rho j p
    exact Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
      Qn.erase raw hrawTree hQraw
  obtain ⟨D, hD, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho j p hQTree
  have hDrun : RunBlock S rho D :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hp hD
  have hDQ : D = Qn := fixedRoot_runBlock_unique_of_erase_eq
    adm hDrun hQnRun (hDerase.trans rfl)
  have hjState := Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hj
  subst D
  rw [hjState] at hD
  exact ⟨Qn, hD, hQnErase, hQnRun⟩

private theorem fixedRoot_selectedQ2_preceq_voterHead_of_rawDomain
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    {r : Round} (hr : 0 < r) {p w : V}
    (hp : p ∈ rho.honest) (hw : w ∈ rho.honest) {Q : Block V}
    (hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho p r) r = some Q)
    {s : Slot} (hround : S.hc.round_of s = r)
    (hread : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 <
      Protocol.vote_time S.E s)
    (hnext : Protocol.vote_time S.E s ≤
      DecoupledConsensusModel.Protocol.opening S.E S.hc (r + 1))
    (hhor : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 ≤ rho.horizon)
    (hQdomain : Q ∈ (rho.storeBeforeTime S w
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)).core.T)
    (hgrade : PhaseGrades.storeGrade S.E S.hc
      (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st r .g1 Q = true)
    (hQread : Q ∈ PhaseGrades.filteredTree
      (PhaseGrades.readAt S rho (Protocol.vote_time S.E s) w)) :
    Block.Preceq Q (voterHeadAt S rho w s) := by
  let t := Protocol.vote_time S.E s
  let before := NamedRun.stateBeforeTime S rho t w
  let read := NamedActionReads.confirmationReadFrom S before t
  let domainRead := NamedRun.stateBeforeTime S rho
    (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w
  have hround' : S.hc.round_of (S.E.slotOf t) = r := by
    simpa only [t, Proofs.Optimistic.slotOf_vote_time] using hround
  have hgrade' : DecoupledConsensusModel.Protocol.gradeBool S.E
      domainRead.st.core.toHealing.gradeView domainRead.st.core.F
      S.hc.η_SG r (DecoupledConsensusModel.Protocol.early S.E S.hc r .g1)
      (DecoupledConsensusModel.Protocol.late S.E S.hc r .g1) Q = true := by
    simpa only [PhaseGrades.storeGrade, PhaseGrades.phaseGrade,
      domainRead, PhaseGrades.readAt] using hgrade
  obtain ⟨raw, hraw, hQraw⟩ :=
    NamedOutageClosure.q10_freeze_of_graded S.E
      domainRead.st.core.toHealing.gradeView domainRead.st.core.F
      S.hc.η_SG r (NamedOutageClosure.q10_early_le_late S r .g1)
      (by simpa only [domainRead] using hQdomain) hgrade'
  have hQread' : Q ∈ Protocol.get_filtered_block_tree
      before.st.core.toHealing.toFG := by
    simpa only [before, t, PhaseGrades.filteredTree,
      PhaseGrades.readAt] using hQread
  have hFQ : Block.Preceq before.st.core.F Q :=
    NamedOutageClosure.q10_filtered_F hQread'
  have hQclip : Block.Preceq Q
      (DecoupledConsensusModel.Protocol.clipGrade raw before.st.core.F) := by
    apply (NamedOutageClosure.q10_retained_prefix raw before.st.core.F Q (by
      simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr hFQ)).mpr
    exact hQraw
  have hframe := FrameCompleted.frame_phase_completed_in_round
    S rho core w hw r hr .g1 t hread hnext hhor
  have hframe' :
      (DecoupledConsensusModel.Protocol.readFrame before.cache
        before.st.core.toHealing r).g1 =
        some ((PhaseGrades.storeRoot S.E S.hc domainRead.st r .g1).map
          (fun X => DecoupledConsensusModel.Protocol.clipGrade X before.st.core.F)) := by
    simpa only [before, domainRead, PhaseGrades.storeRoot,
      PhaseGrades.phaseRoot] using hframe
  have hbase :
      (DecoupledConsensusModel.Protocol.readFrame before.cache
        before.st.core.toHealing r).g1 =
        some (some (DecoupledConsensusModel.Protocol.clipGrade raw before.st.core.F)) := by
    simpa only [PhaseGrades.storeRoot, PhaseGrades.phaseRoot, hraw,
      Option.map_some] using hframe'
  have hprepared := NamedOutageClosure.frame_phase_prepared_eq S rho w r
    .g1 t hround' (some (DecoupledConsensusModel.Protocol.clipGrade raw before.st.core.F))
    hbase
  let n := Internal.NamedRecoveryRead.voteDutyRead S rho w s
  have hroundVote : S.hc.round_of n.st.core.s = r := by
    simpa only [n, Proofs.Optimistic.voteDutyRead_slot] using hround
  have hframeVote :
      (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing
        (S.hc.round_of n.st.core.s)).g1 =
        some (some (DecoupledConsensusModel.Protocol.clipGrade raw before.st.core.F)) := by
    simpa only [DecoupledConsensusModel.Protocol.phaseResult, n, hroundVote, hround', read, before, t,
      Internal.NamedRecoveryRead.voteDutyRead,
      Internal.NamedOutageEntry.confirmationReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hprepared
  have hactiveVote : Q ∈ Protocol.get_filtered_block_tree
      n.st.core.toHealing.toFG := by
    simpa only [n, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, PhaseGrades.filteredTree,
      PhaseGrades.readAt] using hQread
  have hanchorQ : Block.Preceq Q (voterAnchorAt S rho w s) := by
    change Block.Preceq Q
      (DecoupledConsensusModel.Protocol.anchor S.E S.hc n.st.core.toHealing
        (S.hc.round_of n.st.core.s)
        (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing
          (S.hc.round_of n.st.core.s)).g1)
    rw [hframeVote]
    obtain ⟨A, hA, hQA⟩ := NamedOutageClosure.q10_activePrefix_dominates
      hactiveVote hQclip
    simp only [DecoupledConsensusModel.Protocol.anchor, hA, Option.getD_some]
    exact hQA
  exact NamedOutageClosure.preceq_voteDutyHead_of_preceq_voteDutyAnchor
    S rho w s hanchorQ

private theorem fixedRoot_strict_finality_mono
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    (w : V) {c d : Time} (hcd : c ≤ d) :
    Block.Preceq (rho.storeBeforeTime S w c).core.F
      (rho.storeBeforeTime S w d).core.F := by
  let ic := strictEventIndex rho c
  let id := strictEventIndex rho d
  have hc : rho.storeBeforeTime S w c = (rho.stateBefore S ic w).st := by
    unfold Run.storeBeforeTime
    exact congrArg NamedNodeState.st
      (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S sch c) w)
  have hd : rho.storeBeforeTime S w d = (rho.stateBefore S id w).st := by
    unfold Run.storeBeforeTime
    exact congrArg NamedNodeState.st
      (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S sch d) w)
  rw [hc, hd]
  exact Protocol.stateBefore_F_mono S rho w
    (by simpa only [ic, id] using strictEventIndex_mono rho hcd)

private theorem fixedRoot_voteTime_lt_nextProposal
    (E : Env V) (s : Slot) :
    Protocol.vote_time E s < Protocol.proposal_time E (s + 1) := by
  simp only [Protocol.vote_time, Protocol.proposal_time, Env.t, slotStart]
  push_cast
  nlinarith [E.Δ_pos]

/-- A prepared selected Q2 has an honest-vote cone at every supplied interior
duty under the exact named root and one-step height cap. -/
theorem honestVotesCone_of_selectedActionG2_exactFGRoot_heightCap
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {r : Round} (hr : 0 < r) (ready : GradeRoundReady S rho r)
    {J : NamedBlock V} (hJrun : RunBlock S rho J)
    {u : V} (hu : u ∈ rho.honest) {Q : Block V}
    (hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho u r) r = some Q)
    {s : Slot} (hslo : S.hc.opening_slot r + 1 ≤ s)
    (hshi : s < S.hc.opening_slot (r + 1))
    (hhor : Protocol.vote_time S.E s ≤ rho.horizon)
    (hactionRoot : ∀ w ∈ rho.honest,
      Protocol.get_fg_root
        (actionStoreAt S rho w r).st.core.toHealing.toFG = J.erase)
    (hvoteRoot : ∀ w ∈ rho.honest,
      Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w s).st.core.toHealing.toFG =
          J.erase)
    (hvoteCap : ∀ w ∈ rho.honest,
      (Internal.NamedRecoveryRead.voteDutyRead S rho w s).st.core.h_max ≤
        (Protocol.derive_named S.E S.cfg J).h + 1) :
    NamedHonestVotesCone S rho s (fun X => Block.Preceq Q X) := by
  have hs : 0 < s := lt_of_lt_of_le (Nat.zero_lt_succ _) hslo
  have hround : S.hc.round_of s = r :=
    round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc hslo hshi
  have hread : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 <
      Protocol.vote_time S.E s := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact (Protocol.proposal_time_lt_vote_time S.E
      (S.hc.opening_slot r)).trans_le
        (Protocol.vote_time_mono_slots S.E
          (le_trans (Nat.le_succ _) hslo))
  have hnext : Protocol.vote_time S.E s ≤
      DecoupledConsensusModel.Protocol.opening S.E S.hc (r + 1) := by
    exact (fixedRoot_voteTime_lt_nextProposal S.E s).le.trans
      (Protocol.proposal_time_mono S.E
        (Nat.succ_le_iff.mpr hshi))
  have hdomainHor : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 ≤ rho.horizon :=
    hread.le.trans hhor
  have hJQ : Block.Preceq J.erase Q := by
    rw [← hactionRoot u hu]
    exact Proofs.Records.preceq_get_fg_root_of_mem_filtered
      (actionQ2_mem_filteredTree S rho u r hQ)
  obtain ⟨Qn, hQsource, hQnErase, hQnRun⟩ :=
    fixedRoot_selectedQ2_body_at_capture S adm hu hQ
  have hpostSource : S.E.t_GST ≤ DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2 :=
    ready.1.trans (NamedOutageClosure.early_le_domain S r)
  have hdeadline :
      max (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) S.E.t_GST + S.E.Δ ≤
        DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 := by
    rw [max_eq_left hpostSource]
    apply le_of_eq
    simp only [DecoupledConsensusModel.Protocol.domain, DecoupledConsensusModel.Protocol.Phase.domainOffset]
    ring
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  intro w hw hcommittee
  have hFvoteJ : Block.Preceq
      (rho.storeBeforeTime S w (Protocol.vote_time S.E s)).core.F J.erase := by
    have hFroot := Proofs.Records.preceq_get_fg_root_of_F
      (st := (rho.storeBeforeTime S w
        (Protocol.vote_time S.E s)).core.toHealing.toFG)
      (Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        S rho (Protocol.vote_time S.E s) w)
    have hrootStrict : Protocol.get_fg_root
        (rho.storeBeforeTime S w
          (Protocol.vote_time S.E s)).core.toHealing.toFG = J.erase := by
      simpa only [Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
        using hvoteRoot w hw
    rw [hrootStrict] at hFroot
    exact hFroot
  have hFg1J : Block.Preceq
      (rho.storeBeforeTime S w
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)).core.F J.erase :=
    Block.preceq_trans
      (fixedRoot_strict_finality_mono S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed w hread.le)
      hFvoteJ
  have hFg1Q : Block.Preceq
      (rho.storeBeforeTime S w
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)).core.F Q :=
    Block.preceq_trans hFg1J hJQ
  have hQatG1 := NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
    S rho adm.toNamedAdmissibleCore u hu w hw Qn
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) hQsource hdeadline
      (le_refl _) hdomainHor (by simpa only [hQnErase] using hFg1Q)
  have hforward : ∀ sender x root H,
      x ∈ DecoupledConsensusModel.Protocol.interpretedInputs
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) u).st.core.toHealing.gradeView
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) u).st.core.F
        S.hc.η_SG r (DecoupledConsensusModel.Protocol.early S.E S.hc r .g2) sender →
      DecoupledConsensusModel.Protocol.localCovers
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) u).st.core.toHealing.gradeView
        x.confirmed Q = true →
      x.confirmed = some root →
      Block.find? (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) u).st.core.T root = some H →
      Block.Preceq (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.F H := by
    intro sender x root H _ hcover hconf hfind
    exact Block.preceq_trans (by simpa only [PhaseGrades.readAt] using hFg1Q) (by
      unfold DecoupledConsensusModel.Protocol.localCovers at hcover
      unfold Protocol.head_covers at hcover
      simp only [Protocol.HealingStore.gradeView, Protocol.Store.toHealing, hconf]
        at hcover
      rw [hfind] at hcover
      exact hcover)
  have hbelow := crossReaderFinalizedBelow_of_finalitySafety_and_relay
    S adm hsb ready.1 ready.2 hu hw hforward
  have hguard := crossReaderBodyReadyGuard_of_finalizedBelow
    S adm.toNamedAdmissibleCore hr ready.1 ready.2 hu hw hbelow
  have hG2 := selectedQ2_storeGrade_at_g2Domain S adm hQ
  have hG1 := storeGrade_g1_of_storeGrade_g2_cross_reader
    S rho adm.toNamedAdmissibleCore r
      (twoCutoffDelivery_of_core S adm.toNamedAdmissibleCore ready.1)
      ready.2 u w hu hw Q hG2 hguard
  have hQvote := NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
    S rho adm.toNamedAdmissibleCore u hu w hw Qn
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)
      (Protocol.vote_time S.E s) hQsource hdeadline hread.le hdomainHor
      (by simpa only [hQnErase] using Block.preceq_trans hFvoteJ hJQ)
  obtain ⟨Jn, hJnQ, hJnErase⟩ :=
    Proofs.NamedAncestry.erased_ancestor_lift Qn (by simpa only [hQnErase] using hJQ)
  have hJnRun := Proofs.NamedRuntime.blockInRun_of_ancestor S rho hQnRun hJnQ
  have hJnEq : Jn = J := fixedRoot_runBlock_unique_of_erase_eq
    adm hJnRun hJrun (hJnErase.trans rfl)
  have hheight : (Protocol.derive_named S.E S.cfg J).h ≤
      (Protocol.derive_named S.E S.cfg Qn).h := by
    rw [← hJnEq]
    exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hJnQ
  have hQfiltered : Q ∈ PhaseGrades.filteredTree
      (PhaseGrades.readAt S rho (Protocol.vote_time S.E s) w) := by
    apply mem_filtered_of_mem_tree_of_exactFGRoot_heightCap
      S rho w (Protocol.vote_time S.E s) hQvote.1 hQnErase
    · simpa only [Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
        using hvoteRoot w hw
    · exact hJQ
    · exact (by
        have hcap := hvoteCap w hw
        simpa only [Internal.NamedRecoveryRead.voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
          using hcap.trans (Nat.add_le_add_right hheight 1))
  have hQhead := fixedRoot_selectedQ2_preceq_voterHead_of_rawDomain
    S adm.toNamedAdmissibleCore hr hu hw hQ hround hread hnext hdomainHor
      (by
        have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).1.1.1
        change Q ∈ (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.T
        rw [hcoh.1]
        simpa only [hQnErase] using
          Finset.mem_image_of_mem NamedBlock.erase hQatG1.1)
      hG1 hQfiltered
  obtain ⟨X, hXerase, hXrun, hXemit⟩ :=
    named_voter_head_emits S adm hw hs hcommittee hhor
  exact ⟨X, by simpa only [hXerase] using hQhead, hXrun, hXemit⟩


omit [Fintype V] in
private theorem fixedRoot_localCovers_mono
    {A B : Block V} {gv : Protocol.GradeView V} {key : Option BlockId}
    (hAB : Block.Preceq A B)
    (hB : DecoupledConsensusModel.Protocol.localCovers gv key B = true) :
    DecoupledConsensusModel.Protocol.localCovers gv key A = true := by
  unfold DecoupledConsensusModel.Protocol.localCovers at hB ⊢
  unfold Protocol.head_covers at hB ⊢
  cases key with
  | none => exact hB
  | some root =>
      dsimp only at hB ⊢
      cases hfind : Block.find? gv.T root with
      | none => rw [hfind] at hB; exact absurd hB (by simp)
      | some head =>
          rw [hfind] at hB
          exact Block.preceq_trans hAB hB

omit [Fintype V] in
private theorem fixedRoot_positive_mono
    {A B : Block V} (hAB : Block.Preceq A B)
    (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    (early late : Time) (v : V)
    (hB : DecoupledConsensusModel.Protocol.positive gv F eta r early late v B = true) :
    DecoupledConsensusModel.Protocol.positive gv F eta r early late v A = true := by
  simp only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq] at hB ⊢
  rcases hB with ⟨u, hu, hmax, hcov, hclean, hlate⟩
  refine ⟨u, hu, hmax, fixedRoot_localCovers_mono hAB hcov, hclean, ?_⟩
  intro x hx hlt
  exact fixedRoot_localCovers_mono hAB (hlate x hx hlt)

omit [Fintype V] in
private theorem fixedRoot_opposing_mono
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
    exact hnot (fixedRoot_localCovers_mono hAB hcov)
  · exact Or.inr ⟨x, hx, y, hy, hmax, heq, hkey⟩

private theorem fixedRoot_phaseGrade_mono
    (E : Env V) (hc : Protocol.HealConfig) (gv : Protocol.GradeView V)
    (F : Block V) (r : Round) (phase : DecoupledConsensusModel.Protocol.Phase)
    {A B : Block V}
    (hAB : Block.Preceq A B)
    (hB : PhaseGrades.phaseGrade E hc gv F r phase B = true) :
    PhaseGrades.phaseGrade E hc gv F r phase A = true := by
  simp only [PhaseGrades.phaseGrade, DecoupledConsensusModel.Protocol.gradeBool,
    decide_eq_true_eq] at hB ⊢
  have hOpp : (Finset.univ.filter fun v =>
      DecoupledConsensusModel.Protocol.opposing gv F hc.η_SG r
        (DecoupledConsensusModel.Protocol.early E hc r phase)
        (DecoupledConsensusModel.Protocol.late E hc r phase) v A = true) ⊆
      Finset.univ.filter fun v =>
        DecoupledConsensusModel.Protocol.opposing gv F hc.η_SG r
          (DecoupledConsensusModel.Protocol.early E hc r phase)
          (DecoupledConsensusModel.Protocol.late E hc r phase) v B = true := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v,
      fixedRoot_opposing_mono hAB gv F hc.η_SG r
        (DecoupledConsensusModel.Protocol.early E hc r phase)
        (DecoupledConsensusModel.Protocol.late E hc r phase) v
        (Finset.mem_filter.mp hv).2⟩
  have hPos : (Finset.univ.filter fun v =>
      DecoupledConsensusModel.Protocol.positive gv F hc.η_SG r
        (DecoupledConsensusModel.Protocol.early E hc r phase)
        (DecoupledConsensusModel.Protocol.late E hc r phase) v B = true) ⊆
      Finset.univ.filter fun v =>
        DecoupledConsensusModel.Protocol.positive gv F hc.η_SG r
          (DecoupledConsensusModel.Protocol.early E hc r phase)
          (DecoupledConsensusModel.Protocol.late E hc r phase) v A = true := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v,
      fixedRoot_positive_mono hAB gv F hc.η_SG r
        (DecoupledConsensusModel.Protocol.early E hc r phase)
        (DecoupledConsensusModel.Protocol.late E hc r phase) v
        (Finset.mem_filter.mp hv).2⟩
  exact lt_of_le_of_lt (E.electorate.weightOf_mono hOpp)
    (lt_of_lt_of_le hB (E.electorate.weightOf_mono hPos))

theorem fixedRoot_activeVoterAnchor_g1_data
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (hr : 0 < r) {s : Slot}
    (hslo : S.hc.opening_slot r ≤ s)
    (hround : S.hc.round_of s = r)
    (hnext : Protocol.vote_time S.E s ≤
      DecoupledConsensusModel.Protocol.opening S.E S.hc (r + 1))
    (hvoteHor : Protocol.vote_time S.E s ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) {root L : Block V}
    (hframe : (DecoupledConsensusModel.Protocol.readFrame
      (Internal.NamedRecoveryRead.voteDutyRead S rho w s).cache
      (Internal.NamedRecoveryRead.voteDutyRead S rho w s).st.core.toHealing r).g1 =
        some (some root))
    (hactive : DecoupledConsensusModel.Protocol.activePrefix
      (PhaseGrades.filteredTree
        (Internal.NamedRecoveryRead.voteDutyRead S rho w s)) root = some L) :
    L ∈ (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.T ∧
      PhaseGrades.storeGrade S.E S.hc
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st r .g1 L = true := by
  let t := Protocol.vote_time S.E s
  let before := NamedRun.stateBeforeTime S rho t w
  let read := Internal.NamedRecoveryRead.voteDutyRead S rho w s
  let domainRead := PhaseGrades.readAt S rho
    (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w
  have hround' : S.hc.round_of (S.E.slotOf t) = r := by
    simpa only [t, Proofs.Optimistic.slotOf_vote_time] using hround
  have hdomainVote : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 < t := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact (Protocol.proposal_time_mono S.E hslo).trans_lt
      (Protocol.proposal_time_lt_vote_time S.E s)
  have hg1Hor : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 ≤ rho.horizon :=
    hdomainVote.le.trans hvoteHor
  have hbase := FrameCompleted.frame_phase_completed_in_round
    S rho adm.toNamedAdmissibleCore w hw r hr .g1 t hdomainVote hnext hg1Hor
  have hbase' :
      (DecoupledConsensusModel.Protocol.readFrame before.cache
        before.st.core.toHealing r).g1 =
        some ((PhaseGrades.storeRoot S.E S.hc domainRead.st r .g1).map
          (fun X => DecoupledConsensusModel.Protocol.clipGrade X before.st.core.F)) := by
    simpa only [before, domainRead, PhaseGrades.storeRoot,
      PhaseGrades.phaseRoot, PhaseGrades.readAt] using hbase
  have hprepared := NamedOutageClosure.frame_phase_prepared_eq
    S rho w r .g1 t hround' _ hbase'
  have hreadFrame :
      (DecoupledConsensusModel.Protocol.readFrame read.cache read.st.core.toHealing r).g1 =
        some ((PhaseGrades.storeRoot S.E S.hc domainRead.st r .g1).map
          (fun X => DecoupledConsensusModel.Protocol.clipGrade X read.st.core.F)) := by
    simpa only [read, before, t, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom] using hprepared
  cases hstore : PhaseGrades.storeRoot S.E S.hc domainRead.st r .g1 with
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
      have hrawData := Proofs.Engine.deepest?_mem hstore
      have hrawTree : raw ∈ domainRead.st.core.T :=
        (Finset.mem_filter.mp hrawData).1
      have hLtree : L ∈ domainRead.st.core.T := by
        have hpc := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w
        exact Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
          L raw hrawTree hLraw
      have hrawGrade : PhaseGrades.phaseGrade S.E S.hc
          domainRead.st.core.toHealing.gradeView domainRead.st.core.F
          r .g1 raw = true := (Finset.mem_filter.mp hrawData).2
      refine ⟨hLtree, ?_⟩
      exact fixedRoot_phaseGrade_mono S.E S.hc _ _ r .g1 hLraw hrawGrade

private theorem fixedRoot_g0_compatible_clearSource
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (hr : 0 < r) (hactionHor : S.a r ≤ rho.horizon)
    {u : V} (hu : u ∈ rho.honest) {L B : Block V}
    (hLtree : L ∈ (PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) u).st.core.T)
    (hLgrade : PhaseGrades.storeGrade S.E S.hc
      (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) u).st r .g0 L = true)
    (hLaction : L ∈ PhaseGrades.filteredTree
      (Internal.NamedRecoveryRead.actionDutyRead S rho u r))
    (hBclear : PhaseGrades.nodeClear S (actionReadAt S rho u r) r B = true) :
    Block.compatible L B = true := by
  obtain ⟨raw, hraw, hLraw⟩ := NamedOutageClosure.q10_freeze_of_graded
    S.E
    (PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) u).st.core.toHealing.gradeView
    (PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) u).st.core.F
    S.hc.η_SG r (e := DecoupledConsensusModel.Protocol.early S.E S.hc r .g0)
    (l := DecoupledConsensusModel.Protocol.late S.E S.hc r .g0)
    (by
      simp only [DecoupledConsensusModel.Protocol.early, DecoupledConsensusModel.Protocol.late,
      DecoupledConsensusModel.Protocol.Phase.earlyOffset, DecoupledConsensusModel.Protocol.Phase.lateOffset]
      exact le_rfl)
    hLtree (by simpa only [PhaseGrades.storeGrade] using hLgrade)
  have hactionFrame := actionFrame_g0 S adm.toNamedAdmissibleCore
    hu hr hactionHor
  have hframe :
      (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho u r).cache
        (actionReadAt S rho u r).st.core.toHealing r).g0 =
        some (some (DecoupledConsensusModel.Protocol.clipGrade raw
          (actionReadAt S rho u r).st.core.F)) := by
    simpa only [PhaseGrades.storeRoot, PhaseGrades.phaseRoot, hraw,
      Option.map_some] using hactionFrame
  have hFL : Block.Preceq (actionReadAt S rho u r).st.core.F L :=
    (Finset.mem_filter.mp
      (Finset.mem_filter.mp (Finset.mem_filter.mp hLaction).1).1).2
  have hLclip : Block.Preceq L
      (DecoupledConsensusModel.Protocol.clipGrade raw
        (actionReadAt S rho u r).st.core.F) := by
    apply (NamedOutageClosure.q10_retained_prefix raw
      (actionReadAt S rho u r).st.core.F L ?_).mpr hLraw
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr hFL
  have hBclip : Block.compatible B
      (DecoupledConsensusModel.Protocol.clipGrade raw
        (actionReadAt S rho u r).st.core.F) = true := by
    simpa only [PhaseGrades.nodeClear, PhaseGrades.nodeRead,
      NamedProfile.gradeContract, DecoupledConsensusModel.Protocol.frameContract,
      DecoupledConsensusModel.Protocol.frameGradeRead,
      DecoupledConsensusModel.Protocol.clear, hframe] using hBclear
  simp only [Block.compatible, Bool.or_eq_true] at hBclip ⊢
  rcases hBclip with hBclip | hclipB
  · exact (Block.preceq_linear hLclip hBclip).elim Or.inl Or.inr
  · exact Or.inl (Block.preceq_trans hLclip hclipB)


/-- An active prepared voter anchor is compatible with a clear prepared action
carrier in the same fixed-root round. -/
theorem voterAnchorAt_compatible_actionSGBlockAt
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {r : Round} (hr : 0 < r) (ready : GradeRoundReady S rho r)
    (hactionHor : S.a r ≤ rho.horizon)
    {J : NamedBlock V} (hJrun : RunBlock S rho J)
    {u : V} (hu : u ∈ rho.honest) {s : Slot}
    (hslo : S.hc.opening_slot r + 1 ≤ s)
    (hshi : s < S.hc.opening_slot (r + 1))
    (hvoteHor : Protocol.vote_time S.E s ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) {root L B : Block V}
    (hframe : (DecoupledConsensusModel.Protocol.readFrame
      (Internal.NamedRecoveryRead.voteDutyRead S rho w s).cache
      (Internal.NamedRecoveryRead.voteDutyRead S rho w s).st.core.toHealing r).g1 =
        some (some root))
    (hactive : DecoupledConsensusModel.Protocol.activePrefix
      (PhaseGrades.filteredTree
        (Internal.NamedRecoveryRead.voteDutyRead S rho w s)) root = some L)
    (hactionRoot : Protocol.get_fg_root
      (actionStoreAt S rho u r).st.core.toHealing.toFG = J.erase)
    (hactionCap : (actionStoreAt S rho u r).st.core.h_max ≤
      (Protocol.derive_named S.E S.cfg J).h + 1)
    (hvoteRoot : Protocol.get_fg_root
      (Internal.NamedRecoveryRead.voteDutyRead S rho w s).st.core.toHealing.toFG =
        J.erase)
    (hBclear : PhaseGrades.nodeClear S (actionReadAt S rho u r) r B = true)
    (htarget : actionSGBlockAt S rho u r = B) :
    Block.compatible (voterAnchorAt S rho w s)
      (actionSGBlockAt S rho u r) = true := by
  have hround : S.hc.round_of s = r :=
    round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc hslo hshi
  have hnext : Protocol.vote_time S.E s ≤
      DecoupledConsensusModel.Protocol.opening S.E S.hc (r + 1) :=
    (fixedRoot_voteTime_lt_nextProposal S.E s).le.trans
      (Protocol.proposal_time_mono S.E (Nat.succ_le_iff.mpr hshi))
  obtain ⟨hLtreeG1, hLgrade1⟩ := fixedRoot_activeVoterAnchor_g1_data
    S adm hr ((Nat.le_succ _).trans hslo) hround hnext hvoteHor hw
      hframe hactive
  have hLvote : L ∈ PhaseGrades.filteredTree
      (Internal.NamedRecoveryRead.voteDutyRead S rho w s) := by
    unfold DecoupledConsensusModel.Protocol.activePrefix at hactive
    exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).1
  have hJL : Block.Preceq J.erase L := by
    rw [← hvoteRoot]
    exact Proofs.Records.preceq_get_fg_root_of_mem_filtered hLvote
  obtain ⟨Ln, hLnG1, hLnErase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w hLtreeG1
  have hLnRun : RunBlock S rho Ln :=
    fixedRoot_runBlock_of_body_at_read S adm hw hLnG1
  have hgstG1 : S.E.t_GST ≤ DecoupledConsensusModel.Protocol.early S.E S.hc r .g1 := by
    exact ready.1.trans (by
      simp only [DecoupledConsensusModel.Protocol.early, DecoupledConsensusModel.Protocol.Phase.earlyOffset]
      linarith [S.E.Δ_pos])
  have hgstDomain : S.E.t_GST ≤
      DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 :=
    hgstG1.trans (by
      simp only [DecoupledConsensusModel.Protocol.early, DecoupledConsensusModel.Protocol.domain,
        DecoupledConsensusModel.Protocol.Phase.earlyOffset,
        DecoupledConsensusModel.Protocol.Phase.domainOffset]
      linarith [S.E.Δ_pos])
  have hdeadline :
      max (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) S.E.t_GST + S.E.Δ ≤
        DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0 := by
    rw [max_eq_left hgstDomain]
    apply le_of_eq
    simp only [DecoupledConsensusModel.Protocol.domain, DecoupledConsensusModel.Protocol.Phase.domainOffset]
    ring
  have hFActionJ : Block.Preceq
      (rho.storeBeforeTime S u (S.a r)).core.F J.erase := by
    have hFroot := Proofs.Records.preceq_get_fg_root_of_F
      (st := (rho.storeBeforeTime S u (S.a r)).core.toHealing.toFG)
      (Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        S rho (S.a r) u)
    have hroot : Protocol.get_fg_root
        (rho.storeBeforeTime S u (S.a r)).core.toHealing.toFG = J.erase := by
      simpa only [actionStoreAt, actionReadAt,
        NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
        NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache] using hactionRoot
    simpa only [hroot] using hFroot
  have hFActionL : Block.Preceq
      (rho.storeBeforeTime S u (S.a r)).core.F L :=
    Block.preceq_trans hFActionJ hJL
  have hdomainAction : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0 ≤ S.a r :=
    FrameForward.domain_le_a S r .g0
  have hF0L : Block.Preceq
      (rho.storeBeforeTime S u
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0)).core.F L :=
    Block.preceq_trans
      (fixedRoot_strict_finality_mono S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed u hdomainAction)
      hFActionL
  have hLnG0 := NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
    S rho adm.toNamedAdmissibleCore w hw u hu Ln
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0)
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) hLnG1 hdeadline
      (le_refl _) ready.2 (by simpa only [hLnErase] using hF0L)
  have hLnAction := NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
    S rho adm.toNamedAdmissibleCore w hw u hu Ln
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1)
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) (S.a r) hLnG1
      hdeadline hdomainAction ready.2
      (by simpa only [hLnErase] using hFActionL)
  obtain ⟨Jn, hJnLn, hJnErase⟩ := Proofs.NamedAncestry.erased_ancestor_lift Ln
    (by simpa only [hLnErase] using hJL)
  have hJnRun := Proofs.NamedRuntime.blockInRun_of_ancestor S rho hLnRun hJnLn
  have hJnEq : Jn = J := fixedRoot_runBlock_unique_of_erase_eq
    adm hJnRun hJrun (hJnErase.trans rfl)
  have hheight : (Protocol.derive_named S.E S.cfg J).h ≤
      (Protocol.derive_named S.E S.cfg Ln).h := by
    rw [← hJnEq]
    exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hJnLn
  have hLaction : L ∈ PhaseGrades.filteredTree
      (Internal.NamedRecoveryRead.actionDutyRead S rho u r) := by
    have hfiltered := mem_filtered_of_mem_tree_of_exactFGRoot_heightCap
      S rho u (S.a r) hLnAction.1 hLnErase (by
        simpa only [actionStoreAt, actionReadAt,
          NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
          NamedActionReads.confirmationReadFrom,
          NamedActionReads.preparedCache] using hactionRoot) hJL (by
        have hcap := hactionCap
        simpa only [actionStoreAt, actionReadAt,
          NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
          NamedActionReads.confirmationReadFrom,
          NamedActionReads.preparedCache] using
            hcap.trans (Nat.add_le_add_right hheight 1))
    simpa only [Internal.NamedRecoveryRead.actionDutyRead, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, PhaseGrades.filteredTree,
      PhaseGrades.readAt] using hfiltered
  have hforward : ∀ sender x key Head,
      x ∈ DecoupledConsensusModel.Protocol.interpretedInputs
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.F
        S.hc.η_SG r (DecoupledConsensusModel.Protocol.early S.E S.hc r .g1) sender →
      DecoupledConsensusModel.Protocol.localCovers
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
        x.confirmed L = true → x.confirmed = some key →
      Block.find? (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st.core.T key = some Head →
      Block.Preceq (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) u).st.core.F Head := by
    intro sender x key Head _ hcover hconf hfind
    apply Block.preceq_trans hF0L
    unfold DecoupledConsensusModel.Protocol.localCovers at hcover
    unfold Protocol.head_covers at hcover
    simp only [Protocol.HealingStore.gradeView, Protocol.Store.toHealing, hconf] at hcover
    rw [hfind] at hcover
    exact hcover
  have hbelow := g1G0CrossReaderFinalizedBelow_of_finalitySafety_and_relay
    S adm hsb hgstG1 ready.2 hw hu hforward
  have hguard := g1G0CrossReaderBodyReadyGuard_of_finalizedBelow
    S adm.toNamedAdmissibleCore hr hgstG1 ready.2 hw hu hbelow
  have hLgrade0 := storeGrade_g0_of_storeGrade_g1_cross_reader
    S rho adm.toNamedAdmissibleCore r
      (g1G0TwoCutoffDelivery_of_core S adm.toNamedAdmissibleCore hgstG1)
      ready.2 w u hw hu L hLgrade1 hguard
  have hLtreeG0 : L ∈ (PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) u).st.core.T := by
    have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) u).1.1.1
    change L ∈ (NamedRun.stateBeforeTime S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) u).st.core.T
    rw [hcoh.1, ← hLnErase]
    exact Finset.mem_image_of_mem NamedBlock.erase hLnG0.1
  have hcompat := fixedRoot_g0_compatible_clearSource
    S adm hr hactionHor hu hLtreeG0 hLgrade0 hLaction hBclear
  have hanchor : voterAnchorAt S rho w s = L := by
    have hroundRead : S.hc.round_of
        (Internal.NamedRecoveryRead.voteDutyRead S rho w s).st.core.s = r := by
      simpa only [Proofs.Optimistic.voteDutyRead_slot] using hround
    change DecoupledConsensusModel.Protocol.anchor S.E S.hc
      (Internal.NamedRecoveryRead.voteDutyRead S rho w s).st.core.toHealing
      (S.hc.round_of
        (Internal.NamedRecoveryRead.voteDutyRead S rho w s).st.core.s)
      (DecoupledConsensusModel.Protocol.readFrame
        (Internal.NamedRecoveryRead.voteDutyRead S rho w s).cache
        (Internal.NamedRecoveryRead.voteDutyRead S rho w s).st.core.toHealing
        (S.hc.round_of
          (Internal.NamedRecoveryRead.voteDutyRead S rho w s).st.core.s)).g1 = L
    rw [hroundRead, hframe]
    simp only [DecoupledConsensusModel.Protocol.anchor, hactive, Option.getD_some]
  rw [hanchor, htarget]
  exact hcompat

/-- Every prepared interior voter anchor is compatible with a clear action
target under the exact named root and action height cap. -/
theorem
    interiorVoteFreshAnchor_compatible_actionSGBlockAt_of_gradeFormsAt_exactFGRoot_heightCap
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {r : Round} (hr : 0 < r) (ready : GradeRoundReady S rho r)
    (hactionHor : S.a r ≤ rho.horizon)
    {J : NamedBlock V} (hJrun : RunBlock S rho J)
    {u : V} (hu : u ∈ rho.honest) {Q T : Block V}
    (hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho u r) r = some Q)
    (hclear : Protocol.deepest_clear
      (some (PhaseGrades.nodeAnchor S (actionReadAt S rho u r) r))
      (actionReadAt S rho u r).st.core.live_confirmed
      (PhaseGrades.nodeClear S (actionReadAt S rho u r) r) = some T)
    (htarget : actionSGBlockAt S rho u r = T)
    {s : Slot} (hslo : S.hc.opening_slot r + 1 ≤ s)
    (hshi : s < S.hc.opening_slot (r + 1))
    (hvoteHor : Protocol.vote_time S.E s ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest)
    (hactionRoot : Protocol.get_fg_root
      (actionStoreAt S rho u r).st.core.toHealing.toFG = J.erase)
    (hactionCap : (actionStoreAt S rho u r).st.core.h_max ≤
      (Protocol.derive_named S.E S.cfg J).h + 1)
    (hvoteRoot : Protocol.get_fg_root
      (Internal.NamedRecoveryRead.voteDutyRead S rho w s).st.core.toHealing.toFG =
        J.erase) :
    Block.compatible (voterAnchorAt S rho w s)
      (actionSGBlockAt S rho u r) = true := by
  have hJQ : Block.Preceq J.erase Q := by
    rw [← hactionRoot]
    exact Proofs.Records.preceq_get_fg_root_of_mem_filtered
      (actionQ2_mem_filteredTree S rho u r hQ)
  have hQT : Block.Preceq Q (actionSGBlockAt S rho u r) :=
    preceq_actionSGBlockAt_of_actionQ2 S adm.toNamedAdmissibleCore hu
      hr hactionHor hQ (Block.preceq_self Q)
  rcases voterAnchorAt_cases S rho w s with hroot | hactive
  · rw [hroot]
    simp only [Block.compatible, Bool.or_eq_true]
    rw [hvoteRoot]
    exact Or.inl (Block.preceq_trans hJQ hQT)
  · obtain ⟨root, L, hframe, hactive, -⟩ := hactive
    have hroundRead : S.hc.round_of
        (Internal.NamedRecoveryRead.voteDutyRead S rho w s).st.core.s = r := by
      simpa only [Proofs.Optimistic.voteDutyRead_slot] using
        (round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc hslo hshi)
    rw [hroundRead] at hframe
    have hTclear : PhaseGrades.nodeClear S
        (actionReadAt S rho u r) r T = true := by
      have hmem := Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hclear)
      exact hmem.2.2
    exact voterAnchorAt_compatible_actionSGBlockAt
      S adm hsb hr ready hactionHor hJrun hu hslo hshi hvoteHor hw
        hframe hactive hactionRoot hactionCap hvoteRoot hTclear htarget

/-- A named target above the common root is a voter candidate, with its path. -/
theorem fixedRoot_targetCandidateAndPath
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {J T : NamedBlock V} (hJrun : RunBlock S rho J)
    (hTrun : RunBlock S rho T) (hJT : Block.Preceq J.erase T.erase)
    {w : V} (hw : w ∈ rho.honest) {d : Slot} (hd : 0 < d)
    (hroot : Protocol.get_fg_root
      (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.toFG =
        J.erase)
    (hcap : (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.h_max ≤
      (Protocol.derive_named S.E S.cfg J).h + 1)
    (hprocessed : T.erase ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w d).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho w d).toHealing.s) :
    T.erase ∈ voterCandidateTreeAt S rho w d ∧
      ∀ D : Block V,
        Block.Preceq (voterAnchorAt S rho w d) D →
        D ≠ voterAnchorAt S rho w d →
        Block.Preceq D T.erase → D ≠ T.erase →
        D ∈ voterCandidateTreeAt S rho w d := by
  let read := Internal.NamedRecoveryRead.voteDutyRead S rho w d
  have hraw : T.erase ∈ read.st.core.T := by
    have hdata := hprocessed
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter] at hdata
    simpa only [read, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using hdata.1
  obtain ⟨T', hT', hT'erase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (Protocol.vote_time S.E d) w (by
        simpa only [read, Internal.NamedRecoveryRead.voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock] using hraw)
  have hT'run : RunBlock S rho T' :=
    fixedRoot_runBlock_of_body_at_read S adm hw hT'
  have hT'eq : T' = T := fixedRoot_runBlock_unique_of_erase_eq
    adm hT'run hTrun (hT'erase.trans rfl)
  have hTbody : T ∈ (rho.storeBeforeTime S w
      (Protocol.vote_time S.E d)).bodies := by
    simpa only [hT'eq] using hT'
  have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime
    S rho (Protocol.vote_time S.E d) w T hTbody
  have hstored : (read.st.core.σ T.erase).h =
      (Protocol.derive_named S.E S.cfg T).h := by
    simpa only [read, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using congrArg (fun st => st.h) hview
  obtain ⟨J', hJ'T, hJ'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift T hJT
  have hJ'run := Proofs.NamedRuntime.blockInRun_of_ancestor S rho hTrun hJ'T
  have hJ'eq : J' = J := fixedRoot_runBlock_unique_of_erase_eq
    adm hJ'run hJrun (hJ'erase.trans rfl)
  have hheightJT : (Protocol.derive_named S.E S.cfg J).h ≤
      (Protocol.derive_named S.E S.cfg T).h := by
    rw [← hJ'eq]
    exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hJ'T
  have hheight : read.st.core.h_max - 1 ≤ (read.st.core.σ T.erase).h := by
    rw [hstored]
    exact Nat.sub_le_iff_le_add.mpr
      (hcap.trans (Nat.add_le_add_right hheightJT 1))
  have hfiltered : T.erase ∈ PhaseGrades.filteredTree read := by
    change T.erase ∈ Protocol.get_filtered_block_tree
      (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).toHealing.toFG
    apply mem_filtered_of_mem_tree_of_exactFGRoot_heightCap
      S rho w (Protocol.vote_time S.E d) hTbody rfl
    · simpa only [read, Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock] using hroot
    · exact hJT
    · simpa only [read, Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock] using
          hcap.trans (Nat.add_le_add_right hheightJT 1)
  have hcandidate : T.erase ∈ voterCandidateTreeAt S rho w d := by
    apply Protocol.voterCandidate_of_processed_self_and_filtered
      S.E read.st.core.toHealing
    · simpa only [read, Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
        Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hprocessed
    · exact hheight
    · exact hfiltered
  refine ⟨hcandidate, ?_⟩
  intro D hAD _ hDT _
  have hDprocessed : D ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w d).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho w d).toHealing.s := by
    have hanc := WeakGoldfish.ancestorProcessed_of_voterProcessed
      S adm.toNamedAdmissibleCore hw (s := d - 1) (B := T.erase) (by
        simpa only [Nat.sub_add_cancel hd] using hprocessed) D hDT
    simpa only [Nat.sub_add_cancel hd] using hanc
  have hrootAnchor : Block.Preceq
      (Protocol.get_fg_root read.st.core.toHealing.toFG)
      (voterAnchorAt S rho w d) := by
    exact NamedOutageClosure.fg_root_preceq_anchor S.E S.hc
      read.st.core.toHealing (S.hc.round_of read.st.core.s)
      (DecoupledConsensusModel.Protocol.readFrame read.cache
        read.st.core.toHealing (S.hc.round_of read.st.core.s)).g1
  have hrootD : Block.Preceq
      (Protocol.get_fg_root read.st.core.toHealing.toFG) D :=
    Block.preceq_trans hrootAnchor hAD
  have hFD : Block.Preceq read.st.core.F D :=
    Block.preceq_trans
      (Proofs.Records.preceq_get_fg_root_of_F
        (st := read.st.core.toHealing.toFG) (by
          simpa only [read, Internal.NamedRecoveryRead.voteDutyRead,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom,
            Protocol.NamedStore.setClock] using
              (Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
                S rho (Protocol.vote_time S.E d) w))) hrootD
  change D ∈ Protocol.get_filtered_block_tree_from
    read.st.core.toHealing.toFG
    (Protocol.voter_processed_block_tree S.E
      read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
  simp only [Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq]
  exact ⟨⟨⟨by
    simpa only [read, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
      Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hDprocessed, hFD⟩,
    T.erase, by
      simpa only [read, Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
        Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hprocessed,
      hDT, hheight⟩, hrootD⟩

private theorem fixedRoot_preceq_voterHeadAt_of_adoption
    (S : Setup V) {rho : Run V} {source : Protocol.Store V}
    {s : Slot} {B : Block V} {w : V}
    (heligible : Protocol.voters_count S.E (confLate S.E source s) s <
      2 * Protocol.goldfish_score S.E source.T
        (confVotes S.E source s) (confVotes S.E source s) s B)
    (hadopt : NamedNextVoteAdoption S rho source s B w) :
    Block.Preceq B (voterHeadAt S rho w (s + 1)) := by
  let read := Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)
  let st := read.st.core
  let tree := voterCandidateTreeAt S rho w (s + 1)
  let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  have hslot : st.s = s + 1 := by
    simpa only [st, read] using Proofs.Optimistic.voteDutyRead_slot S rho w (s + 1)
  have hprev : st.s - 1 = s := by rw [hslot]; simp
  change Block.Preceq B
    (Protocol.get_head_in_tree_with_layer
      (NamedProfile.gradeContract read.cache) S.E S.hc st.toHealing
      tree votes support (st.s - 1))
  rw [Proofs.Optimistic.get_head_in_tree_split_with, hprev]
  simpa only [Protocol.Store.toHealing, read, st] using
    (Protocol.goldfish_fork_choice_captures_of_confirmation
      S.E st.σ st.h_max source.T st.T tree st.s
      (confEarly S.E source s) (confLate S.E source s)
      (confVotes S.E source s) votes support s
      (confNumerator S.E source s) hadopt.transport heligible
      hadopt.support_subset hadopt.anchor hadopt.path)

private theorem fixedRoot_ancestorConfirmation_eligible
    (E : Env V) (hc : Protocol.HealConfig)
    (source : Protocol.Store V) (s : Slot)
    {T C : Block V} {contract : Protocol.GradeContract V}
    (hTC : Block.Preceq T C)
    (hC : GenuineConfirmationWith contract E hc source s C) :
    Protocol.voters_count E (confLate E source s) s <
      2 * Protocol.goldfish_score E source.T
        (confVotes E source s) (confVotes E source s) s T := by
  have hN := confNumerator E source s
  have hsupport := supporters_mono E source.T
    (confVotes E source s) (confVotes E source s) s hTC
  have hcard := Finset.card_le_card hsupport
  have hCg : GenuineConfirmation (contract := contract) E hc source s C :=
    ⟨hC.selected, hC.genuine⟩
  have hCeligible := hCg.eligible
  rw [hN.score_eq_supporters] at hCeligible ⊢
  exact lt_of_lt_of_le hCeligible (Nat.mul_le_mul_left 2 hcard)

/-- A genuine opening confirmation seeds the first interior honest-vote cone
under the exact named root and one-step height cap. -/
theorem honestVotesCone_succ_of_ancestorGenuineConfirmation_exactFGRoot_heightCap
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {r : Round} (hr : 0 < r) (ready : GradeRoundReady S rho r)
    {J T : NamedBlock V} (hJrun : RunBlock S rho J)
    (hTrun : RunBlock S rho T) (hJT : Block.Preceq J.erase T.erase)
    {u : V} (hu : u ∈ rho.honest) {Q C : Block V}
    (hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho u r) r = some Q)
    (hclear : Protocol.deepest_clear
      (some (PhaseGrades.nodeAnchor S (actionReadAt S rho u r) r))
      (actionReadAt S rho u r).st.core.live_confirmed
      (PhaseGrades.nodeClear S (actionReadAt S rho u r) r) = some T.erase)
    (htarget : actionSGBlockAt S rho u r = T.erase)
    {contract : Protocol.GradeContract V}
    (hgenuine : GenuineConfirmationWith contract S.E S.hc
      (Proofs.Optimistic.confStore S rho u (S.hc.opening_slot r))
      (S.hc.opening_slot r) C)
    (hTC : Block.Preceq T.erase C)
    (hactionHor : S.a r ≤ rho.horizon)
    (hactionRoot : Protocol.get_fg_root
      (actionStoreAt S rho u r).st.core.toHealing.toFG = J.erase)
    (hactionCap : (actionStoreAt S rho u r).st.core.h_max ≤
      (Protocol.derive_named S.E S.cfg J).h + 1)
    (hvoteRoot : ∀ w ∈ rho.honest,
      Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w
          (S.hc.opening_slot r + 1)).st.core.toHealing.toFG = J.erase)
    (hvoteCap : ∀ w ∈ rho.honest,
      (Internal.NamedRecoveryRead.voteDutyRead S rho w
        (S.hc.opening_slot r + 1)).st.core.h_max ≤
          (Protocol.derive_named S.E S.cfg J).h + 1) :
    NamedHonestVotesCone S rho (S.hc.opening_slot r + 1)
      (fun X => Block.Preceq T.erase X) := by
  let source := S.hc.opening_slot r
  have hpost : S.E.t_GST ≤ Protocol.proposal_time S.E source := by
    exact ready.1.trans (by
      simp only [source, DecoupledConsensusModel.Protocol.early,
        DecoupledConsensusModel.Protocol.opening, DecoupledConsensusModel.Protocol.Phase.earlyOffset,
        Protocol.proposal_time]
      linarith [S.E.Δ_pos])
  have hsourceHor : Protocol.confirmation_time S.E source ≤ rho.horizon := by
    simpa only [source, opening_confirmation_time_eq_action S r] using hactionHor
  have hvoteHor : Protocol.vote_time S.E (source + 1) ≤ rho.horizon :=
    (next_vote_time_lt_action S r).le.trans hactionHor
  intro w hw hcommittee
  have hrootC : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (source + 1)).toHealing.toFG) C := by
    have hroot : Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (source + 1)).toHealing.toFG = J.erase := by
      simpa only [source, Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
        using hvoteRoot w hw
    rw [hroot]
    exact Block.preceq_trans hJT hTC
  have hgenuine' : GenuineConfirmation (contract := contract) S.E S.hc
      (Proofs.Optimistic.confStore S rho u source) source C :=
    ⟨hgenuine.selected, hgenuine.genuine⟩
  have hCprocessed := Protocol.voterProcessedTarget_of_genuineConfirmation_after_gst
    S adm hu hw hpost hsourceHor hgenuine' hrootC
  have hTprocessed := WeakGoldfish.ancestorProcessed_of_voterProcessed
    S adm.toNamedAdmissibleCore hw hCprocessed T.erase hTC
  have hroot : Protocol.get_fg_root
      (Internal.NamedRecoveryRead.voteDutyRead S rho w (source + 1)).st.core.toHealing.toFG =
        J.erase := by simpa only [source] using hvoteRoot w hw
  have hcap : (Internal.NamedRecoveryRead.voteDutyRead S rho w
      (source + 1)).st.core.h_max ≤
        (Protocol.derive_named S.E S.cfg J).h + 1 := by
    simpa only [source] using hvoteCap w hw
  obtain ⟨hcandidate, hpath⟩ := fixedRoot_targetCandidateAndPath
    S adm hJrun hTrun hJT hw (Nat.succ_pos source) hroot hcap (by
      simpa only [source] using hTprocessed)
  have hR : 1 < S.hc.R :=
    lt_of_lt_of_le (by decide : 1 < 2) S.hc.R_ge_two
  have hcompat :=
    interiorVoteFreshAnchor_compatible_actionSGBlockAt_of_gradeFormsAt_exactFGRoot_heightCap
      S adm hsb hr ready hactionHor hJrun hu hQ hclear htarget
      (le_refl _) (by
        calc
          S.hc.opening_slot r + 1 < S.hc.opening_slot r + S.hc.R :=
            Nat.add_lt_add_left hR _
          _ = S.hc.opening_slot (r + 1) :=
            (opening_slot_succ_eq S.hc r).symm) hvoteHor hw
      hactionRoot hactionCap hroot
  have hhead : Block.Preceq T.erase
      (voterHeadAt S rho w (source + 1)) := by
    rw [htarget] at hcompat
    simp only [Block.compatible, Bool.or_eq_true] at hcompat
    rcases hcompat with hanchorT | hTanchor
    · have hanchor' : Block.Preceq
          (Protocol.get_sg_root_with
            (NamedProfile.gradeContract
              (Internal.NamedRecoveryRead.voteDutyRead S rho w
                (source + 1)).cache)
            S.E S.hc
            (Internal.NamedRecoveryRead.voteDutyRead S rho w
              (source + 1)).st.core.toHealing
            (S.hc.round_of
              (Internal.NamedRecoveryRead.voteDutyRead S rho w
                (source + 1)).st.core.s)) T.erase := by
        simpa only [voterAnchorAt, PhaseGrades.nodeAnchor,
          PhaseGrades.nodeRead] using hanchorT
      have hadopt := nextVoteAdoption_of_frozenCandidateAtRead
        S adm hu hpost hsourceHor hw hcandidate hanchor'
      exact fixedRoot_preceq_voterHeadAt_of_adoption S
        (fixedRoot_ancestorConfirmation_eligible S.E S.hc
          (Proofs.Optimistic.confStore S rho u source) source hTC hgenuine) hadopt
    · exact Block.preceq_trans hTanchor
        (voterAnchorAt_preceq_voterHeadAt S rho w (source + 1))
  obtain ⟨X, hXhead, hXrun, hXemit⟩ := named_voter_head_emits
    S adm hw (Nat.succ_pos source) hcommittee hvoteHor
  exact ⟨X, by rw [hXhead]; exact hhead, hXrun, hXemit⟩

private theorem fixedRoot_preparedVoteViewValid
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (w : V) (s : Slot) :
    Protocol.VoteSetValid S.E
      ((Internal.NamedRecoveryRead.voteDutyRead S rho w s).st.core.s - 1)
      (Protocol.voter_view S.E
        (Internal.NamedRecoveryRead.voteDutyRead S rho w s).st.core.toHealing.toFG.toSG.toGoldfishStore
        (Internal.NamedRecoveryRead.voteDutyRead S rho w s).st.core.s) := by
  let t := Protocol.vote_time S.E s
  let read := Internal.NamedRecoveryRead.voteDutyRead S rho w s
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed t
  have hpool := Protocol.voteSetValid_pool_stateBefore S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed w n
    (read.st.core.s - 1)
  have hcarried : ∀ B ∈ (rho.stateBefore S n w).st.core.T,
      ∀ u ∈ B.gf_votes, u.val_index ∈ S.E.committee u.slot := by
    intro B hB u hu
    exact Protocol.carriedVote_committee_of_mem_T S adm w n hB u hu
  have hvalid := Protocol.voteSetValid_voter_view_of_carried
    (E := S.E) (st := (rho.stateBefore S n w).st.core)
    (s := read.st.core.s) hpool hcarried
  simpa only [read, t, Internal.NamedRecoveryRead.voteDutyRead,
    NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock, hn]
    using hvalid

private theorem fixedRoot_goldfishConeStep
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    {C : Block V}
    (hnames : NamedHonestVotesCone S rho s (fun X => Block.Preceq C X))
    {w : V} (hw : w ∈ rho.honest)
    (hinputs : GoldfishConeVoteInputs S rho s C w) :
    Block.Preceq C (voterHeadAt S rho w (s + 1)) := by
  let read := Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)
  let st := read.st.core
  let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  let tree := voterCandidateTreeAt S rho w (s + 1)
  have hcutHor : Protocol.support_cutoff S.E s ≤ rho.horizon :=
    (Proofs.Optimistic.support_cutoff_le_vote_time_succ S.E s).trans hvoteHor
  have havailable := honestHeadsAvailableBefore_of_namedPostHealingCone
    S adm hw hpost hcutHor hinputs.root hnames
  have hresolve0 := Protocol.headsResolveIn_storeBeforeTime_of_availableBefore_at
    S adm hw s (Proofs.Optimistic.support_cutoff_le_vote_time_succ S.E s) havailable
  have hresolve : Proofs.Optimistic.HeadsResolveIn S rho s st.T st.timestamp_block := by
    simpa only [st, read, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
      using hresolve0
  have hbase := Protocol.canonicalSuffixConeSupportVoterView
    S adm hcom hs hpost hcutHor hnames hw
      (Proofs.Optimistic.support_cutoff_le_vote_time_succ S.E s)
      (gst := st.toHealing.toFG.toSG.toGoldfishStore) (by rfl) (by rfl) (by rfl)
      (hresolve.of_eq rfl rfl)
  have hslot : st.s = s + 1 := by
    simpa only [st, read] using Proofs.Optimistic.voteDutyRead_slot S rho w (s + 1)
  have hvalid := fixedRoot_preparedVoteViewValid S adm w (s + 1)
  have hcone : Proofs.Optimistic.ConeSupport S.E st.T votes support votes
      (st.s - 1) rho.honest (fun X => Block.Preceq C X) := by
    simpa only [st, read, votes, support, hslot,
      Protocol.Store.toHealing] using hbase
  have hmajority : Protocol.voters_count S.E votes (st.s - 1) <
      2 * (Protocol.goldfishSupporters S.E st.T votes support (st.s - 1) C).card :=
    Protocol.supporterMajority_of_cone S.E hcone hvalid
  have hpath : ∀ D : Block V,
      Block.Preceq (voterAnchorAt S rho w (s + 1)) D →
      D ≠ voterAnchorAt S rho w (s + 1) →
      Block.Preceq D C → D ∈ tree := by
    intro D hAD hDne hDC
    by_cases hEq : D = C
    · simpa only [hEq] using hinputs.candidate
    · exact hinputs.path D hAD hDne hDC hEq
  have hhead := Protocol.goldfish_fork_choice_captures_supporter_majority
    S.E st.σ st.h_max st.T tree st.s votes support (st.s - 1)
      (Proofs.Optimistic.ConeSupport.sub hcone) hmajority hinputs.anchor
      (fun _ D hAD hDne hDC => hpath D hAD hDne hDC)
  change Block.Preceq C
    (Protocol.get_head_in_tree_with_layer
      (NamedProfile.gradeContract read.cache) S.E S.hc st.toHealing
      tree votes support (st.s - 1))
  simpa only [get_head_in_tree_eq_voterHeadAt_of_anchor, read, st] using hhead

/-- The genuine-clear cone persists through every supplied interior slot under
the exact named root and one-step height caps. -/
theorem
    honestVotesCone_on_roundInterior_of_ancestorGenuineConfirmation_exactFGRoot_heightCap
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hsb : SlashableBound S rho)
    {r : Round} (hr : 0 < r) (ready : GradeRoundReady S rho r)
    {J T : NamedBlock V} (hJrun : RunBlock S rho J)
    (hTrun : RunBlock S rho T) (hJT : Block.Preceq J.erase T.erase)
    {u : V} (hu : u ∈ rho.honest) {Q C : Block V}
    (hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho u r) r = some Q)
    (hclear : Protocol.deepest_clear
      (some (PhaseGrades.nodeAnchor S (actionReadAt S rho u r) r))
      (actionReadAt S rho u r).st.core.live_confirmed
      (PhaseGrades.nodeClear S (actionReadAt S rho u r) r) = some T.erase)
    (htarget : actionSGBlockAt S rho u r = T.erase)
    {contract : Protocol.GradeContract V}
    (hgenuine : GenuineConfirmationWith contract S.E S.hc
      (Proofs.Optimistic.confStore S rho u (S.hc.opening_slot r))
      (S.hc.opening_slot r) C)
    (hTC : Block.Preceq T.erase C)
    {s : Slot} (hslo : S.hc.opening_slot r + 1 ≤ s)
    (hshi : s < S.hc.opening_slot (r + 1))
    (hactionHor : S.a r ≤ rho.horizon)
    (hvoteHor : Protocol.vote_time S.E s ≤ rho.horizon)
    (hactionRoot : Protocol.get_fg_root
      (actionStoreAt S rho u r).st.core.toHealing.toFG = J.erase)
    (hactionCap : (actionStoreAt S rho u r).st.core.h_max ≤
      (Protocol.derive_named S.E S.cfg J).h + 1)
    (hvoteRoot : ∀ d : Slot,
      S.hc.opening_slot r + 1 ≤ d →
      d < S.hc.opening_slot (r + 1) → ∀ w ∈ rho.honest,
      Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.toFG =
          J.erase)
    (hvoteCap : ∀ d : Slot,
      S.hc.opening_slot r + 1 ≤ d →
      d < S.hc.opening_slot (r + 1) → ∀ w ∈ rho.honest,
      (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.h_max ≤
        (Protocol.derive_named S.E S.cfg J).h + 1) :
    NamedHonestVotesCone S rho s (fun X => Block.Preceq T.erase X) := by
  let lo := S.hc.opening_slot r + 1
  have hloPos : 0 < lo := Nat.zero_lt_succ _
  have hlohi : lo ≤ s := hslo
  have hloNext : lo < S.hc.opening_slot (r + 1) := hslo.trans_lt hshi
  have hseed :=
    honestVotesCone_succ_of_ancestorGenuineConfirmation_exactFGRoot_heightCap
      S adm hsb hr ready hJrun hTrun hJT hu hQ hclear htarget
      hgenuine hTC hactionHor hactionRoot hactionCap
      (fun w hw => hvoteRoot lo (le_refl _) hloNext w hw)
      (fun w hw => hvoteCap lo (le_refl _) hloNext w hw)
  have hpostLo : S.E.t_GST ≤ Protocol.vote_time S.E lo := by
    have hpostSource : S.E.t_GST ≤
        Protocol.proposal_time S.E (S.hc.opening_slot r) := by
      exact ready.1.trans (by
        simp only [DecoupledConsensusModel.Protocol.early, DecoupledConsensusModel.Protocol.opening,
          DecoupledConsensusModel.Protocol.Phase.earlyOffset, Protocol.proposal_time]
        linarith [S.E.Δ_pos])
    exact hpostSource.trans
      ((Protocol.proposal_time_lt_vote_time S.E _).le.trans
        (by simpa only [lo] using
          (Protocol.vote_time_mono_slots S.E
            (Nat.le_succ (S.hc.opening_slot r)))))
  have hfold : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq T.erase X) ∨ False :=
    honestVotesCone_or_exit_of_bounded_fold S rho hlohi hseed (by
      intro k hklo hkhi hcone
      apply Or.inl
      have hkPos : 0 < k := hloPos.trans_le hklo
      have hdlo : S.hc.opening_slot r + 1 ≤ k + 1 :=
        hklo.trans (Nat.le_succ k)
      have hdhi : k + 1 < S.hc.opening_slot (r + 1) :=
        (Nat.succ_le_iff.mpr hkhi).trans_lt hshi
      have hdHor : Protocol.vote_time S.E (k + 1) ≤ rho.horizon :=
        (Protocol.vote_time_mono_slots S.E
          (Nat.succ_le_iff.mpr hkhi)).trans hvoteHor
      have hpostK : S.E.t_GST ≤ Protocol.vote_time S.E k :=
        hpostLo.trans (Protocol.vote_time_mono_slots S.E hklo)
      intro w hw hcommittee
      have hroot := hvoteRoot (k + 1) hdlo hdhi w hw
      have hcap := hvoteCap (k + 1) hdlo hdhi w hw
      have hrootC : Block.Preceq
          (Protocol.get_fg_root
            (Proofs.Optimistic.voteDutyStore S rho w (k + 1)).toHealing.toFG) C := by
        have hroot' : Protocol.get_fg_root
            (Proofs.Optimistic.voteDutyStore S rho w (k + 1)).toHealing.toFG =
              J.erase := by
          simpa only [Internal.NamedRecoveryRead.voteDutyRead,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom,
            Protocol.NamedStore.setClock] using hroot
        rw [hroot']
        exact Block.preceq_trans hJT hTC
      have hpostSource : S.E.t_GST ≤ Protocol.proposal_time S.E
          (S.hc.opening_slot r) := by
        exact ready.1.trans (by
          simp only [DecoupledConsensusModel.Protocol.early, DecoupledConsensusModel.Protocol.opening,
            DecoupledConsensusModel.Protocol.Phase.earlyOffset, Protocol.proposal_time]
          linarith [S.E.Δ_pos])
      have hCprocessed :=
        voterProcessedTarget_of_genuineConfirmation_at_laterVoteDuty_after_gst
          S adm hu hw hklo hpostSource hdHor
            (⟨hgenuine.selected, hgenuine.genuine⟩ :
              GenuineConfirmation (contract := contract) S.E S.hc
                (Proofs.Optimistic.confStore S rho u (S.hc.opening_slot r))
                (S.hc.opening_slot r) C) hrootC
      have hTprocessed := WeakGoldfish.ancestorProcessed_of_voterProcessed
        S adm.toNamedAdmissibleCore hw hCprocessed T.erase hTC
      obtain ⟨hcandidate, hpath⟩ := fixedRoot_targetCandidateAndPath
        S adm hJrun hTrun hJT hw (Nat.succ_pos k) hroot hcap hTprocessed
      have hanchor :=
        interiorVoteFreshAnchor_compatible_actionSGBlockAt_of_gradeFormsAt_exactFGRoot_heightCap
          S adm hsb hr ready hactionHor hJrun hu hQ hclear htarget
          hdlo hdhi hdHor hw hactionRoot hactionCap hroot
      have hhead := fixedRoot_goldfishConeStep
        S adm hcom hkPos hpostK hdHor hcone hw
          { candidate := hcandidate
            root := by rw [hroot]; exact hJT
            anchor := by simpa only [htarget] using hanchor
            path := hpath }
      obtain ⟨X, hXhead, hXrun, hXemit⟩ := named_voter_head_emits
        S adm hw (Nat.succ_pos k) hcommittee hdHor
      exact ⟨X, by rw [hXhead]; exact hhead, hXrun, hXemit⟩)
  exact hfold.resolve_right False.elim

private theorem fixedRoot_namedGrade_processedAtAction
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {J : Block V} (hforms : NamedGradeFormsAt S rho r J)
    {v : V} (hv : v ∈ rho.honest) :
    J ∈ (rho.storeBeforeTime S v (S.a r)).core.T := by
  have hsource : J ∈ (rho.storeBeforeTime S v
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)).core.T := by
    have hfiltered := (hforms v hv).1
    have htree := Proofs.Records.get_filtered_block_tree_subset _ hfiltered
    simpa only [PhaseGrades.filteredTree, PhaseGrades.readAt,
      Run.storeBeforeTime] using htree
  rw [storeBeforeTime_eq_storeAt_sub_one_recovery] at hsource ⊢
  apply StoreFinality.stateAt_T_subset
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v
      (Int.sub_le_sub_right (FrameForward.domain_le_a S r .g2) 1) hsource

/-- Direct named Claim 1 under an exact common SG root. -/
theorem sgTargetConeCanonicality_of_gradeFormsAt_exactFGRoot_heightCap
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {r : Round} (hr : 0 < r) (ready : GradeRoundReady S rho r)
    {J : NamedBlock V} (hJrun : RunBlock S rho J)
    (hforms : NamedGradeFormsAt S rho r J.erase)
    {s : Slot} (hslo : S.hc.opening_slot r + 1 ≤ s)
    (hshi : s < S.hc.opening_slot (r + 1))
    (hactionHor : S.a r ≤ rho.horizon)
    (hvoteHor : Protocol.vote_time S.E s ≤ rho.horizon)
    (hactionRoot : ∀ w ∈ rho.honest,
      Protocol.get_fg_root
        (actionStoreAt S rho w r).st.core.toHealing.toFG = J.erase)
    (hactionCap : ∀ w ∈ rho.honest,
      (actionStoreAt S rho w r).st.core.h_max ≤
        (Protocol.derive_named S.E S.cfg J).h + 1)
    (hvoteRoot : ∀ d : Slot,
      S.hc.opening_slot r + 1 ≤ d →
      d < S.hc.opening_slot (r + 1) → ∀ w ∈ rho.honest,
      Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.toFG =
          J.erase)
    (hvoteCap : ∀ d : Slot,
      S.hc.opening_slot r + 1 ≤ d →
      d < S.hc.opening_slot (r + 1) → ∀ w ∈ rho.honest,
      (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.h_max ≤
        (Protocol.derive_named S.E S.cfg J).h + 1) :
    NamedSGTargetConeCanonicality S rho r s := by
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  intro v hv
  have hJraw := fixedRoot_namedGrade_processedAtAction S adm hforms hv
  obtain ⟨J', hJ'body, hJ'erase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho (S.a r) v hJraw
  have hJ'run : RunBlock S rho J' :=
    fixedRoot_runBlock_of_body_at_read S adm hv hJ'body
  have hJ'eq : J' = J := fixedRoot_runBlock_unique_of_erase_eq
    adm hJ'run hJrun (hJ'erase.trans rfl)
  have hJbody : J ∈ (rho.storeBeforeTime S v (S.a r)).bodies := by
    simpa only [hJ'eq] using hJ'body
  have hJactive : J.erase ∈ PhaseGrades.filteredTree
      (actionReadAt S rho v r) := by
    have hfiltered := mem_filtered_of_mem_tree_of_exactFGRoot_heightCap
      S rho v (S.a r) hJbody rfl (hactionRoot v hv)
      (Block.preceq_self J.erase) (hactionCap v hv)
    simpa only [PhaseGrades.filteredTree, PhaseGrades.readAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache] using hfiltered
  obtain ⟨Q, hQ, hJQ⟩ := namedGradeFormsAt_preceq_actionQ2
    S adm.toNamedAdmissibleCore hr hactionHor hforms hv hJactive
  have htargetRaw : actionSGBlockAt S rho v r ∈
      (actionReadAt S rho v r).st.core.T :=
    actionSGBlockAt_mem_actionStore_of_actionQ2 S rho v r hQ
  obtain ⟨T, hTbody, hTerase⟩ := Finset.mem_image.mp (by
    have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a r) v).1.1.1
    have htargetRaw' := htargetRaw
    change actionSGBlockAt S rho v r ∈
      (NamedRun.stateBeforeTime S rho (S.a r) v).st.core.T at htargetRaw'
    rw [hcoh.1] at htargetRaw'
    exact htargetRaw')
  have hTrun : RunBlock S rho T := by
    apply fixedRoot_runBlock_of_body_at_read S adm hv
    simpa only [actionReadAt, NamedActionReads.actionReadAt,
      NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache] using hTbody
  have hQT : Block.Preceq Q T.erase := by
    rw [hTerase]
    exact preceq_actionSGBlockAt_of_actionQ2 S adm.toNamedAdmissibleCore hv
      hr hactionHor hQ (Block.preceq_self Q)
  have hJT : Block.Preceq J.erase T.erase := Block.preceq_trans hJQ hQT
  rcases actionSGBlockAt_clear_or_selectedG2 S rho hQ with hclear | hselected
  · obtain ⟨U, hclear, htarget⟩ := hclear
    have hUT : U = T.erase := htarget.symm.trans hTerase.symm
    rw [hUT] at hclear
    rcases actionStoreAt_liveConfirmed_genuine_or_fgRoot S rho v r with
      hgenuine | hroot
    · obtain ⟨C, hgenuine, hClive⟩ := hgenuine
      have hTC : Block.Preceq T.erase C := by
        rw [hClive]
        exact Proofs.Engine.deepest_clear_preceq hclear
      have hcone :=
        honestVotesCone_on_roundInterior_of_ancestorGenuineConfirmation_exactFGRoot_heightCap
          S adm hcom hsb hr ready hJrun hTrun hJT hv hQ hclear
          hTerase.symm (hgenuine := hgenuine) (hTC := hTC)
          hslo hshi hactionHor hvoteHor
          (hactionRoot v hv) (hactionCap v hv) hvoteRoot hvoteCap
      simpa only [hTerase] using hcone
    · obtain ⟨R, hRroot, hRlive⟩ := hroot
      have hTQ :=
        (clearTarget_eq_fgRoot_and_selectedG2_of_selectedG2
          S adm hr hactionHor hv hQ hclear hRroot hRlive).2
      have hcone := honestVotesCone_of_selectedActionG2_exactFGRoot_heightCap
        S adm hfb hr ready hJrun hv hQ hslo hshi hvoteHor hactionRoot
          (fun w hw => hvoteRoot s hslo hshi w hw)
          (fun w hw => hvoteCap s hslo hshi w hw)
      have haQ : actionSGBlockAt S rho v r = Q :=
        hTerase.symm.trans hTQ
      simpa only [haQ] using hcone
  · have hcone := honestVotesCone_of_selectedActionG2_exactFGRoot_heightCap
      S adm hfb hr ready hJrun hv hQ hslo hshi hvoteHor hactionRoot
        (fun w hw => hvoteRoot s hslo hshi w hw)
        (fun w hw => hvoteCap s hslo hshi w hw)
    simpa only [hselected] using hcone







#print axioms honestVotesCone_of_selectedActionG2_exactFGRoot_heightCap
#print axioms fixedRoot_activeVoterAnchor_g1_data
#print axioms voterAnchorAt_compatible_actionSGBlockAt
#print axioms
  interiorVoteFreshAnchor_compatible_actionSGBlockAt_of_gradeFormsAt_exactFGRoot_heightCap
#print axioms honestVotesCone_succ_of_ancestorGenuineConfirmation_exactFGRoot_heightCap
#print axioms
  honestVotesCone_on_roundInterior_of_ancestorGenuineConfirmation_exactFGRoot_heightCap
#print axioms sgTargetConeCanonicality_of_gradeFormsAt_exactFGRoot_heightCap

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
