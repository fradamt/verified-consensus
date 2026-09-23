module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.RelativeOneChain
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FixedHeightRootOpeningParent
public import DecoupledConsensusProofs.Execution.PreparedReadBridge

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## (a) The honest preceding-round action carrier above a relative grade -/


/-- **Relative twin of `RecoveryFreshGradeProvenanceRun.
G1_preceq_honestPreviousActionCarrier`.** A block carrying the relative G1
grade of round `c` at an honest reader's own G1 domain read is below one
honest validator's round-`(c-1)` Section 7 action carrier.

Superseded: the content is `RelativeOneChainRun.relativeGrade_has_roundCarrier`.
This wrapper only renames the round (`c` for `r + 1`), states the premise in
the `namedG1At` vocabulary the seed branches uses, and weakens the conclusion's
`honestRoundVoters` to plain honesty, which is earlier's conclusion shape.

The two premises are the relative replacements of earlier's post-GST, horizon and
`BelowOneThird` premises; the seed's own gate-off frame discharges them with
`relativeCarrierWindowAt_of_gateOff` and
`gradeFormingMajority_of_admissible_belowOneThird` (both in
`SeedBoundaryConeLeadRun`, which the seed module already imports). -/
theorem namedG1At_preceq_honestPreviousActionCarrier
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    {c : Round} (hc : 1 ≤ c)
    (hwindow : RelativeCarrierWindowAt S rho (c - 1) DecoupledConsensusModel.Protocol.Phase.g1)
    (hmajority : Internal.NamedOutageEntry.GradeFormingMajority S rho c)
    {v : V} (hv : v ∈ rho.honest) {B : Block V}
    (hG1 : namedG1At S rho v c B) :
    ∃ u ∈ rho.honest, Block.Preceq B (actionSGBlockAt S rho u (c - 1)) := by
  have hpredSucc : c - 1 + 1 = c := Nat.sub_add_cancel hc
  have hmaj : Internal.NamedOutageEntry.GradeFormingMajority S rho (c - 1 + 1) := by
    rw [hpredSucc]
    exact hmajority
  have hgrade : DecoupledConsensusModel.Protocol.gradeBool S.E
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc (c - 1 + 1) .g1)
        v).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc (c - 1 + 1) .g1) v).st.core.F
      S.hc.η_SG (c - 1 + 1)
      (DecoupledConsensusModel.Protocol.early S.E S.hc (c - 1 + 1) .g1)
      (DecoupledConsensusModel.Protocol.late S.E S.hc (c - 1 + 1) .g1) B = true := by
    rw [hpredSucc]
    simpa only [namedG1At, PhaseGrades.storeGrade, PhaseGrades.phaseGrade,
      PhaseGrades.readAt] using hG1
  obtain ⟨u, hu, hBu⟩ :=
    relativeGrade_has_roundCarrier S core hwindow hmaj hv hgrade
  exact ⟨u, ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u (c - 1)).mp hu).1, hBu⟩

/-! ## (b) The relative v-to-w grade delivery -/

/-- **The source grade the seed's action read actually carries.** The action
read's selected candidate is not itself graded at the G2 domain read: it is the
active, clipped prefix of the round's G2 freeze root, and that ROOT is what the
domain read grades. This is the first half of
`SGOutputInheritanceRun.honestSupporter_of_nodeQ2`, exposed on its own: the
carrier half of that theorem needs the relative carrier window and the
grade-forming majority, this half needs neither. -/
theorem namedG2At_freezeRoot_of_nodeQ2
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    {v : V} {c : Round} {Q : Block V}
    (hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho v c) c = some Q) :
    ∃ raw : Block V,
      PhaseGrades.storeGrade S.E S.hc
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g2) v).st c .g2 raw = true ∧
      Block.Preceq Q raw := by
  have hread := stateBeforeTime_eq_stateBefore_strictEventIndex
    S core.toNamedScheduleWellFormed (S.a c)
  have hreadv := congrFun hread v
  have hQ' := hQ
  simp only [PhaseGrades.nodeQ2, PhaseGrades.nodeRead,
    NamedProfile.gradeContract, DecoupledConsensusModel.Protocol.frameContract] at hQ'
  unfold actionReadAt NamedActionReads.actionReadAt at hQ'
  rw [hreadv] at hQ'
  obtain ⟨j, raw, -, hj, hfreeze, hQraw⟩ :=
    NamedOutageHistory.JointHistoryProducersTime.q2_capture_at_action_read
      S rho (strictEventIndex rho (S.a c)) v c hQ'
  refine ⟨raw, ?_, hQraw⟩
  have hgrade : DecoupledConsensusModel.Protocol.gradeBool S.E
      (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
      (NamedRun.stateBefore S rho j v).st.core.F S.hc.η_SG c
      (DecoupledConsensusModel.Protocol.early S.E S.hc c .g2)
      (DecoupledConsensusModel.Protocol.late S.E S.hc c .g2) raw = true :=
    (Finset.mem_filter.mp
      (Proofs.Engine.deepest?_mem (by simpa only [DecoupledConsensusModel.Protocol.freezeRoot]
        using hfreeze))).2
  have hjState := Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
    S core.toNamedScheduleWellFormed hj
  simpa only [PhaseGrades.storeGrade, PhaseGrades.phaseGrade,
    PhaseGrades.readAt, ← hjState] using hgrade

/-- **Relative twin of `GradeDeliveryRun.G2_action_imp_G1_action_of_
finalizedPreceq`.** A block relatively graded 2 at one honest reader's G2
domain read is relatively graded 1 at every honest reader's G1 domain read
whose finalized block is below it.

earlier's receiver-local premise is exactly this finalized-ancestor guard, and it
plays the same role here: it is the only fact the cross-reader relay needs
about the target, because every head that covers the block in the source's
interpreted inputs is then above the target's finalized block, hence body
ready there. -/
theorem namedG1At_of_namedG2At_finalizedPreceq
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {c : Round} (hc : 0 < c)
    (hgst : S.E.t_GST ≤ DecoupledConsensusModel.Protocol.early S.E S.hc c .g2)
    (hhor : DecoupledConsensusModel.Protocol.domain S.E S.hc c .g0 ≤ rho.horizon)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) {Q : Block V}
    (hFQ : Block.Preceq
      (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.F Q)
    (hG2 : PhaseGrades.storeGrade S.E S.hc
      (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g2) v).st c .g2 Q = true) :
    namedG1At S rho w c Q := by
  have core : NamedAdmissibleCore S rho := adm.toNamedAdmissibleCore
  have hbelow := crossReaderFinalizedBelow_of_finalitySafety_and_relay
    S adm hsb hgst hhor hv hw (B := Q) (by
      intro sender u root H _hu hcov hconf hfind
      refine Block.preceq_trans hFQ ?_
      simp only [DecoupledConsensusModel.Protocol.localCovers, Protocol.head_covers,
        hconf, hfind] at hcov
      exact hcov)
  have guard := crossReaderBodyReadyGuard_of_finalizedBelow
    S core hc hgst hhor hv hw hbelow
  have delivery := twoCutoffDelivery_of_core S core hgst
  exact storeGrade_g1_of_storeGrade_g2_cross_reader S rho core c delivery hhor
    v w hv hw Q hG2 guard

/-- The finalized block of an honest reader is monotone in the read time. -/
private theorem seedRel_stateBeforeTime_F_mono
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho) (v : V)
    {t t' : Time} (htt' : t ≤ t') :
    Block.Preceq (NamedRun.stateBeforeTime S rho t v).st.core.F
      (NamedRun.stateBeforeTime S rho t' v).st.core.F := by
  have sch := core.toNamedScheduleWellFormed
  rw [NamedOutageClosure.strict_read_eq_index S rho sch.sorted t,
    NamedOutageClosure.strict_read_eq_index S rho sch.sorted t']
  exact Proofs.NamedRuntime.stateBefore_F_mono S rho v
    (NamedOutageClosure.strict_lengths_mono rho htt')


/-- **The form the seed's action-Q2 source feeds.** The action read's selected
candidate is the active, clipped prefix of the round's G2 freeze root, and it is
that ROOT, not the candidate, which the source's G2 domain read grades. So the
delivery is applied to the root and the grade descends to the candidate: the
relative grade is monotone under `Preceq` (`namedG1At_of_preceq`), and the
target's finalized guard for the root follows from the candidate's activity at
the duty read.

With `P:= Q` this is `namedG1At_of_namedG2At_activeAtDutyRead`. -/
theorem namedG1At_of_gradedAncestor_activeAtDutyRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {c : Round} (hc : 0 < c) {d : Slot}
    (hdomainVote : DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1 ≤
      Protocol.vote_time S.E d)
    (hgst : S.E.t_GST ≤ DecoupledConsensusModel.Protocol.early S.E S.hc c .g2)
    (hhor : DecoupledConsensusModel.Protocol.domain S.E S.hc c .g0 ≤ rho.horizon)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) {Q P : Block V}
    (hQP : Block.Preceq Q P)
    (hQactive : Q ∈ PhaseGrades.filteredTree
      (Internal.NamedRecoveryRead.voteDutyRead S rho w d))
    (hG2 : PhaseGrades.storeGrade S.E S.hc
      (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g2) v).st c .g2 P = true) :
    namedG1At S rho w c Q := by
  have hFduty : Block.Preceq
      (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.F Q :=
    NamedOutageClosure.q10_filtered_F hQactive
  have hFQ : Block.Preceq
      (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.F Q := by
    refine Block.preceq_trans ?_ hFduty
    exact seedRel_stateBeforeTime_F_mono S adm.toNamedAdmissibleCore w
      hdomainVote
  have hP := namedG1At_of_namedG2At_finalizedPreceq S adm hsb hc hgst hhor
    hv hw (Block.preceq_trans hFQ hQP) hG2
  exact namedG1At_of_preceq S rho hQP hP

/-! ## (c) The relative anchor covers an active relative grade -/

/-- A relatively graded block is in its reader's own tree at the read that
grades it. A grade has strictly more positive weight than opposing weight, so
it has at least one supporter; that supporter's interpreted head resolves in
the reader's tree and covers the block; and the tree is parent-closed. -/
theorem namedG1At_mem_domainTree
    (S : Setup V) (rho : Run V) {c : Round} {w : V} {Q : Block V}
    (hG1 : namedG1At S rho w c Q) :
    Q ∈ (PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.T := by
  set n := PhaseGrades.readAt S rho
    (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w with hn
  have hgrade : DecoupledConsensusModel.Protocol.gradeBool S.E
      n.st.core.toHealing.gradeView n.st.core.F S.hc.η_SG c
      (DecoupledConsensusModel.Protocol.early S.E S.hc c .g1)
      (DecoupledConsensusModel.Protocol.late S.E S.hc c .g1) Q = true := by
    simpa only [namedG1At, PhaseGrades.storeGrade, PhaseGrades.phaseGrade,
      PhaseGrades.readAt, hn] using hG1
  simp only [DecoupledConsensusModel.Protocol.gradeBool, decide_eq_true_eq] at hgrade
  have hne : (Finset.univ.filter fun s =>
      DecoupledConsensusModel.Protocol.positive n.st.core.toHealing.gradeView
        n.st.core.F S.hc.η_SG c (DecoupledConsensusModel.Protocol.early S.E S.hc c .g1)
        (DecoupledConsensusModel.Protocol.late S.E S.hc c .g1) s Q = true).Nonempty := by
    rcases Finset.eq_empty_or_nonempty (Finset.univ.filter fun s =>
      DecoupledConsensusModel.Protocol.positive n.st.core.toHealing.gradeView
        n.st.core.F S.hc.η_SG c (DecoupledConsensusModel.Protocol.early S.E S.hc c .g1)
        (DecoupledConsensusModel.Protocol.late S.E S.hc c .g1) s Q = true) with hempty | hsome
    · rw [hempty] at hgrade
      simp only [Electorate.weightOf, Finset.sum_empty] at hgrade
      omega
    · exact hsome
  obtain ⟨s, hs⟩ := hne
  have hpos := (Finset.mem_filter.mp hs).2
  simp only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq] at hpos
  obtain ⟨tok, -, -, hcov, -, -⟩ := hpos
  have hcov' : Protocol.head_covers n.st.core.toHealing.gradeView.T Q tok.key
      = true := hcov
  cases hkey : tok.key with
  | none =>
      rw [hkey] at hcov'
      simp [Protocol.head_covers] at hcov'
  | some root =>
      rw [hkey] at hcov'
      cases hfind : Block.find? n.st.core.toHealing.gradeView.T root with
      | none =>
          simp [Protocol.head_covers, hfind] at hcov'
      | some H =>
          simp only [Protocol.head_covers, hfind] at hcov'
          have hHmem : H ∈ n.st.core.T := Proofs.HealingLemmas.find?_mem hfind
          have hQH : Block.Preceq Q H := hcov'
          have hpc := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w
          exact Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2 Q H
            hHmem hQH

/-- **Relative twin of the fresh-anchor block of `secondSlotCone_of_grade2'`.**
A block carrying the relative G1 grade of round `c` at an honest reader's G1
domain read, and still active in that reader's filtered tree at its round-`c`
vote duty, is below the reader's prepared anchor at that duty.

The selection runtime's anchor is not `Protocol.fresh_anchor` of the duty store: it
is the active prefix, in the duty read's own filtered tree, of the round's
frozen relative-G1 root (`voterAnchorAt_cases`). The frozen root is the
deepest graded block of the G1-domain read's tree, so it is above `Q`; the clip
against the duty read's finalized block keeps `Q` below it because `Q` is active
there; and the active prefix of a root dominates every filtered-tree member
below that root. -/
theorem preceq_voterAnchorAt_of_dutyReadGrade
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {c : Round} (hc : 0 < c) {d : Slot}
    (hslo : S.hc.opening_slot c ≤ d)
    (hround : S.hc.round_of d = c)
    (hnext : Protocol.vote_time S.E d ≤ DecoupledConsensusModel.Protocol.opening S.E S.hc (c + 1))
    (hvoteHor : Protocol.vote_time S.E d ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) {Q : Block V}
    (hQgrade : namedG1At S rho w c Q)
    (hQactive : Q ∈ PhaseGrades.filteredTree
      (Internal.NamedRecoveryRead.voteDutyRead S rho w d)) :
    Block.Preceq Q (voterAnchorAt S rho w d) := by
  have hround' : S.hc.round_of
      (S.E.slotOf (Protocol.vote_time S.E d)) = c := by
    simpa only [Proofs.Optimistic.slotOf_vote_time] using hround
  have hdomainVote : DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1 <
      Protocol.vote_time S.E d := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact (Protocol.proposal_time_mono S.E hslo).trans_lt
      (Protocol.proposal_time_lt_vote_time S.E d)
  have hg1Hor : DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1 ≤ rho.horizon :=
    hdomainVote.le.trans hvoteHor
  have hbase := FrameCompleted.frame_phase_completed_in_round
    S rho adm.toNamedAdmissibleCore w hw c hc .g1 (Protocol.vote_time S.E d)
    hdomainVote hnext hg1Hor
  have hbase' :
      (DecoupledConsensusModel.Protocol.readFrame
        (NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E d) w).cache
        (NamedRun.stateBeforeTime S rho
          (Protocol.vote_time S.E d) w).st.core.toHealing c).g1 =
        some ((PhaseGrades.storeRoot S.E S.hc
          (PhaseGrades.readAt S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st c .g1).map
          (fun X => DecoupledConsensusModel.Protocol.clipGrade X
            (NamedRun.stateBeforeTime S rho
              (Protocol.vote_time S.E d) w).st.core.F)) := by
    simpa only [PhaseGrades.storeRoot, PhaseGrades.phaseRoot,
      PhaseGrades.readAt] using hbase
  have hprepared := NamedOutageClosure.frame_phase_prepared_eq
    S rho w c .g1 (Protocol.vote_time S.E d) hround' _ hbase'
  have hreadFrame :
      (DecoupledConsensusModel.Protocol.readFrame
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d).cache
        (Internal.NamedRecoveryRead.voteDutyRead S rho
          w d).st.core.toHealing c).g1 =
        some ((PhaseGrades.storeRoot S.E S.hc
          (PhaseGrades.readAt S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st c .g1).map
          (fun X => DecoupledConsensusModel.Protocol.clipGrade X
            (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.F)) := by
    simpa only [Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom] using hprepared
  obtain ⟨raw, hraw, hQraw⟩ := NamedOutageClosure.q10_freeze_of_graded S.E
    (PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.toHealing.gradeView
    (PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st.core.F
    S.hc.η_SG c (NamedOutageClosure.q10_early_le_late S c .g1)
    (namedG1At_mem_domainTree S rho hQgrade)
    (by
      simpa only [namedG1At, PhaseGrades.storeGrade, PhaseGrades.phaseGrade,
        PhaseGrades.readAt] using hQgrade)
  have hstore : PhaseGrades.storeRoot S.E S.hc
      (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1) w).st c .g1 = some raw := by
    simpa only [PhaseGrades.storeRoot, PhaseGrades.phaseRoot] using hraw
  have hframe :
      (DecoupledConsensusModel.Protocol.readFrame
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d).cache
        (Internal.NamedRecoveryRead.voteDutyRead S rho
          w d).st.core.toHealing c).g1 =
        some (some (DecoupledConsensusModel.Protocol.clipGrade raw
          (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.F)) := by
    simpa only [hstore, Option.map_some] using hreadFrame
  have hFQ : Block.Preceq
      (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.F Q :=
    NamedOutageClosure.q10_filtered_F hQactive
  have hcompat : Block.compatible Q
      (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.F = true := by
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr hFQ
  have hQroot : Block.Preceq Q (DecoupledConsensusModel.Protocol.clipGrade raw
      (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.F) :=
    (NamedOutageClosure.q10_retained_prefix raw
      (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.F Q
      hcompat).mpr hQraw
  obtain ⟨A, hA, hQA⟩ :=
    NamedOutageClosure.q10_activePrefix_dominates hQactive hQroot
  have hroundRead : S.hc.round_of
      (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.s = c := by
    simpa only [Proofs.Optimistic.voteDutyRead_slot] using hround
  change Block.Preceq Q
    (DecoupledConsensusModel.Protocol.anchor S.E S.hc
      (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing
      (S.hc.round_of
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.s)
      (DecoupledConsensusModel.Protocol.readFrame
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d).cache
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing
        (S.hc.round_of
          (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.s)).g1)
  rw [hroundRead, hframe]
  simp only [DecoupledConsensusModel.Protocol.anchor, hA, Option.getD_some]
  exact hQA

/-- The duty-head form the seed consumer uses: a relative grade that is still
active at the duty read is below that duty's prepared vote head. -/
theorem preceq_voterHeadAt_of_dutyReadGrade
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {c : Round} (hc : 0 < c) {d : Slot}
    (hslo : S.hc.opening_slot c ≤ d)
    (hround : S.hc.round_of d = c)
    (hnext : Protocol.vote_time S.E d ≤ DecoupledConsensusModel.Protocol.opening S.E S.hc (c + 1))
    (hvoteHor : Protocol.vote_time S.E d ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) {Q : Block V}
    (hQgrade : namedG1At S rho w c Q)
    (hQactive : Q ∈ PhaseGrades.filteredTree
      (Internal.NamedRecoveryRead.voteDutyRead S rho w d)) :
    Block.Preceq Q (voterHeadAt S rho w d) :=
  Block.preceq_trans
    (preceq_voterAnchorAt_of_dutyReadGrade S adm hc hslo hround hnext hvoteHor
      hw hQgrade hQactive)
    (voterAnchorAt_preceq_voterHeadAt S rho w d)

/-- **The seed entry's contract, end to end.** An honest reader's round-`c`
action selection is below every honest reader's prepared vote head at any
round-`c` duty at which the selected block is still active. This is the
relative replacement of the `Protocol.G2` premise of
`SeedEntryCanonicalRun.secondSlotCone_of_grade2'` together with its delivery
and fresh-anchor steps. -/
theorem preceq_voterHeadAt_of_nodeQ2_activeAtDutyRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {c : Round} (hc : 0 < c) {d : Slot}
    (hslo : S.hc.opening_slot c ≤ d)
    (hround : S.hc.round_of d = c)
    (hnext : Protocol.vote_time S.E d ≤ DecoupledConsensusModel.Protocol.opening S.E S.hc (c + 1))
    (hvoteHor : Protocol.vote_time S.E d ≤ rho.horizon)
    (hgst : S.E.t_GST ≤ DecoupledConsensusModel.Protocol.early S.E S.hc c .g2)
    (hhor : DecoupledConsensusModel.Protocol.domain S.E S.hc c .g0 ≤ rho.horizon)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) {Q : Block V}
    (hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho v c) c = some Q)
    (hQactive : Q ∈ PhaseGrades.filteredTree
      (Internal.NamedRecoveryRead.voteDutyRead S rho w d)) :
    Block.Preceq Q (voterHeadAt S rho w d) := by
  have hdomainVote : DecoupledConsensusModel.Protocol.domain S.E S.hc c .g1 ≤
      Protocol.vote_time S.E d := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact le_of_lt ((Protocol.proposal_time_mono S.E hslo).trans_lt
      (Protocol.proposal_time_lt_vote_time S.E d))
  obtain ⟨raw, hrawGrade, hQraw⟩ :=
    namedG2At_freezeRoot_of_nodeQ2 S adm.toNamedAdmissibleCore hQ
  exact preceq_voterHeadAt_of_dutyReadGrade S adm hc hslo hround hnext hvoteHor
    hw (namedG1At_of_gradedAncestor_activeAtDutyRead S adm hsb hc hdomainVote
      hgst hhor hv hw hQraw hQactive hrawGrade) hQactive

#print axioms namedG1At_preceq_honestPreviousActionCarrier
#print axioms namedG1At_of_namedG2At_finalizedPreceq
#print axioms namedG1At_of_gradedAncestor_activeAtDutyRead
#print axioms namedG1At_mem_domainTree
#print axioms preceq_voterAnchorAt_of_dutyReadGrade
#print axioms namedG2At_freezeRoot_of_nodeQ2
#print axioms preceq_voterHeadAt_of_dutyReadGrade
#print axioms preceq_voterHeadAt_of_nodeQ2_activeAtDutyRead

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
