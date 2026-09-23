module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.FixedHeightRootOpeningFrozenVote
public import DecoupledConsensusProofs.Protocol.ForkChoice.Head.PreparedProposalReadBridge
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeDelivery
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsProducers
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RawProposerSelection
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.Grades.ProposalParent

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.NamedRecoveryRead
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The prepared opening frame -/

private theorem relAnchor_cacheAtRound_align_self
    (c : DecoupledConsensusModel.Protocol.Cache V) (r : Round) :
    DecoupledConsensusModel.Protocol.cacheAtRound (DecoupledConsensusModel.Protocol.alignRound c r) r =
      DecoupledConsensusModel.Protocol.cacheAtRound c r := by
  by_cases h1 : r = c.round
  · rw [show DecoupledConsensusModel.Protocol.alignRound c r = c by
      unfold DecoupledConsensusModel.Protocol.alignRound
      rw [if_pos h1]]
  · by_cases h2 : r = c.round + 1
    · rw [show DecoupledConsensusModel.Protocol.alignRound c r =
        ⟨r, c.next, DecoupledConsensusModel.Protocol.pendingFrame⟩ by
        unfold DecoupledConsensusModel.Protocol.alignRound
        rw [if_neg h1, if_pos h2]]
      subst h2
      simp [DecoupledConsensusModel.Protocol.cacheAtRound]
    · rw [show DecoupledConsensusModel.Protocol.alignRound c r =
        ⟨r, DecoupledConsensusModel.Protocol.pendingFrame, DecoupledConsensusModel.Protocol.pendingFrame⟩ by
        unfold DecoupledConsensusModel.Protocol.alignRound
        rw [if_neg h1, if_neg h2]]
      simp [DecoupledConsensusModel.Protocol.cacheAtRound, h1, h2]

private theorem relAnchor_clip_grade_compatible (g F : Block V) :
    Block.compatible (DecoupledConsensusModel.Protocol.clipGrade g F) F = true := by
  induction g with
  | genesis => simp [DecoupledConsensusModel.Protocol.clipGrade,
      Block.compatible, Protocol.preceq_genesis]
  | node p s root gv gsv ats v ih =>
      simp only [DecoupledConsensusModel.Protocol.clipGrade]
      split
      · assumption
      · exact ih

private theorem relAnchor_clip_grade_keeps (g F : Block V)
    (h : Block.compatible g F = true) :
    DecoupledConsensusModel.Protocol.clipGrade g F = g := by
  cases g with
  | genesis => rfl
  | node p s root gv gsv ats v =>
      simp only [DecoupledConsensusModel.Protocol.clipGrade, h, ↓reduceIte]

private theorem relAnchor_clip_grade_idempotent (g F : Block V) :
    DecoupledConsensusModel.Protocol.clipGrade
        (DecoupledConsensusModel.Protocol.clipGrade g F) F =
      DecoupledConsensusModel.Protocol.clipGrade g F :=
  relAnchor_clip_grade_keeps _ _
    (relAnchor_clip_grade_compatible g F)

private theorem relAnchor_clip_result_idempotent
    (F : Block V) (x : Option (Option (Block V))) :
    DecoupledConsensusModel.Protocol.clipResult F (DecoupledConsensusModel.Protocol.clipResult F x) =
      DecoupledConsensusModel.Protocol.clipResult F x := by
  cases x with
  | none => rfl
  | some y =>
      cases y with
      | none => rfl
      | some B =>
          simp only [DecoupledConsensusModel.Protocol.clipResult, Option.map_some]
          rw [relAnchor_clip_grade_idempotent]

private theorem relAnchor_clip_frame_idempotent
    (F : Block V) (f : DecoupledConsensusModel.Protocol.Frame V) :
    DecoupledConsensusModel.Protocol.clipFrame F (DecoupledConsensusModel.Protocol.clipFrame F f) =
      DecoupledConsensusModel.Protocol.clipFrame F f := by
  cases f
  simp only [DecoupledConsensusModel.Protocol.clipFrame]
  congr 1 <;> exact relAnchor_clip_result_idempotent F _

private theorem relAnchor_preparedFrame_g1_eq_storeRoot_at_opening
    (S : Setup V) (rho : Run V) (core : NamedAdmissibleCore S rho)
    (w : V) (hw : w ∈ rho.honest) (r : Round) (hr : 0 < r) (t : Time)
    (hround : S.hc.round_of (S.E.slotOf t) = r)
    (hopen : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 = t)
    (hhor : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 ≤ rho.horizon) :
    (DecoupledConsensusModel.Protocol.readFrame
      (NamedActionReads.confirmationReadAt S rho w t).cache
      (NamedActionReads.confirmationReadAt S rho w t).st.core.toHealing r).g1 =
      some ((PhaseGrades.storeRoot S.E S.hc
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st r .g1).map
        (fun X => DecoupledConsensusModel.Protocol.clipGrade X
          (NamedActionReads.confirmationReadAt S rho w t).st.core.F)) := by
  let before := NamedRun.stateBeforeTime S rho t w
  let read := NamedActionReads.confirmationReadFrom S before t
  have hnotg2 : t ≠ DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2 := by
    intro heq
    exact (ne_of_gt (NamedOutageClosure.q10_domain_g2_lt_domain_g1 S r))
      (hopen.trans heq)
  have hnotg0 : t ≠ DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0 := by
    intro heq
    have h10 : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 <
        DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0 := by
      unfold DecoupledConsensusModel.Protocol.domain
      simp only [DecoupledConsensusModel.Protocol.Phase.domainOffset, zero_mul, one_mul, add_zero]
      exact lt_add_of_pos_right _ S.E.Δ_pos
    exact (ne_of_gt h10) (hopen.trans heq).symm
  have hrawNone : DecoupledConsensusModel.Protocol.phaseResult
        (DecoupledConsensusModel.Protocol.cacheAtRound before.cache r) .g1 = none := by
    by_contra hnone
    obtain ⟨root, hroot⟩ := Option.ne_none_iff_exists'.mp hnone
    rcases NamedCacheProvenance.completed_phase_before_read S rho core.sorted
      core.nodup t w r .g1 root hroot with hzero | hdone
    · exact (Nat.ne_of_gt hr) hzero.1
    · obtain ⟨j, u, hj, hu, hdom, hvalue⟩ := hdone
      have hlt : t < t := by
        calc
          t = DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 := hopen.symm
          _ = u := hdom.symm
          _ < t := hu
      exact (lt_irrefl t) hlt
  let aligned := DecoupledConsensusModel.Protocol.alignRound before.cache r
  have halign : DecoupledConsensusModel.Protocol.cacheAtRound aligned r =
      DecoupledConsensusModel.Protocol.cacheAtRound before.cache r := by
    exact relAnchor_cacheAtRound_align_self before.cache r
  have halignedNone : DecoupledConsensusModel.Protocol.phaseResult
        (DecoupledConsensusModel.Protocol.cacheAtRound aligned r) .g1 = none := by
    rw [halign]
    exact hrawNone
  have hcomplete : DecoupledConsensusModel.Protocol.phaseResult
        (DecoupledConsensusModel.Protocol.completeFrame S.E S.hc before.st.core.toHealing
          r t (DecoupledConsensusModel.Protocol.cacheAtRound aligned r)) .g1 =
      some (PhaseGrades.storeRoot S.E S.hc
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st r .g1) := by
    have hG1 : (DecoupledConsensusModel.Protocol.cacheAtRound aligned r).g1 = none :=
      halignedNone
    cases hG2 : (DecoupledConsensusModel.Protocol.cacheAtRound aligned r).g2 <;>
      cases hG0 : (DecoupledConsensusModel.Protocol.cacheAtRound aligned r).g0 <;>
        simp [DecoupledConsensusModel.Protocol.completeFrame, DecoupledConsensusModel.Protocol.completeOne,
          DecoupledConsensusModel.Protocol.putPhase, DecoupledConsensusModel.Protocol.phaseResult, hG2,
          hG0, hG1, hnotg2, hnotg0, before, hopen,
          PhaseGrades.storeRoot, PhaseGrades.phaseRoot,
          Protocol.Store.toHealing]
  have hframe :
      (DecoupledConsensusModel.Protocol.readFrame read.cache read.st.core.toHealing r).g1 =
        some ((PhaseGrades.storeRoot S.E S.hc
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st r .g1).map
          (fun X => DecoupledConsensusModel.Protocol.clipGrade X read.st.core.F)) := by
    dsimp only [read, NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache]
    have halignedRound : aligned.round = r := by
      dsimp only [aligned]
      unfold DecoupledConsensusModel.Protocol.alignRound
      split_ifs with h
      · exact h.symm
      · rfl
      · rfl
    have hcacheTick :
        DecoupledConsensusModel.Protocol.cacheAtRound
            (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc before.st.core.toHealing
              t before.cache) r =
          DecoupledConsensusModel.Protocol.clipFrame before.st.core.F
            (DecoupledConsensusModel.Protocol.completeFrame S.E S.hc
              before.st.core.toHealing r t aligned.current) := by
      unfold DecoupledConsensusModel.Protocol.onPhaseTick
      rw [hround]
      simp [aligned, DecoupledConsensusModel.Protocol.cacheAtRound, halignedRound,
        DecoupledConsensusModel.Protocol.clipCache, Protocol.Store.toHealing]
    change (DecoupledConsensusModel.Protocol.readFrame
      (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc before.st.core.toHealing
        t before.cache) before.st.core.toHealing r).g1 = _
    unfold DecoupledConsensusModel.Protocol.readFrame
    change (DecoupledConsensusModel.Protocol.clipFrame before.st.core.F
      (DecoupledConsensusModel.Protocol.cacheAtRound
        (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc before.st.core.toHealing
          t before.cache) r)).g1 = _
    rw [hcacheTick, relAnchor_clip_frame_idempotent]
    have hcache : DecoupledConsensusModel.Protocol.cacheAtRound aligned r = aligned.current := by
      simp [DecoupledConsensusModel.Protocol.cacheAtRound, halignedRound]
    have hcomplete' := hcomplete
    rw [hcache] at hcomplete'
    have hcomplete'' :
        (DecoupledConsensusModel.Protocol.completeFrame S.E S.hc before.st.core.toHealing
          r t aligned.current).g1 =
        some (PhaseGrades.storeRoot S.E S.hc
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st r .g1) := by
      simpa only [DecoupledConsensusModel.Protocol.phaseResult] using hcomplete'
    simp only [DecoupledConsensusModel.Protocol.clipFrame, DecoupledConsensusModel.Protocol.clipResult]
    rw [hcomplete'']
    rfl
  simpa only [before, read, NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom] using hframe


/-! ## Store and read bridges -/



/-- Clock staging changes no fork-choice field, so the prepared proposer read
has the strict read's filtered tree. -/
theorem relativeAnchor_proposerReadAt_filteredTree_eq
    (S : Setup V) (rho : Run V) (s : Slot) :
    Protocol.get_filtered_block_tree
        (proposerReadAt S rho s).st.core.toHealing.toFG =
      Protocol.get_filtered_block_tree
        (NamedRun.stateBeforeTime S rho (Protocol.proposal_time S.E s)
          (S.E.proposer s)).st.core.toHealing.toFG := by
  simp only [proposerReadAt, NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
    Protocol.Store.toHealing, Protocol.get_filtered_block_tree,
    Protocol.get_filtered_block_tree_from, Protocol.get_fg_root,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable]
  rfl

/-! ## T1: the prepared opening frame's G1 root is above the fixed root -/

set_option maxHeartbeats 400000 in
/-- The honest opening proposer's prepared frame has a non-empty G1 result, and
that frozen relative-G1 root is above the fixed justification root. -/
theorem proposerFrameG1_of_fixedRootLock
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {w : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho H w read)
    {q : Round} (hqTwo : 2 ≤ q)
    (hforms : NamedGradeFormsAt S rho (q - 1)
      (rho.storeBeforeTime S w read).J)
    (hwindow : ∀ v ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho v (S.a (q - 1))
        (rho.storeBeforeTime S w read).J)
    (hdomainWindow : ∀ v ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho v (domain S.E S.hc q .g2)
        (rho.storeBeforeTime S w read).J)
    (hpostRead : S.E.t_GST ≤ read)
    (hpostPreviousAction : S.E.t_GST ≤ S.a (q - 1))
    (hcut : S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon)
    (hactionHor : S.a q ≤ rho.horizon)
    (hactiveAtAction : ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S w read).J ∈
        Protocol.get_filtered_block_tree (healStoreAt S rho v q).toFG)
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hproposalDelay : read + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hproposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hproposalCap : honestHMaxAt S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) ≤ H) :
    ∃ root : Block V,
      (DecoupledConsensusModel.Protocol.readFrame
          (proposerReadAt S rho (S.hc.opening_slot q)).cache
          (proposerReadAt S rho
            (S.hc.opening_slot q)).st.core.toHealing q).g1 =
        some (some root) ∧
      Block.Preceq (rho.storeBeforeTime S w read).J root := by
  have hq : 0 < q := (by decide : 0 < 2).trans_le hqTwo
  have hopen : domain S.E S.hc q .g1 =
      Protocol.proposal_time S.E (S.hc.opening_slot q) := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    rfl
  have hdomainHor : domain S.E S.hc q .g1 ≤ rho.horizon := by
    rw [hopen]
    exact hproposalHor
  have hround : S.hc.round_of (S.E.slotOf
      (Protocol.proposal_time S.E (S.hc.opening_slot q))) = q := by
    simpa only [Proofs.Optimistic.slotOf_proposal_time] using
      (round_of_opening_slot_eq S.hc q)
  have hJG1 : namedG1At S rho (S.E.proposer (S.hc.opening_slot q)) q
      (rho.storeBeforeTime S w read).J :=
    namedG1At_fixedRootTarget_of_retainedPreviousGrade S adm hfb hfix hqTwo
      hforms hwindow hdomainWindow hpostRead hpostPreviousAction hcut
      hactionHor hactiveAtAction hprop hproposalDelay hproposalHor hproposalCap
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  obtain ⟨hrootPre, -⟩ :=
    fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
      S adm hsb hfix hprop hpostRead hproposalDelay hproposalHor hproposalCap
  have hJstrict : (rho.storeBeforeTime S w read).J ∈
      Protocol.get_filtered_block_tree
        (NamedRun.stateBeforeTime S rho
          (Protocol.proposal_time S.E (S.hc.opening_slot q))
          (S.E.proposer (S.hc.opening_slot q))).st.core.toHealing.toFG := by
    rw [← hrootPre]
    simpa only [Run.storeBeforeTime, Protocol.NamedStore.toHealing] using
      named_fgRoot_mem_filtered_stateBeforeTime S rho
        (Protocol.proposal_time S.E (S.hc.opening_slot q))
        (S.E.proposer (S.hc.opening_slot q))
  have hJdomain : (rho.storeBeforeTime S w read).J ∈
      Protocol.get_filtered_block_tree
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g1)
          (S.E.proposer (S.hc.opening_slot q))).st.core.toHealing.toFG := by
    rw [hopen]
    exact hJstrict
  have hJmemT : (rho.storeBeforeTime S w read).J ∈
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g1)
        (S.E.proposer (S.hc.opening_slot q))).st.core.T :=
    mem_T_of_mem_filteredTree hJdomain
  have hgrade : DecoupledConsensusModel.Protocol.gradeBool S.E
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g1)
        (S.E.proposer (S.hc.opening_slot q))).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g1)
        (S.E.proposer (S.hc.opening_slot q))).st.core.F
      S.hc.η_SG q (early S.E S.hc q .g1) (late S.E S.hc q .g1)
      (rho.storeBeforeTime S w read).J = true := by
    simpa only [namedG1At, PhaseGrades.storeGrade, PhaseGrades.phaseGrade,
      PhaseGrades.readAt] using hJG1
  obtain ⟨raw, hraw, hJraw⟩ := NamedOutageClosure.q10_freeze_of_graded S.E
    (NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g1)
      (S.E.proposer (S.hc.opening_slot q))).st.core.toHealing.gradeView
    (NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g1)
      (S.E.proposer (S.hc.opening_slot q))).st.core.F
    S.hc.η_SG q (NamedOutageClosure.q10_early_le_late S q .g1) hJmemT hgrade
  have hstoreRoot : PhaseGrades.storeRoot S.E S.hc
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g1)
        (S.E.proposer (S.hc.opening_slot q))).st q .g1 = some raw := by
    simpa only [PhaseGrades.storeRoot, PhaseGrades.phaseRoot] using hraw
  have hframeStore := relAnchor_preparedFrame_g1_eq_storeRoot_at_opening
    S rho adm.toNamedAdmissibleCore (S.E.proposer (S.hc.opening_slot q)) hprop
    q hq (Protocol.proposal_time S.E (S.hc.opening_slot q)) hround hopen
    hdomainHor
  have hframe :
      (DecoupledConsensusModel.Protocol.readFrame
          (proposerReadAt S rho (S.hc.opening_slot q)).cache
          (proposerReadAt S rho
            (S.hc.opening_slot q)).st.core.toHealing q).g1 =
        some (some (DecoupledConsensusModel.Protocol.clipGrade raw
          (proposerReadAt S rho (S.hc.opening_slot q)).st.core.F)) := by
    simpa only [proposerReadAt, hstoreRoot, Option.map_some] using hframeStore
  have hFJ : Block.Preceq
      (proposerReadAt S rho (S.hc.opening_slot q)).st.core.F
      (rho.storeBeforeTime S w read).J :=
    NamedOutageClosure.q10_filtered_F hJstrict
  have hcompat : Block.compatible (rho.storeBeforeTime S w read).J
      (proposerReadAt S rho (S.hc.opening_slot q)).st.core.F = true := by
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr hFJ
  refine ⟨DecoupledConsensusModel.Protocol.clipGrade raw
    (proposerReadAt S rho (S.hc.opening_slot q)).st.core.F, hframe, ?_⟩
  exact (NamedOutageClosure.q10_retained_prefix raw
    (proposerReadAt S rho (S.hc.opening_slot q)).st.core.F
    (rho.storeBeforeTime S w read).J hcompat).mpr hJraw

/-! ## T2: the frame anchor and its three properties -/

set_option maxHeartbeats 400000 in
/-- The selection protocol's opening anchor: the frame anchor of the honest
proposer's prepared read carries the relative G1 grade of round `q`, sits above
the fixed justification root, and is active in the proposer's filtered tree. -/
theorem relativeAnchor_of_fixedRootLock
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {w : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho H w read)
    {q : Round} (hqTwo : 2 ≤ q)
    (hforms : NamedGradeFormsAt S rho (q - 1)
      (rho.storeBeforeTime S w read).J)
    (hwindow : ∀ v ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho v (S.a (q - 1))
        (rho.storeBeforeTime S w read).J)
    (hdomainWindow : ∀ v ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho v (domain S.E S.hc q .g2)
        (rho.storeBeforeTime S w read).J)
    (hpostRead : S.E.t_GST ≤ read)
    (hpostPreviousAction : S.E.t_GST ≤ S.a (q - 1))
    (hcut : S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon)
    (hactionHor : S.a q ≤ rho.horizon)
    (hactiveAtAction : ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S w read).J ∈
        Protocol.get_filtered_block_tree (healStoreAt S rho v q).toFG)
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hproposalDelay : read + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hproposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hproposalCap : honestHMaxAt S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) ≤ H) :
    namedG1At S rho (S.E.proposer (S.hc.opening_slot q)) q
        (nodeAnchor S (proposerReadAt S rho (S.hc.opening_slot q)) q) ∧
      Block.Preceq (rho.storeBeforeTime S w read).J
        (nodeAnchor S (proposerReadAt S rho (S.hc.opening_slot q)) q) ∧
      nodeAnchor S (proposerReadAt S rho (S.hc.opening_slot q)) q ∈
        Protocol.get_filtered_block_tree
          (proposerReadAt S rho
            (S.hc.opening_slot q)).st.core.toHealing.toFG := by
  have hq : 0 < q := (by decide : 0 < 2).trans_le hqTwo
  obtain ⟨root, hframe, hJroot⟩ :=
    proposerFrameG1_of_fixedRootLock S adm hfb hfix hqTwo hforms hwindow
      hdomainWindow hpostRead hpostPreviousAction hcut hactionHor
      hactiveAtAction hprop hproposalDelay hproposalHor hproposalCap
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  obtain ⟨hrootPre, -⟩ :=
    fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
      S adm hsb hfix hprop hpostRead hproposalDelay hproposalHor hproposalCap
  have hJtree : (rho.storeBeforeTime S w read).J ∈
      Protocol.get_filtered_block_tree
        (proposerReadAt S rho
          (S.hc.opening_slot q)).st.core.toHealing.toFG := by
    rw [relativeAnchor_proposerReadAt_filteredTree_eq, ← hrootPre]
    simpa only [Run.storeBeforeTime, Protocol.NamedStore.toHealing] using
      named_fgRoot_mem_filtered_stateBeforeTime S rho
        (Protocol.proposal_time S.E (S.hc.opening_slot q))
        (S.E.proposer (S.hc.opening_slot q))
  obtain ⟨A, hactive, hJA⟩ :=
    NamedOutageClosure.activePrefix_covers hJtree hJroot
  have hanchorEq : nodeAnchor S (proposerReadAt S rho (S.hc.opening_slot q)) q
      = A :=
    GradeDeliveryRun.nodeAnchor_eq_of_activePrefix_some S
      (proposerReadAt S rho (S.hc.opening_slot q))
      (by simpa only [DecoupledConsensusModel.Protocol.phaseResult] using hframe) hactive
  have hrootG1 : namedG1At S rho (S.E.proposer (S.hc.opening_slot q)) q root :=
    namedG1At_of_preparedOpeningFrame S adm hq hprop hproposalHor hframe
  have hAroot : Block.Preceq A root := by
    unfold DecoupledConsensusModel.Protocol.activePrefix at hactive
    exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).2
  refine ⟨?_, ?_, ?_⟩
  · rw [hanchorEq]
    exact namedG1At_of_preceq S rho hAroot hrootG1
  · rw [hanchorEq]
    exact hJA
  · rw [hanchorEq]
    exact NamedProposalParent.activePrefix_mem _ root A hactive

/-! ## T3: the two anchor consumers over the relative anchor

Both producers below take the relative anchor facts of T2 in place of the
absolute `hanchor: Protocol.fresh_anchor … = some A`.

The parent proof uses the public common action ceiling. The ceiling is an
honest action carrier, bounds every honest action carrier and every relative G1
block, and has an honest vote cone. Together with the frame anchor's filtered
membership and the fixed-root target data, these facts populate the prepared
parent candidate directly. The proof preserves `Preceq`; it does not identify
the relative anchor with an absolute fresh anchor.
-/

set_option maxHeartbeats 400000 in
/-- The two opening parent ceilings, with the absolute anchor premise replaced
by the relative frame-anchor facts. -/
theorem fixedHeightJustificationRootOpeningParentRun_of_fixedRootLock_relative
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {w : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho H w read)
    {q : Round} {A : Block V} (hqTwo : 2 ≤ q)
    (hforms : NamedGradeFormsAt S rho (q - 1)
      (rho.storeBeforeTime S w read).J)
    (hwindow : ∀ v ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho v (S.a (q - 1))
        (rho.storeBeforeTime S w read).J)
    (_hdomainWindow : ∀ v ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho v (domain S.E S.hc q .g2)
        (rho.storeBeforeTime S w read).J)
    (_hactiveAtAction : ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S w read).J ∈
        Protocol.get_filtered_block_tree (healStoreAt S rho v q).toFG)
    (hlock : SGTargetOpeningConeRootLock S rho H (q - 1)
      (S.hc.opening_slot q - 1))
    (hpostRead : S.E.t_GST ≤ read)
    (hproposalDelay : read + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hproposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hproposalCap : honestHMaxAt S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) ≤ H)
    (hpostCone : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot q - 1))
    (hpostPreviousAction : S.E.t_GST ≤ S.a (q - 1))
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (_hAanchor : nodeAnchor S (proposerReadAt S rho (S.hc.opening_slot q)) q = A)
    (hAG1 : namedG1At S rho (S.E.proposer (S.hc.opening_slot q)) q A)
    (hAfiltered : A ∈ Protocol.get_filtered_block_tree
      (proposerReadAt S rho (S.hc.opening_slot q)).st.core.toHealing.toFG)
    (hJA : Block.Preceq (rho.storeBeforeTime S w read).J A) :
    FixedHeightRootOpeningParentRun S rho q := by
  have hq : 0 < q := (by decide : 0 < 2).trans_le hqTwo
  let fixed := rho.storeBeforeTime S w read
  let pre := rho.storeBeforeTime S
    (S.E.proposer (S.hc.opening_slot q))
    (Protocol.proposal_time S.E (S.hc.opening_slot q))
  let source := Protocol.proposerDutyStore S rho (S.hc.opening_slot q)
  obtain ⟨target, htarget⟩ :=
    fixedRoot_preparedTargetData_of_fixedRoot_abstract
      S adm hfb hfix fixed pre rfl rfl hprop hpostRead hproposalDelay
        hproposalHor hproposalCap
  obtain ⟨C, vC, hvC, hCvC, hupper, hcone, hbelow⟩ :=
    fixedRoot_namedG1CommonCeiling_public S adm hcom hfb hfix hqTwo hforms
      hwindow hlock hpostRead hproposalDelay hproposalHor hproposalCap
        hpostPreviousAction
  have hAC : Block.Preceq A C := hbelow hprop hAG1
  have hrootC : Block.Preceq
      (Protocol.get_fg_root pre.toHealing.toFG) C := by
    rw [htarget.rootAtProposal, htarget.targetErase]
    exact Block.preceq_trans (by simpa only [fixed] using hJA) hAC
  have hAfilteredSource : A ∈
      Protocol.get_filtered_block_tree source.toHealing.toFG := by
    simpa only [source, Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
      proposerReadAt, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Protocol.NamedStore.toHealing] using hAfiltered
  have hdata : FixedRootPreparedParentCandidate
      S rho H q w read A target C C vC fixed pre source :=
    { targetErase := htarget.targetErase
      targetRun := htarget.targetRun
      targetHeight := htarget.targetHeight
      targetHeightPositive := htarget.targetHeightPositive
      actionWitnessHonest := hvC
      actionCeilingEq := hCvC
      ceilingUpper := hupper
      ceilingCone := hcone
      ceilingRoot := hrootC
      ceilingChoice := Or.inr rfl
      anchorFiltered := hAfilteredSource
      rootAtProposal := htarget.rootAtProposal
      hMaxAtProposal := htarget.hMaxAtProposal }
  have hcut : S.hc.Γ_neg1 S.E.Δ ((q - 1) + 1) ≤ rho.horizon := by
    rw [Nat.sub_add_cancel hq]
    exact (le_of_lt
      (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos q)).trans
      (by simpa only [Protocol.Γ_0_eq_proposal_time] using hproposalHor)
  have hparent := fixedRoot_preparedParent_of_candidate_abstract
    S adm hcom hfb fixed pre source rfl rfl hq hpostCone hproposalHor
      hpostPreviousAction hprop hcut hdata
  exact
    { actionTargetParent := fun v hv =>
        Block.preceq_trans (hupper v hv) hparent
      liveG1Parent := fun x hx B hG1 =>
        Block.preceq_trans (hbelow hx hG1) hparent }

set_option maxHeartbeats 400000 in
/-- The frozen opening-vote comparison at the relative frame anchor, for every
honest opening committee member. -/
theorem openingFrozenVotes_of_fixedJustificationRootLock_relative
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {w : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho H w read)
    {q : Round} {A : Block V} {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot q) = some P)
    (hqTwo : 2 ≤ q)
    (hforms : NamedGradeFormsAt S rho (q - 1)
      (rho.storeBeforeTime S w read).J)
    (hwindow : ∀ v ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho v (S.a (q - 1))
        (rho.storeBeforeTime S w read).J)
    (hdomainWindow : ∀ v ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho v (domain S.E S.hc q .g2)
        (rho.storeBeforeTime S w read).J)
    (hactiveAtAction : ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S w read).J ∈
        Protocol.get_filtered_block_tree (healStoreAt S rho v q).toFG)
    (hlock : SGTargetOpeningConeRootLock S rho H (q - 1)
      (S.hc.opening_slot q - 1))
    (hpostRead : S.E.t_GST ≤ read)
    (hproposalDelay : read + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hvoteDelay : read + S.E.Δ ≤
      Protocol.vote_time S.E (S.hc.opening_slot q))
    (hconfirmationDelay : read + S.E.Δ ≤
      Protocol.confirmation_time S.E (S.hc.opening_slot q))
    (hconfirmationHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hconfirmationCap : honestHMaxAt S rho
      (Protocol.confirmation_time S.E (S.hc.opening_slot q)) ≤ H)
    (hpostSource : S.E.t_GST ≤ Protocol.proposal_time S.E
      (S.hc.opening_slot q - 1))
    (hpostCone : S.E.t_GST ≤ Protocol.vote_time S.E
      (S.hc.opening_slot q - 1))
    (hpostPreviousAction : S.E.t_GST ≤ S.a (q - 1))
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hAanchor : nodeAnchor S (proposerReadAt S rho (S.hc.opening_slot q)) q = A)
    (hAG1 : namedG1At S rho (S.E.proposer (S.hc.opening_slot q)) q A)
    (hAfiltered : A ∈ Protocol.get_filtered_block_tree
      (proposerReadAt S rho (S.hc.opening_slot q)).st.core.toHealing.toFG)
    (hJA : Block.Preceq (rho.storeBeforeTime S w read).J A)
    (_of_pivotTransfer : ∀ v ∈ rho.honest,
      NamedProposalPivotSuffixTransfer S rho (S.hc.opening_slot q) A v P)
    (_of_frozenSuffix : ∀ v ∈ rho.honest, ∀ u,
      u ∈ Protocol.voter_view S.E
        (voteDutyRead S rho v (S.hc.opening_slot q)).st.core.toHealing.toFG.toSG.toGoldfishStore
        (S.hc.opening_slot q) →
      u ∉ P.erase.gf_votes.toFinset →
      Protocol.equivocates P.erase.gf_votes.toFinset u.val_index = true) :
    ∀ v ∈ rho.honest, v ∈ S.E.committee (S.hc.opening_slot q) →
      NamedSGOpeningFrozenVoteAt S rho (S.hc.opening_slot q - 1) A v P := by
  have hq : 0 < q := (by decide : 0 < 2).trans_le hqTwo
  have hproposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon :=
    (Protocol.proposal_time_le_confirmation_time S.E
      (S.hc.opening_slot q)).trans hconfirmationHor
  have hproposalCap : honestHMaxAt S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) ≤ H :=
    (honestHMaxAt_mono S adm.toNamedScheduleWellFormed
      (Protocol.proposal_time_le_confirmation_time S.E
        (S.hc.opening_slot q))).trans hconfirmationCap
  have hparents := fixedHeightJustificationRootOpeningParentRun_of_fixedRootLock_relative
    S adm hcom hfb hfix hqTwo hforms hwindow hdomainWindow hactiveAtAction hlock
    hpostRead hproposalDelay hproposalHor hproposalCap hpostCone
    hpostPreviousAction hprop hAanchor hAG1 hAfiltered hJA
  have hAparent : Block.Preceq A
      (proposedParent S rho (S.hc.opening_slot q)) :=
    hparents.liveG1Parent (S.E.proposer (S.hc.opening_slot q)) hprop A hAG1
  exact openingFrozenVotes_of_fixedJustificationRootParentData
    S adm hcom hfb hfix hP hq hpostRead hproposalDelay hvoteDelay
    hconfirmationDelay hconfirmationHor hconfirmationCap hpostSource
    hpostPreviousAction hprop hJA hAparent hparents
    _of_pivotTransfer _of_frozenSuffix

#print axioms fixedHeightJustificationRootOpeningParentRun_of_fixedRootLock_relative
#print axioms openingFrozenVotes_of_fixedJustificationRootLock_relative

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
