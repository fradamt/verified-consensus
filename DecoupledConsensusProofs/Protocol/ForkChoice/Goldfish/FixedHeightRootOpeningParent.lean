module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.FixedHeightRootAdmission
public import DecoupledConsensusProofs.Objects.SGTargetG1Concentration
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryCapturedSlotInterval
public import DecoupledConsensusProofs.Protocol.Store.RecoveryG1AfterCutoffPersistence
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGProposalLifecycle
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGTargetCanonicalityFixedRoot
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedCeilingStep

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Fixed-height opening-parent ceilings

At the opening after a fixed-root Claim-1 round, the honest proposal parent
captures every preceding honest action target and every live next-round G1
block. The proof relays action targets to the proposal read and retains them
with the exact fixed root and one-step height cap. Claim 1 and Claim 3 then
control the proposal fork-choice walk.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.NamedRecoveryRead
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open Proofs.Optimistic
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]





/-
/-- An honest action target is active at a later honest proposal read when the
proposal store has the exact common FG root and the one-step height cap.

The source target is relayed as an accepted block. The common root, which is
active at the proposal read, supplies the finalized-history guard needed by the
relay theorem. -/
theorem actionSGBlockAt_mem_filtered_proposerDutyStore_of_gradeFormsAt_exactFGRoot_heightCap
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {r: Round} {J: Block V} (hforms: GradeFormsAt S rho r J)
    {v: V} (hv: v ∈ rho.honest)
    {s: Slot} (hprop: S.E.proposer s ∈ rho.honest)
    (hproposalHor: Protocol.proposal_time S.E s ≤ rho.horizon)
    (hpost: S.E.t_GST ≤ S.a r)
    (hdelay: S.a r + S.E.Δ ≤ Protocol.proposal_time S.E s)
    (hroot: Protocol.get_fg_root
      (Protocol.proposerDutyStore S rho s).toHealing.toFG = J)
    (hcap: (Protocol.proposerDutyStore S rho s).h_max ≤
      (derived_state S.E S.cfg J).h + 1):
    actionSGBlockAt S rho v r ∈ Protocol.get_filtered_block_tree
      (Protocol.proposerDutyStore S rho s).toHealing.toFG:= by
  let p:= S.E.proposer s
  let read:= Protocol.proposal_time S.E s
  let pre:= rho.storeBeforeTime S p read
  let duty:= Protocol.proposerDutyStore S rho s
  let C:= actionSGBlockAt S rho v r
  have hJC: Block.Preceq J C:= by
    simpa only [C] using preceq_actionSGBlockAt_of_gradeFormsAt S hforms hv
  have hCsource: C ∈ (rho.storeBeforeTime S v (S.a r)).T:= by
    simpa only [C] using
      actionSGBlockAt_mem_storeBeforeTime_of_gradeFormsAt S adm hforms hv
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node p) pre:= by
    simpa only [pre, p, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed read p)
  have hrootPre: Protocol.get_fg_root pre.toHealing.toFG = J:= by
    simpa only [duty, Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
      pre, p, read] using hroot
  have hJactive: J ∈ Protocol.get_filtered_block_tree pre.toHealing.toFG:= by
    rw [← hrootPre]
    exact fgRoot_mem_filtered_depReachable S.E S.hc S.cfg (S.node p) hdep
  have hCpre: C ∈ pre.T:= by
    rcases block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTime
        S adm.toScheduleWellFormed v (S.a r) hCsource with
      hgen | ⟨i, t, hacc, ht⟩
    · rw [hgen]
      exact (Protocol.genesis_mem_and_stamp_storeBeforeTime S
        adm.toScheduleWellFormed p read read).1
    · have hCpos: 0 < C.slot:=
        Nat.zero_lt_of_lt
          (Protocol.parent_slot_lt_of_acceptsAt_block S hacc)
      have hFhist: Protocol.BlockFinalizedBelowAtDeliveriesBefore
          S rho p C (S.a r + S.E.Δ):=
        finalizedBelowAtDeliveriesBefore_of_filteredAtLaterRead
          S adm hdelay hJactive hJC
      have hadmit: Protocol.AdmittedBefore S rho p C
          (S.a r + S.E.Δ):=
        Protocol.block_admittedBefore_of_accepted_after_cutoff
          S adm hv hprop hCpos hacc ht hpost rfl
            (le_trans hdelay hproposalHor) hFhist
      exact (Protocol.admittedBefore_mem_and_stamp_at S
        adm.toScheduleWellFormed hadmit hdelay).1
  have hcapPre: pre.h_max ≤ (derived_state S.E S.cfg J).h + 1:= by
    simpa only [duty, Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
      pre, p, read] using hcap
  have hfiltered: C ∈
      Protocol.get_filtered_block_tree pre.toHealing.toFG:=
    mem_filtered_of_mem_tree_of_exactFGRoot_heightCap
      S.E S.hc S.cfg (S.node p) hdep hCpre hrootPre hJC hcapPre
  simpa only [C, duty, Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
    pre, p, read] using hfiltered
-/


/-
/-- The two callback-free parent ceilings needed by the fixed-root opening
lifecycle. -/
structure FixedHeightRootOpeningParentRun
    (S: Setup V) (rho: Run V) (q: Round): Prop where
  actionTargetParent: ∀ v ∈ rho.honest,
    Block.Preceq (actionSGBlockAt S rho v (q - 1))
      (Protocol.proposedParent S rho (S.hc.opening_slot q))
  liveG1Parent: ∀ w ∈ rho.honest, ∀ B,
    Protocol.G1 S.E (gradeViewAt S rho w q) S.hc q B = true →
    Block.Preceq B
      (Protocol.proposedParent S rho (S.hc.opening_slot q))
-/



omit [Fintype V] in
private theorem fixedRoot_confirmation_localCovers_mono
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
private theorem fixedRoot_confirmation_positive_mono
    {A B : Block V} (hAB : Block.Preceq A B)
    (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    (early late : Time) (v : V)
    (hB : DecoupledConsensusModel.Protocol.positive gv F eta r early late v B = true) :
    DecoupledConsensusModel.Protocol.positive gv F eta r early late v A = true := by
  simp only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq] at hB ⊢
  rcases hB with ⟨u, hu, hmax, hcov, hclean, hlate⟩
  refine ⟨u, hu, hmax, fixedRoot_confirmation_localCovers_mono hAB hcov,
    hclean, ?_⟩
  intro x hx hlt
  exact fixedRoot_confirmation_localCovers_mono hAB (hlate x hx hlt)

omit [Fintype V] in
private theorem fixedRoot_confirmation_opposing_mono
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
    exact hnot (fixedRoot_confirmation_localCovers_mono hAB hcov)
  · exact Or.inr ⟨x, hx, y, hy, hmax, heq, hkey⟩

private theorem fixedRoot_confirmation_phaseGrade_mono
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
      fixedRoot_confirmation_opposing_mono hAB gv F hc.η_SG r
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
      fixedRoot_confirmation_positive_mono hAB gv F hc.η_SG r
        (DecoupledConsensusModel.Protocol.early E hc r phase)
        (DecoupledConsensusModel.Protocol.late E hc r phase) v
        (Finset.mem_filter.mp hv).2⟩
  exact lt_of_le_of_lt (E.electorate.weightOf_mono hOpp)
    (lt_of_lt_of_le hB (E.electorate.weightOf_mono hPos))

private theorem fixedRoot_cacheAtRound_align_self_opening
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

private theorem fixedRoot_clip_grade_compatible_opening (g F : Block V) :
    Block.compatible (DecoupledConsensusModel.Protocol.clipGrade g F) F = true := by
  induction g with
  | genesis => simp [DecoupledConsensusModel.Protocol.clipGrade,
      Block.compatible, Protocol.preceq_genesis]
  | node p s root gv gsv ats v ih =>
      simp only [DecoupledConsensusModel.Protocol.clipGrade]
      split
      · assumption
      · exact ih

private theorem fixedRoot_clip_grade_keeps_opening (g F : Block V)
    (h : Block.compatible g F = true) :
    DecoupledConsensusModel.Protocol.clipGrade g F = g := by
  cases g with
  | genesis => rfl
  | node p s root gv gsv ats v =>
      simp only [DecoupledConsensusModel.Protocol.clipGrade, h, ↓reduceIte]

private theorem fixedRoot_clip_grade_idempotent_opening (g F : Block V) :
    DecoupledConsensusModel.Protocol.clipGrade
        (DecoupledConsensusModel.Protocol.clipGrade g F) F =
      DecoupledConsensusModel.Protocol.clipGrade g F :=
  fixedRoot_clip_grade_keeps_opening _ _
    (fixedRoot_clip_grade_compatible_opening g F)

private theorem fixedRoot_clip_result_idempotent_opening
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
          rw [fixedRoot_clip_grade_idempotent_opening]

private theorem fixedRoot_clip_frame_idempotent_opening
    (F : Block V) (f : DecoupledConsensusModel.Protocol.Frame V) :
    DecoupledConsensusModel.Protocol.clipFrame F (DecoupledConsensusModel.Protocol.clipFrame F f) =
      DecoupledConsensusModel.Protocol.clipFrame F f := by
  cases f
  simp only [DecoupledConsensusModel.Protocol.clipFrame]
  congr 1 <;> exact fixedRoot_clip_result_idempotent_opening F _

private theorem fixedRoot_preparedFrame_g1_eq_storeRoot_at_opening
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
    exact fixedRoot_cacheAtRound_align_self_opening before.cache r
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
    rw [hcacheTick, fixedRoot_clip_frame_idempotent_opening]
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

set_option maxHeartbeats 400000 in
/-- A nonempty prepared G1 frame at an honest opening proposer is the
relative G1 fact at that proposer's G1-domain read. -/
theorem namedG1At_of_preparedOpeningFrame
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} (hq : 0 < q)
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    {A : Block V}
    (hframe :
      (DecoupledConsensusModel.Protocol.readFrame
        (proposerReadAt S rho (S.hc.opening_slot q)).cache
        (proposerReadAt S rho
          (S.hc.opening_slot q)).st.core.toHealing q).g1 =
        some (some A)) :
    namedG1At S rho (S.E.proposer (S.hc.opening_slot q)) q A := by
  have hopen : domain S.E S.hc q .g1 =
      Protocol.proposal_time S.E (S.hc.opening_slot q) := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    rfl
  have hround : S.hc.round_of (S.E.slotOf
      (Protocol.proposal_time S.E (S.hc.opening_slot q))) = q := by
    simpa only [Proofs.Optimistic.slotOf_proposal_time] using
      (round_of_opening_slot_eq S.hc q)
  have hdomainHor : domain S.E S.hc q .g1 ≤ rho.horizon := by
    rw [hopen]
    exact hhor
  have hframeStore :
      (DecoupledConsensusModel.Protocol.readFrame
        (proposerReadAt S rho (S.hc.opening_slot q)).cache
        (proposerReadAt S rho
          (S.hc.opening_slot q)).st.core.toHealing q).g1 =
      some ((PhaseGrades.storeRoot S.E S.hc
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g1)
          (S.E.proposer (S.hc.opening_slot q))).st q .g1).map
        (fun X => DecoupledConsensusModel.Protocol.clipGrade X
          (proposerReadAt S rho
            (S.hc.opening_slot q)).st.core.F)) := by
    simpa only [proposerReadAt] using
      (fixedRoot_preparedFrame_g1_eq_storeRoot_at_opening
        S rho adm.toNamedAdmissibleCore
        (S.E.proposer (S.hc.opening_slot q)) hprop q hq
        (Protocol.proposal_time S.E (S.hc.opening_slot q))
        hround hopen hdomainHor)
  cases hroot : PhaseGrades.storeRoot S.E S.hc
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g1)
        (S.E.proposer (S.hc.opening_slot q))).st q .g1 with
  | none =>
      simp only [hroot, Option.map_none] at hframeStore
      rw [hframe] at hframeStore
      cases hframeStore
  | some raw =>
      have hA : A = DecoupledConsensusModel.Protocol.clipGrade raw
          (proposerReadAt S rho
            (S.hc.opening_slot q)).st.core.F := by
        rw [hroot, Option.map_some] at hframeStore
        rw [hframe] at hframeStore
        exact Option.some.inj (Option.some.inj hframeStore)
      have hrawGrade : PhaseGrades.phaseGrade S.E S.hc
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g1)
            (S.E.proposer (S.hc.opening_slot q))).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g1)
            (S.E.proposer (S.hc.opening_slot q))).st.core.F
          q .g1 raw = true := by
        have hmem := Proofs.Engine.deepest?_mem hroot
        exact (Finset.mem_filter.mp hmem).2
      have hclipGrade : PhaseGrades.phaseGrade S.E S.hc
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g1)
            (S.E.proposer (S.hc.opening_slot q))).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g1)
            (S.E.proposer (S.hc.opening_slot q))).st.core.F q .g1
          (DecoupledConsensusModel.Protocol.clipGrade raw
            (proposerReadAt S rho
              (S.hc.opening_slot q)).st.core.F) = true := by
        exact fixedRoot_confirmation_phaseGrade_mono S.E S.hc
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g1)
            (S.E.proposer (S.hc.opening_slot q))).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g1)
            (S.E.proposer (S.hc.opening_slot q))).st.core.F q .g1
          (NamedOutageClosure.q10_clip_preceq raw
            (proposerReadAt S rho (S.hc.opening_slot q)).st.core.F)
          hrawGrade
      rw [namedG1At, hA]
      exact hclipGrade

/-- Relative G1 is closed under taking an ancestor at the same domain read. -/
theorem namedG1At_of_preceq
    (S : Setup V) (rho : Run V) {w : V} {q : Round} {A B : Block V}
    (hAB : Block.Preceq A B) (hB : namedG1At S rho w q B) :
    namedG1At S rho w q A := by
  exact fixedRoot_confirmation_phaseGrade_mono S.E S.hc
    (NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g1) w).st.core.toHealing.gradeView
    (NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g1) w).st.core.F q .g1
    hAB hB

theorem fixedRoot_commonActionCeiling_of_lock
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) {H : Height} {q : Round}
    (hlock : SGTargetOpeningConeRootLock S rho H (q - 1)
      (S.hc.opening_slot q - 1)) :
    ∃ C : Block V,
      (∃ v0 ∈ rho.honest, C = actionSGBlockAt S rho v0 (q - 1)) ∧
      (∀ v ∈ rho.honest,
        Block.Preceq (actionSGBlockAt S rho v (q - 1)) C) ∧
      NamedHonestVotesCone S rho (S.hc.opening_slot q - 1)
        (fun X => Block.Preceq C X) := by
  let s := S.hc.opening_slot q - 1
  have hnonempty : rho.honest.Nonempty :=
    Protocol.honest_nonempty_of_honestCommittees hcom
  obtain ⟨v0, hv0, hv0sup⟩ := Finset.exists_mem_eq_sup' hnonempty
    (fun v => (actionSGBlockAt S rho v (q - 1)).depth)
  let C := actionSGBlockAt S rho v0 (q - 1)
  have hmax : ∀ v ∈ rho.honest,
      (actionSGBlockAt S rho v (q - 1)).depth ≤ C.depth := by
    intro v hv
    rw [← hv0sup]
    exact Finset.le_sup' (fun v => (actionSGBlockAt S rho v (q - 1)).depth) hv
  have hupper : ∀ v ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho v (q - 1)) C := by
    intro v hv
    have hcompat := sgTargetCompatible_of_honestVotesCone S hcom
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      adm.toNamedAdmissibleCore.toNamedRootCollisionFree
      (hlock.canonical v hv) (hlock.canonical v0 hv0)
    simpa only [C] using
      AlignedRoundLemmas.preceq_of_compatible_of_depth_le hcompat (hmax v hv)
  exact ⟨C, ⟨v0, hv0, rfl⟩, hupper,
    by simpa only [C] using hlock.canonical v0 hv0⟩

theorem fixedRoot_preparedProposalAnchor_preceq_of_previousCarriers
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {q : Round}
    (hpost : S.E.t_GST ≤ S.a q)
    (hcut : S.hc.Γ_neg1 S.E.Δ (q + 1) ≤ rho.horizon)
    (hproposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot (q + 1)) ≤ rho.horizon)
    {C : Block V}
    (hupper : ∀ v ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho v q) C)
    (hprop : S.E.proposer (S.hc.opening_slot (q + 1)) ∈ rho.honest)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (proposerReadAt S rho
          (S.hc.opening_slot (q + 1))).st.core.toHealing.toFG) C) :
    Block.Preceq
      (nodeAnchor S
        (Internal.NamedRecoveryRead.proposalDutyRead S rho
          (S.hc.opening_slot (q + 1))) (q + 1)) C := by
  let o := S.hc.opening_slot (q + 1)
  let w := S.E.proposer o
  have hw : w ∈ rho.honest := by simpa only [w] using hprop
  have hround : S.hc.round_of o = q + 1 :=
    round_of_opening_slot_eq_schedule S.hc (q + 1)
  have hopen : DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1 =
      Protocol.proposal_time S.E o := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    rfl
  have hdomainHor : DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1 ≤
      rho.horizon := by
    rw [hopen]
    exact hproposalHor
  have hroundTime : S.hc.round_of (S.E.slotOf
      (Protocol.proposal_time S.E o)) = q + 1 := by
    simpa only [Proofs.Optimistic.slotOf_proposal_time] using hround
  have hframeStore := fixedRoot_preparedFrame_g1_eq_storeRoot_at_opening S rho
    adm.toNamedAdmissibleCore (S.E.proposer o) hprop (q + 1) (Nat.succ_pos q)
    (Protocol.proposal_time S.E o) hroundTime hopen hdomainHor
  have hroundSt : S.hc.round_of
      (Internal.NamedRecoveryRead.proposalDutyRead S rho o).st.core.s = q + 1 := by
    simpa only [Internal.NamedRecoveryRead.proposalDutyRead, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.slotOf_proposal_time] using hround
  change Block.Preceq
    (nodeAnchor S (Internal.NamedRecoveryRead.proposalDutyRead S rho o)
      (q + 1)) C
  rcases proposalAnchor_cases S rho o with hfg | hactive
  · rw [hroundSt] at hfg
    rw [hfg]
    exact hroot
  · obtain ⟨root, A, hframe, hactive, hanchor⟩ := hactive
    have hanchor' : nodeAnchor S
        (Internal.NamedRecoveryRead.proposalDutyRead S rho o) (q + 1) = A := by
      simpa only [hroundSt] using hanchor
    rw [hanchor']
    have hframe' := hframe
    rw [hroundSt] at hframe'
    have hframe'' :
        (DecoupledConsensusModel.Protocol.readFrame
          (proposerReadAt S rho o).cache
        (proposerReadAt S rho o).st.core.toHealing (q + 1)).g1 =
          some (some root) := by
      simpa only [Internal.NamedRecoveryRead.proposalDutyRead,
        proposerReadAt] using hframe'
    let read := PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1)
      (S.E.proposer o)
    have hframeRead :
        (DecoupledConsensusModel.Protocol.readFrame
          (proposerReadAt S rho o).cache
          (proposerReadAt S rho o).st.core.toHealing (q + 1)).g1 =
          some ((PhaseGrades.storeRoot S.E S.hc read.st (q + 1) .g1).map
            (fun X => DecoupledConsensusModel.Protocol.clipGrade X
              (proposerReadAt S rho o).st.core.F)) := by
      simpa only [read, Internal.NamedRecoveryRead.proposalDutyRead, proposerReadAt,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
        hframeStore
    cases hstore : PhaseGrades.storeRoot S.E S.hc read.st (q + 1) .g1 with
    | none =>
        simp only [hstore, Option.map_none] at hframeRead
        rw [hframe''] at hframeRead
        cases hframeRead
    | some raw =>
        have hrootEq : root =
            DecoupledConsensusModel.Protocol.clipGrade raw
              (proposerReadAt S rho o).st.core.F := by
          have hopt : some (some root) = some
              (some (DecoupledConsensusModel.Protocol.clipGrade raw
                (proposerReadAt S rho o).st.core.F)) :=
            hframe''.symm.trans (by
              simpa only [hstore, Option.map_some] using hframeRead)
          exact Option.some.inj (Option.some.inj hopt)
        have hLroot : Block.Preceq A root := by
          unfold DecoupledConsensusModel.Protocol.activePrefix at hactive
          exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).2
        have hLraw : Block.Preceq A raw := by
          rw [hrootEq] at hLroot
          exact Block.preceq_trans hLroot
            (NamedOutageClosure.q10_clip_preceq raw
              (proposerReadAt S rho o).st.core.F)
        have hrawData := Proofs.Engine.deepest?_mem hstore
        have hrawTree : raw ∈ read.st.core.T :=
          (Finset.mem_filter.mp hrawData).1
        have hLtree : A ∈ read.st.core.T := by
          have hpc := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1)
            (S.E.proposer o)
          exact Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
            A raw hrawTree hLraw
        have hrawGrade : PhaseGrades.phaseGrade S.E S.hc
            read.st.core.toHealing.gradeView read.st.core.F
            (q + 1) .g1 raw = true := (Finset.mem_filter.mp hrawData).2
        have hAGrade := fixedRoot_confirmation_phaseGrade_mono S.E S.hc _ _
          (q + 1) .g1 hLraw hrawGrade
        have hFroot : Block.Preceq read.st.core.F
            (Protocol.get_fg_root
              (proposerReadAt S rho o).st.core.toHealing.toFG) := by
          have hFJ :=
            Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
              (Protocol.proposal_time S.E o) (S.E.proposer o)
          simpa only [read, PhaseGrades.readAt, proposerReadAt,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom, hopen,
            Protocol.NamedStore.setClock] using
            (Proofs.Records.preceq_get_fg_root_of_F
              (st := (NamedRun.stateBeforeTime S rho
                (Protocol.proposal_time S.E o) (S.E.proposer o)).st.core.toHealing.toFG)
              hFJ)
        have hFC : Block.Preceq read.st.core.F C :=
          Block.preceq_trans hFroot hroot
        have hlatest : q ∈ Protocol.latest_window S.hc.η_SG (q + 1) := by
          simpa only [Nat.add_sub_cancel] using
            Protocol.pred_mem_latest_window S.hc.η_SG (q + 1)
              S.hc.η_SG_ge_one (Nat.succ_pos q)
        have hactionDeadline : S.a q + S.E.Δ ≤
            DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1 :=
          (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
            (Nat.lt_succ_self q)).trans
            (NamedOutageClosure.q10_early_g2_le_early_g1 S (q + 1))
        have hactionHor : S.a q ≤ rho.horizon :=
          (le_add_of_nonneg_right S.E.Δ_pos.le).trans
            ((action_add_delta_le_next_Γ_neg1 S q).trans hcut)
        have hearlyHor : DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1 ≤
            rho.horizon :=
          (NamedOutageClosure.q10_early_g1_le_domain_g2 S (q + 1)).trans
            (by simpa only [gammaNeg1_eq_domain_g2_succ S q] using hcut)
        have hearlyDomain : DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1 ≤
            DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1 :=
          (NamedOutageClosure.q10_early_g1_le_domain_g2 S (q + 1)).trans
            (NamedOutageClosure.q10_domain_g2_lt_domain_g1 S (q + 1)).le
        have hinterpreted : ∀ v ∈ rho.honest,
            (DecoupledConsensusModel.Protocol.interpretedInputs
              read.st.core.toHealing.gradeView read.st.core.F S.hc.η_SG
              (q + 1) (DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1) v).Nonempty := by
          intro v hv
          obtain ⟨a, hemit, hproj⟩ :=
            honest_emits_actionAttestationAt S adm hv q hactionHor (by assumption)
          obtain ⟨i, hi, -, H, hH, hconfirmed⟩ :=
            Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
          have haval : a.val_index = v := by
            have h := congrArg Protocol.SGVote.val_index hproj
            simpa only [Protocol.sgVote, actionSGVoteAt,
              NamedAttestation.erase] using h
          have haround : a.round = q := by
            have h := congrArg Protocol.SGVote.round hproj
            simpa only [Protocol.sgVote, actionSGVoteAt,
              NamedAttestation.erase] using h
          have hHbody : H ∈ (NamedRun.stateBefore S rho i v).st.bodies := by
            change H ∈ (NamedRun.stateBefore S rho i v).st.bodies at hH
            exact hH
          have hHrun : RunBlock S rho H :=
            Proofs.Bridges.runBlock_of_stateBefore_mem S hv hHbody
          have hCmem : actionSGBlockAt S rho v q ∈
              (rho.storeBeforeTime S v (S.a q)).T :=
            actionSGBlockAt_mem_storeBeforeTime S rho v q
          obtain ⟨Cn, hCnerase, hCnrun⟩ :=
            Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
              adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv (S.a q) hCmem
          have hconfirmedCarrier : a.confirmed =
              some (actionSGBlockAt S rho v q).root := by
            have h := congrArg Protocol.SGVote.confirmed hproj
            simpa only [Protocol.sgVote, actionSGVoteAt,
              NamedAttestation.erase] using h
          have hrootEq : H.erase.root = Cn.erase.root := by
            rw [Proofs.NamedWire.erase_root, hCnerase]
            exact congrArg id (Option.some.inj
              (hconfirmed.symm.trans hconfirmedCarrier))
          have hHCeq : H.erase = Cn.erase :=
            Protocol.runBlock_eq_of_root_eq
              adm.toNamedAdmissibleCore.toNamedRootCollisionFree hHrun hCnrun hrootEq
          have hHC : Block.Preceq H.erase C := by
            rw [hHCeq, hCnerase]
            exact hupper v hv
          have hmem :=
            action_vote_mem_interpretedInputs_after_gst_common_upper
              S adm.toNamedAdmissibleCore .g1 hlatest hv hw
              ⟨haval, haround, hemit⟩ ⟨i, hi, hH, hconfirmed⟩ hHC hFC
              (by simpa only [haround] using hpost)
              (by rw [haround, max_eq_left hpost]; exact hactionDeadline)
              hearlyDomain hearlyHor
          exact ⟨Protocol.sgVote a.erase, by simpa only [read] using hmem⟩
        have hrepresented : ∀ v ∈ rho.honest,
            Protocol.represented read.st.core.toHealing.sg_votes
              S.hc.η_SG v (q + 1) = true := by
          intro v hv
          obtain ⟨a, hemit, hproj⟩ :=
            honest_emits_actionAttestationAt S adm hv q hactionHor (by assumption)
          obtain ⟨i, hi, -, H, hH, hconfirmed⟩ :=
            Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
          have haval : a.val_index = v := by
            have h := congrArg Protocol.SGVote.val_index hproj
            simpa only [Protocol.sgVote, actionSGVoteAt,
              NamedAttestation.erase] using h
          have haround : a.round = q := by
            have h := congrArg Protocol.SGVote.round hproj
            simpa only [Protocol.sgVote, actionSGVoteAt,
              NamedAttestation.erase] using h
          have hHbody : H ∈ (NamedRun.stateBefore S rho i v).st.bodies := by
            change H ∈ (NamedRun.stateBefore S rho i v).st.bodies at hH
            exact hH
          have hHrun : RunBlock S rho H :=
            Proofs.Bridges.runBlock_of_stateBefore_mem S hv hHbody
          have hCmem : actionSGBlockAt S rho v q ∈
              (rho.storeBeforeTime S v (S.a q)).T :=
            actionSGBlockAt_mem_storeBeforeTime S rho v q
          obtain ⟨Cn, hCnerase, hCnrun⟩ :=
            Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
              adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv (S.a q) hCmem
          have hconfirmedCarrier : a.confirmed =
              some (actionSGBlockAt S rho v q).root := by
            have h := congrArg Protocol.SGVote.confirmed hproj
            simpa only [Protocol.sgVote, actionSGVoteAt,
              NamedAttestation.erase] using h
          have hrootEq : H.erase.root = Cn.erase.root := by
            rw [Proofs.NamedWire.erase_root, hCnerase]
            exact congrArg id (Option.some.inj
              (hconfirmed.symm.trans hconfirmedCarrier))
          have hHCeq : H.erase = Cn.erase :=
            Protocol.runBlock_eq_of_root_eq
              adm.toNamedAdmissibleCore.toNamedRootCollisionFree hHrun hCnrun hrootEq
          have hHC : Block.Preceq H.erase C := by
            rw [hHCeq, hCnerase]
            exact hupper v hv
          have hmem :=
            action_vote_mem_interpretedInputs_after_gst_common_upper
              S adm.toNamedAdmissibleCore .g1 hlatest hv hw
              ⟨haval, haround, hemit⟩ ⟨i, hi, hH, hconfirmed⟩ hHC hFC
              (by simpa only [haround] using hpost)
              (by rw [haround, max_eq_left hpost]; exact hactionDeadline)
              hearlyDomain hearlyHor
          have hraw := (Finset.mem_filter.mp hmem).1
          obtain ⟨hpool, hfields⟩ := Finset.mem_filter.mp hraw
          obtain ⟨k, hk, huk⟩ := Finset.mem_biUnion.mp hpool
          exact Protocol.represented_of_vote_mem
            (List.mem_toFinset.mp hk) huk hfields.1
        have hwindow := windowMajorityAt_of_honestWeightMajority_of_represented
          S (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird
            (S := S) hfb) hrepresented hinterpreted
        have hgrade : DecoupledConsensusModel.Protocol.gradeBool S.E
            read.st.core.toHealing.gradeView read.st.core.F S.hc.η_SG (q + 1)
            (DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1)
            (DecoupledConsensusModel.Protocol.late S.E S.hc (q + 1) .g1)
            A = true := by
          simpa only [read, PhaseGrades.storeGrade, PhaseGrades.phaseGrade] using hAGrade
        obtain ⟨v, hv, u, hu, head, hconf, hfind, -, hAhead, -, hmax⟩ :=
          exists_honest_max_positive_supporter_of_relativeGrade
            S.E S.hc hwindow hgrade
        obtain ⟨a, hemit, hproj⟩ :=
          honest_emits_actionAttestationAt S adm hv q hactionHor (by assumption)
        obtain ⟨i, hi, -, H, hH, hconfirmed⟩ :=
          Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
        have haval : a.val_index = v := by
          have h := congrArg Protocol.SGVote.val_index hproj
          simpa only [Protocol.sgVote, actionSGVoteAt,
            NamedAttestation.erase] using h
        have haround : a.round = q := by
          have h := congrArg Protocol.SGVote.round hproj
          simpa only [Protocol.sgVote, actionSGVoteAt,
            NamedAttestation.erase] using h
        have hHbody : H ∈ (NamedRun.stateBefore S rho i v).st.bodies := by
          change H ∈ (NamedRun.stateBefore S rho i v).st.bodies at hH
          exact hH
        have hHrun : RunBlock S rho H :=
          Proofs.Bridges.runBlock_of_stateBefore_mem S hv hHbody
        have hCmem : actionSGBlockAt S rho v q ∈
            (rho.storeBeforeTime S v (S.a q)).T :=
          actionSGBlockAt_mem_storeBeforeTime S rho v q
        obtain ⟨Cn, hCnerase, hCnrun⟩ :=
          Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
            adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv (S.a q) hCmem
        have hconfirmedCarrier : a.confirmed =
            some (actionSGBlockAt S rho v q).root := by
          have h := congrArg Protocol.SGVote.confirmed hproj
          simpa only [Protocol.sgVote, actionSGVoteAt,
            NamedAttestation.erase] using h
        have hrootEq : H.erase.root = Cn.erase.root := by
          rw [Proofs.NamedWire.erase_root, hCnerase]
          exact congrArg id (Option.some.inj
            (hconfirmed.symm.trans hconfirmedCarrier))
        have hHCeq : H.erase = Cn.erase :=
          Protocol.runBlock_eq_of_root_eq
            adm.toNamedAdmissibleCore.toNamedRootCollisionFree hHrun hCnrun hrootEq
        have hHC : Block.Preceq H.erase C := by
          rw [hHCeq, hCnerase]
          exact hupper v hv
        have hactionInput :=
          action_vote_mem_interpretedInputs_after_gst_common_upper
            S adm.toNamedAdmissibleCore .g1 hlatest hv hw
            ⟨haval, haround, hemit⟩ ⟨i, hi, hH, hconfirmed⟩ hHC hFC
            (by simpa only [haround] using hpost)
            (by rw [haround, max_eq_left hpost]; exact hactionDeadline)
            hearlyDomain hearlyHor
        have hqle : q ≤ u.round := by
          have h := hmax (Protocol.sgVote a.erase) hactionInput
          simpa only [Protocol.sgVote, NamedAttestation.erase, haround] using h
        have huraw := (Finset.mem_filter.mp hu).1
        obtain ⟨b, hbval, hbround, hbproj, huwindow, -, hbemit⟩ :=
          NamedOutageClosure.rawInputs_trace S rho
            adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
            adm.toNamedAdmissibleCore.toNamedUnforgeable
            (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1)
            (DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1) w
            S.hc.η_SG (q + 1) v hv (by simpa only [read] using huraw)
        have hule : u.round ≤ q := Nat.le_of_lt_succ
          (NamedOutageClosure.window_bounds huwindow).2
        have huroundEq : u.round = q := Nat.le_antisymm hule hqle
        have hbroundQ : b.round = q := hbround.trans huroundEq
        have hba : b = a := Proofs.Optimistic.emits_attest_unique S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hbemit hemit
          (hbroundQ.trans haround.symm)
        have huEq : u = Protocol.sgVote a.erase := by
          rw [← hbproj, hba]
        have hheadRoot : head.root = (actionSGBlockAt S rho v q).root := by
          have huconf := congrArg Protocol.SGVote.confirmed huEq
          simpa only [Protocol.sgVote, NamedAttestation.erase, hconf,
            hconfirmedCarrier, Option.some.injEq] using huconf
        have hheadMem : head ∈ read.st.core.T := Proofs.HealingLemmas.find?_mem hfind
        obtain ⟨Headn, hHeaderase, hHeadrun⟩ :=
          Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
            adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hw
            (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1) (by
              simpa only [read] using hheadMem)
        have hheadCnRoot : Headn.erase.root = Cn.erase.root := by
          rw [hHeaderase, hCnerase]
          exact hheadRoot
        have hheadCarrier : head = actionSGBlockAt S rho v q := by
          rw [← hHeaderase, ← hCnerase]
          exact Protocol.runBlock_eq_of_root_eq
            adm.toNamedAdmissibleCore.toNamedRootCollisionFree
            hHeadrun hCnrun hheadCnRoot
        have hAC : Block.Preceq A C :=
          Block.preceq_trans (by simpa only [hheadCarrier] using hAhead)
            (hupper v hv)
        exact hAC

theorem fixedRoot_actionCarrier_mem_proposerRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {J : NamedBlock V} {C : Block V} {v : V} (hv : v ∈ rho.honest)
    (hJrun : RunBlock S rho J) (hJC : Block.Preceq J.erase C)
    {r : Round} (hCsource : C ∈
      (rho.storeBeforeTime S v (S.a r)).T)
    {s : Slot} (hprop : S.E.proposer s ∈ rho.honest)
    (hproposalHor : Protocol.proposal_time S.E s ≤ rho.horizon)
    (hpost : S.E.t_GST ≤ S.a r)
    (hdelay : S.a r + S.E.Δ ≤ Protocol.proposal_time S.E s)
    (hroot : Protocol.get_fg_root
        (rho.storeBeforeTime S (S.E.proposer s)
          (Protocol.proposal_time S.E s)).toHealing.toFG = J.erase)
    (hcap : (rho.storeBeforeTime S (S.E.proposer s)
      (Protocol.proposal_time S.E s)).h_max ≤
      (Protocol.derive_named S.E S.cfg J).h + 1) :
    C ∈ (rho.storeBeforeTime S (S.E.proposer s)
      (Protocol.proposal_time S.E s)).T ∧
      J ∈ (rho.storeBeforeTime S (S.E.proposer s)
        (Protocol.proposal_time S.E s)).bodies := by
  let p := S.E.proposer s
  let tp := Protocol.proposal_time S.E s
  let pre := rho.storeBeforeTime S p tp
  have hroot' : Protocol.get_fg_root pre.toHealing.toFG = J.erase := by
    simpa only [pre, p, tp] using hroot
  have hrootMem : Protocol.get_fg_root pre.toHealing.toFG ∈ pre.T := by
    have hroots :=
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho tp p).1.1.2
    have hmem := Proofs.NamedStoreRoots.fg_root_mem
      (NamedRun.stateBeforeTime S rho tp p).st hroots
    simpa only [pre, Run.storeBeforeTime] using hmem
  obtain ⟨K, hKbody, hKerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho tp p hrootMem
  have hKrun : RunBlock S rho K := by
    obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed tp
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hprop (i := n)
    rw [← hn]
    exact hKbody
  have hKroot : K.root = J.root := by
    calc
      K.root = K.erase.root := (Proofs.NamedWire.erase_root K).symm
      _ = (Protocol.get_fg_root pre.toHealing.toFG).root :=
        congrArg Block.root hKerase
      _ = J.erase.root := congrArg Block.root hroot'
      _ = J.root := Proofs.NamedWire.erase_root J
  have hKJ : K = J := by
    apply adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      K J hKrun hJrun K J (Or.inl (Proofs.NamedAncestry.named_self K))
      (Or.inr (Proofs.NamedAncestry.named_self J)) hKroot
  have hJbody : J ∈ (rho.storeBeforeTime S p tp).bodies := by
    simpa only [hKJ] using hKbody
  have hJactive : J.erase ∈
      Protocol.get_filtered_block_tree pre.toHealing.toFG := by
    exact mem_filtered_of_mem_tree_of_exactFGRoot_heightCap S rho p tp
      hJbody rfl (by simpa only [pre, p, tp] using hroot')
      (Block.preceq_self J.erase) (by simpa only [pre, p, tp] using hcap)
  rcases block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTime
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v (S.a r)
      hCsource with hgen | ⟨Cn, i, t, hCnerase, hacc, ht⟩
  · rw [hgen]
    exact ⟨(Protocol.genesis_mem_and_stamp_storeBeforeTime S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed p tp tp).1, hJbody⟩
  · have hCpos : 0 < Cn.slot := by
      rw [← Proofs.NamedWire.erase_slot Cn]
      exact Nat.zero_lt_of_lt
        (Protocol.parent_slot_lt_of_acceptsAt_block S hacc)
    have hFhist : Protocol.BlockFinalizedBelowAtDeliveriesBefore
        S rho p Cn (S.a r + S.E.Δ) :=
      finalizedBelowAtDeliveriesBefore_of_filteredAtLaterRead
        S adm hdelay hJactive (by simpa only [hCnerase] using hJC)
    have hadmit : Protocol.AdmittedBefore S rho p C
        (S.a r + S.E.Δ) := by
      have hadm' := Protocol.block_admittedBefore_of_accepted_after_cutoff
        S adm hv hprop hCpos hacc ht hpost rfl
          (le_trans hdelay hproposalHor) hFhist
      simpa only [hCnerase] using hadm'
    have hCmem := (Protocol.admittedBefore_mem_and_stamp_at S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hadmit hdelay).1
    exact ⟨hCmem, hJbody⟩

theorem fixedRoot_preparedProposalConeSupport_of_namedCone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) {s : Slot}
    (hs : 0 < s) (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.support_cutoff S.E s ≤ rho.horizon)
    (hprop : S.E.proposer (s + 1) ∈ rho.honest) {T : Block V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (proposalDutyRead S rho (s + 1)).st.core.toHealing.toFG) T)
    (hnames : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq T X)) :
    Proofs.Optimistic.ConeSupport S.E
      (proposalDutyRead S rho (s + 1)).st.core.T
      (Protocol.proposer_view
        (proposalDutyRead S rho (s + 1)).st.core.toHealing.toFG.toSG.toGoldfishStore
        (proposalDutyRead S rho (s + 1)).st.core.s).toFinset
      (Protocol.proposer_support_view
        (proposalDutyRead S rho (s + 1)).st.core.toHealing.toFG.toSG.toGoldfishStore
        (proposalDutyRead S rho (s + 1)).st.core.s).toFinset
      (Protocol.proposer_view
        (proposalDutyRead S rho (s + 1)).st.core.toHealing.toFG.toSG.toGoldfishStore
        (proposalDutyRead S rho (s + 1)).st.core.s).toFinset
      ((proposalDutyRead S rho (s + 1)).st.core.s - 1) rho.honest
      (fun X => Block.Preceq T X) := by
  let n := proposalDutyRead S rho (s + 1)
  let st := n.st.core
  let raw := (Protocol.proposer_view st.toHealing.toFG.toSG.toGoldfishStore st.s).toFinset
  let support :=
    (Protocol.proposer_support_view st.toHealing.toFG.toSG.toGoldfishStore st.s).toFinset
  have hslot : st.s = s + 1 := by
    simpa only [st, n, proposalDutyRead, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      (Proofs.Optimistic.slotOf_proposal_time S.E (s + 1))
  have hprev : st.s - 1 = s := by
    rw [hslot]
    exact Nat.add_sub_cancel s 1
  have hrootDuty : Block.Preceq
      (Protocol.get_fg_root
        (Protocol.proposerDutyStore S rho (s + 1)).toHealing.toFG) T := by
    simpa only [Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
      proposalDutyRead, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      hroot
  have hresolve0 := Protocol.headsResolveIn_proposerDutyStore_of_postHealingCone
    S adm hpost hhor hprop hrootDuty hnames
  have hresolve : Proofs.Optimistic.HeadsResolveIn S rho s st.T st.timestamp_block := by
    simpa only [st, n, proposalDutyRead, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Protocol.proposerDutyStore, Proofs.Optimistic.tickStore] using hresolve0
  have hss : support ⊆ raw := by
    intro u hu
    simp only [support, raw, Protocol.proposer_support_view,
      Protocol.proposer_view, List.mem_toFinset, List.mem_filter] at hu ⊢
    exact hu.1
  obtain ⟨m, hm, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (Protocol.proposal_time S.E (s + 1))
  have hgf : st.gf_votes =
      (rho.stateBefore S m (S.E.proposer (s + 1))).st.core.gf_votes := by
    dsimp only [st, n, proposalDutyRead, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
    exact congrArg (fun z =>
      (z (S.E.proposer (s + 1))).st.core.gf_votes) hm
  have hgfTime : st.gf_votes =
      (NamedRun.stateBeforeTime S rho (Protocol.proposal_time S.E (s + 1))
        (S.E.proposer (s + 1))).st.core.gf_votes := by
    rfl
  have hne : ∀ x ∈ S.E.committee s, x ∈ rho.honest →
      Protocol.equivocates raw x = false := by
    intro x _ hx
    have hno := Proofs.Optimistic.pool_no_honest_equivocation S adm
      (S.E.proposer (s + 1)) m s hx
    simpa only [raw, Protocol.proposer_view, hprev, hgf,
      Protocol.NamedStore.setClock, Protocol.NamedStore.pool,
      Protocol.Store.pool, Protocol.Store.toHealing, List.toFinset] using hno
  have hvote : ∀ x ∈ S.E.committee s, x ∈ rho.honest →
      ∃ X : Block V, Block.Preceq T X ∧
        X.slot ≤ s ∧
        (⟨x, s, X.root⟩ : GoldfishVote V) ∈ support ∧
        Block.find? st.T X.root = some X := by
    intro x hxCommittee hxHonest
    obtain ⟨X, hX, hXrun, hXemit⟩ := hnames x hxHonest hxCommittee
    have hhead : Proofs.Optimistic.HonestHead S rho s X.erase :=
      ⟨x, hxHonest, hxCommittee, ⟨X, rfl, hXrun⟩, hXemit⟩
    obtain ⟨hfind, -⟩ := hresolve X.erase hhead
    have hcut := Protocol.gfVote_in_cutoff_view_after_gst
      S adm.toNamedAdmissibleCore hxHonest hs hpost hXemit rfl hprop
      (Protocol.proposal_time S.E (s + 1))
      (Protocol.proposal_time S.E (s + 1))
      (Protocol.support_cutoff_le_proposal_time_succ S.E s)
      (Protocol.support_cutoff_le_proposal_time_succ S.E s) hhor
    have hcut' := hcut
    rw [beforeCutoff, Finset.mem_filter] at hcut'
    have hpool := hcut'.1
    have hpool' : (⟨x, s, X.erase.root⟩ : GoldfishVote V) ∈
        (NamedRun.stateBeforeTime S rho
          (Protocol.proposal_time S.E (s + 1))
          (S.E.proposer (s + 1))).st.core.gf_votes s := by
      simpa only [Run.storeBeforeTime, Protocol.Store.pool,
        List.mem_toFinset] using hpool
    have hraw : (⟨x, s, X.erase.root⟩ : GoldfishVote V) ∈ raw := by
      dsimp only [raw]
      change (⟨x, s, X.erase.root⟩ : GoldfishVote V) ∈
        (st.gf_votes (st.s - 1)).toFinset
      rw [hprev, hgfTime]
      exact List.mem_toFinset.mpr hpool'
    have hfind' : Block.find? st.toHealing.T
        (⟨x, s, X.erase.root⟩ : GoldfishVote V).head = some X.erase := by
      simpa only [st, n] using hfind
    have hXmem : X.erase ∈
        (rho.storeBeforeTime S (S.E.proposer (s + 1))
          (Protocol.proposal_time S.E (s + 1))).T := by
      simpa only [st, n, proposalDutyRead, proposerReadAt,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
        (Proofs.HealingLemmas.find?_mem hfind)
    have hXslot : X.erase.slot ≤ s :=
      Proofs.Optimistic.emitted_vote_head_slot_le_of_store_mem S
        adm.toNamedAdmissibleCore hxHonest hprop hXemit rfl hXmem (by rfl)
    have hsupport : (⟨x, s, X.erase.root⟩ : GoldfishVote V) ∈ support := by
      simp only [support, Protocol.proposer_support_view,
        List.mem_toFinset, List.mem_filter, hprev]
      refine ⟨?_, ?_⟩
      · simpa only [Protocol.proposer_view, hprev,
          Protocol.Store.toHealing] using List.mem_toFinset.mp hraw
      · change decide (Protocol.resolved st.toHealing.T
          (⟨x, s, X.erase.root⟩ : GoldfishVote V) = true) = true
        simp [Protocol.resolved, hfind', hXslot]
    exact ⟨X.erase, hX, hXslot, hsupport, hfind⟩
  have hcone := Proofs.Optimistic.coneSupport_of_named_votes (E := S.E) (T := st.T)
    (votes := raw) (support := support) (late := raw) (s := s)
    (Hon := rho.honest) (tgt := fun X => Block.Preceq T X)
    (hcom s) (subset_refl _) hss hne hvote
  simpa only [raw, support, st, n, hslot, hprev] using hcone

theorem fixedRoot_preparedProposalHead_preceq_of_cone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} {P : Block V}
    (hcompat : Block.compatible
      (Protocol.get_fg_root
        (proposalDutyRead S rho s).st.core.toHealing.toFG) P = true)
    (hwitness : CanonicalConeWitness
      (proposalDutyRead S rho s).st.core P)
    (hanchor : Block.Preceq
      (Protocol.get_sg_root_with
        (NamedProfile.gradeContract
          (proposalDutyRead S rho s).cache)
        S.E S.hc (proposalDutyRead S rho s).st.core.toHealing
        (S.hc.round_of (proposalDutyRead S rho s).st.core.s)) P)
    (hsupport : Proofs.Optimistic.ConeSupport S.E
      (proposalDutyRead S rho s).st.core.T
      (Protocol.proposer_view
        (proposalDutyRead S rho s).st.core.toHealing.toFG.toSG.toGoldfishStore
        (proposalDutyRead S rho s).st.core.s).toFinset
      (Protocol.proposer_support_view
        (proposalDutyRead S rho s).st.core.toHealing.toFG.toSG.toGoldfishStore
        (proposalDutyRead S rho s).st.core.s).toFinset
      (Protocol.proposer_view
        (proposalDutyRead S rho s).st.core.toHealing.toFG.toSG.toGoldfishStore
        (proposalDutyRead S rho s).st.core.s).toFinset
      ((proposalDutyRead S rho s).st.core.s - 1) rho.honest
      (fun X => Block.Preceq P X))
    (hvalid : Protocol.VoteSetValid S.E
      ((proposalDutyRead S rho s).st.core.s - 1)
      (Protocol.proposer_view
        (proposalDutyRead S rho s).st.core.toHealing.toFG.toSG.toGoldfishStore
        (proposalDutyRead S rho s).st.core.s).toFinset) :
    Block.Preceq P (proposedParent S rho s) := by
  let n := proposalDutyRead S rho s
  let st := n.st.core
  let gc := NamedProfile.gradeContract n.cache
  let tree := Protocol.get_filtered_block_tree st.toHealing.toFG
  let votes := (Protocol.proposer_view st.toHealing.toFG.toSG.toGoldfishStore st.s).toFinset
  let support :=
    (Protocol.proposer_support_view st.toHealing.toFG.toSG.toGoldfishStore st.s).toFinset
  have hpc : ParentClosed st := by
    have h := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
      (Protocol.proposal_time S.E s) (S.E.proposer s)
    change ParentClosed st at h
    exact h
  have hFJ : Block.Preceq st.F st.J := by
    exact Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
      (Protocol.proposal_time S.E s) (S.E.proposer s)
  have hsplit := canonicalFloor_preceq_root_or_mem_filtered
    hpc hFJ hcompat hwitness
  rcases hsplit with hProot | hPfiltered
  · have hfgsg := fg_root_preceq_get_sg_root_with_frame
      n.cache S.E S.hc st.toHealing (S.hc.round_of st.s)
    have hsghead := get_sg_root_with_preceq_get_head_with
      gc S.E S.hc st.toHealing votes support (st.s - 1)
    have hhead : Block.Preceq P
        (Protocol.get_head_with gc S.E S.hc st.toHealing votes support
          (st.s - 1)) :=
      Block.preceq_trans hProot (Block.preceq_trans hfgsg hsghead)
    simpa only [proposedParent, proposalInputAt,
      Internal.NamedRecoveryRead.proposalDutyRead, n, st, gc, tree, votes, support,
      DutyInputDefaults.proposal_input_parent] using hhead
  · have hPT : P ∈ st.T := by
      have hparts := hPfiltered
      simp only [Protocol.get_filtered_block_tree,
        Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
        Protocol.finalized_descendants, Finset.mem_filter,
        Protocol.Store.toHealing] at hparts
      exact hparts.1.1.1
    have hpath : ∀ C : Block V,
        Block.Preceq (Protocol.get_sg_root_with gc S.E S.hc st.toHealing
          (S.hc.round_of st.s)) C →
        C ≠ Protocol.get_sg_root_with gc S.E S.hc st.toHealing
          (S.hc.round_of st.s) → Block.Preceq C P → C ∈ tree := by
      intro C hAC _ hCP
      have hCT : C ∈ st.T :=
        Proofs.Records.mem_of_preceq ((parentClosed_iff st).mp hpc).2 C P hPT hCP
      have hfgsg := fg_root_preceq_get_sg_root_with_frame
        n.cache S.E S.hc st.toHealing (S.hc.round_of st.s)
      have hrootC : Block.Preceq
          (Protocol.get_fg_root st.toHealing.toFG) C :=
        Block.preceq_trans hfgsg hAC
      exact Proofs.Records.mem_filtered_of_preceq hFJ hPfiltered hCT hCP hrootC
    have hhead := Proofs.Optimistic.goldfish_passes_cone S.E st.σ st.h_max st.T tree
      st.s votes support (st.s - 1) rho.honest hsupport hvalid hanchor hpath
    change Block.Preceq P
      (Protocol.get_head_in_tree_with_layer gc S.E S.hc st.toHealing tree votes support
        (st.s - 1))
    rw [Proofs.Optimistic.get_head_in_tree_split_with]
    simpa only [tree, votes, support] using hhead

/-- The two callback-free parent ceilings needed by the fixed-root opening
lifecycle. -/
structure FixedHeightRootOpeningParentRun
    (S : Setup V) (rho : Run V) (q : Round) : Prop where
  actionTargetParent : ∀ v ∈ rho.honest,
    Block.Preceq (actionSGBlockAt S rho v (q - 1))
      (proposedParent S rho (S.hc.opening_slot q))
  liveG1Parent : ∀ w ∈ rho.honest, ∀ B,
    namedG1At S rho w q B →
    Block.Preceq B
      (proposedParent S rho (S.hc.opening_slot q))

theorem fixedRoot_namedTarget_of_fixedRoot
    (S : Setup V) {rho : Run V} {H : Height} {w : V} {read : Time}
    (h : FixedHeightJustificationRootAtRead
      S rho H w read) :
    ∃ J : NamedBlock V,
      J.erase = (rho.storeBeforeTime S w read).J ∧
        RunBlock S rho J ∧
          (Protocol.derive_named S.E S.cfg J).h = H - 1 := by
  obtain ⟨D, _hDbody, hDrun, hjust⟩ := h.carrierExists
  have hhj : (Protocol.derive_named S.E S.cfg D).h_j = H - 1 := by
    exact hjust.2.trans (by simpa only using h.fixedTarget.justificationHeight)
  have hhjNe : (Protocol.derive_named S.E S.cfg D).h_j ≠ 0 := by
    rw [hhj]
    exact Nat.ne_of_gt h.targetHeightPositive
  obtain ⟨J, hJD, hJerase, hJheight⟩ :=
    (NamedCheckpointHeights.justified_ancestor_height S.E S.cfg D).resolve_left hhjNe
  refine ⟨J, hJerase.trans hjust.1, ?_, ?_⟩
  · exact Proofs.NamedRuntime.blockInRun_of_ancestor S rho hDrun hJD
  · rw [hJheight, hhj]

theorem fixedRoot_runBlock_of_body_at_read
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


#print axioms fixedRoot_confirmation_localCovers_mono
#print axioms fixedRoot_confirmation_positive_mono
#print axioms fixedRoot_confirmation_opposing_mono
#print axioms fixedRoot_confirmation_phaseGrade_mono
#print axioms fixedRoot_cacheAtRound_align_self_opening
#print axioms fixedRoot_clip_grade_compatible_opening
#print axioms fixedRoot_clip_grade_keeps_opening
#print axioms fixedRoot_clip_grade_idempotent_opening
#print axioms fixedRoot_clip_result_idempotent_opening
#print axioms fixedRoot_clip_frame_idempotent_opening
#print axioms fixedRoot_preparedFrame_g1_eq_storeRoot_at_opening
#print axioms namedG1At_of_preparedOpeningFrame
#print axioms namedG1At_of_preceq
#print axioms fixedRoot_commonActionCeiling_of_lock
#print axioms fixedRoot_preparedProposalAnchor_preceq_of_previousCarriers
#print axioms fixedRoot_actionCarrier_mem_proposerRead
#print axioms fixedRoot_preparedProposalConeSupport_of_namedCone
#print axioms fixedRoot_preparedProposalHead_preceq_of_cone
#print axioms fixedRoot_namedTarget_of_fixedRoot
#print axioms fixedRoot_runBlock_of_body_at_read




theorem fixedRoot_tickStore_G1
    (S : Setup V) (st : Protocol.NamedStore V) (t : Time) :
    ∀ r B, Protocol.G1 S.E
      (Proofs.Optimistic.tickStore S st.core t).toHealing.gradeView S.hc r B =
      Protocol.G1 S.E st.toHealing.gradeView S.hc r B := by
  intro r B
  simp only [Protocol.G1, Protocol.direct_support, Protocol.summary,
    Proofs.Optimistic.tickStore, Protocol.Store.toHealing,
    Protocol.NamedStore.toHealing]
  congr 1



theorem fixedRoot_G1_gradeViewAt_raw
    (S : Setup V) (rho : Run V) (v : V) (r : Round) (B : Block V) :
    Protocol.G1 S.E (gradeViewAt S rho v r) S.hc r B =
      Protocol.G1 S.E
        ((rho.storeBeforeTime S v (S.a r)).toHealing.gradeView) S.hc r B := by
  rfl

theorem fixedRoot_G1_persists_from_read
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {q : Round}
    {early : Time} {pre : Protocol.NamedStore V}
    (hpre : rho.storeBeforeTime S v early = pre)
    (hcut : S.hc.Γ_0 S.E.Δ q ≤ early)
    (hlater : early ≤ S.a q) {B : Block V}
    (hG1 : Protocol.G1 S.E pre.toHealing.gradeView S.hc q B = true) :
    Protocol.G1 S.E (gradeViewAt S rho v q) S.hc q B = true := by
  have hraw := G1_persists_after_cutoff S adm hv hcut hlater
    (hpre ▸ hG1)
  exact (fixedRoot_G1_gradeViewAt_raw S rho v q B).symm ▸ hraw

#print axioms fixedRoot_tickStore_G1
#print axioms fixedRoot_G1_gradeViewAt_raw
#print axioms fixedRoot_G1_persists_from_read










/-
/-- Exact fixed-root retention, the Claim-1 opening cone, and the actual honest
opening fresh anchor construct both proposal-parent ceilings without a recovery
callback. -/
theorem fixedHeightJustificationRootOpeningParentRun_of_fixedRootLock
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {H: Height} {w: V} {read: Time}
    (hfix: FixedHeightJustificationRootAtRead S rho H w read)
    {q: Round} {A: Block V} (hq: 0 < q)
    (hforms: GradeFormsAt S rho (q - 1)
      (rho.storeBeforeTime S w read).J)
    (hlock: SGTargetOpeningConeRootLock S rho H (q - 1)
      (S.hc.opening_slot q - 1))
    (hpostRead: S.E.t_GST ≤ read)
    (hproposalDelay: read + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hproposalHor: Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hproposalCap: honestHMaxAt S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) ≤ H)
    (hpostCone: S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot q - 1))
    (hpostPreviousAction: S.E.t_GST ≤ S.a (q - 1))
    (hprop: S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hanchor: Protocol.fresh_anchor S.E S.hc
      (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot q)).toHealing q = some A):
    FixedHeightRootOpeningParentRun S rho q:= by
  let s:= S.hc.opening_slot q - 1
  let p:= S.E.proposer (S.hc.opening_slot q)
  let proposalRead:= Protocol.proposal_time S.E (S.hc.opening_slot q)
  let pre:= rho.storeBeforeTime S p proposalRead
  let duty:= Protocol.proposerDutyStore S rho (S.hc.opening_slot q)
  let J:= (rho.storeBeforeTime S w read).J
  have hqOne: 1 ≤ q:= Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hq)
  obtain ⟨hslo, hshi, hsucc⟩:= lastInteriorSlot_before_opening S.hc hq
  have hspos: 0 < s:= by
    exact lt_of_lt_of_le (Nat.zero_lt_succ _) (by simpa only [s] using hslo)
  have hformsJ: GradeFormsAt S rho (q - 1) J:= by
    simpa only [J] using hforms
  have hlockS: SGTargetOpeningConeRootLock S rho H (q - 1) s:= by
    simpa only [s] using hlock
  have hsb: SlashableBound S rho:=
    slashableBound_of_admissible_belowOneThird S adm hfb
  obtain ⟨hrootPre, hmaxPre⟩:=
    fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
      S adm hsb hfix hprop hpostRead hproposalDelay hproposalHor hproposalCap
  have hrootDuty: Protocol.get_fg_root duty.toHealing.toFG = J:= by
    simpa only [duty, Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
      pre, p, proposalRead, J] using hrootPre
  have hmaxDuty: duty.h_max = H:= by
    simpa only [duty, Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
      pre, p, proposalRead] using hmaxPre
  have hHone: 1 ≤ H:=
    Nat.le_of_lt (Nat.sub_pos_iff_lt.mp hfix.targetHeightPositive)
  have hJheight: (derived_state S.E S.cfg J).h = H - 1:= by
    simpa only [J] using hfix.targetDerivedHeight
  have hJheightSucc: (derived_state S.E S.cfg J).h + 1 = H:= by
    rw [hJheight]
    exact Nat.sub_add_cancel hHone
  have hcapDuty: duty.h_max ≤ (derived_state S.E S.cfg J).h + 1:=
    le_of_eq (hmaxDuty.trans hJheightSucc.symm)
  have hselected: Block.deepest?
      ((Protocol.get_filtered_block_tree duty.toHealing.toFG).filter
        (fun B => Protocol.G1 S.E duty.toHealing.gradeView S.hc q B = true)) =
        some A:= by
    simpa only [Protocol.fresh_anchor, duty] using hanchor
  have hAdata:= Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hselected)
  have hanchorDuty: Protocol.fresh_anchor S.E S.hc duty.toHealing q =
      some A:= by
    simpa only [duty] using hanchor
  have hAG1Duty: Protocol.G1 S.E duty.toHealing.gradeView S.hc q A = true:=
    hAdata.2
  have hroundDuty: S.hc.round_of duty.toHealing.s = q:= by
    change S.hc.round_of duty.s = q
    simpa only [duty, Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
      Proofs.Optimistic.slotOf_proposal_time] using
      (round_of_opening_slot_eq S.hc q)
  have hhealAnchor: Proofs.Optimistic.healAnchor S.E S.hc duty.toHealing = A:= by
    rw [Proofs.Optimistic.healAnchor_eq_get_sg_root, hroundDuty]
    simp only [Protocol.get_sg_root, hanchorDuty]
  have hAG1Pre: Protocol.G1 S.E pre.toHealing.gradeView S.hc q A = true:= by
    simpa only [duty, Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
      pre, p, proposalRead] using hAG1Duty
  have hcutAtProposal: S.hc.Γ_0 S.E.Δ q ≤ proposalRead:= by
    simpa only [proposalRead] using
      (Protocol.Γ_0_eq_proposal_time S.hc S.E q).le
  have hproposalLeAction: proposalRead ≤ S.a q:= by
    dsimp only [proposalRead]
    calc
      Protocol.proposal_time S.E (S.hc.opening_slot q) =
          S.hc.Γ_0 S.E.Δ q:=
        (Protocol.Γ_0_eq_proposal_time S.hc S.E q).symm
      _ ≤ S.hc.Γ_1 S.E.Δ q:=
        le_of_lt (Proofs.HealingLemmas.Γ_0_lt_Γ_1 S.hc S.E.Δ_pos q)
      _ ≤ S.hc.Γ_2 S.E.Δ q:=
        le_of_lt (Proofs.HealingLemmas.Γ_1_lt_Γ_2 S.hc S.E.Δ_pos q)
      _ ≤ S.a q:= Γ_2_le_a S.hc S.E.Δ_pos q
  have hAG1ActionRaw: Protocol.G1 S.E
      ((rho.storeBeforeTime S p (S.a q)).toHealing.gradeView) S.hc q A = true:=
    G1_persists_after_cutoff S adm hprop hcutAtProposal hproposalLeAction hAG1Pre
  have hAG1Action: Protocol.G1 S.E (gradeViewAt S rho p q) S.hc q A = true:= by
    simpa only [gradeViewAt, healStoreAt, Run.storeBeforeTime,
      Protocol.HealingStore.gradeView, Protocol.Store.toHealing, p] using hAG1ActionRaw
  have hcut: S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon:= by
    calc
      S.hc.Γ_neg1 S.E.Δ q ≤ S.hc.Γ_0 S.E.Δ q:=
        le_of_lt (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos q)
      _ = Protocol.proposal_time S.E (S.hc.opening_slot q):=
        Protocol.Γ_0_eq_proposal_time S.hc S.E q
      _ ≤ rho.horizon:= hproposalHor
  have hcutPred:
      S.hc.Γ_neg1 S.E.Δ ((q - 1) + 1) ≤ rho.horizon:= by
    simpa only [Nat.sub_add_cancel hqOne] using hcut
  have hconcentration: G1Concentration S rho (q - 1) s:=
    g1Concentration_of_targetCanonicality S adm hcom hfb
      hpostPreviousAction hcutPred hlockS.canonical
  have hconeA: HonestVotesCone S rho s (fun X => Block.Preceq A X):= by
    exact hconcentration.supported hprop (by
      simpa only [p, Nat.sub_add_cancel hqOne] using hAG1Action)
  have hsupportHor: Protocol.support_cutoff S.E s ≤ rho.horizon:= by
    exact (Protocol.support_cutoff_le_proposal_time_succ S.E s).trans
      (by simpa only [s, hsucc] using hproposalHor)
  have hpostConeS: S.E.t_GST ≤ Protocol.vote_time S.E s:= by
    simpa only [s] using hpostCone
  have hpredLt: q - 1 < q:= Nat.sub_lt hq (by decide)
  have hactionDelay: S.a (q - 1) + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q):=
    Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt S hpredLt
  have htargetActive: ∀ v ∈ rho.honest,
      actionSGBlockAt S rho v (q - 1) ∈
        Protocol.get_filtered_block_tree duty.toHealing.toFG:= by
    intro v hv
    exact
      actionSGBlockAt_mem_filtered_proposerDutyStore_of_gradeFormsAt_exactFGRoot_heightCap
        S adm hformsJ hv hprop hproposalHor hpostPreviousAction hactionDelay
          (by simpa only [duty] using hrootDuty)
          (by simpa only [duty] using hcapDuty)
  have hdepPre: DepReachableStore S.E S.hc S.cfg (S.node p) pre:= by
    simpa only [pre, p, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed proposalRead p)
  have hpcPre: ParentClosed pre:=
    parentClosed_depReachable S.E S.hc S.cfg (S.node p) pre hdepPre
  have hrootPreJ: Protocol.get_fg_root pre.toHealing.toFG = J:= by
    simpa only [duty, Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
      pre, p, proposalRead] using hrootDuty
  have hcapPre: pre.h_max ≤ (derived_state S.E S.cfg J).h + 1:= by
    simpa only [duty, Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
      pre, p, proposalRead] using hcapDuty
  let raw:= (Protocol.proposer_view duty.toHealing.toFG.toSG.toGoldfishStore duty.s).toFinset
  let support:=
    (Protocol.proposer_support_view duty.toHealing.toFG.toSG.toGoldfishStore duty.s).toFinset
  have hJparent: Block.Preceq J
      (Protocol.proposedParent S rho (S.hc.opening_slot q)):= by
    have hfloor:= StoreFinality.get_head_of_preceq_fgRoot
      S.E S.hc duty J raw support (duty.s - 1) (by
        rw [hrootDuty]
        exact Block.preceq_self J)
    change Block.Preceq J
      (Protocol.get_head S.E S.hc duty raw support (duty.s - 1))
    exact hfloor
  refine ⟨?_, ?_⟩
  · intro v hv
    have hconeT:= hlockS.canonical v hv
    have hcompatAT: Block.compatible A (actionSGBlockAt S rho v (q - 1)) = true:=
      sgTargetCompatible_of_honestVotesCone S hcom
        adm.toScheduleWellFormed adm.toRootCollisionFree hconeA hconeT
    have hcompat: Block.compatible
        (Proofs.Optimistic.healAnchor S.E S.hc duty.toHealing)
        (actionSGBlockAt S rho v (q - 1)) = true:= by
      rw [hhealAnchor]
      exact hcompatAT
    have hout:= coneTarget_preceq_nextProposedParent
      S adm hcom hspos hpostConeS hsupportHor
        (by simpa only [s, hsucc] using hprop) hconeT
        (by simpa only [duty, s, hsucc] using htargetActive v hv)
        (by simpa only [duty, s, hsucc] using hcompat)
    simpa only [s, hsucc] using hout
  · intro x hx B hG1
    obtain ⟨v, hv, hBT⟩:= exists_honestSGTarget_extending_g1
      S adm hfb hx hpostPreviousAction hcutPred (by
        simpa only [Nat.sub_add_cancel hqOne] using hG1)
    let T:= actionSGBlockAt S rho v (q - 1)
    have hJT: Block.Preceq J T:= by
      simpa only [T] using
        preceq_actionSGBlockAt_of_gradeFormsAt S hformsJ hv
    have hBT': Block.Preceq B T:= by simpa only [T] using hBT
    have hrootCompat: Block.compatible J B = true:=
      Block.compatible_of_preceq_common hJT hBT'
    simp only [Block.compatible, Bool.or_eq_true] at hrootCompat
    rcases hrootCompat with hJB | hBJ
    · have hTactive: T ∈
          Protocol.get_filtered_block_tree duty.toHealing.toFG:= by
        simpa only [T] using htargetActive v hv
      have hTpre: T ∈ pre.T:= by
        have hTduty:= Proofs.Records.get_filtered_block_tree_subset
          duty.toHealing.toFG hTactive
        simpa only [duty, Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
          pre, p, proposalRead] using hTduty
      have hBpre: B ∈ pre.T:=
        Proofs.Records.mem_of_preceq ((parentClosed_iff pre).mp hpcPre).2
          B T hTpre hBT'
      have hBfilteredPre: B ∈
          Protocol.get_filtered_block_tree pre.toHealing.toFG:=
        mem_filtered_of_mem_tree_of_exactFGRoot_heightCap
          S.E S.hc S.cfg (S.node p) hdepPre hBpre hrootPreJ hJB hcapPre
      have hBactive: B ∈
          Protocol.get_filtered_block_tree duty.toHealing.toFG:= by
        simpa only [duty, Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
          pre, p, proposalRead] using hBfilteredPre
      have hconeB: HonestVotesCone S rho s (fun X => Block.Preceq B X):=
        hconcentration.supported hx (by
          simpa only [Nat.sub_add_cancel hqOne] using hG1)
      have hcompatAB: Block.compatible A B = true:=
        hconcentration.compatible hprop hx
          (by simpa only [p, Nat.sub_add_cancel hqOne] using hAG1Action)
          (by simpa only [Nat.sub_add_cancel hqOne] using hG1)
      have hcompat: Block.compatible
          (Proofs.Optimistic.healAnchor S.E S.hc duty.toHealing) B = true:= by
        rw [hhealAnchor]
        exact hcompatAB
      have hout:= coneTarget_preceq_nextProposedParent
        S adm hcom hspos hpostConeS hsupportHor
          (by simpa only [s, hsucc] using hprop) hconeB
          (by simpa only [duty, s, hsucc] using hBactive)
          (by simpa only [duty, s, hsucc] using hcompat)
      simpa only [s, hsucc] using hout
    · exact Block.preceq_trans hBJ hJparent

/-- Compatibility corollary for the original strict-read interference record. -/
theorem fixedHeightRootOpeningParentRun_of_fixedRootLock
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {H: Height} {w: V} {read: Time} {P: Block V}
    (hfix: FixedHeightRootInterferenceAtRead S rho H w read P)
    {q: Round} {A: Block V} (hq: 0 < q)
    (hforms: GradeFormsAt S rho (q - 1)
      (rho.storeBeforeTime S w read).J)
    (hlock: SGTargetOpeningConeRootLock S rho H (q - 1)
      (S.hc.opening_slot q - 1))
    (hpostRead: S.E.t_GST ≤ read)
    (hproposalDelay: read + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hproposalHor: Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hproposalCap: honestHMaxAt S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) ≤ H)
    (hpostCone: S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot q - 1))
    (hpostPreviousAction: S.E.t_GST ≤ S.a (q - 1))
    (hprop: S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hanchor: Protocol.fresh_anchor S.E S.hc
      (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot q)).toHealing q = some A):
    FixedHeightRootOpeningParentRun S rho q:=
  fixedHeightJustificationRootOpeningParentRun_of_fixedRootLock
    S adm hcom hfb hfix.toJustificationRootAtRead hq hforms hlock hpostRead
      hproposalDelay hproposalHor hproposalCap hpostCone hpostPreviousAction
      hprop hanchor


/-- Standalone callback-free producer for the preceding action-target parent
field. -/
theorem actionTarget_preceq_openingParent_of_fixedJustificationRootLock
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {H: Height} {w: V} {read: Time}
    (hfix: FixedHeightJustificationRootAtRead S rho H w read)
    {q: Round} {A: Block V} (hq: 0 < q)
    (hforms: GradeFormsAt S rho (q - 1)
      (rho.storeBeforeTime S w read).J)
    (hlock: SGTargetOpeningConeRootLock S rho H (q - 1)
      (S.hc.opening_slot q - 1))
    (hpostRead: S.E.t_GST ≤ read)
    (hproposalDelay: read + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hproposalHor: Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hproposalCap: honestHMaxAt S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) ≤ H)
    (hpostCone: S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot q - 1))
    (hpostPreviousAction: S.E.t_GST ≤ S.a (q - 1))
    (hprop: S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hanchor: Protocol.fresh_anchor S.E S.hc
      (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot q)).toHealing q = some A):
    ∀ v ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho v (q - 1))
        (Protocol.proposedParent S rho (S.hc.opening_slot q)):=
  (fixedHeightJustificationRootOpeningParentRun_of_fixedRootLock
    S adm hcom hfb hfix hq hforms hlock hpostRead hproposalDelay
      hproposalHor hproposalCap hpostCone hpostPreviousAction hprop hanchor).actionTargetParent

/-- Compatibility corollary for the original strict-read interference record. -/
theorem actionTarget_preceq_openingParent_of_fixedRootLock
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {H: Height} {w: V} {read: Time} {P: Block V}
    (hfix: FixedHeightRootInterferenceAtRead S rho H w read P)
    {q: Round} {A: Block V} (hq: 0 < q)
    (hforms: GradeFormsAt S rho (q - 1)
      (rho.storeBeforeTime S w read).J)
    (hlock: SGTargetOpeningConeRootLock S rho H (q - 1)
      (S.hc.opening_slot q - 1))
    (hpostRead: S.E.t_GST ≤ read)
    (hproposalDelay: read + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hproposalHor: Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hproposalCap: honestHMaxAt S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) ≤ H)
    (hpostCone: S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot q - 1))
    (hpostPreviousAction: S.E.t_GST ≤ S.a (q - 1))
    (hprop: S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hanchor: Protocol.fresh_anchor S.E S.hc
      (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot q)).toHealing q = some A):
    ∀ v ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho v (q - 1))
        (Protocol.proposedParent S rho (S.hc.opening_slot q)):=
  actionTarget_preceq_openingParent_of_fixedJustificationRootLock
    S adm hcom hfb hfix.toJustificationRootAtRead hq hforms hlock hpostRead
      hproposalDelay hproposalHor hproposalCap hpostCone hpostPreviousAction
      hprop hanchor


/-- Standalone callback-free producer for every live round-`q` G1 block at an
honest action read. -/
theorem liveG1_preceq_openingParent_of_fixedJustificationRootLock
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {H: Height} {w: V} {read: Time}
    (hfix: FixedHeightJustificationRootAtRead S rho H w read)
    {q: Round} {A: Block V} (hq: 0 < q)
    (hforms: GradeFormsAt S rho (q - 1)
      (rho.storeBeforeTime S w read).J)
    (hlock: SGTargetOpeningConeRootLock S rho H (q - 1)
      (S.hc.opening_slot q - 1))
    (hpostRead: S.E.t_GST ≤ read)
    (hproposalDelay: read + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hproposalHor: Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hproposalCap: honestHMaxAt S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) ≤ H)
    (hpostCone: S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot q - 1))
    (hpostPreviousAction: S.E.t_GST ≤ S.a (q - 1))
    (hprop: S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hanchor: Protocol.fresh_anchor S.E S.hc
      (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot q)).toHealing q = some A)
    {x: V} (hx: x ∈ rho.honest) {B: Block V}
    (hG1: Protocol.G1 S.E (gradeViewAt S rho x q) S.hc q B = true):
    Block.Preceq B
      (Protocol.proposedParent S rho (S.hc.opening_slot q)):=
  (fixedHeightJustificationRootOpeningParentRun_of_fixedRootLock
    S adm hcom hfb hfix hq hforms hlock hpostRead hproposalDelay
      hproposalHor hproposalCap hpostCone hpostPreviousAction hprop hanchor).liveG1Parent
        x hx B hG1

/-- Compatibility corollary for the original strict-read interference record. -/
theorem liveG1_preceq_openingParent_of_fixedRootLock
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {H: Height} {w: V} {read: Time} {P: Block V}
    (hfix: FixedHeightRootInterferenceAtRead S rho H w read P)
    {q: Round} {A: Block V} (hq: 0 < q)
    (hforms: GradeFormsAt S rho (q - 1)
      (rho.storeBeforeTime S w read).J)
    (hlock: SGTargetOpeningConeRootLock S rho H (q - 1)
      (S.hc.opening_slot q - 1))
    (hpostRead: S.E.t_GST ≤ read)
    (hproposalDelay: read + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hproposalHor: Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hproposalCap: honestHMaxAt S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) ≤ H)
    (hpostCone: S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot q - 1))
    (hpostPreviousAction: S.E.t_GST ≤ S.a (q - 1))
    (hprop: S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hanchor: Protocol.fresh_anchor S.E S.hc
      (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot q)).toHealing q = some A)
    {x: V} (hx: x ∈ rho.honest) {B: Block V}
    (hG1: Protocol.G1 S.E (gradeViewAt S rho x q) S.hc q B = true):
    Block.Preceq B
      (Protocol.proposedParent S rho (S.hc.opening_slot q)):=
  liveG1_preceq_openingParent_of_fixedJustificationRootLock
    S adm hcom hfb hfix.toJustificationRootAtRead hq hforms hlock hpostRead
      hproposalDelay hproposalHor hproposalCap hpostCone hpostPreviousAction
      hprop hanchor hx hG1

-/


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
