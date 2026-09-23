module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.FinalityMonotoneCore
public import DecoupledConsensusProofs.Objects.BlockVisibilityCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.ProposalCore
public import DecoupledConsensusProofs.Generic.PostGSTCarrierAdmissionCore
public import DecoupledConsensusProofs.Protocol.Schedule.Action
public import DecoupledConsensusInternal.Definitions.PhaseGradeQueries
public import DecoupledConsensusProofs.Protocol.Grades.VoteBelowSource
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.Grades.Q10Frame

@[expose] public section

/-!
# Action sources and SG carrier resolution

This module isolates the exact action source, its selected SG carrier, and the
post-GST relay that resolves that carrier at a later honest proposal. These
facts depend only on the run, availability, and common-grade surfaces.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Transfer of a common grade into the action store -/

/-- The confirmation write immediately before the round action does not
change the filtered block tree. -/
theorem actionStoreAt_filteredTree
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    Protocol.get_filtered_block_tree
        (actionStoreAt S rho v r).toHealing.toFG =
      Protocol.get_filtered_block_tree
        (healStoreAt S rho v r).toFG := by
  have hσ : (actionStoreAt S rho v r).st.core.σ =
      (rho.storeBeforeTime S v (S.a r)).core.σ := rfl
  have hT : (actionStoreAt S rho v r).st.core.T =
      (rho.storeBeforeTime S v (S.a r)).core.T := rfl
  have hJ : (actionStoreAt S rho v r).st.core.J =
      (rho.storeBeforeTime S v (S.a r)).core.J := rfl
  have hF : (actionStoreAt S rho v r).st.core.F =
      (rho.storeBeforeTime S v (S.a r)).core.F := rfl
  have hhmax : (actionStoreAt S rho v r).st.core.h_max =
      (rho.storeBeforeTime S v (S.a r)).core.h_max := rfl
  have hhj : (actionStoreAt S rho v r).st.core.h_j =
      (rho.storeBeforeTime S v (S.a r)).core.h_j := rfl
  change Protocol.get_filtered_block_tree
      (actionStoreAt S rho v r).st.core.toHealing.toFG =
    Protocol.get_filtered_block_tree
      (rho.storeBeforeTime S v (S.a r)).core.toHealing.toFG
  unfold Protocol.get_filtered_block_tree
    Protocol.get_filtered_block_tree_from
    Protocol.viable_tree Protocol.finalized_descendants
    Protocol.viable Protocol.get_fg_root
  simp only [Protocol.Store.toHealing]
  simp only [hσ, hT, hJ, hF, hhmax, hhj]
  rfl

/-! ## The frozen round-`r` frame the action reads

Under the frame runtime the round action does not re-evaluate a grade. Its
grade contract is `NamedProfile.gradeContract n.cache`, whose read is
`DecoupledConsensusModel.Protocol.frameGradeRead`: each round-`r` phase root was frozen once,
at that phase's own domain tick, and every later read returns it clipped
against the reader's current finalized block. The facts below are that frame,
at the prepared action read.
-/


/-- Every phase slot of round `r` is closed at an honest node's action read, and
holds the freeze that node's own domain tick computed, clipped against the
action's finalized block. -/
theorem actionFrame_phase_completed (S : Setup V) {rho : Run V}
    (core : NamedAdmissibleCore S rho) {v : V} (hv : v ∈ rho.honest)
    {r : Round} (hr : 0 < r) (hhor : S.a r ≤ rho.horizon) (p : DecoupledConsensusModel.Protocol.Phase) :
    DecoupledConsensusModel.Protocol.phaseResult
        (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho v r).cache
          (actionReadAt S rho v r).st.core.toHealing r) p =
      some ((PhaseGrades.storeRoot S.E S.hc
          (NamedRun.stateBeforeTime S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r p) v).st r p).map
        (fun B => DecoupledConsensusModel.Protocol.clipGrade B
          (actionReadAt S rho v r).st.core.F)) :=
  FrameForward.frame_phase_checkpoint_eq S rho v r p _
    (FrameCompleted.frame_phase_completed S rho core v hv r hr p (S.a r)
      (NamedOutageClosure.q10_domain_lt_a S r p) le_rfl
      (le_trans (FrameForward.domain_le_a S r p) hhor))

/-- The prepared action read and the round checkpoint read the same round-`r`
frame. `readFrame` consults only the cache and the finalized block, and the
action's confirmation write changes neither. -/
theorem actionRead_readFrame_eq_checkpoint (S : Setup V) (rho : Run V) (v : V)
    (r : Round) :
    DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho v r).cache
        (actionReadAt S rho v r).st.core.toHealing r =
      DecoupledConsensusModel.Protocol.readFrame (Internal.NamedJointOutage.checkpoint S rho v r).cache
        (Internal.NamedJointOutage.checkpoint S rho v r).st.core.toHealing r := rfl

/-- The G2 slot form. -/
theorem actionFrame_g2 (S : Setup V) {rho : Run V}
    (core : NamedAdmissibleCore S rho) {v : V} (hv : v ∈ rho.honest)
    {r : Round} (hr : 0 < r) (hhor : S.a r ≤ rho.horizon) :
    (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho v r).cache
        (actionReadAt S rho v r).st.core.toHealing r).g2 =
      some ((PhaseGrades.storeRoot S.E S.hc
          (NamedRun.stateBeforeTime S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) v).st r .g2).map
        (fun B => DecoupledConsensusModel.Protocol.clipGrade B
          (actionReadAt S rho v r).st.core.F)) :=
  actionFrame_phase_completed S core hv hr hhor .g2

/-- The G1 slot form. -/
theorem actionFrame_g1 (S : Setup V) {rho : Run V}
    (core : NamedAdmissibleCore S rho) {v : V} (hv : v ∈ rho.honest)
    {r : Round} (hr : 0 < r) (hhor : S.a r ≤ rho.horizon) :
    (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho v r).cache
        (actionReadAt S rho v r).st.core.toHealing r).g1 =
      some ((PhaseGrades.storeRoot S.E S.hc
          (NamedRun.stateBeforeTime S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) v).st r .g1).map
        (fun B => DecoupledConsensusModel.Protocol.clipGrade B
          (actionReadAt S rho v r).st.core.F)) :=
  actionFrame_phase_completed S core hv hr hhor .g1

/-- The G0 slot form. -/
theorem actionFrame_g0 (S : Setup V) {rho : Run V}
    (core : NamedAdmissibleCore S rho) {v : V} (hv : v ∈ rho.honest)
    {r : Round} (hr : 0 < r) (hhor : S.a r ≤ rho.horizon) :
    (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho v r).cache
        (actionReadAt S rho v r).st.core.toHealing r).g0 =
      some ((PhaseGrades.storeRoot S.E S.hc
          (NamedRun.stateBeforeTime S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0) v).st r .g0).map
        (fun B => DecoupledConsensusModel.Protocol.clipGrade B
          (actionReadAt S rho v r).st.core.F)) :=
  actionFrame_phase_completed S core hv hr hhor .g0

/-- All three phase results of round `r` are complete at an honest action read.
This is what lets the action consume its saved G2 root at all. -/
theorem actionFrame_allClosed (S : Setup V) {rho : Run V}
    (core : NamedAdmissibleCore S rho) {v : V} (hv : v ∈ rho.honest)
    {r : Round} (hr : 0 < r) (hhor : S.a r ≤ rho.horizon) :
    DecoupledConsensusModel.Protocol.allClosed
        (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho v r).cache
          (actionReadAt S rho v r).st.core.toHealing r) = true := by
  simp only [DecoupledConsensusModel.Protocol.allClosed, Bool.and_eq_true,
    actionFrame_g0 S core hv hr hhor, actionFrame_g1 S core hv hr hhor,
    actionFrame_g2 S core hv hr hhor, Option.isSome_some, and_self]

omit [Fintype V] in
/-- A block the FG filter keeps is a processed block. -/
theorem mem_T_of_mem_filteredTree {st : Protocol.Store V} {B : Block V}
    (h : B ∈ Protocol.get_filtered_block_tree st.toHealing.toFG) : B ∈ st.T := by
  simp only [Protocol.get_filtered_block_tree,
    Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
    Protocol.finalized_descendants, Finset.mem_filter,
    Protocol.Store.toHealing] at h
  exact h.1.1.1

/-! ## Transfer of a common grade into the action's frozen candidate -/

/-- **The frozen-frame replacement of `gradeFormsAt_actionStore`.** A block
graded G2 at an honest node's own G2-domain read — the store `freezeRoot`
consumed — and still active at that node's action read is at or below the
action's frozen, clipped, active G2 candidate.

No cross-tick stability is assumed. The grade is read at the freeze tick, the
frame carries it forward (`FrameCompleted`, `FrameForward`), and clipping only
shortens a root toward the finalized block, which a still-active block is
compatible with. -/
theorem preceq_actionQ2_of_domainGrade (S : Setup V) {rho : Run V}
    (core : NamedAdmissibleCore S rho) {v : V} (hv : v ∈ rho.honest)
    {r : Round} (hr : 0 < r) (hhor : S.a r ≤ rho.horizon) {C : Block V}
    (hmem : C ∈ PhaseGrades.filteredTree
      (NamedRun.stateBeforeTime S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) v))
    (hgrade : PhaseGrades.storeGrade S.E S.hc
      (NamedRun.stateBeforeTime S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) v).st
      r .g2 C = true)
    (hactive : C ∈ PhaseGrades.filteredTree (actionReadAt S rho v r)) :
    ∃ Q : Block V,
      PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r = some Q ∧ Block.Preceq C Q := by
  have hT : C ∈ (NamedRun.stateBeforeTime S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) v).st.core.T := mem_T_of_mem_filteredTree hmem
  obtain ⟨raw, hfz, hCraw⟩ := NamedOutageClosure.q10_freeze_of_graded S.E
    (NamedRun.stateBeforeTime S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) v).st.core.toHealing.gradeView
    (NamedRun.stateBeforeTime S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) v).st.core.F
    S.hc.η_SG r (NamedOutageClosure.q10_early_le_late S r .g2) hT hgrade
  have hFC : Block.Preceq (actionReadAt S rho v r).st.core.F C :=
    NamedOutageClosure.q10_filtered_F hactive
  have hcompat : Block.compatible C (actionReadAt S rho v r).st.core.F = true := by
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr hFC
  have hCclip : Block.Preceq C
      (DecoupledConsensusModel.Protocol.clipGrade raw (actionReadAt S rho v r).st.core.F) :=
    (NamedOutageClosure.q10_retained_prefix raw
      (actionReadAt S rho v r).st.core.F C hcompat).mpr hCraw
  obtain ⟨X, hX, hCX⟩ := NamedOutageClosure.q10_activePrefix_dominates hactive hCclip
  refine ⟨X, ?_, hCX⟩
  show DecoupledConsensusModel.Protocol.grade2Block (actionReadAt S rho v r).st.core.toHealing
    (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho v r).cache
      (actionReadAt S rho v r).st.core.toHealing r) = some X
  unfold DecoupledConsensusModel.Protocol.grade2Block
  rw [if_pos (actionFrame_allClosed S core hv hr hhor), actionFrame_g2 S core hv hr hhor,
    show PhaseGrades.storeRoot S.E S.hc (NamedRun.stateBeforeTime S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) v).st r .g2 = some raw from hfz]
  exact hX

/-- The `NamedGradeFormsAt` form: a common G2 grade of round `r` is at or below
every honest validator's own frozen action candidate, wherever it is still
active at that validator's action read. This replaces `gradeFormsAt_actionStore`
and `GradeFormsAt`. -/
theorem namedGradeFormsAt_preceq_actionQ2 (S : Setup V) {rho : Run V}
    (core : NamedAdmissibleCore S rho) {r : Round} (hr : 0 < r)
    (hhor : S.a r ≤ rho.horizon) {C : Block V}
    (hforms : NamedGradeFormsAt S rho r C) {v : V} (hv : v ∈ rho.honest)
    (hactive : C ∈ PhaseGrades.filteredTree (actionReadAt S rho v r)) :
    ∃ Q : Block V,
      PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r = some Q ∧ Block.Preceq C Q :=
  preceq_actionQ2_of_domainGrade S core hv hr hhor (hforms v hv).1 (hforms v hv).2 hactive

/-- Row Q10 at the action read: the frozen active G2 candidate is at or below the
frozen anchor. This is the step row Q11 leaves open at an arbitrary node; here
the node is honest and the round is inside the run. -/
theorem actionQ2_preceq_actionAnchor (S : Setup V) {rho : Run V}
    (core : NamedAdmissibleCore S rho) {v : V} (hv : v ∈ rho.honest)
    {r : Round} (hr : 0 < r) (hhor : S.a r ≤ rho.horizon) {Q : Block V}
    (hq : PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r = some Q) :
    Block.Preceq Q (PhaseGrades.nodeAnchor S (actionReadAt S rho v r) r) :=
  NamedOutageClosure.grade2_preceq_anchor_at_checkpoint S rho core v hv (S.a r) r
    ⟨hr, le_rfl, hhor⟩ Q hq

/-- The action's frozen candidate is at or below the action's SG carrier: the
selector either walks up from the anchor, or returns the candidate itself. -/
theorem preceq_actionSGBlockAt_of_actionQ2 (S : Setup V) {rho : Run V}
    (core : NamedAdmissibleCore S rho) {v : V} (hv : v ∈ rho.honest)
    {r : Round} (hr : 0 < r) (hhor : S.a r ≤ rho.horizon) {C Q : Block V}
    (hq : PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r = some Q)
    (hCQ : Block.Preceq C Q) :
    Block.Preceq C (actionSGBlockAt S rho v r) := by
  set n := actionReadAt S rho v r with hn
  set st := n.st.core.toHealing with hst
  set grades := DecoupledConsensusModel.Protocol.frameGradeRead n.cache S.E S.hc st r with hgr
  have hk : S.hc.round_of st.s = r := Proofs.HealingLemmas.round_of_slotOf_a S r
  have heq : actionSGBlockAt S rho v r = Protocol.currentSGVote st grades := by
    show Protocol.get_sg_vote_with (NamedProfile.gradeContract n.cache) S.E S.hc st
        (S.hc.round_of st.s)
        (Protocol.grade2_block_with (NamedProfile.gradeContract n.cache) S.E S.hc st
          (S.hc.round_of st.s)) = Protocol.currentSGVote st grades
    rw [hk]; rfl
  have hQ2 : grades.Q2 = some Q := hq
  have hanchor : Block.Preceq Q grades.anchor :=
    actionQ2_preceq_actionAnchor S core hv hr hhor hq
  rw [heq]
  unfold Protocol.currentSGVote
  cases hdc : Protocol.deepest_clear (some grades.anchor) st.live_confirmed grades.clear with
  | none =>
      simp only [hQ2]
      exact hCQ
  | some B =>
      simp only []
      have hAB : Block.Preceq grades.anchor B := by
        have hmem := Proofs.Engine.deepest?_mem hdc
        unfold Protocol.deepest_clear at hmem
        exact (Finset.mem_filter.mp hmem).2.1
      exact Block.preceq_trans hCQ (Block.preceq_trans hanchor hAB)

/-- The action's frozen candidate is at or below the action's FG source: the
source is the candidate, or a clear block above it. -/
theorem preceq_actionFGSource_of_actionQ2 (S : Setup V) (rho : Run V) (v : V)
    (r : Round) {C Q X : Block V}
    (hq : PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r = some Q)
    (hCQ : Block.Preceq C Q)
    (hsource : PhaseGrades.nodeFGSource S (actionReadAt S rho v r) r = some X) :
    Block.Preceq C X := by
  have hQ2 : Protocol.grade2_block_with
      (NamedProfile.gradeContract (actionReadAt S rho v r).cache) S.E S.hc
      (actionReadAt S rho v r).st.core.toHealing r = some Q := hq
  rw [PhaseGrades.nodeFGSource, Protocol.fg_source_with.eq_def, hQ2] at hsource
  cases hwalk : Protocol.deepest_clear (some Q)
      (actionReadAt S rho v r).st.core.toHealing.live_confirmed
      ((NamedProfile.gradeContract (actionReadAt S rho v r).cache).read S.E S.hc
        (actionReadAt S rho v r).st.core.toHealing r).clear with
  | none =>
      simp only [hwalk] at hsource
      rw [← Option.some_inj.mp hsource]
      exact hCQ
  | some B =>
      simp only [hwalk] at hsource
      have hQB : Block.Preceq Q B := by
        have hmem := Proofs.Engine.deepest?_mem hwalk
        unfold Protocol.deepest_clear at hmem
        exact (Finset.mem_filter.mp hmem).2.1
      rw [← Option.some_inj.mp hsource]
      exact Block.preceq_trans hCQ hQB

/-- The action's FG source is nonempty once its frozen candidate exists. -/
theorem exists_actionFGSource_of_actionQ2 (S : Setup V) (rho : Run V) (v : V)
    (r : Round) {Q : Block V}
    (hq : PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r = some Q) :
    ∃ X : Block V, PhaseGrades.nodeFGSource S (actionReadAt S rho v r) r = some X := by
  have hQ2 : Protocol.grade2_block_with
      (NamedProfile.gradeContract (actionReadAt S rho v r).cache) S.E S.hc
      (actionReadAt S rho v r).st.core.toHealing r = some Q := hq
  rw [PhaseGrades.nodeFGSource, Protocol.fg_source_with.eq_def, hQ2]
  cases hwalk : Protocol.deepest_clear (some Q)
      (actionReadAt S rho v r).st.core.toHealing.live_confirmed
      ((NamedProfile.gradeContract (actionReadAt S rho v r).cache).read S.E S.hc
        (actionReadAt S rho v r).st.core.toHealing r).clear with
  | none => exact ⟨Q, by simp only [hwalk]⟩
  | some B => exact ⟨B, by simp only [hwalk]⟩

/-! ## A local active grade is preserved by the SG selector -/



/-- A non-genesis block in a pre-time store was accepted at that node strictly
before the read. This is the direct event-prefix form of block provenance; it
does not need a timestamp argument. -/
theorem block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTime
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    (v : V) (read : Time) {B : Block V}
    (hB : B ∈ (rho.storeBeforeTime S v read).T) :
    B = Block.genesis ∨
      ∃ (D : NamedBlock V) (i : Nat) (t : Time),
        D.erase = B ∧ Run.acceptsAt S rho i v (.block D) t ∧ t < read := by
  obtain ⟨N, hN, hNlt⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S sch read
  have hread : rho.storeBeforeTime S v read = (rho.stateBefore S N v).st := by
    unfold Run.storeBeforeTime
    exact congrArg NamedNodeState.st (congrFun hN v)
  have hB' : B ∈ (rho.stateBefore S N v).st.core.T := by
    simpa only [← hread] using hB
  obtain ⟨D, hDbodies, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho N v hB'
  have hprocessed : Object.processed (rho.stateBefore S N v).st (.block D) = true := by
    simp only [Object.processed, NamedReceipt.processed, decide_eq_true_eq]
    exact hDbodies
  rcases Protocol.acceptsAt_block_of_processed S rho v N D hprocessed with
    hgen | ⟨i, hiN, t, hacc⟩
  · exact Or.inl (by rw [← hDerase, hgen]; rfl)
  · obtain ⟨-, e, he, -, het⟩ := hacc.1
    have heLt : e.time < read := hNlt i e hiN he
    exact Or.inr ⟨D, i, t, hDerase, hacc, by simpa only [het] using heLt⟩

/-! ## The exact action source and carrier -/

/-- The action's frozen candidate is itself an active block of the action read. -/
theorem actionQ2_mem_filteredTree (S : Setup V) (rho : Run V) (v : V) (r : Round)
    {Q : Block V} (hq : PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r = some Q) :
    Q ∈ PhaseGrades.filteredTree (actionReadAt S rho v r) := by
  have hq' : DecoupledConsensusModel.Protocol.grade2Block
      (actionReadAt S rho v r).st.core.toHealing
      (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho v r).cache
        (actionReadAt S rho v r).st.core.toHealing r) = some Q := hq
  unfold DecoupledConsensusModel.Protocol.grade2Block at hq'
  by_cases hcl : DecoupledConsensusModel.Protocol.allClosed
      (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho v r).cache
        (actionReadAt S rho v r).st.core.toHealing r) = true
  · rw [if_pos hcl] at hq'
    obtain ⟨root, -, hact⟩ := Option.bind_eq_some_iff.mp hq'
    unfold DecoupledConsensusModel.Protocol.activePrefix at hact
    exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hact)).1
  · rw [if_neg hcl] at hq'
    exact absurd hq' (by simp)

/-- A common grade makes the exact action FG source nonempty. -/
theorem exists_actionFGSource_of_namedGradeFormsAt (S : Setup V) {rho : Run V}
    (core : NamedAdmissibleCore S rho) {r : Round} (hr : 0 < r)
    (hhor : S.a r ≤ rho.horizon) {C : Block V}
    (hforms : NamedGradeFormsAt S rho r C) {v : V} (hv : v ∈ rho.honest)
    (hactive : C ∈ PhaseGrades.filteredTree (actionReadAt S rho v r)) :
    ∃ X : Block V, PhaseGrades.nodeFGSource S (actionReadAt S rho v r) r = some X := by
  obtain ⟨Q, hq, -⟩ := namedGradeFormsAt_preceq_actionQ2 S core hr hhor hforms hv hactive
  exact exists_actionFGSource_of_actionQ2 S rho v r hq

/-- A common grade block precedes every exact FG source selected by an honest
action read. -/
theorem namedGradeFormsAt_preceq_actionSource (S : Setup V) {rho : Run V}
    (core : NamedAdmissibleCore S rho) {r : Round} (hr : 0 < r)
    (hhor : S.a r ≤ rho.horizon) {C X : Block V}
    (hforms : NamedGradeFormsAt S rho r C) {v : V} (hv : v ∈ rho.honest)
    (hactive : C ∈ PhaseGrades.filteredTree (actionReadAt S rho v r))
    (hsource : PhaseGrades.nodeFGSource S (actionReadAt S rho v r) r = some X) :
    Block.Preceq C X := by
  obtain ⟨Q, hq, hCQ⟩ := namedGradeFormsAt_preceq_actionQ2 S core hr hhor hforms hv hactive
  exact preceq_actionFGSource_of_actionQ2 S rho v r hq hCQ hsource

/-- A common grade in round `r` is below every honest validator's exact
Section 7 SG action carrier. -/
theorem preceq_actionSGBlockAt_of_namedGradeFormsAt (S : Setup V) {rho : Run V}
    (core : NamedAdmissibleCore S rho) {r : Round} (hr : 0 < r)
    (hhor : S.a r ≤ rho.horizon) {C : Block V}
    (hforms : NamedGradeFormsAt S rho r C) {v : V} (hv : v ∈ rho.honest)
    (hactive : C ∈ PhaseGrades.filteredTree (actionReadAt S rho v r)) :
    Block.Preceq C (actionSGBlockAt S rho v r) := by
  obtain ⟨Q, hq, hCQ⟩ := namedGradeFormsAt_preceq_actionQ2 S core hr hhor hforms hv hactive
  exact preceq_actionSGBlockAt_of_actionQ2 S core hv hr hhor hq hCQ

/-- The exact SG action carrier is a processed block in the action read's store.
The frozen candidate rules out both raw-anchor fallbacks: the selector returns
either an ancestor of `live_confirmed` or the candidate itself. -/
theorem actionSGBlockAt_mem_actionStore_of_actionQ2 (S : Setup V) (rho : Run V)
    (v : V) (r : Round) {Q : Block V}
    (hq : PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r = some Q) :
    actionSGBlockAt S rho v r ∈ (actionReadAt S rho v r).st.core.T := by
  set n := actionReadAt S rho v r with hn
  set st := n.st.core.toHealing with hst
  set grades := DecoupledConsensusModel.Protocol.frameGradeRead n.cache S.E S.hc st r with hgr
  have hk : S.hc.round_of st.s = r := Proofs.HealingLemmas.round_of_slotOf_a S r
  have heq : actionSGBlockAt S rho v r = Protocol.currentSGVote st grades := by
    show Protocol.get_sg_vote_with (NamedProfile.gradeContract n.cache) S.E S.hc st
        (S.hc.round_of st.s)
        (Protocol.grade2_block_with (NamedProfile.gradeContract n.cache) S.E S.hc st
          (S.hc.round_of st.s)) = Protocol.currentSGVote st grades
    rw [hk]; rfl
  have hQ2 : grades.Q2 = some Q := hq
  have hpc : ParentClosed n.st.core := by
    have h := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho (S.a r) v
    rw [parentClosed_iff] at h ⊢
    exact h
  have hlc : st.live_confirmed ∈ n.st.core.T := by
    have h0 : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
        (rho.stateBeforeTime S (S.a r) v).st :=
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a r) v).1
    have h1 := Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ (S.a r) h0
    exact (Proofs.NamedConfirmationMembership.invariant_update
      (NamedActionReads.preparedCache S (rho.stateBeforeTime S (S.a r) v) (S.a r))
      S.E S.hc S.cfg _ (S.E.slotOf (S.a r) - 1) h1).2.1
  rw [heq]
  unfold Protocol.currentSGVote
  cases hdc : Protocol.deepest_clear (some grades.anchor) st.live_confirmed grades.clear with
  | none =>
      simp only [hQ2]
      exact mem_T_of_mem_filteredTree (actionQ2_mem_filteredTree S rho v r hq)
  | some B =>
      simp only []
      exact Proofs.Records.mem_of_preceq ((parentClosed_iff n.st.core).mp hpc).2 B
        st.live_confirmed hlc (Proofs.Engine.deepest_clear_preceq hdc)


/-! ## Relaying the exact action carrier to a later proposal -/

/-- If `P` is active at a later strict read and `P ⪯ C`, every delivery of
`C` before an earlier cutoff sees a finalized block below `C`. -/
theorem finalizedBelowAtDeliveriesBefore_of_filteredAtLaterRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} {P : Block V} {C : NamedBlock V} {cut read : Time}
    (hcut : cut ≤ read)
    (hactive : P ∈ Protocol.get_filtered_block_tree
      (rho.storeBeforeTime S w read).toHealing.toFG)
    (hPC : Block.Preceq P C.erase) :
    Protocol.BlockFinalizedBelowAtDeliveriesBefore
      S rho w C cut := by
  let N := (rho.events.filter (fun e => decide (e.time < read))).length
  have hWorld : Run.stateBeforeTime S rho read = Run.stateBefore S rho N :=
    Proofs.Optimistic.stateBeforeTime_eq_take S adm.toNamedScheduleWellFormed read
  have hread : rho.storeBeforeTime S w read =
      (rho.stateBefore S N w).st := by
    unfold Run.storeBeforeTime
    exact congrArg NamedNodeState.st (congrFun hWorld w)
  have hFread : Block.Preceq (rho.stateBefore S N w).st.F P := by
    have hactive' := hactive
    simp only [Protocol.get_filtered_block_tree,
      Protocol.get_filtered_block_tree_from,
      Protocol.viable_tree, Protocol.finalized_descendants,
      Finset.mem_filter, Protocol.Store.toHealing, hread] at hactive'
    exact hactive'.1.1.2
  intro i hi
  have hiN : i ≤ N := hi.trans (strict_filter_length_mono rho hcut)
  exact Block.preceq_trans
    (Protocol.stateBefore_F_mono S rho w hiN)
    (Block.preceq_trans hFread hPC)






end HealingSurface
end Proofs
end DecoupledConsensusModel

end
