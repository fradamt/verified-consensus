module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryProposalWindow
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryProposalConfirmation
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionActivity
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsBridge

@[expose] public section

/-!
# Recovery proposal confirmation-read producer

At an opening slot of round `q`, the confirmation read is exactly the round
action time `a_q`. A persistent `GradeFormsAt q P` therefore places `P` in
the real confirmation candidate tree. This immediately puts the confirmation
FG root below `P`.

If the bounded honest proposal descends from `P`, that floor also supplies all
finalized-root guards needed for post-GST proposal admission. The proposal is
a confirmation candidate once its own derived height reaches the local
viability threshold `h_max - 1`.

The SG-anchor field remains separate. A common G2 at `P` places the later
fresh anchor above `P`; it does not orient that anchor below the fresh
proposal. The exact-proposal constructor therefore exposes one local
reflection residual. A separate result proves the reflection-free statement:
all honest opening outputs lie on one common chain through `P`.
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
open DecoupledConsensusModel.Protocol
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The persistent grade is already at the confirmation read -/

/-- The opening slot's confirmation time is its round action time. -/
theorem opening_confirmation_time_eq_action
    (S : Setup V) (q : Round) :
    Protocol.confirmation_time S.E (S.hc.opening_slot q) = S.a q :=
  (Protocol.a_eq_confirmation_time S.hc S.E q).symm

/-

/-- A round-`q` common grade places its block in every honest opening-slot
confirmation candidate tree. -/
theorem protected_candidateAtOpeningConfirmation_of_gradeFormsAt
    (S: Setup V) {rho: Run V} {q: Round} {P: Block V}
    (hforms: GradeFormsAt S rho q P) {v: V} (hv: v ∈ rho.honest):
    P ∈ confTree
      (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q)):= by
  have hP:= (hforms v hv).1
  simpa only [confTree, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
    healStoreAt, opening_confirmation_time_eq_action] using hP

/-- The same grade directly orients the exact confirmation FG root below its
protected block. -/
theorem confRoot_preceq_protected_of_gradeFormsAt
    (S: Setup V) {rho: Run V} {q: Round} {P: Block V}
    (hforms: GradeFormsAt S rho q P) {v: V} (hv: v ∈ rho.honest):
    Block.Preceq
      (confRoot (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q))) P:= by
  have hP:= protected_candidateAtOpeningConfirmation_of_gradeFormsAt
    S hforms hv
  exact Proofs.Records.preceq_get_fg_root_of_mem_filtered hP

/-! ## Honest proposal admission from the grade floor -/

/-- The confirmation-grade floor supplies every finalized-root guard used
while the honest proposal is delivered before its vote duty. -/
theorem proposedBlock_finalizedBelowAtDeliveries_of_openingGrade
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {q: Round} {P: Block V}
    (hforms: GradeFormsAt S rho q P)
    (hPparent: Block.Preceq P
      (Internal.proposedBlock S rho
        (S.hc.opening_slot q)).parent):
    ProposalFinalizedBelowAtDeliveries S rho (S.hc.opening_slot q)
      (Internal.proposedBlock S rho (S.hc.opening_slot q)):= by
  let s:= S.hc.opening_slot q
  let B:= Internal.proposedBlock S rho s
  have hPB: Block.Preceq P B:= by
    exact Block.preceq_trans hPparent
      (Protocol.preceq_of_parent?
        (Protocol.proposedBlock_parent S rho s))
  intro v hv i t hi _ htVote
  have hrootP:= confRoot_preceq_protected_of_gradeFormsAt
    S hforms hv
  have htCut: t < Protocol.support_cutoff S.E s:= by
    exact htVote.trans (by
      rw [← Proofs.Optimistic.vote_time_add_delta]
      exact Int.lt_add_of_pos_right _ S.E.Δ_pos)
  exact Block.preceq_trans
    (finalized_preceq_at_delivery_of_confRoot_preceq
      S adm (by simpa only [s] using hrootP) hi htCut)
    (by simpa only [B] using hPB)

/-- Post-GST synchrony and the confirmation-grade floor accept the bounded
honest opening proposal before every honest vote duty. -/
theorem proposedBlock_admittedBeforeVote_of_openingGrade
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {q: Round} (hq: 0 < q) {P: Block V}
    (hforms: GradeFormsAt S rho q P)
    (hPparent: Block.Preceq P
      (Internal.proposedBlock S rho
        (S.hc.opening_slot q)).parent)
    (hprop: S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hpost: S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hvoteHor: Protocol.vote_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon):
    ∀ v ∈ rho.honest,
      AdmittedBefore S rho v
        (Internal.proposedBlock S rho (S.hc.opening_slot q))
        (Protocol.vote_time S.E (S.hc.opening_slot q)):= by
  have hs: 0 < S.hc.opening_slot q:= by
    exact Nat.mul_pos hq
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  exact proposedBlock_admittedBefore_vote_after_gst
    S adm hs hprop
      hpost hvoteHor
      (proposedBlock_finalizedBelowAtDeliveries_of_openingGrade
        S adm hforms hPparent)

/-! ## Candidate survival under the exact local height cap -/

/-- The exact numerical condition needed to use the proposal itself as the
confirmation-store viability witness. -/
def RecoveryProposalConfirmationHeightCap
    (S: Setup V) (rho: Run V) (q: Round) (v: V): Prop:=
  let s:= S.hc.opening_slot q
  let st:= Proofs.Optimistic.confStore S rho v s
  st.h_max - 1 ≤
    (derived_state S.E S.cfg (Internal.proposedBlock S rho s)).h

/-- A processed proposal above the local viability threshold is a candidate
at the opening confirmation read. -/
theorem proposedBlock_candidateAtOpeningConfirmation_of_gradeFormsAt_and_heightCap
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {q: Round} (hq: 0 < q) {P: Block V}
    (hforms: GradeFormsAt S rho q P)
    (hPparent: Block.Preceq P
      (Internal.proposedBlock S rho
        (S.hc.opening_slot q)).parent)
    (hprop: S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hpost: S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hconfHor: Protocol.confirmation_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    {v: V} (hv: v ∈ rho.honest)
    (hcap: RecoveryProposalConfirmationHeightCap S rho q v):
    Internal.proposedBlock S rho (S.hc.opening_slot q) ∈
      confTree (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q)):= by
  let s:= S.hc.opening_slot q
  let B:= Internal.proposedBlock S rho s
  let read:= Protocol.confirmation_time S.E s
  let pre:= rho.storeBeforeTime S v read
  let st:= Proofs.Optimistic.confStore S rho v s
  have hs: 0 < s:= by
    exact Nat.mul_pos hq
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hvoteHor: Protocol.vote_time S.E s ≤ rho.horizon:=
    (vote_time_le_confirmation_time S.E s).trans hconfHor
  have hadmit:= proposedBlock_admittedBeforeVote_of_openingGrade
    S adm hq hforms hPparent hprop hpost hvoteHor v hv
  have hBT: B ∈ pre.T:= by
    exact (admittedBefore_mem_and_stamp_at S adm.toScheduleWellFormed hadmit
      (vote_time_le_confirmation_time S.E s)).1
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node v) pre:=
    Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
      adm.toDeliveryWellFormed read v
  have hagree: DerivedStateAgrees S.E S.cfg pre:=
    derivedStateAgrees_depReachable S.E S.hc S.cfg (S.node v) pre hdep
  have hFJ: Block.Preceq pre.F pre.J:=
    finalizedPrecedesJustifiedInvariant S.E S.hc S.cfg (S.node v) pre
      (Proofs.Bridges.reachableStore_of_depReachableStore
        S.E S.hc S.cfg (S.node v) hdep)
  have hrootP:= confRoot_preceq_protected_of_gradeFormsAt
    S hforms hv
  have hPB: Block.Preceq P B:=
    Block.preceq_trans hPparent
      (Protocol.preceq_of_parent?
        (Protocol.proposedBlock_parent S rho s))
  have hrootB: Block.Preceq
      (Protocol.get_fg_root pre.toHealing.toFG) B:= by
    exact Block.preceq_trans
      (by simpa only [confRoot, st, Proofs.Optimistic.confStore,
          Proofs.Optimistic.tickStore, pre] using hrootP)
      hPB
  have hFB: Block.Preceq pre.F B:=
    Block.preceq_trans
      (Proofs.Records.preceq_get_fg_root_of_F (st:= pre.toHealing.toFG) hFJ)
      hrootB
  have hheight: pre.h_max - 1 ≤ (pre.σ B).h:= by
    rw [hagree B hBT]
    simpa only [RecoveryProposalConfirmationHeightCap, st,
      Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore, pre, read, s, B] using hcap
  have hV: B ∈ Protocol.V_tree pre.toHealing.toFG:= by
    simp only [Protocol.V_tree, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq, Protocol.Store.toHealing]
    exact ⟨⟨hBT, hFB⟩, B, hBT, Block.preceq_self B, hheight⟩
  have hfiltered:= Proofs.Records.mem_filtered_of_mem_V_tree hV hrootB
  simpa only [confTree, st, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
    pre, read] using hfiltered

/-! ## The exact opening-anchor seam -/

/-- The suffix-local fact that would make the opening confirmation anchor a
proposal-time fresh-anchor candidate.

This is deliberately a reflection statement, not an assumption about all
past selections. It says only that the fresh anchor selected at the opening
confirmation read was already active and grade 1 in the opening proposer's
earlier read. The common G2 and proposal-height window do not imply this
field: grade 1 is reader-local, and a vote received before `Gamma[0]` at one
reader need only reach another reader by `Gamma[1]`. -/
def RecoveryOpeningFreshAnchorReflection
    (S: Setup V) (rho: Run V) (q: Round) (v: V): Prop:=
  let s:= S.hc.opening_slot q
  let conf:= Proofs.Optimistic.confStore S rho v s
  let proposal:= Protocol.proposerDutyStore S rho s
  ∀ A: Block V,
    Protocol.fresh_anchor S.E S.hc conf.toHealing q = some A →
      A ∈ Protocol.get_filtered_block_tree proposal.toHealing.toFG ∧
        Protocol.G1 S.E proposal.toHealing.gradeView S.hc q A = true

/-- At the opening confirmation read, a common active G2 forces the integrated
SG root to use the fresh-anchor branch and places the protected block below
that anchor. -/
theorem protected_preceq_confAnchor_of_gradeFormsAt
    (S: Setup V) {rho: Run V} {q: Round} {P: Block V}
    (hforms: GradeFormsAt S rho q P) {v: V} (hv: v ∈ rho.honest):
    Block.Preceq P
      (confAnchor S.E S.hc
        (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q))):= by
  let s:= S.hc.opening_slot q
  let st:= Proofs.Optimistic.confStore S rho v s
  have hPmem: P ∈ Protocol.get_filtered_block_tree st.toHealing.toFG:= by
    simpa only [st, s, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
      opening_confirmation_time_eq_action, healStoreAt] using (hforms v hv).1
  have hPG2: Protocol.G2 S.E st.toHealing.gradeView S.hc q P = true:= by
    simpa only [st, s, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
      opening_confirmation_time_eq_action, gradeViewAt, healStoreAt,
      Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using (hforms v hv).2
  have hsome:
      (Protocol.grade2_block S.E S.hc st.toHealing q).isSome = true:= by
    refine deepest?_isSome_of_compatible ?_
      ⟨P, Finset.mem_filter.mpr ⟨hPmem, hPG2⟩⟩
    intro X hX Y hY
    exact G2_compatible S.E (Finset.mem_filter.mp hX).2
      (Finset.mem_filter.mp hY).2
  obtain ⟨Q, hQ⟩:= Option.isSome_iff_exists.mp hsome
  obtain ⟨A, hA⟩:= Option.isSome_iff_exists.mp
    (fresh_anchor_isSome_of_grade2 S.E hQ)
  have hPQ: Block.Preceq P Q:= by
    refine deepest?_dominates hQ
      (Finset.mem_filter.mpr ⟨hPmem, hPG2⟩) ?_
    exact G2_compatible S.E hPG2
      (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hQ)).2
  have hQA: Block.Preceq Q A:=
    grade2_preceq_fresh_anchor S.E hQ hA
  have hround: S.hc.round_of st.s = q:= by
    simp only [st, s, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
      opening_confirmation_time_eq_action]
    exact Proofs.HealingLemmas.round_of_slotOf_a S q
  have hanchor: confAnchor S.E S.hc st = A:= by
    simp only [confAnchor, hround, Protocol.get_sg_root, hA]
  rw [hanchor]
  exact Block.preceq_trans hPQ hQA

/-- Fresh-anchor reflection is exactly enough to put the later opening
confirmation anchor below the honest opening proposal. The proposer selects
the deepest reflected grade-1 candidate and the final Section 7 head descends
from that selected SG root. -/
theorem confAnchor_preceq_proposedBlock_of_gradeFormsAt_and_freshReflection
    (S: Setup V) {rho: Run V} {q: Round} {P: Block V}
    (hforms: GradeFormsAt S rho q P)
    {v: V} (hv: v ∈ rho.honest)
    (hreflect: RecoveryOpeningFreshAnchorReflection S rho q v):
    Block.Preceq
      (confAnchor S.E S.hc
        (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q)))
      (Internal.proposedBlock S rho (S.hc.opening_slot q)):= by
  let s:= S.hc.opening_slot q
  let conf:= Proofs.Optimistic.confStore S rho v s
  let proposal:= Protocol.proposerDutyStore S rho s
  have hPmem: P ∈ Protocol.get_filtered_block_tree conf.toHealing.toFG:= by
    simpa only [conf, s, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
      opening_confirmation_time_eq_action, healStoreAt] using (hforms v hv).1
  have hPG2: Protocol.G2 S.E conf.toHealing.gradeView S.hc q P = true:= by
    simpa only [conf, s, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
      opening_confirmation_time_eq_action, gradeViewAt, healStoreAt,
      Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using (hforms v hv).2
  have hsome:
      (Protocol.grade2_block S.E S.hc conf.toHealing q).isSome = true:= by
    refine deepest?_isSome_of_compatible ?_
      ⟨P, Finset.mem_filter.mpr ⟨hPmem, hPG2⟩⟩
    intro X hX Y hY
    exact G2_compatible S.E (Finset.mem_filter.mp hX).2
      (Finset.mem_filter.mp hY).2
  obtain ⟨Q, hQ⟩:= Option.isSome_iff_exists.mp hsome
  obtain ⟨A, hA⟩:= Option.isSome_iff_exists.mp
    (fresh_anchor_isSome_of_grade2 S.E hQ)
  obtain ⟨hAactive, hAG1⟩:= hreflect A (by simpa only [conf] using hA)
  have hproposalSome:
      (Protocol.fresh_anchor S.E S.hc proposal.toHealing q).isSome = true:= by
    refine deepest?_isSome_of_compatible ?_
      ⟨A, Finset.mem_filter.mpr ⟨hAactive, hAG1⟩⟩
    intro X hX Y hY
    exact G1_compatible S.E (Finset.mem_filter.mp hX).2
      (Finset.mem_filter.mp hY).2
  obtain ⟨A0, hA0⟩:= Option.isSome_iff_exists.mp hproposalSome
  have hAA0: Block.Preceq A A0:= by
    refine deepest?_dominates hA0
      (Finset.mem_filter.mpr ⟨hAactive, hAG1⟩) ?_
    exact G1_compatible S.E hAG1
      (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hA0)).2
  have hconfRound: S.hc.round_of conf.s = q:= by
    simp only [conf, s, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
      opening_confirmation_time_eq_action]
    exact Proofs.HealingLemmas.round_of_slotOf_a S q
  have hconfAnchor: confAnchor S.E S.hc conf = A:= by
    simp only [confAnchor, hconfRound, Protocol.get_sg_root, hA]
  have hproposalRound: S.hc.round_of proposal.s = q:= by
    simp only [proposal, s, Protocol.proposerDutyStore,
      Proofs.Optimistic.tickStore, Proofs.Optimistic.slotOf_proposal_time]
    exact round_of_opening_slot_eq S.hc q
  have hrootHead:= StoreFinality.get_sg_root_preceq_get_head
    S.E S.hc proposal
      (Protocol.proposer_view proposal.toHealing.toFG.toSG.toGoldfishStore proposal.s).toFinset
      (Protocol.proposer_support_view proposal.toHealing.toFG.toSG.toGoldfishStore proposal.s).toFinset
      (proposal.s - 1)
  have hA0parent: Block.Preceq A0 (Protocol.proposedParent S rho s):= by
    simpa only [Protocol.proposedParent, proposal, hproposalRound,
      Protocol.get_sg_root, hA0] using hrootHead
  have hparentBlock: Block.Preceq
      (Protocol.proposedParent S rho s)
      (Internal.proposedBlock S rho s):=
    Protocol.proposedParent_preceq_proposedBlock S rho s
  simpa only [conf, s, hconfAnchor] using
    Block.preceq_trans hAA0 (Block.preceq_trans hA0parent hparentBlock)

/-! ## The reflection-free compatible confirmation -/

/-- The opening update is always on the protected block's chain. A genuine
walk result is above the fresh anchor and therefore above `P`; an unsuccessful
confirmation writes the FG root, which is below `P`.

This statement needs no proposal confirmation and no fresh-anchor reflection.
-/
theorem openingUpdateConfirmation_ordered_with_protected_of_gradeFormsAt
    (S: Setup V) {rho: Run V} {q: Round} {P: Block V}
    (hforms: GradeFormsAt S rho q P) {v: V} (hv: v ∈ rho.honest):
    let s:= S.hc.opening_slot q
    let st:= Proofs.Optimistic.confStore S rho v s
    Block.Preceq (Protocol.update_confirmation S.E S.hc st s).live_confirmed P ∨
      Block.Preceq P
        (Protocol.update_confirmation S.E S.hc st s).live_confirmed:= by
  let s:= S.hc.opening_slot q
  let st:= Proofs.Optimistic.confStore S rho v s
  have hroot: Block.Preceq (confRoot st) P:= by
    simpa only [st, s] using
      confRoot_preceq_protected_of_gradeFormsAt S hforms hv
  have hanchor: Block.Preceq P (confAnchor S.E S.hc st):= by
    simpa only [st, s] using
      protected_preceq_confAnchor_of_gradeFormsAt S hforms hv
  rcases live_confirmed_eq_walk_or_root S.E S.hc st s with hwalk | hrootEq
  · right
    rw [hwalk]
    exact Block.preceq_trans hanchor (Protocol.ghost_preceq _ _ _ _)
  · left
    rwa [hrootEq]

/-- In particular, every honest opening update is compatible with the common
protected block. -/
theorem openingUpdateConfirmation_compatible_protected_of_gradeFormsAt
    (S: Setup V) {rho: Run V} {q: Round} {P: Block V}
    (hforms: GradeFormsAt S rho q P) {v: V} (hv: v ∈ rho.honest):
    let s:= S.hc.opening_slot q
    let st:= Proofs.Optimistic.confStore S rho v s
    Block.compatible P
      (Protocol.update_confirmation S.E S.hc st s).live_confirmed = true:= by
  have horder:= openingUpdateConfirmation_ordered_with_protected_of_gradeFormsAt
    S hforms hv
  simpa only [Block.compatible, Bool.or_eq_true, or_comm] using horder

/-- Two honest opening updates are compatible after GST. If both guards pass,
the normal same-slot cross-view theorem applies. In every other branch at
least one output is an FG-root fallback below `P`, while any genuine walk is
above `P`. -/
theorem openingUpdateConfirmations_pairwiseCompatible_of_gradeFormsAt_after_gst
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {q: Round} {P: Block V}
    (hforms: GradeFormsAt S rho q P)
    (hpost: S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hhor: Protocol.confirmation_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    {v w: V} (hv: v ∈ rho.honest) (hw: w ∈ rho.honest):
    let s:= S.hc.opening_slot q
    let stv:= Proofs.Optimistic.confStore S rho v s
    let stw:= Proofs.Optimistic.confStore S rho w s
    Block.compatible
      (Protocol.update_confirmation S.E S.hc stv s).live_confirmed
      (Protocol.update_confirmation S.E S.hc stw s).live_confirmed = true:= by
  let s:= S.hc.opening_slot q
  let stv:= Proofs.Optimistic.confStore S rho v s
  let stw:= Proofs.Optimistic.confStore S rho w s
  have hrootV: Block.Preceq (confRoot stv) P:= by
    simpa only [stv, s] using
      confRoot_preceq_protected_of_gradeFormsAt S hforms hv
  have hrootW: Block.Preceq (confRoot stw) P:= by
    simpa only [stw, s] using
      confRoot_preceq_protected_of_gradeFormsAt S hforms hw
  have hanchorV: Block.Preceq P (confAnchor S.E S.hc stv):= by
    simpa only [stv, s] using
      protected_preceq_confAnchor_of_gradeFormsAt S hforms hv
  have hanchorW: Block.Preceq P (confAnchor S.E S.hc stw):= by
    simpa only [stw, s] using
      protected_preceq_confAnchor_of_gradeFormsAt S hforms hw
  have hwalkV: Block.Preceq P (confWalk S.E S.hc stv s):=
    Block.preceq_trans hanchorV (Protocol.ghost_preceq _ _ _ _)
  have hwalkW: Block.Preceq P (confWalk S.E S.hc stw s):=
    Block.preceq_trans hanchorW (Protocol.ghost_preceq _ _ _ _)
  change Block.compatible
    (Protocol.update_confirmation S.E S.hc stv s).live_confirmed
    (Protocol.update_confirmation S.E S.hc stw s).live_confirmed = true
  by_cases hgv: confEligible S.E stv s (confWalk S.E S.hc stv s) = true
  · by_cases hgw: confEligible S.E stw s (confWalk S.E S.hc stw s) = true
    · obtain ⟨hvw, hwv⟩:= crossViews_confStore_after_gst
        S adm hv hw (by simpa only [s] using hpost)
          (by simpa only [s] using hhor)
      exact live_confirmed_compatible S.E S.hc stv stw s
        (by simpa only [stv, stw, s] using hvw)
        (by simpa only [stv, stw, s] using hwv) hgv hgw
    · rw [update_confirmation_live_confirmed,
        update_confirmation_live_confirmed, if_pos hgv, if_neg hgw]
      exact Block.compatible_of_preceq_common
        (Block.preceq_self (confWalk S.E S.hc stv s))
        (Block.preceq_trans hrootW hwalkV)
  · by_cases hgw: confEligible S.E stw s (confWalk S.E S.hc stw s) = true
    · rw [update_confirmation_live_confirmed,
        update_confirmation_live_confirmed, if_neg hgv, if_pos hgw]
      exact Block.compatible_of_preceq_common
        (Block.preceq_trans hrootV hwalkW)
        (Block.preceq_self (confWalk S.E S.hc stw s))
    · rw [update_confirmation_live_confirmed,
        update_confirmation_live_confirmed, if_neg hgv, if_neg hgw]
      exact Block.compatible_of_preceq_common hrootV hrootW

/-- The action store is exactly the update produced by the opening slot's
confirmation read. -/
theorem actionStoreAt_eq_openingUpdate
    (S: Setup V) (rho: Run V) (v: V) (q: Round):
    actionStoreAt S rho v q =
      Protocol.update_confirmation S.E S.hc
        (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q))
        (S.hc.opening_slot q):= by
  rw [actionStoreAt_eq_update_confirmation]
  have hslot: S.E.slotOf (S.a q) - 1 = S.hc.opening_slot q:= by
    have hsc: S.a q =
        Protocol.support_cutoff S.E (S.hc.opening_slot q + 1):=
      Protocol.a_eq_support_cutoff_succ S.hc S.E q
    rw [hsc, Proofs.Optimistic.slotOf_support_cutoff]
    exact Nat.add_sub_cancel (S.hc.opening_slot q) 1
  rw [hslot]
  simp only [Proofs.Optimistic.confStore, opening_confirmation_time_eq_action,
    Run.storeBeforeTime]

/-- Reflection-free compatibility at the exact store read by the SG and FG
round action. -/
theorem actionLiveConfirmed_compatible_protected_of_gradeFormsAt
    (S: Setup V) {rho: Run V} {q: Round} {P: Block V}
    (hforms: GradeFormsAt S rho q P) {v: V} (hv: v ∈ rho.honest):
    Block.compatible P (actionStoreAt S rho v q).live_confirmed = true:= by
  rw [actionStoreAt_eq_openingUpdate]
  exact openingUpdateConfirmation_compatible_protected_of_gradeFormsAt
    S hforms hv

/-- Reflection-free pairwise compatibility at the exact action stores. -/
theorem actionLiveConfirmed_pairwiseCompatible_of_gradeFormsAt_after_gst
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {q: Round} {P: Block V}
    (hforms: GradeFormsAt S rho q P)
    (hpost: S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hhor: Protocol.confirmation_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    {v w: V} (hv: v ∈ rho.honest) (hw: w ∈ rho.honest):
    Block.compatible (actionStoreAt S rho v q).live_confirmed
      (actionStoreAt S rho w q).live_confirmed = true:= by
  rw [actionStoreAt_eq_openingUpdate, actionStoreAt_eq_openingUpdate]
  exact
    openingUpdateConfirmations_pairwiseCompatible_of_gradeFormsAt_after_gst
      S adm hforms hpost hhor hv hw

/-- The protected block and all honest opening outputs form one finite chain,
so they have a common deepest endpoint. The endpoint is either `P` itself or
one actual honest action-store confirmation. -/
theorem exists_openingConfirmationFrontier_of_gradeFormsAt_after_gst
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {q: Round} {P: Block V}
    (hforms: GradeFormsAt S rho q P)
    (hpost: S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hhor: Protocol.confirmation_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon):
    ∃ C: Block V,
      Block.Preceq P C ∧
        (∀ v ∈ rho.honest,
          Block.Preceq (actionStoreAt S rho v q).live_confirmed C) ∧
        (C = P ∨ ∃ v ∈ rho.honest,
          C = (actionStoreAt S rho v q).live_confirmed):= by
  let output: V → Block V:= fun v =>
    (actionStoreAt S rho v q).live_confirmed
  let candidates: Finset (Block V):= insert P (rho.honest.image output)
  have hcompatible: ∀ X ∈ candidates, ∀ Y ∈ candidates,
      Block.compatible X Y = true:= by
    intro X hX Y hY
    rcases Finset.mem_insert.mp hX with hXP | hXout
    · subst X
      rcases Finset.mem_insert.mp hY with hYP | hYout
      · subst Y
        exact Block.compatible_of_preceq_common
          (Block.preceq_self P) (Block.preceq_self P)
      · obtain ⟨w, hw, hwY⟩:= Finset.mem_image.mp hYout
        subst Y
        simpa only [output] using
          actionLiveConfirmed_compatible_protected_of_gradeFormsAt
            S hforms hw
    · obtain ⟨v, hv, hvX⟩:= Finset.mem_image.mp hXout
      subst X
      rcases Finset.mem_insert.mp hY with hYP | hYout
      · subst Y
        have hcompat:=
          actionLiveConfirmed_compatible_protected_of_gradeFormsAt
            S hforms hv
        exact Protocol.compatible_comm (by simpa only [output] using hcompat)
      · obtain ⟨w, hw, hwY⟩:= Finset.mem_image.mp hYout
        subst Y
        simpa only [output] using
          actionLiveConfirmed_pairwiseCompatible_of_gradeFormsAt_after_gst
            S adm hforms hpost hhor hv hw
  have hsome: (Block.deepest? candidates).isSome = true:= by
    refine deepest?_isSome_of_compatible hcompatible ?_
    exact ⟨P, Finset.mem_insert_self P _⟩
  obtain ⟨C, hC⟩:= Option.isSome_iff_exists.mp hsome
  have hCmem: C ∈ candidates:= Proofs.Engine.deepest?_mem hC
  have hPC: Block.Preceq P C:= by
    exact deepest?_dominates hC (Finset.mem_insert_self P _)
      (hcompatible P (Finset.mem_insert_self P _) C hCmem)
  refine ⟨C, hPC, ?_, ?_⟩
  · intro v hv
    have hout: output v ∈ candidates:= by
      apply Finset.mem_insert_of_mem
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
    simpa only [output] using
      deepest?_dominates hC hout (hcompatible (output v) hout C hCmem)
  · rcases Finset.mem_insert.mp hCmem with hCP | hCout
    · exact Or.inl hCP
    · obtain ⟨v, hv, hvC⟩:= Finset.mem_image.mp hCout
      exact Or.inr ⟨v, hv, by simpa only [output] using hvC.symm⟩

/-- The strongest common opening-confirmation statement that does not require
fresh-anchor reflection or exact proposal confirmation. -/
structure RecoveryOpeningCompatibleConfirmationsAt
    (S: Setup V) (rho: Run V) (q: Round) (P: Block V): Prop where
  orderedWithProtected: ∀ v ∈ rho.honest,
    Block.Preceq (actionStoreAt S rho v q).live_confirmed P ∨
      Block.Preceq P (actionStoreAt S rho v q).live_confirmed
  pairwise: ∀ v ∈ rho.honest, ∀ w ∈ rho.honest,
    Block.compatible (actionStoreAt S rho v q).live_confirmed
      (actionStoreAt S rho w q).live_confirmed = true
  frontier: ∃ C: Block V,
    Block.Preceq P C ∧
      ∀ v ∈ rho.honest,
        Block.Preceq (actionStoreAt S rho v q).live_confirmed C

/-- A common active G2 and the ordinary post-GST confirmation cross view
produce the complete compatible-confirmation surface at the opening action.
-/
theorem recoveryOpeningCompatibleConfirmationsAt_of_gradeFormsAt_after_gst
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {q: Round} {P: Block V}
    (hforms: GradeFormsAt S rho q P)
    (hpost: S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hhor: Protocol.confirmation_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon):
    RecoveryOpeningCompatibleConfirmationsAt S rho q P where
  orderedWithProtected:= by
    intro v hv
    rw [actionStoreAt_eq_openingUpdate]
    exact openingUpdateConfirmation_ordered_with_protected_of_gradeFormsAt
      S hforms hv
  pairwise:= by
    intro v hv w hw
    exact actionLiveConfirmed_pairwiseCompatible_of_gradeFormsAt_after_gst
      S adm hforms hpost hhor hv hw
  frontier:= by
    obtain ⟨C, hPC, hall, -⟩:=
      exists_openingConfirmationFrontier_of_gradeFormsAt_after_gst
        S adm hforms hpost hhor
    exact ⟨C, hPC, hall⟩

/-! ## Packaging the local read -/

/-- Persistent grades and the exact local height cap derive the root and
candidate fields of `RecoveryProposalConfirmationRead`. The only residual is
the SG-anchor order at this exact reader. -/
theorem recoveryProposalConfirmationRead_of_gradeFormsAt_and_heightCap
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {q: Round} (hq: 0 < q) {P: Block V}
    (hforms: GradeFormsAt S rho q P)
    (hPparent: Block.Preceq P
      (Internal.proposedBlock S rho
        (S.hc.opening_slot q)).parent)
    (hprop: S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hpost: S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hconfHor: Protocol.confirmation_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    {v: V} (hv: v ∈ rho.honest)
    (hcap: RecoveryProposalConfirmationHeightCap S rho q v)
    (hanchor: Block.Preceq
      (confAnchor S.E S.hc
        (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q)))
      (Internal.proposedBlock S rho (S.hc.opening_slot q))):
    RecoveryProposalConfirmationRead S rho (S.hc.opening_slot q) v
      (Internal.proposedBlock S rho (S.hc.opening_slot q)):= by
  have hrootP:= confRoot_preceq_protected_of_gradeFormsAt
    S hforms hv
  have hPB: Block.Preceq P
      (Internal.proposedBlock S rho (S.hc.opening_slot q)):=
    Block.preceq_trans hPparent
      (Protocol.preceq_of_parent?
        (Protocol.proposedBlock_parent S rho (S.hc.opening_slot q)))
  exact
    { root:= Block.preceq_trans hrootP hPB
      anchor:= hanchor
      candidate:=
        proposedBlock_candidateAtOpeningConfirmation_of_gradeFormsAt_and_heightCap
          S adm hq hforms hPparent hprop hpost hconfHor hv hcap }

/-- The complete local confirmation-read producer with the exact
fresh-anchor reflection seam exposed. -/
theorem recoveryProposalConfirmationRead_of_gradeFormsAt_heightCap_and_freshReflection
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {q: Round} (hq: 0 < q) {P: Block V}
    (hforms: GradeFormsAt S rho q P)
    (hPparent: Block.Preceq P
      (Internal.proposedBlock S rho
        (S.hc.opening_slot q)).parent)
    (hprop: S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hpost: S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hconfHor: Protocol.confirmation_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    {v: V} (hv: v ∈ rho.honest)
    (hcap: RecoveryProposalConfirmationHeightCap S rho q v)
    (hreflect: RecoveryOpeningFreshAnchorReflection S rho q v):
    RecoveryProposalConfirmationRead S rho (S.hc.opening_slot q) v
      (Internal.proposedBlock S rho (S.hc.opening_slot q)):= by
  apply recoveryProposalConfirmationRead_of_gradeFormsAt_and_heightCap
    S adm hq hforms hPparent hprop hpost hconfHor hv hcap
  exact confAnchor_preceq_proposedBlock_of_gradeFormsAt_and_freshReflection
    S hforms hv hreflect

/-- All honest opening confirmation reads follow from pointwise height caps
and pointwise fresh-anchor reflection. This is the exact input expected by
`openingProposal_liveConfirmed_actionStore_after_gst_of_localReads`. -/
theorem honestRecoveryProposalConfirmationReads_of_gradeFormsAt_heightCaps_and_freshReflection
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {q: Round} (hq: 0 < q) {P: Block V}
    (hforms: GradeFormsAt S rho q P)
    (hPparent: Block.Preceq P
      (Internal.proposedBlock S rho
        (S.hc.opening_slot q)).parent)
    (hprop: S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hpost: S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hconfHor: Protocol.confirmation_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hcaps: ∀ v ∈ rho.honest,
      RecoveryProposalConfirmationHeightCap S rho q v)
    (hreflect: ∀ v ∈ rho.honest,
      RecoveryOpeningFreshAnchorReflection S rho q v):
    ∀ v ∈ rho.honest,
      RecoveryProposalConfirmationRead S rho (S.hc.opening_slot q) v
        (Internal.proposedBlock S rho (S.hc.opening_slot q)):= by
  intro v hv
  exact
    recoveryProposalConfirmationRead_of_gradeFormsAt_heightCap_and_freshReflection
      S adm hq hforms hPparent hprop hpost hconfHor hv
        (hcaps v hv) (hreflect v hv)

 -/

/-! ## Named read-local proof -/



/-! ## Prepared confirmation-anchor floor -/



/- The named prepared confirmation-anchor floor is available above. The previous
absolute-grade declaration remains absent because its erased-store statement
has no named twin in this frozen proof cone. -/

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
