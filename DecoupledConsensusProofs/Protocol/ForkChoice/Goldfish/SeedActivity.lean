module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.SeedSelectiveG1Flush
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryFreshGradeProvenance
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FinalityFilterQuietAncestor
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionConfirmationCore
public import DecoupledConsensusProofs.Execution.FrontierWitnessRelay
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightProgressSeedRegime
public import DecoupledConsensusProofs.Protocol.Schedule.ProposalCanonicality
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsProducers
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryGenuineClearNextVote
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge

@[expose] public section

/-!
# Seed activity from quiet preceding action carriers

This module isolates the sound part of the proposed one-round activity flush.
An honest grade-1 or selected grade-2 block is below an honest preceding action
carrier. Thus, pointwise finality-filter quietness of those carriers at the
current action read projects to both settled predicates.

The local action carrier is proved active below. The remaining gate-off join
is its viability witness's admissible relay to the next strict action read.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every prior honest action carrier is noninterfering at every current honest
action read. This is the exact missing activity bridge for the gate-off seed. -/
def PreviousActionCarriersQuietAt
    (S : Setup V) (rho : Run V) (r : Round) : Prop :=
  ∀ u ∈ rho.honest, ∀ w ∈ rho.honest,
    FinalityFilterNoninterferenceAtRead S rho w (S.a r)
      (actionSGBlockAt S rho u (r - 1))

private theorem frame_anchor_mem_filtered_of_fgRoot_mem_filtered
    (cache : DecoupledConsensusModel.Protocol.Cache V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round)
    (hroot : Protocol.get_fg_root st.toFG ∈
      Protocol.get_filtered_block_tree st.toFG) :
    (Protocol.get_sg_root_with (DecoupledConsensusModel.Protocol.frameContract cache)
      E hc st r) ∈ Protocol.get_filtered_block_tree st.toFG := by
  change DecoupledConsensusModel.Protocol.anchor E hc st r
    (DecoupledConsensusModel.Protocol.readFrame cache st r).g1 ∈
      Protocol.get_filtered_block_tree st.toFG
  cases hframe : (DecoupledConsensusModel.Protocol.readFrame cache st r).g1 with
  | none => exact hroot
  | some opt =>
      cases opt with
      | none => exact hroot
      | some root =>
          cases hactive : DecoupledConsensusModel.Protocol.activePrefix
              (Protocol.get_filtered_block_tree st.toFG) root with
          | none => simpa only [DecoupledConsensusModel.Protocol.anchor, hactive,
              Option.getD_none] using hroot
          | some A =>
              simpa only [DecoupledConsensusModel.Protocol.anchor, hactive,
                Option.getD_some] using
                (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).1

omit [Fintype V] in
private theorem currentSGVote_mem_filtered
    (st : Protocol.Store V) (grades : Protocol.GradeRead V)
    (hpc : ParentClosed st) (hFJ : Block.Preceq st.F st.J)
    (hlive : st.live_confirmed ∈ Protocol.get_filtered_block_tree st.toHealing.toFG)
    (hroot : Protocol.get_fg_root st.toHealing.toFG ∈
      Protocol.get_filtered_block_tree st.toHealing.toFG)
    (hanchor : grades.anchor ∈ Protocol.get_filtered_block_tree st.toHealing.toFG)
    (hrootAnchor : Block.Preceq
      (Protocol.get_fg_root st.toHealing.toFG) grades.anchor)
    (hQ2 : ∀ Q, grades.Q2 = some Q →
      Q ∈ Protocol.get_filtered_block_tree st.toHealing.toFG) :
    Protocol.currentSGVote st.toHealing grades ∈
      Protocol.get_filtered_block_tree st.toHealing.toFG := by
  classical
  unfold Protocol.currentSGVote
  split
  · rename_i B hclear
    have hmem := Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hclear)
    have hBpre : Block.Preceq B st.live_confirmed :=
      Proofs.Engine.deepest_clear_preceq hclear
    have hBT : B ∈ st.T :=
      Proofs.Records.mem_of_preceq ((parentClosed_iff st).mp hpc).2 B st.live_confirmed
        (Proofs.Records.get_filtered_block_tree_subset st.toHealing.toFG hlive) hBpre
    have hrootB : Block.Preceq (Protocol.get_fg_root st.toHealing.toFG) B :=
      Block.preceq_trans hrootAnchor (by
        simpa only [Option.elim_some] using hmem.2.1)
    exact Proofs.Records.mem_filtered_of_preceq hFJ hlive hBT hBpre hrootB
  · split
    · rename_i Q hQ
      exact hQ2 Q hQ
    · split
      · exact hroot
      · exact hanchor

private theorem actionLiveConfirmed_mem_filtered
    (S : Setup V) (rho : Run V) (v : V) (r : Round)
    (hrootConf : Protocol.get_fg_root
        (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r)).toHealing.toFG ∈
      Protocol.get_filtered_block_tree
        (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r)).toHealing.toFG) :
    (actionStoreAt S rho v r).st.core.live_confirmed ∈
      Protocol.get_filtered_block_tree
        (actionStoreAt S rho v r).toHealing.toFG := by
  let cst := Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r)
  let confCache :=
    (NamedActionReads.confirmationReadAt S rho v (S.a r)).cache
  let gc := NamedProfile.gradeContract confCache
  have hanchorConf : Protocol.get_sg_root_with gc S.E S.hc cst.toHealing
      (S.hc.round_of cst.s) ∈
      Protocol.get_filtered_block_tree cst.toHealing.toFG := by
    exact frame_anchor_mem_filtered_of_fgRoot_mem_filtered confCache S.E S.hc
      cst.toHealing (S.hc.round_of cst.s) hrootConf
  have hliveUpdate :
      (Protocol.update_confirmation_with gc S.E S.hc cst
        (S.hc.opening_slot r)).live_confirmed ∈
        Protocol.get_filtered_block_tree cst.toHealing.toFG := by
    rw [Protocol.update_confirmation_with_live_confirmed]
    split
    · simpa only [Protocol.confWalkWith, Protocol.confAnchorWith,
        Protocol.confTree] using
        (Proofs.Records.ghost_mem_of _ _ hanchorConf (Finset.Subset.refl _))
    · simpa only [Protocol.confRoot] using hrootConf
  have hactionEq : (actionStoreAt S rho v r).st.core =
      Protocol.update_confirmation_with gc S.E S.hc cst
        (S.hc.opening_slot r) := by
    change (actionStoreAt S rho v r).st.core =
      Protocol.update_confirmation_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadAt S rho v (S.a r)).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r))
        (S.hc.opening_slot r)
    exact actionStoreAt_eq_update_confirmation_confStore S rho v r
  rw [hactionEq]
  change (Protocol.update_confirmation_with gc S.E S.hc cst
    (S.hc.opening_slot r)).live_confirmed ∈
      Protocol.get_filtered_block_tree cst.toHealing.toFG
  exact hliveUpdate

private theorem actionSGBlockAt_mem_filtered_actionStore_core
    (S : Setup V) {rho : Run V} (v : V) (r : Round) :
    actionSGBlockAt S rho v r ∈
      Protocol.get_filtered_block_tree
        (actionStoreAt S rho v r).toHealing.toFG := by
  classical
  let pre := rho.storeBeforeTime S v (S.a r)
  let ast := actionStoreAt S rho v r
  have hrootPre : Protocol.get_fg_root pre.core.toHealing.toFG ∈
      Protocol.get_filtered_block_tree pre.toHealing.toFG :=
    named_fgRoot_mem_filtered_stateBeforeTime S rho (S.a r) v
  have hrootAction : Protocol.get_fg_root ast.toHealing.toFG ∈
      Protocol.get_filtered_block_tree ast.toHealing.toFG := by
    rw [actionStoreAt_filteredTree S rho v r,
      actionStoreAt_fgRoot_eq_storeBeforeTime S rho v r]
    exact hrootPre
  have hrootConf : Protocol.get_fg_root
        (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r)).toHealing.toFG ∈
      Protocol.get_filtered_block_tree
        (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r)).toHealing.toFG := by
    rw [← actionStoreAt_filteredTree_eq_openingConfStore S rho v r,
      ← actionStoreAt_fgRoot_eq_openingConfStore S rho v r]
    exact hrootAction
  have hlive := actionLiveConfirmed_mem_filtered S rho v r hrootConf
  have hpcPre : ParentClosed pre.core :=
    Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho (S.a r) v
  have hpc : ParentClosed ast.st.core := by
    have hT : ast.st.core.T = pre.core.T := rfl
    simpa only [hT] using hpcPre
  have hFJPre : Block.Preceq pre.core.F pre.core.J :=
    Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
      (S.a r) v
  have hFJ : Block.Preceq ast.st.core.F ast.st.core.J := by
    have hF : ast.st.core.F = pre.core.F := rfl
    have hJ : ast.st.core.J = pre.core.J := rfl
    rw [hF, hJ]
    exact hFJPre
  set n := actionReadAt S rho v r with hn
  set st := n.st.core.toHealing with hst
  set grades := DecoupledConsensusModel.Protocol.frameGradeRead n.cache S.E S.hc st r with hgrades
  have hk : S.hc.round_of st.s = r :=
    Proofs.HealingLemmas.round_of_slotOf_a S r
  have heq : actionSGBlockAt S rho v r = Protocol.currentSGVote st grades := by
    show Protocol.get_sg_vote_with (NamedProfile.gradeContract n.cache) S.E S.hc st
        (S.hc.round_of st.s)
        (Protocol.grade2_block_with (NamedProfile.gradeContract n.cache) S.E S.hc st
          (S.hc.round_of st.s)) = Protocol.currentSGVote st grades
    rw [hk]
    rfl
  have hrootAnchor : Block.Preceq (Protocol.get_fg_root st.toFG)
      grades.anchor := by
    change Block.Preceq (Protocol.get_fg_root st.toFG)
      (Protocol.get_sg_root_with (DecoupledConsensusModel.Protocol.frameContract n.cache)
        S.E S.hc st r)
    exact fg_root_preceq_get_sg_root_with_frame n.cache S.E S.hc st r
  have hanchor : grades.anchor ∈ Protocol.get_filtered_block_tree st.toFG := by
    change Protocol.get_sg_root_with (DecoupledConsensusModel.Protocol.frameContract n.cache)
      S.E S.hc st r ∈ Protocol.get_filtered_block_tree st.toFG
    exact frame_anchor_mem_filtered_of_fgRoot_mem_filtered n.cache
      S.E S.hc st r hrootAction
  have hQ2 : ∀ Q, grades.Q2 = some Q →
      Q ∈ Protocol.get_filtered_block_tree st.toFG := by
    intro Q hQ
    exact actionQ2_mem_filteredTree S rho v r hQ
  change actionSGBlockAt S rho v r ∈
      Protocol.get_filtered_block_tree ast.toHealing.toFG
  rw [heq]
  exact currentSGVote_mem_filtered n.st.core grades hpc hFJ hlive hrootAction hanchor
    hrootAnchor hQ2

/-- Every exact honest action SG carrier is in the filtered tree read by that
action. The confirmation value is itself filtered: its genuine branch is a
walk over that tree and its fallback is the FG root. -/
theorem actionSGBlockAt_mem_filtered_actionStore
    (S : Setup V) {rho : Run V} (_adm : Admissible S rho)
    (v : V) (r : Round) :
    actionSGBlockAt S rho v r ∈
      Protocol.get_filtered_block_tree
        (actionStoreAt S rho v r).toHealing.toFG := by
  exact actionSGBlockAt_mem_filtered_actionStore_core S v r

/-
  classical
  let pre:= rho.storeBeforeTime S v (S.a r)
  let ast:= actionStoreAt S rho v r
  let cst:= Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r)
  have hpcPre: ParentClosed pre.core:=
    Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho (S.a r) v
  have hFJPre: Block.Preceq pre.core.F pre.core.J:=
    Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
      (S.a r) v
  have hrootPre: Protocol.get_fg_root pre.core.toHealing.toFG ∈
      Protocol.get_filtered_block_tree pre.toHealing.toFG:=
    named_fgRoot_mem_filtered_stateBeforeTime S rho (S.a r) v
  have hrootAction: Protocol.get_fg_root ast.toHealing.toFG ∈
      Protocol.get_filtered_block_tree ast.toHealing.toFG:= by
    rw [actionStoreAt_filteredTree S rho v r,
      actionStoreAt_fgRoot_eq_storeBeforeTime S rho v r]
    exact hrootPre
  have hrootConf: Protocol.get_fg_root cst.toHealing.toFG ∈
      Protocol.get_filtered_block_tree cst.toHealing.toFG:= by
    rw [← actionStoreAt_filteredTree_eq_openingConfStore S rho v r,
      ← actionStoreAt_fgRoot_eq_openingConfStore S rho v r]
    exact hrootAction
  let confCache:=
    (NamedActionReads.confirmationReadAt S rho v (S.a r)).cache
  let gc:= NamedProfile.gradeContract confCache
  have hanchorConf: Protocol.get_sg_root_with gc S.E S.hc cst.toHealing
      (S.hc.round_of cst.s) ∈
      Protocol.get_filtered_block_tree cst.toHealing.toFG:= by
    exact frame_anchor_mem_filtered_of_fgRoot_mem_filtered confCache S.E S.hc
      cst.toHealing (S.hc.round_of cst.s) hrootConf
  have hliveUpdate:
      (Protocol.update_confirmation_with gc S.E S.hc cst
        (S.hc.opening_slot r)).live_confirmed ∈
        Protocol.get_filtered_block_tree cst.toHealing.toFG:= by
    rw [Protocol.update_confirmation_with_live_confirmed]
    split
    · simpa only [Protocol.confWalkWith, Protocol.confAnchorWith,
        Protocol.confTree] using
        (Proofs.Records.ghost_mem_of _ _ hanchorConf (Finset.Subset.refl _))
    · simpa only [Protocol.confRoot] using hrootConf
  have hactionEq: ast.st.core =
      Protocol.update_confirmation_with gc S.E S.hc cst
        (S.hc.opening_slot r):= by
    change (actionStoreAt S rho v r).st.core =
      Protocol.update_confirmation_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadAt S rho v (S.a r)).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r))
        (S.hc.opening_slot r)
    exact actionStoreAt_eq_update_confirmation_confStore S rho v r
  have hlive: ast.st.core.live_confirmed ∈
      Protocol.get_filtered_block_tree ast.toHealing.toFG:= by
    rw [hactionEq]
    change (Protocol.update_confirmation_with gc S.E S.hc cst
      (S.hc.opening_slot r)).live_confirmed ∈
        Protocol.get_filtered_block_tree
          (Protocol.update_confirmation_with gc S.E S.hc cst
            (S.hc.opening_slot r)).toHealing.toFG
    change (Protocol.update_confirmation_with gc S.E S.hc cst
      (S.hc.opening_slot r)).live_confirmed ∈
        Protocol.get_filtered_block_tree cst.toHealing.toFG
    exact hliveUpdate
  have hpc: ParentClosed ast.st.core:= by
    have hT: ast.st.core.T = pre.core.T:= rfl
    simpa only [hT] using hpcPre
  have hFJ: Block.Preceq ast.st.core.F ast.st.core.J:= by
    have hF: ast.st.core.F = pre.core.F:= rfl
    have hJ: ast.st.core.J = pre.core.J:= rfl
    rw [hF, hJ]
    exact hFJPre
  set n:= actionReadAt S rho v r with hn
  set st:= n.st.core.toHealing with hst
  set grades:= DecoupledConsensusModel.Protocol.frameGradeRead n.cache S.E S.hc st r with hgrades
  have hk: S.hc.round_of st.s = r:=
    Proofs.HealingLemmas.round_of_slotOf_a S r
  have heq: actionSGBlockAt S rho v r = Protocol.currentSGVote st grades:= by
    show Protocol.get_sg_vote_with (NamedProfile.gradeContract n.cache) S.E S.hc st
        (S.hc.round_of st.s)
        (Protocol.grade2_block_with (NamedProfile.gradeContract n.cache) S.E S.hc st
          (S.hc.round_of st.s)) = Protocol.currentSGVote st grades
    rw [hk]
    rfl
  have hrootAnchor: Block.Preceq (Protocol.get_fg_root st.toFG)
      grades.anchor:= by
    change Block.Preceq (Protocol.get_fg_root st.toFG)
      (Protocol.get_sg_root_with (DecoupledConsensusModel.Protocol.frameContract n.cache)
        S.E S.hc st r)
    exact fg_root_preceq_get_sg_root_with_frame n.cache S.E S.hc st r
  change actionSGBlockAt S rho v r ∈
      Protocol.get_filtered_block_tree ast.toHealing.toFG
  rw [heq]
  unfold Protocol.currentSGVote
  cases hdc: Protocol.deepest_clear (some grades.anchor) st.live_confirmed
      grades.clear with
  | some B =>
      have hBpre: Block.Preceq B st.live_confirmed:=
        Proofs.Engine.deepest_clear_preceq hdc
      have hBT: B ∈ ast.st.core.T:= by
        exact Proofs.Records.mem_of_preceq ((parentClosed_iff ast.st.core).mp hpc).2 B
          ast.st.core.live_confirmed
          (Proofs.Records.get_filtered_block_tree_subset ast.toHealing.toFG hlive) hBpre
      have hrootB: Block.Preceq (Protocol.get_fg_root ast.toHealing.toFG) B:=
        Block.preceq_trans hrootAnchor (by
          simpa only [grades, hgrades] using
            (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hdc)).2.1)
      exact Proofs.Records.mem_filtered_of_preceq hFJ hlive hBT hBpre hrootB
  | none =>
      cases hq: grades.Q2 with
      | some Q =>
          have hq': PhaseGrades.nodeQ2 S n r = some Q:= hq
          exact actionQ2_mem_filteredTree S rho v r hq'
      | none =>
          have hanchor: grades.anchor ∈
              Protocol.get_filtered_block_tree ast.toHealing.toFG:= by
            change (Protocol.get_sg_root_with
              (DecoupledConsensusModel.Protocol.frameContract n.cache) S.E S.hc st r) ∈
              Protocol.get_filtered_block_tree st.toFG
            exact frame_anchor_mem_filtered_of_fgRoot_mem_filtered n.cache
              S.E S.hc st r hrootAction
          by_cases hraw: grades.rawG2
          · simp only [hq, hraw]
            exact hrootAction
          · simp only [hq, hraw]
            exact hanchor

 -/

/-
/-- At a gate-off exact frontier read, a run block in the thin window already
descends from the selected FG root. Unlike filtered membership, this does not
require that the block has reached the reader yet. -/
theorem frontierRoot_preceq_of_gateOff
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hsb: SlashableBound S rho)
    {w: V} (hw: w ∈ rho.honest) {read: Time} {X: Block V} {M: Height}
    (hXrun: RunBlock S rho X)
    (hXh: M - 1 ≤ (derived_state S.E S.cfg X).h)
    (hfrontier: (rho.storeBeforeTime S w read).h_max = M)
    (hgateOff: (rho.storeBeforeTime S w read).h_j + 2 ≤ M):
    Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w read).toHealing.toFG) X:= by
  let st:= rho.storeBeforeTime S w read
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node w) st:= by
    simpa only [st, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed read w)
  have hfrontier': st.h_max = M:= by
    simpa only [st] using hfrontier
  have hgateOff': st.h_j + 2 ≤ M:= by
    simpa only [st] using hgateOff
  have hnoHigh: NoHighJustifications S.E S.cfg st:=
    FixedHeightRootCore.noHighJustifications_depReachable
      S.E S.hc S.cfg (S.node w) hdep
  obtain ⟨C, hC, hF⟩:=
    Proofs.Bridges.storeFinalizationOnChain_depReachable
      S.E S.hc S.cfg (S.node w) hdep
  have hCrun: RunBlock S rho C:= by
    obtain ⟨n, hn, _⟩:= Proofs.Bridges.stateBeforeTime_eq_stateBefore
      S adm.toScheduleWellFormed read
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw (i:= n)
    simpa only [st, Run.storeBeforeTime, hn] using hC
  have hhjlt: st.h_j < M - 1:= by
    rw [Nat.lt_sub_iff_add_lt]
    exact Nat.lt_of_succ_le (by
      simpa only [Nat.add_assoc] using hgateOff')
  have hcrossed: (derived_state S.E S.cfg C).h_F <
      (derived_state S.E S.cfg X).h:= by
    calc
      (derived_state S.E S.cfg C).h_F ≤
          (derived_state S.E S.cfg C).h_j:=
        (Protocol.chainOrder_derived_state S.E S.cfg C).heights_ordered
      _ ≤ st.h_j:= hnoHigh C hC
      _ < M - 1:= hhjlt
      _ ≤ (derived_state S.E S.cfg X).h:= hXh
  have hFX: Block.Preceq st.F X:= by
    have hpre: Block.Preceq (derived_state S.E S.cfg C).F X:=
      Protocol.finalized_preceq_of_height_lt hsb hCrun hXrun
        (adm.toRootCollisionFree.root_injective X C hXrun hCrun)
        ⟨rfl, rfl⟩ hcrossed
    simpa only [hF] using hpre
  have hgate: ¬ st.h_max = st.h_j + 1:= by
    apply Nat.ne_of_gt
    rw [hfrontier']
    exact Nat.lt_of_succ_le (by simpa only [Nat.add_assoc] using hgateOff')
  have hroot: Protocol.get_fg_root st.toHealing.toFG = st.F:= by
    simp only [Protocol.get_fg_root, Protocol.Store.toHealing, if_neg hgate]
  simpa only [st, hroot] using hFX

/-- The filtered prior action carrier has a processed descendant in the thin
frontier window. -/
theorem actionSGBlockAt_frontierWitness
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {v: V} {r: Round} {M: Height}
    (hfrontier: (rho.storeBeforeTime S v (S.a r)).h_max = M):
    ∃ W ∈ (actionStoreAt S rho v r).T,
      Block.Preceq (actionSGBlockAt S rho v r) W ∧
        M - 1 ≤ (derived_state S.E S.cfg W).h:= by
  have hfiltered:= actionSGBlockAt_mem_filtered_actionStore S adm v r
  simp only [Protocol.get_filtered_block_tree,
    Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq,
    Protocol.Store.toHealing] at hfiltered
  obtain ⟨⟨⟨-, -⟩, W, hWT, hcarrierW, hheight⟩, -⟩:= hfiltered
  have hmax: (actionStoreAt S rho v r).h_max = M:= by
    have hfinality:= attestStore_finality S
      (rho.stateBeforeTime S (S.a r) v).st (S.a r)
    change (Proofs.Optimistic.attestStore S
      (rho.stateBeforeTime S (S.a r) v).st (S.a r)).h_max = M
    rw [hfinality.2.2.1]
    simpa only [Run.storeBeforeTime] using hfrontier
  have hagree:= derivedStateAgrees_actionStoreAt S adm v r
  refine ⟨W, hWT, hcarrierW, ?_⟩
  calc
    M - 1 = (actionStoreAt S rho v r).h_max - 1:= by rw [hmax]
    _ ≤ ((actionStoreAt S rho v r).σ W).h:= hheight
    _ = (derived_state S.E S.cfg W).h:=
      congrArg (fun cs => cs.h) (hagree W hWT)

/-- Gate-off exact frontier reads settle all preceding honest action carriers.
The source frontier must be pointwise: an equality only for `honestHMaxAt`
does not determine the local frontier of the honest grade supporter. -/
theorem previousActionCarriersQuietAt_of_gateOff
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hsb: SlashableBound S rho)
    {r: Round} (hr: 0 < r) {M: Height}
    (hpost: S.E.t_GST ≤ S.a (r - 1))
    (hprev: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (r - 1))).h_max = M)
    (hfrontier: ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a r)).h_max = M)
    (hgateOff: ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a r)).h_j + 2 ≤ M)
    (hhor: S.a r ≤ rho.horizon):
    PreviousActionCarriersQuietAt S rho r:= by
  intro u hu w hw
  have hM: 1 ≤ M:= by
    have h:= hgateOff w hw
    exact (Nat.succ_le_succ (Nat.zero_le 1)).trans
      (Nat.le_add_left 2 (rho.storeBeforeTime S w (S.a r)).h_j) |>.trans h
  obtain ⟨W, hWT, hcarrierW, hWh⟩:=
    actionSGBlockAt_frontierWitness S adm (hprev u hu)
  have hWrun: RunBlock S rho W:= by
    have hWpre: W ∈ (rho.storeBeforeTime S u (S.a (r - 1))).T:= by
      have hfields:= Proofs.Optimistic.attestStore_fields S
        (rho.stateBeforeTime S (S.a (r - 1)) u).st (S.a (r - 1))
      simpa only [actionStoreAt, hfields.2.1, Run.storeBeforeTime] using hWT
    obtain ⟨n, hn, -⟩:= Proofs.Bridges.stateBeforeTime_eq_stateBefore
      S adm.toScheduleWellFormed (S.a (r - 1))
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hu (i:= n)
    rw [← hn]
    exact hWpre
  have hrootW: Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w (S.a r)).toHealing.toFG) W:=
    frontierRoot_preceq_of_gateOff S adm hsb hw hWrun hWh
      (hfrontier w hw) (hgateOff w hw)
  have hdelay: S.a (r - 1) + S.E.Δ ≤ S.a r:=
    Protocol.previous_action_add_delta_le_action S hr
  have hWhAction: M - 1 ≤ ((actionStoreAt S rho u (r - 1)).σ W).h:= by
    rw [derivedStateAgrees_actionStoreAt S adm u (r - 1) W hWT]
    exact hWh
  obtain ⟨hWtarget, -, -⟩:=
    actionConeWitness_visibleAtReader_after_gst S adm (r:= r - 1)
      hu hw hWT (Block.preceq_self W) hWhAction hpost hdelay hhor hrootW
  have hWfiltered: W ∈ Protocol.get_filtered_block_tree
      (rho.storeBeforeTime S w (S.a r)).toHealing.toFG:=
    frontierBlock_filtered_of_gateOff S adm hsb hw hhor hWtarget hWrun hWh hM
      (hfrontier w hw) (hgateOff w hw)
  have hWquiet: FinalityFilterNoninterferenceAtRead S rho w (S.a r) W:=
    Or.inr hWfiltered
  exact hWquiet.ancestor S adm hcarrierW

/-- Quiet previous honest action carriers settle every selected grade-2 block
at the current action read. -/
theorem selectedG2SettledAt_of_previousActionCarriersQuiet
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest) {r: Round} (hr: 0 < r)
    (hpost: S.E.t_GST ≤ S.a (r - 1))
    (hcut: S.hc.Γ_neg1 S.E.Δ r ≤ rho.horizon)
    (hquiet: PreviousActionCarriersQuietAt S rho r):
    SelectedG2SettledAt S rho r:= by
  intro u hu Q hQ w hw
  have hQG2Action: Protocol.G2 S.E
      (actionStoreAt S rho u r).toHealing.gradeView S.hc r Q = true:=
    (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hQ)).2
  have hQG2: Protocol.G2 S.E (gradeViewAt S rho u r) S.hc r Q = true:= by
    unfold actionStoreAt at hQG2Action
    rw [Protocol.G2_attestStore_eq S] at hQG2Action
    simpa only [gradeViewAt, healStoreAt, Run.storeBeforeTime] using hQG2Action
  have hpred: r - 1 + 1 = r:=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hr)
  obtain ⟨v, hv, hQcarrier⟩:=
    G2_preceq_honestPreviousActionCarrier S adm hfb hu (r - 1) hpost
      (by simpa only [hpred] using hcut) (by simpa only [hpred] using hQG2)
  exact (hquiet v hv w hw).ancestor S adm hQcarrier

/-- Quiet previous honest action carriers settle every live grade-1 block at
The current action read. -/
theorem liveG1SettledAt_of_previousActionCarriersQuiet
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest) {r: Round} (hr: 0 < r)
    (hpost: S.E.t_GST ≤ S.a (r - 1))
    (hcut: S.hc.Γ_neg1 S.E.Δ r ≤ rho.horizon)
    (hquiet: PreviousActionCarriersQuietAt S rho r):
    LiveG1SettledAt S rho r:= by
  intro u hu B hG1 w hw
  have hpred: r - 1 + 1 = r:=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hr)
  obtain ⟨v, hv, hBcarrier⟩:=
    G1_preceq_honestPreviousActionCarrier S adm hfb hu (r - 1) hpost
      (by simpa only [hpred] using hcut) (by simpa only [hpred] using hG1)
  exact (hquiet v hv w hw).ancestor S adm hBcarrier

/-- The existing one-chain assembler applied after the two carrier-quietness
settlement projections. -/
theorem honestActionCarriersOneChainAt_of_previousActionCarriersQuiet
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest) {r: Round} (hr: 0 < r)
    (hpostPrev: S.E.t_GST ≤ S.a (r - 1))
    (hcut: S.hc.Γ_neg1 S.E.Δ r ≤ rho.horizon)
    (hquiet: PreviousActionCarriersQuietAt S rho r)
    (hready: GradeRoundReady S rho r)
    (hpost: S.E.t_GST ≤ Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hhor: Protocol.confirmation_time S.E (S.hc.opening_slot r) ≤ rho.horizon)
    (hselectedExists: ∀ v ∈ rho.honest, ∃ Q,
      Protocol.grade2_block S.E S.hc
        (actionStoreAt S rho v r).toHealing r = some Q)
    (hgenuine: ∀ v ∈ rho.honest,
      GenuineConfirmation (contract:= Protocol.GradeContract.current) S.E S.hc
        (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r))
        (S.hc.opening_slot r)
        (actionStoreAt S rho v r).live_confirmed):
    HonestActionCarriersOneChainAt S rho r:= by
  apply honestActionCarriers_oneChain_of_settled S adm hready hpost hhor
  · exact selectedG2SettledAt_of_previousActionCarriersQuiet
      S adm hfb hr hpostPrev hcut hquiet
  · exact liveG1SettledAt_of_previousActionCarriersQuiet
      S adm hfb hr hpostPrev hcut hquiet
  · exact hselectedExists
  · exact hgenuine

/-- Gate-off exact frontiers settle the selected grade-2 blocks at the next
action read. The previous frontier is pointwise because the honest supporter
may be any validator. -/
theorem selectedG2SettledAt_of_gateOff
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest) {r: Round} (hr: 0 < r)
    {M: Height} (hpost: S.E.t_GST ≤ S.a (r - 1))
    (hprev: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (r - 1))).h_max = M)
    (hfrontier: ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a r)).h_max = M)
    (hgateOff: ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a r)).h_j + 2 ≤ M)
    (hhor: S.a r ≤ rho.horizon):
    SelectedG2SettledAt S rho r:= by
  have hsb:= slashableBound_of_admissible_belowOneThird S adm hfb
  have hquiet:= previousActionCarriersQuietAt_of_gateOff S adm hsb hr hpost
    hprev hfrontier hgateOff hhor
  have hpred: r - 1 + 1 = r:=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hr)
  have hcut':= le_of_lt (next_Γ_neg1_lt_action S (r - 1))
  rw [hpred] at hcut'
  exact selectedG2SettledAt_of_previousActionCarriersQuiet
    S adm hfb hr hpost (hcut'.trans hhor) hquiet

/-- Gate-off exact frontiers settle every live grade-1 block at the next
action read. -/
theorem liveG1SettledAt_of_gateOff
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest) {r: Round} (hr: 0 < r)
    {M: Height} (hpost: S.E.t_GST ≤ S.a (r - 1))
    (hprev: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (r - 1))).h_max = M)
    (hfrontier: ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a r)).h_max = M)
    (hgateOff: ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a r)).h_j + 2 ≤ M)
    (hhor: S.a r ≤ rho.horizon):
    LiveG1SettledAt S rho r:= by
  have hsb:= slashableBound_of_admissible_belowOneThird S adm hfb
  have hquiet:= previousActionCarriersQuietAt_of_gateOff S adm hsb hr hpost
    hprev hfrontier hgateOff hhor
  have hpred: r - 1 + 1 = r:=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hr)
  have hcut':= le_of_lt (next_Γ_neg1_lt_action S (r - 1))
  rw [hpred] at hcut'
  exact liveG1SettledAt_of_previousActionCarriersQuiet
    S adm hfb hr hpost (hcut'.trans hhor) hquiet

/-- Gate-off exact frontiers give the one-chain action-carrier conclusion when
the action has a selected grade-2 block and a genuine confirmation. These two
facts are residual: gate-off and a fixed frontier do not force either a
selected grade-2 block or a non-root confirmation. -/
theorem honestActionCarriersOneChainAt_of_gateOff
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest) {r: Round} (hr: 0 < r)
    {M: Height} (hpost: S.E.t_GST ≤ S.a (r - 1))
    (hprev: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (r - 1))).h_max = M)
    (hfrontier: ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a r)).h_max = M)
    (hgateOff: ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a r)).h_j + 2 ≤ M)
    (hhor: S.a r ≤ rho.horizon)
    (hselectedExists: ∀ v ∈ rho.honest, ∃ Q,
      Protocol.grade2_block S.E S.hc
        (actionStoreAt S rho v r).toHealing r = some Q)
    (hgenuine: ∀ v ∈ rho.honest,
      GenuineConfirmation (contract:= Protocol.GradeContract.current) S.E S.hc
        (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r))
        (S.hc.opening_slot r)
        (actionStoreAt S rho v r).live_confirmed):
    HonestActionCarriersOneChainAt S rho r:= by
  have hpred: r - 1 + 1 = r:=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hr)
  have hgstCut: S.E.t_GST ≤ S.hc.Γ_neg1 S.E.Δ r:= by
    have h:= gst_le_Γ_neg1_succ S (r - 1) hpost
    simpa only [hpred] using h
  have hready: GradeRoundReady S rho r:=
    gradeRoundReady_of_action_horizon S hgstCut (le_refl r) hhor
  have hround: S.hc.round_of (S.hc.opening_slot r) = r:= by
    simp only [Protocol.HealConfig.round_of, Protocol.HealConfig.opening_slot]
    exact Nat.mul_div_left r
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hdelay:= Protocol.previous_action_add_delta_le_proposal S
    (s:= S.hc.opening_slot r) (by simpa only [hround] using hr)
  rw [hround] at hdelay
  have hproposal: S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot r):= by
    exact hpost.trans
      ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans hdelay)
  have hconfirmation: Protocol.confirmation_time S.E
      (S.hc.opening_slot r) ≤ rho.horizon:= by
    simpa only [← Protocol.a_eq_confirmation_time] using hhor
  apply honestActionCarriers_oneChain_of_settled S adm hready hproposal
    hconfirmation
  · exact selectedG2SettledAt_of_gateOff S adm hfb hr hpost hprev
      hfrontier hgateOff hhor
  · exact liveG1SettledAt_of_gateOff S adm hfb hr hpost hprev
      hfrontier hgateOff hhor
  · exact hselectedExists
  · exact hgenuine

 -/



/-! ## Named frontier and quietness declarations -/

/-- At a gate-off exact frontier read, a named run block in the thin window
descends from the selected FG root. -/
theorem frontierRoot_preceq_of_gateOff
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {w : V} (hw : w ∈ rho.honest) {read : Time}
    {X : Block V} {Xn : NamedBlock V} {M : Height}
    (hXerase : Xn.erase = X) (hXrun : RunBlock S rho Xn)
    (hXh : M - 1 ≤ (Protocol.derive_named S.E S.cfg Xn).h)
    (hfrontier : (rho.storeBeforeTime S w read).h_max = M)
    (hgateOff : (rho.storeBeforeTime S w read).h_j + 2 ≤ M) :
    Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w read).toHealing.toFG) X := by
  let st := rho.storeBeforeTime S w read
  have hfrontier' : st.h_max = M := by
    simpa only [st] using hfrontier
  have hgateOff' : st.h_j + 2 ≤ M := by
    simpa only [st] using hgateOff
  have hnoHigh : Internal.NamedNoHighJustifications S.E S.cfg st :=
    NamedJustificationBound.noHighJustifications_stateBeforeTime S rho read w
  obtain ⟨C, hC, hF, -⟩ :=
    Proofs.Bridges.storeFinalizationOnChain_stateBeforeTime S rho read w
  have hCrun : RunBlock S rho C := by
    obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed read
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw (i := n)
    simpa only [st, Run.storeBeforeTime, hn] using hC
  have hhjlt : st.h_j < M - 1 := by
    rw [Nat.lt_sub_iff_add_lt]
    exact Nat.lt_of_succ_le (by
      simpa only [Nat.add_assoc] using hgateOff')
  have hcrossed : (Protocol.derive_named S.E S.cfg C).h_F <
      (Protocol.derive_named S.E S.cfg Xn).h := by
    calc
      (Protocol.derive_named S.E S.cfg C).h_F ≤
          (Protocol.derive_named S.E S.cfg C).h_j :=
        (NamedDerivationGeometry.chainOrder_derive_named S.E S.cfg C).heights_ordered
      _ ≤ st.h_j := hnoHigh C hC
      _ < M - 1 := hhjlt
      _ ≤ (Protocol.derive_named S.E S.cfg Xn).h := hXh
  have hFX : Block.Preceq st.F X := by
    have hpre := NamedFinalizationBridge.finalized_preceq_of_height_lt
      S rho Xn C hsb adm.toNamedAdmissibleCore.toNamedRootCollisionFree
      hXrun hCrun hcrossed
    rw [hXerase] at hpre
    simpa only [hF] using hpre
  have hgate : ¬ st.h_max = st.h_j + 1 := by
    apply Nat.ne_of_gt
    rw [hfrontier']
    exact Nat.lt_of_succ_le (by simpa only [Nat.add_assoc] using hgateOff')
  have hroot : Protocol.get_fg_root st.toHealing.toFG = st.F := by
    simp only [Protocol.get_fg_root, Protocol.Store.toHealing, if_neg hgate]
  simpa only [st, hroot] using hFX

/-- The filtered prior action carrier has a named processed descendant in the
thin frontier window. -/
theorem actionSGBlockAt_frontierWitness
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} {r : Round} {M : Height}
    (hfrontier : (rho.storeBeforeTime S v (S.a r)).h_max = M) :
    ∃ W : NamedBlock V,
      W ∈ (actionStoreAt S rho v r).st.bodies ∧
        Block.Preceq (actionSGBlockAt S rho v r) W.erase ∧
          M - 1 ≤ (Protocol.derive_named S.E S.cfg W).h := by
  have hfiltered := actionSGBlockAt_mem_filtered_actionStore S adm v r
  simp only [Protocol.get_filtered_block_tree,
    Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq,
    Protocol.Store.toHealing] at hfiltered
  obtain ⟨⟨⟨-, -⟩, W, hWT, hcarrierW, hheight⟩, -⟩ := hfiltered
  have hmax : (actionStoreAt S rho v r).st.core.h_max = M := by
    rw [actionStoreAt_eq_update_confirmation_confStore]
    simp only [Protocol.update_confirmation_with]
    simpa only [Run.storeBeforeTime] using hfrontier
  rw [hmax] at hheight
  have hWTpre : W ∈ (rho.storeBeforeTime S v (S.a r)).core.T := by
    have hWT' := hWT
    rw [actionStoreAt_eq_update_confirmation_confStore] at hWT'
    simpa only [Protocol.update_confirmation_with] using hWT'
  obtain ⟨D, hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho (S.a r) v hWTpre
  have hsig : (actionStoreAt S rho v r).st.core.σ D.erase =
      Protocol.derive_named S.E S.cfg D := by
    rw [actionStoreAt_eq_update_confirmation_confStore]
    simpa only [Protocol.update_confirmation_with, hDerase] using
      (Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho (S.a r) v D hDbody)
  refine ⟨D, ?_, ?_, ?_⟩
  · exact hDbody
  · simpa only [hDerase] using hcarrierW
  · rw [← congrArg (fun cs => cs.h) hsig]
    simpa only [hDerase] using hheight

/-- Gate-off exact frontier reads settle all preceding honest action carriers.
The source frontier is pointwise because the honest supporter may be any node. -/
theorem previousActionCarriersQuietAt_of_gateOff
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {r : Round} (hr : 0 < r) {M : Height}
    (hpost : S.E.t_GST ≤ S.a (r - 1))
    (hprev : ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (r - 1))).h_max = M)
    (hfrontier : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a r)).h_max = M)
    (hgateOff : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a r)).h_j + 2 ≤ M)
    (hhor : S.a r ≤ rho.horizon) :
    PreviousActionCarriersQuietAt S rho r := by
  intro u hu w hw
  have hM : 1 ≤ M := by
    have h := hgateOff w hw
    exact (Nat.succ_le_succ (Nat.zero_le 1)).trans
      (Nat.le_add_left 2 (rho.storeBeforeTime S w (S.a r)).h_j) |>.trans h
  obtain ⟨W, hWbody, hcarrierW, hWh⟩ :=
    actionSGBlockAt_frontierWitness S adm (hprev u hu)
  have hWrun : RunBlock S rho W := by
    have hWpre : W ∈ (rho.storeBeforeTime S u (S.a (r - 1))).bodies := by
      simpa only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
        NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hWbody
    obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.a (r - 1))
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hu (i := n)
    rw [← hn]
    exact hWpre
  have hrootW : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w (S.a r)).toHealing.toFG) W.erase :=
    frontierRoot_preceq_of_gateOff S adm hsb hw
      (X := W.erase) (Xn := W) rfl hWrun hWh
      (hfrontier w hw) (hgateOff w hw)
  have hdelay : S.a (r - 1) + S.E.Δ ≤ S.a r :=
    Protocol.previous_action_add_delta_le_action S hr
  obtain ⟨hWtarget, -, -⟩ :=
    actionConeWitness_visibleAtReader_after_gst S adm (r := r - 1)
      hu hw hWbody (Block.preceq_self W.erase) hWh hpost hdelay hhor hrootW
  have hWtargetCore : W.erase ∈
      (rho.storeBeforeTime S w (S.a r)).core.T := by
    have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
      (S.a r) w).1.1.1
    change W.erase ∈ (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.T
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hWtarget
  have hWfiltered : W.erase ∈ Protocol.get_filtered_block_tree
      (rho.storeBeforeTime S w (S.a r)).toHealing.toFG :=
    frontierBlock_filtered_of_gateOff S adm hsb hw hhor hWtargetCore
      rfl hWrun hWh hM (hfrontier w hw) (hgateOff w hw)
  have hWquiet : FinalityFilterNoninterferenceAtRead S rho w (S.a r) W.erase :=
    Or.inr hWfiltered
  exact hWquiet.ancestor S adm hcarrierW

/-- Quiet previous honest action carriers settle every selected grade-2 block
at the current action read. -/
theorem selectedG2SettledAt_of_previousActionCarriersQuiet
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (hr : 0 < r)
    (hwindow : RelativeCarrierWindowAt S rho (r - 1) .g2)
    (hmajority : Internal.NamedOutageEntry.GradeFormingMajority S rho r)
    (hquiet : PreviousActionCarriersQuietAt S rho r) :
    SelectedG2SettledAt S rho r := by
  intro u hu Q hQ w hw
  have hpred : r - 1 + 1 = r :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hr)
  have hQgrade := selectedQ2_storeGrade_at_g2Domain S adm hQ
  have hQgrade' : Internal.PhaseGrades.storeGrade S.E S.hc
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc ((r - 1) + 1) .g2) u).st
      ((r - 1) + 1) .g2 Q = true := by
    simpa only [Internal.PhaseGrades.readAt, hpred] using hQgrade
  have hmajority' : Internal.NamedOutageEntry.GradeFormingMajority
      S rho ((r - 1) + 1) := by
    simpa only [hpred] using hmajority
  obtain ⟨v, hv, hQcarrier⟩ := relativeGrade_has_roundCarrier
    S adm.toNamedAdmissibleCore hwindow hmajority' hu hQgrade'
  have hvHon : v ∈ rho.honest :=
    ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho v (r - 1)).mp hv).1
  exact (hquiet v hvHon w hw).ancestor S adm hQcarrier


/-- Gate-off exact frontiers settle the selected grade-2 blocks at the next
action read. -/
theorem selectedG2SettledAt_of_gateOff
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest) {r : Round} (hr : 0 < r)
    (hwindow : RelativeCarrierWindowAt S rho (r - 1) .g2)
    (hmajority : Internal.NamedOutageEntry.GradeFormingMajority S rho r)
    {M : Height} (hpost : S.E.t_GST ≤ S.a (r - 1))
    (hprev : ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (r - 1))).h_max = M)
    (hfrontier : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a r)).h_max = M)
    (hgateOff : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a r)).h_j + 2 ≤ M)
    (hhor : S.a r ≤ rho.horizon) :
    SelectedG2SettledAt S rho r := by
  have hsb := slashableBound_of_admissible_belowOneThird S adm hfb
  have hquiet := previousActionCarriersQuietAt_of_gateOff S adm hsb hr hpost
    hprev hfrontier hgateOff hhor
  exact selectedG2SettledAt_of_previousActionCarriersQuiet
    S adm hr hwindow hmajority hquiet


end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms actionSGBlockAt_mem_filtered_actionStore
#print axioms frontierRoot_preceq_of_gateOff
#print axioms actionSGBlockAt_frontierWitness
#print axioms previousActionCarriersQuietAt_of_gateOff
#print axioms selectedG2SettledAt_of_previousActionCarriersQuiet
#print axioms selectedG2SettledAt_of_gateOff
end DecoupledConsensusModel.Proofs.HealingSurface

end
