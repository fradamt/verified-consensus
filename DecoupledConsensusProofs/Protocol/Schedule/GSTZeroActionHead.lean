module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.ProposalCanonicality
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.VoteViewValidity
public import DecoupledConsensusProofs.Protocol.Schedule.GSTZeroReorgResilience
public import DecoupledConsensusProofs.Protocol.Schedule.Action
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.ValidatorClient.FinalityPairCore
public import DecoupledConsensusProofs.Protocol.Schedule.ConfirmationHistoryProducer
public import DecoupledConsensusInternal.Execution.Run
public import DecoupledConsensusProofs.Execution.Concentration
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Protocol.ChainState.DerivationGeometry
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryHandoffCore
public import DecoupledConsensusInternal.Legacy.Definitions.NamedHeadReads

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution
open Internal.NamedRecoveryRead

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Prefix-index transport -/



/-! ## The named action store's field transport -/

/-- The action read preserves every Goldfish pool bucket. -/
theorem actionStoreAt_pool
    (S : Setup V) (rho : Run V) (v : V) (r : Round) (q : Slot) :
    (Proofs.HealingSurface.actionStoreAt S rho v r).pool q =
      (rho.storeBeforeTime S v (S.a r)).pool q := by
  rfl

/-- The action read preserves block receipt timestamps. -/
theorem actionStoreAt_timestamp_block
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    (Proofs.HealingSurface.actionStoreAt S rho v r).timestamp_block =
      (rho.storeBeforeTime S v (S.a r)).timestamp_block := by
  rfl

/-- The action read preserves the processed block tree. -/
theorem actionStoreAt_T
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    (Proofs.HealingSurface.actionStoreAt S rho v r).T =
      (rho.storeBeforeTime S v (S.a r)).T := by
  rfl

/-- The action read has the slot selected by its scheduled action time. -/
theorem actionStoreAt_slot_of_action_eq_cutoff
    (S : Setup V) (rho : Run V) (v : V) (r : Round) (q : Slot)
    (ha : S.a r = Protocol.support_cutoff S.E q) :
    (Proofs.HealingSurface.actionStoreAt S rho v r).s = q := by
  change S.E.slotOf (S.a r) = q
  rw [ha]
  exact Proofs.Optimistic.slotOf_support_cutoff S.E q


/-- Core-admissibility twin of `honest_vote_mem_actionStore_pair`. -/
theorem honest_vote_mem_actionStore_pair_core
    (S : Setup V) {rho : Run V} (core : Proofs.AdmissibleCore S rho)
    (hGST : S.E.t_GST = 0)
    {q : Slot} (hq : 0 < q)
    (hhor : Protocol.support_cutoff S.E q <= rho.horizon)
    {x : V} (hx : x ∈ rho.honest) {u : GoldfishVote V}
    (huq : u.slot = q)
    (hemit : rho.emits S x (Object.gfVote u) (Protocol.vote_time S.E q))
    {v : V} (hv : v ∈ rho.honest) {r : Round}
    (ha : S.a r = Protocol.support_cutoff S.E q)
    {X : Block V}
    (hfind : Block.find? (Proofs.HealingSurface.actionStoreAt S rho v r).T u.head = some X) :
    u ∈ (Proofs.HealingSurface.actionStoreAt S rho v r).pool q ∧
      u ∈ ((Proofs.HealingSurface.actionStoreAt S rho v r).pool q).filter
        (fun z => Protocol.resolved
          (Proofs.HealingSurface.actionStoreAt S rho v r).T z = true) := by
  have hpost : S.E.t_GST ≤ Protocol.vote_time S.E q := by
    rw [hGST]
    exact Proofs.Optimistic.vote_time_nonneg S.E q
  have hcut := gfVote_in_cutoff_view_after_gst
    S core hx hq hpost hemit huq hv
      (S.a r) (S.a r) (by rw [ha]) (by rw [ha]) hhor
  have hpre : u ∈ (rho.storeBeforeTime S v (S.a r)).pool q :=
    (Finset.mem_filter.mp hcut).1
  have hpool : u ∈ (Proofs.HealingSurface.actionStoreAt S rho v r).pool q := by
    rw [actionStoreAt_pool S rho v r q]
    exact hpre
  have hslot : X.slot ≤ u.slot :=
    Proofs.Optimistic.emitted_vote_head_slot_le_of_store_mem S core
      hx hv hemit huq (by
        rw [← actionStoreAt_T S rho v r]
        exact Proofs.HealingLemmas.find?_mem hfind)
      (Proofs.HealingLemmas.find?_root hfind)
  refine ⟨hpool, Finset.mem_filter.mpr ⟨hpool, ?_⟩⟩
  simp [Protocol.resolved, hfind, hslot]

#print axioms honest_vote_mem_actionStore_pair_core


/-- Core-admissibility twin of `coneSupport_actionStoreAt`. -/
theorem coneSupport_actionStoreAt_core
    (S : Setup V) {rho : Run V} (core : Proofs.AdmissibleCore S rho)
    (hGST : S.E.t_GST = 0)
    (hcom : HonestCommittees S rho.honest)
    {q : Slot} (hq : 0 < q)
    (hhor : Protocol.support_cutoff S.E q <= rho.horizon)
    {tgt : Block V -> Prop}
    (hnames : Proofs.HealingSurface.NamedHonestVotesCone S rho q tgt)
    {v : V} (hv : v ∈ rho.honest) {r : Round}
    (ha : S.a r = Protocol.support_cutoff S.E q)
    (hresolve : Proofs.Optimistic.HeadsResolveIn S rho q
      (Proofs.HealingSurface.actionStoreAt S rho v r).T
      (Proofs.HealingSurface.actionStoreAt S rho v r).timestamp_block) :
    let ast := Proofs.HealingSurface.actionStoreAt S rho v r
    let raw := ast.pool q
    let support := raw.filter (fun u => Protocol.resolved ast.T u = true)
    Proofs.Optimistic.ConeSupport S.E ast.T raw support raw q rho.honest tgt := by
  dsimp only
  apply Proofs.Optimistic.coneSupport_of_named_votes (hcom q) (subset_refl _)
  · exact Finset.filter_subset _ _
  · obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
      S core.toNamedScheduleWellFormed (S.a r)
    intro x _ hx
    have hno := Proofs.Optimistic.pool_no_honest_equivocation_of_core
      S core v n q hx
    rw [actionStoreAt_pool S rho v r q]
    have hstore : rho.storeBeforeTime S v (S.a r) =
        (rho.stateBefore S n v).st :=
      congrArg NamedNodeState.st (congrFun hn v)
    rw [hstore]
    exact hno
  · intro x hxCommittee hxHonest
    obtain ⟨X, hX, hXrun, hXemit⟩ := hnames x hxHonest hxCommittee
    obtain ⟨hfind, -⟩ := hresolve X.erase
      ⟨x, hxHonest, hxCommittee, ⟨X, rfl, hXrun⟩, hXemit⟩
    have hpair := honest_vote_mem_actionStore_pair_core
      S core hGST hq hhor hxHonest rfl hXemit hv ha hfind
    have hslot : X.erase.slot ≤ q :=
      Proofs.Optimistic.emitted_vote_head_slot_le_of_store_mem S core
        hxHonest hv hXemit rfl (by
          rw [← actionStoreAt_T S rho v r]
          exact Proofs.HealingLemmas.find?_mem hfind)
        (Proofs.HealingLemmas.find?_root hfind)
    exact ⟨X.erase, hX, hslot, hpair.2, hfind⟩

#print axioms coneSupport_actionStoreAt_core

/-! ## The named candidate path -/


/-- Core-admissibility twin of `actionPath_to_ancestor_of_candidate`. -/
theorem actionPath_to_ancestor_of_candidate_core
    (S : Setup V) {rho : Run V} (_core : Proofs.AdmissibleCore S rho)
    {v : V} {r : Round} {B E : Block V}
    (hE : E ∈ Protocol.get_filtered_block_tree
      (Proofs.HealingSurface.actionStoreAt S rho v r).toHealing.toFG)
    (hBE : Block.Preceq B E) :
    ∀ C : Block V,
      Block.Preceq
          (Protocol.get_sg_root_with
            (NamedProfile.gradeContract
              (Proofs.HealingSurface.actionStoreAt S rho v r).cache)
            S.E S.hc
            (Proofs.HealingSurface.actionStoreAt S rho v r).toHealing
            (S.hc.round_of
              (Proofs.HealingSurface.actionStoreAt S rho v r).s)) C ->
        C ≠ Protocol.get_sg_root_with
          (NamedProfile.gradeContract
            (Proofs.HealingSurface.actionStoreAt S rho v r).cache)
          S.E S.hc (Proofs.HealingSurface.actionStoreAt S rho v r).toHealing
          (S.hc.round_of (Proofs.HealingSurface.actionStoreAt S rho v r).s) ->
        Block.Preceq C B ->
        C ∈ Protocol.get_filtered_block_tree
          (Proofs.HealingSurface.actionStoreAt S rho v r).toHealing.toFG := by
  let pre := rho.storeBeforeTime S v (S.a r)
  let ast := Proofs.HealingSurface.actionStoreAt S rho v r
  have hpc : ParentClosed pre.core :=
    Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho (S.a r) v
  have hFJpre : Block.Preceq pre.F pre.J :=
    Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
      S rho (S.a r) v
  have hFJ : Block.Preceq ast.F ast.J := by
    simpa only [ast, pre] using hFJpre
  intro C hAC _ hCB
  have hET : E ∈ ast.T := Proofs.Records.get_filtered_block_tree_subset _ hE
  have hETpre : E ∈ pre.T := by
    rw [← actionStoreAt_T S rho v r]
    exact hET
  have hCTpre : C ∈ pre.T :=
    Proofs.Records.mem_of_preceq ((Proofs.parentClosed_iff pre.core).mp hpc).2 C E hETpre
      (Block.preceq_trans hCB hBE)
  have hCT : C ∈ ast.T := by
    rw [actionStoreAt_T S rho v r]
    exact hCTpre
  apply Proofs.Records.mem_filtered_of_preceq
    (st := ast.toHealing.toFG) hFJ hE hCT
      (Block.preceq_trans hCB hBE)
  exact Block.preceq_trans
    (Proofs.HealingSurface.fg_root_preceq_get_sg_root_with_frame
      ast.cache S.E S.hc ast.toHealing (S.hc.round_of ast.s)) hAC

#print axioms actionPath_to_ancestor_of_candidate_core

/-! ## The exact named action head -/





/-- Core-admissibility twin of
`protectedBlock_preceq_actionHead_of_cone_compatible`. -/
theorem protectedBlock_preceq_actionHead_of_cone_compatible_core
    (S : Setup V) {rho : Run V} (core : Proofs.AdmissibleCore S rho)
    {q : Slot} {v : V} {r : Round}
    (ha : S.a r = Protocol.support_cutoff S.E q)
    {B : Block V}
    (hcone :
      let ast := Proofs.HealingSurface.actionStoreAt S rho v r
      let raw := ast.pool q
      let support := raw.filter (fun u => Protocol.resolved ast.T u = true)
      Proofs.Optimistic.ConeSupport S.E ast.T raw support raw q rho.honest
        (fun X => Block.Preceq B X))
    (hcompat :
      Block.compatible
        (Protocol.get_sg_root_with
          (NamedProfile.gradeContract
            (Proofs.HealingSurface.actionStoreAt S rho v r).cache)
          S.E S.hc
          (Proofs.HealingSurface.actionStoreAt S rho v r).toHealing
          (S.hc.round_of
            (Proofs.HealingSurface.actionStoreAt S rho v r).s)) B = true)
    (hpath :
      Block.Preceq
          (Protocol.get_sg_root_with
            (NamedProfile.gradeContract
              (Proofs.HealingSurface.actionStoreAt S rho v r).cache)
            S.E S.hc
            (Proofs.HealingSurface.actionStoreAt S rho v r).toHealing
            (S.hc.round_of
              (Proofs.HealingSurface.actionStoreAt S rho v r).s)) B ->
        ∀ C : Block V,
          Block.Preceq
              (Protocol.get_sg_root_with
                (NamedProfile.gradeContract
                  (Proofs.HealingSurface.actionStoreAt S rho v r).cache)
                S.E S.hc
                (Proofs.HealingSurface.actionStoreAt S rho v r).toHealing
                (S.hc.round_of
                  (Proofs.HealingSurface.actionStoreAt S rho v r).s)) C ->
          C ≠ Protocol.get_sg_root_with
            (NamedProfile.gradeContract
              (Proofs.HealingSurface.actionStoreAt S rho v r).cache)
            S.E S.hc
            (Proofs.HealingSurface.actionStoreAt S rho v r).toHealing
            (S.hc.round_of (Proofs.HealingSurface.actionStoreAt S rho v r).s) ->
          Block.Preceq C B ->
          C ∈ Protocol.get_filtered_block_tree
            (Proofs.HealingSurface.actionStoreAt S rho v r).toHealing.toFG) :
    Block.Preceq B (Internal.actionHeadAt S rho v r) := by
  let ast := Proofs.HealingSurface.actionStoreAt S rho v r
  let raw := ast.pool q
  let support := raw.filter (fun u => Protocol.resolved ast.T u = true)
  let gc := NamedProfile.gradeContract ast.cache
  have hslot : ast.s = q := by
    simpa only [ast] using
      actionStoreAt_slot_of_action_eq_cutoff S rho v r q ha
  have hvalid0 := voteSetValid_pool_stateBeforeTime
    S core.toNamedScheduleWellFormed v (S.a r) q
  have hvalid : Protocol.VoteSetValid S.E q raw := by
    simpa only [ast, raw, actionStoreAt_pool S rho v r q] using hvalid0
  have hhead : Block.Preceq B
      (Protocol.get_head_with gc S.E S.hc ast.toHealing raw support q) := by
    unfold Protocol.get_head_with
    rw [Proofs.Optimistic.get_head_in_tree_split_with]
    exact goldfish_fork_choice_captures_supporter_majority
      S.E ast.σ ast.h_max ast.T
      (Protocol.get_filtered_block_tree ast.toHealing.toFG) ast.s
      raw support q (Proofs.Optimistic.ConeSupport.sub hcone)
      (supporterMajority_of_cone S.E hcone hvalid)
      hcompat (fun hAB => hpath hAB)
  change Block.Preceq B
    (Protocol.get_head_with gc S.E S.hc ast.toHealing
      (ast.pool ast.s)
      ((ast.pool ast.s).filter
        (fun u => Protocol.resolved ast.T u = true)) ast.s)
  rw [hslot]
  exact hhead

#print axioms protectedBlock_preceq_actionHead_of_cone_compatible_core









/-- Named action-call resilience surface. -/
structure HonestProposalActionResilience
    (S : Setup V) (rho : Run V) (s : Slot) : Prop where
  action_calls : ∀ B : NamedBlock V,
    Statements.Instantiation.proposedBlockAt S rho s = some B ->
    ∀ {q : Slot}, s <= q ->
    Protocol.support_cutoff S.E q <= rho.horizon ->
    ∀ {v : V}, v ∈ rho.honest ->
    ∀ {r : Round}, S.a r = Protocol.support_cutoff S.E q ->
    Block.Preceq B.erase (Internal.actionHeadAt S rho v r)



structure HonestProposalReorgResilience
    (S : Setup V) (rho : Run V) (s : Slot) : Prop
    extends HonestProposalProposalVoteResilience S rho s,
      HonestProposalActionResilience S rho s

#print axioms actionStoreAt_pool
#print axioms actionStoreAt_timestamp_block
#print axioms actionStoreAt_T
#print axioms actionStoreAt_slot_of_action_eq_cutoff
#print axioms HonestProposalActionResilience
#print axioms HonestProposalReorgResilience

end Protocol
end DecoupledConsensusModel

end
