module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.GSTZeroActionHead

@[expose] public section

/-!
# Core support and capture for the actual round-action head

The raw/resolved action pair follows from timely honest votes and core
execution. Candidate paths use local reachability, not global history.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakAction

open Internal Execution Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem pool_no_honest_equivocation_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (w : V) (n : Nat) (k : Slot) {x : V} (hx : x ∈ rho.honest) :
    Protocol.equivocates ((NamedRun.stateBefore S rho n w).st.pool k) x = false := by
  have hps := Protocol.poolStamps_stateBefore
    S adm.toNamedScheduleWellFormed w n
  rw [Protocol.equivocates, decide_eq_false_iff_not, Nat.not_le]
  refine Nat.lt_succ_of_le (Finset.card_le_one.mpr ?_)
  intro u₁ hu₁ u₂ hu₂
  simp only [Protocol.votes_by, Finset.mem_filter,
    Protocol.NamedStore.pool, Protocol.Store.pool, List.mem_toFinset] at hu₁ hu₂
  have hval₁ : u₁.val_index ∈ rho.honest := by
    rw [hu₁.2]
    exact hx
  have hval₂ : u₂.val_index ∈ rho.honest := by
    rw [hu₂.2]
    exact hx
  have hemits : ∀ {u : GoldfishVote V},
      u ∈ (NamedRun.stateBefore S rho n w).st.gf_votes k →
        u.val_index ∈ rho.honest →
        ∃ t, NamedRun.emits S rho u.val_index (Object.gfVote u) t := by
    intro u hu hval
    obtain ⟨j, e, hj, he, hproc⟩ :=
      Protocol.processes_gfVote_of_mem_pool S rho w n k u hu
    rcases hproc with hbare | ⟨B, hprocB, hmem⟩
    · obtain ⟨t, -, hem⟩ := adm.toNamedUnforgeable.unforgeable w
        (Object.gfVote u) e.time hbare u.val_index hval rfl
      exact ⟨t, hem⟩
    · obtain ⟨t, -, hem⟩ := adm.toNamedUnforgeable.carried_gf w B e.time
        hprocB u hmem hval
      exact ⟨t, hem⟩
  obtain ⟨t₁, he₁⟩ := hemits hu₁.1 hval₁
  obtain ⟨t₂, he₂⟩ := hemits hu₂.1 hval₂
  have he₁' : NamedRun.emits S rho x (Object.gfVote u₁) t₁ := by
    simpa only [hu₁.2] using he₁
  have he₂' : NamedRun.emits S rho x (Object.gfVote u₂) t₂ := by
    simpa only [hu₂.2] using he₂
  exact Proofs.Optimistic.emits_gfVote_unique S adm.toNamedScheduleWellFormed he₁' he₂'
    (by rw [hps.slot k u₁ hu₁.1, hps.slot k u₂ hu₂.1])

theorem honest_vote_mem_actionStore_pair
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {q : Slot} (hq : 0 < q)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E q)
    (hhor : Protocol.support_cutoff S.E q <= rho.horizon)
    {x : V} (hx : x ∈ rho.honest) {u : GoldfishVote V}
    (huq : u.slot = q)
    (hemit : rho.emits S x (Object.gfVote u) (Protocol.vote_time S.E q))
    {v : V} (hv : v ∈ rho.honest) {r : Round}
    (ha : S.a r = Protocol.support_cutoff S.E q)
    {X : Block V}
    (hfind : Block.find?
      (Proofs.HealingSurface.actionStoreAt S rho v r).T u.head = some X) :
    u ∈ (Proofs.HealingSurface.actionStoreAt S rho v r).pool q ∧
      u ∈ ((Proofs.HealingSurface.actionStoreAt S rho v r).pool q).filter
        (fun z => Protocol.resolved
          (Proofs.HealingSurface.actionStoreAt S rho v r).T z = true) := by
  have hcut := Protocol.gfVote_in_cutoff_view_after_gst S adm hx hq hpost hemit huq hv
    (S.a r) (S.a r) (by rw [ha]) (by rw [ha]) hhor
  have hpre : u ∈ (rho.storeBeforeTime S v (S.a r)).pool q :=
    (Finset.mem_filter.mp hcut).1
  have hpool : u ∈ (Proofs.HealingSurface.actionStoreAt S rho v r).pool q := by
    rw [actionStoreAt_pool S rho v r q]
    exact hpre
  have hslot : X.slot ≤ u.slot :=
    Proofs.Optimistic.emitted_vote_head_slot_le_of_store_mem S adm
      hx hv hemit huq (by
        rw [← Protocol.actionStoreAt_T S rho v r]
        exact Proofs.HealingLemmas.find?_mem hfind)
      (Proofs.HealingLemmas.find?_root hfind)
  refine ⟨hpool, Finset.mem_filter.mpr ⟨hpool, ?_⟩⟩
  simp [Protocol.resolved, hfind, hslot]

/-- An honest-vote cone becomes `ConeSupport` for the exact raw/resolved pair
read by `get_fg_vote` at a round action. -/
theorem coneSupport_actionStoreAt
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {q : Slot} (hq : 0 < q)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E q)
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
      S adm.toNamedScheduleWellFormed (S.a r)
    intro x _ hx
    have hno := pool_no_honest_equivocation_core S adm v n q hx
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
    have hpair := honest_vote_mem_actionStore_pair S adm hq hpost hhor
      hxHonest rfl hXemit hv ha hfind
    have hslot : X.erase.slot ≤ q :=
      Proofs.Optimistic.emitted_vote_head_slot_le_of_store_mem S adm
        hxHonest hv hXemit rfl (by
          rw [← Protocol.actionStoreAt_T S rho v r]
          exact Proofs.HealingLemmas.find?_mem hfind)
        (Proofs.HealingLemmas.find?_root hfind)
    exact ⟨X.erase, hX, hslot, hpair.2, hfind⟩

theorem actionPath_to_ancestor_of_candidate
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} {r : Round} {B E : Block V}
    (hE : E ∈ Protocol.get_filtered_block_tree
      (Proofs.HealingSurface.actionStoreAt S rho v r).toHealing.toFG)
    (hBE : Block.Preceq B E) :
    forall C : Block V,
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
  have hF : ast.F = pre.F := rfl
  have hJ : ast.J = pre.J := rfl
  have hFJ : Block.Preceq ast.F ast.J := by
    rw [hF, hJ]
    exact hFJpre
  intro C hAC _ hCB
  have hET : E ∈ ast.T := Proofs.Records.get_filtered_block_tree_subset _ hE
  have hETpre : E ∈ pre.T := by
    rw [← actionStoreAt_T S rho v r]
    exact hET
  have hCTpre : C ∈ pre.T :=
    Proofs.Records.mem_of_preceq ((parentClosed_iff pre.core).mp hpc).2 C E hETpre
      (Block.preceq_trans hCB hBE)
  have hCT : C ∈ ast.T := by
    rw [actionStoreAt_T S rho v r]
    exact hCTpre
  apply Proofs.Records.mem_filtered_of_preceq
    (st := ast.toHealing.toFG) hFJ hE hCT
      (Block.preceq_trans hCB hBE)
  exact Block.preceq_trans
    (Proofs.HealingSurface.fg_root_preceq_get_sg_root_with_frame
      ast.cache S.E S.hc ast.toHealing
      (S.hc.round_of ast.s)) hAC

theorem protectedBlock_preceq_actionHead_of_cone_compatible
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {q : Slot} {v : V} {r : Round}
    (ha : S.a r = Protocol.support_cutoff S.E q)
    {B : Block V}
    (hcone :
      let ast := Proofs.HealingSurface.actionStoreAt S rho v r
      let raw := ast.pool q
      let support := raw.filter (fun u => Protocol.resolved ast.T u = true)
      Proofs.Optimistic.ConeSupport S.E ast.T raw support raw q rho.honest
        (fun X => Block.Preceq B X))
    (hcompat : Block.compatible
      (Protocol.get_sg_root_with
        (NamedProfile.gradeContract
          (Proofs.HealingSurface.actionStoreAt S rho v r).cache)
        S.E S.hc
        (Proofs.HealingSurface.actionStoreAt S rho v r).toHealing
        (S.hc.round_of
          (Proofs.HealingSurface.actionStoreAt S rho v r).s)) B = true)
    (hpath : Block.Preceq
        (Protocol.get_sg_root_with
          (NamedProfile.gradeContract
            (Proofs.HealingSurface.actionStoreAt S rho v r).cache)
          S.E S.hc
          (Proofs.HealingSurface.actionStoreAt S rho v r).toHealing
          (S.hc.round_of
            (Proofs.HealingSurface.actionStoreAt S rho v r).s)) B ->
      forall C : Block V,
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
    S adm.toNamedScheduleWellFormed v (S.a r) q
  have hvalid : Protocol.VoteSetValid S.E q raw := by
    simpa only [ast, raw, actionStoreAt_pool S rho v r q] using hvalid0
  have hhead : Block.Preceq B
      (Protocol.get_head_with gc S.E S.hc ast.toHealing raw support q) := by
    unfold Protocol.get_head_with
    rw [Proofs.Optimistic.get_head_in_tree_split_with]
    have hcompat' : Block.compatible
        (Protocol.get_sg_root_with gc S.E S.hc ast.toHealing
          (S.hc.round_of ast.s)) B = true := by
      simpa only [ast, gc] using hcompat
    have hpath' : Block.Preceq
        (Protocol.get_sg_root_with gc S.E S.hc ast.toHealing
          (S.hc.round_of ast.s)) B →
        ∀ C : Block V,
          Block.Preceq
              (Protocol.get_sg_root_with gc S.E S.hc ast.toHealing
                (S.hc.round_of ast.s)) C →
          C ≠ Protocol.get_sg_root_with gc S.E S.hc ast.toHealing
            (S.hc.round_of ast.s) →
          Block.Preceq C B →
          C ∈ Protocol.get_filtered_block_tree ast.toHealing.toFG := by
      simpa only [ast, gc] using hpath
    exact goldfish_fork_choice_captures_supporter_majority
      S.E ast.σ ast.h_max ast.T
        (Protocol.get_filtered_block_tree ast.toHealing.toFG) ast.s
        raw support q (Proofs.Optimistic.ConeSupport.sub hcone)
        (supporterMajority_of_cone S.E hcone hvalid) hcompat' hpath'
  change Block.Preceq B
    (Protocol.get_head_with gc S.E S.hc ast.toHealing
      (ast.pool ast.s)
      ((ast.pool ast.s).filter (fun u => Protocol.resolved ast.T u = true)) ast.s)
  rw [hslot]
  exact hhead


end WeakAction
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
