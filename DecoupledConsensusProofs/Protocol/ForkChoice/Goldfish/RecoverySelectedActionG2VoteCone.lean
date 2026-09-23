module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.RecoveryVoteCone
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryG1AfterCutoffReflection
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeDelivery
public import DecoupledConsensusProofs.Protocol.Grades.Q26
public import DecoupledConsensusProofs.Protocol.Grades.PostOutage
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Handlers.ConfirmationMembership
public import DecoupledConsensusProofs.Protocol.Handlers.StoreRoots

@[expose] public section

/-!
# Honest vote cone from a selected action G2

The named vote-duty head route is blocked at the prepared-read boundary. The
old declarations remain absent because they have live consumers.
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
open DecoupledConsensusModel.Proofs.NamedOutageClosure

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The named vote cone -/

/- The prepared head is a named run block. This local producer keeps the
   witness and the emission in the same prepared-read vocabulary. -/
private theorem preparedVoteHead_runBlock_and_emits
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hs : 0 < s)
    (hhor : Protocol.vote_time S.E s ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) (hcommittee : w ∈ S.E.committee s) :
    ∃ C : NamedBlock V,
      C.erase = voterHeadAt S rho w s ∧
      NamedRun.blockInRun S rho C ∧
      NamedRun.emits S rho w (.gfVote ⟨w, s, C.erase.root⟩)
        (Protocol.vote_time S.E s) := by
  let t := Protocol.vote_time S.E s
  let pre := NamedRun.stateBeforeTime S rho t w
  let n := NamedActionReads.confirmationReadFrom S pre t
  let gc := NamedProfile.gradeContract n.cache
  let tree := Protocol.voter_filtered_block_tree S.E n.st.core n.st.core.s
  let head := voterHeadAt S rho w s
  have hslot : n.st.core.s = s := by
    exact Proofs.Optimistic.voteDutyRead_slot S rho w s
  have hcommittee' : (S.node w).val_index ∈ S.E.committee n.st.core.s := by
    rw [S.node_val_index, hslot]
    exact hcommittee
  have hinvPre : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg pre.st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t w).1
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg n.st := by
    exact Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg pre.st t hinvPre
  have hroot : Protocol.get_fg_root n.st.core.toHealing.toFG ∈ n.st.core.T :=
    Proofs.NamedStoreRoots.fg_root_mem n.st (hinv.1.2)
  have htree : tree ⊆ n.st.core.T := by
    dsimp only [tree]
    rw [← Proofs.Optimistic.voter_candidate_tree_eq_protocol_voter_filtered_block_tree]
    intro C hC
    simp only [Proofs.Optimistic.voter_candidate_tree,
      Protocol.get_filtered_block_tree_from,
      Protocol.viable_tree, Protocol.finalized_descendants,
      Protocol.voter_processed_block_tree, Finset.mem_filter] at hC
    exact hC.1.1.1.1
  have hanchor : Protocol.get_sg_root_with gc S.E S.hc n.st.core.toHealing
      (S.hc.round_of n.st.core.s) ∈ n.st.core.T := by
    exact Proofs.NamedConfirmationMembership.runtime_anchor_mem n.cache
      S.E S.hc n.st.core.toHealing (S.hc.round_of n.st.core.s) hroot
  have hhead : head ∈ n.st.core.T := by
    dsimp only [head]
    rw [voterHeadAt_eq_get_head_with_anchor]
    rw [Proofs.Optimistic.get_head_in_tree_split_with]
    exact Proofs.Records.ghost_mem_of _ _ hanchor htree
  have hheadPre : head ∈ pre.st.core.T := by
    exact hhead
  obtain ⟨C, hCerase, hCrun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hw t hheadPre
  have hu : (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc
      (S.node w) n.st).2 =
      some ⟨(S.node w).val_index, n.st.core.s, head.root⟩ := by
    simp only [Protocol.NamedDuties.goldfish_vote_with,
      Protocol.goldfish_vote_with]
    rw [if_pos hcommittee']
    rfl
  have ho : Object.gfVote ⟨(S.node w).val_index, n.st.core.s, head.root⟩ ∈
      (on_tick_emit S w pre t).2 := by
    exact Proofs.Optimistic.on_tick_emit_vote_mem S w pre s hs hu
  have hemit := Proofs.Optimistic.emits_of_on_tick_emit S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hw
    (Proofs.Optimistic.publicTime_vote_time S s)
    (Proofs.Optimistic.vote_time_nonneg S.E s) hhor ho
  refine ⟨C, ?_, hCrun, ?_⟩
  · simpa only [head] using hCerase
  · simpa only [hCerase, S.node_val_index, hslot] using hemit

theorem honestVotesCone_of_selectedActionG2_of_readDisposition
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (hr : 0 < r) (ready : GradeRoundReady S rho r)
    {u : V} (hu : u ∈ rho.honest) {Q : Block V}
    (hsource : Protocol.grade2_block_with
      (NamedProfile.gradeContract (actionDutyRead S rho u r).cache)
      S.E S.hc (actionDutyRead S rho u r).st.core.toHealing r = some Q)
    {s : Slot} (hs : 0 < s)
    (hround : S.hc.round_of s = r)
    (hread : domain S.E S.hc r .g1 < Protocol.vote_time S.E s)
    (hta : Protocol.vote_time S.E s ≤ S.a r)
    (hhor : Protocol.vote_time S.E s ≤ rho.horizon)
    (htransport : ∀ w ∈ rho.honest, w ∈ S.E.committee s →
      Q ∈ filteredTree (readAt S rho (domain S.E S.hc r .g1) w) ∧
      storeGrade S.E S.hc
        (readAt S rho (domain S.E S.hc r .g1) w).st r .g1 Q = true ∧
      Q ∈ filteredTree (readAt S rho (Protocol.vote_time S.E s) w))
    (hvoteDisposition : ∀ w ∈ rho.honest, w ∈ S.E.committee s →
      Block.Preceq Q (Protocol.get_fg_root
        (voteDutyRead S rho w s).st.core.toHealing.toFG) ∨
      Q ∈ Protocol.get_filtered_block_tree
        (voteDutyRead S rho w s).st.core.toHealing.toFG) :
    NamedHonestVotesCone S rho s (fun X => Block.Preceq Q X) := by
  intro w hw hcommittee
  have hQX : Block.Preceq Q (voterHeadAt S rho w s) := by
    rcases htransport w hw hcommittee with ⟨hdom, hgrade, hreadMem⟩
    rcases hvoteDisposition w hw hcommittee with hroot | hactive
    · let n := voteDutyRead S rho w s
      have hfg : Block.Preceq
          (Protocol.get_fg_root n.st.core.toHealing.toFG)
          (Protocol.get_sg_root_with (NamedProfile.gradeContract n.cache)
            S.E S.hc n.st.core.toHealing (S.hc.round_of n.st.core.s)) := by
        simpa only [n] using
          fg_root_preceq_get_sg_root_with_frame n.cache S.E S.hc
            n.st.core.toHealing (S.hc.round_of n.st.core.s)
      have hanchor : Block.Preceq Q (voterAnchorAt S rho w s) := by
        change Block.Preceq Q
          (Protocol.get_sg_root_with (NamedProfile.gradeContract n.cache)
            S.E S.hc n.st.core.toHealing (S.hc.round_of n.st.core.s))
        exact Block.preceq_trans hroot hfg
      exact preceq_voteDutyHead_of_preceq_voteDutyAnchor S rho w s hanchor
    · exact selectedActionG2_preceq_sameRoundVoteDutyHead_of_activeAtVote
        S adm.toNamedAdmissibleCore hr hu hsource hround hw hread hta
        (le_trans (le_of_lt hread) hhor) hdom hgrade hreadMem hactive
  obtain ⟨C, hCerase, hCrun, hemit⟩ :=
    preparedVoteHead_runBlock_and_emits S adm hs hhor hw hcommittee
  have hheadC : Block.Preceq (voterHeadAt S rho w s) C.erase := by
    rw [hCerase]
    exact Block.preceq_self _
  exact ⟨C, Block.preceq_trans hQX hheadC, hCrun, hemit⟩


#print axioms honestVotesCone_of_selectedActionG2_of_readDisposition

/-! ## Prepared root arm -/



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
