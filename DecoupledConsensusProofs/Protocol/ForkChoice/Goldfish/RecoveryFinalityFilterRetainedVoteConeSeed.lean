module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryFinalityFilterRetainedAdoption
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.AdoptionRun

@[expose] public section

/-!
# Honest-vote cone seed from frozen vote-duty reads

A genuine source confirmation seeds the next honest-vote cone once every
honest committee target retains the block in its exact frozen voter candidate
tree and the block descends from its healing anchor.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

def frozenVoteRead (S : Setup V) (rho : Run V) (s : Slot) (w : V) :
    NamedNodeState V :=
  NamedActionReads.confirmationReadFrom S
    (Run.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w)
    (Protocol.vote_time S.E (s + 1))

/-- Exact frozen vote-duty candidates and target-local healing-anchor floors
transport a genuine confirmation into the next honest-vote cone. -/
theorem honestVotesCone_succ_of_genuineConfirmation_of_frozenVoteReads
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest)
    {s : Slot} {B : Block V}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {contract : Protocol.GradeContract V}
    (hgenuine : GenuineConfirmation (contract := contract) S.E S.hc
      (Proofs.Optimistic.confStore S rho v s) s B)
    (hcandidate : ∀ w ∈ rho.honest,
      w ∈ S.E.committee (s + 1) →
      B ∈ Proofs.Optimistic.voter_candidate_tree S.E
        (frozenVoteRead S rho s w).st.core.toHealing)
    (hanchor : ∀ w ∈ rho.honest,
      w ∈ S.E.committee (s + 1) →
      Block.Preceq
        (Protocol.get_sg_root_with
          (NamedProfile.gradeContract (frozenVoteRead S rho s w).cache)
          S.E S.hc (frozenVoteRead S rho s w).st.core.toHealing
          (S.hc.round_of (frozenVoteRead S rho s w).st.core.s)) B) :
    Proofs.HealingSurface.NamedHonestVotesCone S rho (s + 1)
      (fun X => Block.Preceq B X) := by
  intro w hw hwcommittee
  let read := frozenVoteRead S rho s w
  have hslot : read.st.core.s = s + 1 := by
    simpa only [read, frozenVoteRead, NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, Protocol.NamedStore.setClock] using
      Proofs.Optimistic.slotOf_vote_time S.E (s + 1)
  have hprev : read.st.core.s - 1 = s := by
    rw [hslot]
    have key : ∀ a : Nat, a + 1 - 1 = a := by
      intro a
      omega
    exact key s
  have hcommittee : (S.node w).val_index ∈ S.E.committee read.st.core.s := by
    rw [S.node_val_index, hslot]
    exact hwcommittee
  have hdata := hcandidate w hw hwcommittee
  simp only [Proofs.Optimistic.voter_candidate_tree,
    Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq] at hdata
  have hroot : Block.Preceq
      (Protocol.get_fg_root read.st.core.toHealing.toFG) B := by
    simpa only [read] using hdata.2
  have hd := nextVoteAdoption_of_recovery_after_gst
    S adm hv hw hpost hhor hroot
      (hanchor w hw hwcommittee) (hcandidate w hw hwcommittee)
  let tree := Protocol.voter_filtered_block_tree S.E read.st.core read.st.core.s
  let votes := Protocol.voter_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s
  let support := Protocol.voter_support_view S.E
    read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s
  let head := Protocol.get_head_in_tree_with
    (NamedProfile.gradeContract read.cache) S.E S.hc read.st.core
    tree votes support (read.st.core.s - 1)
  have hhead : Block.Preceq B head := by
    change Block.Preceq B (Protocol.get_head_in_tree_with_layer
      (NamedProfile.gradeContract read.cache) S.E S.hc read.st.core.toHealing
      tree votes support (read.st.core.s - 1))
    rw [hprev, Proofs.Optimistic.get_head_in_tree_split_with]
    exact Protocol.goldfish_fork_choice_captures_of_confirmation
      S.E read.st.core.σ read.st.core.h_max
      (Proofs.Optimistic.confStore S rho v s).T read.st.core.T tree read.st.core.s
      (confEarly S.E (Proofs.Optimistic.confStore S rho v s) s)
      (confLate S.E (Proofs.Optimistic.confStore S rho v s) s)
      (confVotes S.E (Proofs.Optimistic.confStore S rho v s) s) votes support s
      (confNumerator S.E (Proofs.Optimistic.confStore S rho v s) s)
      hd.transport hgenuine.eligible hd.support_subset hd.anchor hd.path
  obtain ⟨C, hChead, hCrun⟩ := hd.run
  have hChead' : C.erase = head := by
    simpa only [head, tree, votes, support, read, frozenVoteRead] using hChead
  refine ⟨C, ?_, ?_, ?_⟩
  · rw [hChead']
    exact hhead
  · exact hCrun
  · have hout :
        (Protocol.NamedDuties.goldfish_vote_with
          (NamedProfile.gradeContract read.cache) S.E S.hc (S.node w) read.st).2 =
          some ⟨(S.node w).val_index, read.st.core.s, head.root⟩ := by
      simp only [Protocol.NamedDuties.goldfish_vote_with,
        Protocol.goldfish_vote_with, hcommittee, if_true, head, tree, votes, support]
    have hem := hd.emit _ hout
    rw [← hChead'] at hem
    rw [hslot] at hem
    simpa only [S.node_val_index] using hem

#print axioms honestVotesCone_succ_of_genuineConfirmation_of_frozenVoteReads

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
