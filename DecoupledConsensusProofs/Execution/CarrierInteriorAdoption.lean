module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedCeiling
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGOpeningFrozenSuffix
public import DecoupledConsensusProofs.Protocol.Schedule.SlotInduction

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Interior carrier proposal adoption

The opening and the next two honest proposers are slots of one carrier round.
This module isolates the proposal-walk facts that turn an interior proposal
into an honest vote cone, then feeds that cone to the next honest proposer.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Protocol Proofs.HealingLemmas Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]



theorem carrierInterior_scoreEq_of_scoreBridge
    (S : Setup V) {rho : Run V} {s : Slot} {v : V} {P : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P)
    (hbridge : NamedProposalCandidateScoreBridge S rho s v P) : ∀ C,
    C ∈ namedWalkSourceTree S rho s →
    C ∈ namedWalkTargetTree S rho s v P →
    namedWalkTargetScore S rho s v C = namedWalkSourceScore S rho s C := by
  intro C hCsource hCtarget
  have hCcandidate : C ∈ voterCandidateTreeAt S rho v s := by
    simpa only [namedWalkTargetTree] using Finset.mem_of_mem_erase hCtarget
  have hCfiltered : C ∈ Protocol.get_filtered_block_tree
      (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.toFG :=
    frozenVoterCandidateTree_subset_filtered S.E _ hCcandidate
  have hext := hbridge C hCsource hCfiltered
  have hscore := hext.goldfish_score_eq S.E (s - 1)
  have hsourceCore : (Internal.NamedRecoveryRead.proposalDutyRead S rho s).st.core =
      Protocol.proposerDutyStore S rho s := rfl
  have hproposerCore : (proposerReadAt S rho s).st.core =
      Protocol.proposerDutyStore S rho s := rfl
  have htargetCore : (Internal.NamedRecoveryRead.voteDutyRead S rho v s).st.core =
      Proofs.Optimistic.voteDutyStore S rho v s := rfl
  have hsourceSlot : (Protocol.proposerDutyStore S rho s).s = s := by
    simp only [Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
      Proofs.Optimistic.slotOf_proposal_time]
  have htargetSlot : (Proofs.Optimistic.voteDutyStore S rho v s).s = s :=
    Proofs.Optimistic.voteDutyStore_slot S rho v s
  symm
  unfold namedWalkSourceScore namedWalkTargetScore
  rw [hsourceCore, htargetCore, hsourceSlot, htargetSlot]
  simpa only [Proofs.NamedWire.erase_goldfish_votes, Proofs.NamedWire.erase_goldfish_support,
    Protocol.proposedBlock_gf_votes S rho s hP,
    Protocol.proposedBlock_gf_support_votes S rho s hP,
    proposalInputAt, Protocol.proposal_input_with, Protocol.with_proposal_input,
    id_eq, hsourceCore, hproposerCore, hsourceSlot,
    Protocol.Store.toHealing] using hscore









#print axioms carrierInterior_scoreEq_of_scoreBridge

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
