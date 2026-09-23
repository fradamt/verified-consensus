module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryHandoffCore

@[expose] public section

/-!
# Next-vote adoption from an exact frozen candidate read

An actual vote-duty read supplies the endpoint's exact frozen voter-candidate
membership. This includes the selected FG-root ordering and viability
recomputed inside the frozen processed-block domain. The healing-anchor floor
is the one separate target-local premise.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The exact frozen candidate and prepared anchor supply next-vote adoption.
The vote-duty output stays on the prepared read used by the named runtime. -/
theorem nextVoteAdoption_of_frozenCandidateAtRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest)
    {s : Slot} {D : Block V}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest)
    (hcandidate : D ∈ Proofs.Optimistic.voter_candidate_tree S.E
      (NamedActionReads.confirmationReadFrom S
        (Run.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w)
        (Protocol.vote_time S.E (s + 1))).st.core.toHealing)
    (hanchor : Block.Preceq
      (Protocol.get_sg_root_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S
            (Run.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w)
            (Protocol.vote_time S.E (s + 1))).cache)
        S.E S.hc
        (NamedActionReads.confirmationReadFrom S
          (Run.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w)
          (Protocol.vote_time S.E (s + 1))).st.core.toHealing
        (S.hc.round_of
          (NamedActionReads.confirmationReadFrom S
            (Run.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w)
            (Protocol.vote_time S.E (s + 1))).st.core.s)) D) :
    NamedNextVoteAdoption S rho
      (Proofs.Optimistic.confStore S rho v s) s D w := by
  have hdata := hcandidate
  simp only [Proofs.Optimistic.voter_candidate_tree,
    Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq] at hdata
  have hroot : Block.Preceq
      (Protocol.get_fg_root
        (NamedActionReads.confirmationReadFrom S
          (Run.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w)
          (Protocol.vote_time S.E (s + 1))).st.core.toHealing.toFG) D :=
    hdata.2
  exact nextVoteAdoption_of_recovery_after_gst
    S adm hv hw hpost hhor hroot hanchor hcandidate



/-- **The same, with the anchor premise at COMPATIBILITY strength**
( gs, deliverable 4).

Additive; `nextVoteAdoption_of_frozenCandidateAtRead` and its consumers are
untouched. The record's `anchor` field is compatibility and the constructor
reads the premise only there, so this is the form the live general-slot
producer `nextVoteDutyAnchor_compatible_of_honestPreviousHead_after_SG_healing_named`
(`SGLifetimeNamedRun.lean:984`) can actually feed, and the form earlier's
`nextVoteAdoption_of_commonHead_after_SG_healing` builds the record from. -/
theorem nextVoteAdoption_of_frozenCandidateAtRead_compatibleAnchor
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest)
    {s : Slot} {D : Block V}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest)
    (hcandidate : D ∈ Proofs.Optimistic.voter_candidate_tree S.E
      (NamedActionReads.confirmationReadFrom S
        (Run.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w)
        (Protocol.vote_time S.E (s + 1))).st.core.toHealing)
    (hanchor : Block.compatible
      (Protocol.get_sg_root_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S
            (Run.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w)
            (Protocol.vote_time S.E (s + 1))).cache)
        S.E S.hc
        (NamedActionReads.confirmationReadFrom S
          (Run.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w)
          (Protocol.vote_time S.E (s + 1))).st.core.toHealing
        (S.hc.round_of
          (NamedActionReads.confirmationReadFrom S
            (Run.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w)
            (Protocol.vote_time S.E (s + 1))).st.core.s)) D = true) :
    NamedNextVoteAdoption S rho
      (Proofs.Optimistic.confStore S rho v s) s D w := by
  have hdata := hcandidate
  simp only [Proofs.Optimistic.voter_candidate_tree,
    Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq] at hdata
  have hroot : Block.Preceq
      (Protocol.get_fg_root
        (NamedActionReads.confirmationReadFrom S
          (Run.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w)
          (Protocol.vote_time S.E (s + 1))).st.core.toHealing.toFG) D :=
    hdata.2
  exact nextVoteAdoption_of_recovery_after_gst_compatibleAnchor
    S adm hv hw hpost hhor hroot hanchor hcandidate

#print axioms nextVoteAdoption_of_frozenCandidateAtRead_compatibleAnchor



#print axioms nextVoteAdoption_of_frozenCandidateAtRead

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
