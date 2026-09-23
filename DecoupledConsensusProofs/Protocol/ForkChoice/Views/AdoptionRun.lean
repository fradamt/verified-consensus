module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Adoption
public import DecoupledConsensusProofs.Protocol.Schedule.SlotInduction

@[expose] public section

/-! # Run seam for confirmation adoption
`Adoption.lean` proves the pure confirmation-to-voter majority transfer and the
final `get_head` capture. This module packages the remaining facts at each
honest next-slot vote duty and produces the exact `HonestVotesCone` seed used by
the existing slot induction.
The producer is deliberately abstract while the execution contract is being
repaired. In particular, `NextVoteAdoption.transport` must come from
event-indexed, causal, accepted forwarding. This module does not weaken it to
The previous time-only relay statement.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]



/-- R44c: the next-vote adoption interface over the prepared vote-duty read.

Every tree, anchor, and head in this structure is read from the exact named
vote duty input used by the runtime. The emitted-vote premise therefore uses
`Protocol.NamedDuties.goldfish_vote_with` with that read's cached contract.
Source and endpoint geometry remain erased because `AdoptionTransport` and
the public cone target use erased blocks. -/
structure NamedNextVoteAdoption (S : Setup V) (rho : Run V)
    (source : Protocol.Store V) (s : Slot) (B : Block V) (w : V) : Prop where
  transport :
    let read := NamedActionReads.confirmationReadFrom S
      (Run.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w)
      (Protocol.vote_time S.E (s + 1))
    AdoptionTransport source.T read.st.core.T
      (confVotes S.E source s) (confLate S.E source s)
      (Protocol.voter_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
      (Protocol.voter_support_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
      B
  support_subset :
    let read := NamedActionReads.confirmationReadFrom S
      (Run.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w)
      (Protocol.vote_time S.E (s + 1))
    Protocol.voter_support_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s ⊆
      Protocol.voter_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s
  anchor :
    let read := NamedActionReads.confirmationReadFrom S
      (Run.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w)
      (Protocol.vote_time S.E (s + 1))
    Block.compatible
      (Protocol.get_sg_root_with (NamedProfile.gradeContract read.cache)
        S.E S.hc read.st.core.toHealing (S.hc.round_of read.st.core.s)) B = true
  path :
    let read := NamedActionReads.confirmationReadFrom S
      (Run.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w)
      (Protocol.vote_time S.E (s + 1))
    Block.Preceq
        (Protocol.get_sg_root_with (NamedProfile.gradeContract read.cache)
          S.E S.hc read.st.core.toHealing (S.hc.round_of read.st.core.s)) B →
      ∀ C : Block V,
        Block.Preceq
            (Protocol.get_sg_root_with (NamedProfile.gradeContract read.cache)
              S.E S.hc read.st.core.toHealing (S.hc.round_of read.st.core.s)) C →
        C ≠ Protocol.get_sg_root_with (NamedProfile.gradeContract read.cache)
          S.E S.hc read.st.core.toHealing (S.hc.round_of read.st.core.s) →
        Block.Preceq C B →
        C ∈ Protocol.voter_filtered_block_tree S.E read.st.core read.st.core.s
  run :
    let read := NamedActionReads.confirmationReadFrom S
      (Run.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w)
      (Protocol.vote_time S.E (s + 1))
    ∃ C : NamedBlock V,
      C.erase = Protocol.get_head_in_tree_with_layer
        (NamedProfile.gradeContract read.cache) S.E S.hc read.st.core.toHealing
        (Protocol.voter_filtered_block_tree S.E read.st.core read.st.core.s)
        (Protocol.voter_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
        (Protocol.voter_support_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
        (read.st.core.s - 1) ∧ RunBlock S rho C
  emit : ∀ u : GoldfishVote V,
    let read := NamedActionReads.confirmationReadFrom S
      (Run.stateBeforeTime S rho (Protocol.vote_time S.E (s + 1)) w)
      (Protocol.vote_time S.E (s + 1))
    (Protocol.NamedDuties.goldfish_vote_with
      (NamedProfile.gradeContract read.cache) S.E S.hc (S.node w) read.st).2 = some u →
    rho.emits S w (Object.gfVote u) (Protocol.vote_time S.E (s + 1))


end Protocol
end DecoupledConsensusModel

end
