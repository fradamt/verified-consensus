module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.FrontierWitnessRelay
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalVoteDuty
public import DecoupledConsensusProofs.Protocol.Schedule.GSTZeroReorgResilience
public import DecoupledConsensusProofs.Protocol.ValidatorClient.Schedule

@[expose] public section

/-!
# Recovery-filter source settlement at Section 7 reads

The recovery filter package needs one full network delay between the honest
height-pair source and the reader. This module supplies that timing fact at
each actual Section 7 `get_head` read family.

An attestation emission is not an arbitrary real-valued instant. It occurs at
the round action `a_r`. The Section 7 schedule has no later read of any of the
four relevant kinds less than one delay after an earlier action. Therefore,
strict source-before-read ordering is enough at proposal, vote, confirmation,
and later round-action reads.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Schedule arithmetic -/

/-- An action before a vote read is settled by that read. -/
theorem action_add_delta_le_vote_of_lt
    (S : Setup V) {r : Round} {s : Slot}
    (hlt : S.a r < Protocol.vote_time S.E s) :
    S.a r + S.E.Δ ≤ Protocol.vote_time S.E s := by
  have hproposal : S.a r < Protocol.proposal_time S.E s :=
    Protocol.action_time_lt_proposal_of_lt_vote S hlt
  exact le_trans
    (Protocol.action_add_delta_le_proposal_of_lt S hproposal)
    (le_of_lt (Protocol.proposal_time_lt_vote_time S.E s))



/-! ## Exact `sourceSettled` field producers -/





end HealingSurface
end Proofs
end DecoupledConsensusModel

end
