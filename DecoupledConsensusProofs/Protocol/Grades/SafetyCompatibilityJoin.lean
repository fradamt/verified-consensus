module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGCompatibleHistory
public import DecoupledConsensusProofs.Protocol.Grades.RelativeOneChain
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryHandoffCore
public import DecoupledConsensusProofs.Protocol.Schedule.WeakGoldfishCone
public import DecoupledConsensusProofs.Execution.RecoveryActionLiveSourceSplit
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionConfirmationCore
public import DecoupledConsensusProofs.Protocol.ChainState.FGRootWitness

@[expose] public section

/-!
# Compatibility from earlier confirmation safety

An action before the slot-(s+1) vote evaluates an opening-slot confirmation
strictly before slot s. Its genuine branch can therefore use the earlier
confirmation induction, even if the action itself follows the slot-s vote.
This is valid for R=2. Exact certificate provenance makes an action root
inherit from a strictly earlier action witness. A joint round induction then
derives the SG, FG-root, and exact FG-witness source bounds together.

The finite SG bootstrap, relevant old FG sources, earlier confirmation
safety, and local window majority remain inputs. No safety of later SG
emissions, action roots, current FG witnesses, or live-confirmed fields is
assumed by the final join.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Protocol
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]



/-- Every preceding-round action occurs before the later vote read. This
time-only part of earlier's route is independent of the grade rewrite. -/
theorem action_before_vote_of_round_lt
    (S : Setup V) {r : Round} {d : Slot} (hr : r < S.hc.round_of d) :
    S.a r < Protocol.vote_time S.E d := by
  have hfirst := Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt S hr
  have hslots : S.hc.opening_slot (S.hc.round_of d) ≤ d :=
    Nat.div_mul_le_self d S.hc.R
  have hproposal := hfirst.trans (proposal_time_mono S.E hslots)
  exact (Int.lt_add_of_pos_right _ S.E.Δ_pos).trans_le
    (hproposal.trans (le_of_lt (proposal_time_lt_vote_time S.E d)))

#print axioms action_before_vote_of_round_lt

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
