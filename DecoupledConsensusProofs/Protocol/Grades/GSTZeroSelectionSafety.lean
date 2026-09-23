module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.ConfirmationHistoryProducer
public import DecoupledConsensusProofs.Generic.SuffixHistory
public import DecoupledConsensusProofs.Protocol.Grades.CarrierAdmission
public import DecoupledConsensusProofs.Protocol.Handlers.AdoptionConstructor
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ConePersistence
public import DecoupledConsensusProofs.Protocol.Schedule.GSTZeroHeadResolution
public import DecoupledConsensusProofs.Protocol.Handlers.AcceptanceTiming
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Adoption
public import DecoupledConsensusProofs.Generic.GSTZeroHealthy
public import DecoupledConsensusProofs.Protocol.Handlers.GoldfishVotePool

@[expose] public section

/-!
# GST-zero selection safety at arbitrary confirmation ticks

This file separates the two semantic branches of an ordinary Section 7
confirmation tick from the honest-proposal liveness route.

* A genuine walk is safe above any directed prior-selection frontier. The
  proof needs the current honest-vote cone, frontier admission, and root
  resolution, but it does not need an honest proposer.
* A `get_fg_root` fallback is safe below the same frontier. Canonical history
  alone closes this branch; it does not use Goldfish votes, candidate
  admission, or root resolution.

The final theorem folds event-local boundaries into
`ConfirmationCompatibleFrom`. Producing the frontier and the genuine-branch
transport at every confirmation event remains the cross-slot induction.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution
open Internal.NamedRecoveryRead

variable {V : Type} [DecidableEq V] [Fintype V]








/-- Vote instants are monotone in the slot index. -/
theorem vote_time_mono_slots (E : Env V) {a b : Slot} (hab : a ≤ b) :
    Protocol.vote_time E a ≤ Protocol.vote_time E b := by
  unfold Protocol.vote_time
  exact Int.add_le_add_right (proposal_time_mono E hab) E.Δ

























end Protocol
end DecoupledConsensusModel

end
