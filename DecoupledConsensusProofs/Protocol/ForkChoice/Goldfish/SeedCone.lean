module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.GoldfishCone
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightProgressSeedRegime
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGTargetCanonicality
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryFinalityFilterRetainedVoteConeSeed
public import DecoupledConsensusProofs.Protocol.Schedule.WeakProcessedTree

@[expose] public section

/-!
# Gate-off seed cone

This module supplies the finality-filter, candidate, root, and path fields for
the regime-free Goldfish cone induction. A genuine confirmation is relayed to
each later frozen vote view. Exact gate-off frontier reads then keep the
confirmed block and its path in the filtered tree.

Gate-off does not orient a fresh SG anchor. `SeedConeAnchorAlignmentAt` is the
single remaining interface. It states only the anchor facts that the pure
Goldfish induction needs.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.PhaseGrades
open Internal.HealingSurface
open Internal.NamedRecoveryRead
open Protocol
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Exact gate-off frontier data at the vote and confirmation reads used by a
Goldfish slot interval. -/
structure GateOffSeedConeWindowAt
    (S : Setup V) (rho : Run V) (M : Height) (lo hi : Slot) : Prop where
  voteFrontier : ∀ d : Slot, lo ≤ d → d ≤ hi + 1 → ∀ w ∈ rho.honest,
    (Proofs.Optimistic.voteDutyStore S rho w d).h_max = M
  voteGateOff : ∀ d : Slot, lo ≤ d → d ≤ hi + 1 → ∀ w ∈ rho.honest,
    (Proofs.Optimistic.voteDutyStore S rho w d).h_j + 2 ≤ M
  confirmationFrontier : ∀ s : Slot, lo ≤ s → s ≤ hi → ∀ w ∈ rho.honest,
    (Proofs.Optimistic.confStore S rho w s).h_max = M
  confirmationGateOff : ∀ s : Slot, lo ≤ s → s ≤ hi → ∀ w ∈ rho.honest,
    (Proofs.Optimistic.confStore S rho w s).h_j + 2 ≤ M

/-- A gate-off window shrinks on the left. -/
theorem GateOffSeedConeWindowAt.mono_lo
    {S : Setup V} {rho : Run V} {M : Height} {lo lo' hi : Slot}
    (h : GateOffSeedConeWindowAt S rho M lo hi) (hlo : lo ≤ lo') :
    GateOffSeedConeWindowAt S rho M lo' hi where
  voteFrontier := fun d hdlo hdhi w hw => h.voteFrontier d (hlo.trans hdlo) hdhi w hw
  voteGateOff := fun d hdlo hdhi w hw => h.voteGateOff d (hlo.trans hdlo) hdhi w hw
  confirmationFrontier := fun s hslo hshi w hw =>
    h.confirmationFrontier s (hlo.trans hslo) hshi w hw
  confirmationGateOff := fun s hslo hshi w hw =>
    h.confirmationGateOff s (hlo.trans hslo) hshi w hw







/-! ## Named candidate and confirmation-store helpers -/





end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

#print axioms GateOffSeedConeWindowAt.mono_lo

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
