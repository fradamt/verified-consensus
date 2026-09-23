module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Liveness
public import DecoupledConsensusProofs.Execution.W4A3AvailableGrowthFold
public import DecoupledConsensusProofs.Execution.GSTZeroSafetyClosedNamed
public import DecoupledConsensusProofs.Execution.RecoveryWindowClosure

@[expose] public section

/-!
# W4 B2 — the public `availableChainGrowth` field

Assembles the public `AvailableChainGrowth` field from the A3 named
two-proposal fold (`W4.availableChainGrowthFrom_of_userProposals`,
`W4A3AvailableGrowthFoldRun.lean`), the closed GST-zero safety producer
(`Proofs.HealingSurface.gstZeroSafety`), and the closed bounded-safety-recovery
phase shift (`boundedSafetyRecovery_closed`). See the liveness audit
`the proof record` §5 B2.

earlier's route (`LivenessContractsRun.lean:67-82`, both trees) is:
GST zero via `availableChainGrowthFrom_of_gstZero`; after GST via
`availableChainGrowth_after_boundedStrongPhase`, which obtains a healed
`PhaseShiftSafety` and applies the same generic fold. The concrete selection
difference is only in the fold itself (A3); the assembly below follows
earlier's shape unchanged.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace W4

open Internal Execution Statements
variable {V : Type} [DecidableEq V] [Fintype V]


/-- The healed post-GST records gives bounded available-chain growth when the
continuation has the accepted proposer recurrence. Named twin of earlier's
`availableChainGrowthFrom_of_healed` (`WeakAvailableChainGrowthRun.lean:88-93`). -/
theorem availableChainGrowthFrom_of_healed
    (S : Setup V) {rho : Run V} {start : Slot} {P : Block V} {gap : Round}
    (hsafe : UserConfirmationAfterHealing S rho start P)
    (hrec : ProposerOpeningCarrierRecurrence S rho gap) :
    AvailableChainGrowthFrom S rho start gap :=
  availableChainGrowthFrom_of_userProposals S hsafe.latestMonotone hsafe.proposals hrec


/-- The GST-zero safety records gives bounded available-chain growth from slot
`0`. Named twin of earlier's `availableChainGrowthFrom_of_genesis`
(`WeakAvailableChainGrowthRun.lean:97-104`): widening the monotonicity floor
from `0` to `confirmation_time 0` uses `Proofs.Optimistic.confirmation_time_nonneg`. -/
theorem availableChainGrowthFrom_of_genesis
    (S : Setup V) {rho : Run V} {gap : Round}
    (hsafe : GSTZeroGuarantees S rho)
    (hrec : ProposerOpeningCarrierRecurrence S rho gap) :
    AvailableChainGrowthFrom S rho 0 gap := by
  apply availableChainGrowthFrom_of_userProposals S _ hsafe.userProposals hrec
  intro v hv t t' ht htt hhor
  apply hsafe.availableChain.2.1 v hv t t' _ htt hhor
  exact (Proofs.Optimistic.confirmation_time_nonneg S.E 0).trans ht


/-- **The public `availableChainGrowth` field.** GST zero: the closed
`GSTZeroGuarantees` records feeds A3 through `availableChainGrowthFrom_of_genesis`.
After GST: `boundedSafetyRecovery_closed` selects the round `m` and the seed
proposal once; every continuation's `PhaseShiftSafety.userConfirmation` then
feeds A3 through `availableChainGrowthFrom_of_healed`. -/
theorem availableChainGrowth (S : Setup V) : AvailableChainGrowth S where
  gstZero := by
    intro rho hgenesis gap hrec
    have hgst : GSTZeroGuarantees S rho :=
      Proofs.HealingSurface.gstZeroSafety S hgenesis.core hgenesis.committees
        hgenesis.gstZero hgenesis.windows
    exact availableChainGrowthFrom_of_genesis S hgst hrec
  afterGST := by
    intro rho rGST gap extra n hprefix
    obtain ⟨m, hnm, hmgap, hgapm, P, hP, hcont⟩ :=
      boundedSafetyRecovery_closed S rho rGST gap extra n hprefix
    refine ⟨m, hnm, hmgap, hgapm, ?_⟩
    intro rho' hweak continuationGap hrec'
    exact availableChainGrowthFrom_of_healed S (hcont rho' hweak).userConfirmation hrec'

#print axioms availableChainGrowth

end W4
end Proofs
end DecoupledConsensusModel

end
