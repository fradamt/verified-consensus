module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Claims
public import DecoupledConsensusInternal.Legacy.Definitions.Confirmation
public import DecoupledConsensusInternal.Legacy.Definitions.FinalitySafety
public import DecoupledConsensusInternal.Legacy.Definitions.NamedStableChainOutageInternal
public import DecoupledConsensusInternal.Legacy.Definitions.SafetyRegimes
public import DecoupledConsensusInternal.Legacy.Safety

@[expose] public section

/-! # Internal proof-side results

These fields preserve the protocol-internal reads that are not part of the
standard public bundle. They are printed by the review scripts but are not
manual review obligations.
-/

namespace DecoupledConsensusModel
namespace Statements

open Internal Execution

variable {V : Type} [DecidableEq V] [Fintype V]

structure Internal (S : Setup V) : Prop where
  /-- Recorded-confirmation compatibility and monotonicity. -/
  confirmationRecordSafety :
    ∀ rho, WeakGenesis S rho →
      ConfirmationCompatibleFrom S rho 0 ∧ ConfirmationMonotoneFrom S rho 0
  /-- Stable-record canonicity, including the finality compatibility read. -/
  stableRecordCanonical :
    ∀ rho, WeakGenesis S rho → StableRecordCanonicalFrom S rho 0
  /-- Exact confirmation-walk result and the equality clause for proposals. -/
  exactConfirmation : ∀ rho, WeakGenesis S rho → ProposalConfirmedFrom S rho 0
  /-- The refreshed handover seed. -/
  handoverSeed : BoundedSafetyRecovery S
  /-- Phase-shift internal reads. -/
  phaseShiftInternals : BoundedSafetyRecovery S
  /-- GST-zero internal reads. -/
  gstZeroInternals : ∀ rho, WeakGenesis S rho → GSTZeroGuarantees S rho
  /-- Whole-run chains and pure finality agreement. -/
  finalityChains :
    (∀ rho, FinalityExecution S rho → WholeRunAccountableFinalitySafety S rho) ∧
      PureFinalityAgreement S
  /-- The time-form stable-output outage persistence result used internally. -/
  outageInternals : NamedStableChainOutage.StableChainOutageResilience S
  /-- Vote-source safety after recovery. -/
  voteSourceSafety : VoteSafetyAfterRecovery S

end Statements
end DecoupledConsensusModel

end
