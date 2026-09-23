module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Assumptions.Regimes
public import DecoupledConsensusStatements.Instantiation.Deadlines
public import DecoupledConsensusInternal.Legacy.Definitions.NamedHeadReads
public import DecoupledConsensusInternal.Legacy.Definitions.NamedLivenessStatements
public import DecoupledConsensusInternal.Legacy.Definitions.NamedVoteConsumers
public import DecoupledConsensusInternal.Legacy.Definitions.StableOutput

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # The five final liveness properties
Each property states its GST-zero and arbitrary-GST regimes. The arbitrary-GST
available-chain results require only a finite strong prefix. Finality names
its closed startup and deadline formulas in both regimes.
No G2, height-progress, or recovery-invariant result is part of this contract.
Validator-client vote safety is a separate safety field of `Statements.Consensus`.
-/

namespace DecoupledConsensusModel
namespace Statements
open Internal Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Prompt confirmation of honest proposals, from genesis or after a bounded
strong prefix. Later honest-proposer recurrence is not needed. -/
structure HonestProposalConfirmation (S : Setup V) : Prop where
  gstZero : ∀ rho, WeakGenesis S rho → HonestProposalsConfirmedFrom S rho 0
  /-- The `WeakContinuation` premise has
  `covered: healingBoundaryTime S (n + gap) ≤ rho'.horizon`. -/
  afterGST : ∀ rho rGST gap extra n,
    StrongRecoveryPrefix S rho rGST gap extra n →
    ∃ m, n ≤ m ∧ m ≤ n + gap ∧ n + gap ≤ m + gap ∧
      ∀ rho', WeakContinuation S rho rho' (n + gap) →
        HonestProposalsConfirmedFrom S rho' (S.hc.opening_slot m)

/-- Strict growth of the raw user confirmation record. The confirmed getter
also contains each new block persistently. The two recurrence gaps can differ. -/
structure AvailableChainGrowth (S : Setup V) : Prop where
  gstZero : ∀ rho, WeakGenesis S rho →
    ∀ gap, ProposerOpeningCarrierRecurrence S rho gap → AvailableChainGrowthFrom S rho 0 gap
  /-- The `WeakContinuation` premise has
  `covered: healingBoundaryTime S (n + gap) ≤ rho'.horizon`. -/
  afterGST : ∀ rho rGST gap extra n,
    StrongRecoveryPrefix S rho rGST gap extra n →
    ∃ m, n ≤ m ∧ m ≤ n + gap ∧ n + gap ≤ m + gap ∧
      ∀ rho', WeakContinuation S rho rho' (n + gap) →
        ∀ continuationGap, ProposerOpeningCarrierRecurrence S rho' continuationGap →
          AvailableChainGrowthFrom S rho' (S.hc.opening_slot m) continuationGap


/-- Growth of the stable record: the user-facing liveness of the G2-root
record, in the same two regimes as `AvailableChainGrowth`. The growth deadline is
`gap + η_SG - 1` rounds: the G2 root is formed by votes
over the expiry window of `η_SG` rounds, so under an awake-window majority it can
lag the confirmation record by up to `η_SG - 1` rounds; the premises are unchanged
and the constant degenerates to `gap` at `η_SG = 1`. -/
structure StableRecordGrowth (S : Setup V) : Prop where
  gstZero : ∀ rho, WeakGenesis S rho →
    ∀ gap, ProposerOpeningCarrierRecurrence S rho gap →
      StableRecordGrowthFrom S rho 0 (gap + S.hc.η_SG - 1)
  /-- The `WeakContinuation` premise has
  `covered: healingBoundaryTime S (n + gap) ≤ rho'.horizon`. -/
  afterGST : ∀ rho rGST gap extra n,
    StrongRecoveryPrefix S rho rGST gap extra n →
    ∃ m, n ≤ m ∧ m ≤ n + gap ∧
      ∀ rho', WeakContinuation S rho rho' (n + gap) →
        ∀ continuationGap, ProposerOpeningCarrierRecurrence S rho' continuationGap →
          StableRecordGrowthFrom S rho' (S.hc.opening_slot m) (continuationGap + S.hc.η_SG - 1)

/-- Common finalized checkpoint and height bounds advance by the closed
startup and constant deadline. The current GST-zero case still includes the
startup; it does not assert progress from round zero with the subsequent
deadline alone. -/
structure FinalizedChainGrowth (S : Setup V) : Prop where
  gstZero : ∀ extra, TimeoutDelayBound S extra → ∀ gap,
    ∀ rho, StrongFinalityRun S rho gap → S.E.t_GST = 0 →
      healingBoundaryTime S (finalityStartup S gap extra) ≤ rho.horizon →
      ∃ q, q ≤ finalityStartup S gap extra ∧
        RecurringFinalityFrom S rho q (finalityDeadline S gap extra)
  /-- The explicit after-GST horizon reaches
  `healingBoundaryTime S (rGST + finalityStartup S gap extra)`. -/
  afterGST : ∀ extra, TimeoutDelayBound S extra → ∀ gap,
    ∀ rho rGST, StrongFinalityRun S rho gap → S.E.t_GST ≤ S.a rGST →
      healingBoundaryTime S (rGST + finalityStartup S gap extra) ≤ rho.horizon →
      ∃ q, rGST ≤ q ∧ q ≤ rGST + finalityStartup S gap extra ∧
        RecurringFinalityFrom S rho q (finalityDeadline S gap extra)

/-- Each honest proposal after the selected startup boundary becomes a prefix
of every honest finalized chain by its proposal-relative deadline. This
startup exclusion also remains at GST zero. Covering early genesis proposals
and reducing the closed startup are separate, unproved improvements. -/
structure HonestProposalFinalization (S : Setup V) : Prop where
  gstZero : ∀ extra, TimeoutDelayBound S extra → ∀ gap,
    ∀ rho, StrongFinalityRun S rho gap → S.E.t_GST = 0 →
      healingBoundaryTime S (finalityStartup S gap extra) ≤ rho.horizon →
      ∃ q, q ≤ finalityStartup S gap extra ∧
        HonestProposalFinalityFrom S rho q (finalityDeadline S gap extra)
  /-- The explicit after-GST horizon reaches
  `healingBoundaryTime S (rGST + finalityStartup S gap extra)`. -/
  afterGST : ∀ extra, TimeoutDelayBound S extra → ∀ gap,
    ∀ rho rGST, StrongFinalityRun S rho gap → S.E.t_GST ≤ S.a rGST →
      healingBoundaryTime S (rGST + finalityStartup S gap extra) ≤ rho.horizon →
      ∃ q, rGST ≤ q ∧ q ≤ rGST + finalityStartup S gap extra ∧
        HonestProposalFinalityFrom S rho q (finalityDeadline S gap extra)

/-- The complete liveness review list. Each field is one observable property,
with its two explicit assumption regimes. -/
structure Liveness (S : Setup V) : Prop where
  honestProposalConfirmation : HonestProposalConfirmation S
  availableChainGrowth : AvailableChainGrowth S
  stableRecordGrowth : StableRecordGrowth S
  finalizedChainGrowth : FinalizedChainGrowth S
  honestProposalFinalization : HonestProposalFinalization S

end Statements
end DecoupledConsensusModel

end
