module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Model
public import DecoupledConsensusInternal.Legacy.Safety
public import DecoupledConsensusInternal.Legacy.Liveness
public import DecoupledConsensusInternal.Legacy.Interface
public import DecoupledConsensusInternal.Legacy.Definitions.Vocabulary
public import DecoupledConsensusInternal.Legacy.Assumptions.Regimes
public import DecoupledConsensusInternal.Legacy.Definitions.LeakFairnessL1
public import DecoupledConsensusInternal.Legacy.Definitions.NestedOutputs
public import DecoupledConsensusInternal.Legacy.Definitions.NamedStableChainOutageInternal

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Public review contracts

`LegacyConsensus` keeps the historical record used by the existing checked
proofs. The public record below is the standard vocabulary surface. -/

namespace DecoupledConsensusModel
namespace Statements
open Internal Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The accepted safety and liveness contracts. Public visibility elsewhere in
Lean does not make a helper or an intermediate result part of this review. -/
structure LegacyConsensus (S : Setup V) : Prop where
  finality : FinalitySafety S
  /-- Honest validators are never slashable when they follow the validator
  client's finality/timeout signing rules. -/
  voteSafetyOfClients : ValidatorVoteSafety S
  finalizedPrefix : ∀ rho, FinalizedPrefixConfirmed S rho
  
  nestedOutputs : NestedOutputs S
  /-- Safety AND liveness of the available chain from genesis when GST = 0 under weak participation (`WeakGenesis`): compatible and monotone confirmations and user outputs across honest nodes, safe proposal reads, and confirmation of honest and user proposals. -/
  gstZeroGuarantees : ∀ rho, WeakGenesis S rho → GSTZeroGuarantees S rho
  boundedSafety : BoundedSafetyRecovery S
  /-- Current-production L1 leak fairness at the source frontier. Its execution
  premise contains only schedule well-formedness and root collision freedom;
  `SlashableBound` supplies same-height justification uniqueness. -/
  leakFairness : LeakFairness.LeakFairnessL1CurrentProduction S
  
  stableSafety : StableRecordSafety S
  liveness : Liveness S
  
  asynchronyResilience : NamedStableChainOutage.StableChainOutageResilience S

/-- The historical run-well-formedness record under the standard name. -/
abbrev RunWellFormed (S : Setup V) (rho : Run V) : Prop :=
  FinalityExecution S rho

/-- No premise beyond run well-formedness. -/
structure Unconditional (S : Setup V) (I : Interface V) : Prop where
  finalizedBelowStable : ∀ rho, Prefix S rho I.finalized I.stable
  stableBelowConfirmed : ∀ rho, Prefix S rho I.stable I.confirmed
  pureFinality : ∀ c c' T T', I.collisionFree c c' → I.finalizes c T →
    I.finalizes c' T' → Block.compatible T T' = true ∨ I.evidence c c'
  finalizedAccountable : ∀ rho, RunWellFormed S rho →
    AccountablyConsistentFrom S I rho I.finalized I.finalized 0
  voteSafetyOfClients : ValidatorVoteSafety S

/-- Claims under the accountable bound. -/
structure Accountable (S : Setup V) (I : Interface V) : Prop where
  finalizedAgree : ∀ rho, RunWellFormed S rho → SlashableBound I rho →
    AgreeFrom S rho I.finalized 0
  leakFairness : LeakFairness.LeakFairnessL1CurrentProduction S

/-- Available-chain safety and liveness from a recovered sleepy regime. -/
structure Available (S : Setup V) (I : Interface V) (C : Constants) : Prop where
  confirmedSafe : ∀ rho t₀, SleepyRegime S I C rho t₀ → RecoveredBy S I C rho t₀ →
    SafeFrom S rho I.confirmed t₀
  confirmedIncluded : ∀ rho t₀, SleepyRegime S I C rho t₀ → RecoveredBy S I C rho t₀ →
    Included S I rho I.confirmed t₀ C.confirmationDelay
  confirmedGrowth : ∀ rho t₀, SleepyRegime S I C rho t₀ → RecoveredBy S I C rho t₀ →
    ∀ gap, ProposerOpeningCarrierRecurrence S rho gap →
      Growth S rho I.confirmed t₀ (C.growthDelay gap) (honestAfter I rho)
  stableSafe : ∀ rho t₀, SleepyRegime S I C rho t₀ → RecoveredBy S I C rho t₀ →
    SafeFrom S rho I.stable t₀
  stableGrowth : ∀ rho t₀, SleepyRegime S I C rho t₀ → RecoveredBy S I C rho t₀ →
    ∀ gap, ProposerOpeningCarrierRecurrence S rho gap →
      Growth S rho I.stable t₀ (C.stableGrowthDelay gap) (honestAfter I rho)

/-- Finalized-chain inclusion from a BFT finality regime. -/
structure Finalized (S : Setup V) (I : Interface V) (C : Constants) : Prop where
  included : ∀ rho t₀ gap extra, FinalityRegime S I rho t₀ gap extra →
    t₀ + C.finalityStartup gap extra ≤ rho.horizon →
    Included S I rho I.finalized (t₀ + C.finalityStartup gap extra)
      (C.finalityDeadline gap extra)

/-- Every block below an honest node's stable output at a time `T` before the
outage stays below every honest node's stable output from `b₀` through the
horizon; the margin and expiry are measured from the first round action at or
after `T`. -/
structure Outage (S : Setup V) (I : Interface V) (C : Constants) : Prop where
  stablePersists : ∀ rho b₀ b₁ (T : Time) v P,
    OutageRegime S I C rho b₀ b₁ → SlashableBound I rho → v ∈ rho.honest →
    Block.Preceq P (readAt S rho I.stable v T) →
    Statements.Instantiation.nextAction S T + C.formationMargin ≤ b₀ →
    b₁ + S.E.Δ ≤ C.expiry (Statements.Instantiation.nextAction S T) → b₁ + S.E.Δ ≤ rho.horizon →
    ∀ t, b₀ ≤ t → t ≤ rho.horizon → InBy S rho I.stable P t

/-- The standard public bundle, grouped by regime. -/
structure Consensus (S : Setup V) (I : Interface V) (C : Constants) : Prop where
  unconditional : Unconditional S I
  accountable : Accountable S I
  available : Available S I C
  finalized : Finalized S I C
  outage : Outage S I C

end Statements
end DecoupledConsensusModel

end
