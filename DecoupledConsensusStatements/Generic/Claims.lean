module
public import DecoupledConsensusStatements.Generic.Properties
public import DecoupledConsensusStatements.Generic.Regimes

@[expose] public section

/-!
# Generic claims

Purpose: bundle the public output-order, safety, liveness, finality, and outage
claims into the review contract.
An auditor checks the unconditional fields, the premise-to-field mapping, and
the exact conclusion record for each protocol result.

Defines: `AvailableAt`, `StableLiveAt`, `FinalizedAt`, and `Consensus`.
Read after: `Properties` and `Regimes`.
Read next: `DecoupledConsensusStatements.Instantiation`.
-/

namespace DecoupledConsensusModel.Statements.Generic

open DecoupledConsensusModel

variable {V : Type} {P : DecoupledConsensusModel.Generic.ProtocolSpec V}
  [DecidableEq V] [_root_.Fintype V]

/-- Available outputs from `t₀`; inclusion into the confirmed chain needs no
recurrence: an honest proposal is confirmed by everyone within
`confirmationDelay`. -/
structure AvailableAt (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (I : Interface P) (C : Constants)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) (t₀ : Time) : Prop where
  confirmedSafe : SafeFrom P rho I.confirmed t₀
  confirmedIncluded : IncludedFrom P I rho I.confirmed t₀ C.confirmationDelay
  stableSafe : SafeFrom P rho I.stable t₀

/-- The stable output from `t₀` when the strong recurrence holds: inclusion into the stable chain
needs an honest multi-proposer window, because a G2 root forms only in such a window. -/
structure StableLiveAt (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (I : Interface P) (C : Constants)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) (t₀ : Time) (gap : Nat) : Prop where
  stableIncluded : IncludedFrom P I rho I.stable t₀ (C.stableInclusionDelay gap)
  stableLive : LiveFrom P I rho I.stable t₀ (C.stableGrowthDelay gap)

/-- The finalized output from the end of the startup. -/
structure FinalizedAt (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (I : Interface P) (C : Constants)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) (t₁ : Time) (gap : Nat) : Prop where
  finalizedIncluded : IncludedFrom P I rho I.finalized t₁ (C.finalityDeadline gap)
  finalizedLive : LiveFrom P I rho I.finalized t₁
    ((gap : Time) * C.period + C.finalityDeadline gap)

/-- The generic consensus bundle: each field has one named regime premise and one named
conclusion record or output predicate. -/
structure Consensus
    (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (E : DecoupledConsensusModel.Generic.Env V) (I : Interface P) (C : Constants) : Prop where
  /-- The constants satisfy the stated timing and bound constraints. -/
  constants : C.Valid
  /-- No premise. -/
  nested : ∀ rho, OutputOrder P I rho
  /-- No run premise. -/
  certificatesAccountable : ∀ c c' T T', I.collisionFree c c' → I.finalizes c T → I.finalizes c' T' →
    Block.Compatible T T' ∨ I.evidence c c'
  /-- Well-formed run. -/
  finalizedAccountable : ∀ rho, RunWellFormed E I rho → AccountablySafeFrom P I rho I.finalized 0
  /-- Unforgeable run. -/
  honestNeverSlashed : ∀ rho, UnforgeableRun P E I rho → ∀ v ∈ rho.honest, ¬ I.slashes rho v
  /-- Accountable regime. -/
  finalizedSafe : ∀ rho, AccountableRegime E I rho → SafeFrom P rho I.finalized 0
  /-- Sleepy regime. -/
  available : ∀ rho t₀, SleepyRegime P E I C rho t₀ → AvailableAt P I C rho t₀
  confirmedLive : ∀ rho t₀ gap, LiveSleepyRegime P E I C rho t₀ gap →
    LiveFrom P I rho I.confirmed t₀ (C.growthDelay gap)
  stableLive : ∀ rho t₀ gap, StrongLiveSleepyRegime P E I C rho t₀ gap →
    StableLiveAt P I C rho t₀ gap
  /-- Finality regime. -/
  finalized : ∀ rho t₀ gap, FinalityRegime P E I C rho t₀ gap →
    FinalizedAt P I C rho (t₀ + C.finalityStartup gap) gap
  /-- Outage regime. -/
  stablePersists : ∀ rho T b₀ b₁, OutageRegime P E I C rho T b₀ b₁ →
    PersistsFrom P rho I.stable T b₀

end DecoupledConsensusModel.Statements.Generic

end
