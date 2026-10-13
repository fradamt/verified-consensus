import DecoupledConsensusStatements
import Lean

/-! Check the generic review bundle and its result records. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let checkFields (name : Name) (expected : List String) := do
    let actual := (getStructureFields env name).toList.map (fun field => field.getString!)
    if actual != expected then
      throwError s!"Unexpected fields for {name}: {actual}"
  checkFields `DecoupledConsensusModel.Statements.Generic.Consensus
    ["constants", "nested", "certificatesAccountable", "finalizedAccountable",
      "finalizedMonotone", "honestNeverSlashed", "finalizedSafe", "available", "confirmedLive",
      "stableLive", "stableIncludedFast", "finalized", "stableAsynchronyResilient"]
  checkFields `DecoupledConsensusModel.Statements.Generic.OutputOrder
    ["finalizedBelowStable", "stableBelowConfirmed"]
  checkFields `DecoupledConsensusModel.Statements.Generic.AvailableAt
    ["confirmedSafe", "confirmedIncluded", "stableSafe", "stableIncluded"]
  checkFields `DecoupledConsensusModel.Statements.Generic.FinalizedAt
    ["finalizedIncluded", "finalizedLive"]
  for name in [
      `DecoupledConsensusModel.Statements.Generic.Consensus.nested,
      `DecoupledConsensusModel.Statements.Generic.Consensus.certificatesAccountable,
      `DecoupledConsensusModel.Statements.Generic.Consensus.finalizedAccountable,
      `DecoupledConsensusModel.Statements.Generic.Consensus.finalizedMonotone,
      `DecoupledConsensusModel.Statements.Generic.Consensus.honestNeverSlashed,
      `DecoupledConsensusModel.Statements.Generic.Consensus.finalizedSafe,
      `DecoupledConsensusModel.Statements.Generic.Consensus.available,
      `DecoupledConsensusModel.Statements.Generic.Consensus.confirmedLive,
      `DecoupledConsensusModel.Statements.Generic.Consensus.stableLive,
      `DecoupledConsensusModel.Statements.Generic.Consensus.stableIncludedFast,
      `DecoupledConsensusModel.Statements.Generic.Consensus.finalized,
      `DecoupledConsensusModel.Statements.Generic.Consensus.stableAsynchronyResilient,
      `DecoupledConsensusModel.Statements.Generic.OutputOrder.finalizedBelowStable,
      `DecoupledConsensusModel.Statements.Generic.OutputOrder.stableBelowConfirmed,
      `DecoupledConsensusModel.Statements.Generic.AvailableAt.confirmedSafe,
      `DecoupledConsensusModel.Statements.Generic.AvailableAt.confirmedIncluded,
      `DecoupledConsensusModel.Statements.Generic.AvailableAt.stableSafe,
      `DecoupledConsensusModel.Statements.Generic.AvailableAt.stableIncluded,
      `DecoupledConsensusModel.Statements.Generic.FinalizedAt.finalizedIncluded,
      `DecoupledConsensusModel.Statements.Generic.FinalizedAt.finalizedLive,
      `DecoupledConsensusModel.Statements.Instantiation.Consensus] do
    unless env.contains name do
      throwError "Missing generic review declaration: {name}"
  for name in [
      `DecoupledConsensusModel.Statements.Consensus,
      `DecoupledConsensusModel.Statements.Interface,
      `DecoupledConsensusModel.Statements.Constants,
      `DecoupledConsensusModel.Statements.instance,
      `DecoupledConsensusModel.Statements.ourConstants] do
    if env.contains name then
      throwError "Legacy statement declaration remains on review surface: {name}"

namespace DecoupledConsensusModel
open Statements.Generic
variable {V : Type} [DecidableEq V] [Fintype V]

example (P : Generic.ProtocolSpec V) (E : Generic.Env V)
    (I : Interface P) (C : Constants)
    (h : Consensus P E I C) : C.Valid := h.constants
example (P : Generic.ProtocolSpec V) (E : Generic.Env V)
    (I : Interface P) (C : Constants)
    (h : Consensus P E I C) (rho : Generic.Run V P.Object) : OutputOrder P I rho :=
  h.nested rho
example (P : Generic.ProtocolSpec V) (E : Generic.Env V)
    (I : Interface P) (C : Constants)
    (h : Consensus P E I C) :
      ∀ c c' T T', I.collisionFree c c' → I.finalizes c T → I.finalizes c' T' →
        Block.Compatible T T' ∨ I.evidence c c' := h.certificatesAccountable
example (P : Generic.ProtocolSpec V) (E : Generic.Env V)
    (I : Interface P) (C : Constants)
    (h : Consensus P E I C) :
      ∀ rho, RunWellFormed E I rho → AccountablySafeFrom P I rho I.finalized 0 :=
  h.finalizedAccountable
example (P : Generic.ProtocolSpec V) (E : Generic.Env V)
    (I : Interface P) (C : Constants)
    (h : Consensus P E I C) :
      ∀ rho, SortedRun rho → MonotoneFrom P rho I.finalized 0 :=
  h.finalizedMonotone
example (P : Generic.ProtocolSpec V) (E : Generic.Env V)
    (I : Interface P) (C : Constants)
    (h : Consensus P E I C) :
      ∀ rho, UnforgeableRun P E I rho → ∀ v ∈ rho.honest, ¬ I.slashes rho v :=
  h.honestNeverSlashed
example (P : Generic.ProtocolSpec V) (E : Generic.Env V)
    (I : Interface P) (C : Constants)
    (h : Consensus P E I C) :
      ∀ rho, AccountableRegime E I rho → AgreeFrom P rho I.finalized 0 :=
  h.finalizedSafe
example (P : Generic.ProtocolSpec V) (E : Generic.Env V)
    (I : Interface P) (C : Constants)
    (h : Consensus P E I C) :
      ∀ rho t₀, SleepyRegime P E I C rho t₀ → AvailableAt P I C rho t₀ :=
  h.available
example (P : Generic.ProtocolSpec V) (E : Generic.Env V)
    (I : Interface P) (C : Constants) (h : Consensus P E I C) :
      ∀ rho t₀ gap, LiveSleepyRegime P E I C rho t₀ gap →
        LiveFrom P I rho I.confirmed t₀ (C.growthDelay gap) := h.confirmedLive
example (P : Generic.ProtocolSpec V) (E : Generic.Env V)
    (I : Interface P) (C : Constants) (h : Consensus P E I C) :
      ∀ rho t₀ gap, LiveSleepyRegime P E I C rho t₀ gap →
        LiveFrom P I rho I.stable t₀ (C.stableGrowthDelay gap) := h.stableLive
example (P : Generic.ProtocolSpec V) (E : Generic.Env V)
    (I : Interface P) (C : Constants) (h : Consensus P E I C) :
      ∀ rho t₀, FreshSleepyRegime P E I C rho t₀ →
        IncludedFrom P I rho I.stable t₀ C.fastStableInclusionDelay := h.stableIncludedFast
example (P : Generic.ProtocolSpec V) (E : Generic.Env V) (I : Interface P) (C : Constants)
    (h : Consensus P E I C) :
      ∀ rho t₀ gap, FinalityRegime P E I C rho t₀ gap →
        FinalizedAt P I C rho (t₀ + C.finalityStartup gap) gap := h.finalized
example (P : Generic.ProtocolSpec V) (E : Generic.Env V)
    (I : Interface P) (C : Constants)
    (h : Consensus P E I C) :
      ∀ rho T b₀ b₁, OutageRegime P E I C rho T b₀ b₁ →
        PersistsFrom P rho I.stable T b₀ :=
  h.stableAsynchronyResilient

-- Constructor checks prevent redundant premises from returning unnoticed.
example (P : Generic.ProtocolSpec V) (E : Generic.Env V) (I : Interface P)
    (rho : Generic.Run V P.Object)
    (h : CarriedUnforgeable P rho)
    (hs : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    (hh : ∀ e ∈ rho.events, e.node ∈ rho.honest) : UnforgeableRun P E I rho :=
  { toCarriedUnforgeable := h, sorted := hs, honest_only := hh }

example (P : Generic.ProtocolSpec V) (E : Generic.Env V) (I : Interface P)
    (rho : Generic.Run V P.Object)
    (hs : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    (hi : I.idealization rho) : RunWellFormed E I rho :=
  { sorted := hs, idealization := hi }

example (P : Generic.ProtocolSpec V) (E : Generic.Env V) (I : Interface P)
    (C : Constants) (rho : Generic.Run V P.Object) (t₀ : Time)
    (h : SleepyRegime P E I C rho t₀) :
    ∀ t, ActionTime C t → t₀ ≤ t → C.participationLag ≤ t →
      t - C.participationLag ≤ rho.horizon →
      WindowMajority E rho.honest C.participationWindow t := h.windows

example (P : Generic.ProtocolSpec V) (E : Generic.Env V) (C : Constants)
    (rho : Generic.Run V P.Object)
    (h : ∀ v ∈ rho.honest, ∀ t, ActionTime C t → E.t_GST ≤ t →
      t ≤ rho.horizon → E.awake v t = true) : FullParticipation E C rho := h

example (P : Generic.ProtocolSpec V) (I : Interface P) (C : Constants)
    (rho : Generic.Run V P.Object) (start : Time) (gap : Nat)
    (h : ∀ t, OpeningTime I t → start ≤ t → t + gap * C.period ≤ rho.horizon →
      ∃ s, t + 2 * C.period ≤ I.proposalTime s ∧
        I.proposalTime s ≤ t + gap * C.period ∧ MultiProposerAt I C rho.honest s ∧
        ∀ s', I.opening s' → I.proposalTime s - 2 * C.period ≤ I.proposalTime s' →
          I.proposalTime s' < I.proposalTime s → I.proposer s' ∈ rho.honest) :
    StrongMultiProposerRecurrence I C rho start gap := h

example (P : Generic.ProtocolSpec V) (E : Generic.Env V) (I : Interface P)
    (C : Constants) (rho : Generic.Run V P.Object) (t₀ : Time)
    (h : FreshSleepyRegime P E I C rho t₀) :
    ∀ t, ActionTime C t → t₀ ≤ t → C.participationLag ≤ t →
      t - C.participationLag ≤ rho.horizon → FreshMajority E rho.honest C t := h.fresh

example (P : Generic.ProtocolSpec V) (E : Generic.Env V) (I : Interface P)
    (C : Constants) (rho : Generic.Run V P.Object) (T b₀ b₁ : Time)
    (h : OutageRegime P E I C rho T b₀ b₁) :
    ∀ t, ActionTime C t → C.participationLag ≤ t → t ≤ rho.horizon + C.participationLag →
      FreshMajority E rho.honest C t := h.participation

example (P : Generic.ProtocolSpec V) (I : Interface P) (C : Constants)
    (rho : Generic.Run V P.Object) (start : Time) (gap : Nat)
    (h : ∀ t, OpeningTime I t → start ≤ t → t + gap * C.period ≤ rho.horizon →
      ∃ s, t < I.proposalTime s ∧ I.proposalTime s ≤ t + gap * C.period ∧
        MultiProposerAt I C rho.honest s) : MultiProposerRecurrence I C rho start gap := h

-- Sleepy growth still needs a proposer strictly after every time, not just openings.
example (P : Generic.ProtocolSpec V) (I : Interface P) (C : Constants)
    (rho : Generic.Run V P.Object) (start : Time) (gap : Nat)
    (h : SingleProposerRecurrence I C rho start gap) :
    ∀ t, start ≤ t → t + gap * C.period ≤ rho.horizon →
      ∃ s, t < I.proposalTime s ∧ I.proposalTime s ≤ t + gap * C.period ∧
        I.proposer s ∈ rho.honest := h

end DecoupledConsensusModel
