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
      "honestNeverSlashed", "finalizedSafe", "available", "confirmedLive",
      "stableLive", "finalized", "stableAsynchronyResilient"]
  checkFields `DecoupledConsensusModel.Statements.Generic.OutputOrder
    ["finalizedBelowStable", "stableBelowConfirmed"]
  checkFields `DecoupledConsensusModel.Statements.Generic.AvailableAt
    ["confirmedSafe", "confirmedIncluded", "stableSafe"]
  checkFields `DecoupledConsensusModel.Statements.Generic.StableLiveAt
    ["stableIncluded", "stableLive"]
  checkFields `DecoupledConsensusModel.Statements.Generic.FinalizedAt
    ["finalizedIncluded", "finalizedLive"]
  for name in [
      `DecoupledConsensusModel.Statements.Generic.Consensus.nested,
      `DecoupledConsensusModel.Statements.Generic.Consensus.certificatesAccountable,
      `DecoupledConsensusModel.Statements.Generic.Consensus.finalizedAccountable,
      `DecoupledConsensusModel.Statements.Generic.Consensus.honestNeverSlashed,
      `DecoupledConsensusModel.Statements.Generic.Consensus.finalizedSafe,
      `DecoupledConsensusModel.Statements.Generic.Consensus.available,
      `DecoupledConsensusModel.Statements.Generic.Consensus.confirmedLive,
      `DecoupledConsensusModel.Statements.Generic.Consensus.stableLive,
      `DecoupledConsensusModel.Statements.Generic.Consensus.finalized,
      `DecoupledConsensusModel.Statements.Generic.Consensus.stableAsynchronyResilient,
      `DecoupledConsensusModel.Statements.Generic.OutputOrder.finalizedBelowStable,
      `DecoupledConsensusModel.Statements.Generic.OutputOrder.stableBelowConfirmed,
      `DecoupledConsensusModel.Statements.Generic.AvailableAt.confirmedSafe,
      `DecoupledConsensusModel.Statements.Generic.AvailableAt.confirmedIncluded,
      `DecoupledConsensusModel.Statements.Generic.AvailableAt.stableSafe,
      `DecoupledConsensusModel.Statements.Generic.StableLiveAt.stableIncluded,
      `DecoupledConsensusModel.Statements.Generic.StableLiveAt.stableLive,
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
      ∀ rho, UnforgeableRun P E I rho → ∀ v ∈ rho.honest, ¬ I.slashes rho v :=
  h.honestNeverSlashed
example (P : Generic.ProtocolSpec V) (E : Generic.Env V)
    (I : Interface P) (C : Constants)
    (h : Consensus P E I C) :
      ∀ rho, AccountableRegime E I rho → SafeFrom P rho I.finalized 0 :=
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
      ∀ rho t₀ gap, StrongLiveSleepyRegime P E I C rho t₀ gap →
        StableLiveAt P I C rho t₀ gap := h.stableLive
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

end DecoupledConsensusModel
