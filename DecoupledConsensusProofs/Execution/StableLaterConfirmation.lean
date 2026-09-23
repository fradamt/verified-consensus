module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.StablePreBoundarySuccessor
public import DecoupledConsensusProofs.Execution.OutputSeedCore

@[expose] public section

/-!
# Later pre-boundary confirmations above the stable chain

The stable-round carrier floor is the base. The pre-boundary successor is the
step. Each honest attestation is then handled at its own exact round by the
existing carrier-floor consumer.
-/

namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Internal Execution Internal.HealingSurface
open Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

set_option maxHeartbeats 400000 in
/-- Every pre-boundary round at or after the stable round has honest action
carriers above the protected prefix. -/
theorem stableAt_honestCarriersAbove_before_boundary
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s : Round) (P : Block V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : NamedOutageEntry.SlashableBound S rho)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hseed : OutputSeed S rho b0 s P) (hs : 0 < s) :
    ∀ r, s ≤ r → S.a r < b0 → HonestCarriersAbove S rho P r := by
  have hbase : HonestCarriersAbove S rho P s := hseed.carriers
  have hno : NoHonestConflictAbove S rho b0 P := hseed.noConflict
  intro r hsr hpre
  induction r, hsr using Nat.le_induction with
  | base => exact hbase
  | succ r hsr ih =>
      exact honestCarriersAbove_succ_of_gradeFormingMajority_of_stable
        S rho b0 b1 v s r P hexec hslash hcom hsleep hforming
          hv hmargin hseed hno hsr hpre
            (ih ((action_strictMono S) (Nat.lt_succ_self r) |>.trans hpre))

#print axioms stableAt_honestCarriersAbove_before_boundary

set_option maxHeartbeats 400000 in
/-- Clause 1: every honest pre-boundary attestation from the stable round on
confirms a named block above the protected prefix. -/
theorem stableAt_honestConfirmedAtOrAbove
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s : Round) (P : Block V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : NamedOutageEntry.SlashableBound S rho)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hseed : OutputSeed S rho b0 s P) (hs : 0 < s) :
    HonestConfirmedAtOrAbove S rho b0 s P := by
  have hall := stableAt_honestCarriersAbove_before_boundary
    S rho b0 b1 v s P hexec hslash hcom hsleep hforming
      hv hmargin hseed hs
  intro a t ha hem ht hsa key hkey K hKrun hKroot
  obtain ⟨_, _, _, _, _, _, htime, _⟩ :=
    Proofs.NamedOutageInputs.emitted_attestation_stages S rho hem
  have haction : S.a a.round < b0 := by
    simpa only [htime] using ht
  have hfloor := hall a.round hsa haction
  exact honestConfirmedAtOrAbove_exactRound_of_carrierFloor
    S rho a.round P hexec.core hfloor a t ha hem rfl key hkey K hKrun hKroot

#print axioms stableAt_honestConfirmedAtOrAbove

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
