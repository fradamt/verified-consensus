module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ValidatorClient.HeightPairCases
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradePersistence
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.RecoverySourceProgress
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.Actions
public import DecoupledConsensusProofs.Execution.EmissionShape

@[expose] public section

/-!
# Exact FG-selector witness for emitted height rows

The emitted row is named. The selector source and its height are read from
the named action duty, and the retained body is supplied by the named action
source witness.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- An honest emitted nonempty height row has its exact named selector body.

The erasure appears only at the geometric wire boundary. -/
theorem honestEmittedHeightRow_exactFGSelectorWitness
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {a : NamedAttestation V} {ta : Time} {h : Height}
    (haHon : a.val_index ∈ rho.honest)
    (hemit : rho.emits S a.val_index (Object.attest a) ta)
    (hh : a.height_pair.erase.height? = some h) :
    ∃ D : NamedBlock V, ∃ J : Block V,
      ta = S.a a.round ∧
        a = actionAttestationAt S rho a.val_index a.round ∧
        actionFGSource S (actionStoreAt S rho a.val_index a.round) =
          some D.erase ∧
        D ∈ (actionStoreAt S rho a.val_index a.round).st.bodies ∧
        ((actionStoreAt S rho a.val_index a.round).st.core.σ D.erase).h = h ∧
        (Protocol.derive_named S.E S.cfg D).h = h ∧
        J = (Protocol.derive_named S.E S.cfg D).T_h ∧
        (a.height_pair.erase = HeightPair.target h J.root ∨
          a.height_pair.erase = HeightPair.timeout h) := by
  have hshape := Proofs.Optimistic.emits_attest_shape S hemit
  have htime : ta = S.a a.round := hshape.2
  have hemitCopy := hemit
  obtain ⟨i, hi, -⟩ := hemitCopy
  have hiMem : Event.tick a.val_index ta ∈ rho.events :=
    List.mem_of_getElem? hi
  have hactionHor : S.a a.round ≤ rho.horizon := by
    have hin := (adm.in_horizon (Event.tick a.val_index ta) hiMem).2
    simpa only [Event.time, htime] using hin
  have hemitExact := honest_emits_exact_actionAttestationAt
    S adm haHon a.round hactionHor
  have haEq : a = actionAttestationAt S rho a.val_index a.round := by
    apply Proofs.Optimistic.emits_attest_unique S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hemit hemitExact
    exact (actionAttestationAt_shape S rho a.val_index a.round).2.1.symm
  rw [haEq] at hh
  generalize hp : (actionAttestationAt S rho a.val_index a.round).height_pair = q at hh
  cases q with
  | empty =>
      cases hh
  | vote h' entry timeout =>
      have hh' : h' = h := by
        cases timeout <;>
          simpa [NamedHeightPair.erase, HeightPair.height?] using hh
      subst h'
      obtain ⟨Cfg, hCfg, hCfgHeight, hCfgRoot⟩ :=
        NamedActionSources.action_source S rho a.val_index a.round h entry timeout
          hp
      obtain ⟨D, hD, hDerase, hDderive, -⟩ :=
        NamedActionSources.action_witness S rho a.val_index a.round Cfg hCfg
      let J := (Protocol.derive_named S.E S.cfg D).T_h
      have hsource : actionFGSource S
          (actionStoreAt S rho a.val_index a.round) = some D.erase := by
        simpa only [actionStoreAt, hDerase] using hCfg
      have hheight :
          ((actionStoreAt S rho a.val_index a.round).st.core.σ D.erase).h = h := by
        simpa only [actionStoreAt, hDerase] using hCfgHeight
      have hnamedHeight :
          (Protocol.derive_named S.E S.cfg D).h = h := by
        simpa only [hDderive, actionStoreAt, hDerase] using hheight
      have hJroot : J.root = entry := by
        dsimp only [J]
        simpa only [hDderive] using hCfgRoot
      refine ⟨D, J, htime, haEq, hsource, hD, hheight,
        hnamedHeight, rfl, ?_⟩
      cases timeout with
      | false =>
          left
          rw [haEq, hp]
          simp [NamedHeightPair.erase, hJroot]
      | true =>
          right
          rw [haEq, hp]
          simp [NamedHeightPair.erase]

#print axioms honestEmittedHeightRow_exactFGSelectorWitness

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
