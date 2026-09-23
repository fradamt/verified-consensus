module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.FirstProgressFGWitness
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryFGSelectorPrefixSeed
public import DecoupledConsensusProofs.Protocol.ChainState.Emission
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore

@[expose] public section

/-!
# Initial FG cones from actual first recovery crossings

The named selector seed exposes two local consequences that do not need the
missing genuine-clear producer: the exact checkpoint witness and weakening of
the named vote cone from the source to that checkpoint.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

theorem PrefixFGSelectorConeAt.confirmationWitness
    {S : Setup V} {rho : Run V} {start stop : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start stop blocked i a ta Cfg T) :
    fgConfirmationWitness S
      (actionStoreAt S rho a.val_index a.round) = some T := by
  rw [fgConfirmationWitness, hseed.exactFGSource]
  exact congrArg some hseed.checkpointStored.symm

theorem PrefixFGSelectorConeAt.checkpointCone
    {S : Setup V} {rho : Run V} {start stop : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start stop blocked i a ta Cfg T) :
    NamedHonestVotesCone S rho (S.hc.opening_slot a.round)
        (fun X => Block.Preceq T X) ∨
      NamedHonestVotesCone S rho (S.hc.opening_slot a.round + 1)
        (fun X => Block.Preceq T X) := by
  have hTCfg : Block.Preceq T Cfg.erase := by
    rw [hseed.checkpointDerived]
    exact Proofs.Optimistic.derive_named_T_h_preceq S.E S.cfg Cfg
  have lower : ∀ s : Slot,
      NamedHonestVotesCone S rho s
        (fun X => Block.Preceq Cfg.erase X) →
      NamedHonestVotesCone S rho s
        (fun X => Block.Preceq T X) := by
    intro s hcone w hw hcommittee
    obtain ⟨X, hCfgX, hXrun, hXemit⟩ := hcone w hw hcommittee
    exact ⟨X, Block.preceq_trans hTCfg hCfgX, hXrun, hXemit⟩
  exact hseed.cone.imp (lower _) (lower _)

/-! ## Mechanical named consequences of the selector seed -/

theorem noLocalHeightPairBefore_of_frontier_lt
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {start : Nat} {H : Height}
    (hbound : honestHMaxBeforeIndex S rho start < H) :
    Internal.NoLocalHeightPairBefore S rho start H := by
  intro i v t a hi hv hevent hemit hrow
  exact (Nat.not_le_of_gt hbound)
    (honestEmittedHeight_le_honestHMaxBeforeIndex S adm hv hevent hemit hi hrow)

theorem PrefixFGSelectorConeAt.action_hMax_of_firstProgress
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time} {Cfg : NamedBlock V}
    {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : FirstHeightProgressAt S rho (blocked + 1) first) :
    (actionStoreAt S rho a.val_index a.round).st.core.h_max = blocked + 1 := by
  apply hfirst.action_hMax adm hseed.indexLtStop hseed.signerHonest
    hseed.exactTick hseed.emitted
  rcases hseed.targetOrTimeout with htarget | htimeout
  · rw [htarget]
    rfl
  · rw [htimeout]
    rfl

theorem PrefixFGSelectorConeAt.selectedG2_preceq_source_named
    {S : Setup V} {rho : Run V} {start stop : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time} {Cfg : NamedBlock V}
    {T Q : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start stop blocked i a ta Cfg T)
    (hselected : PhaseGrades.nodeQ2 S
      (actionReadAt S rho a.val_index a.round) a.round = some Q) :
    Block.Preceq Q Cfg.erase := by
  have hround : S.hc.round_of
      (actionReadAt S rho a.val_index a.round).st.core.s = a.round :=
    actionStoreAt_round S rho a.val_index a.round
  have hround' : S.hc.round_of
      (actionReadAt S rho a.val_index a.round).st.core.toHealing.s = a.round := by
    simpa only [Protocol.Store.toHealing] using hround
  have hsource : Protocol.fg_source_with
      (NamedProfile.gradeContract
        (actionReadAt S rho a.val_index a.round).cache) S.E S.hc
      (actionReadAt S rho a.val_index a.round).st.core.toHealing
      (S.hc.round_of
        (actionReadAt S rho a.val_index a.round).st.core.toHealing.s)
      (Protocol.grade2_block_with
        (NamedProfile.gradeContract
          (actionReadAt S rho a.val_index a.round).cache) S.E S.hc
        (actionReadAt S rho a.val_index a.round).st.core.toHealing
        (S.hc.round_of
          (actionReadAt S rho a.val_index a.round).st.core.toHealing.s)) =
      some Cfg.erase := by
    simpa only [actionFGSource, actionStoreAt] using hseed.exactFGSource
  rw [hround'] at hsource
  have hsource' : PhaseGrades.nodeFGSource S
      (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase := by
    simpa only [PhaseGrades.nodeFGSource] using hsource
  exact preceq_actionFGSource_of_actionQ2 S rho a.val_index a.round hselected
    (Block.preceq_self Q) hsource'

#print axioms PrefixFGSelectorConeAt.confirmationWitness
#print axioms PrefixFGSelectorConeAt.checkpointCone
#print axioms noLocalHeightPairBefore_of_frontier_lt
#print axioms PrefixFGSelectorConeAt.action_hMax_of_firstProgress
#print axioms PrefixFGSelectorConeAt.selectedG2_preceq_source_named






end HealingSurface
end Proofs
end DecoupledConsensusModel

end
