module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.ActionSources
public import DecoupledConsensusProofs.Execution.FGSelectorWitness
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Execution.ProgressCanonicality
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.RecoveryVoteCone
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsBridge
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Canonicality
public import DecoupledConsensusProofs.Protocol.ChainState.Main
public import DecoupledConsensusInternal.Execution.Assumptions
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusProofs.Execution.FrontierProducers
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionHistory
public import DecoupledConsensusProofs.Generic.EvaluationStore
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsProducers
public import DecoupledConsensusProofs.Protocol.Grades.FrameCompleted
public import DecoupledConsensusProofs.Protocol.Grades.FrameForward
public import DecoupledConsensusProofs.Protocol.Grades.Interpolation
public import DecoupledConsensusProofs.Protocol.Grades.Q10Frame

@[expose] public section

/-!
# Exact FG confirmation-witness history

The witness is selected before the validator client chooses a target or a
timeout. A timeout does not put the witness root on the wire, but its action
still selects the same source and checkpoint. The named source body is kept
through this file. Erased blocks appear only at geometric interfaces.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem actionStore_coherent
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (v : V) (r : Round) :
    Proofs.NamedStore.Coherent S.E S.cfg (actionStoreAt S rho v r).st := by
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (actionStoreAt S rho v r).st := by
    apply Proofs.NamedConfirmationMembership.invariant_update
    exact Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ (S.a r)
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a r) v).1
  exact hinv.1.1

private theorem actionBody_runBlock
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionStoreAt S rho v r).st.bodies) :
    RunBlock S rho D := by
  have hDpre : D ∈ (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    simpa only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
      NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hD
  obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted (S.a r)
  have hDi : D ∈ (rho.stateBefore S i v).st.bodies := by
    change D ∈ (NamedRun.stateBefore S rho i v).st.bodies
    rw [← hi]
    exact hDpre
  exact Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hDi)

private theorem namedAncestorBodyMem {st : Protocol.NamedStore V}
    (hpc : NamedStore.NamedParentClosed st) {A B : NamedBlock V}
    (hB : B ∈ st.bodies) (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
      exact hAB ▸ hB
  | node parent slot root votes support rows proposer ih =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hparent
      · exact hB
      · exact ih (hpc.2 _ hB) hparent

theorem action_named_checkpoint
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionStoreAt S rho v r).st.bodies) :
    ∃ K : NamedBlock V,
      K ∈ (actionStoreAt S rho v r).st.bodies ∧
      K.erase = (derive_named S.E S.cfg D).T_h ∧
      (derive_named S.E S.cfg K).h = (derive_named S.E S.cfg D).h ∧
      NamedBlock.Preceq K D ∧
      RunBlock S rho K := by
  obtain ⟨K, hKD, hKentry, hKh⟩ :=
    Proofs.NamedEntryHeight.entry_ancestor_same_height S.E S.cfg D
  have hcoh := actionStore_coherent S adm v r
  have hK : K ∈ (actionStoreAt S rho v r).st.bodies :=
    namedAncestorBodyMem hcoh.2.2.1 hD hKD
  exact ⟨K, hK, hKentry, hKh, hKD, actionBody_runBlock S adm hv hK⟩

#print axioms action_named_checkpoint

/-- A named source body determines the checkpoint returned by the action. -/
theorem fgConfirmationWitness_checkpoint
    (S : Setup V) {n : NamedNodeState V} {T : Block V}
    (hagree : Internal.NamedDerivedStateAgrees S.E S.cfg n.st)
    {C : NamedBlock V} (hC : C ∈ n.st.bodies)
    (hsource : actionFGSource S n = some C.erase)
    (hwitness : fgConfirmationWitness S n = some T) :
    (derive_named S.E S.cfg C).T_h = T := by
  unfold fgConfirmationWitness at hwitness
  rw [hsource] at hwitness
  simp only [Option.map_some, Option.some.injEq] at hwitness
  rw [← hwitness, hagree C hC]

/-- Compatible named checkpoints at the same named height are equal. -/
theorem fgConfirmationWitness_eq_of_compatible_of_height_eq
    (S : Setup V) {C C' : NamedBlock V} {T T' : Block V}
    (hcompat : NamedBlock.compatible C C' = true)
    (hheight : (derive_named S.E S.cfg C).h =
      (derive_named S.E S.cfg C').h)
    (hT : T = (derive_named S.E S.cfg C).T_h)
    (hT' : T' = (derive_named S.E S.cfg C').T_h) :
    T = T' := by
  have hordered : NamedBlock.Preceq C C' ∨ NamedBlock.Preceq C' C := by
    simpa only [NamedBlock.compatible, Bool.or_eq_true] using hcompat
  rcases hordered with hpre | hpre
  · rw [hT, hT']
    exact Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hpre hheight
  · rw [hT, hT']
    exact (Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hpre hheight.symm).symm

/-! ## Exact row provenance -/

theorem honestHeightRow_confirmationWitness
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {a : NamedAttestation V} {ta : Time} {h : Height}
    (haHon : a.val_index ∈ rho.honest)
    (hemit : rho.emits S a.val_index (Object.attest a) ta)
    (hh : a.height_pair.erase.height? = some h) :
    ∃ D K : NamedBlock V,
      fgConfirmationWitness S
          (actionStoreAt S rho a.val_index a.round) =
        some (derive_named S.E S.cfg K).T_h ∧
      D ∈ (actionStoreAt S rho a.val_index a.round).st.bodies ∧
      actionFGSource S (actionStoreAt S rho a.val_index a.round) = some D.erase ∧
      (derive_named S.E S.cfg D).h = h ∧
      K ∈ (actionStoreAt S rho a.val_index a.round).st.bodies ∧
      K.erase = (derive_named S.E S.cfg D).T_h ∧
      (derive_named S.E S.cfg K).h = h ∧
      Block.Preceq K.erase D.erase ∧
      (a.height_pair.erase = HeightPair.target h K.erase.root ∨
        a.height_pair.erase = HeightPair.timeout h) := by
  obtain ⟨D, J, htime, ha, hsource, hD, hheight, hnamedHeight, hJ, hrow⟩ :=
    honestEmittedHeightRow_exactFGSelectorWitness S adm haHon hemit hh
  obtain ⟨K, hK, hKentry, hKheight, hKpre, hKrun⟩ :=
    action_named_checkpoint S adm haHon hD
  have hKheight' : (derive_named S.E S.cfg K).h = h :=
    hKheight.trans hnamedHeight
  have hDderive :
      (actionStoreAt S rho a.val_index a.round).st.core.σ D.erase =
        derive_named S.E S.cfg D :=
    (actionStore_coherent S adm a.val_index a.round).2.2.2.2 D hD
  have hfg' : fgConfirmationWitness S
      (actionStoreAt S rho a.val_index a.round) =
      some (derive_named S.E S.cfg D).T_h := by
    unfold fgConfirmationWitness
    rw [hsource, Option.map_some, hDderive]
  have hKtarget : (derive_named S.E S.cfg K).T_h = K.erase := by
    exact (Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hKpre hKheight).trans
      hKentry.symm
  have hfgK : fgConfirmationWitness S
      (actionStoreAt S rho a.val_index a.round) =
      some (derive_named S.E S.cfg K).T_h := by
    rw [hfg']
    congr 1
    exact (hKtarget.trans hKentry).symm
  have hJroot : J.root = K.erase.root := by
    rw [hJ, ← hKentry]
  refine ⟨D, K, hfgK, hD, hsource, hnamedHeight, hK, hKentry,
    hKheight', ?_, ?_⟩
  · exact Proofs.NamedWire.erase_preceq hKpre
  · simpa only [hJroot] using hrow

/-! ## A frontier row supplies a named checkpoint -/

theorem frontier_confirmationWitness
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hmajority : HonestWeightMajority S rho.honest)
    {v : V} {time : Time}
    (hlarge : 1 < (rho.storeBeforeTime S v time).h_max) :
    ∃ (a : NamedAttestation V) (ta : Time) (D K : NamedBlock V),
      a.val_index ∈ rho.honest ∧
      NamedRun.emits S rho a.val_index (Object.attest a) ta ∧ ta < time ∧
      a.height_pair.erase.height? =
        some ((rho.storeBeforeTime S v time).core.h_max - 1) ∧
      fgConfirmationWitness S
          (actionStoreAt S rho a.val_index a.round) =
        some (derive_named S.E S.cfg K).T_h ∧
      D ∈ (actionStoreAt S rho a.val_index a.round).st.bodies ∧
      K ∈ (actionStoreAt S rho a.val_index a.round).st.bodies ∧
      K.erase = (derive_named S.E S.cfg D).T_h ∧
      RunBlock S rho K ∧
      (derive_named S.E S.cfg K).h =
        (rho.storeBeforeTime S v time).core.h_max - 1 := by
  obtain ⟨W, hW, Q, X, a, ta, hmaxW, hQ, hXW, haW, haHon, hemit, hta,
      hheight⟩ := Protocol.frontierQuorumWitness_stateBeforeTime
    S adm hmajority hlarge
  obtain ⟨D, K, hfg, hD, -, hDheight, hK, hKentry, hKheight, -, -⟩ :=
    honestHeightRow_confirmationWitness S adm haHon hemit hheight
  have hKrun := actionBody_runBlock S adm haHon hK
  exact ⟨a, ta, D, K, haHon, hemit, hta, hheight, hfg, hD, hK,
    hKentry, hKrun, hKheight⟩

/-! ## Source bounds and event-prefix history -/


/-! ## The named upper-window source package -/


















end HealingSurface
end Proofs
end DecoupledConsensusModel

end
