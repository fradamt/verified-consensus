module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryFGSourceFrame
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedEntryCanonical
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryG1AfterCutoffReflection
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryFreshGradeProvenance
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoverySelectedG2SGHistory
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainRoundRead
public import Mathlib.Data.Int.LeastGreatest
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RawHeightProgress
public import DecoupledConsensusProofs.Protocol.ChainState.SlashableBoundBridge
public import DecoupledConsensusProofs.Objects.EmittedHeightBound
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityCertificates
public import DecoupledConsensusProofs.Execution.OutageProvenance
public import DecoupledConsensusProofs.Objects.MovingChainStep
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeDelivery
public import DecoupledConsensusProofs.Protocol.Store.RecoveryG1AfterCutoffPersistence
public import DecoupledConsensusProofs.Protocol.Grades.Grades
public import DecoupledConsensusInternal.HealingSurface
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Objects.FGConfirmationHistory
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryHandoffCore
public import DecoupledConsensusProofs.Objects.HealingDirectedHistory
public import DecoupledConsensusProofs.Protocol.Grades.RelativeOneChain
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryGenuineClearNextVote
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.FGSourceRawGrade

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface
open Protocol Proofs.HealingLemmas Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]



/-! ## Active finalized-below compatibility producer -/

private theorem relative_gradeBool_zero
    (E : Env V) (gv : Protocol.GradeView V) (F : Block V)
    (eta : Round) (early late : Time) (B : Block V) :
    DecoupledConsensusModel.Protocol.gradeBool E gv F eta 0 early late B = false := by
  simp [DecoupledConsensusModel.Protocol.gradeBool,
    DecoupledConsensusModel.Protocol.positive, DecoupledConsensusModel.Protocol.opposing,
    DecoupledConsensusModel.Protocol.readyView, DecoupledConsensusModel.Protocol.rawView,
    DecoupledConsensusModel.Protocol.interpretedInputs, DecoupledConsensusModel.Protocol.rawInputs,
    Protocol.latest_window_zero, DecoupledConsensusModel.Protocol.Supports,
    DecoupledConsensusModel.Protocol.Opposes, DecoupledConsensusModel.Protocol.CleanFrom]

private theorem nodeQ2_round_pos
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} {r : Round} {Q : Block V}
    (hQ : Internal.PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r = some Q) :
    0 < r := by
  apply Nat.pos_of_ne_zero
  intro hzero
  subst r
  have hgrade := selectedQ2_storeGrade_at_g2Domain S adm hQ
  simp only [Internal.PhaseGrades.storeGrade, Internal.PhaseGrades.phaseGrade] at hgrade
  rw [relative_gradeBool_zero] at hgrade
  cases hgrade

private theorem nodeQ2_of_nodeFGSource
    (S : Setup V) (rho : Run V) (v : V) (r : Round) {B : Block V}
    (hB : Internal.PhaseGrades.nodeFGSource S (actionReadAt S rho v r) r = some B) :
    ∃ Q, Internal.PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r = some Q := by
  cases hQ : Internal.PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r with
  | none =>
      have hQ' : Protocol.grade2_block_with
          (NamedProfile.gradeContract (actionReadAt S rho v r).cache)
          S.E S.hc (actionReadAt S rho v r).st.core.toHealing r = none := by
        simpa only [Internal.PhaseGrades.nodeQ2, Internal.PhaseGrades.nodeRead,
          Protocol.grade2_block_with] using hQ
      rw [Internal.PhaseGrades.nodeFGSource, Protocol.fg_source_with.eq_def, hQ'] at hB
      cases hB
  | some Q => exact ⟨Q, rfl⟩

/-- A named selected FG source implies that its frame contains a Q2 root, so
the source round is positive. -/
theorem PrefixFGSelectorConeAt.round_pos_of_seed
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T) :
    1 ≤ a.round := by
  have hsource : Internal.PhaseGrades.nodeFGSource S
      (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase := by
    have hs := hseed.exactFGSource
    unfold actionFGSource at hs
    dsimp only at hs
    change Protocol.fg_source_with
      (NamedProfile.gradeContract (actionStoreAt S rho a.val_index a.round).cache)
      S.E S.hc (actionStoreAt S rho a.val_index a.round).st.core.toHealing
      (S.hc.round_of (actionStoreAt S rho a.val_index a.round).s)
      (Protocol.grade2_block_with
        (NamedProfile.gradeContract (actionStoreAt S rho a.val_index a.round).cache)
        S.E S.hc (actionStoreAt S rho a.val_index a.round).st.core.toHealing
        (S.hc.round_of (actionStoreAt S rho a.val_index a.round).s)) =
          some Cfg.erase at hs
    rw [actionStoreAt_round] at hs
    simpa only [Internal.PhaseGrades.nodeFGSource, actionStoreAt] using hs
  obtain ⟨Q, hQ⟩ := nodeQ2_of_nodeFGSource S rho a.val_index a.round hsource
  exact nodeQ2_round_pos S adm hQ


#print axioms PrefixFGSelectorConeAt.round_pos_of_seed

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
