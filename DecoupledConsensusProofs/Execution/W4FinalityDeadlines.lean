module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Liveness
public import DecoupledConsensusProofs.Execution.W4RecoverySpine
public import DecoupledConsensusProofs.Protocol.ChainState.RecurringFinality

@[expose] public section

/-!
# Equality bridge for the closed finality bounds

The statement library exposes only expanded formulas. This leaf proves that
those formulas are the exact bounds used by the W4 recovery and recurring
finality proofs.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Statements

variable {V : Type} [DecidableEq V] [Fintype V]

theorem finalityStartup_eq_w4UniformHandoffLag
    (S : Setup V) (gap : Round) (extra : Nat) :
    Statements.Instantiation.finalityStartup S gap extra =
      w4UniformHandoffLag S gap extra := by
  simp [Statements.Instantiation.finalityStartup, w4UniformHandoffLag,
    w4UniformMovingBoundaryRound, w4UniformFGSafetyDeadline,
    progressLag', seedLag]
  ring

theorem finalityDeadline_eq_recurringFinalityDeadline
    (S : Setup V) (gap : Round) (extra : Nat) :
    Statements.Instantiation.finalityDeadline S gap extra =
      recurringFinalityDeadline S
        (recurringFinalityPhaseLag (progressLag' gap extra) gap) gap := by
  simp [Statements.Instantiation.finalityDeadline, recurringFinalityDeadline,
    recurringFinalityOneHeightLag, recurringFinalitySelectionLag,
    recurringFinalityPhaseCount, recurringFinalityPhaseLag,
    progressLag', seedLag]
  ring

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
