module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.EvaluationStore
public import DecoupledConsensusProofs.Protocol.Grades.GSTZeroSelectionSafety
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalVoteDuty

@[expose] public section



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The empty prefix before the first action -/

/-- The first confirmation duty is the first healing action. -/
theorem confirmation_time_zero_eq_action_zero (S : Setup V) :
    Protocol.confirmation_time S.E 0 = S.a 0 := by
  change Protocol.confirmation_time S.E 0 = S.hc.a S.E.Δ 0
  rw [Protocol.confirmation_time_eq_support_cutoff_succ,
    Protocol.a_eq_support_cutoff_succ]
  simp [Protocol.HealConfig.opening_slot]



/-! ## The slot-zero evaluation root -/



/-! ## The slot-zero walk -/











end Protocol
end DecoupledConsensusModel

end
