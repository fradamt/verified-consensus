module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.UserConfirmationHistory
public import DecoupledConsensusProofs.Protocol.Grades.VoteBelowSource
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Schedule.RecordAtBoundary

@[expose] public section

/-!
# Stable-record write mechanics over the named runtime

This module preserves the names from the pre-rewrite stable-record module.
The handler facts delegate to the named retention ladder. The stable-root
origin and tick facts delegate to `StableRootSuffixOriginRun`, which uses the
prepared confirmation read and its frame contract.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace StableRecord

open Protocol (ChainState HeightConfig)
open Protocol (HealConfig)
open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]













omit [Fintype V] in
theorem preceq_advance_of_nesting {old_s old_c H new_s : Block V}
    (hnew : new_s = old_s ∨ Block.Preceq new_s H)
    (hnest : Block.Preceq old_s old_c)
    (hcompat : Block.compatible old_c H = true) :
    Block.Preceq new_s (Protocol.advance_confirmed old_c H) := by
  unfold Protocol.advance_confirmed
  split
  · rename_i hle
    rcases hnew with h | h
    · rw [h]
      exact hnest
    · exact Block.preceq_trans h hle
  · rename_i hnot
    rcases hnew with h | h
    · have hcH : Block.Preceq old_c H := by
        simp only [Block.compatible, Bool.or_eq_true] at hcompat
        exact hcompat.resolve_right hnot
      rw [h]
      exact Block.preceq_trans hnest hcH
    · exact h





theorem update_confirmation_latest_stable
    (contract : Protocol.GradeContract V) (E : Env V)
    (hc : HealConfig) (st : Protocol.NamedStore V) (s : Slot) :
    (Protocol.NamedDuties.update_confirmation_with contract E hc st s).latest_stable =
      match contract.stableRoot E hc st.core.toHealing (hc.round_of st.core.s) with
      | some G => Protocol.advance_confirmed st.core.latest_stable G
      | none => st.core.latest_stable := rfl


end StableRecord
end Proofs
end DecoupledConsensusModel

end
