module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.WeakFiniteWindow

@[expose] public section

/-!
# Timing core for live-confirmation consumers

This leaf keeps the confirmation-to-next-vote timing theorem separate from
the stale settled-handover declarations in `WeakLiveConfirmationRun`.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

/-- An earlier slot confirms before the vote duty after the destination slot. -/
theorem confirmationTime_lt_nextVote_of_lt (E : Env V) {q d : Slot} (hqd : q < d) :
    Protocol.confirmation_time E q < Protocol.vote_time E (d + 1) := by
  have hnext : Protocol.vote_time E (d + 1) = Protocol.vote_time E d + 4 * E.Δ := by
    unfold Protocol.vote_time Env.t slotStart
    push_cast
    ring
  rw [← vote_time_succ_add_delta_eq_confirmation_time E q, hnext]
  have hle := vote_time_mono_slots E (Nat.succ_le_of_lt hqd)
  have harith : ∀ a b z : Int, a ≤ b → 0 < z → a + z < b + 4 * z := by
    intro a b z hab hz
    omega
  exact harith _ _ _ hle E.Δ_pos

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
