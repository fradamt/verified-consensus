module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.WeakLiveConfirmationCore

@[expose] public section

/-!
# Timing core for strict confirmation reads

This leaf keeps the action-to-proposal timing theorem separate from the stale
settled-handover confirmation-read declarations.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

theorem action_time_lt_proposal_of_lt_previous_confirmation
    (S : Setup V) {r : Round} {s : Slot} (hs : 0 < s)
    (h : S.a r < Protocol.confirmation_time S.E (s - 1)) :
    S.a r < Protocol.proposal_time S.E s := by
  rw [Setup.a, Protocol.a_eq_support_cutoff_succ] at h ⊢
  rw [Protocol.confirmation_time_eq_support_cutoff_succ] at h
  have hpred : s - 1 + 1 = s := Nat.sub_add_cancel hs
  rw [hpred] at h
  have hslot : S.hc.opening_slot r + 1 ≤ s :=
    Proofs.Optimistic.slot_le_of_support_cutoff_le S.E (le_of_lt h)
  have hslotPred : S.hc.opening_slot r + 1 ≤ s - 1 := by
    have hne : S.hc.opening_slot r + 1 ≠ s := by
      intro heq
      rw [heq] at h
      exact (lt_irrefl _ h)
    exact Nat.le_sub_one_of_lt (lt_of_le_of_ne hslot hne)
  exact (Proofs.Optimistic.support_cutoff_mono S.E hslotPred).trans_lt
    (by simpa only [hpred] using
      support_cutoff_lt_proposal_time_succ S.E (s - 1))

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
