module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore

@[expose] public section

/-!
# Low action/confirmation store projections

The Section 7 round action is the opening slot's confirmation tick. This file
records the exact store equality and the fields that confirmation leaves
unchanged. It has no recovery or suffix dependency.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The exact action store is the opening confirmation store followed by the
confirmation write for that opening slot. The action's own read supplies the
grade contract: the named action read prepares its cache from the same
confirmation-time read that `Proofs.Optimistic.confStore` reconstructs, so the two
sides name the same store literally, and only the slot index needs the usual
`a_r` alignment. -/
theorem actionStoreAt_eq_update_confirmation_openingConfStore
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    (actionStoreAt S rho v r).st.core =
      Protocol.update_confirmation_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadAt S rho v (S.a r)).cache)
        S.E S.hc
        (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r))
        (S.hc.opening_slot r) := by
  have hsc : S.a r =
      Protocol.support_cutoff S.E (S.hc.opening_slot r + 1) :=
    Protocol.a_eq_support_cutoff_succ S.hc S.E r
  have hslot : S.E.slotOf (S.a r) = S.hc.opening_slot r + 1 := by
    rw [hsc]
    exact Proofs.Optimistic.slotOf_support_cutoff S.E _
  have hidx : S.E.slotOf (S.a r) - 1 = S.hc.opening_slot r := by
    rw [hslot]; simp
  rw [Proofs.Optimistic.confStore_eq_confirmationInputRead]
  show (Protocol.NamedDuties.update_confirmation_with
      (NamedProfile.gradeContract
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBeforeTime S rho (S.a r) v) (S.a r)).cache)
      S.E S.hc
      (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBeforeTime S rho (S.a r) v) (S.a r)).st
      (S.E.slotOf (S.a r) - 1)).core = _
  rw [hidx]
  rfl


/-- The confirmation write does not change the FG root read at the action. -/
theorem actionStoreAt_fgRoot_eq_openingConfStore
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    Protocol.get_fg_root
        (actionStoreAt S rho v r).toHealing.toFG =
      Protocol.get_fg_root
        (Proofs.Optimistic.confStore S rho v
          (S.hc.opening_slot r)).toHealing.toFG := by
  show Protocol.get_fg_root (actionStoreAt S rho v r).st.core.toHealing.toFG = _
  rw [actionStoreAt_eq_update_confirmation_openingConfStore]
  rfl

/-- The confirmation write does not change the filtered block tree read at the
round action. -/
theorem actionStoreAt_filteredTree_eq_openingConfStore
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    Protocol.get_filtered_block_tree
        (actionStoreAt S rho v r).toHealing.toFG =
      Protocol.get_filtered_block_tree
        (Proofs.Optimistic.confStore S rho v
          (S.hc.opening_slot r)).toHealing.toFG := by
  show Protocol.get_filtered_block_tree
      (actionStoreAt S rho v r).st.core.toHealing.toFG = _
  rw [actionStoreAt_eq_update_confirmation_openingConfStore]
  rfl

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
