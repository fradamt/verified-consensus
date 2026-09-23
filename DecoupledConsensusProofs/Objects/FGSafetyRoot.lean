module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.HeightRegimeNamedClosed
public import DecoupledConsensusProofs.Protocol.ChainState.FGRootWitness

@[expose] public section

/-!
# FG roots after the safety deadline

A selected FG root is genesis or the witness of an earlier honest target
row. The height regimes therefore connect root selection to the protected
Goldfish and SG histories. Roots can extend an older checkpoint; the
conclusion is compatibility, not a bound below one fixed checkpoint.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.Optimistic
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

/-- An action strictly before a slot's confirmation has already reached
its first interior slot. Equality at the confirmation tick is excluded. -/
theorem firstInterior_le_of_action_lt_confirmation
    (S : Setup V) {r : Round} {s : Slot}
    (hact : S.a r < Protocol.confirmation_time S.E s) :
    S.hc.opening_slot r + 1 ≤ s := by
  by_contra hn
  have hslot : s ≤ S.hc.opening_slot r :=
    Nat.le_of_lt_succ (Nat.lt_of_not_ge hn)
  have hmono : Protocol.confirmation_time S.E s ≤
      Protocol.confirmation_time S.E (S.hc.opening_slot r) := by
    unfold Protocol.confirmation_time
    exact Int.add_le_add_right (proposal_time_mono S.E hslot) _
  change Protocol.confirmation_time S.E (S.hc.opening_slot r) <
    Protocol.confirmation_time S.E s at hact
  exact (not_lt_of_ge hmono) hact

#print axioms firstInterior_le_of_action_lt_confirmation






end HealingSurface
end Proofs
end DecoupledConsensusModel

end
