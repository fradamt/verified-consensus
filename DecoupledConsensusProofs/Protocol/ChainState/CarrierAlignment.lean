module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.CarrierFirst
public import DecoupledConsensusProofs.Protocol.Grades.LifecycleActionSource
public import DecoupledConsensusProofs.Protocol.ChainState.RecurringFinality
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Carrier parent alignment

This module reduces the two carrier parent equalities to Goldfish cone
orientation. The strict parent-slot guard makes a block from the immediately
previous slot terminal in the next proposal store.

The lifecycle records excludes current-round action rows from the `+1` proposal,
but it does not exclude an older partial honest batch from becoming a progress
quorum after faulty rows arrive. `CarrierPlusOneNoHeightEventAt` names that
remaining transition-level residual.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]






/-- Open: the two Goldfish orientation facts needed for the `+1` and `+2`
proposal parents. Slot terminality converts these ancestry facts to equalities.
The lifecycle records names the opening votes, but it does not contain the next
slot's frozen-vote transfer needed to derive both cones. -/
structure CarrierParentConesAt
    (S : Setup V) (rho : Run V) (q : Round) (B0 : NamedBlock V) : Prop where
  plusOneCone : Block.Preceq B0.erase
    (proposedParent S rho (S.hc.opening_slot q + 1))
  plusTwoCone : ∀ P1 : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot q + 1) = some P1 →
    Block.Preceq P1.erase
      (proposedParent S rho (S.hc.opening_slot q + 2))








end HealingSurface
end Proofs

end DecoupledConsensusModel

end
