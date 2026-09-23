module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.DutyReads
public import DecoupledConsensusInternal.Availability

@[expose] public section

/-!
# Exact recovery reads

This module names the four handler reads used by causal recovery. Every store
starts from the strict pre-time state (`Run.storeBeforeTime`). Proposal, vote,
and confirmation name the store before their handler mutates it. An action
names the store after the confirmation update that runs at the same tick.
-/

namespace DecoupledConsensusModel
namespace Internal

open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A concrete scheduled read that can affect recovery.

Proposal reads are indexed by their duty slot; the setup determines their sole
reader. Vote and confirmation reads also name the validator. Action reads are
indexed by validator and round. -/
inductive RecoveryRead (V : Type) where
  | proposal (slot : Slot)
  | vote (validator : V) (slot : Slot)
  | confirmation (validator : V) (slot : Slot)
  | action (validator : V) (round : Round)
deriving DecidableEq

namespace RecoveryRead

/-- The validator that performs the read. -/
def reader (x : RecoveryRead V) (S : Setup V) : V :=
  match x with
  | .proposal s => S.E.proposer s
  | .vote v _ => v
  | .confirmation v _ => v
  | .action v _ => v

/-- The exact public time of the read. -/
def readTime (x : RecoveryRead V) (S : Setup V) : Time :=
  match x with
  | .proposal s => Protocol.proposal_time S.E s
  | .vote _ s => Protocol.vote_time S.E s
  | .confirmation _ s => Protocol.confirmation_time S.E s
  | .action _ r => S.a r

/-- The exact handler-staged store read by `x`. In particular, confirmation is
pre-update while action is post-update, even when their times coincide. -/
def store (x : RecoveryRead V) (S : Setup V) (rho : Run V) : Protocol.Store V :=
  match x with
  | .proposal s => proposalDutyStore S rho s
  | .vote v s => voteDutyStore S rho v s
  | .confirmation v s => confirmationInputStore S rho v s
  | .action v r => actionDutyStore S rho v r

/-- The natural schedule index carried by a read: a slot for the three slot
duties and a round for an action. -/
def index (x : RecoveryRead V) : Nat :=
  match x with
  | .proposal s => s
  | .vote _ s => s
  | .confirmation _ s => s
  | .action _ r => r

/-- The positive-slot guards that occur in `on_tick`.

Proposal and vote handlers require their duty slot to be positive. A
confirmation indexed by slot `s` runs in slot `s + 1`, whose positivity is
automatic. The action handler has no positive-slot guard. -/
def handlerSlotPositive (x : RecoveryRead V) : Prop :=
  match x with
  | .proposal s => 0 < s
  | .vote _ s => 0 < s
  | .confirmation _ _ => True
  | .action _ _ => True

end RecoveryRead

/-- A recovery read in the half-open time window `[lo, hi)`.

The lower bound is inclusive, the upper bound is strict, and the run horizon is
inclusive. The last clause is exactly the positive-slot condition of the
corresponding handler; it adds no guard to confirmation or action reads. -/
def RecoveryReadBetween (S : Setup V) (rho : Run V) (lo hi : Time)
    (x : RecoveryRead V) : Prop :=
  x.reader S ∈ rho.honest ∧
    lo ≤ x.readTime S ∧
    x.readTime S < hi ∧
    x.readTime S ≤ rho.horizon ∧
    x.handlerSlotPositive

end Internal
end DecoupledConsensusModel

end
