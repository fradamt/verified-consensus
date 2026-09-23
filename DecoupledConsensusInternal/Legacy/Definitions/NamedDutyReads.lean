module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Definitions.ProposalSourcesInternal
public import DecoupledConsensusInternal.Legacy.Definitions.ActionSources

@[expose] public section

/-!
# Named prepared-duty reads 

Named reads in their own namespace `Internal.NamedRecoveryRead`
(`Internal.RecoveryRead` is also the namespace of the inductive
`RecoveryRead`, review finding 8.1); the prior names in `DutyReads.lean`
(`Internal.RecoveryRead.proposalDutyStore`, `voteDutyStore`,
`confirmationInputStore`, `actionDutyStore`) take forwarding bodies to the
erased projections defined here. the prior
bodies rebuilt an erased core store from a named read and re-ran the prior
duties; the named duties run on a prepared node (strict read, clock staged,
cache prepared, and for the action the confirmation duty applied). Each old
name keeps its erased type as `.st.core` of the named read, for consumers
that only read fields; consumers that need the duty's actual input use the
`*Read` forms.
-/


namespace DecoupledConsensusModel.Internal.NamedRecoveryRead
open Execution Proofs.HealingSurface
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The voter's prepared read at the vote time: strict read, clock staged,
cache prepared (the same staging as the confirmation read). -/
def voteDutyRead (S : Setup V) (rho : Run V) (v : V) (s : Slot) : NamedNodeState V :=
  NamedActionReads.confirmationReadAt S rho v (Protocol.vote_time S.E s)

/-- The confirmation duty's prepared input at the confirmation time. -/
def confirmationInputRead (S : Setup V) (rho : Run V) (v : V) (s : Slot) : NamedNodeState V :=
  NamedActionReads.confirmationReadAt S rho v (Protocol.confirmation_time S.E s)

/-- The action's prepared read after the same-tick confirmation duty. -/
def actionDutyRead (S : Setup V) (rho : Run V) (v : V) (r : Round) : NamedNodeState V :=
  actionReadAt S rho v r

end DecoupledConsensusModel.Internal.NamedRecoveryRead

end
