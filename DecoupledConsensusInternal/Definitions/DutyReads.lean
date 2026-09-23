module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.NamedDutyReads

@[expose] public section

/-! Compatibility import for the named prepared-duty read definitions. -/

namespace DecoupledConsensusModel.Internal.RecoveryRead
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

def proposalDutyStore (S : Setup V) (rho : Run V) (s : Slot) : Protocol.Store V :=
  NamedRecoveryRead.proposalDutyStore S rho s

def voteDutyStore (S : Setup V) (rho : Run V) (v : V) (s : Slot) : Protocol.Store V :=
  NamedRecoveryRead.voteDutyStore S rho v s

def confirmationInputStore (S : Setup V) (rho : Run V) (v : V) (s : Slot) : Protocol.Store V :=
  NamedRecoveryRead.confirmationInputStore S rho v s

def actionDutyStore (S : Setup V) (rho : Run V) (v : V) (r : Round) : Protocol.Store V :=
  NamedRecoveryRead.actionDutyStore S rho v r

end DecoupledConsensusModel.Internal.RecoveryRead

end
