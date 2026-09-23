module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Definitions.ConfirmationScore

@[expose] public section

/-! Proof-side confirmation-score helpers outside `Statements.Consensus`. -/
namespace DecoupledConsensusModel.Internal
variable {V : Type} [DecidableEq V] [Fintype V]

/-- §7.2 `count`: the denominator of the confirmation evaluation. -/
def confirmationCount (E : Env V) (st : Protocol.Store V) (s : Slot) : Nat :=
  Protocol.voters_count E (confirmationLate E st s) s

end DecoupledConsensusModel.Internal

end
