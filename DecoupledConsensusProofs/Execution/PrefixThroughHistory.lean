module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.NamedOutageEntry
public import DecoupledConsensusModel.Protocol.Duties.Proposals
public import DecoupledConsensusProofs.ModelVocabulary.Execution.NamedReceiptCalls

@[expose] public section

open DecoupledConsensusModel
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Protocol

namespace DecoupledConsensusModel.Internal.NamedOutageEntry.History
variable {V : Type} [DecidableEq V] [Fintype V]

/-- PROPOSED precise completion of the index-cut wording in 1602.
Includes the empty and terminal prefixes and strict-read prefixes whose
next event is later than t. Not yet an approved interpretation. -/
def PrefixThrough (rho : NamedRun V) (i : Nat) (t : Time) : Prop :=
  i ≤ rho.events.length ∧
    ∀ j : Nat, j < i → ∀ e : NamedEvent V,
      rho.events[j]? = some e → e.time ≤ t



end DecoupledConsensusModel.Internal.NamedOutageEntry.History

end
