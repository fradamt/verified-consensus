module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.ModelVocabulary.Execution.Run

@[expose] public section

/-! # Profile-independent confirmation score and gate 
Byte-identical extraction of the five pure GF definitions from
`Confirmation.lean` so that the named confirmation walk and the prior owner
share one leaf without a cycle. -/


namespace DecoupledConsensusModel
namespace Internal
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The resolved early vote set of the Section 7 confirmation evaluation. -/
def confirmationEarly (E : Env V) (st : Protocol.Store V) (s : Slot) :
    Finset (GoldfishVote V) :=
  beforeCutoff st.tau (Protocol.support_cutoff E s) (st.pool s)

/-- The receipt-time late vote set of the Section 7 confirmation evaluation. -/
def confirmationLate (E : Env V) (st : Protocol.Store V) (s : Slot) :
    Finset (GoldfishVote V) :=
  beforeCutoff st.timestamp_vote (Protocol.confirmation_time E s) (st.pool s)

/-- The non-equivocating support numerator of the confirmation evaluation. -/
def confirmationVotes (E : Env V) (st : Protocol.Store V) (s : Slot) :
    Finset (GoldfishVote V) :=
  (confirmationEarly E st s).filter
    (fun u => Protocol.no_second_vote_in (confirmationLate E st s) u = true)

/-- The exact Section 7 confirmation score. -/
def confirmationScore (E : Env V) (st : Protocol.Store V) (s : Slot)
    (B : Block V) : Nat :=
  Protocol.goldfish_score E st.T (confirmationVotes E st s)
    (confirmationVotes E st s) s B

/-- The exact Section 7 confirmation gate. -/
def confirmationEligible (E : Env V) (st : Protocol.Store V) (s : Slot)
    (B : Block V) : Bool :=
  decide (Protocol.voters_count E (confirmationLate E st s) s <
    2 * confirmationScore E st s B)

end Internal
end DecoupledConsensusModel

end
