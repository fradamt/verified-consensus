module
public import DecoupledConsensusModel

@[expose] public section

/-! Proof-free quorum vocabulary used by statement-side predicates. -/

namespace DecoupledConsensusModel
namespace Electorate

variable {V : Type} [Fintype V] [DecidableEq V]

/-- §4 a quorum is a validator set of total weight at least `q`
(PROTOCOL.md `sec:state-machine`, "A quorum is a set of validators"). -/
def IsQuorum (E : Electorate V) (S : Finset V) : Prop :=
  E.finalityThreshold ≤ E.weightOf S

end Electorate
end DecoupledConsensusModel

end
