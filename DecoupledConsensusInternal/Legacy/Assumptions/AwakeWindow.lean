module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.ModelVocabulary.Execution.Admissible

@[expose] public section

/-!
# Honest participation across an SG expiry window

Count a validator once if it is honest and awake at any action in the
window. Compare this honest weight with all faulty weight, not only
with the weight of faulty emitters.
-/

namespace DecoupledConsensusModel
namespace Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The union of honest awake validators across the eligible rounds. -/
def honestAwakeWindow (awake : V → Round → Bool) (Hon : Finset V)
    (etaSG r : Round) : Finset V :=
  Hon.filter (fun v => (Protocol.latest_window etaSG r).any (awake v))

/-- All faulty weight is below the honest awake weight in the window. -/
def AwakeWindowMajority (E : Env V) (awake : V → Round → Bool)
    (Hon : Finset V) (etaSG r : Round) : Prop :=
  E.electorate.weightOf (Finset.univ \ Hon) <
    E.electorate.weightOf (honestAwakeWindow awake Hon etaSG r)

end Execution
end DecoupledConsensusModel

end
