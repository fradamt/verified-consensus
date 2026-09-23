module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Execution.AwakeWindow

@[expose] public section

/-!
# Persistent honest participation in an SG window

This stronger condition is separate from the normal-safety window majority.
It describes participation only; delivery and prefix protection are separate
execution obligations in an asynchrony-resilience proof.
-/

namespace DecoupledConsensusModel
namespace Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Honest validators awake at every action in the SG expiry window. -/
def honestAwakeThroughoutWindow (awake : V → Round → Bool) (Hon : Finset V)
    (etaSG r : Round) : Finset V :=
  Hon.filter (fun v => (Protocol.latest_window etaSG r).all (awake v))

/-- A nonempty window has more continuously awake honest weight than faulty
weight. This does not classify votes from honest validators outside the cohort. -/
def AwakeThroughoutWindowMajority (E : Env V) (awake : V → Round → Bool)
    (Hon : Finset V) (etaSG r : Round) : Prop :=
  Protocol.latest_window etaSG r ≠ [] ∧
    E.electorate.weightOf (Finset.univ \ Hon) <
      E.electorate.weightOf (honestAwakeThroughoutWindow awake Hon etaSG r)

end Execution
end DecoupledConsensusModel

end
