module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Assumptions.AwakeWindow
public import DecoupledConsensusProofs.Objects.Weights

@[expose] public section

namespace DecoupledConsensusModel.Proofs.AwakeWindowQuorum

open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

theorem faulty_weight_lt_quorum (E : Env V) (awake : V → Round → Bool)
    (Hon : Finset V) (etaSG r : Round)
    (h : AwakeWindowMajority E awake Hon etaSG r) :
    E.electorate.weightOf (Finset.univ \ Hon) < E.q := by
  unfold AwakeWindowMajority at h
  have hsubset : honestAwakeWindow awake Hon etaSG r ⊆ Hon :=
    Finset.filter_subset _ _
  have hhonest :
      E.electorate.weightOf (Finset.univ \ Hon) < E.electorate.weightOf Hon :=
    lt_of_lt_of_le h (E.electorate.weightOf_mono hsubset)
  have hsum := E.electorate.weightOf_add_weightOf_sdiff Hon
  unfold Env.q Electorate.finalityThreshold
  omega

end DecoupledConsensusModel.Proofs.AwakeWindowQuorum

end
