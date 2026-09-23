module
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Pairs
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Blocks
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Time
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Weights
public import DecoupledConsensusModel.Objects.Parameters
public import DecoupledConsensusModel.Objects.Blocks
public import DecoupledConsensusModel.Objects.Time
public import DecoupledConsensusModel.Objects.Weights

@[expose] public section

/-!
# §1 Protocol environment

The fixed data every section reads: the validator set (as the type `V`), the
schedule unit `Δ`, `t_GST`, the per-slot proposer and committee oracles, and the
weighted electorate (PROTOCOL.md `sec:substrate`, `sec:sg-schedule`).

`Δ` is a schedule constant unconditionally; only the delivery guarantee is
conditional on `t_GST` (F1.4), so nothing here mentions delivery. `R`, `η_SG`,
`K` and `D` are not here: they enter with §3 and §4.
-/

namespace DecoupledConsensusModel

namespace Env

variable {V : Type} [DecidableEq V] [Fintype V] (E : Env V)

/-- §6 `m = ⌊W/2⌋ + 1`. -/
def m : Nat :=
  E.electorate.strictMajorityThreshold

end Env

end DecoupledConsensusModel

end
