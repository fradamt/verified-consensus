module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.W4GSTZeroStableGrowthLagged
public import DecoupledConsensusProofs.Execution.W4StableRecordGrowthPreparedClosed

@[expose] public section

/-! # Complete stable-record growth field
The GST-zero branch is the lagged prepared proof. The after-GST branch is the
closed prepared-V4 composer. This leaf only assembles the two exact frozen
branches into `StableRecordGrowth`. -/

namespace DecoupledConsensusModel
namespace Proofs

open Internal Execution Statements

variable {V : Type} [DecidableEq V] [Fintype V]

theorem stableRecordGrowth_closed (S : Setup V) :
    StableRecordGrowth S :=
  W4StableWrite.stableRecordGrowth_of_gstZeroPreparedClosed S
    (stableRecordGrowth_gstZero_lagged S)

#print axioms stableRecordGrowth_closed

end Proofs
end DecoupledConsensusModel

end
