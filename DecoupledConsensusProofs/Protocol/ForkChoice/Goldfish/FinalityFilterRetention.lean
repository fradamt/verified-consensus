module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FinalityFilterInterference
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ReaderLocalCone
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HonestMajorityCore
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionHistory
public import DecoupledConsensusProofs.Generic.SuffixHistory
public import DecoupledConsensusProofs.Protocol.Handlers.StoreFinality
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.ChainState.JustificationCertificates
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Protocol.Grades.ProposalParent
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordClean
public import DecoupledConsensusProofs.Generic.EvaluationStore
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Objects.EmittedHeightBound
public import DecoupledConsensusProofs.Execution.ReleasedCertificateHeightProgress
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecoveryTimeout
public import DecoupledConsensusProofs.Execution.RecoveryGradeProcessedRead
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsProducers

@[expose] public section

/-!
# Finality-filter retention

This proof-only interface names the stronger branch of a full finality-filter
read: the protected block itself remains in the actual filtered tree. Such a
read is automatically noninterfering, and its membership also exposes the
actual finality-root ordering.

The bounded-height producers below use a processed block at or above the
protected floor as the reader-local cone witness. This supplies the height
filter part of retention; the actual `get_fg_root` ordering supplies the other
part. These producers permit the local `H` to `H + 1` catch-up allowed by
their cap. They are not literal height-stall statements.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The protected block is retained by the actual filtered tree at one
protocol read. -/
def FinalityFilterRetainedAtRead
    (S : Setup V) (rho : Run V) (w : V) (read : Time)
    (P : Block V) : Prop :=
  P ∈ Protocol.get_filtered_block_tree
    (rho.storeBeforeTime S w read).toHealing.toFG



/-- Retention is the filtered-tree branch of full finality-filter
noninterference. -/
theorem FinalityFilterRetainedAtRead.finalityFilterNoninterference
    (S : Setup V) {rho : Run V} {w : V} {read : Time} {P : Block V}
    (h : FinalityFilterRetainedAtRead S rho w read P) :
    FinalityFilterNoninterferenceAtRead S rho w read P := by
  exact Or.inr h


/-- Membership in the actual filtered tree exposes the actual selected
finality root below the retained block. -/
theorem FinalityFilterRetainedAtRead.get_fg_root_preceq
    (S : Setup V) {rho : Run V} {w : V} {read : Time} {P : Block V}
    (h : FinalityFilterRetainedAtRead S rho w read P) :
    Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w read).toHealing.toFG) P := by
  exact Proofs.Records.preceq_get_fg_root_of_mem_filtered h





end HealingSurface
end Proofs
end DecoupledConsensusModel

end
