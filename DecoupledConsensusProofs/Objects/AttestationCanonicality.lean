module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Canonicality
public import DecoupledConsensusProofs.Protocol.Grades.HonestMajority
public import DecoupledConsensusProofs.Protocol.ValidatorClient.FinalityPairCore
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordClean

@[expose] public section

/-!
# GST-zero attestation canonicality

`Canonicality.lean` states the history that protects `get_fg_root`. This file
proves the local producer at one honest round action. A height-pair target is
read from the derived state of either an ancestor of the node's confirmation or
the selected grade-2 block. If both possible sources are compatible with an
existing confirmed block, the emitted target is compatible with it too.

The proof keeps the selected source's tree membership. `Proofs.Engine.round_action_gated`
intentionally hides that fact because its quorum consumers need only the source
height; target-history induction needs membership so that derived-state
agreement and collision-free roots can identify the target block.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]





omit [Fintype V] in
/-- Moving upward from a block that precedes a compatible block preserves
compatibility with the fixed reference. -/
theorem compatible_of_preceq_of_compatible {A C B : Block V}
    (hAC : Block.Preceq A C) (hCB : Block.compatible C B = true) :
    Block.compatible A B = true := by
  simp only [Block.compatible, Bool.or_eq_true] at hCB ⊢
  rcases hCB with hCB | hBC
  · exact Or.inl (Block.preceq_trans hAC hCB)
  · simpa only [Block.compatible, Bool.or_eq_true] using
      (Block.compatible_of_preceq_common hAC hBC)


/-! ## The SG-vote projection -/


/-! ## Both targets emitted by one round action -/








#print axioms compatible_of_preceq_of_compatible

end Protocol
end DecoupledConsensusModel

end
