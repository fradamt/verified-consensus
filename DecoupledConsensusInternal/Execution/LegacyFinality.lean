module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.ModelVocabulary.Execution.Run
public import DecoupledConsensusModel.Protocol.ChainState

@[expose] public section

/-!
# The finalized-root fact used at a safety handover

This property covers certificates held at any honest read in the run,
including certificates that arrive after handover. It compares their
finalized roots with one fixed block, not with future honest heads.
-/

namespace DecoupledConsensusModel
namespace Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every full named certificate held by an honest reader with finalized
height at most `cap` finalizes an ancestor of the fixed handover block `P`.
The bound and finalized value use actual named derivation, not derivation of
an erased block. The property name is retained for its existing callers. -/
def FinalizedRootsBelowAtRead (S : Setup V) (rho : Run V)
    (cap : Height) (P : Block V) : Prop :=
  ∀ v ∈ rho.honest, ∀ t : Time, ∀ C ∈ (rho.storeBeforeTime S v t).bodies,
    (Protocol.derive_named S.E S.cfg C).h_F ≤ cap →
      Block.Preceq (Protocol.derive_named S.E S.cfg C).F P

end Execution
end DecoupledConsensusModel

end
