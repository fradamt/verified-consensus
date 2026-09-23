module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.Ancestry
public import DecoupledConsensusInternal.Legacy.Definitions.NestedOutputs

@[expose] public section

/-! # The three user-facing chains nest, by construction

Addendum 34 22. `Protocol/Confirmed.lean` carries the two accessors but
no theorem, because `Block.preceq_self` and `Block.preceq_trans` belong to
`DecoupledConsensusProofs.Ancestry`, which the model layer cannot import.
Each step is one branch split on the accessor: the positive branch returns the
stored record, which the branch condition already puts above the lower chain;
the negative branch returns the lower chain itself. -/



namespace DecoupledConsensusModel
namespace Proofs
namespace NestedOutputs

open Internal Execution

variable {V : Type} [DecidableEq V]

/-- Finality reaches the stable output, for an arbitrary store. -/
theorem finalized_preceq_get_stable (st : Protocol.Store V) :
    Block.Preceq st.F (Protocol.get_stable st) := by
  unfold Protocol.get_stable
  split
  · assumption
  · exact Block.preceq_self _

/-- The stable output reaches the confirmed output, for an arbitrary store. -/
theorem get_stable_preceq_get_confirmed (st : Protocol.Store V) :
    Block.Preceq (Protocol.get_stable st) (Protocol.get_confirmed st) := by
  unfold Protocol.get_confirmed
  split
  · assumption
  · exact Block.preceq_self _


variable [Fintype V]

/-- The earlier result holds with no hypothesis at all: it is a property of the
two accessors, at every read of every node in every named run. -/
theorem nestedOutputs_holds (S : Setup V) : Internal.NestedOutputs S := by
  intro rho v t
  exact ⟨finalized_preceq_get_stable _, get_stable_preceq_get_confirmed _⟩

end NestedOutputs
end Proofs
end DecoupledConsensusModel

end
