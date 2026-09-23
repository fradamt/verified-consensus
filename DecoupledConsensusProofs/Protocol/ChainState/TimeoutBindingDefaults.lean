module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusModel.Protocol.ChainState
public import DecoupledConsensusProofs.Protocol.ChainState.Chain

@[expose] public section

/-! Proofs for the identity TimeoutBinding and the leaf
adapter's field behavior. No named timeout instance or wire runtime is used. -/
namespace DecoupledConsensusModel.Proofs.TimeoutBindingDefaults
open Protocol


section Processing
variable {V Row : Type} [DecidableEq V]



/-- Finality processing is independent of the interpreted height pair. In
particular, erasing a height contribution does not erase its finality vote. -/
theorem process_finality_eq_base (binding : TimeoutBinding V Row)
    (st : ChainState V) (row : Row) :
    (process_attestation_with binding st row).finalize =
      (process_attestation st (binding.base row)).finalize := by
  simp only [process_attestation_with, Protocol.process_attestation_finalize, TimeoutBinding.view]

/-- Reuse the existing processor's structural field theorem. -/
theorem process_context_fields (binding : TimeoutBinding V Row)
    (st : ChainState V) (row : Row) :
    (process_attestation_with binding st row).L = st.L ∧
    (process_attestation_with binding st row).h = st.h ∧
    (process_attestation_with binding st row).T_h = st.T_h ∧
    (process_attestation_with binding st row).J = st.J ∧
    (process_attestation_with binding st row).h_j = st.h_j ∧
    (process_attestation_with binding st row).F = st.F ∧
    (process_attestation_with binding st row).h_F = st.h_F :=
  Protocol.process_attestation_fields st (binding.view st row)


end Processing

#print axioms process_finality_eq_base
#print axioms process_context_fields
end DecoupledConsensusModel.Proofs.TimeoutBindingDefaults

end
