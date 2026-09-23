module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusModel.Protocol.ChainState
public import DecoupledConsensusProofs.Protocol.ChainState.TimeoutBindingDefaults
public import DecoupledConsensusModel.Protocol.ChainState

@[expose] public section

/-! Targeted-row leaf proofs. They cover matching and E1/E2,
not named blocks, signing-record history, actual emissions or progress lags.
No activity bit or extra accountability target is introduced. -/
namespace DecoupledConsensusModel.Proofs.TargetedTimeoutBinding
open Protocol
variable {V : Type}



section Processing
variable [DecidableEq V]

/-- The concrete processor has one match test for progress. Only a proper
(false-flag) target can also enter target_participation. -/
theorem process_height_fields (st : ChainState V) (row : NamedAttestation V) :
    (process_attestation_with (TimeoutBinding.targeted V) st row).progress =
      (if row.height_pair.matchesEntry st.h st.T_h.root then insert row.val_index st.progress
        else st.progress) ∧
    (process_attestation_with (TimeoutBinding.targeted V) st row).target_participation =
      (if row.height_pair.matchesEntry st.h st.T_h.root && row.height_pair.properTarget then
        insert row.val_index st.target_participation else st.target_participation) := by
  cases hp : row.height_pair with
  | empty =>
    simp [process_attestation_with, TimeoutBinding.targeted, TimeoutBinding.view,
      TimeoutBinding.targetedHeightPair, NamedAttestation.erase, NamedHeightPair.matchesEntry,
      NamedHeightPair.erase, NamedHeightPair.properTarget, hp,
      Protocol.process_attestation_progress, Protocol.process_attestation_target_participation]
  | vote h entry timeout =>
    by_cases hm : h = st.h ∧ entry = st.T_h.root
    · rcases hm with ⟨rfl, rfl⟩
      cases timeout <;>
        simp [process_attestation_with, TimeoutBinding.targeted, TimeoutBinding.view,
          TimeoutBinding.targetedHeightPair, NamedAttestation.erase, NamedHeightPair.matchesEntry,
          NamedHeightPair.erase, NamedHeightPair.properTarget, hp,
          Protocol.process_attestation_progress, Protocol.process_attestation_target_participation]
    · cases timeout <;>
        simp [process_attestation_with, TimeoutBinding.targeted, TimeoutBinding.view,
          TimeoutBinding.targetedHeightPair, NamedAttestation.erase, NamedHeightPair.matchesEntry,
          NamedHeightPair.erase, NamedHeightPair.properTarget, hp, hm,
          Protocol.process_attestation_progress, Protocol.process_attestation_target_participation]

theorem process_finality_eq (st : ChainState V) (row : NamedAttestation V) :
    (process_attestation_with (TimeoutBinding.targeted V) st row).finalize =
      (process_attestation st row.erase).finalize :=
  TimeoutBindingDefaults.process_finality_eq_base (TimeoutBinding.targeted V) st row



end Processing



#print axioms process_height_fields
#print axioms process_finality_eq
end DecoupledConsensusModel.Proofs.TargetedTimeoutBinding

end
