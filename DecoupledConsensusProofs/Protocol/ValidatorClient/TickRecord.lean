module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.NamedTick
public import DecoupledConsensusProofs.Protocol.ValidatorClient.Record

@[expose] public section

/-! Local named-record history and lock invariants for the actual named
tick result. The final attestation branch is the only record writer. -/
namespace DecoupledConsensusModel.Proofs.NamedTickRecord
variable {V : Type} [DecidableEq V] [Fintype V]

def Invariant (record : Protocol.NamedRecord) : Prop :=
  NamedRecord.HistoryConsistent record ∧ Proofs.Records.LockCompatible record.legacy

omit [DecidableEq V] [Fintype V] in
theorem invariant_initial : Invariant Protocol.NamedRecord.initial :=
  ⟨NamedRecord.history_consistent_initial, Proofs.Records.lockCompatible_initial⟩

/-- The actual duty calls the fixed creator on the shared computed read. -/
theorem invariant_attest (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (h : Invariant record) :
    Invariant (Protocol.NamedDuties.attest_with gc E hc nd st record).2.1 := by
  change Invariant (Protocol.NamedActions.round_action_with gc E hc nd st.core.toHealing record).1
  rw [Proofs.NamedActions.round_action_shared_read]
  exact ⟨NamedRecord.history_consistent_create record _ h.1,
    NamedRecord.lock_compatible_create record _ h.2⟩

/-- All stages and the final action store are those computed by NamedTick.
The record is either unchanged or is the actual final duty's returned record. -/
theorem invariant_tick (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time)
    (h : Invariant record) :
    Invariant (Protocol.NamedTick.tick gc E hc cfg nd st record t).2.1 := by
  rw [NamedTick.tick_computed_duties]
  dsimp only
  split_ifs <;> first
    | exact h
    | exact invariant_attest gc E hc nd _ record h



#print axioms invariant_initial
end DecoupledConsensusModel.Proofs.NamedTickRecord

end
