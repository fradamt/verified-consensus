module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusModel.Protocol.ValidatorClient
public import DecoupledConsensusProofs.Protocol.ChainState.TargetedTimeoutBinding
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordCore
public import DecoupledConsensusProofs.Protocol.ValidatorClient.SlashableBound

@[expose] public section

/-! Named-record/client proofs. History validity is produced from
initialization and signing calls. No network runtime, arbitrary-record safety,
source-selection history, activity field or new standing premise is asserted. -/
namespace DecoupledConsensusModel.Proofs.NamedRecord
open Protocol
open Protocol.NamedRecord
open Proofs.HealingSurface
open Proofs.Records (LockCompatible)
variable {V : Type}

/-- The compatibility pair rule supplies the codec's source-field consistency. -/
theorem encode_height_erase (record : Record)
    (fields : Option (Height × BlockId × Bool)) (fp : Option FinalityPair) :
    (encodeHeight fields (height_pair record fields fp)).erase =
      height_pair record fields fp := by
  rcases Proofs.Engine.height_pair_cases (Λ := record) fields fp with he | ⟨h, entry, nu, hf, hp⟩
  · simp [encodeHeight, he, NamedHeightPair.erase]
  · rcases hp with ht | ht <;> rw [ht, hf] <;> rfl

/-- Every field of the named output erases to the exact old client output. -/
theorem create_erases (record : Protocol.NamedRecord) (input : Input V) :
    (create record input).2.erase = (legacyCreate record.legacy input).2 := by
  simp only [create, legacyCreate, create_attestation, encodeRow, NamedAttestation.erase,
    encode_height_erase]


/-- Useful update equation expressed on the exact named row just emitted. -/
theorem create_legacy_records_erasure (record : Protocol.NamedRecord) (input : Input V) :
    (create record input).1.legacy =
      record_attestation record.legacy (create record input).2.erase := by
  rw [create_erases]
  rfl

/-- A named nonempty output names the actual supplied source fields. -/
theorem create_names_source (record : Protocol.NamedRecord) (input : Input V)
    {h : Height} {entry : BlockId} {timeout : Bool}
    (hp : (create record input).2.height_pair = .vote h entry timeout) :
    ∃ nu, input.fields = some (h, entry, nu) := by
  cases hf : input.fields with
  | none => simp [create, legacyCreate, create_attestation, encodeRow, encodeHeight,
      height_pair, hf] at hp
  | some fields =>
    obtain ⟨k, target, nu⟩ := fields
    cases hpair : (legacyCreate record.legacy input).2.height_pair <;>
      simp [create, encodeRow, encodeHeight, hf, hpair] at hp
    all_goals
      obtain ⟨rfl, rfl, _⟩ := hp
      exact ⟨nu, rfl⟩

/-- A raw timeout update is either old history or this emitted timeout. -/
private theorem timeout_update_iff (record : Record) (row : CombinedAttestation V) (h : Height) :
    (record_attestation record row).timeout h = true ↔
      record.timeout h = true ∨ row.height_pair = .timeout h := by
  constructor
  · intro hpost
    by_cases hpre : record.timeout h = true
    · exact Or.inl hpre
    · exact Or.inr (record_attestation_timeout_introduced
        (Bool.eq_false_of_not_eq_true hpre) hpost)
  · rintro (hpre | hp)
    · exact record_attestation_timeout_mono row hpre
    · exact record_attestation_timeout_true record row hp

/-- The pair-history update represents the same height-wide timeout event. -/
theorem remember_timeout_height_iff (history : Finset (Height × BlockId))
    (pair : NamedHeightPair) (h : Height) :
    (∃ entry, (h, entry) ∈ rememberTimeout history pair) ↔
      (∃ entry, (h, entry) ∈ history) ∨ pair.erase = .timeout h := by
  cases pair with
  | empty => simp [rememberTimeout, NamedHeightPair.erase]
  | vote k entry timeout =>
    cases timeout <;>
      simp [rememberTimeout, NamedHeightPair.erase, Prod.mk.injEq, exists_or, eq_comm, or_comm]

/-- Internal consistency of the height-wide E1 flag and finite pair history. -/
def HistoryConsistent (record : Protocol.NamedRecord) : Prop :=
  ∀ h, record.legacy.timeout h = true ↔ ∃ entry, (h, entry) ∈ record.timeoutHistory

/-- Initialization has no height-wide flag or pair-history entry. -/
theorem history_consistent_initial : HistoryConsistent Protocol.NamedRecord.initial := by
  simp [HistoryConsistent, Protocol.NamedRecord.initial, Record.initial]

/-- An actual signing call preserves exact flag/history correspondence. -/
theorem history_consistent_create (record : Protocol.NamedRecord) (input : Input V)
    (hconsistent : HistoryConsistent record) : HistoryConsistent (create record input).1 := by
  intro h
  change (create record input).1.legacy.timeout h = true ↔
    ∃ entry, (h, entry) ∈ rememberTimeout record.timeoutHistory (create record input).2.height_pair
  rw [create_legacy_records_erasure, timeout_update_iff, remember_timeout_height_iff]
  change (record.legacy.timeout h = true ∨
    (create record input).2.height_pair.erase = .timeout h) ↔ _
  exact or_congr (hconsistent h) Iff.rfl

/-- No separate named lock policy is introduced. -/
theorem lock_compatible_create (record : Protocol.NamedRecord) (input : Input V)
    (hlock : LockCompatible record.legacy) : LockCompatible (create record input).1.legacy := by
  exact lockCompatible_create_attestation hlock input.val_index input.round input.confirmed
    input.fields input.h_j input.J input.h_F















#print axioms encode_height_erase
#print axioms create_erases
#print axioms create_legacy_records_erasure
#print axioms create_names_source
#print axioms remember_timeout_height_iff
#print axioms history_consistent_initial
#print axioms history_consistent_create
#print axioms lock_compatible_create
end DecoupledConsensusModel.Proofs.NamedRecord

end
