module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.StableRecordPreparedV4

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Public stable-record safety assembly -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Statements

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The closed GST-zero field of the public stable-record statement. -/
theorem stableRecordSafety_gstZero_clean (S : Setup V) :
    ∀ rho, WeakGenesis S rho → StableRecordCanonicalFrom S rho 0 := by
  intro rho h
  exact WeakGenesis.stableRecordCanonicalFrom_of_weakGenesis S h

/-- Public stable-record safety, prebuilt over the bounded-phase after-GST
field until its complete producer lands. -/
theorem stableRecordSafety_holds_of_pins
    (S : Setup V)
    (hafter : ∀ rho rGST gap extra n,
      StrongRecoveryPrefix S rho rGST gap extra n →
      ∃ m, n ≤ m ∧ m ≤ n + gap ∧
        ∀ rho', WeakContinuation S rho rho' (n + gap) →
          StableRecordCanonicalFrom S rho' (healingBoundaryTime S m)) :
    StableRecordSafety S :=
  ⟨stableRecordSafety_gstZero_clean S, hafter⟩

#print axioms stableRecordSafety_gstZero_clean
#print axioms stableRecordSafety_holds_of_pins

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
