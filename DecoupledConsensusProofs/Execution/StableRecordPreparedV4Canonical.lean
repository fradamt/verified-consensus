module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.StableRecordPreparedV4Complete

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Canonical stable-record wire for the prepared V4 producer -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Statements

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Wire the complete prepared V4 producer into the available canonical-record
assembler. -/
theorem stableRecordSafety_afterGST_preparedV4_canonical_of_pins
    (S : Setup V)
    (hprepared : ∀ rho rGST gap extra n,
      StrongRecoveryPrefix S rho rGST gap extra n →
      ∃ m, n ≤ m ∧ m ≤ n + gap ∧
        ∀ rho', WeakContinuation S rho rho' (n + gap) →
          ∃ cut P,
            PhaseShiftSafety S rho' cut (S.hc.opening_slot m) P ∧
            (∀ u ∈ rho'.honest, ∀ v ∈ rho'.honest, ∀ t t',
              Protocol.confirmation_time S.E (S.hc.opening_slot m) ≤ t →
              Protocol.confirmation_time S.E (S.hc.opening_slot m) ≤ t' →
              t ≤ rho'.horizon → t' ≤ rho'.horizon →
              Block.compatible (rho'.storeAt S u t).core.latest_confirmed
                (rho'.storeAt S v t').core.F = true)) :
    ∀ rho rGST gap extra n,
      StrongRecoveryPrefix S rho rGST gap extra n →
      ∃ m, n ≤ m ∧ m ≤ n + gap ∧
        ∀ rho', WeakContinuation S rho rho' (n + gap) →
          StableRecordCanonicalFrom S rho' (healingBoundaryTime S m) :=
  stableRecordSafety_afterGST_of_pins S hprepared

#print axioms stableRecordSafety_afterGST_preparedV4_canonical_of_pins

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
