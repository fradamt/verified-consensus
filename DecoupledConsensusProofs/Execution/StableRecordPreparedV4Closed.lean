module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.StableRecordPreparedV4WindowPhase
public import DecoupledConsensusProofs.Execution.PreparedV4LatestFinalizedCompatibilityClosed
public import DecoupledConsensusProofs.Execution.StableRecordPreparedV4Complete

@[expose] public section

/-! # Stable-record safety after GST under the corrected recovery window -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The prepared V4 after-GST stable-record producer has no proof-layer pin.
The corrected recovery-window bound is its only extra hypothesis. -/
theorem stableRecordSafety_afterGST_preparedV4
    (S : Setup V)
    (hwindow : ∀ rho rGST gap extra n,
      StrongRecoveryPrefix S rho rGST gap extra n →
      fgSafetyProgressDeadline S rho rGST gap extra +
        2 * progressLag' gap extra +
        max (1 + S.hc.η_SG) (gap + 3) ≤ n) :
    ∀ rho rGST gap extra n,
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
                (rho'.storeAt S v t').core.F = true) := by
  exact stableRecordSafety_afterGST_preparedV4_of_pins S
    (stableRecordPreparedV4_phase_of_window S hwindow)
    (SettledBootstrapPreparedV4.latest_compatible_finalized_core S)

#print axioms stableRecordSafety_afterGST_preparedV4

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
