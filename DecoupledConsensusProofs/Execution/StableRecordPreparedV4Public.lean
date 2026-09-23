module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.StableRecordPreparedV4Canonical
public import DecoupledConsensusProofs.Generic.StableRecordSafetyAssembly

@[expose] public section

/-! # Public stable-record wire for the prepared V4 producer -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Statements

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Wire the prepared V4 after-GST producer into public stable-record safety. -/
theorem stableRecordSafety_holds_preparedV4_of_pins
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
    StableRecordSafety S :=
  stableRecordSafety_holds_of_pins S
    (stableRecordSafety_afterGST_preparedV4_canonical_of_pins S hprepared)

#print axioms stableRecordSafety_holds_preparedV4_of_pins

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
