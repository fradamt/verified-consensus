module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.BoundedSafetyRecoveryPreparedV4Window
public import DecoupledConsensusProofs.Execution.StableRecordSafetyPreparedV4Window
public import DecoupledConsensusProofs.Execution.VoteSafetyPreparedV4

@[expose] public section

namespace DecoupledConsensusModel
namespace Proofs

open Internal Execution Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

theorem window_of_strongRecoveryPrefix (S : Setup V) :
    ∀ rho rGST gap extra n,
      Statements.StrongRecoveryPrefix S rho rGST gap extra n →
      fgSafetyProgressDeadline S rho rGST gap extra +
        2 * progressLag' gap extra +
        max (1 + S.hc.η_SG) (gap + 3) ≤ n := by
  intro rho rGST gap extra n h
  have hs := h.start
  simp only [Internal.BoundedPhaseStart] at hs
  simp only [fgSafetyProgressDeadline, progressLag', seedLag, inclusiveEventIndex]
  rw [hs]


/-- Bounded safety recovery, pin-free under the corrected recovery window. -/
theorem boundedSafetyRecovery_closed (S : Setup V) : Statements.BoundedSafetyRecovery S :=
  boundedSafetyRecovery_of_window S (window_of_strongRecoveryPrefix S)


/-- Stable-record safety, pin-free under the corrected recovery window. -/
theorem stableRecordSafety_closed (S : Setup V) : Statements.StableRecordSafety S :=
  stableRecordSafety_holds_of_window S (window_of_strongRecoveryPrefix S)


#print axioms boundedSafetyRecovery_closed
#print axioms stableRecordSafety_closed

end Proofs
end DecoupledConsensusModel

end
