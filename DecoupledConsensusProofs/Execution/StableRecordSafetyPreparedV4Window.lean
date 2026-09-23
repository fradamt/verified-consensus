module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.StableRecordPreparedV4Closed
public import DecoupledConsensusProofs.Execution.StableRecordPreparedV4Public

@[expose] public section

/-! # Stable-record safety under the corrected recovery window -/

namespace DecoupledConsensusModel
namespace Proofs

open Internal Execution Statements Proofs.HealingSurface
open Proofs.HealingSurface.Handover

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The corrected recovery-window bound closes public stable-record safety. -/
theorem stableRecordSafety_holds_of_window
    (S : Setup V)
    (hwindow : ∀ rho rGST gap extra n,
      StrongRecoveryPrefix S rho rGST gap extra n →
      fgSafetyProgressDeadline S rho rGST gap extra +
        2 * progressLag' gap extra +
        max (1 + S.hc.η_SG) (gap + 3) ≤ n) :
    Statements.StableRecordSafety S :=
  stableRecordSafety_holds_preparedV4_of_pins S
    (stableRecordSafety_afterGST_preparedV4 S hwindow)

#print axioms stableRecordSafety_holds_of_window

end Proofs
end DecoupledConsensusModel

end
