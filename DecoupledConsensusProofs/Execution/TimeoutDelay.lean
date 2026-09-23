module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Execution.Setup

@[expose] public section

/-!
# Separate bounds for timeout timing

The default timeout hypothesis still means exactly two rounds. An extra
round changes the progress budget, while the gate-protection lower bound
stays at two rounds. No protocol handler is changed by these lemmas.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Execution

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

/-- Every indexed delay supplies the two-round protection bound. -/
theorem timeoutDelay_ge_twoRounds (S : Setup V)
    (hdelay : TimeoutDelayBound S delayExtra) :
    2 * S.hc.R ≤ S.cfg.timeoutDelay := by
  rw [hdelay]
  exact Nat.mul_le_mul_right S.hc.R (Nat.le_add_right 2 delayExtra)

/-- The same hypothesis gives the upper bound needed for height progress. -/
theorem timeoutDelay_le_roundBound (S : Setup V)
    (hdelay : TimeoutDelayBound S delayExtra) :
    S.cfg.timeoutDelay ≤ (2 + delayExtra) * S.hc.R :=
  Nat.le_of_eq hdelay



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
