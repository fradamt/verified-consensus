module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.ModelVocabulary.Execution.Run

@[expose] public section

/-! Numeric height progress is internal support for recovery and finality. -/

namespace DecoupledConsensusModel
namespace Internal
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The largest inclusive `h_max` held by an honest store at time `t`.
The value is zero if the honest set is empty. -/
noncomputable def honestHMaxAt
    (S : Setup V) (rho : Run V) (t : Time) : Height :=
  rho.honest.sup fun v => (rho.storeAt S v t).core.h_max


/-- Uniform raw honest-height progress after round ``. The positive lag and
horizon guard make this a finite-run liveness property without imposing any
canonical-chain or finality condition. -/
def EventualHeightProgressFrom
    (S : Setup V) (rho : Run V) (r0 lag : Round) : Prop :=
  0 < lag ∧
    ∀ r, r0 ≤ r → S.a (r + lag) ≤ rho.horizon →
      honestHMaxAt S rho (S.a r) <
        honestHMaxAt S rho (S.a (r + lag))

end Internal
end DecoupledConsensusModel

end
