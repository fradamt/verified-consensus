module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Healing

@[expose] public section

/-!
# Honest-opening streak fairness

These predicates state the stronger recurrence used by arbitrary-GST finality.
The streak length is selected before the run; each horizon-qualified suffix
contains one consecutive streak of honest opening proposers.
-/

namespace DecoupledConsensusModel
namespace Internal

open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every opening proposer in the half-open interval `[q, q + len)` is honest. -/
def HonestOpeningStreakAt
    (S : Setup V) (rho : Run V) (q len : Round) : Prop :=
  ∀ j, j < len →
    S.E.proposer (S.hc.opening_slot (q + j)) ∈ rho.honest


/-- From each round at or after ``, a bounded future interval contains an
honest-opening streak whenever the complete search window is in the run. -/
def RecurringHonestOpeningStreaks
    (S : Setup V) (rho : Run V) (r0 gap len : Round) : Prop :=
  ∀ r, r0 ≤ r → S.a (r + gap + len) ≤ rho.horizon →
    ∃ q, r ≤ q ∧ q ≤ r + gap ∧ HonestOpeningStreakAt S rho q len

end Internal
end DecoupledConsensusModel

end
