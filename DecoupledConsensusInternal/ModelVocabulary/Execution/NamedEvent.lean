module
public import DecoupledConsensusModel
public import Mathlib.Data.Prod.Lex

@[expose] public section

/-! Named event data, with the existing time/phase ordering. Erasure is not
an execution simulation and does not discard the original named object. -/
namespace DecoupledConsensusModel.Execution

namespace NamedEvent
variable {V : Type}

@[simp] theorem tick.injEq (v v' : V) (t t' : Time) :
    (NamedEvent.tick v t = NamedEvent.tick v' t') = (v = v' ∧ t = t') :=
  Generic.Event.tick.injEq v t v' t'

theorem tick.inj {v v' : V} {t t' : Time}
    (h : NamedEvent.tick v t = NamedEvent.tick v' t') : v = v' ∧ t = t' :=
  Generic.Event.tick.inj h

def phase : NamedEvent V → Nat
  | .tick _ _ => 0
  | .deliver _ _ _ => 1

def key (e : NamedEvent V) : Lex (Time × Nat) := toLex (e.time, e.phase)

end NamedEvent
end DecoupledConsensusModel.Execution

end
