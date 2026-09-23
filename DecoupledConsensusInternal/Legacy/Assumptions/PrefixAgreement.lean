module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.ModelVocabulary.Execution.Admissible

@[expose] public section

/-! # Local event-prefix agreement
A continuation can keep a subset of the previous honest validators. Each retained
validator has the same ordered local events before the handover time. Events
at other validators need not have the same interleaving.
-/

namespace DecoupledConsensusModel
namespace Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Prefix agreement for retained honest validators, before the cutoff. -/
structure AgreesUntil (rho rho' : Run V) (cutoff : Time) : Prop where
  honest_subset : rho'.honest ⊆ rho.honest
  events : ∀ v ∈ rho'.honest,
    rho'.events.filter (fun e => decide (e.node = v ∧ e.time < cutoff)) =
      rho.events.filter (fun e => decide (e.node = v ∧ e.time < cutoff))

end Execution
end DecoupledConsensusModel

end
