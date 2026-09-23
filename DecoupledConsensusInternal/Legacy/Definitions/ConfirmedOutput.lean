module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.ModelVocabulary.Execution.Run
public import DecoupledConsensusModel.Protocol.Handlers

@[expose] public section

/-! # Public confirmed output and its finalized-prefix property -/

namespace DecoupledConsensusModel
namespace Internal

open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The actual named node exposes the confirmed chain computed from its core
fields. This projection does not reconstruct any grade or phase cache. -/
def confirmedOutputAt (S : Setup V) (rho : Run V) (v : V) (t : Time) : Block V :=
  Protocol.get_confirmed (rho.storeAt S v t).core

/-- At every node and time, the finalized chain is a prefix of the exposed
confirmed chain; this is a store invariant of the named store, so no honesty
or horizon guard is needed. -/
def FinalizedPrefixConfirmed (S : Setup V) (rho : Run V) : Prop :=
  ∀ v t,
    Block.Preceq (rho.storeAt S v t).core.F (confirmedOutputAt S rho v t)

/-- Agreement of the exposed confirmed chains. -/
def ConfirmedOutputCompatibleFrom (S : Setup V) (rho : Run V) (t0 : Time) : Prop :=
  ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t', t0 ≤ t → t0 ≤ t' →
    t ≤ rho.horizon → t' ≤ rho.horizon →
    Block.compatible (confirmedOutputAt S rho u t) (confirmedOutputAt S rho v t') = true

/-- Monotonicity of one node's exposed confirmed chain in a safe interval. -/
def ConfirmedOutputMonotoneFrom (S : Setup V) (rho : Run V) (t0 : Time) : Prop :=
  ∀ v ∈ rho.honest, ∀ t t', t0 ≤ t → t ≤ t' → t' ≤ rho.horizon →
    Block.Preceq (confirmedOutputAt S rho v t) (confirmedOutputAt S rho v t')

end Internal
end DecoupledConsensusModel

end
