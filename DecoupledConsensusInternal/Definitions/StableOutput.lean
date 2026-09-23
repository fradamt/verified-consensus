module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Definitions.StableOutput

@[expose] public section

/-! Proof-side stable-output helpers outside `Statements.Consensus`. -/
namespace DecoupledConsensusModel.Internal
open Execution Proofs.HealingSurface
variable {V : Type} [DecidableEq V] [Fintype V]

def StableOutputMonotoneFrom (S : Setup V) (rho : Run V) (t0 : Time) : Prop :=
  ∀ v ∈ rho.honest, ∀ t t', t0 ≤ t → t ≤ t' → t' ≤ rho.horizon →
    Block.Preceq (stableOutputAt S rho v t) (stableOutputAt S rho v t')

def StableOutputCompatibleFrom (S : Setup V) (rho : Run V) (t0 : Time) : Prop :=
  ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t', t0 ≤ t → t0 ≤ t' →
    t ≤ rho.horizon → t' ≤ rho.horizon →
    Block.compatible (stableOutputAt S rho u t) (stableOutputAt S rho v t') = true

end DecoupledConsensusModel.Internal

end
