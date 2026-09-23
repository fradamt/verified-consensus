module
public import DecoupledConsensusModel.Protocol.ChainState

@[expose] public section

/-!
# Instantiation certificates

Purpose: define the named finalization certificate predicate used by the
selected interface.
An auditor checks that the predicate is only the named derived-state equality.

Defines: `NamedFinalizedAt`.
Read after: the model finality transition.
Read next: the instantiation contents page.
-/
namespace DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The internal certificate-finalization predicate: the named derived state of
`C` carries `(F, h_F) = (T, h)`. This is distinct from the public generic
`Generic.FinalizedAt` liveness record. -/
def NamedFinalizedAt (E : Env V) (cfg : HeightConfig) (C : NamedBlock V) (T : Block V)
    (h : Height) : Prop :=
  (derive_named E cfg C).F = T ∧ (derive_named E cfg C).h_F = h

end DecoupledConsensusModel.Statements.Instantiation

end
