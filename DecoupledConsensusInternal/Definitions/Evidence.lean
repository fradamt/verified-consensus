module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusModel.Protocol.Evidence

@[expose] public section

/-! Proof-side erased evidence helpers outside `Statements.Consensus`. -/
namespace DecoupledConsensusModel.Internal
open Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- P1 `σ[B]`, derived from the structural block chain. This is an inactive
erased reference used only by proof-side comparison lemmas. -/
def derived_state (E : Env V) (cfg : HeightConfig) : Block V → ChainState V
  | .genesis => ChainState.initial
  | B@(.node p _ _ _ _ _ _) =>
      Protocol.state_transition E cfg (derived_state E cfg p) B

/-- Erased reference finalization query. -/
def FinalizedAt (E : Env V) (cfg : HeightConfig) (B T : Block V) (h : Height) : Prop :=
  (derived_state E cfg B).F = T ∧ (derived_state E cfg B).h_F = h

end DecoupledConsensusModel.Internal

end
