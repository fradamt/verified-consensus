module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Definitions.ValidatorVoteSafety

@[expose] public section

/-! Proof-side adapters for validator-client vote safety. -/
namespace DecoupledConsensusModel.Internal
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Project the attestation-only premise from the larger authenticity contract. -/
def AttestationAuthenticity.ofAuthentic {S : Setup V} {rho : Run V}
    (auth : Unforgeable S rho) : AttestationAuthenticity S rho :=
  ⟨NamedUnforgeable.carried_attest auth⟩

end DecoupledConsensusModel.Internal

end
