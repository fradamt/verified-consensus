module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.ModelVocabulary.Execution.Admissible
public import DecoupledConsensusModel.Protocol.Evidence

@[expose] public section

/-!
# Validator-client vote safety

The validator client's finality/timeout signing record prevents one validator's
actual emissions from forming E1 or E2 evidence. This property needs no
synchrony, participation, fault bound, or honesty assumption about another
validator.
-/

namespace DecoupledConsensusModel
namespace Internal

open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The narrow authenticity premise for attestation rows carried by blocks.

This is exactly the `NamedUnforgeable.carried_attest` field. It says that a row
which names an honest validator and occurs in a processed block came from an
actual earlier emission by that validator. -/
structure AttestationAuthenticity (S : Setup V) (rho : Run V) : Prop where
  carriedAttest : ∀ v B t, Run.processes S rho v (.block B) t →
    ∀ a ∈ B.attestations, a.val_index ∈ rho.honest →
      ∃ t', t' ≤ t ∧ Run.emits S rho a.val_index (.attest a) t'

/-- The two schedule facts validator-client vote safety needs: events are in key
order and every event belongs to an honest node. -/
structure VoteSafetySchedule (S : Setup V) (rho : Run V) : Prop where
  sorted : rho.events.Pairwise (fun e f => NamedEvent.key e ≤ NamedEvent.key f)
  honest_only : ∀ e ∈ rho.events, e.node ∈ rho.honest

/-- Every two attestations actually emitted by one validator client are not
slashable against each other. The schedule premise is used only to establish
that an emitting tick belongs to the run's honest set. -/
def EmissionVoteSafety (S : Setup V) : Prop :=
  ∀ rho, VoteSafetySchedule S rho →
    ∀ (v : V) (a b : NamedAttestation V),
      (∃ ta : Time, rho.emits S v (.attest a) ta) →
      (∃ tb : Time, rho.emits S v (.attest b) tb) →
      ¬ Protocol.Slashable a.erase b.erase

/-- No E1 or E2 evidence in two honest stores can be attributed to the same
honest validator. Besides schedule well-formedness, this needs only the narrow
carried-attestation authenticity premise. It needs no synchrony, participation,
fault bound, or honesty assumption about another validator. -/
def AttributedVoteSafety (S : Setup V) : Prop :=
  ∀ rho, VoteSafetySchedule S rho → AttestationAuthenticity S rho →
    ∀ u v t t' i, i ∈ rho.honest →
      ¬ SlashableBetween
        (store_attestations (rho.storeAt S u t).core)
        (store_attestations (rho.storeAt S v t').core) i

/-- Validator-client signing safety for actual emissions and for honest-attributed
evidence retained in honest stores. -/
structure ValidatorVoteSafety (S : Setup V) : Prop where
  emission : EmissionVoteSafety S
  attributed : AttributedVoteSafety S

end Internal
end DecoupledConsensusModel

end
