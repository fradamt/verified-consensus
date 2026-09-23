module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.ModelVocabulary.Execution.Admissible
public import DecoupledConsensusModel.Protocol.Evidence

@[expose] public section

/-! Definitions used by the final review statements. No proof obligations are assumed here. -/

namespace DecoupledConsensusModel
namespace Execution

open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every slot committee has a strict honest majority by count.
This is separate from validator weight. -/
def HonestCommittees (S : Setup V) (H : Finset V) : Prop :=
  ∀ s : Slot, (S.E.committee s).card < 2 * ((S.E.committee s) ∩ H).card

/-- Faulty validators hold less than one third of total validator weight.
The complement of the honest set is the faulty set. -/
def BelowOneThird (S : Setup V) (H : Finset V) : Prop :=
  3 * S.E.electorate.weightOf (Finset.univ \ H) < S.E.W

/-- No two full named run-block chains expose E1/E2-slashable weight of at
least 2q - W after their chain evidence is erased. This bounds accountable
faults, not the total faulty weight. -/
def SlashableBound (S : Setup V) (ρ : Run V) : Prop :=
  ∀ B₁ B₂ : NamedBlock V, RunBlock S ρ B₁ → RunBlock S ρ B₂ →
    ¬ HasSlashableWeightBetween S.E
      (chain_attestations B₁.erase) (chain_attestations B₂.erase)

end Execution
end DecoupledConsensusModel

end
