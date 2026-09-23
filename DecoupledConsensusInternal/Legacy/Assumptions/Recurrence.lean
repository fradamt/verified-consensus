module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.ModelVocabulary.Execution.Run

@[expose] public section

/-! Definitions used by the final review statements. No proof obligations are assumed here. -/

namespace DecoupledConsensusModel
namespace Internal

open Execution Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A proposer-carrier round has honest proposers at the opening slot and at
the next two slots. The carrier slots are `S.hc.opening_slot r + 1` and
`S.hc.opening_slot r + 2`, rather than opening slots of later rounds. -/
def ProposerCarrierAt (S : Setup V) (ρ : Run V) (r : Round) : Prop :=
  S.E.proposer (S.hc.opening_slot r) ∈ ρ.honest ∧
    S.E.proposer (S.hc.opening_slot r + 1) ∈ ρ.honest ∧
      S.E.proposer (S.hc.opening_slot r + 2) ∈ ρ.honest

/-- The triple-proposer recurrence: every inclusive round window
`[r, r + gap]` contains a round whose opening proposer and next two
slot proposers are all honest (PROTOCOL.md#the-complete-protocol). -/
def MultiProposerRecurrence (S : Setup V) (ρ : Run V) (gap : Round) : Prop :=
  ∀ r : Round, ∃ r' : Round, r ≤ r' ∧ r' ≤ r + gap ∧
    ProposerCarrierAt S ρ r'

def ProposerOpeningCarrierAt (S : Setup V) (rho : Run V) (r : Round) : Prop :=
  S.E.proposer (S.hc.opening_slot (r - 2)) ∈ rho.honest ∧
  S.E.proposer (S.hc.opening_slot (r - 1)) ∈ rho.honest ∧
  ProposerCarrierAt S rho r

/-- Each window contains the complete three-round pattern. The selected
carrier is its last round; both earlier openings lie in the same window. -/
def ProposerOpeningCarrierRecurrence (S : Setup V) (rho : Run V) (gap : Round) : Prop :=
  ∀ k : Round, ∃ r : Round, k + 2 ≤ r ∧ r ≤ k + gap ∧
    ProposerOpeningCarrierAt S rho r

end Internal
end DecoupledConsensusModel

end
