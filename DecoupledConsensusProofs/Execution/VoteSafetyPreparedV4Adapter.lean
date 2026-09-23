module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Safety
public import DecoupledConsensusProofs.Execution.OpeningCarrierSelection

@[expose] public section

/-! # Clean public vote-safety projection
This leaf keeps the opening-carrier conversion above the continuation
producer. The producer remains an internal pin until the prepared V4
continuation closes.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Statements

variable {V : Type} [DecidableEq V] [Fintype V]

/-- An internal producer stated with plain proposer recurrence closes the
public opening-carrier vote-safety contract. -/
theorem voteSafety_of_weakContinuation_of_pins
    (S : Setup V)
    (_of_complete : ∀ extra, TimeoutDelayBound S extra → ∀ gap,
      ∃ progressLag, 0 < progressLag ∧
        ∀ rho rGST, Admissible S rho →
          HonestCommittees S rho.honest →
          BelowOneThird S rho.honest →
          S.E.t_GST ≤ S.a rGST →
          MultiProposerRecurrence S rho gap →
          WeakVoteContinuation S rho rGST gap progressLag) :
    VoteSafetyAfterRecovery S := by
  intro extra hdelay gap
  obtain ⟨progressLag, hpos, hcomplete⟩ :=
    _of_complete extra hdelay gap
  refine ⟨progressLag, hpos, ?_⟩
  intro rho rGST adm hcom hbelow hpost hopening
  exact hcomplete rho rGST adm hcom hbelow hpost
    (proposerRecurrence_of_openingCarrierRecurrence S hopening)

#print axioms voteSafety_of_weakContinuation_of_pins

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
