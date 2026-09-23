module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.BoundedSafetyCompletePins
public import DecoupledConsensusProofs.Objects.AdmissibleCore

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Public bounded-safety projection from the complete phase producer -/

namespace DecoupledConsensusModel
namespace Proofs

open Internal Execution Statements Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The public bounded-safety field is a direct projection once the complete
prepared phase producer is available. -/
theorem boundedSafetyRecovery_of_pins
    (S : Setup V)
    (hcomplete : ∀ (rho : Run V) (rGST gap : Round) (extra : Nat) (n : Round),
      Admissible S rho → HonestCommittees S rho.honest →
      BelowOneThird S rho.honest → MultiProposerRecurrence S rho gap →
      TimeoutDelayBound S extra → S.E.t_GST ≤ S.a rGST →
      BoundedPhaseStart S rho rGST gap extra n →
      rho.horizon = S.a (n + gap) →
      ∃ m, n ≤ m ∧ m ≤ n + gap ∧ n + gap ≤ m + gap ∧
        ∃ P : NamedBlock V,
          proposedBlockAt S rho (S.hc.opening_slot m) = some P ∧
          ∀ rho' : Run V, AdmissibleCore S rho' →
            HonestCommittees S rho'.honest → SlashableBound S rho' →
            AgreesUntil rho rho' (S.a (n + gap)) →
            S.a (n + gap) ≤ rho'.horizon →
            (∀ r, n + gap < r → S.a (r - 1) ≤ rho'.horizon →
              AwakeWindowMajority S.E (fun v => (S.node v).awake)
                rho'.honest S.hc.η_SG r) →
            PhaseShiftSafety S rho' n (S.hc.opening_slot m) P.erase) :
    Statements.BoundedSafetyRecovery S := by
  intro rho rGST gap extra n hprefix
  obtain ⟨m, hmlo, hmhi, hend, P, hP, hcontinue⟩ :=
    hcomplete rho rGST gap extra n hprefix.admissible
      hprefix.committees hprefix.belowThird hprefix.recurrence
      hprefix.timeout hprefix.postGST hprefix.start hprefix.horizon
  refine ⟨m, hmlo, hmhi, hend, P, hP, ?_⟩
  intro rho' hw
  exact hcontinue rho' hw.core hw.committees hw.accountable
    hw.agrees ((a_le_healingBoundaryTime S (n + gap)).trans hw.covered) hw.windows

#print axioms boundedSafetyRecovery_of_pins

end Proofs
end DecoupledConsensusModel

end
