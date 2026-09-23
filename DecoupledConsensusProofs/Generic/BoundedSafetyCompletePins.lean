module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Safety
public import DecoupledConsensusProofs.Objects.AdmissibleCore

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Bounded phase-shift safety from the prepared continuation pin -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Statements

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Prebuilt bounded-phase producer. The pin is the exact result supplied by
the V4 selector and continuation record producers, before the redundant
shifted upper bound is added. The named proposal stays outside the
continuation binder. -/
theorem safety_after_boundedStrongPhase_complete_of_pins
    (S : Setup V)
    (_of_pins : ∀ (rho : Run V) (rGST gap : Round) (extra : Nat) (n : Round),
      Admissible S rho → HonestCommittees S rho.honest →
      BelowOneThird S rho.honest → MultiProposerRecurrence S rho gap →
      TimeoutDelayBound S extra → S.E.t_GST ≤ S.a rGST →
      BoundedPhaseStart S rho rGST gap extra n →
      rho.horizon = S.a (n + gap) →
      ∃ m, n ≤ m ∧ m ≤ n + gap ∧
        ∃ P : NamedBlock V,
          proposedBlockAt S rho (S.hc.opening_slot m) = some P ∧
          ∀ rho' : Run V, AdmissibleCore S rho' →
            HonestCommittees S rho'.honest → SlashableBound S rho' →
            AgreesUntil rho rho' (S.a (n + gap)) →
            S.a (n + gap) ≤ rho'.horizon →
            (∀ r, n + gap < r → S.a (r - 1) ≤ rho'.horizon →
              AwakeWindowMajority S.E (fun v => (S.node v).awake)
                rho'.honest S.hc.η_SG r) →
            PhaseShiftSafety S rho' n (S.hc.opening_slot m) P.erase)
    {rho : Run V} {rGST gap : Round} {extra : Nat} {n : Round}
    (adm : Admissible S rho) (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S extra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    (hstart : BoundedPhaseStart S rho rGST gap extra n)
    (hprefix : rho.horizon = S.a (n + gap)) :
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
          PhaseShiftSafety S rho' n (S.hc.opening_slot m) P.erase := by
  obtain ⟨m, hmlo, hmhi, P, hP, hcontinue⟩ :=
    _of_pins rho rGST gap extra n adm hcom hbelow hrec hdelay hpost
      hstart hprefix
  exact ⟨m, hmlo, hmhi, Nat.add_le_add_right hmlo gap, P, hP, hcontinue⟩

#print axioms safety_after_boundedStrongPhase_complete_of_pins

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
