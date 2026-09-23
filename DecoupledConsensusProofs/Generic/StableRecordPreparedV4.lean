module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.StableRecordGSTZero

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Stable-record safety after the prepared handover -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The phase-shift record clauses and the V4 latest/finality clause form the
canonical stable-record bundle at the confirmation boundary. -/
theorem stableRecordCanonicalFrom_of_phaseShift_latestFinality
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {cut : Round} {start : Slot} {P : Block V}
    (hphase : PhaseShiftSafety S rho cut start P)
    (hlatest : ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t',
      Protocol.confirmation_time S.E start ≤ t →
      Protocol.confirmation_time S.E start ≤ t' →
      t ≤ rho.horizon → t' ≤ rho.horizon →
      Block.compatible (rho.storeAt S u t).core.latest_confirmed
        (rho.storeAt S v t').core.F = true) :
    StableRecordCanonicalFrom S rho
      (Protocol.confirmation_time S.E start) := by
  refine
    { monotone := stableRecordMonotoneFrom_of_confirmation_clean
        S sch hphase.userConfirmation.latestCompatible
      agree := stableRecordCompatibleFrom_of_confirmation_clean
        S sch hphase.userConfirmation.latestCompatible
      finality := ?_ }
  intro u hu v hv t t' ht ht' hhor hhor'
  exact compatible_of_ancestors_of_compatible_clean
    (StableRecord.stableBelowConfirmed_storeAt S sch u t)
    (Block.preceq_self _)
    (hlatest u hu v hv t t' ht ht' hhor hhor')

private theorem confirmation_time_le_healing_boundary_clean
    (S : Setup V) (m : Round) :
    Protocol.confirmation_time S.E (S.hc.opening_slot m) ≤
      healingBoundaryTime S m := by
  unfold healingBoundaryTime Protocol.confirmation_time Protocol.vote_time Env.t slotStart
    Protocol.HealConfig.opening_slot
  push_cast
  ring_nf
  nlinarith [S.E.Δ_pos]

/-- A canonical stable-record bundle remains valid when its start time moves
later. -/
theorem StableRecordCanonicalFrom.mono_start
    (S : Setup V) {rho : Run V} {t₀ t₁ : Time}
    (h : t₀ ≤ t₁) (hcanon : StableRecordCanonicalFrom S rho t₀) :
    StableRecordCanonicalFrom S rho t₁ := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv t t' ht htt' hhor
    exact hcanon.monotone v hv t t' (h.trans ht) htt' hhor
  · intro u hu v hv t t' ht ht' hhor hhor'
    exact hcanon.agree u hu v hv t t' (h.trans ht) (h.trans ht') hhor hhor'
  · intro u hu v hv t t' ht ht' hhor hhor'
    exact hcanon.finality u hu v hv t t' (h.trans ht) (h.trans ht') hhor hhor'

/-- The after-GST arm, prebuilt over the complete bounded-phase producer.
The producer returns the phase-shift package and its V4 latest/finality
consequence from the same witness. -/
theorem stableRecordSafety_afterGST_of_pins
    (S : Setup V)
    (hcomplete : ∀ rho rGST gap extra n,
      StrongRecoveryPrefix S rho rGST gap extra n →
      ∃ m, n ≤ m ∧ m ≤ n + gap ∧
        ∀ rho', WeakContinuation S rho rho' (n + gap) →
          ∃ cut P,
            PhaseShiftSafety S rho' cut (S.hc.opening_slot m) P ∧
            (∀ u ∈ rho'.honest, ∀ v ∈ rho'.honest, ∀ t t',
              Protocol.confirmation_time S.E (S.hc.opening_slot m) ≤ t →
              Protocol.confirmation_time S.E (S.hc.opening_slot m) ≤ t' →
              t ≤ rho'.horizon → t' ≤ rho'.horizon →
              Block.compatible (rho'.storeAt S u t).core.latest_confirmed
                (rho'.storeAt S v t').core.F = true)) :
    ∀ rho rGST gap extra n,
      StrongRecoveryPrefix S rho rGST gap extra n →
      ∃ m, n ≤ m ∧ m ≤ n + gap ∧
        ∀ rho', WeakContinuation S rho rho' (n + gap) →
          StableRecordCanonicalFrom S rho' (healingBoundaryTime S m) := by
  intro rho rGST gap extra n hprefix
  obtain ⟨m, hmn, hm, hcontinuation⟩ :=
    hcomplete rho rGST gap extra n hprefix
  refine ⟨m, hmn, hm, ?_⟩
  intro rho' hcont
  obtain ⟨cut, P, hphase, hlatest⟩ := hcontinuation rho' hcont
  apply StableRecordCanonicalFrom.mono_start S
    (confirmation_time_le_healing_boundary_clean S m)
  exact stableRecordCanonicalFrom_of_phaseShift_latestFinality
    S hcont.core.toNamedScheduleWellFormed hphase hlatest

#print axioms stableRecordCanonicalFrom_of_phaseShift_latestFinality
#print axioms StableRecordCanonicalFrom.mono_start
#print axioms stableRecordSafety_afterGST_of_pins

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
