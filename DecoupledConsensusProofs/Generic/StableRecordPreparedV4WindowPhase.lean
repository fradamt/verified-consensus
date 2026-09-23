module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.HandoverPreparedV4Direct
public import DecoupledConsensusProofs.Objects.HandoverPreparedV4Transfer
public import DecoupledConsensusProofs.Execution.PreparedV4Finality
public import DecoupledConsensusProofs.Protocol.Schedule.PreparedV4PhaseShiftSafety

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Stable-record phase witness under the corrected recovery window -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem stableRecord_windowAwake_of_prefix
    (S : Setup V) {source rho : Run V} (adm : Admissible S source)
    {lastStrong : Round} (hprefix : source.horizon = S.a lastStrong)
    (hretain : rho.honest ⊆ source.honest)
    (hcovered : S.a lastStrong ≤ rho.horizon)
    (hawake : ∀ r, lastStrong < r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r) :
    ∀ r, 0 < r → S.E.t_GST ≤ S.a (r - 1) →
      S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r := by
  have hmajority : HonestWeightMajority S rho.honest :=
    WeakSG.honestWeightMajority_of_awakeWindowMajority S
      (hawake (lastStrong + 1) (Nat.lt_succ_self _)
        (by simpa only [Nat.add_sub_cancel] using hcovered))
  intro r hr hpostPrev hhor
  by_cases hafter : lastStrong < r
  · exact hawake r hafter hhor
  have heq : honestAwakeWindow (fun v => (S.node v).awake)
      rho.honest S.hc.η_SG r = rho.honest := by
    apply Finset.Subset.antisymm
      (WeakSG.honestAwakeWindow_subset _ _ _ _)
    intro v hv
    refine WeakSG.mem_honestAwakeWindow_iff.mpr
      ⟨hv, r - 1,
        pred_mem_latest_window S.hc.η_SG r S.hc.η_SG_ge_one hr, ?_⟩
    apply adm.all_awake v (hretain hv) (r - 1) hpostPrev
    change S.a (r - 1) ≤ source.horizon
    rw [hprefix]
    exact Assembly.a_mono S
      ((Nat.sub_le r 1).trans (Nat.le_of_not_gt hafter))
  unfold AwakeWindowMajority
  rw [heq]
  exact hmajority

/-- The corrected recovery window selects one prepared V4 witness and keeps
that witness through continuation transfer and phase-shift safety. -/
theorem stableRecordPreparedV4_phase_of_window
    (S : Setup V)
    (hwindow : ∀ rho rGST gap extra n,
      StrongRecoveryPrefix S rho rGST gap extra n →
      fgSafetyProgressDeadline S rho rGST gap extra +
        2 * progressLag' gap extra +
        max (1 + S.hc.η_SG) (gap + 3) ≤ n) :
    ∀ rho rGST gap extra n,
      StrongRecoveryPrefix S rho rGST gap extra n →
      ∃ m, n ≤ m ∧ m ≤ n + gap ∧
        ∃ fresh base P cap,
          SettledBootstrapPreparedV4 S rho fresh base
            (S.hc.opening_slot m) P cap ∧
          SettledBootstrapPreparedV4.LatestSeed S rho
            (S.hc.opening_slot m) P ∧
          fresh ≤ base + S.hc.η_SG ∧
          cap < (Protocol.derive_named S.E S.cfg P).h ∧
          ∀ rho', WeakContinuation S rho rho' (n + gap) →
            PhaseShiftSafety S rho' (base + S.hc.η_SG)
              (S.hc.opening_slot m) P.erase := by
  intro rho rGST gap extra n hprefix
  have hsourceHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot (n + gap)) ≤ rho.horizon := by
    rw [opening_confirmation_time_eq_action, hprefix.horizon]
  obtain ⟨m, hmlo, hmhi, _hcarrier, P, _hP, hboot, hlatest, hheight⟩ :=
    settledBootstrap_of_strong_preparedV4_latest_closed
      S hprefix.admissible hprefix.committees hprefix.belowThird
        hprefix.timeout hprefix.recurrence hprefix.postGST
        (hwindow rho rGST gap extra n hprefix) hsourceHor
  have hfresh :
      fgSafetyProgressDeadline S rho rGST gap extra + 1 ≤
        (fgSafetyProgressDeadline S rho rGST gap extra +
          2 * progressLag' gap extra + 1) + S.hc.η_SG := by
    exact (Nat.add_le_add_right
      (Nat.le_add_right (fgSafetyProgressDeadline S rho rGST gap extra)
        (2 * progressLag' gap extra)) 1).trans
      (Nat.le_add_right _ S.hc.η_SG)
  refine ⟨m, hmlo, hmhi,
    fgSafetyProgressDeadline S rho rGST gap extra + 1,
    fgSafetyProgressDeadline S rho rGST gap extra +
      2 * progressLag' gap extra + 1,
    P, honestHMaxAt S rho
      (S.a (fgSafetyProgressDeadline S rho rGST gap extra)),
    hboot, hlatest, hfresh, hheight, ?_⟩
  intro rho' hcont
  have hseedCut : Protocol.confirmation_time S.E
      (S.hc.opening_slot m) ≤ S.a (n + gap) := by
    rw [opening_confirmation_time_eq_action]
    exact Assembly.a_mono S hmhi
  have hagreeSeed : AgreesUntil rho rho'
      (Protocol.confirmation_time S.E (S.hc.opening_slot m)) :=
    AgreesUntil.mono hcont.agrees hseedCut
  have hboot' := SettledBootstrapPreparedV4.transfer
    S hprefix.admissible.toNamedAdmissibleCore hcont.core hcont.committees
      hboot hfresh hagreeSeed
  have hlatest' := SettledBootstrapPreparedV4.LatestSeed.transfer
    S hlatest hagreeSeed
  have hfinality :=
    SettledBootstrapPreparedV4.finalizedRootsBelowAtRead_of_accountable
      S hcont.core hcont.accountable hboot' hheight
  have hcovered : S.a (n + gap) ≤ rho'.horizon :=
    (a_le_healingBoundaryTime S (n + gap)).trans hcont.covered
  have hwindows := stableRecord_windowAwake_of_prefix
    S hprefix.admissible hprefix.horizon hcont.agrees.honest_subset
      hcovered hcont.windows
  have hcutPos : 0 <
      (fgSafetyProgressDeadline S rho rGST gap extra +
        2 * progressLag' gap extra + 1) + S.hc.η_SG :=
    (Nat.zero_lt_succ
      (fgSafetyProgressDeadline S rho rGST gap extra +
        2 * progressLag' gap extra)).trans_le
      (Nat.le_add_right _ S.hc.η_SG)
  have hawake' : ∀ r,
      (fgSafetyProgressDeadline S rho rGST gap extra +
        2 * progressLag' gap extra + 1) + S.hc.η_SG ≤ r →
      S.a (r - 1) ≤ rho'.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho'.honest S.hc.η_SG r :=
    fun r hr hhor => hwindows r (hcutPos.trans_le hr)
      (hprefix.postGST.trans (Assembly.a_mono S (by
        have hGSTdead : rGST + 1 ≤
            fgSafetyProgressDeadline S rho rGST gap extra := by
          unfold fgSafetyProgressDeadline
          exact Nat.le_add_right _ _
        have hdeadR : fgSafetyProgressDeadline S rho rGST gap extra ≤ r := by
          calc
            fgSafetyProgressDeadline S rho rGST gap extra ≤
                fgSafetyProgressDeadline S rho rGST gap extra +
                  2 * progressLag' gap extra := Nat.le_add_right _ _
            _ ≤ fgSafetyProgressDeadline S rho rGST gap extra +
                  2 * progressLag' gap extra + 1 := Nat.le_add_right _ _
            _ ≤ fgSafetyProgressDeadline S rho rGST gap extra +
                  2 * progressLag' gap extra + 1 + S.hc.η_SG := Nat.le_add_right _ _
            _ ≤ r := hr
        exact Nat.le_sub_of_add_le (hGSTdead.trans hdeadR)))) hhor
  have hstartHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot m) ≤ rho'.horizon :=
    hseedCut.trans hcovered
  exact SettledBootstrapPreparedV4.phaseShiftSafety_core
    S hcont.core hcont.committees hboot' hlatest' hawake' hfinality
      hstartHor hcont.accountable

#print axioms stableRecordPreparedV4_phase_of_window

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
