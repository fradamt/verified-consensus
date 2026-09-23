module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.PreparedV4BoundedSafety
public import DecoupledConsensusProofs.Objects.AdmissibleCore
public import DecoupledConsensusProofs.Generic.BoundedSafetyRecoveryPins
public import DecoupledConsensusProofs.Protocol.Handlers.ProposalConfirmationPreparedLatestNamed

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Bounded safety under the corrected recovery window -/

namespace DecoupledConsensusModel
namespace Proofs

open Internal Execution Protocol Proofs.Optimistic Statements Proofs.HealingSurface
open Proofs.HealingSurface.Handover

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem preparedV4_windowAwake_of_prefix
    (S : Setup V) {source rho : Run V} (adm : Admissible S source)
    {lastStrong : Round} (hprefix : source.horizon = S.a lastStrong)
    (hretain : rho.honest ⊆ source.honest)
    (hcovered : S.a lastStrong ≤ rho.horizon)
    (hawake : ∀ r, lastStrong < r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r) :
    ∀ r, 0 < r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r := by
  have hmajority : HonestWeightMajority S rho.honest :=
    WeakSG.honestWeightMajority_of_awakeWindowMajority S
      (hawake (lastStrong + 1) (Nat.lt_succ_self _)
        (by simpa only [Nat.add_sub_cancel] using hcovered))
  intro r hr hhor
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
    apply adm.all_awake v (hretain hv)
    change S.a (r - 1) ≤ source.horizon
    rw [hprefix]
    exact Assembly.a_mono S
      ((Nat.sub_le r 1).trans (Nat.le_of_not_gt hafter))
  unfold AwakeWindowMajority
  rw [heq]
  exact hmajority

private theorem safety_after_boundedStrongPhase_complete_of_window
    (S : Setup V)
    {rho : Run V} {rGST gap : Round} {extra : Nat} {n : Round}
    (adm : Admissible S rho) (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S extra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    (hstart : BoundedPhaseStart S rho rGST gap extra n)
    (hprefix : rho.horizon = S.a (n + gap))
    (hwindow : fgSafetyProgressDeadline S rho rGST gap extra +
      2 * progressLag' gap extra +
      max (1 + S.hc.η_SG) (gap + 3) ≤ n) :
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
          PhaseShiftSafety S rho' n (S.hc.opening_slot m) P.erase := by
  have hn : n = fgSafetyProgressDeadline S rho rGST gap extra +
      2 * progressLag' gap extra + max (1 + S.hc.η_SG) (gap + 3) := hstart
  have hold : fgSafetyProgressDeadline S rho rGST gap extra +
      2 * progressLag' gap extra + 1 + S.hc.η_SG ≤ n := by
    rw [hn]
    exact (Nat.add_assoc _ _ _).le.trans (Nat.add_le_add_left (le_max_left _ _) _)
  have hsourceHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot (n + gap)) ≤ rho.horizon := by
    rw [opening_confirmation_time_eq_action, hprefix]
  obtain ⟨m, hmlo, hmhi, hcarrier, P, hP, hboot, hheight⟩ :=
    settledBootstrap_of_strong_preparedV4
      S adm hcom hbelow hdelay hrec hpost hold hsourceHor
  have hlatest : SettledBootstrapPreparedV4.LatestSeed S rho
      (S.hc.opening_slot m) P :=
    honestProposal_confirmationSeedPrepared_latest_after_SG_healing_named
      S adm hcom hbelow hrec hdelay hpost (hwindow.trans hmlo)
        hcarrier hP (by
          have : Protocol.confirmation_time S.E (S.hc.opening_slot m) ≤
              Protocol.confirmation_time S.E (S.hc.opening_slot (n + gap)) := by
            rw [Protocol.confirmation_time_eq_support_cutoff_succ,
              Protocol.confirmation_time_eq_support_cutoff_succ]
            exact support_cutoff_mono S.E
              (Nat.add_le_add_right
                (Nat.mul_le_mul_right S.hc.R hmhi) 1)
          exact this.trans hsourceHor)
  refine ⟨m, hmlo, hmhi, P, hP, ?_⟩
  intro rho' adm' hcom' hsb hagree hcovered hawake
  have hseedCut : Protocol.confirmation_time S.E
      (S.hc.opening_slot m) ≤ S.a (n + gap) := by
    rw [opening_confirmation_time_eq_action]
    exact Assembly.a_mono S hmhi
  have hagreeSeed : AgreesUntil rho rho'
      (Protocol.confirmation_time S.E (S.hc.opening_slot m)) :=
    AgreesUntil.mono hagree hseedCut
  have hfresh : fgSafetyProgressDeadline S rho rGST gap extra + 1 ≤
      fgSafetyProgressDeadline S rho rGST gap extra +
        2 * progressLag' gap extra + 1 + S.hc.η_SG :=
    (Nat.add_le_add_right
      (Nat.le_add_right (fgSafetyProgressDeadline S rho rGST gap extra)
        (2 * progressLag' gap extra)) 1).trans
      (Nat.le_add_right _ S.hc.η_SG)
  have hboot' := SettledBootstrapPreparedV4.transfer
    S adm.toNamedAdmissibleCore adm' hcom' hboot hfresh hagreeSeed
  have hlatest' := SettledBootstrapPreparedV4.LatestSeed.transfer
    S hlatest hagreeSeed
  have hfinality :=
    SettledBootstrapPreparedV4.finalizedRootsBelowAtRead_of_accountable
      S adm' hsb hboot' hheight
  have hwindows := preparedV4_windowAwake_of_prefix
    S adm hprefix hagree.honest_subset hcovered hawake
  have hcutPos : 0 < fgSafetyProgressDeadline S rho rGST gap extra +
      2 * progressLag' gap extra + 1 + S.hc.η_SG :=
    (Nat.zero_lt_succ
      (fgSafetyProgressDeadline S rho rGST gap extra +
        2 * progressLag' gap extra)).trans_le
      (Nat.le_add_right _ S.hc.η_SG)
  have hawake' : ∀ r,
      fgSafetyProgressDeadline S rho rGST gap extra +
        2 * progressLag' gap extra + 1 + S.hc.η_SG ≤ r →
      S.a (r - 1) ≤ rho'.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho'.honest S.hc.η_SG r :=
    fun r hr => hwindows r (hcutPos.trans_le hr)
  have hstartHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot m) ≤ rho'.horizon :=
    hseedCut.trans hcovered
  have hphase := SettledBootstrapPreparedV4.phaseShiftSafety_core
    S adm' hcom' hboot' hlatest' hawake' hfinality hstartHor hsb
  exact Proofs.HealingSurface.Handover.preparedV4_phaseShiftSafety_mono_cut hold hphase

/-- The corrected recovery-window bound closes bounded safety without a P7b
proof-layer pin. -/
theorem boundedSafetyRecovery_of_window
    (S : Setup V)
    (hwindow : ∀ rho rGST gap extra n,
      StrongRecoveryPrefix S rho rGST gap extra n →
      fgSafetyProgressDeadline S rho rGST gap extra +
        2 * progressLag' gap extra +
        max (1 + S.hc.η_SG) (gap + 3) ≤ n) :
    Statements.BoundedSafetyRecovery S := by
  apply boundedSafetyRecovery_of_pins S
  apply safety_after_boundedStrongPhase_complete_of_pins S
  intro rho rGST gap extra n adm hcom hbelow hrec hdelay hpost hstart hprefix
  apply safety_after_boundedStrongPhase_complete_of_window
    S adm hcom hbelow hrec hdelay hpost hstart hprefix
  exact hwindow rho rGST gap extra n
    { execution := adm.toExecutionValid
      synchrony := adm.toNamedSynchrony
      allAwake := adm.all_awake
      committees := hcom
      belowThird := hbelow
      recurrence := hrec
      timeout := hdelay
      postGST := hpost
      start := hstart
      horizon := hprefix }

#print axioms boundedSafetyRecovery_of_window

end Proofs
end DecoupledConsensusModel

end
