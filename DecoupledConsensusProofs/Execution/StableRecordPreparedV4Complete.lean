module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.HandoverPreparedV4Transfer
public import DecoupledConsensusProofs.Execution.PreparedV4Finality
public import DecoupledConsensusProofs.Generic.StableRecordPreparedV4

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Complete stable-record producer from the prepared V4 handover -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Prefix participation from GST and suffix awake windows give each
continuation window whose preceding action is from GST. -/
private theorem preparedV4_awakeWindows_of_prefix
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

/-- The bounded V4 witness supplies the phase package and, after transfer,
the continuation-side latest/finality compatibility clause. -/
theorem stableRecordSafety_afterGST_preparedV4_of_pins
    (S : Setup V)
    (preparedV4_phase_of_pins :
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
                (S.hc.opening_slot m) P.erase)
    (latest_compatible_finalized_core_of_pins :
      ∀ {rho : Run V}, AdmissibleCore S rho →
      HonestCommittees S rho.honest →
      ∀ {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height},
      SettledBootstrapPreparedV4 S rho fresh base start P cap →
      SettledBootstrapPreparedV4.LatestSeed S rho start P →
      (∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
        AwakeWindowMajority S.E (fun v => (S.node v).awake)
          rho.honest S.hc.η_SG r) →
      FinalizedRootsBelowAtRead S rho cap P.erase →
      Protocol.confirmation_time S.E start ≤ rho.horizon →
      ∀ {v w : V}, v ∈ rho.honest → w ∈ rho.honest →
      ∀ {t u : Time},
      Protocol.confirmation_time S.E start ≤ t →
      Protocol.confirmation_time S.E start ≤ u →
      t ≤ rho.horizon → u ≤ rho.horizon →
      Block.compatible (rho.storeAt S v t).core.latest_confirmed
        (rho.storeAt S w u).core.F = true) :
    ∀ rho rGST gap extra n,
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
                (rho'.storeAt S v t').core.F = true) := by
  intro source rGST gap extra n hprefix
  obtain ⟨m, hmn, hmend, fresh, base, P, cap, hboot, hlatest, hfresh,
      hheight, hphase⟩ :=
    preparedV4_phase_of_pins source rGST gap extra n hprefix
  refine ⟨m, hmn, hmend, ?_⟩
  intro rho hcont
  have hseedCut : Protocol.confirmation_time S.E (S.hc.opening_slot m) ≤
      S.a (n + gap) := by
    rw [opening_confirmation_time_eq_action]
    exact Assembly.a_mono S hmend
  have hagreeSeed : AgreesUntil source rho
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
  have hcovered : S.a (n + gap) ≤ rho.horizon :=
    (a_le_healingBoundaryTime S (n + gap)).trans hcont.covered
  have hwindows := preparedV4_awakeWindows_of_prefix
    S hprefix.admissible hprefix.horizon hcont.agrees.honest_subset
      hcovered hcont.windows
  have hcutPos : 0 < base + S.hc.η_SG :=
    Nat.zero_lt_of_lt (Nat.add_lt_add_left S.hc.η_SG_ge_one base)
  have hawake' : ∀ r, base + S.hc.η_SG ≤ r →
      S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r :=
    fun r hr hhor => hwindows r (hcutPos.trans_le hr)
      (hboot.basePost.trans (Assembly.a_mono S
        (Nat.le_sub_of_add_le
          ((Nat.add_le_add_left S.hc.η_SG_ge_one base).trans hr)))) hhor
  have hstartHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot m) ≤ rho.horizon :=
    hseedCut.trans hcovered
  refine ⟨base + S.hc.η_SG, P.erase, hphase rho hcont, ?_⟩
  intro u hu v hv t t' ht ht' htHor htHor'
  exact latest_compatible_finalized_core_of_pins
    hcont.core hcont.committees hboot' hlatest' hawake' hfinality hstartHor
      hu hv ht ht' htHor htHor'

#print axioms stableRecordSafety_afterGST_preparedV4_of_pins

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
