module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.TimeoutDelay
public import DecoupledConsensusProofs.Protocol.ChainState.CanonicalRegimeRound
public import DecoupledConsensusProofs.Protocol.ChainState.RawHeightCoverage
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordTargetHistory
public import DecoupledConsensusProofs.Execution.EmissionShape
public import DecoupledConsensusProofs.Protocol.ChainState.NamedNjGap
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecoveryTimeout
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HonestMajorityCore
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Protocol.ChainState.JustificationCertificates
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

/-!
# Migration residual discharges

This module discharges the Rule B residuals that follow from execution
provenance. A finality pair reads a justified action head, so its target has an
earlier honest height-target source in that head's carried justification
quorum. A stored lock comes from an earlier finality-pair emission; at a
recovery height, the nonfinality gap excludes that pair at its action head.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

set_option maxHeartbeats 500000

/-- Every honest finality-pair target has an earlier honest height-target
source. The source is an honest member of the target quorum carried by the
emitting action head's justification chain. -/
theorem finalityTargetHeightSource_of_honestWeightMajority
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hmajority : HonestWeightMajority S rho.honest) :
    FinalityTargetHeightSource S rho := by
  intro a ta haHon hemit h target hpair
  obtain ⟨i, hi, ha⟩ := hemit
  have htime : ta = S.a a.round :=
    (Proofs.Optimistic.emits_attest_shape S ⟨i, hi, ha⟩).2
  subst ta
  have hsch : ScheduleWellFormed S rho :=
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
  have haAction : a = actionAttestationAt S rho a.val_index a.round := by
    have hemitAction : NamedRun.emits S rho a.val_index
        (Object.attest a) (S.a a.round) := by
      exact ⟨i, hi, ha⟩
    obtain ⟨-, -, haeq⟩ :=
      (NamedActionSources.action_run_emission S rho hsch
        a.val_index a.round a).mp hemitAction
    exact haeq
  let ast := actionStoreAt S rho a.val_index a.round
  let gc := NamedProfile.gradeContract ast.cache
  obtain ⟨Hd, hHdDef, hround⟩ :=
    DecoupledConsensusModel.Proofs.round_action_finality_pair gc S.E S.hc
      (S.node a.val_index) ast.st.core.toHealing ast.record
  have hHdPre : Hd ∈
      (rho.stateBeforeTime S (S.a a.round) a.val_index).st.core.T := by
    rw [hHdDef]
    simpa only [actionHeadWith, ast] using
      (actionHeadWith_mem_storeBeforeTime (rho := rho) S a.val_index a.round)
  obtain ⟨D, hD, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (S.a a.round) a.val_index hHdPre
  have hσ : ast.st.core.σ =
      (rho.stateBeforeTime S (S.a a.round) a.val_index).st.core.σ := rfl
  have hpairAction :
      (Protocol.NamedActions.round_action_with gc S.E S.hc (S.node a.val_index)
        ast.st.core.toHealing ast.record).2.finality_pair = some ⟨h, target⟩ := by
    have hpairAction' :
        (actionAttestationAt S rho a.val_index a.round).finality_pair =
          some ⟨h, target⟩ := by
      rw [← haAction]
      exact hpair
    simpa only [actionAttestationAt, ast, actionStoreAt,
      Protocol.NamedDuties.attest_with] using
      hpairAction'
  have hround' :
      (Protocol.NamedActions.round_action_with gc S.E S.hc (S.node a.val_index)
        ast.st.core.toHealing ast.record).2.finality_pair =
      Protocol.finality_pair ast.record.legacy
        (ast.st.core.σ Hd).h_j (ast.st.core.σ Hd).J.root
        (ast.st.core.σ Hd).h_F := by
    simpa only [Protocol.Store.toHealing] using hround
  have hfp : Protocol.finality_pair ast.record.legacy
      (ast.st.core.σ Hd).h_j (ast.st.core.σ Hd).J.root
      (ast.st.core.σ Hd).h_F = some ⟨h, target⟩ := by
    rw [← hround']
    exact hpairAction
  have hheightAst : (ast.st.core.σ Hd).h_j = h :=
    DecoupledConsensusModel.Proofs.finality_pair_height hfp
  have hrootAst : (ast.st.core.σ Hd).J.root = target := by
    have hfpRoot := hfp
    simp only [Protocol.finality_pair] at hfpRoot
    split_ifs at hfpRoot
    simpa using congrArg FinalityPair.target (Option.some.inj hfpRoot)
  have hderive := Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho
    (S.a a.round) a.val_index D hD
  have hheightD : (Protocol.derive_named S.E S.cfg D).h_j = h := by
    rw [← hderive, hDerase, ← hσ]
    exact hheightAst
  have hrootD : (Protocol.derive_named S.E S.cfg D).J.root = target := by
    rw [← hderive, hDerase, ← hσ]
    exact hrootAst
  have hne : h ≠ 0 := by
    intro hz
    have hfin : (ast.st.core.σ Hd).h_F < (ast.st.core.σ Hd).h_j := by
      by_cases hlt : (ast.st.core.σ Hd).h_F < (ast.st.core.σ Hd).h_j
      · exact hlt
      · simp [Protocol.finality_pair, hlt] at hfp
    rw [hheightAst, hz] at hfin
    exact Nat.not_lt_zero _ hfin
  have hneD : (Protocol.derive_named S.E S.cfg D).h_j ≠ 0 := by
    intro hz
    exact hne (hheightD ▸ hz)
  obtain ⟨J, hJD, hJerase, Q, hQ, hwit⟩ :=
    NamedJustificationCertificates.justification_certificate S.E S.cfg D hneD
  obtain ⟨signer, hsignerQ, hsignerHonest⟩ :=
    Protocol.HonestWeightMajority.exists_honest_member_of_quorum hmajority hQ
  obtain ⟨carrier, b, hcarrierD, hb, hbVal, hbPair⟩ := hwit signer hsignerQ
  have hbHon : b.val_index ∈ rho.honest := by
    rw [hbVal]
    exact hsignerHonest
  have hJroot : J.root = target := by
    exact (Proofs.NamedWire.erase_root J).symm.trans
      ((congrArg Block.root hJerase).trans hrootD)
  have hbPair' : b.height_pair = NamedHeightPair.vote h target false := by
    simpa only [hheightD, hJroot] using hbPair
  obtain ⟨hbRound, hbEmit⟩ :=
    NamedOutageProvenance.honest_held_ancestor_row_before_action S rho hsch
      adm.toNamedAdmissibleCore.toNamedUnforgeable a.val_index a.round hD
      hcarrierD hb hbHon
  refine ⟨b, S.a b.round, hbHon, hbEmit,
    (action_strictMono S) hbRound, hbPair'⟩

/-- Compatibility wrapper for callers that still use the stronger fault bound.
The causal source theorem itself only needs an honest-weight majority. -/
theorem finalityTargetHeightSource_of_admissible
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest) :
    FinalityTargetHeightSource S rho :=
  finalityTargetHeightSource_of_honestWeightMajority S adm
    (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hfb)

/-- **Record-lock provenance over the named runtime.** A lock recorded at a
height traces back to an earlier honest tick whose emitted attestation carries
the finality pair at that height. This is the named twin of the parked
`RawHeightCoverageRun.recordLock_finalityEmission_before`, and consumers of
that retired name should reach for this one. -/
theorem recordLock_finalityEmission_before_migration
    (S : Setup V) (rho : Run V) (v : V) :
    ∀ (n : Nat) {H : Height} {T : BlockId},
      (rho.stateBefore S n v).record.legacy.lock H = some T →
        ∃ (i : Nat), i < n ∧ ∃ (t : Time) (a : NamedAttestation V),
          rho.events[i]? = some (Event.tick v t) ∧
            Object.attest a ∈
              (on_tick_emit S v (rho.stateBefore S i v) t).2 ∧
            a.finality_pair = some ⟨H, T⟩ := by
  intro n
  induction n with
  | zero =>
      intro H T hlock
      exact absurd hlock (by
        simp [Run.stateBefore, NamedRun.stateBefore, NamedWorld.init,
          NamedNode.initial, Protocol.NamedRecord.initial,
          Protocol.Record.initial])
  | succ n ih =>
      intro H T hlock
      change (NamedRun.stateBefore S rho (n + 1) v).record.legacy.lock H =
        some T at hlock
      cases hpre : (rho.stateBefore S n v).record.legacy.lock H with
      | some X =>
          have hmono :
              (rho.stateBefore S (n + 1) v).record.legacy.lock H = some X :=
            stateBefore_lock_mono S rho v (n + 1) (Nat.le_succ n) hpre
          have hXT : X = T := by
            rw [hlock] at hmono
            exact (Option.some.inj hmono).symm
          subst X
          obtain ⟨i, hi, t, a, hevent, hemitted, hpair⟩ := ih hpre
          exact ⟨i, Nat.lt_succ_of_lt hi, t, a, hevent, hemitted, hpair⟩
      | none =>
          change (NamedRun.stateBefore S rho n v).record.legacy.lock H =
            none at hpre
          have hstep := congrFun (Proofs.NamedRuntime.stateBefore_succ S rho n) v
          cases hevent : rho.events[n]? with
          | none =>
              rw [hstep, hevent] at hlock
              simp only [Option.toList, List.foldl_nil] at hlock
              exact absurd hlock (by rw [hpre]; simp)
          | some e =>
              cases e with
              | tick u t =>
                  by_cases huv : u = v
                  · subst u
                    have hpost :
                        (on_tick_emit S v (rho.stateBefore S n v) t).1.record.legacy.lock H =
                          some T := by
                      rw [← stateBefore_succ_record S rho hevent]
                      exact hlock
                    obtain ⟨a, hemitted, hpair⟩ :=
                      Protocol.on_tick_emit_lock_introduced
                        S v (rho.stateBefore S n v) t hpre hpost
                    exact ⟨n, Nat.lt_succ_self n, t, a, hevent,
                      hemitted, hpair⟩
                  · rw [hstep, hevent] at hlock
                    simp only [Option.toList, List.foldl_cons,
                      List.foldl_nil, NamedWorld.step,
                      Function.update_of_ne (Ne.symm huv)] at hlock
                    exact absurd hlock (by rw [hpre]; simp)
              | deliver u o t =>
                  by_cases huv : u = v
                  · subst u
                    rw [hstep, hevent] at hlock
                    simp only [Option.toList, List.foldl_cons,
                      List.foldl_nil, NamedWorld.step,
                      Function.update_self] at hlock
                    change (NamedNode.process S
                      (NamedRun.stateBefore S rho n v) o).record.legacy.lock H =
                        some T at hlock
                    rw [NamedNode.process_record_eq] at hlock
                    exact absurd hlock (by rw [hpre]; simp)
                  · rw [hstep, hevent] at hlock
                    simp only [Option.toList, List.foldl_cons,
                      List.foldl_nil, NamedWorld.step,
                      Function.update_of_ne (Ne.symm huv)] at hlock
                    exact absurd hlock (by rw [hpre]; simp)





#print axioms finalityTargetHeightSource_of_honestWeightMajority
#print axioms finalityTargetHeightSource_of_admissible

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
