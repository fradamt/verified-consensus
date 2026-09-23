module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.RecoveryFGRoundAgreement
public import DecoupledConsensusProofs.Protocol.Schedule.SeedBoundaryConeLead
public import DecoupledConsensusProofs.Protocol.Grades.SeedFinalizedCanonical
public import DecoupledConsensusProofs.Execution.SeedGradeExistence
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGCompatibleHistory
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGCompatibleBootstrap
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryHandoffCore
public import DecoupledConsensusProofs.Protocol.Schedule.WeakGoldfishCone
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryGenuineClearNextVote
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.WeakConfirmationSupport
public import DecoupledConsensusProofs.Protocol.Grades.WeakBootstrapSG
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.WeakBootstrapGradePersistence
public import DecoupledConsensusProofs.Protocol.Grades.WeakBootstrapAction
public import DecoupledConsensusProofs.Protocol.Store.WeakSGHistory
public import DecoupledConsensusProofs.Protocol.Grades.Q31_actionSGBlock_tiers

@[expose] public section

/-!
# SG bootstrap from a G2-covered recovery checkpoint

The named-runtime proof is blocked at the SG-output transport step. The
pre-rewrite declarations are retained in the Open records below.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]



private theorem compatible_lower_right {B C T : Block V}
    (hBC : Block.compatible B C = true) (hTC : Block.Preceq T C) :
    Block.compatible B T = true := by
  rcases (show Block.Preceq B C ∨ Block.Preceq C B by
    simpa only [Block.compatible, Bool.or_eq_true] using hBC) with h | h
  · exact Block.compatible_of_preceq_common h hTC
  · simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr (Block.preceq_trans hTC h)
private theorem relative_gradeBool_zero_local
    (E : Env V) (gv : Protocol.GradeView V) (F : Block V)
    (eta : Round) (early late : Time) (B : Block V) :
    DecoupledConsensusModel.Protocol.gradeBool E gv F eta 0 early late B = false := by
  simp [DecoupledConsensusModel.Protocol.gradeBool,
    DecoupledConsensusModel.Protocol.positive, DecoupledConsensusModel.Protocol.opposing,
    DecoupledConsensusModel.Protocol.readyView, DecoupledConsensusModel.Protocol.rawView,
    DecoupledConsensusModel.Protocol.interpretedInputs, DecoupledConsensusModel.Protocol.rawInputs,
    Protocol.latest_window_zero, DecoupledConsensusModel.Protocol.Supports,
    DecoupledConsensusModel.Protocol.Opposes, DecoupledConsensusModel.Protocol.CleanFrom]

private theorem selectedQ2_round_pos_local
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} {r : Round} {Q : Block V}
    (hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r = some Q) :
    0 < r := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have hgrade := selectedQ2_storeGrade_at_g2Domain S adm hQ
  rw [hzero] at hgrade
  simp only [PhaseGrades.storeGrade, PhaseGrades.phaseGrade] at hgrade
  rw [relative_gradeBool_zero_local] at hgrade
  cases hgrade







/-- A retained named selected Q2 above the checkpoint and the prepared read
window control every honest SG output in the source round. -/
theorem PrefixFGSelectorConeAt.sgEmissionsCompatible_sameRound_of_G2_cover_named
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked hF0 : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Q : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : FirstHeightProgressAt S rho (blocked + 1) first)
    (hcap : HonestPrefixFinalityCap S rho first hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (ready : GradeRoundReady S rho a.round)
    (hselected : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Q.erase)
    (hQmem : Q ∈ (actionStoreAt S rho a.val_index a.round).st.bodies)
    (hQheight : (Protocol.derive_named S.E S.cfg Q).h = blocked + 1)
    (hTQ : Block.Preceq T Q.erase)
    (hhistory : ∀ w ∈ rho.honest, previousSGWindowHistory S rho w
      (actionReadAt S rho w a.round) a.round T) :
    HonestSGEmissionsCompatibleAtRound S rho a.round T := by
  let cut := strictEventIndex rho (S.a a.round)
  have hcut : cut < first :=
    hseed.actionPrefix_lt adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
  have hcapCut := honestPrefixFinalityCap_of_le S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hcut.le hcap
  have hfrontier : honestHMaxBeforeIndex S rho cut < blocked + 2 :=
    (hfirst.before cut hcut).trans_lt (Nat.lt_succ_self (blocked + 1))
  have hhor : S.a a.round ≤ rho.horizon := hseed.actionHorizon adm
  have _hr : 0 < a.round := selectedQ2_round_pos_local S adm hselected
  intro w hw _
  have hactiveAction : Q.erase ∈ Protocol.get_filtered_block_tree
      (actionStoreAt S rho w a.round).st.core.toHealing.toFG := by
    have hactive := (selectedQ2_filtered_at_action_and_openingVote_of_prefixCap
      S adm hbelow ready hseed.signerHonest hselected hQmem hcapCut hrec
        hQheight (Nat.le_refl cut) hfrontier hw).1
    simpa only [PhaseGrades.filteredTree,
      Internal.NamedRecoveryRead.actionDutyRead, actionReadAt] using hactive
  have hrootQ : Block.Preceq
      (Protocol.get_fg_root
        (actionStoreAt S rho w a.round).st.core.toHealing.toFG) Q.erase :=
    Proofs.Records.preceq_get_fg_root_of_mem_filtered hactiveAction
  have hroot : Block.compatible
      (Protocol.get_fg_root
        (actionStoreAt S rho w a.round).st.core.toHealing.toFG) T = true :=
    Block.compatible_of_preceq_common hrootQ hTQ
  have hlive : Block.compatible
      (actionStoreAt S rho w a.round).live_confirmed T = true := by
    rcases actionStoreAt_liveConfirmed_genuine_or_fgRoot S rho w a.round with
      ⟨C, hgenuine, hC⟩ | ⟨R, hRroot, hRlive⟩
    · rw [← hC]
      have hQC := selectedG2_compatible_genuineOpening_of_recoveryPrefix
        S adm hcom hbelow ready hseed.signerHonest hw hselected hQmem
          (by
            simpa only [Internal.NamedRecoveryRead.confirmationInputRead,
              opening_confirmation_time_eq_action] using hgenuine)
          hcapCut hrec hQheight (Nat.le_refl cut) hfrontier hhor
      exact compatible_lower_right
        (by simpa only [Block.compatible, Bool.or_comm] using hQC) hTQ
    · rw [← hRlive, hRroot]
      exact Block.compatible_of_preceq_common hrootQ hTQ
  exact actionSGBlock_compatible_of_previousSGHistory_at_round
    S adm (hhistory w hw) hhor hw hroot hlive

#print axioms PrefixFGSelectorConeAt.sgEmissionsCompatible_sameRound_of_G2_cover_named

/-- The same named SG-output transport from a named predecessor frame. -/
theorem PrefixFGSelectorConeAt.sgEmissionsCompatible_sameRound_of_G2_cover_of_frameN
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Q Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    (hframe : HeightRegimeFrameN S rho blocked (first - 1) Tprev c0)
    (ready : GradeRoundReady S rho a.round)
    (hK6Q2 : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase →
      VoterAnchorSourceQ2Inputs S rho a.round a.val_index Cfg.erase)
    (hK6Clear : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round ≠ some Cfg.erase →
      VoterAnchorSourceClearInputs S rho a.round a.val_index Cfg.erase)
    (hselected : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Q.erase)
    (hQmem : Q ∈ (actionStoreAt S rho a.val_index a.round).st.bodies)
    (hQheight : (Protocol.derive_named S.E S.cfg Q).h = blocked + 1)
    (hTQ : Block.Preceq T Q.erase)
    (hhistory : ∀ w ∈ rho.honest, previousSGWindowHistory S rho w
      (actionReadAt S rho w a.round) a.round T) :
    HonestSGEmissionsCompatibleAtRound S rho a.round T := by
  let cut := strictEventIndex rho (S.a a.round)
  have hcut : cut < first :=
    hseed.actionPrefix_lt adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
  have hcutFrame : cut ≤ first - 1 := Nat.le_sub_one_of_lt hcut
  have hframeCut := hframe.mono hcutFrame
  have hfrontier : honestHMaxBeforeIndex S rho cut < blocked + 2 :=
    (hfirst.before cut hcut).trans_lt (Nat.lt_succ_self (blocked + 1))
  have hhor : S.a a.round ≤ rho.horizon := hseed.actionHorizon adm
  have _hr : 0 < a.round := selectedQ2_round_pos_local S adm hselected
  obtain ⟨K, _, hKT0, hKh, hKCfg, hKrun⟩ :=
    action_named_checkpoint S adm hseed.signerHonest hseed.sourceMem
  have hKT : K.erase = T := hKT0.trans hseed.checkpointDerived.symm
  have hKheight : (Protocol.derive_named S.E S.cfg K).h = blocked + 1 :=
    hKh.trans hseed.sourceDerivedHeight
  have hTprevCfg : Block.Preceq Tprev.erase Cfg.erase :=
    hframe.namedSourceAbove a.val_index hseed.signerHonest a.round
      hcutFrame hhor Cfg hseed.sourceMem hseed.exactFGSource
        hseed.sourceDerivedHeight
  have hTprevK : Block.Preceq Tprev.erase K.erase := by
    rcases Block.preceq_linear (Proofs.NamedWire.erase_preceq hKCfg) hTprevCfg with
      hKTprev | hTprevK
    · obtain ⟨K', hK'Tprev, hK'erase⟩ :=
        Proofs.NamedAncestry.erased_ancestor_lift Tprev hKTprev
      have hK'run : RunBlock S rho K' :=
        Proofs.NamedRuntime.blockInRun_of_ancestor S rho hframe.prevRun hK'Tprev
      have hK'eq : K' = K := by
        apply adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
          K' K hK'run hKrun K' K
          (Or.inl (Proofs.NamedAncestry.named_self K'))
          (Or.inr (Proofs.NamedAncestry.named_self K))
        rw [← Proofs.NamedWire.erase_root K', hK'erase, Proofs.NamedWire.erase_root]
      have hmono := Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hK'Tprev
      rw [hK'eq, hKheight] at hmono
      exact False.elim
        (Nat.not_succ_le_self blocked (hmono.trans hframe.prevHeight))
    · exact hTprevK
  have hTprevQ : Block.Preceq Tprev.erase Q.erase :=
    Block.preceq_trans (by simpa only [hKT] using hTprevK) hTQ
  intro w hw _
  have hrootBound := (hseed.checkpointFiltered_at_read_of_frameN
    adm hfirst hframe ready hK6Q2 hK6Clear (le_refl (S.a a.round))
      hcut hw).2.1
  have hroot : Block.compatible
      (Protocol.get_fg_root
        (actionStoreAt S rho w a.round).st.core.toHealing.toFG) T = true := by
    have hpre : Block.Preceq
        (Protocol.get_fg_root
          (actionStoreAt S rho w a.round).st.core.toHealing.toFG) T := by
      simpa only [actionStoreAt_fgRoot_eq_storeBeforeTime] using hrootBound
    simpa only [Block.compatible, Bool.or_eq_true] using Or.inl hpre
  have hlive : Block.compatible
      (actionStoreAt S rho w a.round).live_confirmed T = true := by
    rcases actionStoreAt_liveConfirmed_genuine_or_fgRoot S rho w a.round with
      ⟨C, hgenuine, hC⟩ | ⟨R, hRroot, hRlive⟩
    · rw [← hC]
      have hQC := selectedG2_compatible_genuineOpening_of_frameN
        S adm hcom hbelow ready hseed.signerHonest hw hselected hQmem
          (by
            simpa only [Internal.NamedRecoveryRead.confirmationInputRead,
              opening_confirmation_time_eq_action] using hgenuine)
          hframeCut hQheight hTprevQ (Nat.le_refl cut) hfrontier hhor
      exact compatible_lower_right
        (by simpa only [Block.compatible, Bool.or_comm] using hQC) hTQ
    · rw [← hRlive, hRroot]
      exact hroot
  exact actionSGBlock_compatible_of_previousSGHistory_at_round
    S adm (hhistory w hw) hhor hw hroot hlive

#print axioms PrefixFGSelectorConeAt.sgEmissionsCompatible_sameRound_of_G2_cover_of_frameN



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
