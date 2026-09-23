module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FixedHeightRootOpeningParent

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Fixed-height prepared proposal parent

This module isolates the prepared-parent proof from concrete runtime store
expressions. The candidate record takes the proposal stores as parameters, so
elaboration does not reduce `storeBeforeTime` or `proposerDutyStore`.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.NamedRecoveryRead
open Internal.PhaseGrades
open Proofs.Optimistic
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

structure FixedRootPreparedParentCandidate
    (S : Setup V) (rho : Run V) (H : Height) (q : Round)
    (w : V) (read : Time) (A : Block V) (target : NamedBlock V)
    (ceiling actionCeiling : Block V) (actionWitness : V)
    (fixed pre : Protocol.NamedStore V) (source : Protocol.Store V) : Prop where
  targetErase : target.erase = fixed.J
  targetRun : RunBlock S rho target
  targetHeight : (Protocol.derive_named S.E S.cfg target).h = H - 1
  targetHeightPositive : 0 < H - 1
  actionWitnessHonest : actionWitness ∈ rho.honest
  actionCeilingEq : actionCeiling =
    actionSGBlockAt S rho actionWitness (q - 1)
  ceilingUpper : ∀ v ∈ rho.honest,
    Block.Preceq (actionSGBlockAt S rho v (q - 1)) ceiling
  ceilingCone : NamedHonestVotesCone S rho (S.hc.opening_slot q - 1)
    (fun X => Block.Preceq ceiling X)
  ceilingRoot : Block.Preceq
    (Protocol.get_fg_root pre.toHealing.toFG) ceiling
  ceilingChoice : ceiling = A ∨ ceiling = actionCeiling
  anchorFiltered : A ∈
    Protocol.get_filtered_block_tree source.toHealing.toFG
  rootAtProposal : Protocol.get_fg_root pre.toHealing.toFG = target.erase
  hMaxAtProposal : pre.h_max = H




structure FixedRootPreparedTargetData
    (S : Setup V) (rho : Run V) (H : Height)
    (fixed pre : Protocol.NamedStore V) (target : NamedBlock V) : Prop where
  targetErase : target.erase = fixed.J
  targetRun : RunBlock S rho target
  targetHeight : (Protocol.derive_named S.E S.cfg target).h = H - 1
  targetHeightPositive : 0 < H - 1
  rootAtProposal : Protocol.get_fg_root pre.toHealing.toFG = target.erase
  hMaxAtProposal : pre.h_max = H

theorem fixedRoot_preparedTargetData_of_fixedRoot_abstract
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {w : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho H w read)
    {q : Round} (fixed pre : Protocol.NamedStore V)
    (hfixed : rho.storeBeforeTime S w read = fixed)
    (hpre : rho.storeBeforeTime S
      (S.E.proposer (S.hc.opening_slot q))
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) = pre)
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hpostRead : S.E.t_GST ≤ read)
    (hproposalDelay : read + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hproposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hproposalCap : honestHMaxAt S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) ≤ H) :
    ∃ target : NamedBlock V,
      FixedRootPreparedTargetData S rho H fixed pre target := by
  obtain ⟨target, htargetErase, htargetRun, htargetHeight⟩ :=
    fixedRoot_namedTarget_of_fixedRoot S hfix
  have htargetEraseFixed : target.erase = fixed.J := by
    rw [← hfixed]
    exact htargetErase
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  obtain ⟨hroot, hmax⟩ :=
    fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
      S adm hsb hfix hprop hpostRead hproposalDelay hproposalHor hproposalCap
  have hroot' : Protocol.get_fg_root pre.toHealing.toFG = target.erase := by
    rw [← hpre, htargetErase]
    exact hroot
  have hmax' : pre.h_max = H := by
    rw [← hpre]
    exact hmax
  exact ⟨target,
    { targetErase := htargetEraseFixed
      targetRun := htargetRun
      targetHeight := htargetHeight
      targetHeightPositive := hfix.targetHeightPositive
      rootAtProposal := hroot'
      hMaxAtProposal := hmax' }⟩

structure FixedRootPreparedAnchorData
    (S : Setup V) (rho : Run V) (q : Round) (A : Block V)
    (pre : Protocol.NamedStore V) (source : Protocol.Store V) : Prop where
  cone : NamedHonestVotesCone S rho (S.hc.opening_slot q - 1)
    (fun X => Block.Preceq A X)
  filtered : A ∈ Protocol.get_filtered_block_tree source.toHealing.toFG
  rootPreceq : Block.Preceq
    (Protocol.get_fg_root pre.toHealing.toFG) A




theorem fixedRoot_preparedAnchorGradeData_abstract
    (S : Setup V) {rho : Run V} {q : Round} {A : Block V}
    (pre : Protocol.NamedStore V) (source : Protocol.Store V)
    (hpre : rho.storeBeforeTime S
      (S.E.proposer (S.hc.opening_slot q))
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) = pre)
    (hsource : Protocol.proposerDutyStore S rho
      (S.hc.opening_slot q) = source)
    (hanchorSource : Protocol.fresh_anchor S.E S.hc
      source.toHealing q = some A) :
    Protocol.G1 S.E pre.toHealing.gradeView S.hc q A = true ∧
      A ∈ Protocol.get_filtered_block_tree source.toHealing.toFG ∧
      Protocol.get_fg_root source.toHealing.toFG =
        Protocol.get_fg_root pre.toHealing.toFG := by
  have hselected : Block.deepest?
      ((Protocol.get_filtered_block_tree source.toHealing.toFG).filter
        (fun B => Protocol.G1 S.E source.toHealing.gradeView S.hc q B = true)) =
      some A := hanchorSource
  have hAdata := Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hselected)
  have hAG1Pre : Protocol.G1 S.E pre.toHealing.gradeView S.hc q A = true := by
    have hAG1Duty : Protocol.G1 S.E source.toHealing.gradeView S.hc q A = true :=
      hAdata.2
    have hsourceG1 := fixedRoot_tickStore_G1 S pre
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) q A
    rw [← hsource, Protocol.proposerDutyStore, hpre] at hAG1Duty
    rw [hsourceG1] at hAG1Duty
    exact hAG1Duty
  have hsourceRoot : Protocol.get_fg_root source.toHealing.toFG =
      Protocol.get_fg_root pre.toHealing.toFG := by
    rw [← hsource, Protocol.proposerDutyStore, hpre]
    simp only [Proofs.Optimistic.tickStore, Protocol.Store.toHealing,
      Protocol.NamedStore.toHealing, Protocol.get_fg_root]
  exact ⟨hAG1Pre, hAdata.1, hsourceRoot⟩




theorem fixedRoot_actionG1_of_preparedGrade_abstract
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} {A : Block V} (pre : Protocol.NamedStore V)
    (hpre : rho.storeBeforeTime S
      (S.E.proposer (S.hc.opening_slot q))
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) = pre)
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hAG1Pre : Protocol.G1 S.E pre.toHealing.gradeView S.hc q A = true) :
    Protocol.G1 S.E
      (gradeViewAt S rho (S.E.proposer (S.hc.opening_slot q)) q)
      S.hc q A = true := by
  have hproposalLeAction :
      Protocol.proposal_time S.E (S.hc.opening_slot q) ≤ S.a q := by
    calc
      Protocol.proposal_time S.E (S.hc.opening_slot q) =
          S.hc.Γ_0 S.E.Δ q :=
        (Protocol.Γ_0_eq_proposal_time S.hc S.E q).symm
      _ ≤ S.hc.Γ_1 S.E.Δ q :=
        le_of_lt (Proofs.HealingLemmas.Γ_0_lt_Γ_1 S.hc S.E.Δ_pos q)
      _ ≤ S.hc.Γ_2 S.E.Δ q :=
        le_of_lt (Proofs.HealingLemmas.Γ_1_lt_Γ_2 S.hc S.E.Δ_pos q)
      _ ≤ S.a q := Γ_2_le_a S.hc S.E.Δ_pos q
  exact fixedRoot_G1_persists_from_read S adm hprop hpre
    (Protocol.Γ_0_eq_proposal_time S.hc S.E q).le
    hproposalLeAction hAG1Pre







theorem fixedRoot_preparedAnchorData_of_cone
    (S : Setup V) {rho : Run V} {q : Round} {A : Block V}
    (pre : Protocol.NamedStore V) (source : Protocol.Store V)
    (hcone : NamedHonestVotesCone S rho (S.hc.opening_slot q - 1)
      (fun X => Block.Preceq A X))
    (hfiltered : A ∈
      Protocol.get_filtered_block_tree source.toHealing.toFG)
    (hsourceRoot : Protocol.get_fg_root source.toHealing.toFG =
      Protocol.get_fg_root pre.toHealing.toFG) :
    FixedRootPreparedAnchorData S rho q A pre source := by
  have hrootA := Proofs.Records.preceq_get_fg_root_of_mem_filtered hfiltered
  rw [hsourceRoot] at hrootA
  exact ⟨hcone, hfiltered, hrootA⟩

theorem fixedRoot_preparedAnchorData_of_actionGrade
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {q : Round} {A : Block V}
    (pre : Protocol.NamedStore V) (source : Protocol.Store V)
    (hq : 0 < q)
    (hcanonical : SGTargetConeCanonicality S rho (q - 1)
      (S.hc.opening_slot q - 1))
    (hproposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hpostPreviousAction : S.E.t_GST ≤ S.a (q - 1))
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hAG1Action : Protocol.G1 S.E
      (gradeViewAt S rho (S.E.proposer (S.hc.opening_slot q)) q)
      S.hc q A = true)
    (hfiltered : A ∈
      Protocol.get_filtered_block_tree source.toHealing.toFG)
    (hsourceRoot : Protocol.get_fg_root source.toHealing.toFG =
      Protocol.get_fg_root pre.toHealing.toFG) :
    FixedRootPreparedAnchorData S rho q A pre source := by
  have hcut : S.hc.Γ_neg1 S.E.Δ ((q - 1) + 1) ≤ rho.horizon := by
    rw [Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hq))]
    exact (le_of_lt (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos q)).trans
      (by simpa only [Protocol.Γ_0_eq_proposal_time] using hproposalHor)
  have hqPredAdd : q - 1 + 1 = q :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hq))
  have hG1Pred : Protocol.G1 S.E
      (gradeViewAt S rho (S.E.proposer (S.hc.opening_slot q))
        ((q - 1) + 1)) S.hc ((q - 1) + 1) A = true := by
    simpa only [hqPredAdd] using hAG1Action
  have hcone := honestVotesCone_of_g1
    (r := q - 1) (s := S.hc.opening_slot q - 1)
    (w := S.E.proposer (S.hc.opening_slot q)) (B := A)
    S adm hfb hpostPreviousAction hcut hcanonical hprop hG1Pred
  exact fixedRoot_preparedAnchorData_of_cone
    S pre source hcone hfiltered hsourceRoot

theorem fixedRoot_preparedAnchorData_of_grade_abstract
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {q : Round} {A : Block V}
    (pre : Protocol.NamedStore V) (source : Protocol.Store V)
    (hpre : rho.storeBeforeTime S
      (S.E.proposer (S.hc.opening_slot q))
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) = pre)
    (hq : 0 < q)
    (hlock : SGTargetOpeningConeRootLock S rho H (q - 1)
      (S.hc.opening_slot q - 1))
    (hproposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hpostPreviousAction : S.E.t_GST ≤ S.a (q - 1))
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hAG1Pre : Protocol.G1 S.E pre.toHealing.gradeView S.hc q A = true)
    (hfiltered : A ∈
      Protocol.get_filtered_block_tree source.toHealing.toFG)
    (hsourceRoot : Protocol.get_fg_root source.toHealing.toFG =
      Protocol.get_fg_root pre.toHealing.toFG) :
    FixedRootPreparedAnchorData S rho q A pre source := by
  have hAG1Action := fixedRoot_actionG1_of_preparedGrade_abstract
    S adm pre hpre hprop hAG1Pre
  exact fixedRoot_preparedAnchorData_of_actionGrade
    S adm hcom hfb pre source hq hlock.canonical hproposalHor hpostPreviousAction
      hprop hAG1Action hfiltered hsourceRoot

theorem fixedRoot_preparedAnchorData_of_lock_abstract
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {q : Round} {A : Block V}
    (pre : Protocol.NamedStore V) (source : Protocol.Store V)
    (hpre : rho.storeBeforeTime S
      (S.E.proposer (S.hc.opening_slot q))
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) = pre)
    (hsource : Protocol.proposerDutyStore S rho
      (S.hc.opening_slot q) = source)
    (hq : 0 < q)
    (hlock : SGTargetOpeningConeRootLock S rho H (q - 1)
      (S.hc.opening_slot q - 1))
    (hproposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hpostPreviousAction : S.E.t_GST ≤ S.a (q - 1))
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hanchor : Protocol.fresh_anchor S.E S.hc
      (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot q)).toHealing q = some A) :
    FixedRootPreparedAnchorData S rho q A pre source := by
  have hanchorSource : Protocol.fresh_anchor S.E S.hc
      source.toHealing q = some A := by
    rw [← hsource]
    exact hanchor
  obtain ⟨hG1, hfiltered, hroot⟩ :=
    fixedRoot_preparedAnchorGradeData_abstract
      S pre source hpre hsource hanchorSource
  exact fixedRoot_preparedAnchorData_of_grade_abstract
    S adm hcom hfb pre source hpre hq hlock hproposalHor
      hpostPreviousAction hprop hG1 hfiltered hroot

theorem fixedRoot_parentCandidate_of_parts
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {H : Height} {q : Round} {w : V} {read : Time} {A : Block V}
    {fixed pre : Protocol.NamedStore V} {source : Protocol.Store V}
    {target : NamedBlock V}
    (htarget : FixedRootPreparedTargetData S rho H fixed pre target)
    (hanchor : FixedRootPreparedAnchorData S rho q A pre source)
    (hlock : SGTargetOpeningConeRootLock S rho H (q - 1)
      (S.hc.opening_slot q - 1)) :
    ∃ C C0 : Block V, ∃ vC : V,
      FixedRootPreparedParentCandidate
        S rho H q w read A target C C0 vC fixed pre source := by
  obtain ⟨C0, ⟨vC, hvC, hCvC⟩, hupper0, hcone0⟩ :=
    fixedRoot_commonActionCeiling_of_lock S adm hcom hlock
  have hcompatAC : Block.compatible A C0 = true :=
    sgTargetCompatible_of_honestVotesCone S hcom
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      adm.toNamedAdmissibleCore.toNamedRootCollisionFree hanchor.cone hcone0
  simp only [Block.compatible, Bool.or_eq_true] at hcompatAC
  rcases hcompatAC with hAC | hC0A
  · exact ⟨C0, C0, vC,
      { targetErase := htarget.targetErase
        targetRun := htarget.targetRun
        targetHeight := htarget.targetHeight
        targetHeightPositive := htarget.targetHeightPositive
        actionWitnessHonest := hvC
        actionCeilingEq := hCvC
        ceilingUpper := hupper0
        ceilingCone := hcone0
        ceilingRoot := Block.preceq_trans hanchor.rootPreceq hAC
        ceilingChoice := Or.inr rfl
        anchorFiltered := hanchor.filtered
        rootAtProposal := htarget.rootAtProposal
        hMaxAtProposal := htarget.hMaxAtProposal }⟩
  · refine ⟨A, C0, vC, ?_⟩
    exact
      { targetErase := htarget.targetErase
        targetRun := htarget.targetRun
        targetHeight := htarget.targetHeight
        targetHeightPositive := htarget.targetHeightPositive
        actionWitnessHonest := hvC
        actionCeilingEq := hCvC
        ceilingUpper := fun v hv => Block.preceq_trans (hupper0 v hv) hC0A
        ceilingCone := hanchor.cone
        ceilingRoot := hanchor.rootPreceq
        ceilingChoice := Or.inl rfl
        anchorFiltered := hanchor.filtered
        rootAtProposal := htarget.rootAtProposal
        hMaxAtProposal := htarget.hMaxAtProposal }

theorem fixedRoot_parentCandidate_of_fixedRootLock_abstract
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {w : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho H w read)
    {q : Round} {A : Block V}
    (fixed pre : Protocol.NamedStore V) (source : Protocol.Store V)
    (hfixed : rho.storeBeforeTime S w read = fixed)
    (hpre : rho.storeBeforeTime S
      (S.E.proposer (S.hc.opening_slot q))
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) = pre)
    (hsource : Protocol.proposerDutyStore S rho
      (S.hc.opening_slot q) = source)
    (hq : 0 < q)
    (hlock : SGTargetOpeningConeRootLock S rho H (q - 1)
      (S.hc.opening_slot q - 1))
    (hpostRead : S.E.t_GST ≤ read)
    (hproposalDelay : read + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hproposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hproposalCap : honestHMaxAt S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) ≤ H)
    (hpostCone : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot q - 1))
    (hpostPreviousAction : S.E.t_GST ≤ S.a (q - 1))
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hanchor : Protocol.fresh_anchor S.E S.hc
      (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot q)).toHealing q = some A) :
    ∃ target : NamedBlock V, ∃ C C0 : Block V, ∃ vC : V,
      FixedRootPreparedParentCandidate
        S rho H q w read A target C C0 vC fixed pre source := by
  obtain ⟨target, htarget⟩ :=
    fixedRoot_preparedTargetData_of_fixedRoot_abstract S adm hfb hfix
      fixed pre hfixed hpre hprop hpostRead hproposalDelay hproposalHor
      hproposalCap
  have hanchorData := fixedRoot_preparedAnchorData_of_lock_abstract
    S adm hcom hfb pre source hpre hsource hq hlock hproposalHor
      hpostPreviousAction hprop hanchor
  obtain ⟨C, C0, vC, hcandidate⟩ :=
    fixedRoot_parentCandidate_of_parts S adm hcom htarget hanchorData hlock
  exact ⟨target, C, C0, vC, hcandidate⟩

theorem fixedRoot_parentCandidate_of_fixedRootLock
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {w : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho H w read)
    {q : Round} {A : Block V} (hq : 0 < q)
    (hlock : SGTargetOpeningConeRootLock S rho H (q - 1)
      (S.hc.opening_slot q - 1))
    (hpostRead : S.E.t_GST ≤ read)
    (hproposalDelay : read + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hproposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hproposalCap : honestHMaxAt S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) ≤ H)
    (hpostCone : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot q - 1))
    (hpostPreviousAction : S.E.t_GST ≤ S.a (q - 1))
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hanchor : Protocol.fresh_anchor S.E S.hc
      (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot q)).toHealing q = some A) :
    ∃ target : NamedBlock V, ∃ C C0 : Block V, ∃ vC : V,
      FixedRootPreparedParentCandidate S rho H q w read A target C C0 vC
        (rho.storeBeforeTime S w read)
        (rho.storeBeforeTime S (S.E.proposer (S.hc.opening_slot q))
          (Protocol.proposal_time S.E (S.hc.opening_slot q)))
        (Protocol.proposerDutyStore S rho (S.hc.opening_slot q)) := by
  exact fixedRoot_parentCandidate_of_fixedRootLock_abstract
    S adm hcom hfb hfix
    (rho.storeBeforeTime S w read)
    (rho.storeBeforeTime S (S.E.proposer (S.hc.opening_slot q))
      (Protocol.proposal_time S.E (S.hc.opening_slot q)))
    (Protocol.proposerDutyStore S rho (S.hc.opening_slot q))
    rfl rfl rfl hq hlock hpostRead hproposalDelay hproposalHor
    hproposalCap hpostCone hpostPreviousAction hprop hanchor

theorem fixedRoot_preparedParent_of_candidate_abstract
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {w : V} {read : Time} {q : Round} {A : Block V}
    (fixed pre : Protocol.NamedStore V) (source : Protocol.Store V)
    (hpre : rho.storeBeforeTime S
      (S.E.proposer (S.hc.opening_slot q))
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) = pre)
    (hsource : Protocol.proposerDutyStore S rho
      (S.hc.opening_slot q) = source)
    (hq : 0 < q)
    (hpostCone : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot q - 1))
    (hproposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hpostPreviousAction : S.E.t_GST ≤ S.a (q - 1))
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hcut : S.hc.Γ_neg1 S.E.Δ ((q - 1) + 1) ≤ rho.horizon)
    {Jn : NamedBlock V} {C C0 : Block V} {vC : V}
    (hdata : FixedRootPreparedParentCandidate
      S rho H q w read A Jn C C0 vC fixed pre source) :
    Block.Preceq C (proposedParent S rho (S.hc.opening_slot q)) := by
  obtain ⟨hslo, _hshi, hsucc⟩ := lastInteriorSlot_before_opening S.hc hq
  have hs : 0 < S.hc.opening_slot q - 1 := by
    exact lt_of_lt_of_le (Nat.zero_lt_succ _) (by simpa only using hslo)
  have hprevLt : q - 1 < q := Nat.sub_lt hq (by decide)
  have hqPredAdd : q - 1 + 1 = q :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hq))
  have hrootPre : Protocol.get_fg_root pre.toHealing.toFG = Jn.erase :=
    hdata.rootAtProposal
  have hcapPre : pre.h_max ≤
      (Protocol.derive_named S.E S.cfg Jn).h + 1 := by
    have hHone : 1 ≤ H := Nat.le_of_lt
      (Nat.sub_pos_iff_lt.mp hdata.targetHeightPositive)
    rw [hdata.hMaxAtProposal, hdata.targetHeight]
    exact (Nat.sub_add_cancel hHone).ge
  have hrootCPre : Block.Preceq
      (Protocol.get_fg_root pre.toHealing.toFG) C := hdata.ceilingRoot
  have hrootC : Block.Preceq
      (Protocol.get_fg_root
        (proposalDutyRead S rho (S.hc.opening_slot q)).st.core.toHealing.toFG)
      C := by
    rw [← hpre] at hrootCPre
    simpa only [proposalDutyRead, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      hrootCPre
  have hanchorC := fixedRoot_preparedProposalAnchor_preceq_of_previousCarriers
    S adm hfb hpostPreviousAction hcut
      (by simpa only [hqPredAdd] using hproposalHor)
      hdata.ceilingUpper
      (by simpa only [hqPredAdd] using hprop)
      (by simpa only [hqPredAdd] using hrootC)
  have hroundSt : S.hc.round_of
      (proposalDutyRead S rho (S.hc.opening_slot q)).st.core.s = q := by
    simpa only [proposalDutyRead, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.slotOf_proposal_time] using
      round_of_opening_slot_eq_schedule S.hc q
  have hanchorC' : Block.Preceq
      (Protocol.get_sg_root_with
        (NamedProfile.gradeContract
          (proposalDutyRead S rho (S.hc.opening_slot q)).cache)
        S.E S.hc
        (proposalDutyRead S rho (S.hc.opening_slot q)).st.core.toHealing
        (S.hc.round_of
          (proposalDutyRead S rho (S.hc.opening_slot q)).st.core.s)) C := by
    change Block.Preceq
      (PhaseGrades.nodeAnchor S
        (proposalDutyRead S rho (S.hc.opening_slot q))
        (S.hc.round_of
          (proposalDutyRead S rho (S.hc.opening_slot q)).st.core.s)) C
    rw [hroundSt]
    simpa only [hqPredAdd] using hanchorC
  have hCsource : ∀ v ∈ rho.honest,
      actionSGBlockAt S rho v (q - 1) ∈
        (rho.storeBeforeTime S v (S.a (q - 1))).T := by
    intro v _hv
    exact actionSGBlockAt_mem_storeBeforeTime S rho v (q - 1)
  have hCmem : C ∈ pre.T := by
    rcases hdata.ceilingChoice with hCA | hCaction
    · rw [hCA]
      have hAsub := Proofs.Records.get_filtered_block_tree_subset
        source.toHealing.toFG hdata.anchorFiltered
      rw [← hsource] at hAsub
      rw [← hpre]
      simpa only [Protocol.proposerDutyStore, Proofs.Optimistic.tickStore] using hAsub
    · have htargetC : Block.Preceq Jn.erase C0 := by
        calc
          Jn.erase = Protocol.get_fg_root pre.toHealing.toFG := hrootPre.symm
          _ ⪯ C := hrootCPre
          _ = C0 := hCaction
      have hrootActual : Protocol.get_fg_root
          (rho.storeBeforeTime S (S.E.proposer (S.hc.opening_slot q))
            (Protocol.proposal_time S.E
              (S.hc.opening_slot q))).toHealing.toFG = Jn.erase := by
        rw [hpre]
        exact hrootPre
      have hcapActual :
          (rho.storeBeforeTime S (S.E.proposer (S.hc.opening_slot q))
            (Protocol.proposal_time S.E
              (S.hc.opening_slot q))).h_max ≤
            (Protocol.derive_named S.E S.cfg Jn).h + 1 := by
        rw [hpre]
        exact hcapPre
      have hpreC0 := fixedRoot_actionCarrier_mem_proposerRead S adm
        hdata.actionWitnessHonest hdata.targetRun htargetC
        (by simpa only [hdata.actionCeilingEq] using
          hCsource vC hdata.actionWitnessHonest)
        hprop hproposalHor hpostPreviousAction
        (Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt
          S hprevLt) hrootActual hcapActual
      rw [hpre] at hpreC0
      simpa only [hCaction] using hpreC0.1
  have hCactual : C ∈ (rho.storeBeforeTime S
      (S.E.proposer (S.hc.opening_slot q))
      (Protocol.proposal_time S.E (S.hc.opening_slot q))).T := by
    rw [hpre]
    exact hCmem
  obtain ⟨Cn, hCnbody, hCerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot q))
      (S.E.proposer (S.hc.opening_slot q)) hCactual
  have hCnrun : RunBlock S rho Cn :=
    fixedRoot_runBlock_of_body_at_read S adm hprop hCnbody
  have htargetC : Block.Preceq Jn.erase C := by
    calc
      Jn.erase = Protocol.get_fg_root pre.toHealing.toFG := hrootPre.symm
      _ ⪯ C := hrootCPre
  have hJCN : NamedBlock.Preceq Jn Cn := by
    exact Protocol.namedPreceq_of_runBlock_erase_preceq
      adm hdata.targetRun hCnrun (by simpa only [hCerase] using htargetC)
  have hCderive : pre.σ C =
      Protocol.derive_named S.E S.cfg Cn := by
    rw [← hCerase]
    have hd := Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot q))
      (S.E.proposer (S.hc.opening_slot q)) Cn hCnbody
    change (rho.storeBeforeTime S
      (S.E.proposer (S.hc.opening_slot q))
      (Protocol.proposal_time S.E (S.hc.opening_slot q))).σ Cn.erase = _ at hd
    rw [hpre] at hd
    exact hd
  have hheightJleC :
      (Protocol.derive_named S.E S.cfg Jn).h ≤
        (Protocol.derive_named S.E S.cfg Cn).h :=
    Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hJCN
  have hheightC : pre.h_max ≤ (pre.σ C).h + 1 := by
    rw [hdata.hMaxAtProposal, hCderive]
    calc
      H = (Protocol.derive_named S.E S.cfg Jn).h + 1 := by
        have hHone : 1 ≤ H := Nat.le_of_lt
          (Nat.sub_pos_iff_lt.mp hdata.targetHeightPositive)
        rw [hdata.targetHeight]
        exact (Nat.sub_add_cancel hHone).symm
      _ ≤ (Protocol.derive_named S.E S.cfg Cn).h + 1 :=
        Nat.add_le_add_right hheightJleC 1
  have hwitness : CanonicalConeWitness
      (proposalDutyRead S rho (S.hc.opening_slot q)).st.core C := by
    apply canonicalConeWitness_of_processedDescendant_and_hMax_le_succ
    · rw [← hpre] at hCmem
      simpa only [proposalDutyRead, proposerReadAt,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock] using hCmem
    · exact Block.preceq_self C
    · rw [← hpre] at hheightC
      simpa only [proposalDutyRead, proposerReadAt,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock] using hheightC
  have hsupportC := fixedRoot_preparedProposalConeSupport_of_namedCone
    S adm hcom hs hpostCone
      ((Protocol.support_cutoff_le_proposal_time_succ S.E
        (S.hc.opening_slot q - 1)).trans
        (by simpa only [hsucc] using hproposalHor))
      (by simpa only [hsucc] using hprop)
      (by simpa only [hsucc] using hrootC) hdata.ceilingCone
  have hvalidC : Protocol.VoteSetValid S.E
      ((proposalDutyRead S rho (S.hc.opening_slot q)).st.core.s - 1)
      (Protocol.proposer_view
        (proposalDutyRead S rho
          (S.hc.opening_slot q)).st.core.toHealing.toFG.toSG.toGoldfishStore
        (proposalDutyRead S rho
          (S.hc.opening_slot q)).st.core.s).toFinset := by
    simpa only [proposalDutyRead, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Protocol.proposerDutyStore, Proofs.Optimistic.tickStore] using
      Protocol.proposerDutyStore_proposer_view_valid S adm
        (S.hc.opening_slot q)
  have hcompat : Block.compatible
      (Protocol.get_fg_root
        (proposalDutyRead S rho
          (S.hc.opening_slot q)).st.core.toHealing.toFG) C = true := by
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inl hrootC
  exact fixedRoot_preparedProposalHead_preceq_of_cone S adm hcompat hwitness
    hanchorC' (by simpa only [hsucc] using hsupportC) hvalidC

theorem fixedRoot_preparedParent_of_candidate
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {w : V} {read : Time} {q : Round} {A : Block V}
    (hq : 0 < q)
    (hpostCone : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot q - 1))
    (hproposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hpostPreviousAction : S.E.t_GST ≤ S.a (q - 1))
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hcut : S.hc.Γ_neg1 S.E.Δ ((q - 1) + 1) ≤ rho.horizon)
    {Jn : NamedBlock V} {C C0 : Block V} {vC : V}
    (hdata : FixedRootPreparedParentCandidate S rho H q w read A Jn C C0 vC
      (rho.storeBeforeTime S w read)
      (rho.storeBeforeTime S (S.E.proposer (S.hc.opening_slot q))
        (Protocol.proposal_time S.E (S.hc.opening_slot q)))
      (Protocol.proposerDutyStore S rho (S.hc.opening_slot q))) :
    Block.Preceq C (proposedParent S rho (S.hc.opening_slot q)) := by
  exact fixedRoot_preparedParent_of_candidate_abstract S adm hcom hfb
    (rho.storeBeforeTime S w read)
    (rho.storeBeforeTime S (S.E.proposer (S.hc.opening_slot q))
      (Protocol.proposal_time S.E (S.hc.opening_slot q)))
    (Protocol.proposerDutyStore S rho (S.hc.opening_slot q)) rfl rfl
    hq hpostCone hproposalHor hpostPreviousAction hprop hcut hdata

theorem actionTarget_preceq_preparedOpeningParent_of_fixedRootLock
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {w : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho H w read)
    {q : Round} {A : Block V} (hq : 0 < q)
    (hlock : SGTargetOpeningConeRootLock S rho H (q - 1)
      (S.hc.opening_slot q - 1))
    (hpostRead : S.E.t_GST ≤ read)
    (hproposalDelay : read + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hproposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hproposalCap : honestHMaxAt S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) ≤ H)
    (hpostCone : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot q - 1))
    (hpostPreviousAction : S.E.t_GST ≤ S.a (q - 1))
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hanchor : Protocol.fresh_anchor S.E S.hc
      (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot q)).toHealing q = some A) :
    ∀ v ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho v (q - 1))
        (proposedParent S rho (S.hc.opening_slot q)) := by
  have hcut : S.hc.Γ_neg1 S.E.Δ ((q - 1) + 1) ≤ rho.horizon := by
    rw [Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hq))]
    exact (le_of_lt (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos q)).trans
      (by simpa only [Protocol.Γ_0_eq_proposal_time] using hproposalHor)
  obtain ⟨_target, C, _C0, _vC, hdata⟩ :=
    fixedRoot_parentCandidate_of_fixedRootLock S adm hcom hfb hfix hq
      hlock hpostRead hproposalDelay hproposalHor hproposalCap hpostCone
      hpostPreviousAction hprop hanchor
  have hparent := fixedRoot_preparedParent_of_candidate
    S adm hcom hfb hq hpostCone hproposalHor hpostPreviousAction hprop hcut hdata
  intro v hv
  exact Block.preceq_trans (hdata.ceilingUpper v hv) hparent

#print axioms fixedRoot_preparedTargetData_of_fixedRoot_abstract
#print axioms fixedRoot_preparedAnchorGradeData_abstract
#print axioms fixedRoot_actionG1_of_preparedGrade_abstract
#print axioms fixedRoot_preparedAnchorData_of_cone
#print axioms fixedRoot_preparedAnchorData_of_actionGrade
#print axioms fixedRoot_preparedAnchorData_of_grade_abstract
#print axioms fixedRoot_preparedAnchorData_of_lock_abstract
#print axioms fixedRoot_parentCandidate_of_parts
#print axioms fixedRoot_parentCandidate_of_fixedRootLock_abstract
#print axioms fixedRoot_parentCandidate_of_fixedRootLock
#print axioms fixedRoot_preparedParent_of_candidate_abstract
#print axioms fixedRoot_preparedParent_of_candidate
#print axioms actionTarget_preceq_preparedOpeningParent_of_fixedRootLock

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
