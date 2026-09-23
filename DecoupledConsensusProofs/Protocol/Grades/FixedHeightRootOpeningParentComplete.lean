module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FixedHeightRootPreparedParent
public import DecoupledConsensusProofs.Protocol.Grades.CleanReadBridge

@[expose] public section

/-!
# Complete fixed-height opening-parent record

The prepared parent already bounds every preceding honest action carrier. A
relative G1 block has an honest maximal supporter in the same phase window.
The fixed-root ceiling makes every exact preceding action vote interpretable,
so that supporter is the exact preceding action carrier as well.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.NamedRecoveryRead
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

set_option maxHeartbeats 400000 in
private theorem namedG1_preceq_commonActionCeiling
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {q : Round} (hq : 0 < q)
    (hpost : S.E.t_GST ≤ S.a (q - 1))
    (hhor : domain S.E S.hc q .g1 ≤ rho.horizon)
    {C : Block V}
    (hupper : ∀ v ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho v (q - 1)) C)
    {w : V} (hw : w ∈ rho.honest)
    (hFC : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g1) w).st.core.F C)
    {B : Block V} (hG1 : namedG1At S rho w q B) :
    Block.Preceq B C := by
  let t := domain S.E S.hc q .g1
  let read := NamedRun.stateBeforeTime S rho t w
  have hpred : q - 1 + 1 = q := Nat.sub_add_cancel hq
  have hlatest : q - 1 ∈ Protocol.latest_window S.hc.η_SG q := by
    simpa only [hpred] using
      Protocol.pred_mem_latest_window S.hc.η_SG q
        S.hc.η_SG_ge_one hq
  have hdeadline : S.a (q - 1) + S.E.Δ ≤ early S.E S.hc q .g1 :=
    (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
      (Nat.sub_lt hq (by decide))).trans
      (NamedOutageClosure.q10_early_g2_le_early_g1 S q)
  have hactionHor : S.a (q - 1) ≤ rho.horizon := by
    exact (NamedOutageClosure.action_le_domain S S.hc.R_ge_three
      (Nat.sub_lt hq (by decide))).trans
      ((NamedOutageClosure.q10_domain_g2_lt_domain_g1 S q).le.trans hhor)
  have hearlyHor : early S.E S.hc q .g1 ≤ rho.horizon :=
    (NamedOutageClosure.q10_early_g1_le_domain_g2 S q).trans
      ((NamedOutageClosure.q10_domain_g2_lt_domain_g1 S q).le.trans hhor)
  have hearlyDomain : early S.E S.hc q .g1 ≤ t := by
    exact (NamedOutageClosure.q10_early_g1_le_domain_g2 S q).trans
      (NamedOutageClosure.q10_domain_g2_lt_domain_g1 S q).le
  have hinput : ∀ v ∈ rho.honest,
      Protocol.sgVote (actionAttestationAt S rho v (q - 1)).erase ∈
        DecoupledConsensusModel.Protocol.interpretedInputs
          read.st.core.toHealing.gradeView read.st.core.F S.hc.η_SG q
          (early S.E S.hc q .g1) v := by
    intro v hv
    have hemit := honest_emits_exact_actionAttestationAt S adm hv (q - 1)
      hactionHor
    let a := actionAttestationAt S rho v (q - 1)
    have hshape := actionAttestationAt_shape S rho v (q - 1)
    obtain ⟨i, hi, -, H, hH, hconfirmed⟩ :=
      Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
    have hHbody : H ∈ (NamedRun.stateBefore S rho i v).st.bodies := by
      change H ∈ (NamedRun.stateBefore S rho i v).st.bodies at hH
      exact hH
    have hHrun : RunBlock S rho H :=
      Proofs.Bridges.runBlock_of_stateBefore_mem S hv hHbody
    have hcarrierMem : actionSGBlockAt S rho v (q - 1) ∈
        (rho.storeBeforeTime S v (S.a (q - 1))).T :=
      actionSGBlockAt_mem_storeBeforeTime S rho v (q - 1)
    obtain ⟨D, hDerase, hDrun⟩ :=
      Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv
        (S.a (q - 1)) hcarrierMem
    have hconfirmedCarrier : a.confirmed =
        some (actionSGBlockAt S rho v (q - 1)).root := by
      simpa only [a] using hshape.2.2
    have hrootEq : H.erase.root = D.erase.root := by
      rw [Proofs.NamedWire.erase_root, hDerase]
      exact Option.some.inj (hconfirmed.symm.trans hconfirmedCarrier)
    have hHD : H.erase = D.erase :=
      Protocol.runBlock_eq_of_root_eq
        adm.toNamedAdmissibleCore.toNamedRootCollisionFree hHrun hDrun hrootEq
    have hHC : Block.Preceq H.erase C := by
      rw [hHD, hDerase]
      exact hupper v hv
    have hmem := action_vote_mem_interpretedInputs_after_gst_common_upper
      S adm.toNamedAdmissibleCore .g1 hlatest hv hw
      ⟨hshape.1, hshape.2.1, hemit⟩ ⟨i, hi, hH, hconfirmed⟩ hHC
      (by simpa only [read, t] using hFC)
      (by simpa only [hshape.2.1] using hpost)
      (by rw [hshape.2.1, max_eq_left hpost]; exact hdeadline)
      hearlyDomain hearlyHor
    simpa only [a, read, t] using hmem
  have hinterpreted : ∀ v ∈ rho.honest,
      (DecoupledConsensusModel.Protocol.interpretedInputs
        read.st.core.toHealing.gradeView read.st.core.F S.hc.η_SG q
        (early S.E S.hc q .g1) v).Nonempty := by
    intro v hv
    exact ⟨Protocol.sgVote (actionAttestationAt S rho v (q - 1)).erase,
      hinput v hv⟩
  have hrepresented : ∀ v ∈ rho.honest,
      Protocol.represented read.st.core.toHealing.sg_votes
        S.hc.η_SG v q = true := by
    intro v hv
    have hraw := (Finset.mem_filter.mp (hinput v hv)).1
    obtain ⟨hpool, hfields⟩ := Finset.mem_filter.mp hraw
    obtain ⟨k, hk, huk⟩ := Finset.mem_biUnion.mp hpool
    exact Protocol.represented_of_vote_mem
      (List.mem_toFinset.mp hk) huk hfields.1
  have hwindow := windowMajorityAt_of_honestWeightMajority_of_represented
    S (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird
      (S := S) hfb) hrepresented hinterpreted
  have hgrade : DecoupledConsensusModel.Protocol.gradeBool S.E
      read.st.core.toHealing.gradeView read.st.core.F S.hc.η_SG q
      (early S.E S.hc q .g1) (late S.E S.hc q .g1) B = true := by
    simpa only [namedG1At, PhaseGrades.storeGrade, PhaseGrades.phaseGrade,
      PhaseGrades.readAt, read, t] using hG1
  obtain ⟨v, hv, u, hu, head, hconf, hfind, -, hBhead, -, hmax⟩ :=
    exists_honest_max_positive_supporter_of_relativeGrade
      S.E S.hc hwindow hgrade
  have hemit := honest_emits_exact_actionAttestationAt S adm hv (q - 1)
    hactionHor
  let a := actionAttestationAt S rho v (q - 1)
  have hshape := actionAttestationAt_shape S rho v (q - 1)
  have hactionInput : Protocol.sgVote a.erase ∈
      DecoupledConsensusModel.Protocol.interpretedInputs
        read.st.core.toHealing.gradeView read.st.core.F S.hc.η_SG q
        (early S.E S.hc q .g1) v := by
    simpa only [a] using hinput v hv
  have hqle : q - 1 ≤ u.round := by
    have hle := hmax (Protocol.sgVote a.erase) hactionInput
    simpa only [Protocol.sgVote, NamedAttestation.erase, a, hshape.2.1] using hle
  have huraw := (Finset.mem_filter.mp hu).1
  obtain ⟨b, hbval, hbround, hbproj, huwindow, -, hbemit⟩ :=
    NamedOutageClosure.rawInputs_trace S rho
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      adm.toNamedAdmissibleCore.toNamedUnforgeable t
      (early S.E S.hc q .g1) w S.hc.η_SG q v hv
      (by simpa only [read] using huraw)
  have hule : u.round ≤ q - 1 :=
    Nat.le_sub_one_of_lt (NamedOutageClosure.window_bounds huwindow).2
  have huround : u.round = q - 1 := Nat.le_antisymm hule hqle
  have hbround : b.round = q - 1 := hbround.trans huround
  have hba : b = a := Proofs.Optimistic.emits_attest_unique S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hbemit hemit
    (hbround.trans hshape.2.1.symm)
  have huEq : u = Protocol.sgVote a.erase := by
    rw [← hbproj, hba]
  have hheadRoot : head.root = (actionSGBlockAt S rho v (q - 1)).root := by
    have huconf := congrArg Protocol.SGVote.confirmed huEq
    have huconf' : some head.root = a.confirmed := by
      simpa only [Protocol.sgVote, NamedAttestation.erase, hconf] using huconf
    have hsome : some head.root =
        some (actionSGBlockAt S rho v (q - 1)).root := by
      exact huconf'.trans hshape.2.2
    exact Option.some.inj hsome
  have hheadMem : head ∈ read.st.core.T := Proofs.HealingLemmas.find?_mem hfind
  obtain ⟨Head, hHeaderase, hHeadrun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hw t
      (by simpa only [read] using hheadMem)
  have hcarrierMem : actionSGBlockAt S rho v (q - 1) ∈
      (rho.storeBeforeTime S v (S.a (q - 1))).T :=
    actionSGBlockAt_mem_storeBeforeTime S rho v (q - 1)
  obtain ⟨Carrier, hCarrierErase, hCarrierRun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv
      (S.a (q - 1)) hcarrierMem
  have hnamedRoot : Head.erase.root = Carrier.erase.root := by
    rw [hHeaderase, hCarrierErase]
    exact hheadRoot
  have hheadCarrier : head = actionSGBlockAt S rho v (q - 1) := by
    rw [← hHeaderase, ← hCarrierErase]
    exact Protocol.runBlock_eq_of_root_eq
      adm.toNamedAdmissibleCore.toNamedRootCollisionFree
      hHeadrun hCarrierRun hnamedRoot
  exact Block.preceq_trans (by simpa only [hheadCarrier] using hBhead)
    (hupper v hv)

set_option maxHeartbeats 400000 in
private theorem namedG1_preceq_fixedRootActionCeiling
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {w : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho H w read)
    {q : Round} (hq : 0 < q)
    (hpostRead : S.E.t_GST ≤ read)
    (hproposalDelay : read + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hproposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hproposalCap : honestHMaxAt S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) ≤ H)
    (hpostPreviousAction : S.E.t_GST ≤ S.a (q - 1))
    {C : Block V}
    (hJC : Block.Preceq (rho.storeBeforeTime S w read).J C)
    (hupper : ∀ v ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho v (q - 1)) C)
    {x : V} (hx : x ∈ rho.honest) {B : Block V}
    (hG1 : namedG1At S rho x q B) :
    Block.Preceq B C := by
  have hopen : domain S.E S.hc q .g1 =
      Protocol.proposal_time S.E (S.hc.opening_slot q) := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    rfl
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  obtain ⟨hrootXRaw, -⟩ :=
    fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
      S adm hsb hfix hx hpostRead
        (by simpa only [hopen] using hproposalDelay)
        (by simpa only [hopen] using hproposalHor)
        (by simpa only [hopen] using hproposalCap)
  have hrootX : Protocol.get_fg_root
      (rho.storeBeforeTime S x (domain S.E S.hc q .g1)).toHealing.toFG =
        (rho.storeBeforeTime S w read).J := by
    simpa only [hopen] using hrootXRaw
  have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
    S rho (domain S.E S.hc q .g1) x
  have hFC : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g1) x).st.core.F C := by
    have hrootFloor := Proofs.Records.preceq_get_fg_root_of_F
      (st := (rho.storeBeforeTime S x
        (domain S.E S.hc q .g1)).toHealing.toFG) hFJ
    rw [hrootX] at hrootFloor
    exact Block.preceq_trans
      (by simpa only [Run.storeBeforeTime, Protocol.Store.toHealing,
        Protocol.NamedStore.toHealing] using hrootFloor) hJC
  exact namedG1_preceq_commonActionCeiling S adm hfb hq
    hpostPreviousAction (by simpa only [hopen] using hproposalHor)
    hupper hx hFC hG1

private theorem namedG1Concentration_of_commonCeiling
    (S : Setup V) {rho : Run V} {r : Round} {s : Slot} {C : Block V}
    (hcone : NamedHonestVotesCone S rho s (fun X => Block.Preceq C X))
    (hbelow : ∀ {x : V}, x ∈ rho.honest → ∀ {B : Block V},
      namedG1At S rho x (r + 1) B → Block.Preceq B C) :
    NamedG1Concentration S rho r s := by
  refine ⟨?_, ?_⟩
  · intro x B hx hG1
    have hBC : Block.Preceq B C := hbelow hx hG1
    intro y hy hcommittee
    obtain ⟨X, hCX, hXrun, hemit⟩ := hcone y hy hcommittee
    exact ⟨X, Block.preceq_trans hBC hCX, hXrun, hemit⟩
  · intro x₁ x₂ B₁ B₂ hx₁ hx₂ hG1₁ hG1₂
    exact Block.compatible_of_preceq_common
      (hbelow hx₁ hG1₁) (hbelow hx₂ hG1₂)

set_option maxHeartbeats 400000 in
private theorem fixedRoot_namedG1CommonCeiling
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {w : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho H w read)
    {q : Round} (hqTwo : 2 ≤ q)
    (hforms : NamedGradeFormsAt S rho (q - 1)
      (rho.storeBeforeTime S w read).J)
    (hwindow : ∀ v ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho v (S.a (q - 1))
        (rho.storeBeforeTime S w read).J)
    (hlock : SGTargetOpeningConeRootLock S rho H (q - 1)
      (S.hc.opening_slot q - 1))
    (hpostRead : S.E.t_GST ≤ read)
    (hproposalDelay : read + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hproposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hproposalCap : honestHMaxAt S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) ≤ H)
    (hpostPreviousAction : S.E.t_GST ≤ S.a (q - 1)) :
    ∃ C : Block V, ∃ v0 : V,
      v0 ∈ rho.honest ∧
        C = actionSGBlockAt S rho v0 (q - 1) ∧
        (∀ v ∈ rho.honest,
          Block.Preceq (actionSGBlockAt S rho v (q - 1)) C) ∧
        NamedHonestVotesCone S rho (S.hc.opening_slot q - 1)
          (fun X => Block.Preceq C X) ∧
        ∀ {x : V}, x ∈ rho.honest → ∀ {B : Block V},
          namedG1At S rho x q B → Block.Preceq B C := by
  let J := (rho.storeBeforeTime S w read).J
  have hq : 0 < q := (by decide : 0 < 2).trans_le hqTwo
  obtain ⟨C, ⟨v0, hv0, _hCv0⟩, hupper, hcone⟩ :=
    fixedRoot_commonActionCeiling_of_lock S adm hcom hlock
  have hqPrev : 0 < q - 1 :=
    Nat.sub_pos_of_lt ((by decide : 1 < 2).trans_le hqTwo)
  have hactionHor : S.a (q - 1) ≤ rho.horizon := by
    have hlt : q - 1 < q := Nat.sub_lt hq (by decide)
    exact (Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
      ((action_add_delta_le_openingProposal_of_round_lt S hlt).trans
        hproposalHor)
  have hJactive : J ∈ PhaseGrades.filteredTree
      (actionReadAt S rho v0 (q - 1)) := by
    exact namedGradeFormsAt_actionStore_of_window S hforms hv0
      (by simpa only [J] using hwindow v0 hv0)
  have hJC : Block.Preceq J C := by
    exact Block.preceq_trans
      (preceq_actionSGBlockAt_of_namedGradeFormsAt S
        adm.toNamedAdmissibleCore hqPrev hactionHor hforms hv0 hJactive)
      (hupper v0 hv0)
  refine ⟨C, v0, hv0, _hCv0, hupper, hcone, ?_⟩
  intro x hx B hG1
  exact namedG1_preceq_fixedRootActionCeiling S adm hfb hfix hq
    hpostRead hproposalDelay hproposalHor hproposalCap hpostPreviousAction
    (by simpa only [J] using hJC) hupper hx hG1

set_option maxHeartbeats 400000 in
theorem fixedRoot_namedG1CommonCeiling_public
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {w : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho H w read)
    {q : Round} (hqTwo : 2 ≤ q)
    (hforms : NamedGradeFormsAt S rho (q - 1)
      (rho.storeBeforeTime S w read).J)
    (hwindow : ∀ v ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho v (S.a (q - 1))
        (rho.storeBeforeTime S w read).J)
    (hlock : SGTargetOpeningConeRootLock S rho H (q - 1)
      (S.hc.opening_slot q - 1))
    (hpostRead : S.E.t_GST ≤ read)
    (hproposalDelay : read + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hproposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hproposalCap : honestHMaxAt S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) ≤ H)
    (hpostPreviousAction : S.E.t_GST ≤ S.a (q - 1)) :
    ∃ C : Block V, ∃ v0 : V,
      v0 ∈ rho.honest ∧
        C = actionSGBlockAt S rho v0 (q - 1) ∧
        (∀ v ∈ rho.honest,
          Block.Preceq (actionSGBlockAt S rho v (q - 1)) C) ∧
        NamedHonestVotesCone S rho (S.hc.opening_slot q - 1)
          (fun X => Block.Preceq C X) ∧
        ∀ {x : V}, x ∈ rho.honest → ∀ {B : Block V},
          namedG1At S rho x q B → Block.Preceq B C := by
  exact fixedRoot_namedG1CommonCeiling S adm hcom hfb hfix hqTwo hforms
    hwindow hlock hpostRead hproposalDelay hproposalHor hproposalCap
    hpostPreviousAction


set_option maxHeartbeats 400000 in
/-- A fixed-root opening lock concentrates all relative G1 blocks below one
canonical preceding-action ceiling. -/
theorem namedG1Concentration_of_fixedRootLock
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {w : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho H w read)
    {q : Round} (hqTwo : 2 ≤ q)
    (hforms : NamedGradeFormsAt S rho (q - 1)
      (rho.storeBeforeTime S w read).J)
    (hwindow : ∀ v ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho v (S.a (q - 1))
        (rho.storeBeforeTime S w read).J)
    (hlock : SGTargetOpeningConeRootLock S rho H (q - 1)
      (S.hc.opening_slot q - 1))
    (hpostRead : S.E.t_GST ≤ read)
    (hproposalDelay : read + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hproposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hproposalCap : honestHMaxAt S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) ≤ H)
    (hpostPreviousAction : S.E.t_GST ≤ S.a (q - 1)) :
    NamedG1Concentration S rho (q - 1)
      (S.hc.opening_slot q - 1) := by
  obtain ⟨C, _v0, _hv0, _hCv0, _hupper, hcone, hbelow⟩ :=
    fixedRoot_namedG1CommonCeiling
    S adm hcom hfb hfix hqTwo hforms hwindow hlock hpostRead
      hproposalDelay hproposalHor hproposalCap hpostPreviousAction
  have hpred : q - 1 + 1 = q := by
    exact Nat.sub_add_cancel ((by decide : 0 < 2).trans_le hqTwo)
  rw [← hpred] at hbelow
  exact namedG1Concentration_of_commonCeiling S hcone hbelow

set_option maxHeartbeats 400000 in
/-- The retained preceding grade makes the fixed target a relative G1 block at
the honest opening proposer's domain read. -/
theorem namedG1At_fixedRootTarget_of_retainedPreviousGrade
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {w : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho H w read)
    {q : Round} (hqTwo : 2 ≤ q)
    (hforms : NamedGradeFormsAt S rho (q - 1)
      (rho.storeBeforeTime S w read).J)
    (hwindow : ∀ v ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho v (S.a (q - 1))
        (rho.storeBeforeTime S w read).J)
    (hdomainWindow : ∀ v ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho v (domain S.E S.hc q .g2)
        (rho.storeBeforeTime S w read).J)
    (hpostRead : S.E.t_GST ≤ read)
    (hpostPreviousAction : S.E.t_GST ≤ S.a (q - 1))
    (hcut : S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon)
    (hactionHor : S.a q ≤ rho.horizon)
    (hactiveAtAction : ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S w read).J ∈
        Protocol.get_filtered_block_tree (healStoreAt S rho v q).toFG)
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hproposalDelay : read + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hproposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hproposalCap : honestHMaxAt S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) ≤ H) :
    namedG1At S rho (S.E.proposer (S.hc.opening_slot q)) q
      (rho.storeBeforeTime S w read).J := by
  let J := (rho.storeBeforeTime S w read).J
  let p := S.E.proposer (S.hc.opening_slot q)
  have hq : 0 < q := (by decide : 0 < 2).trans_le hqTwo
  have hqPrev : 0 < q - 1 :=
    Nat.sub_pos_of_lt ((by decide : 1 < 2).trans_le hqTwo)
  have hclean : CleanActionReadFor S rho (q - 1) J :=
    cleanActionReadFor_of_namedGradeFormsAt_and_retained_active
      S adm hqPrev (by simpa only [J] using hforms) hpostPreviousAction
      (by simpa only [Nat.sub_add_cancel hq] using hcut)
      (by simpa only [J] using hwindow)
      (by simpa only [J, Nat.sub_add_cancel hq] using hactiveAtAction)
      (by simpa only [J, Nat.sub_add_cancel hq] using hdomainWindow)
  have hmajority : HonestWeightMajority S rho.honest :=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S := S) hfb
  have hformsQ : NamedGradeFormsAt S rho q J := by
    simpa only [Nat.sub_add_cancel hq] using
      (namedGradeFormsAt_of_cleanActionRead S adm hmajority hclean)
  have hG2 : storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc q .g2) p).st q .g2 J = true := by
    exact (hformsQ p (by simpa only [p] using hprop)).2
  have hgst : S.E.t_GST ≤ early S.E S.hc q .g2 := by
    exact hpostPreviousAction.trans
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
        (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
          (Nat.sub_lt hq (by decide))))
  have hdomainG0Hor : domain S.E S.hc q .g0 ≤ rho.horizon :=
    (FrameForward.domain_le_a S q .g0).trans hactionHor
  have hopen : domain S.E S.hc q .g1 =
      Protocol.proposal_time S.E (S.hc.opening_slot q) := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    rfl
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  obtain ⟨hrootRaw, -⟩ :=
    fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
      S adm hsb hfix (by simpa only [p] using hprop) hpostRead
        (by simpa only [hopen] using hproposalDelay)
        (by simpa only [hopen] using hproposalHor)
        (by simpa only [hopen] using hproposalCap)
  have hroot : Protocol.get_fg_root
      (rho.storeBeforeTime S p (domain S.E S.hc q .g1)).toHealing.toFG = J := by
    simpa only [p, J, hopen] using hrootRaw
  have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
    S rho (domain S.E S.hc q .g1) p
  have hFg1J : Block.Preceq
      (rho.storeBeforeTime S p (domain S.E S.hc q .g1)).core.F J := by
    have hrootFloor := Proofs.Records.preceq_get_fg_root_of_F
      (st := (rho.storeBeforeTime S p
        (domain S.E S.hc q .g1)).toHealing.toFG) hFJ
    rw [hroot] at hrootFloor
    simpa only [Protocol.Store.toHealing] using hrootFloor
  have hforward : ∀ sender u root Head,
      u ∈ DecoupledConsensusModel.Protocol.interpretedInputs
        (readAt S rho (domain S.E S.hc q .g2) p).st.core.toHealing.gradeView
        (readAt S rho (domain S.E S.hc q .g2) p).st.core.F
        S.hc.η_SG q (early S.E S.hc q .g2) sender →
      DecoupledConsensusModel.Protocol.localCovers
        (readAt S rho (domain S.E S.hc q .g2) p).st.core.toHealing.gradeView
        u.confirmed J = true →
      u.confirmed = some root →
      Block.find? (readAt S rho
        (domain S.E S.hc q .g2) p).st.core.T root = some Head →
      Block.Preceq (readAt S rho
        (domain S.E S.hc q .g1) p).st.core.F Head := by
    intro sender u root Head _ hcover hconf hfind
    apply Block.preceq_trans
    · simpa only [PhaseGrades.readAt, Run.storeBeforeTime] using hFg1J
    · unfold DecoupledConsensusModel.Protocol.localCovers at hcover
      unfold Protocol.head_covers at hcover
      simp only [Protocol.HealingStore.gradeView, Protocol.Store.toHealing, hconf]
        at hcover
      rw [hfind] at hcover
      exact hcover
  have hbelow := crossReaderFinalizedBelow_of_finalitySafety_and_relay
    S adm hsb hgst hdomainG0Hor
      (by simpa only [p] using hprop) (by simpa only [p] using hprop) hforward
  have hguard := crossReaderBodyReadyGuard_of_finalizedBelow
    S adm.toNamedAdmissibleCore hq hgst hdomainG0Hor
      (by simpa only [p] using hprop) (by simpa only [p] using hprop) hbelow
  have hG1 := storeGrade_g1_of_storeGrade_g2_cross_reader
    S rho adm.toNamedAdmissibleCore q
      (twoCutoffDelivery_of_core S adm.toNamedAdmissibleCore hgst)
      hdomainG0Hor p p (by simpa only [p] using hprop)
      (by simpa only [p] using hprop) J hG2 hguard
  simpa only [namedG1At, p, J] using hG1

/-- Exact fixed-root retention and the prepared proposal read construct both
parent ceilings in the named relative-grade model. -/
theorem fixedHeightJustificationRootOpeningParentRun_of_fixedRootLock
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {w : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho H w read)
    {q : Round} {A : Block V} (hq : 0 < q)
    (_hforms : NamedGradeFormsAt S rho (q - 1)
      (rho.storeBeforeTime S w read).J)
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
    FixedHeightRootOpeningParentRun S rho q := by
  have hcut : S.hc.Γ_neg1 S.E.Δ ((q - 1) + 1) ≤ rho.horizon := by
    rw [Nat.sub_add_cancel hq]
    exact (le_of_lt
      (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos q)).trans
      (by simpa only [Protocol.Γ_0_eq_proposal_time] using hproposalHor)
  obtain ⟨target, C, _C0, _vC, hdata⟩ :=
    fixedRoot_parentCandidate_of_fixedRootLock S adm hcom hfb hfix hq
      hlock hpostRead hproposalDelay hproposalHor hproposalCap hpostCone
      hpostPreviousAction hprop hanchor
  have hparent := fixedRoot_preparedParent_of_candidate
    S adm hcom hfb hq hpostCone hproposalHor hpostPreviousAction hprop hcut hdata
  refine ⟨?_, ?_⟩
  · intro v hv
    exact Block.preceq_trans (hdata.ceilingUpper v hv) hparent
  · intro x hx B hG1
    have hopen : domain S.E S.hc q .g1 =
        Protocol.proposal_time S.E (S.hc.opening_slot q) := by
      rw [NamedOutageClosure.domain_g1_eq_opening]
      rfl
    have hsb : SlashableBound S rho :=
      slashableBound_of_admissible_belowOneThird S adm hfb
    obtain ⟨hrootXRaw, -⟩ :=
      fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
        S adm hsb hfix hx hpostRead
          (by simpa only [hopen] using hproposalDelay)
          (by simpa only [hopen] using hproposalHor)
          (by simpa only [hopen] using hproposalCap)
    have hrootX : Protocol.get_fg_root
        (rho.storeBeforeTime S x (domain S.E S.hc q .g1)).toHealing.toFG =
          target.erase := by
      simpa only [hopen] using hrootXRaw.trans (hdata.targetErase.symm)
    have hrootC : Block.Preceq target.erase C := by
      rw [← hdata.rootAtProposal]
      exact hdata.ceilingRoot
    have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
      S rho (domain S.E S.hc q .g1) x
    have hFC : Block.Preceq
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g1) x).st.core.F C :=
      Block.preceq_trans
        (by
          have hrootFloor := Proofs.Records.preceq_get_fg_root_of_F
            (st := (rho.storeBeforeTime S x
              (domain S.E S.hc q .g1)).toHealing.toFG) hFJ
          rw [hrootX] at hrootFloor
          simpa only [Run.storeBeforeTime, Protocol.Store.toHealing,
            Protocol.NamedStore.toHealing] using hrootFloor)
        hrootC
    have hBC := namedG1_preceq_commonActionCeiling S adm hfb hq
      hpostPreviousAction (by simpa only [hopen] using hproposalHor)
      hdata.ceilingUpper hx hFC hG1
    exact Block.preceq_trans hBC hparent

#print axioms fixedHeightJustificationRootOpeningParentRun_of_fixedRootLock
#print axioms fixedRoot_namedG1CommonCeiling_public
#print axioms namedG1Concentration_of_fixedRootLock
#print axioms namedG1At_fixedRootTarget_of_retainedPreviousGrade

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
