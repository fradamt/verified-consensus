module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.Grades.NamedDuties
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsBridge
public import DecoupledConsensusProofs.Execution.MovingChainBandCover
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.MovingChainSlotStep
public import DecoupledConsensusProofs.Protocol.Grades.RelativeSupporter
public import DecoupledConsensusProofs.Protocol.ValidatorClient.Schedule
public import DecoupledConsensusProofs.Protocol.Grades.Persistence
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedActivity

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Predecessor source existence over the named moving fold

This leaf ports the source part of earlier's round-floor route to the prepared
grade contract. The prepared action freezes the round's G2 result at its
G2-domain read. The lower helper therefore takes processed membership and
the relative grade at that read, rather than requiring filtered-tree
membership there. The action-frame bridge then supplies the selected Q2 and
the clear-walk conclusion.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Protocol
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem w4src_deepest_clear_eq_tip {floor : Option (Block V)} {C : Block V}
    {test : Block V → Bool}
    (hfloor : floor.elim True (fun a => Block.preceq a C = true))
    (htest : test C = true) :
    Protocol.deepest_clear floor C test = some C := by
  have hmem : C ∈ Protocol.chain_of C := by
    cases C with
    | genesis => simp [Protocol.chain_of, Protocol.chain_up, Block.depth]
    | node p s r gv gsv ats i =>
        simp [Protocol.chain_of, Protocol.chain_up, Block.depth, Block.parent?]
  have hsome : (Protocol.deepest_clear floor C test).isSome = true :=
    deepest_clear_isSome_of_mem hfloor hmem htest
  obtain ⟨L, hL⟩ := Option.isSome_iff_exists.mp hsome
  have hCmem : C ∈ ((Protocol.chain_of C).toFinset.filter (fun B =>
      floor.elim true (fun anchor => Block.preceq anchor B) = true ∧
        test B = true)) := by
    refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hmem, ?_, htest⟩
    cases floor with
    | none => rfl
    | some a => simpa using hfloor
  have hLC : Block.Preceq L C := Proofs.Engine.deepest_clear_preceq hL
  have hCL : Block.Preceq C L := by
    refine deepest?_dominates hL hCmem ?_
    exact Block.compatible_of_preceq_common (Block.preceq_self C) hLC
  have hEq : L = C := Block.preceq_antisymm hLC hCL
  simpa [hEq] using hL

private theorem w4src_actionCarrier_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} :
    ∃ B : NamedBlock V,
      B.erase = actionSGBlockAt S rho v r ∧
        B ∈ (actionStoreAt S rho v r).st.bodies ∧ RunBlock S rho B := by
  have hfiltered := actionSGBlockAt_mem_filtered_actionStore S adm v r
  have hmemAction : actionSGBlockAt S rho v r ∈
      (actionStoreAt S rho v r).st.core.T :=
    mem_T_of_mem_filteredTree hfiltered
  have hmem : actionSGBlockAt S rho v r ∈
      (rho.storeBeforeTime S v (S.a r)).T := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hmemAction
  obtain ⟨B, hBbody, hBerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho (S.a r) v hmem
  have hBaction : B ∈ (actionStoreAt S rho v r).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hBbody
  have hBrun : RunBlock S rho B := by
    obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.a r)
    have hB' : B ∈ (rho.stateBefore S n v).st.bodies := by
      simpa only [hn] using hBbody
    exact Proofs.Bridges.runBlock_of_stateBefore_mem S hv hB'
  exact ⟨B, hBerase, hBaction, hBrun⟩

private theorem w4src_actionHead_eq_carrier
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round}
    {a : NamedAttestation V} {H : NamedBlock V}
    (ha : a = actionAttestationAt S rho v r)
    (hhead : ∃ i : Nat, rho.events[i]? = some (.tick v (S.a r)) ∧
      H ∈ (NamedActionReads.actionReadFrom S
        (NamedRun.stateBefore S rho i v) a.round).st.bodies ∧
      a.confirmed = some H.root) :
    H.erase = actionSGBlockAt S rho v r := by
  obtain ⟨i, hi, hHbody, hconfirmed⟩ := hhead
  have hHrun : RunBlock S rho H :=
    Proofs.NamedRuntime.blockInRun_of_direct S rho
      (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hHbody)
  obtain ⟨B, hBerase, hBbody, hBrun⟩ :=
    w4src_actionCarrier_named S adm hv (r := r)
  have hroot : H.root = B.root := by
    have hconfirmed' : a.confirmed =
        some (actionSGBlockAt S rho v r).root := by
      rw [ha]
      exact (actionAttestationAt_shape S rho v r).2.2
    have hroot' : H.root = (actionSGBlockAt S rho v r).root :=
      Option.some.inj (hconfirmed.symm.trans hconfirmed')
    calc
      H.root = (actionSGBlockAt S rho v r).root := hroot'
      _ = B.erase.root := by rw [hBerase]
      _ = B.root := Proofs.NamedWire.erase_root B
  have hEq := adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
    H B hHrun hBrun H B (Or.inl (Proofs.NamedAncestry.named_self H))
      (Or.inr (Proofs.NamedAncestry.named_self B)) hroot
  exact (congrArg NamedBlock.erase hEq).trans hBerase

private theorem w4src_strict_finality_mono_between
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    (w : V) {c d : Time} (hcd : c ≤ d) :
    Block.Preceq (rho.storeBeforeTime S w c).F
      (rho.storeBeforeTime S w d).F := by
  let ic := (rho.events.filter (fun e => decide (e.time < c))).length
  let id := (rho.events.filter (fun e => decide (e.time < d))).length
  have hc : rho.storeBeforeTime S w c =
      (rho.stateBefore S ic w).st := by
    unfold Run.storeBeforeTime
    exact congrArg NamedNodeState.st (congrFun
      (Proofs.Optimistic.stateBeforeTime_eq_take S sch c) w)
  have hd : rho.storeBeforeTime S w d =
      (rho.stateBefore S id w).st := by
    unfold Run.storeBeforeTime
    exact congrArg NamedNodeState.st (congrFun
      (Proofs.Optimistic.stateBeforeTime_eq_take S sch d) w)
  have hidx : ic ≤ id := by
    dsimp only [ic, id, strictEventIndex]
    exact strictEventIndex_mono rho hcd
  rw [hc, hd]
  exact Proofs.NamedRuntime.stateBefore_F_mono S rho w hidx

private theorem w4src_proposedParent_preceq_proposedBlockAt
    (S : Setup V) {rho : Run V} (s : Slot) {P : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P) :
    Block.Preceq (proposedParent S rho s) P.erase := by
  obtain ⟨p, hp, hparent⟩ := proposedBlockAt_parent S rho s hP
  rw [← hparent]
  cases P with
  | genesis => simp only [NamedBlock.parent?, reduceCtorEq] at hp
  | node parent slot root votes support rows proposer =>
      simp only [NamedBlock.parent?, Option.some.injEq] at hp
      subst hp
      apply Protocol.preceq_of_parent?
      rfl

private theorem w4src_liveConfirmed_mem_action
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (v : V) (r : Round) :
    (actionStoreAt S rho v r).live_confirmed ∈
      (rho.storeBeforeTime S v (S.a r)).T := by
  let n := rho.stateBeforeTime S (S.a r) v
  let cr := NamedActionReads.confirmationReadFrom S n (S.a r)
  have hn : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg n.st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a r) v).1
  have hcr : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg cr.st := by
    exact Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg n.st (S.a r) hn
  have ha := Proofs.NamedConfirmationMembership.invariant_update
    cr.cache S.E S.hc S.cfg cr.st (S.E.slotOf (S.a r) - 1) hcr
  have hmem :
      (Protocol.NamedDuties.update_confirmation_with
      (DecoupledConsensusModel.Protocol.frameContract cr.cache) S.E S.hc cr.st
          (S.E.slotOf (S.a r) - 1)).core.live_confirmed ∈
        (Protocol.NamedDuties.update_confirmation_with
        (DecoupledConsensusModel.Protocol.frameContract cr.cache) S.E S.hc cr.st
          (S.E.slotOf (S.a r) - 1)).core.T := ha.2.1
  change (actionStoreAt S rho v r).st.core.live_confirmed ∈
    (rho.stateBeforeTime S (S.a r) v).st.core.T
  simpa only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
    NamedActionReads.actionReadFrom, NamedActionReads.preparedCache, cr,
    NamedActionReads.confirmationReadFrom, NamedDuties.confirmation_core,
    Protocol.NamedStore.setClock, n,
    Run.storeBeforeTime] using hmem

private theorem w4src_previousOpening_mem_bodies
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {p : Round} {Pprev : NamedBlock V}
    (hPprevRun : RunBlock S rho Pprev)
    (hlive : ∀ v ∈ rho.honest,
      (actionStoreAt S rho v p).live_confirmed = Pprev.erase) :
    ∀ v ∈ rho.honest,
      Pprev ∈ (rho.storeBeforeTime S v (S.a p)).bodies := by
  intro v hv
  have hmem := w4src_liveConfirmed_mem_action S adm v p
  rw [hlive v hv] at hmem
  obtain ⟨D, hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho (S.a p) v hmem
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.a p)
  have hDstore : D ∈ (rho.storeBeforeTime S v (S.a p)).bodies := by
    simpa only [Run.storeBeforeTime, hn] using hDbody
  have hDrun : RunBlock S rho D := by
    have hD' : D ∈ (rho.stateBefore S n v).st.bodies := by
      simpa only [hn] using hDbody
    exact Proofs.Bridges.runBlock_of_stateBefore_mem S hv hD'
  have hroot : D.root = Pprev.root := by
    calc
      D.root = D.erase.root := (Proofs.NamedWire.erase_root D).symm
      _ = Pprev.erase.root := by rw [hDerase]
      _ = Pprev.root := Proofs.NamedWire.erase_root Pprev
  have hEq := adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
    D Pprev hDrun hPprevRun D Pprev
      (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self Pprev)) hroot
  have hDbody' : Pprev ∈
      (rho.storeBeforeTime S v (S.a p)).bodies := by
    rw [← hEq]
    exact hDstore
  exact hDbody'

private theorem w4src_history_separation
    (S : Setup V) {p : Round} :
    ∀ q : Round, S.a q < S.a p →
      S.a q < Protocol.proposal_time S.E (S.hc.opening_slot p) := by
  intro q hq
  have hqp : q < p := (action_strictMono S).lt_iff_lt.mp hq
  exact (Protocol.action_lt_proposal_time_two_after S q).trans_le
    (Protocol.proposal_time_mono S.E
      (openingSlot_add_two_le_openingSlot_of_lt S hqp))

private theorem w4src_predecessor_carriers_of_fold
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {p : Round} (hp : 0 < p)
    {t1 : Time} {M0 : Height} {s0 s : Slot} {F : Slot → Block V}
    {FoldEnd : Block V}
    (hfold : MovingSlotFoldAtN S rho t1 M0 s0 s F FoldEnd)
    (hfoldPrev : s0 ≤ S.hc.opening_slot p ∧
      S.hc.opening_slot p + 1 < s)
    (hstartPrev : t1 ≤ S.a (p - 1))
    (hpostPrev : S.E.t_GST ≤ S.a (p - 1))
    (hprevHor : S.a (p - 1) ≤ rho.horizon) :
    ∀ w ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho w (p - 1))
        (F (S.hc.opening_slot p)) := by
  obtain ⟨EndAt, hstate, hEnd⟩ := hfold.historyAt
    (S.hc.opening_slot p) hfoldPrev.1
    (Nat.lt_of_le_of_lt (Nat.le_succ _) hfoldPrev.2).le
  let k := strictEventIndex rho
    (Protocol.proposal_time S.E (S.hc.opening_slot p))
  have hstartAction : t1 ≤ S.a (p - 1) := by
    exact hstartPrev
  have hpPred : p - 1 < p := Nat.sub_lt hp Nat.one_pos
  have hbefore : S.a (p - 1) <
      Protocol.proposal_time S.E (S.hc.opening_slot p) := by
    exact (Protocol.action_lt_proposal_time_two_after S (p - 1)).trans_le
      (Protocol.proposal_time_mono S.E
        (openingSlot_add_two_le_openingSlot_of_lt S hpPred))
  have hupper : ∀ w ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho w (p - 1)) (EndAt k) := by
    intro w hw
    exact (hstate.previousActionCarriersPreceqAtRead S adm hstartAction
      hprevHor hbefore (by rfl)) w hw
  intro w hw
  rw [hEnd] at hupper
  exact hupper w hw

private theorem w4src_previousOpening_band_of_fold
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {p : Round} (hp : 0 < p)
    (hprop : S.E.proposer (S.hc.opening_slot p) ∈ rho.honest)
    {Pprev : NamedBlock V} (hPprevRun : RunBlock S rho Pprev)
    (hPprev : proposedBlockAt S rho
      (S.hc.opening_slot p) = some Pprev)
    {t1 : Time} {M0 : Height} {s0 s : Slot} {F : Slot → Block V}
    {FoldEnd : Block V}
    (hfold : MovingSlotFoldAtN S rho t1 M0 s0 s F FoldEnd)
    (hfoldPrev : s0 ≤ S.hc.opening_slot p ∧
      S.hc.opening_slot p + 1 < s) :
    ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v (S.a p)).core.h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg Pprev).h := by
  obtain ⟨EndAt, hstate, hEnd⟩ := hfold.historyAt
    (S.hc.opening_slot p) hfoldPrev.1
    (Nat.lt_of_le_of_lt (Nat.le_succ _) hfoldPrev.2).le
  let k := strictEventIndex rho
    (Protocol.proposal_time S.E (S.hc.opening_slot p))
  obtain ⟨E, hE, hErun⟩ := hstate.endpointRun k hstate.start_le (by rfl)
  have hEfloor : E.erase = F (S.hc.opening_slot p) := hE.trans hEnd
  have hsep := w4src_history_separation S (p := p)
  have hparent := hfold.parent (S.hc.opening_slot p)
    hfoldPrev.1 (Nat.lt_of_le_of_lt (Nat.le_succ _) hfoldPrev.2).le
    hprop
  have hparentP := w4src_proposedParent_preceq_proposedBlockAt S
    (S.hc.opening_slot p) hPprev
  have hEtoP : Block.Preceq E.erase Pprev.erase := by
    rw [hEfloor]
    exact Block.preceq_trans hparent hparentP
  have hEnamed : NamedBlock.Preceq E Pprev :=
    Protocol.namedPreceq_of_runBlock_erase_preceq adm hErun hPprevRun hEtoP
  have hheight := Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hEnamed
  intro v hv
  have hband := hstate.readFrontier_sub_one_le_endpointAtCursor_named
    S adm hbelow hsep (by rfl) hv hE hErun
  exact hband.trans (hheight)

theorem w4_predecessorRoundFloor_of_fold
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {q r : Round} (hlate : q + 2 < r)
    (hopening : ProposerOpeningCarrierAt S rho r)
    {Pprev : NamedBlock V}
    (hPprev : proposedBlockAt S rho
      (S.hc.opening_slot (r - 1)) = some Pprev)
    (hprevHor : S.a (r - 1) ≤ rho.horizon)
    (hlive : ∀ v ∈ rho.honest,
      (actionStoreAt S rho v (r - 1)).live_confirmed = Pprev.erase)
    {t1 : Time} {M0 : Height} {s0 s : Slot} {F : Slot → Block V}
    {FoldEnd : Block V}
    (hfold : MovingSlotFoldAtN S rho t1 M0 s0 s F FoldEnd)
    (hfoldPrev : s0 ≤ S.hc.opening_slot (r - 1) ∧
      S.hc.opening_slot (r - 1) + 1 < s)
    (hstartPrev : t1 ≤ S.a (r - 2))
    (hpostPrev : S.E.t_GST ≤ S.a (r - 2))
    (hnlPrev : ¬ LostRoundAt S rho (r - 1)) :
    ∃ C : Block V, RoundFloorFieldsAt S rho (r - 1) C := by
  have h1r : 1 < r := by
    have hq2 : 2 ≤ q + 2 := Nat.le_add_left 2 q
    have h2r : 2 < r := hq2.trans_lt hlate
    exact Nat.lt_of_lt_of_le (by decide) h2r.le
  have hp : 0 < r - 1 := Nat.sub_pos_iff_lt.mpr h1r
  have hprevSlotPos : 0 < S.hc.opening_slot (r - 1) :=
    Nat.mul_pos hp (Nat.zero_lt_of_lt S.hc.R_ge_two)
  have hprevProposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot (r - 1)) ≤ rho.horizon := by
    exact (Protocol.proposal_time_le_confirmation_time S.E
      (S.hc.opening_slot (r - 1))).trans
      (by simpa only [Setup.a, Protocol.a_eq_confirmation_time] using hprevHor)
  have hPprevRun : RunBlock S rho Pprev :=
    proposedBlock_runBlock S adm hprevSlotPos hopening.2.1
      hprevProposalHor hPprev
  have hprevPrevHor : S.a (r - 2) ≤ rho.horizon := by
    have hidx : r - 2 ≤ r - 1 :=
      Nat.sub_le_sub_left (by decide : 1 ≤ 2) r
    exact (action_strictMono S).monotone hidx |>.trans hprevHor
  have hcarriers := w4src_predecessor_carriers_of_fold S adm (p := r - 1) hp hfold
    hfoldPrev
    (by simpa only [Nat.sub_sub, Nat.reduceAdd] using hstartPrev)
    (by simpa only [Nat.sub_sub, Nat.reduceAdd] using hpostPrev)
    hprevPrevHor
  have hbody := w4src_previousOpening_mem_bodies S adm hPprevRun hlive
  have hband := w4src_previousOpening_band_of_fold S adm hbelow hp
    hopening.2.1 hPprevRun hPprev hfold hfoldPrev
  have hwitness : ∀ v ∈ rho.honest, ∃ W : NamedBlock V,
      W ∈ (rho.storeBeforeTime S v (S.a (r - 1))).bodies ∧
      Block.Preceq (F (S.hc.opening_slot (r - 1))) W.erase ∧
      (rho.storeBeforeTime S v (S.a (r - 1))).h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg W).h := by
    intro v hv
    refine ⟨Pprev, hbody v hv, ?_, hband v hv⟩
    have hparent := w4src_proposedParent_preceq_proposedBlockAt S
      (S.hc.opening_slot (r - 1)) hPprev
    have hfoldParent := hfold.parent (S.hc.opening_slot (r - 1))
      hfoldPrev.1 (Nat.lt_of_le_of_lt (Nat.le_succ _) hfoldPrev.2).le
        hopening.2.1
    exact Block.preceq_trans hfoldParent hparent
  rcases movingChainRoundFloor_or_lost_of_carrierCeiling S adm hcom hcarriers
      hwitness with hlost | ⟨C, hC⟩
  · exact (hnlPrev hlost).elim
  · exact ⟨C, hC⟩

#print axioms w4_predecessorRoundFloor_of_fold

/-- Prepared twin of the useful part of `preceq_actionQ2_of_domainGrade`.
The original filtered-tree premise is used there only to obtain processed
membership. This statement takes that exact fact directly. -/
private theorem w4_preceq_actionQ2_of_domainGrade_mem
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} (hr : 0 < r)
    (hhor : S.a r ≤ rho.horizon) {C : Block V}
    (hmem : C ∈ (NamedRun.stateBeforeTime S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) v).st.core.T)
    (hgrade : storeGrade S.E S.hc
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) v).st r .g2 C = true)
    (hactive : C ∈ filteredTree (actionReadAt S rho v r)) :
    ∃ Q : Block V,
      nodeQ2 S (actionReadAt S rho v r) r = some Q ∧ Block.Preceq C Q := by
  obtain ⟨raw, hfz, hCraw⟩ := NamedOutageClosure.q10_freeze_of_graded S.E
    (NamedRun.stateBeforeTime S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) v).st.core.toHealing.gradeView
    (NamedRun.stateBeforeTime S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) v).st.core.F
    S.hc.η_SG r (NamedOutageClosure.q10_early_le_late S r .g2)
    hmem hgrade
  have hFC : Block.Preceq (actionReadAt S rho v r).st.core.F C :=
    NamedOutageClosure.q10_filtered_F hactive
  have hcompat : Block.compatible C
      (actionReadAt S rho v r).st.core.F = true := by
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr hFC
  have hCclip : Block.Preceq C
      (DecoupledConsensusModel.Protocol.clipGrade raw
        (actionReadAt S rho v r).st.core.F) :=
    (NamedOutageClosure.q10_retained_prefix raw
      (actionReadAt S rho v r).st.core.F C hcompat).mpr hCraw
  obtain ⟨Q, hQ, hCQ⟩ :=
    NamedOutageClosure.q10_activePrefix_dominates hactive hCclip
  refine ⟨Q, ?_, hCQ⟩
  show DecoupledConsensusModel.Protocol.grade2Block
      (actionReadAt S rho v r).st.core.toHealing
      (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho v r).cache
        (actionReadAt S rho v r).st.core.toHealing r) = some Q
  unfold DecoupledConsensusModel.Protocol.grade2Block
  rw [if_pos (actionFrame_allClosed S core hv hr hhor),
    actionFrame_g2 S core hv hr hhor,
    show PhaseGrades.storeRoot S.E S.hc
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) v).st r .g2 = some raw from hfz]
  exact hQ

/-- A prepared relative G2 result makes the action FG source exist. The
prepared anchor and clearance make its clear walk end at the live
confirmation. -/
theorem w4_preparedFGSource_eq_live_of_domainGrade
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (hr : 0 < r) (hhor : S.a r ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) {C : Block V}
    (hmem : C ∈ (NamedRun.stateBeforeTime S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) v).st.core.T)
    (hgrade : storeGrade S.E S.hc
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) v).st r .g2 C = true)
    (hactive : C ∈ filteredTree (actionReadAt S rho v r))
    (hanchor : Block.Preceq
      (nodeAnchor S (actionReadAt S rho v r) r)
      (actionStoreAt S rho v r).live_confirmed)
    (hclear : nodeClear S (actionReadAt S rho v r) r
      (actionStoreAt S rho v r).live_confirmed = true) :
    actionFGSource S (actionReadAt S rho v r) =
      some (actionStoreAt S rho v r).live_confirmed := by
  obtain ⟨Q, hQ, -⟩ := w4_preceq_actionQ2_of_domainGrade_mem S
    adm.toNamedAdmissibleCore hv hr hhor hmem hgrade hactive
  have hQanchor : Block.Preceq Q
      (nodeAnchor S (actionReadAt S rho v r) r) :=
    actionQ2_preceq_actionAnchor S adm.toNamedAdmissibleCore hv hr hhor hQ
  have hQlive : Block.Preceq Q (actionStoreAt S rho v r).live_confirmed :=
    Block.preceq_trans hQanchor hanchor
  have hwalk : Protocol.deepest_clear (some Q)
      (actionReadAt S rho v r).st.core.toHealing.live_confirmed
      ((NamedProfile.gradeContract (actionReadAt S rho v r).cache).read
        S.E S.hc (actionReadAt S rho v r).st.core.toHealing r).clear =
        some (actionStoreAt S rho v r).live_confirmed :=
    w4src_deepest_clear_eq_tip (by simpa using hQlive) hclear
  have hround : S.hc.round_of
      (actionReadAt S rho v r).st.core.toHealing.s = r := by
    simpa only [actionStoreAt, Protocol.Store.toHealing] using
      actionStoreAt_round S rho v r
  have hQ' : Protocol.grade2_block_with
      (NamedProfile.gradeContract (actionReadAt S rho v r).cache) S.E S.hc
      (actionReadAt S rho v r).st.core.toHealing r = some Q := hQ
  change nodeFGSource S (actionReadAt S rho v r)
      (S.hc.round_of (actionReadAt S rho v r).st.core.toHealing.s) = _
  rw [hround, nodeFGSource, Protocol.fg_source_with.eq_def, hQ']
  simp only [hwalk]

#print axioms w4_preparedFGSource_eq_live_of_domainGrade

private theorem w4src_actionVote_mem_domain
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {p k : Round} (hk : k ∈ Protocol.latest_window S.hc.η_SG p)
    {u w : V} (hu : u ∈ rho.honest) (hw : w ∈ rho.honest)
    {a : NamedAttestation V} {H : NamedBlock V}
    (hvote : a.val_index = u ∧ a.round = k ∧
      NamedRun.emits S rho u (Object.attest a) (S.a k))
    (hhead : ∃ i : Nat, rho.events[i]? = some (.tick u (S.a k)) ∧
      H ∈ (NamedActionReads.actionReadFrom S
        (NamedRun.stateBefore S rho i u) a.round).st.bodies ∧
      a.confirmed = some H.root)
    (hHcarrier : H.erase = actionSGBlockAt S rho u k)
    (hF : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc p .g2) w).st.core.F
      H.erase)
    (hpost : S.E.t_GST ≤ S.a k)
    (hdeadline : max (S.a k) S.E.t_GST + S.E.Δ ≤
      early S.E S.hc p .g2)
    (hcut : early S.E S.hc p .g2 ≤ rho.horizon) :
    Protocol.sgVote a.erase ∈
        interpretedInputs
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc p .g2) w).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc p .g2) w).st.core.F
          S.hc.η_SG p (early S.E S.hc p .g2) u ∧
      Block.find?
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc p .g2) w).st.core.T
          (actionSGBlockAt S rho u k).root =
        some (actionSGBlockAt S rho u k) := by
  let core := adm.toNamedAdmissibleCore
  have hklt : k < p := (NamedOutageClosure.window_bounds hk).2
  have hsourceDeadline : max (S.a a.round) S.E.t_GST + S.E.Δ ≤
      early S.E S.hc p .g2 := by
    simpa only [hvote.2.1] using hdeadline
  have hactionDeadline : S.a a.round + S.E.Δ ≤
      early S.E S.hc p .g2 := by
    exact (Int.add_le_add_right
      (le_max_left (S.a a.round) S.E.t_GST) S.E.Δ).trans
      hsourceDeadline
  have hpostA : S.E.t_GST ≤ S.a a.round := by
    simpa only [hvote.2.1] using hpost
  obtain ⟨i, hi, hH, hconfirmed⟩ := hhead
  have hval : a.val_index ∈ rho.honest := by
    simpa only [hvote.1] using hu
  have hi' : rho.events[i]? = some (.tick u (S.a a.round)) := by
    simpa only [hvote.2.1] using hi
  have hbody : H ∈ (NamedRun.stateBefore S rho i u).st.bodies := by
    change H ∈ (NamedRun.stateBefore S rho i u).st.bodies at hH
    exact hH
  have hstate := NamedActionSources.action_read_index S rho
    core.toNamedScheduleWellFormed i u a.round hi'
  have hHsource : H ∈
      (NamedRun.stateBeforeTime S rho (S.a a.round) u).st.bodies := by
    rw [← hstate]
    exact hbody
  have horder : early S.E S.hc p .g2 ≤
      domain S.E S.hc p .g2 :=
    NamedOutageClosure.early_le_domain S p
  obtain ⟨hheld, hstamp, hfind⟩ :=
    NamedHealthyHeadReady.healthy_head_body_at_read_after_gst S rho core
      u hu w hw H (S.a a.round) (early S.E S.hc p .g2)
      (domain S.E S.hc p .g2) hHsource hsourceDeadline horder hcut hF
  have hem : NamedRun.emits S rho a.val_index (Object.attest a)
      (S.a a.round) := by
    simpa only [hvote.1, hvote.2.1] using hvote.2.2
  let healthy := NamedOutageClosure.healthyWindowDelivery_after_gst S rho core
  obtain ⟨td, hlo, hhi, j, hcall⟩ := healthy.broadcast a.val_index hval
    (Object.attest a) (S.a a.round) hem w hw hpostA
    (hactionDeadline.trans hcut) rfl
  have hrow := Proofs.NamedSGArrival.honest_row_after_call S rho
    core.toNamedScheduleWellFormed core.toNamedUnforgeable hval hem hcall hlo hhi
  obtain ⟨e, he, _, het⟩ := hcall.2
  obtain ⟨_, stamp, hstampBound, hstampEvent⟩ :=
    Proofs.NamedSGArrival.held_row_own_and_stamp_at_event S rho
      core.toNamedScheduleWellFormed he w a.round a hrow
  have htdEarly : td < early S.E S.hc p .g2 := hhi.trans_le hactionDeadline
  have heEarly : e.time < early S.E S.hc p .g2 := by
    simpa only [het] using htdEarly
  have heCut : e.time < domain S.E S.hc p .g2 := heEarly.trans_le horder
  let cut := domain S.E S.hc p .g2
  let n := (rho.events.filter (fun e => decide (e.time < cut))).length
  have hread : NamedRun.stateBeforeTime S rho cut =
      NamedRun.stateBefore S rho n := by
    exact Proofs.Optimistic.stateBeforeTime_eq_take S core.toNamedScheduleWellFormed cut
  have hjN : j < n := by
    by_contra hnot
    have hnj : n ≤ j := Nat.le_of_not_gt hnot
    have hle := Proofs.Optimistic.le_time_of_index_ge S
      core.toNamedScheduleWellFormed (t := cut) (j := j) (e := e) hnj he
    exact (not_le_of_gt heCut) hle
  have hrowN := Proofs.NamedSGArrival.stateBefore_sg_row_stamp_mono S rho w
    (Nat.succ_le_of_lt hjN) hrow
  have hrowCut : a ∈
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc p .g2) w).st.sg_rows a.round := by
    rw [hread]
    exact hrowN.1
  have hstampCut :
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc p .g2) w).st.core.timestamp_sg_vote
        (Protocol.sgVote a.erase) = some (stamp : Stamp) := by
    rw [hread]
    exact hrowN.2.trans hstampEvent
  have hstampEarly : stamp < early S.E S.hc p .g2 :=
    hstampBound.trans_lt heEarly
  have hoccur : occurrenceBefore
      ((NamedRun.stateBeforeTime S rho (domain S.E S.hc p .g2) w).st.core.timestamp_sg_vote
        (Protocol.sgVote a.erase)) (early S.E S.hc p .g2) = true := by
    simp only [hstampCut, occurrenceBefore, decide_eq_true_eq]
    exact WithBot.coe_lt_coe.mpr hstampEarly
  have hcoh :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
      (domain S.E S.hc p .g2) w).1.1.1
  have hpool := NamedAdmission.pool_view_mem _ hcoh.2.2.2.1 a hrowCut
  let target := NamedRun.stateBeforeTime S rho
    (domain S.E S.hc p .g2) w
  have hsg : Protocol.sgVote a.erase ∈ target.st.core.toHealing.gradeView.sg_votes a.round :=
    Finset.mem_image_of_mem Protocol.sgVote hpool
  have hraw : Protocol.sgVote a.erase ∈
      rawInputs target.st.core.toHealing.gradeView S.hc.η_SG p
        (early S.E S.hc p .g2) u := by
    simp only [rawInputs, Finset.mem_filter]
    refine ⟨Finset.mem_biUnion.mpr ?_, ?_, hoccur⟩
    · exact ⟨a.round, List.mem_toFinset.mpr (by
        simpa only [hvote.2.1] using hk), hsg⟩
    · rw [NamedOutageClosure.sgVote_val, hvote.1]
  have hconf : (Protocol.sgVote a.erase).confirmed = some H.root := by
    rw [NamedOutageClosure.sgVote_confirmed, hconfirmed]
  have hfind' : Block.find? target.st.core.T H.root = some H.erase := by
    simpa only [target, Proofs.NamedWire.erase_root] using hfind
  have hcompat : Block.compatible H.erase target.st.core.F = true := by
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr hF
  have hbodyReady : DecoupledConsensusModel.Protocol.bodyReady target.st.core.toHealing.gradeView
      target.st.core.F (early S.E S.hc p .g2) (Protocol.sgVote a.erase) = true := by
    simp only [bodyReady, hconf]
    change (match Block.find? target.st.core.T H.root with
      | none => false
      | some head => stampedBefore target.st.core.timestamp_block
          (early S.E S.hc p .g2) head &&
          Block.compatible head target.st.core.F) = true
    rw [hfind', Bool.and_eq_true]
    exact ⟨hstamp, hcompat⟩
  have hmem : Protocol.sgVote a.erase ∈
      interpretedInputs target.st.core.toHealing.gradeView target.st.core.F
        S.hc.η_SG p (early S.E S.hc p .g2) u :=
    Finset.mem_filter.mpr ⟨hraw, hbodyReady⟩
  have hfindCarrier : Block.find? target.st.core.T
      (actionSGBlockAt S rho u k).root =
      some (actionSGBlockAt S rho u k) := by
    simpa only [hHcarrier] using hfind
  exact ⟨by simpa only [target] using hmem, by simpa only [target] using hfindCarrier⟩

private theorem w4src_positive_of_actionVote
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {p : Round} (hp : 0 < p) {u w : V}
    (hu : u ∈ rho.honest) (hw : w ∈ rho.honest)
    {C : Block V}
    (hmem : actionSGVoteAt S rho u (p - 1) ∈
      interpretedInputs
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc p .g2) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc p .g2) w).st.core.F
        S.hc.η_SG p (early S.E S.hc p .g2) u)
    (hfind : Block.find?
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc p .g2) w).st.core.T
        (actionSGBlockAt S rho u (p - 1)).root =
      some (actionSGBlockAt S rho u (p - 1)))
    (hC : Block.Preceq C
      (actionSGBlockAt S rho u (p - 1))) :
    DecoupledConsensusModel.Protocol.positive
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc p .g2) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc p .g2) w).st.core.F
      S.hc.η_SG p (early S.E S.hc p .g2) (late S.E S.hc p .g2) u C = true := by
  let n := NamedRun.stateBeforeTime S rho (domain S.E S.hc p .g2) w
  let gv := n.st.core.toHealing.gradeView
  let F := n.st.core.F
  let vote := actionSGVoteAt S rho u (p - 1)
  have hmem : vote ∈ interpretedInputs gv F S.hc.η_SG p
      (early S.E S.hc p .g2) u := by
    simpa only [vote, gv, F, n] using hmem
  have hfind' : Block.find? gv.T
      (actionSGBlockAt S rho u (p - 1)).root =
      some (actionSGBlockAt S rho u (p - 1)) := by
    simpa only [gv, n] using hfind
  have htoken : DecoupledConsensusModel.Protocol.token (actionSGVoteAt S rho u (p - 1)) ∈
      readyView gv F S.hc.η_SG p (early S.E S.hc p .g2) u := by
    simpa only [readyView] using Finset.mem_image_of_mem DecoupledConsensusModel.Protocol.token hmem
  have hcover : localCovers gv
      (actionSGVoteAt S rho u (p - 1)).confirmed C = true := by
    change Protocol.head_covers gv.T C
      (actionSGVoteAt S rho u (p - 1)).confirmed = true
    rw [(actionSGVoteAt_shape S rho u (p - 1)).2.2]
    simp only [Protocol.head_covers]
    rw [hfind']
    exact hC
  have hpred : p - 1 < p := Nat.sub_lt hp Nat.one_pos
  have hactRound : (actionSGVoteAt S rho u (p - 1)).round = p - 1 :=
    (actionSGVoteAt_shape S rho u (p - 1)).2.1
  change DecoupledConsensusModel.Protocol.positive gv F S.hc.η_SG p
      (early S.E S.hc p .g2) (late S.E S.hc p .g2) u C = true
  simp only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq]
  refine ⟨DecoupledConsensusModel.Protocol.token (actionSGVoteAt S rho u (p - 1)), ?_, ?_, ?_, ?_, ?_⟩
  · exact htoken
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    have hzdata := Finset.mem_filter.mp hz
    have hzraw := Finset.mem_filter.mp hzdata.1
    obtain ⟨k, hk, hzk⟩ := Finset.mem_biUnion.mp hzraw.1
    have hk' : k ∈ Protocol.latest_window S.hc.η_SG p :=
      List.mem_toFinset.mp hk
    have hklt : k < p := (NamedOutageClosure.window_bounds hk').2
    have hzStore : z ∈
        (rho.storeBeforeTime S w (domain S.E S.hc p .g2)).toHealing.sg_votes k := by
      simpa only [gv, n, Run.storeBeforeTime, Protocol.HealingStore.gradeView,
        Protocol.Store.toHealing] using hzk
    have hzEq : z = actionSGVoteAt S rho u k :=
      honestSGVote_eq_actionSGVoteAt_of_mem_storeBeforeTime
        S adm hu hzStore hzraw.2.1
    have hzround : z.round = k := by
      rw [hzEq]
      exact (actionSGVoteAt_shape S rho u k).2.1
    change z.round ≤ (actionSGVoteAt S rho u (p - 1)).round
    rw [hzEq, hactRound]
    exact Nat.le_pred_of_lt hklt
  · change localCovers gv
      (actionSGVoteAt S rho u (p - 1)).confirmed C = true
    exact hcover
  · intro x hx y hy _hlo hxy
    obtain ⟨xv, hxv, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨yv, hyv, rfl⟩ := Finset.mem_image.mp hy
    have hxdata := Finset.mem_filter.mp hxv
    have hydata := Finset.mem_filter.mp hyv
    obtain ⟨kx, hkx, hxpool⟩ := Finset.mem_biUnion.mp hxdata.1
    obtain ⟨ky, hky, hypool⟩ := Finset.mem_biUnion.mp hydata.1
    have hxStore : xv ∈
        (rho.storeBeforeTime S w (domain S.E S.hc p .g2)).toHealing.sg_votes kx := by
      simpa only [gv, n, Run.storeBeforeTime, Protocol.HealingStore.gradeView,
        Protocol.Store.toHealing] using hxpool
    have hyStore : yv ∈
        (rho.storeBeforeTime S w (domain S.E S.hc p .g2)).toHealing.sg_votes ky := by
      simpa only [gv, n, Run.storeBeforeTime, Protocol.HealingStore.gradeView,
        Protocol.Store.toHealing] using hypool
    have hxEq : xv = actionSGVoteAt S rho u kx :=
      honestSGVote_eq_actionSGVoteAt_of_mem_storeBeforeTime
        S adm hu hxStore hxdata.2.1
    have hyEq : yv = actionSGVoteAt S rho u ky :=
      honestSGVote_eq_actionSGVoteAt_of_mem_storeBeforeTime
        S adm hu hyStore hydata.2.1
    have hxround : xv.round = kx := by
      rw [hxEq]
      exact (actionSGVoteAt_shape S rho u kx).2.1
    have hyround : yv.round = ky := by
      rw [hyEq]
      exact (actionSGVoteAt_shape S rho u ky).2.1
    change xv.round = yv.round at hxy
    have hkyx : ky = kx := hyround.symm.trans (hxy.symm.trans hxround)
    subst ky
    have hyEq' : yv = actionSGVoteAt S rho u kx := by
      simpa only [hkyx] using hyEq
    exact congrArg (fun z => (DecoupledConsensusModel.Protocol.token z).key)
      (hxEq.trans hyEq'.symm)
  · intro x hx hlt
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    have hzdata := Finset.mem_filter.mp hz
    have hzraw := Finset.mem_filter.mp hzdata.1
    obtain ⟨k, hk, hzk⟩ := Finset.mem_biUnion.mp hzraw.1
    have hk' : k ∈ Protocol.latest_window S.hc.η_SG p :=
      List.mem_toFinset.mp hk
    have hklt : k < p := (NamedOutageClosure.window_bounds hk').2
    have hzStore : z ∈
        (rho.storeBeforeTime S w (domain S.E S.hc p .g2)).toHealing.sg_votes k := by
      simpa only [gv, n, Run.storeBeforeTime, Protocol.HealingStore.gradeView,
        Protocol.Store.toHealing] using hzk
    have hzEq := honestSGVote_eq_actionSGVoteAt_of_mem_storeBeforeTime
      S adm hu hzStore hzraw.2.1
    have hzround : z.round = k := by
      rw [hzEq]
      exact (actionSGVoteAt_shape S rho u k).2.1
    change (actionSGVoteAt S rho u (p - 1)).round < z.round at hlt
    rw [hactRound, hzround] at hlt
    exact False.elim ((Nat.not_lt_of_ge (Nat.le_pred_of_lt hklt)) hlt)

private theorem w4src_not_opposing_of_actionVote
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {p : Round} (hp : 0 < p) {u w : V}
    (hu : u ∈ rho.honest) (hw : w ∈ rho.honest)
    {C : Block V}
    (hmem : actionSGVoteAt S rho u (p - 1) ∈
      interpretedInputs
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc p .g2) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc p .g2) w).st.core.F
        S.hc.η_SG p (early S.E S.hc p .g2) u)
    (hfind : Block.find?
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc p .g2) w).st.core.T
        (actionSGBlockAt S rho u (p - 1)).root =
      some (actionSGBlockAt S rho u (p - 1)))
    (hC : Block.Preceq C
      (actionSGBlockAt S rho u (p - 1))) :
    DecoupledConsensusModel.Protocol.opposing
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc p .g2) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc p .g2) w).st.core.F
      S.hc.η_SG p (early S.E S.hc p .g2) (late S.E S.hc p .g2) u C ≠ true := by
  let n := NamedRun.stateBeforeTime S rho (domain S.E S.hc p .g2) w
  let gv := n.st.core.toHealing.gradeView
  let F := n.st.core.F
  have hfind' : Block.find? gv.T
      (actionSGBlockAt S rho u (p - 1)).root =
      some (actionSGBlockAt S rho u (p - 1)) := by
    simpa only [gv, n] using hfind
  have htoken : DecoupledConsensusModel.Protocol.token (actionSGVoteAt S rho u (p - 1)) ∈
      readyView gv F S.hc.η_SG p (early S.E S.hc p .g2) u := by
    have hmem' : actionSGVoteAt S rho u (p - 1) ∈
        interpretedInputs gv F S.hc.η_SG p
          (early S.E S.hc p .g2) u := by
      simpa only [gv, F, n] using hmem
    simpa only [readyView] using
      Finset.mem_image_of_mem DecoupledConsensusModel.Protocol.token hmem'
  have hcover : localCovers gv
      (actionSGVoteAt S rho u (p - 1)).confirmed C = true := by
    change Protocol.head_covers gv.T C
      (actionSGVoteAt S rho u (p - 1)).confirmed = true
    rw [(actionSGVoteAt_shape S rho u (p - 1)).2.2]
    simp only [Protocol.head_covers]
    rw [hfind']
    exact hC
  have hactRound : (actionSGVoteAt S rho u (p - 1)).round = p - 1 :=
    (actionSGVoteAt_shape S rho u (p - 1)).2.1
  intro hopposing
  have hOpp : DecoupledConsensusModel.Protocol.Opposes
      (fun k b => localCovers gv k b = true)
      (readyView gv F S.hc.η_SG p (early S.E S.hc p .g2) u)
      (readyView gv F S.hc.η_SG p (late S.E S.hc p .g2) u)
      (rawView gv S.hc.η_SG p (late S.E S.hc p .g2) u) C := by
    simpa only [DecoupledConsensusModel.Protocol.opposing, decide_eq_true_eq]
      using hopposing
  rcases hOpp with hbad | hequiv
  · obtain ⟨x, hx, hmax, hnot⟩ := hbad
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    have hzdata := Finset.mem_filter.mp hz
    have hzraw := Finset.mem_filter.mp hzdata.1
    obtain ⟨k, hk, hzk⟩ := Finset.mem_biUnion.mp hzraw.1
    have hk' : k ∈ Protocol.latest_window S.hc.η_SG p :=
      List.mem_toFinset.mp hk
    have hklt : k < p := (NamedOutageClosure.window_bounds hk').2
    have hzStore : z ∈
        (rho.storeBeforeTime S w (domain S.E S.hc p .g2)).toHealing.sg_votes k := by
      simpa only [gv, n, Run.storeBeforeTime, Protocol.HealingStore.gradeView,
        Protocol.Store.toHealing] using hzk
    have hzEq : z = actionSGVoteAt S rho u k :=
      honestSGVote_eq_actionSGVoteAt_of_mem_storeBeforeTime
        S adm hu hzStore hzraw.2.1
    have hzround : z.round = k := by
      rw [hzEq]
      exact (actionSGVoteAt_shape S rho u k).2.1
    have hmax' := hmax
      (DecoupledConsensusModel.Protocol.token (actionSGVoteAt S rho u (p - 1))) htoken
    change (actionSGVoteAt S rho u (p - 1)).round ≤ z.round at hmax'
    rw [hactRound, hzround] at hmax'
    have hk_le : k ≤ p - 1 := Nat.le_pred_of_lt hklt
    have hk_eq : k = p - 1 := Nat.le_antisymm hk_le hmax'
    have hzEqR : z = actionSGVoteAt S rho u (p - 1) := by
      calc
        z = actionSGVoteAt S rho u k := hzEq
        _ = actionSGVoteAt S rho u (p - 1) := by rw [hk_eq]
    apply hnot
    simpa only [DecoupledConsensusModel.Protocol.token, hzEqR] using hcover
  · obtain ⟨x, hx, y, hy, _hmax, hround, hkey⟩ := hequiv
    obtain ⟨xv, hxv, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨yv, hyv, rfl⟩ := Finset.mem_image.mp hy
    have hxdata := Finset.mem_filter.mp hxv
    have hydata := Finset.mem_filter.mp hyv
    obtain ⟨kx, hkx, hxpool⟩ := Finset.mem_biUnion.mp hxdata.1
    obtain ⟨ky, hky, hypool⟩ := Finset.mem_biUnion.mp hydata.1
    have hxStore : xv ∈
        (rho.storeBeforeTime S w (domain S.E S.hc p .g2)).toHealing.sg_votes kx := by
      simpa only [gv, n, Run.storeBeforeTime, Protocol.HealingStore.gradeView,
        Protocol.Store.toHealing] using hxpool
    have hyStore : yv ∈
        (rho.storeBeforeTime S w (domain S.E S.hc p .g2)).toHealing.sg_votes ky := by
      simpa only [gv, n, Run.storeBeforeTime, Protocol.HealingStore.gradeView,
        Protocol.Store.toHealing] using hypool
    have hxEq : xv = actionSGVoteAt S rho u kx :=
      honestSGVote_eq_actionSGVoteAt_of_mem_storeBeforeTime
        S adm hu hxStore hxdata.2.1
    have hyEq : yv = actionSGVoteAt S rho u ky :=
      honestSGVote_eq_actionSGVoteAt_of_mem_storeBeforeTime
        S adm hu hyStore hydata.2.1
    have hxround : xv.round = kx := by
      rw [hxEq]
      exact (actionSGVoteAt_shape S rho u kx).2.1
    have hyround : yv.round = ky := by
      rw [hyEq]
      exact (actionSGVoteAt_shape S rho u ky).2.1
    change xv.round = yv.round at hround
    have hkyx : ky = kx := hyround.symm.trans (hround.symm.trans hxround)
    subst ky
    have hyEq' : yv = actionSGVoteAt S rho u kx := by
      simpa only [hkyx] using hyEq
    exact hkey (congrArg (fun z => (DecoupledConsensusModel.Protocol.token z).key)
      (hxEq.trans hyEq'.symm))

private theorem w4src_domainGrade_of_roundFloor
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hmajority : HonestWeightMajority S rho.honest)
    {p : Round} (hp : 0 < p) {C : Block V}
    (hfields : RoundFloorFieldsAt S rho p C)
    (hpostPrev : S.E.t_GST ≤ S.a (p - 1))
    (hhor : S.a p ≤ rho.horizon)
    (hcut : early S.E S.hc p .g2 ≤ rho.horizon) :
    ∀ v ∈ rho.honest,
      C ∈ (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc p .g2) v).st.core.T ∧
      storeGrade S.E S.hc
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc p .g2) v).st p .g2 C = true ∧
      C ∈ filteredTree (actionReadAt S rho v p) := by
  have hk : p - 1 ∈ Protocol.latest_window S.hc.η_SG p := by
    exact Protocol.pred_mem_latest_window S.hc.η_SG p
      S.hc.η_SG_ge_one hp
  have hactHor : S.a (p - 1) ≤ rho.horizon :=
    (action_strictMono S).monotone (Nat.sub_le p 1) |>.trans hhor
  have hdeadline : max (S.a (p - 1)) S.E.t_GST + S.E.Δ ≤
      early S.E S.hc p .g2 := by
    rw [max_eq_left hpostPrev]
    exact NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
      (NamedOutageClosure.window_bounds hk).2
  have hFfloor : ∀ v ∈ rho.honest,
      Block.Preceq
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc p .g2) v).st.core.F C := by
    intro v hv
    have hFmono := w4src_strict_finality_mono_between S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v
      (FrameForward.domain_le_a S p .g2)
    have hFroot : Block.Preceq
        (rho.storeBeforeTime S v (S.a p)).core.F
          (Protocol.get_fg_root
            (rho.storeBeforeTime S v (S.a p)).core.toHealing.toFG) := by
      exact Proofs.Records.preceq_get_fg_root_of_F
        (st := (rho.storeBeforeTime S v (S.a p)).core.toHealing.toFG)
        (by simpa only [Run.storeBeforeTime] using
          (Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
            S rho (S.a p) v))
    have hroot := hfields.floorAboveRoots v hv
    exact Block.preceq_trans hFmono
      (Block.preceq_trans hFroot (by simpa only [healStoreAt] using hroot))
  have hready : ∀ v ∈ rho.honest, ∀ u ∈ rho.honest,
      actionSGVoteAt S rho u (p - 1) ∈
          interpretedInputs
            (NamedRun.stateBeforeTime S rho
              (domain S.E S.hc p .g2) v).st.core.toHealing.gradeView
            (NamedRun.stateBeforeTime S rho
              (domain S.E S.hc p .g2) v).st.core.F
            S.hc.η_SG p (early S.E S.hc p .g2) u ∧
      Block.find?
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc p .g2) v).st.core.T
          (actionSGBlockAt S rho u (p - 1)).root =
        some (actionSGBlockAt S rho u (p - 1)) := by
    intro v hv u hu
    have hemit := honest_emits_exact_actionAttestationAt S adm hu
      (p - 1) hactHor
    obtain ⟨i, hi, -, hbody⟩ :=
      Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
    dsimp at hbody
    obtain ⟨H, hH, hconfirmed⟩ := hbody
    have hhead : ∃ i : Nat, rho.events[i]? = some (.tick u (S.a (p - 1))) ∧
        H ∈ (NamedActionReads.actionReadFrom S
          (NamedRun.stateBefore S rho i u)
          (actionAttestationAt S rho u (p - 1)).round).st.bodies ∧
        (actionAttestationAt S rho u (p - 1)).confirmed = some H.root := by
      exact ⟨i, hi, hH, hconfirmed⟩
    have hHcarrier := w4src_actionHead_eq_carrier S adm hu rfl hhead
    have hFcarrier : Block.Preceq
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc p .g2) v).st.core.F
          (actionSGBlockAt S rho u (p - 1)) :=
      Block.preceq_trans (hFfloor v hv)
        (hfields.floorBelowCarriers u hu)
    have hres := w4src_actionVote_mem_domain S adm hk hu hv
      ⟨(actionAttestationAt_shape S rho u (p - 1)).1,
        (actionAttestationAt_shape S rho u (p - 1)).2.1, hemit⟩
      hhead hHcarrier (by simpa only [hHcarrier] using hFcarrier)
      hpostPrev hdeadline hcut
    simpa only [sgVote_actionAttestationAt] using hres
  obtain ⟨u0, hu0⟩ :=
    Protocol.honest_nonempty_of_honestCommittees hcom
  intro v hv
  have hready0 := hready v hv u0 hu0
  have hBmem : actionSGBlockAt S rho u0 (p - 1) ∈
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc p .g2) v).st.core.T :=
    Proofs.HealingLemmas.find?_mem hready0.2
  have hpc := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
    (domain S.E S.hc p .g2) v
  have hCmem := Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
    C (actionSGBlockAt S rho u0 (p - 1)) hBmem
      (hfields.floorBelowCarriers u0 hu0)
  have hgrade : storeGrade S.E S.hc
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc p .g2) v).st p .g2 C = true := by
    change DecoupledConsensusModel.Protocol.gradeBool S.E
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc p .g2) v).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc p .g2) v).st.core.F
      S.hc.η_SG p (early S.E S.hc p .g2) (late S.E S.hc p .g2) C = true
    apply phaseGrade_of_honestPositiveSupport
    · exact hmajority
    · intro u hu
      have hru := hready v hv u hu
      exact w4src_positive_of_actionVote S adm hp hu hv hru.1 hru.2
        (hfields.floorBelowCarriers u hu)
    · intro u huOpp hu
      exact (w4src_not_opposing_of_actionVote S adm hp hu hv
        (hready v hv u hu).1 (hready v hv u hu).2
        (hfields.floorBelowCarriers u hu)) huOpp
  have hactive0 := gradeFloor_active_everywhere S adm
    (fun w hw => hfields.floorAboveRoots w hw)
    (fun w hw => hfields.floorWitness w hw) v hv
  have hactive : C ∈ filteredTree (actionReadAt S rho v p) := by
    change C ∈ Protocol.get_filtered_block_tree
      (actionStoreAt S rho v p).toHealing.toFG
    rw [actionStoreAt_filteredTree S rho v p]
    exact hactive0
  exact ⟨hCmem, hgrade, hactive⟩

theorem w4_predecessorSourceAt_of_fold
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (hmajority : HonestWeightMajority S rho.honest)
    {q r : Round} (hlate : q + 2 < r)
    (hopening : ProposerOpeningCarrierAt S rho r)
    {Pprev : NamedBlock V}
    (hPprev : proposedBlockAt S rho
      (S.hc.opening_slot (r - 1)) = some Pprev)
    (hprevHor : S.a (r - 1) ≤ rho.horizon)
    (hlive : ∀ v ∈ rho.honest,
      (actionStoreAt S rho v (r - 1)).live_confirmed = Pprev.erase)
    (hanchor : ∀ v ∈ rho.honest,
      Block.Preceq
        (PhaseGrades.nodeAnchor S (actionReadAt S rho v (r - 1)) (r - 1))
        Pprev.erase)
    (hclear : ∀ v ∈ rho.honest,
      PhaseGrades.nodeClear S (actionReadAt S rho v (r - 1)) (r - 1)
        Pprev.erase = true)
    {t1 : Time} {M0 : Height} {s0 s : Slot} {F : Slot → Block V}
    {FoldEnd : Block V}
    (hfold : MovingSlotFoldAtN S rho t1 M0 s0 s F FoldEnd)
    (hfoldPrev : s0 ≤ S.hc.opening_slot (r - 1) ∧
      S.hc.opening_slot (r - 1) + 1 < s)
    (hstartPrev : t1 ≤ S.a (r - 2))
    (hpostPrev : S.E.t_GST ≤ S.a (r - 2))
    (hcutPrev : S.hc.Γ_neg1 S.E.Δ (r - 1) ≤ rho.horizon)
    (hnlPrev : ¬ LostRoundAt S rho (r - 1)) :
    ∀ v ∈ rho.honest,
      actionFGSource S (actionReadAt S rho v (r - 1)) = some Pprev.erase := by
  have hp : 0 < r - 1 := by
    have h1r : 1 < r := by
      have hq2 : 2 ≤ q + 2 := Nat.le_add_left 2 q
      have h2r : 2 < r := hq2.trans_lt hlate
      exact Nat.lt_of_lt_of_le (by decide) h2r.le
    exact Nat.sub_pos_iff_lt.mpr h1r
  have hfloor := w4_predecessorRoundFloor_of_fold S adm hcom hbelow hlate
    hopening hPprev hprevHor hlive hfold hfoldPrev hstartPrev hpostPrev hnlPrev
  obtain ⟨C, hfields⟩ := hfloor
  have hcutDomain : domain S.E S.hc (r - 1) .g2 ≤ rho.horizon := by
    have hrEq : r - 2 + 1 = r - 1 := by
      simpa only [Nat.sub_sub, Nat.reduceAdd] using Nat.sub_add_cancel hp
    have hgamma := gammaNeg1_eq_domain_g2_succ S (r - 2)
    rw [hrEq] at hgamma
    have hdom : domain S.E S.hc (r - 1) .g2 ≤ rho.horizon := by
      rw [← hgamma]
      exact hcutPrev
    exact hdom
  have hcut : early S.E S.hc (r - 1) .g2 ≤ rho.horizon :=
    (NamedOutageClosure.early_le_domain S (r - 1)).trans hcutDomain
  have hgrade := w4src_domainGrade_of_roundFloor S adm hcom hmajority
    (p := r - 1) hp hfields
    (by simpa only [Nat.sub_sub, Nat.reduceAdd] using hpostPrev)
    hprevHor hcut
  intro v hv
  obtain ⟨hmem, hgraded, hactive⟩ := hgrade v hv
  have hsrc := w4_preparedFGSource_eq_live_of_domainGrade S adm hp hprevHor hv
    hmem hgraded hactive (by
      rw [hlive v hv]
      exact hanchor v hv) (by
      rw [hlive v hv]
      exact hclear v hv)
  rw [hlive v hv] at hsrc
  exact hsrc

#print axioms w4_predecessorSourceAt_of_fold

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
