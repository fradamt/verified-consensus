module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.CanonicalDensityDischarge
public import DecoupledConsensusProofs.Protocol.Grades.PostRecoveryCarrierHeightRead
public import DecoupledConsensusProofs.Protocol.ChainState.CanonicalRegimeRound
public import DecoupledConsensusProofs.Generic.CanonicalSuffix
public import DecoupledConsensusProofs.Protocol.ValidatorClient.CanonicalRegimeFirstVote
public import DecoupledConsensusProofs.Execution.MovingChainRoundFloorFields
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainBatch
public import DecoupledConsensusProofs.Protocol.Grades.VoteBelowSource
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsBridge
public import DecoupledConsensusProofs.Protocol.Grades.SeedRelativeGrade
public import DecoupledConsensusProofs.Protocol.Grades.SeedActionQ2
public import DecoupledConsensusProofs.Protocol.Grades.RelativeSeedK3
public import DecoupledConsensusProofs.Protocol.Grades.RelativeSeedSettlement
public import DecoupledConsensusProofs.Protocol.Schedule.SeedEntry
public import DecoupledConsensusProofs.Protocol.Grades.SeedFlush
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightProgressLadder
public import DecoupledConsensusProofs.Protocol.Grades.RelativeCarrierWindowGateOff
public import DecoupledConsensusProofs.Protocol.Grades.RelativeCarrierWindowFixedRoot
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightProgressClosureBatchAlignedPreceq
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedCeilingStep
public import DecoupledConsensusProofs.Protocol.Handlers.HonestProposalAdmission
public import DecoupledConsensusProofs.Generic.SuffixHistory
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 0. Finalized-prefix monotonicity across two strict reads

Verbatim copies of the `private` helpers in
`NamedOutageHistory/ReadyHeadReturnG0DraftIdx.lean` (`:138`, `:145`, `:159`,
`:177`, `:187`), which are themselves copies of `NamedHealthyHeadReady`'s. -/

omit [DecidableEq V] [Fintype V] in
private theorem w4fkTimeLeOfKeyLe {e f : NamedEvent V} (h : e.key ≤ f.key) :
    e.time ≤ f.time := by
  rcases Prod.Lex.le_iff.mp h with hlt | ⟨heq, -⟩
  · exact hlt.le
  · exact heq.le

omit [DecidableEq V] [Fintype V] in
private theorem w4fkStrictFilterEqTake (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (cut : Time) :
    rho.events.filter (fun e => decide (e.time < cut)) =
      rho.events.take (rho.events.filter (fun e => decide (e.time < cut))).length := by
  have hdown : ∀ e f : NamedEvent V, e.key ≤ f.key →
      decide (f.time < cut) = true → decide (e.time < cut) = true := by
    intro e f hkey hf
    simp only [decide_eq_true_eq] at hf ⊢
    exact (w4fkTimeLeOfKeyLe hkey).trans_lt hf
  refine List.prefix_iff_eq_take.mp ?_
  rw [Proofs.Bridges.filter_eq_takeWhile_of_pairwise hdown _ hsorted]
  exact List.takeWhile_prefix _

private theorem w4fkStrictReadEqIndex (S : Setup V) (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (t : Time) :
    NamedRun.stateBeforeTime S rho t =
      NamedRun.stateBefore S rho
        (rho.events.filter (fun e => decide (e.time < t))).length :=
  congrArg (fun events => events.foldl (NamedWorld.step S) NamedWorld.init)
    (w4fkStrictFilterEqTake rho hsorted t)

omit [DecidableEq V] [Fintype V] in
private theorem w4fkStrictLengthsMono (rho : NamedRun V) {t1 t2 : Time} (ht : t1 ≤ t2) :
    (rho.events.filter (fun e => decide (e.time < t1))).length ≤
      (rho.events.filter (fun e => decide (e.time < t2))).length := by
  have hsub := List.Sublist.filter (fun e : NamedEvent V => decide (e.time < t2))
    (List.filter_sublist (p := fun e : NamedEvent V => decide (e.time < t1))
      (l := rho.events))
  have hs : (rho.events.filter (fun e => decide (e.time < t1))).filter
      (fun e => decide (e.time < t2)) =
      rho.events.filter (fun e => decide (e.time < t1)) := by
    apply List.filter_eq_self.mpr
    intro e he
    have hlow : e.time < t1 := by
      simpa only [decide_eq_true_eq] using (List.mem_filter.mp he).2
    simpa only [decide_eq_true_eq] using hlow.trans_le ht
  rw [hs] at hsub
  exact hsub.length_le

/-- The finalized prefix grows between two strict reads of the same node. -/
private theorem w4fkStateBeforeTimeFMono (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (reader : V) {t1 t2 : Time} (ht : t1 ≤ t2) :
    Block.Preceq (NamedRun.stateBeforeTime S rho t1 reader).st.core.F
      (NamedRun.stateBeforeTime S rho t2 reader).st.core.F := by
  rw [w4fkStrictReadEqIndex S rho sch.sorted t1, w4fkStrictReadEqIndex S rho sch.sorted t2]
  exact Proofs.NamedRuntime.stateBefore_F_mono S rho reader (w4fkStrictLengthsMono rho ht)





set_option maxHeartbeats 400000 in
private theorem w4fkPreviousActionCarrierInput
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} (hq : 0 < q) {p : Phase} {t : Time}
    {C : Block V} (hpost : S.E.t_GST ≤ S.a (q - 1))
    (hsourceHor : S.a (q - 1) ≤ rho.horizon)
    (hcut : early S.E S.hc q p ≤ rho.horizon)
    (horder : early S.E S.hc q p ≤ t)
    {v u : V} (hv : v ∈ rho.honest) (hu : u ∈ rho.honest)
    (hcarrier : Block.Preceq (actionSGBlockAt S rho u (q - 1)) C)
    (hF : Block.Preceq
      (NamedRun.stateBeforeTime S rho t v).st.core.F C) :
    Protocol.sgVote (actionAttestationAt S rho u (q - 1)).erase ∈
      DecoupledConsensusModel.Protocol.interpretedInputs
        (NamedRun.stateBeforeTime S rho t v).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho t v).st.core.F
        S.hc.η_SG q (early S.E S.hc q p) u ∧
      (Protocol.sgVote (actionAttestationAt S rho u (q - 1)).erase).round = q - 1 ∧
      (Protocol.sgVote (actionAttestationAt S rho u (q - 1)).erase).confirmed =
        some (actionSGBlockAt S rho u (q - 1)).root ∧
      Block.find? (NamedRun.stateBeforeTime S rho t v).st.core.T
        (actionSGBlockAt S rho u (q - 1)).root =
          some (actionSGBlockAt S rho u (q - 1)) := by
  have hqr : q - 1 < q := Nat.sub_lt hq (by decide)
  have hk : q - 1 ∈ Protocol.latest_window S.hc.η_SG q := by
    exact NamedOutageClosure.mem_latest_window
      (Nat.sub_le_sub_left S.hc.η_SG_ge_one q) hqr
  have hdeadline : max (S.a (q - 1)) S.E.t_GST + S.E.Δ ≤
      early S.E S.hc q p := by
    rw [max_eq_left hpost]
    apply (NamedOutageClosure.action_delta_le_early
      S S.hc.R_ge_three hqr).trans
    cases p <;> simp only [early, Phase.earlyOffset] <;>
      linarith [S.E.Δ_pos]
  let a := actionAttestationAt S rho u (q - 1)
  have hshape : a.val_index = u ∧ a.round = q - 1 ∧
      a.confirmed = some (actionSGBlockAt S rho u (q - 1)).root := by
    simpa only [a] using actionAttestationAt_shape S rho u (q - 1)
  have hemit : NamedRun.emits S rho u (Object.attest a) (S.a (q - 1)) := by
    simpa only [a] using
      honest_emits_exact_actionAttestationAt S adm hu (q - 1) hsourceHor
  obtain ⟨i, hi, _, hhead⟩ := Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
  dsimp at hhead
  obtain ⟨H, hH, hconfirmed⟩ := hhead
  have hbodySource : H ∈
      (NamedRun.stateBeforeTime S rho (S.a (q - 1)) u).st.bodies := by
    have hi' : rho.events[i]? = some (.tick u (S.a (q - 1))) := by
      simpa only [hshape.2.1] using hi
    have hstate := NamedActionSources.action_read_index S rho
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed i u (q - 1) hi'
    change H ∈ (NamedRun.stateBefore S rho i u).st.bodies at hH
    rw [← hstate]
    exact hH
  have hcarrierMem : actionSGBlockAt S rho u (q - 1) ∈
      (NamedRun.stateBeforeTime S rho (S.a (q - 1)) u).st.core.T :=
    actionSGBlockAt_mem_storeBeforeTime S rho u (q - 1)
  obtain ⟨D, hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (S.a (q - 1)) u hcarrierMem
  obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted (S.a (q - 1))
  have hDprefix : D ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact hDbody
  have hHprefix : H ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact hbodySource
  have hDrun : RunBlock S rho D :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hu (i := n) hDprefix
  have hHrun : RunBlock S rho H :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hu (i := n) hHprefix
  have hroot : D.root = H.root := by
    rw [← Proofs.NamedWire.erase_root D, hDerase]
    exact Option.some.inj (hshape.2.2.symm.trans hconfirmed)
  have hDH : D = H :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective D H
      hDrun hHrun D H (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self H)) hroot
  have hHErase : H.erase = actionSGBlockAt S rho u (q - 1) := by
    rw [← hDH, hDerase]
  have hHC : Block.Preceq H.erase C := by
    rw [hHErase]
    exact hcarrier
  have hinput : Protocol.sgVote a.erase ∈
      DecoupledConsensusModel.Protocol.interpretedInputs
        (NamedRun.stateBeforeTime S rho t v).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho t v).st.core.F
        S.hc.η_SG q (early S.E S.hc q p) u :=
    action_vote_mem_interpretedInputs_after_gst_common_upper
      S adm.toNamedAdmissibleCore p hk hu hv
      ⟨hshape.1, hshape.2.1, hemit⟩ ⟨i, hi, hH, hconfirmed⟩
      hHC hF (by simpa only [hshape.2.1] using hpost)
      (by simpa only [hshape.2.1] using hdeadline) horder hcut
  have hconfirmedInput : (Protocol.sgVote a.erase).confirmed =
      some (actionSGBlockAt S rho u (q - 1)).root := by
    rw [NamedOutageClosure.sgVote_confirmed, hshape.2.2]
  have hfind : Block.find? (NamedRun.stateBeforeTime S rho t v).st.core.T
      (actionSGBlockAt S rho u (q - 1)).root =
        some (actionSGBlockAt S rho u (q - 1)) := by
    have hbodyReady := (Finset.mem_filter.mp hinput).2
    simp only [DecoupledConsensusModel.Protocol.bodyReady, hconfirmedInput] at hbodyReady
    change (match Block.find? (NamedRun.stateBeforeTime S rho t v).st.core.T
        (actionSGBlockAt S rho u (q - 1)).root with
      | none => false
      | some H => stampedBefore
          (NamedRun.stateBeforeTime S rho t v).st.core.timestamp_block
          (early S.E S.hc q p) H &&
        Block.compatible H (NamedRun.stateBeforeTime S rho t v).st.core.F) = true
      at hbodyReady
    cases hx : Block.find? (NamedRun.stateBeforeTime S rho t v).st.core.T
        (actionSGBlockAt S rho u (q - 1)).root with
    | none => simp [hx] at hbodyReady
    | some X =>
        have hXmem := Proofs.HealingLemmas.find?_mem hx
        obtain ⟨Xn, hXerase, hXrun⟩ :=
          Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
            adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv t hXmem
        have hXHroot : Xn.root = H.root := by
          rw [← Proofs.NamedWire.erase_root Xn, hXerase,
            Proofs.HealingLemmas.find?_root hx, ← hHErase, Proofs.NamedWire.erase_root H]
        have hXH :=
          adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective Xn H
            hXrun hHrun Xn H (Or.inl (Proofs.NamedAncestry.named_self Xn))
            (Or.inr (Proofs.NamedAncestry.named_self H)) hXHroot
        congr 1
        exact hXerase.symm.trans ((congrArg NamedBlock.erase hXH).trans hHErase)
  refine ⟨by simpa only [a] using hinput, ?_, by simpa only [a] using hconfirmedInput,
    hfind⟩
  simpa only [NamedOutageClosure.sgVote_round] using hshape.2.1

set_option maxHeartbeats 400000 in
/-- A common upper block for the previous honest action carriers and the
reader's finalized block supplies the relative carrier window. -/
private theorem w4fkRelativeCarrierWindowAt
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} (hq : 0 < q) {p : Phase} {C : Block V}
    (hpost : S.E.t_GST ≤ S.a (q - 1))
    (hsourceHor : S.a (q - 1) ≤ rho.horizon)
    (hhor : domain S.E S.hc q p ≤ rho.horizon)
    (hcarrier : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u (q - 1)) C)
    (hroot : ∀ v ∈ rho.honest,
      Block.Preceq
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc q p) v).st.core.F C) :
    RelativeCarrierWindowAt S rho (q - 1) p := by
  intro v hv u hu
  change ∃ y ∈ DecoupledConsensusModel.Protocol.interpretedInputs
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (q - 1 + 1) p) v).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (q - 1 + 1) p) v).st.core.F
      S.hc.η_SG (q - 1 + 1) (early S.E S.hc (q - 1 + 1) p) u,
    y.round = q - 1 ∧
      y.confirmed = some (actionSGBlockAt S rho u (q - 1)).root ∧
      Block.find? (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (q - 1 + 1) p) v).st.core.T
        (actionSGBlockAt S rho u (q - 1)).root =
          some (actionSGBlockAt S rho u (q - 1))
  have huHon := ((Proofs.NamedOutageInputs.honestRoundVoters_iff
    S rho u (q - 1)).mp hu).1
  have hpred : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hq)
  have hearlyDomain : early S.E S.hc q p ≤ domain S.E S.hc q p := by
    cases p <;> simp only [early, domain, Phase.earlyOffset,
      Phase.domainOffset] <;> linarith [S.E.Δ_pos]
  have hres := w4fkPreviousActionCarrierInput S adm hq hpost hsourceHor
    (hearlyDomain.trans hhor) hearlyDomain hv huHon
    (hcarrier u huHon) (hroot v hv)
  refine ⟨Protocol.sgVote (actionAttestationAt S rho u (q - 1)).erase, ?_⟩
  simpa only [hpred] using hres


set_option maxHeartbeats 400000 in
private theorem w4fkNodeClearOfCommonEndpoint
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {q : Round} (hq : 0 < q) {C : Block V}
    (hactionHor : S.a q ≤ rho.horizon)
    (hgradeHor : domain S.E S.hc q .g2 ≤ rho.horizon)
    (hwindow : RelativeCarrierWindowAt S rho (q - 1) .g0)
    (hcarrier : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u (q - 1)) C)
    {D : Block V} (hCD : Block.Preceq C D) :
    ∀ v ∈ rho.honest,
      nodeClear S (actionReadAt S rho v q) q D = true := by
  have hpred : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hq)
  have hforming : Internal.NamedOutageEntry.GradeFormingMajority S rho (q - 1 + 1) := by
    rw [hpred]
    exact gradeFormingMajority_of_admissible_belowOneThird
      S adm hfb hq hgradeHor
  intro v hv
  have hframe := actionFrame_g0 S adm.toNamedAdmissibleCore hv hq hactionHor
  unfold nodeClear nodeRead
  change DecoupledConsensusModel.Protocol.clear
    (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho v q).cache
      (actionReadAt S rho v q).st.core.toHealing q) D = true
  unfold DecoupledConsensusModel.Protocol.clear
  rw [hframe]
  cases hroot : storeRoot S.E S.hc
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g0) v).st q .g0 with
  | none => rfl
  | some raw =>
      have hrawGrade : DecoupledConsensusModel.Protocol.gradeBool S.E
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc q .g0) v).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc q .g0) v).st.core.F
          S.hc.η_SG q (early S.E S.hc q .g0)
          (late S.E S.hc q .g0) raw = true :=
        (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hroot)).2
      have hrawGrade' : DecoupledConsensusModel.Protocol.gradeBool S.E
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (q - 1 + 1) .g0) v).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (q - 1 + 1) .g0) v).st.core.F
          S.hc.η_SG (q - 1 + 1) (early S.E S.hc (q - 1 + 1) .g0)
          (late S.E S.hc (q - 1 + 1) .g0) raw = true := by
        rw [hpred]
        exact hrawGrade
      obtain ⟨u, hu, hrawCarrier⟩ := relativeGrade_has_roundCarrier
        S adm.toNamedAdmissibleCore hwindow hforming hv hrawGrade'
      have huHon := ((Proofs.NamedOutageInputs.honestRoundVoters_iff
        S rho u (q - 1)).mp hu).1
      have hrawD : Block.Preceq raw D :=
        Block.preceq_trans hrawCarrier
          (Block.preceq_trans (hcarrier u huHon) hCD)
      have hclipD : Block.Preceq
          (DecoupledConsensusModel.Protocol.clipGrade raw
            (actionReadAt S rho v q).st.core.F) D :=
        Block.preceq_trans
          (NamedOutageClosure.q10_clip_preceq raw
            (actionReadAt S rho v q).st.core.F) hrawD
      change Block.compatible D
        (DecoupledConsensusModel.Protocol.clipGrade raw
          (actionReadAt S rho v q).st.core.F) = true
      simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr hclipD

set_option maxHeartbeats 400000 in
private theorem w4fkGetSgRootWithUpdateConfirmation
    (c : DecoupledConsensusModel.Protocol.Cache V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) (s : Slot) (r : Round) :
    Protocol.get_sg_root_with (NamedProfile.gradeContract c) E hc
        (Protocol.NamedDuties.update_confirmation_with
          (NamedProfile.gradeContract c) E hc st s).core.toHealing r =
      Protocol.get_sg_root_with (NamedProfile.gradeContract c) E hc
        st.core.toHealing r := rfl

set_option maxHeartbeats 400000 in
private theorem w4fkActionNodeAnchorPreceq
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {q : Round} (hq : 0 < q) {C : Block V}
    (hpost : S.E.t_GST ≤ S.a (q - 1))
    (hactionHor : S.a q ≤ rho.horizon)
    (hcarrier : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u (q - 1)) C)
    (hroot : ∀ v ∈ rho.honest,
      Block.Preceq
        (Protocol.get_fg_root
          (actionReadAt S rho v q).st.core.toHealing.toFG) C) :
    ∀ v ∈ rho.honest,
      Block.Preceq (nodeAnchor S (actionReadAt S rho v q) q) C := by
  have hpred : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hq)
  intro v hv
  have hanchor := confirmationAnchorAt_preceq_of_previousCarriers
    S adm hfb
      (q := q - 1) (s := S.hc.opening_slot q)
      (by simpa only [hpred] using Proofs.HealingLemmas.round_of_opening_succ S.hc q)
      hpost
      (by
        have hqcut : S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon := calc
          S.hc.Γ_neg1 S.E.Δ q = domain S.E S.hc q .g2 := by
            change slotStart S.E.Δ (S.hc.opening_slot q) - S.E.Δ =
              slotStart S.E.Δ (S.hc.opening_slot q) + (-1) * S.E.Δ
            ring
          _ ≤ rho.horizon :=
            (FrameForward.domain_le_a S q .g2).trans hactionHor
        simpa only [hpred] using hqcut)
      (by simpa only [opening_confirmation_time_eq_action] using hactionHor)
      (by simpa only [hpred] using hcarrier) hv
      (by simpa only [Internal.NamedRecoveryRead.confirmationInputRead,
        NamedActionReads.confirmationReadAt, opening_confirmation_time_eq_action]
        using hroot v hv)
  have hct : Protocol.confirmation_time S.E (S.hc.opening_slot q) = S.a q :=
    (Protocol.a_eq_confirmation_time S.hc S.E q).symm
  have hread : Internal.NamedRecoveryRead.confirmationInputRead S rho v
      (S.hc.opening_slot q) =
      NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBeforeTime S rho (S.a q) v) (S.a q) := by
    simp only [Internal.NamedRecoveryRead.confirmationInputRead,
      NamedActionReads.confirmationReadAt, hct]
  rw [confirmationAnchorAt, namedConfirmationAnchor, hread] at hanchor
  have hs : (NamedActionReads.confirmationReadFrom S
      (NamedRun.stateBeforeTime S rho (S.a q) v) (S.a q)).st.core.s =
      S.E.slotOf (S.a q) := rfl
  rw [hs, Proofs.HealingLemmas.ActionRound.round_of_slotOf_a] at hanchor
  have hcache : (actionReadAt S rho v q).cache =
      (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBeforeTime S rho (S.a q) v) (S.a q)).cache := rfl
  have hst : (actionReadAt S rho v q).st =
      Protocol.NamedDuties.update_confirmation_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S
            (NamedRun.stateBeforeTime S rho (S.a q) v) (S.a q)).cache)
        S.E S.hc
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBeforeTime S rho (S.a q) v) (S.a q)).st
        (S.E.slotOf (S.a q) - 1) := rfl
  change Protocol.get_sg_root_with
      (NamedProfile.gradeContract (actionReadAt S rho v q).cache)
      S.E S.hc (actionReadAt S rho v q).st.core.toHealing q ⪯ C
  rw [hcache, hst, w4fkGetSgRootWithUpdateConfirmation]
  exact hanchor


/-! ## 2. The moving chain supplies the prepared frame at the carrier action -/

/-- Verbatim copies of the three `private` normalizers and of
`openingSlot_three_le_of_healingBoundary_lt_proposal`
(`MovingChainFloorBridgeRun.lean:38, 50, 60`); that module cannot be imported
here because its cone and `W4D3FinalitySpineComposeRun`'s both define
`HealedTwoSlotHandoffPrepared`. -/
private theorem w4fkVoteTimeNormal (E : Env V) (s : Slot) :
    Protocol.vote_time E s = (4 * (s : Time) + 1) * E.Δ := by
  unfold Protocol.vote_time Env.t slotStart
  ring

private theorem w4fkProposalTimeNormal (E : Env V) (s : Slot) :
    Protocol.proposal_time E s = (4 * (s : Time) + 0) * E.Δ := by
  unfold Protocol.proposal_time Env.t slotStart
  ring

private theorem w4fkOpeningSlotThreeLe
    (S : Setup V) {q0 : Round} {d : Slot}
    (hguard : healingBoundaryTime S q0 < Protocol.proposal_time S.E d) :
    S.hc.opening_slot q0 + 3 ≤ d := by
  rw [healingBoundaryTime, w4fkVoteTimeNormal S.E _,
    w4fkProposalTimeNormal S.E d] at hguard
  have hnum : 4 * ((S.hc.opening_slot q0 + 2 : Slot) : Int) + 1 <
      4 * ((d : Slot) : Int) + 0 := by
    by_contra hnot
    exact absurd hguard (not_lt_of_ge
      (Int.mul_le_mul_of_nonneg_right (le_of_not_gt hnot)
        (le_of_lt S.E.Δ_pos)))
  have hcast : ((S.hc.opening_slot q0 : Slot) : Int) + 3 ≤ ((d : Slot) : Int) := by
    push_cast at hnum ⊢
    omega
  exact_mod_cast hcast

/-- The hand-off round is strictly after the boundary round. -/
theorem w4fkRoundLtOfAfterBoundary (S : Setup V) {q0 r : Round}
    (hafter : healingBoundaryTime S q0 <
      Protocol.proposal_time S.E (S.hc.opening_slot r)) : q0 < r := by
  have hslot : S.hc.opening_slot q0 + 3 ≤ S.hc.opening_slot r :=
    w4fkOpeningSlotThreeLe S hafter
  by_contra hnot
  have hle : r ≤ q0 := Nat.le_of_not_lt hnot
  have hmono : S.hc.opening_slot r ≤ S.hc.opening_slot q0 := by
    simp only [Protocol.HealConfig.opening_slot]
    exact Nat.mul_le_mul_right _ hle
  exact Nat.not_succ_le_self (S.hc.opening_slot q0)
    (le_trans (Nat.succ_le_of_lt (Nat.lt_of_lt_of_le
      (Nat.lt_add_of_pos_right (by decide : 0 < 3)) hslot)) hmono)

#print axioms w4fkRoundLtOfAfterBoundary





/-- **The moving-chain hand-off supplies both prepared-frame inputs.**

The endpoint `End` is the common upper block the prepared read needs: every
honest round-`(r-1)` SG carrier is below it, every honest FG root at the round
read is below it (through the round floor), and it is below every honest live
confirmation (through the opening proposal). The only fact outside the
hand-off is the post-GST bound at the previous action. -/
theorem movingChainPreparedFrameAt_of_fields
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbot : BelowOneThird S rho.honest)
    {q0 r : Round} {C End : Block V}
    (hafter : healingBoundaryTime S q0 <
      Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hinHorizon : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    (hopeningLive : ∀ v ∈ rho.honest, ∀ P : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r) = some P →
      (actionStoreAt S rho v r).st.core.live_confirmed = P.erase)
    (hchain : MovingChainAtCarrierFor S rho q0 r C End)
    (hpost : S.E.t_GST ≤ S.a (r - 1)) :
    ∀ v ∈ rho.honest,
      Block.Preceq (nodeAnchor S (actionReadAt S rho v r) r)
          (actionStoreAt S rho v r).live_confirmed ∧
        nodeClear S (actionReadAt S rho v r) r
          (actionStoreAt S rho v r).live_confirmed = true := by
  have hq0r : q0 < r := w4fkRoundLtOfAfterBoundary S hafter
  have hrpos : 0 < r := Nat.zero_lt_of_lt hq0r
  have hconf0 : Protocol.confirmation_time S.E (S.hc.opening_slot r) ≤ rho.horizon := by
    refine le_trans ?_ hinHorizon
    rw [Protocol.confirmation_time_eq_support_cutoff_succ,
      Protocol.confirmation_time_eq_support_cutoff_succ]
    exact Proofs.Optimistic.support_cutoff_mono S.E
      (Nat.add_le_add_right (Nat.le_add_right (S.hc.opening_slot r) 2) 1)
  have hactionHor : S.a r ≤ rho.horizon := by
    simpa only [Setup.a, Protocol.a_eq_confirmation_time] using hconf0
  have hprevHor : S.a (r - 1) ≤ rho.horizon :=
    ((action_strictMono S).monotone (Nat.sub_le r 1)).trans hactionHor
  obtain ⟨P, hP⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot r)
  have hcarrier : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u (r - 1)) End :=
    hchain.carriersBelowEndpoint
  
  -- floor. `healAnchor` IS `Protocol.get_sg_root` at the read's own round
  -- (`healAnchor_eq_get_sg_root`, `rfl`) and the SG root descends from the FG
  -- root on every anchor branch, so `anchorsBelowEndpoint` already bounds the
  -- root. Routing this through `floorAboveRoots` was the proof artifact that
  
  have hrootAction : ∀ v ∈ rho.honest,
      Block.Preceq
        (Protocol.get_fg_root
          (actionReadAt S rho v r).st.core.toHealing.toFG) End := by
    intro v hv
    refine Block.preceq_trans ?_ (hchain.anchorsBelowEndpoint v hv)
    exact healing_get_fg_root_preceq_get_sg_root S.E S.hc
      (actionStoreAt S rho v r).toHealing
      (S.hc.round_of (actionStoreAt S rho v r).toHealing.s)
  have hlive : ∀ v ∈ rho.honest,
      Block.Preceq End (actionStoreAt S rho v r).live_confirmed := by
    intro v hv
    have hlv : (actionStoreAt S rho v r).live_confirmed = P.erase :=
      hopeningLive v hv P hP
    rw [hlv]
    exact hchain.endpointBelowOpening P hP
  have hrootG0 : ∀ v ∈ rho.honest,
      Block.Preceq
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g0) v).st.core.F End := by
    intro v hv
    refine Block.preceq_trans
      (w4fkStateBeforeTimeFMono S rho
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v
        (FrameForward.domain_le_a S r .g0)) ?_
    exact Block.preceq_trans
      (StoreFinality.finalized_preceq_fgRoot
        (Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho (S.a r) v))
      (hrootAction v hv)
  have hdomainG2 : domain S.E S.hc r .g2 ≤ rho.horizon :=
    (FrameForward.domain_le_a S r .g2).trans hactionHor
  have hdomainG0 : domain S.E S.hc r .g0 ≤ rho.horizon :=
    (FrameForward.domain_le_a S r .g0).trans hactionHor
  have hwindow : RelativeCarrierWindowAt S rho (r - 1) .g0 :=
    w4fkRelativeCarrierWindowAt S adm hrpos hpost hprevHor hdomainG0 hcarrier hrootG0
  have hanchor := w4fkActionNodeAnchorPreceq S adm hbot hrpos hpost hactionHor
    hcarrier hrootAction
  intro v hv
  exact ⟨Block.preceq_trans (hanchor v hv) (hlive v hv),
    w4fkNodeClearOfCommonEndpoint S adm hbot hrpos hactionHor hdomainG2 hwindow
      hcarrier (hlive v hv) v hv⟩

#print axioms movingChainPreparedFrameAt_of_fields


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
