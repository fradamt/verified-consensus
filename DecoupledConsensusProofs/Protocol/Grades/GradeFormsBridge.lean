module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsProducers
public import DecoupledConsensusProofs.Protocol.Store.HonestPoolActionBridge
public import DecoupledConsensusProofs.Protocol.Store.BoundaryRows
public import DecoupledConsensusProofs.Protocol.Grades.Inclusions
public import DecoupledConsensusProofs.Protocol.Grades.Q10Frame

@[expose] public section

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Relative-grade quorum bridge -/

def relativePositiveAt (S : Setup V) (rho : Run V) (r : Round)
    (reader author : V) (C : Block V) : Bool :=
  DecoupledConsensusModel.Protocol.positive
    (relativeG2Read S rho r reader).st.core.toHealing.gradeView
    (relativeG2Read S rho r reader).st.core.F
    S.hc.η_SG r (early S.E S.hc r .g2) (late S.E S.hc r .g2) author C

def relativeOpposingAt (S : Setup V) (rho : Run V) (r : Round)
    (reader author : V) (C : Block V) : Bool :=
  DecoupledConsensusModel.Protocol.opposing
    (relativeG2Read S rho r reader).st.core.toHealing.gradeView
    (relativeG2Read S rho r reader).st.core.F
    S.hc.η_SG r (early S.E S.hc r .g2) (late S.E S.hc r .g2) author C

/- The G1-domain twins are kept explicit. Q10 transports the G2 grade to
the G1 read, but the post-GST input producer also uses the G1 read directly. -/



/- The next round's Gamma[-1] cutoff is exactly its G2-domain read. -/
theorem gammaNeg1_eq_domain_g2_succ (S : Setup V) (r : Round) :
    S.hc.Γ_neg1 S.E.Δ (r + 1) = domain S.E S.hc (r + 1) .g2 := by
  change slotStart S.E.Δ (S.hc.opening_slot (r + 1)) - S.E.Δ =
    slotStart S.E.Δ (S.hc.opening_slot (r + 1)) + (-1) * S.E.Δ
  ring


structure RelativeG2Support (S : Setup V) (rho : Run V) (r : Round)
    (C : Block V) : Prop where
  active : ∀ v ∈ rho.honest,
    C ∈ filteredTree (relativeG2Read S rho r v)
  positive : ∀ w ∈ rho.honest, ∀ v ∈ rho.honest,
    relativePositiveAt S rho r w v C = true
  opposing_not_honest : ∀ w ∈ rho.honest, ∀ v,
    relativeOpposingAt S rho r w v C = true →
    v ∉ rho.honest

/- The awake-window version keeps the active and opposition clauses at the
   honest set, but restricts positive support to validators represented by an
   awake action in the SG expiry window. -/

private theorem cleanActionRead_preceq_actionSGBlockAt_local
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {P : Block V} (hclean : CleanActionReadFor S rho r P)
    {w v : V} (hw : w ∈ rho.honest) (hv : v ∈ rho.honest) :
    Block.Preceq P (actionSGBlockAt S rho v r) := by
  let C := actionSGBlockAt S rho v r
  have hcov := (hclean.resolved_support w hw v hv).2
  simp only [Protocol.head_covers, actionSGVoteAt] at hcov
  cases hfind : Block.find? (gradeViewAt S rho w (r + 1)).T C.root with
  | none =>
      rw [hfind] at hcov
      cases hcov
  | some X =>
      rw [hfind] at hcov
      have hXmem : X ∈
          (rho.storeBeforeTime S w (S.a (r + 1))).T := by
        simpa only [gradeViewAt, healStoreAt, Run.storeBeforeTime,
          Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using
          Proofs.HealingLemmas.find?_mem hfind
      have hCmem : C ∈ (rho.storeBeforeTime S v (S.a r)).T := by
        simpa only [C] using actionSGBlockAt_mem_storeBeforeTime S rho v r
      obtain ⟨Nw, hNw, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
        S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.a (r + 1))
      obtain ⟨Nv, hNv, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
        S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.a r)
      obtain ⟨Xn, hXnErase, hXrun⟩ :=
        Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
          (adm.toNamedAdmissibleCore.toNamedScheduleWellFormed) hw
          (S.a (r + 1)) hXmem
      obtain ⟨Cn, hCnErase, hCrun⟩ :=
        Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
          (adm.toNamedAdmissibleCore.toNamedScheduleWellFormed) hv
          (S.a r) hCmem
      have hroot : X.root = C.root := Proofs.HealingLemmas.find?_root hfind
      have hrootN : Xn.root = Cn.root := by
        rw [← Proofs.NamedWire.erase_root Xn, ← Proofs.NamedWire.erase_root Cn,
          hXnErase, hCnErase, hroot]
      have hXC : Xn = Cn :=
        adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective Xn Cn
          hXrun hCrun Xn Cn (Or.inl (Proofs.NamedAncestry.named_self Xn))
          (Or.inr (Proofs.NamedAncestry.named_self Cn)) hrootN
      have hXCerase : X = C := by
        calc
          X = Xn.erase := hXnErase.symm
          _ = Cn.erase := congrArg NamedBlock.erase hXC
          _ = C := hCnErase
      change Block.Preceq P C
      rw [hXCerase] at hcov
      exact hcov

private theorem strict_finality_mono_between
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
  exact Protocol.stateBefore_F_mono S rho w hidx

private theorem actionSGVoteAt_interpreted_early_of_cleanActionRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {P : Block V} (hclean : CleanActionReadFor S rho r P)
    {w v : V} (hw : w ∈ rho.honest) (hv : v ∈ rho.honest) :
    actionSGVoteAt S rho v r ∈
        DecoupledConsensusModel.Protocol.interpretedInputs
          (relativeG2Read S rho (r + 1) w).st.core.toHealing.gradeView
          (relativeG2Read S rho (r + 1) w).st.core.F
          S.hc.η_SG (r + 1) (early S.E S.hc (r + 1) .g2) v ∧
      DecoupledConsensusModel.Protocol.localCovers
        (relativeG2Read S rho (r + 1) w).st.core.toHealing.gradeView
        (actionSGVoteAt S rho v r).confirmed P = true := by
  let C := actionSGBlockAt S rho v r
  let n := relativeG2Read S rho (r + 1) w
  let gv := n.st.core.toHealing.gradeView
  let F := n.st.core.F
  let early := early S.E S.hc (r + 1) .g2
  have sch : ScheduleWellFormed S rho :=
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
  have hdeadline : S.a r + S.E.Δ ≤ rho.horizon :=
    (action_add_delta_le_next_Γ_neg1 S r).trans hclean.cutoff_in_horizon
  have hEarly : S.a r + S.E.Δ ≤ early :=
    NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
      (Nat.lt_succ_self r)
  have hrowData := actionAttestationAt_rows_before_delta S adm hv hw r
    hclean.post_gst hdeadline
  obtain ⟨j', e', hj', hjt', hrow⟩ := hrowData
  have hround : (actionAttestationAt S rho v r).round = r :=
    (actionAttestationAt_shape S rho v r).2.1
  have hrow' : actionAttestationAt S rho v r ∈
      (rho.stateBefore S (j' + 1) w).st.sg_rows
        (actionAttestationAt S rho v r).round := by
    rw [hround]
    exact hrow
  have hearlyEvent : e'.time < early := hjt'.trans_le hEarly
  have hDomain' : e'.time < domain S.E S.hc (r + 1) .g2 := by
    exact lt_of_lt_of_le hearlyEvent
      (NamedOutageClosure.early_le_domain S (r + 1))
  have hpool' : actionSGVoteAt S rho v r ∈
      (rho.stateBefore S (j' + 1) w).st.toHealing.sg_votes r := by
    change actionSGVoteAt S rho v r ∈
      ((rho.stateBefore S (j' + 1) w).st.core.sg_pool r).image Protocol.sgVote
    have hp := NamedAdmission.pool_view_mem
      (rho.stateBefore S (j' + 1) w).st
      (Proofs.NamedRuntime.stateBefore_invariants S rho (j' + 1) w).1.1.1.2.2.2.1
      _ hrow'
    rw [hround] at hp
    have himg := Finset.mem_image_of_mem Protocol.sgVote hp
    rw [sgVote_actionAttestationAt] at himg
    exact himg
  have huPool : actionSGVoteAt S rho v r ∈
      (rho.stateBeforeTime S (domain S.E S.hc (r + 1) .g2) w).st.toHealing.sg_votes r := by
    exact Protocol.sgVote_mem_stateBeforeTime_of_post S sch hj' hDomain' hpool'
  have huD : actionSGVoteAt S rho v r ∈ gv.sg_votes r := by
    simpa only [gv, n, relativeG2Read] using huPool
  have hstamp0 := GradeDeliveryRun.timestamp_sg_vote_before_of_mem_post_event
    S sch hj' hrow' hearlyEvent
  have hstamp1 : occurrenceBefore
      ((rho.stateBefore S (j' + 1) w).st.timestamp_sg_vote
        (actionSGVoteAt S rho v r)) early = true := by
    simpa only [sgVote_actionAttestationAt] using hstamp0
  have hstampD := GradeDeliveryRun.timestamp_sg_vote_stateBeforeTime_of_post
    S sch hj' hDomain' hpool'
  have hstamp : occurrenceBefore (gv.timestamp_sg_vote
      (actionSGVoteAt S rho v r)) early = true := by
    have hstampD' : gv.timestamp_sg_vote (actionSGVoteAt S rho v r) =
        (rho.stateBefore S (j' + 1) w).st.timestamp_sg_vote
          (actionSGVoteAt S rho v r) := by
      simpa only [gv, n, relativeG2Read, Run.storeBeforeTime,
        Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hstampD
    rw [hstampD']
    exact hstamp1
  have hwindow : r ∈ Protocol.latest_window S.hc.η_SG (r + 1) := by
    simpa only [Nat.add_sub_cancel] using
      Protocol.pred_mem_latest_window S.hc.η_SG (r + 1)
        S.hc.η_SG_ge_one (Nat.succ_pos r)
  have hraw : actionSGVoteAt S rho v r ∈
      DecoupledConsensusModel.Protocol.rawInputs gv S.hc.η_SG (r + 1) early v := by
    simp only [DecoupledConsensusModel.Protocol.rawInputs]
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_biUnion.mpr ⟨r, List.mem_toFinset.mpr hwindow, huD⟩,
      (actionSGVoteAt_shape S rho v r).1, hstamp⟩
  have hCpre : Block.Preceq P C := by
    simpa only [C] using
      cleanActionRead_preceq_actionSGBlockAt_local S adm hclean hw hv
  have hCsource : C ∈ (rho.storeBeforeTime S v (S.a r)).T := by
    simpa only [C] using actionSGBlockAt_mem_storeBeforeTime S rho v r
  have hrelayRead : S.a r + S.E.Δ ≤ S.a (r + 1) :=
    (action_add_delta_le_next_Γ_neg1 S r).trans
      (le_of_lt (next_Γ_neg1_lt_action S r))
  have hvisible : C ∈
      (rho.storeBeforeTime S w (domain S.E S.hc (r + 1) .g2)).T ∧
      stampedBefore
        (rho.storeBeforeTime S w (domain S.E S.hc (r + 1) .g2)).timestamp_block early C = true := by
    rcases block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTime
        S sch v (S.a r) hCsource with
      hgen | ⟨D, i, t, hDerase, hacc, ht⟩
    · simpa only [C, hgen] using
        Protocol.genesis_mem_and_stamp_storeBeforeTime S sch w
          (domain S.E S.hc (r + 1) .g2) early
    · have hDpos : 0 < D.slot := by
        rw [← Proofs.NamedWire.erase_slot]
        exact Nat.zero_lt_of_lt (Protocol.parent_slot_lt_of_acceptsAt_block S hacc)
      have hDhist := finalizedBelowAtDeliveriesBefore_of_filteredAtLaterRead
        S adm hrelayRead
          (by simpa only [healStoreAt] using hclean.active w hw)
          (by rw [hDerase]; exact hCpre)
      have hhor : S.a r + S.E.Δ ≤ rho.horizon :=
        (action_add_delta_le_next_Γ_neg1 S r).trans hclean.cutoff_in_horizon
      have hadmitD := Protocol.block_admittedBefore_of_accepted_after_cutoff
        S adm hv hw hDpos hacc ht hclean.post_gst rfl hhor hDhist
      have hadmitC : Protocol.AdmittedBefore S rho w C
          (S.a r + S.E.Δ) := by
        simpa only [hDerase] using hadmitD
      have hvisible' := Protocol.admittedBefore_mem_and_stamp_at
        (Gamma := S.a r + S.E.Δ)
        (Gamma' := domain S.E S.hc (r + 1) .g2) S sch hadmitC
        (hEarly.trans (NamedOutageClosure.early_le_domain S (r + 1)))
      refine ⟨hvisible'.1, ?_⟩
      have hstampGamma := hvisible'.2
      rw [stampedBefore_eq_occurrenceBefore] at hstampGamma ⊢
      exact occurrenceBefore_mono hEarly hstampGamma
  have hCmem : C ∈
      (rho.storeBeforeTime S w (domain S.E S.hc (r + 1) .g2)).T := by
    simpa only [C] using hvisible.1
  have hfind : Block.find?
      (rho.storeBeforeTime S w (domain S.E S.hc (r + 1) .g2)).T C.root = some C := by
    apply Proofs.Optimistic.find?_eq_some_of_unique hCmem
    intro X hX hroot
    obtain ⟨Xn, hXnErase, hXrun⟩ :=
      Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S sch hw
        (domain S.E S.hc (r + 1) .g2) hX
    obtain ⟨Cn, hCnErase, hCrun⟩ :=
      Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S sch hw
        (domain S.E S.hc (r + 1) .g2) hCmem
    have hrootN : Xn.root = Cn.root := by
      rw [← Proofs.NamedWire.erase_root Xn, ← Proofs.NamedWire.erase_root Cn,
        hXnErase, hCnErase, hroot]
    have hXC := adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      Xn Cn hXrun hCrun Xn Cn (Or.inl (Proofs.NamedAncestry.named_self Xn))
      (Or.inr (Proofs.NamedAncestry.named_self Cn)) hrootN
    rw [← hXnErase, hXC, hCnErase]
  have hDomAction : domain S.E S.hc (r + 1) .g2 ≤ S.a (r + 1) := by
    rw [← gammaNeg1_eq_domain_g2_succ S r]
    exact (next_Γ_neg1_lt_action S r).le
  have hFaction : Block.Preceq
      (rho.storeBeforeTime S w (S.a (r + 1))).F P :=
    GradeDeliveryRun.finalized_preceq_of_mem_filtered_at_read S rho
      (hclean.active w hw)
  have hFmono : Block.Preceq
      (rho.storeBeforeTime S w (domain S.E S.hc (r + 1) .g2)).F
      (rho.storeBeforeTime S w (S.a (r + 1))).F :=
    strict_finality_mono_between S sch w hDomAction
  have hFP : Block.Preceq
      (rho.storeBeforeTime S w (domain S.E S.hc (r + 1) .g2)).F P :=
    Block.preceq_trans hFmono hFaction
  have hFC : Block.Preceq
      (rho.storeBeforeTime S w (domain S.E S.hc (r + 1) .g2)).F C :=
    Block.preceq_trans hFP hCpre
  have huconf : (actionSGVoteAt S rho v r).confirmed = some C.root := by
    simpa only [C] using (actionAttestationAt_shape S rho v r).2.2
  have hfindGV : Block.find? gv.T C.root = some C := by
    simpa only [gv, n, relativeG2Read, Run.storeBeforeTime,
      Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hfind
  have hblockStamp : stampedBefore gv.timestamp_block early C = true := by
    simpa only [gv, n, relativeG2Read, Run.storeBeforeTime,
      Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hvisible.2
  have hbody : DecoupledConsensusModel.Protocol.bodyReady gv F early
      (actionSGVoteAt S rho v r) = true := by
    simp only [DecoupledConsensusModel.Protocol.bodyReady, huconf, hfindGV]
    simp only [Bool.and_eq_true]
    exact ⟨hblockStamp, by
      simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr hFC⟩
  refine ⟨Finset.mem_filter.mpr ⟨hraw, hbody⟩, ?_⟩
  simp only [DecoupledConsensusModel.Protocol.localCovers]
  rw [huconf]
  change Protocol.head_covers gv.T P (some C.root) = true
  simp only [Protocol.head_covers, hfindGV]
  exact hCpre

/- The weight bridge from the support package to the named surface. -/
theorem relativePositive_of_cleanActionRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {P : Block V} (hclean : CleanActionReadFor S rho r P)
    {w v : V} (hw : w ∈ rho.honest) (hv : v ∈ rho.honest) :
    relativePositiveAt S rho (r + 1) w v P = true := by
  let n := relativeG2Read S rho (r + 1) w
  let gv := n.st.core.toHealing.gradeView
  let F := n.st.core.F
  let early := early S.E S.hc (r + 1) .g2
  let late := late S.E S.hc (r + 1) .g2
  have hmain := actionSGVoteAt_interpreted_early_of_cleanActionRead
    S adm hclean hw hv
  have hinterp : actionSGVoteAt S rho v r ∈
      DecoupledConsensusModel.Protocol.interpretedInputs gv F S.hc.η_SG (r + 1) early v := by
    simpa only [n, gv, F, early] using hmain.1
  have hcover : DecoupledConsensusModel.Protocol.localCovers gv
      (actionSGVoteAt S rho v r).confirmed P = true := by
    simpa only [n, gv, F, early] using hmain.2
  change DecoupledConsensusModel.Protocol.positive gv F S.hc.η_SG (r + 1)
    early late v P = true
  simp only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq]
  refine ⟨DecoupledConsensusModel.Protocol.token (actionSGVoteAt S rho v r), ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.mem_image_of_mem DecoupledConsensusModel.Protocol.token hinterp
  · intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    have hzdata := Finset.mem_filter.mp hz
    have hzraw := Finset.mem_filter.mp hzdata.1
    obtain ⟨k, hk, hzk⟩ := Finset.mem_biUnion.mp hzraw.1
    have hk' : k ∈ Protocol.latest_window S.hc.η_SG (r + 1) :=
      List.mem_toFinset.mp hk
    have hklt : k < r + 1 := (NamedOutageClosure.window_bounds hk').2
    have hzkStore : z ∈
        (rho.storeBeforeTime S w (domain S.E S.hc (r + 1) .g2)).toHealing.sg_votes k := by
      simpa only [gv, n, relativeG2Read, Run.storeBeforeTime,
        Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hzk
    have hzEq : z = actionSGVoteAt S rho v k :=
      honestSGVote_eq_actionSGVoteAt_of_mem_storeBeforeTime
        (k := k) S adm hv hzkStore hzraw.2.1
    have hzround : z.round = k := by
      rw [hzEq]
      exact (actionSGVoteAt_shape S rho v k).2.1
    change z.round ≤ r
    rw [hzround]
    exact Nat.le_of_lt_succ hklt
  · change DecoupledConsensusModel.Protocol.localCovers gv
      (DecoupledConsensusModel.Protocol.token (actionSGVoteAt S rho v r)).key P = true
    simpa only [DecoupledConsensusModel.Protocol.token] using hcover
  · intro x hx y hy _hlo hxy
    obtain ⟨xv, hxv, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨yv, hyv, rfl⟩ := Finset.mem_image.mp hy
    have hxdata := Finset.mem_filter.mp hxv
    have hydata := Finset.mem_filter.mp hyv
    obtain ⟨kx, hkx, hxpool⟩ := Finset.mem_biUnion.mp hxdata.1
    obtain ⟨ky, hky, hypool⟩ := Finset.mem_biUnion.mp hydata.1
    have hxStore : xv ∈
        (rho.storeBeforeTime S w (domain S.E S.hc (r + 1) .g2)).toHealing.sg_votes kx := by
      simpa only [gv, n, relativeG2Read, Run.storeBeforeTime,
        Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hxpool
    have hyStore : yv ∈
        (rho.storeBeforeTime S w (domain S.E S.hc (r + 1) .g2)).toHealing.sg_votes ky := by
      simpa only [gv, n, relativeG2Read, Run.storeBeforeTime,
        Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hypool
    have hxEq : xv = actionSGVoteAt S rho v kx :=
      honestSGVote_eq_actionSGVoteAt_of_mem_storeBeforeTime
        (k := kx) S adm hv hxStore hxdata.2.1
    have hyEq : yv = actionSGVoteAt S rho v ky :=
      honestSGVote_eq_actionSGVoteAt_of_mem_storeBeforeTime
        (k := ky) S adm hv hyStore hydata.2.1
    have hxround : xv.round = kx := by
      rw [hxEq]
      exact (actionSGVoteAt_shape S rho v kx).2.1
    have hyround : yv.round = ky := by
      rw [hyEq]
      exact (actionSGVoteAt_shape S rho v ky).2.1
    change xv.round = yv.round at hxy
    have hkyx : ky = kx := hyround.symm.trans (hxy.symm.trans hxround)
    subst ky
    have hyEq' : yv = actionSGVoteAt S rho v kx := by
      simpa only [hkyx] using hyEq
    have hvote : xv = yv := hxEq.trans hyEq'.symm
    exact congrArg (fun z => (DecoupledConsensusModel.Protocol.token z).key) hvote
  · intro x hx hlt
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    have hzdata := Finset.mem_filter.mp hz
    have hzraw := Finset.mem_filter.mp hzdata.1
    obtain ⟨k, hk, hzk⟩ := Finset.mem_biUnion.mp hzraw.1
    have hk' : k ∈ Protocol.latest_window S.hc.η_SG (r + 1) :=
      List.mem_toFinset.mp hk
    have hklt : k < r + 1 := (NamedOutageClosure.window_bounds hk').2
    have hzkStore : z ∈
        (rho.storeBeforeTime S w (domain S.E S.hc (r + 1) .g2)).toHealing.sg_votes k := by
      simpa only [gv, n, relativeG2Read, Run.storeBeforeTime,
        Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hzk
    have hzEq := honestSGVote_eq_actionSGVoteAt_of_mem_storeBeforeTime
      S adm hv hzkStore hzraw.2.1
    have hzround : z.round = k := by
      rw [hzEq]
      exact (actionSGVoteAt_shape S rho v k).2.1
    change r < z.round at hlt
    rw [hzround] at hlt
    exfalso
    exact (Nat.not_lt_of_ge (Nat.le_of_lt_succ hklt)) hlt

theorem relativeOpposingNotHonest_of_cleanActionRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {P : Block V} (hclean : CleanActionReadFor S rho r P)
    {w v : V} (hw : w ∈ rho.honest)
    (hopp : relativeOpposingAt S rho (r + 1) w v P = true) :
    v ∉ rho.honest := by
  intro hv
  let n := relativeG2Read S rho (r + 1) w
  let gv := n.st.core.toHealing.gradeView
  let F := n.st.core.F
  let early := early S.E S.hc (r + 1) .g2
  let late := late S.E S.hc (r + 1) .g2
  have hmain := actionSGVoteAt_interpreted_early_of_cleanActionRead
    S adm hclean hw hv
  have hinterp : actionSGVoteAt S rho v r ∈
      DecoupledConsensusModel.Protocol.interpretedInputs gv F S.hc.η_SG (r + 1) early v := by
    simpa only [n, gv, F, early] using hmain.1
  have hcover : DecoupledConsensusModel.Protocol.localCovers gv
      (actionSGVoteAt S rho v r).confirmed P = true := by
    simpa only [n, gv, F, early] using hmain.2
  have hOpp : DecoupledConsensusModel.Protocol.opposing gv F S.hc.η_SG (r + 1)
      early late v P = true := by
    simpa only [relativeOpposingAt, n, gv, F, early, late] using hopp
  simp only [DecoupledConsensusModel.Protocol.opposing, decide_eq_true_eq] at hOpp
  rcases hOpp with hbad | hequiv
  · obtain ⟨x, hx, hguard, hnot⟩ := hbad
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    have hzdata := Finset.mem_filter.mp hz
    have hzraw := Finset.mem_filter.mp hzdata.1
    obtain ⟨k, hk, hzk⟩ := Finset.mem_biUnion.mp hzraw.1
    have hk' : k ∈ Protocol.latest_window S.hc.η_SG (r + 1) :=
      List.mem_toFinset.mp hk
    have hklt : k < r + 1 := (NamedOutageClosure.window_bounds hk').2
    have hzkStore : z ∈
        (rho.storeBeforeTime S w (domain S.E S.hc (r + 1) .g2)).toHealing.sg_votes k := by
      simpa only [gv, n, relativeG2Read, Run.storeBeforeTime,
        Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hzk
    have hzEq : z = actionSGVoteAt S rho v k :=
      honestSGVote_eq_actionSGVoteAt_of_mem_storeBeforeTime
        (k := k) S adm hv hzkStore hzraw.2.1
    have hzround : z.round = k := by
      rw [hzEq]
      exact (actionSGVoteAt_shape S rho v k).2.1
    have htoken : DecoupledConsensusModel.Protocol.token (actionSGVoteAt S rho v r) ∈
        DecoupledConsensusModel.Protocol.readyView gv F S.hc.η_SG (r + 1) early v :=
      Finset.mem_image_of_mem DecoupledConsensusModel.Protocol.token hinterp
    have hmax := hguard
      (DecoupledConsensusModel.Protocol.token (actionSGVoteAt S rho v r)) htoken
    change (actionSGVoteAt S rho v r).round ≤ z.round at hmax
    have hmax' : r ≤ z.round := by
      calc
        r = (actionSGVoteAt S rho v r).round :=
          (actionSGVoteAt_shape S rho v r).2.1.symm
        _ ≤ z.round := hmax
    have hk_le : k ≤ r := Nat.le_of_lt_succ hklt
    have hr_le : r ≤ k := hmax'.trans_eq hzround
    have hkEq : k = r := Nat.le_antisymm hk_le hr_le
    have hzEqR : z = actionSGVoteAt S rho v r := by
      calc
        z = actionSGVoteAt S rho v k := hzEq
        _ = actionSGVoteAt S rho v r := by rw [hkEq]
    apply hnot
    simpa only [DecoupledConsensusModel.Protocol.token] using
      (hzEqR ▸ hcover)
  · obtain ⟨x, hx, y, hy, _hguard, hround, hkey⟩ := hequiv
    obtain ⟨xv, hxv, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨yv, hyv, rfl⟩ := Finset.mem_image.mp hy
    have hxdata := Finset.mem_filter.mp hxv
    have hydata := Finset.mem_filter.mp hyv
    obtain ⟨kx, hkx, hxpool⟩ := Finset.mem_biUnion.mp hxdata.1
    obtain ⟨ky, hky, hypool⟩ := Finset.mem_biUnion.mp hydata.1
    have hxStore : xv ∈
        (rho.storeBeforeTime S w (domain S.E S.hc (r + 1) .g2)).toHealing.sg_votes kx := by
      simpa only [gv, n, relativeG2Read, Run.storeBeforeTime,
        Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hxpool
    have hyStore : yv ∈
        (rho.storeBeforeTime S w (domain S.E S.hc (r + 1) .g2)).toHealing.sg_votes ky := by
      simpa only [gv, n, relativeG2Read, Run.storeBeforeTime,
        Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hypool
    have hxEq : xv = actionSGVoteAt S rho v kx :=
      honestSGVote_eq_actionSGVoteAt_of_mem_storeBeforeTime
        (k := kx) S adm hv hxStore hxdata.2.1
    have hyEq : yv = actionSGVoteAt S rho v ky :=
      honestSGVote_eq_actionSGVoteAt_of_mem_storeBeforeTime
        (k := ky) S adm hv hyStore hydata.2.1
    have hxround : xv.round = kx := by
      rw [hxEq]
      exact (actionSGVoteAt_shape S rho v kx).2.1
    have hyround : yv.round = ky := by
      rw [hyEq]
      exact (actionSGVoteAt_shape S rho v ky).2.1
    change xv.round = yv.round at hround
    have hkyx : ky = kx := hyround.symm.trans (hround.symm.trans hxround)
    have hyEq' : yv = actionSGVoteAt S rho v kx := by
      simpa only [hkyx] using hyEq
    exact hkey (congrArg (fun z => (DecoupledConsensusModel.Protocol.token z).key)
      (hxEq.trans hyEq'.symm))

theorem phaseGrade_of_honestPositiveSupport
    (E : Env V) (gv : Protocol.GradeView V) (F : Block V)
    (Hon : Finset V) (eta r : Round) (ea la : Time) (C : Block V)
    (hmajority : E.electorate.weightOf (Finset.univ \ Hon) <
      E.electorate.weightOf Hon)
    (hpositive : ∀ v ∈ Hon,
      DecoupledConsensusModel.Protocol.positive gv F eta r ea la v C = true)
    (hopposing : ∀ v,
      DecoupledConsensusModel.Protocol.opposing gv F eta r ea la v C = true →
        v ∉ Hon) :
    DecoupledConsensusModel.Protocol.gradeBool E gv F eta r ea la C = true := by
  simp only [DecoupledConsensusModel.Protocol.gradeBool, decide_eq_true_eq]
  have hOpp : (Finset.univ.filter fun v =>
      DecoupledConsensusModel.Protocol.opposing gv F eta r ea la v C = true) ⊆
      Finset.univ \ Hon := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ v,
      hopposing v (Finset.mem_filter.mp hv).2⟩
  have hPos : Hon ⊆ Finset.univ.filter fun v =>
      DecoupledConsensusModel.Protocol.positive gv F eta r ea la v C = true := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hpositive v hv⟩
  exact lt_of_le_of_lt (E.electorate.weightOf_mono hOpp)
    (lt_of_lt_of_le hmajority (E.electorate.weightOf_mono hPos))

/-- The relative-grade weight step for the outage claim. Current-round honest
voters support the candidate, while every opponent is faulty or stale. -/
theorem phaseGrade_of_gradeFormingMajority
    (S : Setup V) (rho : Run V) (r : Round)
    (gv : Protocol.GradeView V) (F C : Block V) (ea la : Time)
    (hmajority : Internal.NamedOutageEntry.GradeFormingMajority S rho r)
    (hpositive : Internal.NamedOutageEntry.honestRoundVoters S rho (r - 1) ⊆
      Finset.univ.filter fun v =>
        DecoupledConsensusModel.Protocol.positive gv F S.hc.η_SG r ea la v C = true)
    (hopposing : (Finset.univ.filter fun v =>
      DecoupledConsensusModel.Protocol.opposing gv F S.hc.η_SG r ea la v C = true) ⊆
        (Finset.univ \ rho.honest) ∪
          Internal.NamedOutageEntry.staleHistoricalVoters S rho r) :
    DecoupledConsensusModel.Protocol.gradeBool S.E gv F S.hc.η_SG r ea la C = true := by
  simp only [DecoupledConsensusModel.Protocol.gradeBool, decide_eq_true_eq]
  have hleft := S.E.electorate.weightOf_mono hopposing
  have hright := S.E.electorate.weightOf_mono hpositive
  exact hleft.trans_lt (hmajority.trans_le hright)

theorem relativeG2Active_of_cleanActionRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {P : Block V}
    (hclean : CleanActionReadFor S rho r P) {w : V} (hw : w ∈ rho.honest) :
    P ∈ filteredTree (relativeG2Read S rho (r + 1) w) := by
  exact hclean.active_domain w hw

theorem relativeG2Support_of_cleanActionRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {P : Block V}
    (hclean : CleanActionReadFor S rho r P) :
    RelativeG2Support S rho (r + 1) P := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun w hw => relativeG2Active_of_cleanActionRead S adm hclean hw
  · intro w hw v hv
    exact relativePositive_of_cleanActionRead S adm hclean hw hv
  · intro w hw v hopp
    exact relativeOpposingNotHonest_of_cleanActionRead S adm hclean hw hopp

set_option maxHeartbeats 800000 in
theorem namedGradeFormsAt_of_honestPositiveSupport
    (S : Setup V) {rho : Run V} {r : Round} {C : Block V}
    (hmajority : HonestWeightMajority S rho.honest)
    (hsupport : RelativeG2Support S rho r C) :
    NamedGradeFormsAt S rho r C := by
  intro w hw
  refine ⟨hsupport.active w hw, ?_⟩
  change DecoupledConsensusModel.Protocol.gradeBool S.E
    (relativeG2Read S rho r w).st.core.toHealing.gradeView
    (relativeG2Read S rho r w).st.core.F S.hc.η_SG r
    (early S.E S.hc r .g2) (late S.E S.hc r .g2) C = true
  apply phaseGrade_of_honestPositiveSupport
  · exact hmajority
  · intro v hv
    simpa only [relativePositiveAt, relativeG2Read] using
      hsupport.positive w hw v hv
  · intro v hv
    apply hsupport.opposing_not_honest w hw v
    simpa only [relativeOpposingAt, relativeG2Read] using hv




/-- A clean action read supplies the relative grade at the next G2-domain read.

: the relative grade is frozen at that domain read, so its protected block
must use `CleanActionReadFor.active_domain`; action-read activity remains a
separate field. -/
theorem namedGradeFormsAt_of_cleanActionRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hmajority : HonestWeightMajority S rho.honest)
    {r : Round} {P : Block V}
    (hclean : CleanActionReadFor S rho r P) :
    NamedGradeFormsAt S rho (r + 1) P := by
  exact namedGradeFormsAt_of_honestPositiveSupport S hmajority
    (relativeG2Support_of_cleanActionRead S adm hclean)

/-- An action-carrier cover and the two read-local activity facts form the
next named relative grade. -/
theorem namedGradeFormsAt_succ_of_actionCarriersCover_and_next_active
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hmajority : HonestWeightMajority S rho.honest)
    {r : Round} {P : Block V}
    (hcover : ActionCarriersCover S rho r P)
    (hpost : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hactive : ∀ w ∈ rho.honest,
      P ∈ Protocol.get_filtered_block_tree
        (healStoreAt S rho w (r + 1)).toFG)
    (hactiveDomain : ∀ w ∈ rho.honest,
      P ∈ PhaseGrades.filteredTree (relativeG2Read S rho (r + 1) w)) :
    NamedGradeFormsAt S rho (r + 1) P := by
  have hclean := cleanActionReadFor_of_actionCarriersCover_and_next_active
    S adm hcover hpost hcut hactive hactiveDomain
  exact namedGradeFormsAt_of_cleanActionRead S adm hmajority hclean

/-- The FG-root-floor form derives the carrier cover before the same named
successor-grade handover. -/
theorem namedGradeFormsAt_succ_of_fgRootFloor
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hmajority : HonestWeightMajority S rho.honest)
    {r : Round} {P F : Block V}
    (hfloor : ∀ v ∈ rho.honest,
      Block.Preceq F
        (Protocol.get_fg_root
          (actionStoreAt S rho v r).toHealing.toFG))
    (hpost : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hactive : ∀ w ∈ rho.honest,
      F ∈ Protocol.get_filtered_block_tree
        (healStoreAt S rho w (r + 1)).toFG)
    (hactiveDomain : ∀ w ∈ rho.honest,
      F ∈ PhaseGrades.filteredTree (relativeG2Read S rho (r + 1) w)) :
    NamedGradeFormsAt S rho (r + 1) F :=
  namedGradeFormsAt_succ_of_actionCarriersCover_and_next_active
    S adm hmajority (actionCarriersCover_of_fgRootFloor S rho hfloor)
    hpost hcut hactive hactiveDomain



end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms gammaNeg1_eq_domain_g2_succ
#print axioms relativePositive_of_cleanActionRead
#print axioms relativeOpposingNotHonest_of_cleanActionRead
#print axioms phaseGrade_of_honestPositiveSupport
#print axioms phaseGrade_of_gradeFormingMajority
#print axioms namedGradeFormsAt_of_honestPositiveSupport
#print axioms relativeG2Active_of_cleanActionRead
#print axioms relativeG2Support_of_cleanActionRead
#print axioms namedGradeFormsAt_of_cleanActionRead
#print axioms namedGradeFormsAt_succ_of_actionCarriersCover_and_next_active
#print axioms namedGradeFormsAt_succ_of_fgRootFloor
end DecoupledConsensusModel.Proofs.HealingSurface

end
