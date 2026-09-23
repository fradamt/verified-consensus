module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.HeightRegimeNamedBaseDeadline
public import DecoupledConsensusProofs.Protocol.Grades.SeedActionQ2
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryInitialSourceNamedHistory
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FGSafetySourceNamed

@[expose] public section

/-!
# Prepared frame producers after the recovery deadline

This leaf records the two prepared-read producers required by the SG safety
proof.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Internal.NamedRecoveryRead DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

/-- A finite family whose members are each comparable with one block has a
common floor. If some member is below the comparison block, the floor is a
shallowest such member. Otherwise, the comparison block is the floor. -/
theorem exists_common_floor_of_compatible_with
    (S : Setup V) (rho : Run V) (c : Round) (T : Block V)
    (hcompat : ∀ v ∈ rho.honest,
      Block.compatible (actionSGBlockAt S rho v c) T = true) :
    ∃ P : Block V,
      (∀ v ∈ rho.honest, Block.Preceq P (actionSGBlockAt S rho v c)) ∧
      ((∃ u ∈ rho.honest, P = actionSGBlockAt S rho u c) ∨ P = T) := by
  classical
  let below := rho.honest.filter fun v =>
    Block.preceq (actionSGBlockAt S rho v c) T
  by_cases hne : below.Nonempty
  · obtain ⟨u, hu, hmin⟩ := Finset.exists_min_image below
      (fun v => (actionSGBlockAt S rho v c).depth) hne
    have huHon : u ∈ rho.honest := (Finset.mem_filter.mp hu).1
    have huT : Block.Preceq (actionSGBlockAt S rho u c) T :=
      (Finset.mem_filter.mp hu).2
    refine ⟨actionSGBlockAt S rho u c, ?_, Or.inl ⟨u, huHon, rfl⟩⟩
    intro v hv
    have hvCases : Block.Preceq (actionSGBlockAt S rho v c) T ∨
        Block.Preceq T (actionSGBlockAt S rho v c) := by
      simpa only [Block.compatible, Bool.or_eq_true] using hcompat v hv
    rcases hvCases with hvT | hTv
    · have hvBelow : v ∈ below := Finset.mem_filter.mpr ⟨hv, hvT⟩
      have huv : Block.Preceq (actionSGBlockAt S rho u c)
          (actionSGBlockAt S rho v c) ∨
          Block.Preceq (actionSGBlockAt S rho v c)
            (actionSGBlockAt S rho u c) := Block.preceq_linear huT hvT
      rcases huv with huv | hvu
      · exact huv
      · exact AlignedRoundLemmas.preceq_of_compatible_of_depth_le
          (by simp only [Block.compatible, Bool.or_eq_true]; exact Or.inr hvu)
          (hmin v hvBelow)
    · exact Block.preceq_trans huT hTv
  · refine ⟨T, ?_, Or.inr rfl⟩
    intro v hv
    have hvCases : Block.Preceq (actionSGBlockAt S rho v c) T ∨
        Block.Preceq T (actionSGBlockAt S rho v c) := by
      simpa only [Block.compatible, Bool.or_eq_true] using hcompat v hv
    exact hvCases.resolve_left (fun hvT =>
      hne ⟨v, Finset.mem_filter.mpr ⟨hv, hvT⟩⟩)

/-- After the recovery deadline, every honest round carrier is present and
interpretable at every honest reader's next relative G2 read. -/
theorem relativeCarrierWindowAt_after_recovery_deadline
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {c : Round} (hc : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ c)
    (hhor : domain S.E S.hc (c + 1) .g2 ≤ rho.horizon) :
    RelativeCarrierWindowAt S rho c .g2 := by
  have hactionDomain : S.a c ≤ domain S.E S.hc (c + 1) .g2 :=
    NamedOutageClosure.action_le_domain S S.hc.R_ge_three
      (Nat.lt_succ_self c)
  have hsourceHor : S.a c ≤ rho.horizon := hactionDomain.trans hhor
  have hdeadlineHor :
      S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) ≤ rho.horizon :=
    ((action_strictMono S).monotone hc).trans hsourceHor
  obtain ⟨blocked, first, Tprev, hfirst, hbase⟩ :=
    exists_namedHeightRegimeBaseRun_before_fgSafetyProgressDeadline
      S adm hcom hbelow hrec hdelay hpost hdeadlineHor
  have hgst := gstLagged_le_Γ_neg1_of_gst_le_a S rGST hpost
  have hpostc : S.E.t_GST ≤ S.a c := by
    have hGSTdead :
        rGST ≤ fgSafetyProgressDeadline S rho rGST gap delayExtra := by
      unfold fgSafetyProgressDeadline
      exact (Nat.le_add_right rGST 1).trans
        (Nat.le_add_right (rGST + 1) _)
    exact hpost.trans ((action_strictMono S).monotone (hGSTdead.trans hc))
  have hdeadline : S.a c + S.E.Δ ≤ early S.E S.hc (c + 1) .g2 :=
    NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
      (Nat.lt_succ_self c)
  have horder : early S.E S.hc (c + 1) .g2 ≤
      domain S.E S.hc (c + 1) .g2 :=
    NamedOutageClosure.early_le_domain S (c + 1)
  have hcut : early S.E S.hc (c + 1) .g2 ≤ rho.horizon :=
    horder.trans hhor
  have hdeadlineRead :
      S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) ≤
        domain S.E S.hc (c + 1) .g2 :=
    ((action_strictMono S).monotone hc).trans hactionDomain
  have hreadNext : domain S.E S.hc (c + 1) .g2 ≤ S.a (c + 1) :=
    FrameForward.domain_le_a S (c + 1) .g2
  intro w hw u hu
  have huHon : u ∈ rho.honest :=
    ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u c).mp hu).1
  have hrootCompat :=
    hbase.fgRoot_compatible_actionSGBlock_at_read_after_deadline
      adm hcom hbelow hgst hfirst hc hsourceHor hdeadlineRead hhor hreadNext
        hw huHon
  have hFroot : Block.Preceq
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (c + 1) .g2) w).st.core.F
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w
          (domain S.E S.hc (c + 1) .g2)).toHealing.toFG) :=
    StoreFinality.finalized_preceq_fgRoot
      (Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        S rho (domain S.E S.hc (c + 1) .g2) w)
  have hcompat : Block.compatible
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (c + 1) .g2) w).st.core.F
      (actionSGBlockAt S rho u c) = true := by
    rcases (show Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S w
            (domain S.E S.hc (c + 1) .g2)).toHealing.toFG)
          (actionSGBlockAt S rho u c) ∨
        Block.Preceq (actionSGBlockAt S rho u c)
          (Protocol.get_fg_root
            (rho.storeBeforeTime S w
              (domain S.E S.hc (c + 1) .g2)).toHealing.toFG) by
      simpa only [Block.compatible, Bool.or_eq_true] using hrootCompat) with
      hrootCarrier | hcarrierRoot
    · simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inl (Block.preceq_trans hFroot hrootCarrier)
    · exact Block.compatible_of_preceq_common hFroot hcarrierRoot
  let a := actionAttestationAt S rho u c
  have hshape : a.val_index = u ∧ a.round = c ∧
      a.confirmed = some (actionSGBlockAt S rho u c).root := by
    simpa only [a] using actionAttestationAt_shape S rho u c
  have hemit : NamedRun.emits S rho u (Object.attest a) (S.a c) := by
    simpa only [a] using
      honest_emits_exact_actionAttestationAt S adm huHon c hsourceHor (by assumption)
  obtain ⟨i, hi, _, hhead⟩ :=
    Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
  dsimp at hhead
  obtain ⟨H, hH, hconfirmed⟩ := hhead
  have hbodySource : H ∈
      (NamedRun.stateBeforeTime S rho (S.a c) u).st.bodies := by
    have hi' : rho.events[i]? = some (.tick u (S.a c)) := by
      simpa only [hshape.2.1] using hi
    have hstate := NamedActionSources.action_read_index S rho
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed i u c hi'
    change H ∈ (NamedRun.stateBefore S rho i u).st.bodies at hH
    rw [← hstate]
    exact hH
  have hcarrierMem : actionSGBlockAt S rho u c ∈
      (NamedRun.stateBeforeTime S rho (S.a c) u).st.core.T :=
    actionSGBlockAt_mem_storeBeforeTime S rho u c
  obtain ⟨D, hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
      S rho (S.a c) u hcarrierMem
  obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted (S.a c)
  have hDprefix : D ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact hDbody
  have hHprefix : H ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact hbodySource
  have hDrun : RunBlock S rho D :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S huHon hDprefix
  have hHrun : RunBlock S rho H :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S huHon hHprefix
  have hroot : D.root = H.root := by
    rw [← Proofs.NamedWire.erase_root D, hDerase]
    exact Option.some.inj (hshape.2.2.symm.trans hconfirmed)
  have hDH : D = H :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective D H
      hDrun hHrun D H (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self H)) hroot
  have hHErase : H.erase = actionSGBlockAt S rho u c := by
    rw [← hDH, hDerase]
  have hk : c ∈ Protocol.latest_window S.hc.η_SG (c + 1) := by
    apply NamedOutageClosure.mem_latest_window
    · simpa only [Nat.add_sub_cancel] using
        (Nat.sub_le_sub_left S.hc.η_SG_ge_one (c + 1))
    · exact Nat.lt_succ_self c
  have hinput : Protocol.sgVote a.erase ∈
      DecoupledConsensusModel.Protocol.interpretedInputs
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (c + 1) .g2) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (c + 1) .g2) w).st.core.F
        S.hc.η_SG (c + 1) (early S.E S.hc (c + 1) .g2) u := by
    have hdeadline' : max (S.a a.round) S.E.t_GST + S.E.Δ ≤
        early S.E S.hc (c + 1) .g2 := by
      rw [max_eq_left (by simpa only [hshape.2.1] using hpostc)]
      simpa only [hshape.2.1] using hdeadline
    rcases (show Block.Preceq
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (c + 1) .g2) w).st.core.F
          (actionSGBlockAt S rho u c) ∨
        Block.Preceq (actionSGBlockAt S rho u c)
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (c + 1) .g2) w).st.core.F by
      simpa only [Block.compatible, Bool.or_eq_true] using hcompat) with
      hFCarrier | hcarrierF
    · exact action_vote_mem_interpretedInputs_after_gst_common_upper
        S adm.toNamedAdmissibleCore .g2 hk huHon hw
          ⟨hshape.1, hshape.2.1, hemit⟩ ⟨i, hi, hH, hconfirmed⟩
          (by rw [hHErase]; exact Block.preceq_self _) hFCarrier
          (by simpa only [hshape.2.1] using hpostc) hdeadline' horder hcut
    · exact action_vote_mem_interpretedInputs_after_gst_common_upper
        S adm.toNamedAdmissibleCore .g2 hk huHon hw
          ⟨hshape.1, hshape.2.1, hemit⟩ ⟨i, hi, hH, hconfirmed⟩
          (by simpa only [hHErase] using hcarrierF)
          (Block.preceq_self _)
          (by simpa only [hshape.2.1] using hpostc) hdeadline' horder hcut
  have hfind : Block.find?
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (c + 1) .g2) w).st.core.T
      (actionSGBlockAt S rho u c).root =
        some (actionSGBlockAt S rho u c) := by
    have hready := (Finset.mem_filter.mp hinput).2
    simp only [DecoupledConsensusModel.Protocol.bodyReady,
      NamedOutageClosure.sgVote_confirmed, hshape.2.2] at hready
    simp only [Protocol.Store.toHealing, Protocol.HealingStore.gradeView] at hready
    cases hfindY : Block.find?
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (c + 1) .g2) w).st.core.T
        (actionSGBlockAt S rho u c).root with
    | none => exact False.elim (by
        simp only [hfindY] at hready
        exact Bool.noConfusion hready)
    | some Y =>
      have hYmem := Proofs.HealingLemmas.find?_mem hfindY
      obtain ⟨Yn, hYerase, hYrun⟩ :=
        Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hw
          (domain S.E S.hc (c + 1) .g2) hYmem
      have hYHroot : Yn.root = H.root := by
        rw [← Proofs.NamedWire.erase_root Yn, hYerase,
          Proofs.HealingLemmas.find?_root hfindY, ← hHErase,
          Proofs.NamedWire.erase_root H]
      have hYH :=
        adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
          Yn H hYrun hHrun Yn H (Or.inl (Proofs.NamedAncestry.named_self Yn))
          (Or.inr (Proofs.NamedAncestry.named_self H)) hYHroot
      have hYeq : Y = actionSGBlockAt S rho u c := by
        rw [← hYerase, hYH, hHErase]
      simpa only [hYeq] using hfindY
  refine ⟨Protocol.sgVote a.erase, hinput, ?_, ?_, hfind⟩
  · simpa only [NamedOutageClosure.sgVote_round] using hshape.2.1
  · rw [NamedOutageClosure.sgVote_confirmed, hshape.2.2]

set_option maxHeartbeats 400000 in
private theorem p6_storeGrade_g2_of_relativeCarrierWindow_and_cover
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} (hq : 0 < q)
    (hpost : S.E.t_GST ≤ S.a (q - 1))
    (hhor : domain S.E S.hc q .g2 ≤ rho.horizon)
    (hforming : Internal.NamedOutageEntry.GradeFormingMajority S rho q)
    (hwindow : RelativeCarrierWindowAt S rho (q - 1) .g2)
    {P : Block V}
    (hcover : ∀ u ∈ rho.honest,
      Block.Preceq P (actionSGBlockAt S rho u (q - 1)))
    {w : V} (hw : w ∈ rho.honest) :
    storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc q .g2) w).st q .g2 P = true := by
  have hpred : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hq)
  let n := NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g2) w
  let gv := n.st.core.toHealing.gradeView
  let F := n.st.core.F
  let ea := early S.E S.hc q .g2
  let la := late S.E S.hc q .g2
  have hwindowAt : ∀ u ∈ Internal.NamedOutageEntry.honestRoundVoters S rho (q - 1),
      ∃ y ∈ DecoupledConsensusModel.Protocol.interpretedInputs gv F S.hc.η_SG q ea u,
        y.round = q - 1 ∧
        y.confirmed = some (actionSGBlockAt S rho u (q - 1)).root ∧
        Block.find? n.st.core.T (actionSGBlockAt S rho u (q - 1)).root =
          some (actionSGBlockAt S rho u (q - 1)) := by
    intro u hu
    have h := hwindow w hw u hu
    change ∃ y ∈ DecoupledConsensusModel.Protocol.interpretedInputs
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (q - 1 + 1) .g2) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (q - 1 + 1) .g2) w).st.core.F
        S.hc.η_SG (q - 1 + 1) (early S.E S.hc (q - 1 + 1) .g2) u,
      y.round = q - 1 ∧
        y.confirmed = some (actionSGBlockAt S rho u (q - 1)).root ∧
        Block.find? (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (q - 1 + 1) .g2) w).st.core.T
          (actionSGBlockAt S rho u (q - 1)).root =
            some (actionSGBlockAt S rho u (q - 1)) at h
    simpa only [n, gv, F, ea, hpred] using h
  have hpositive : Internal.NamedOutageEntry.honestRoundVoters S rho (q - 1) ⊆
      Finset.univ.filter fun u =>
        DecoupledConsensusModel.Protocol.positive gv F S.hc.η_SG q ea la u P = true := by
    intro u hu
    have huHon := ((Proofs.NamedOutageInputs.honestRoundVoters_iff
      S rho u (q - 1)).mp hu).1
    obtain ⟨y, hy, hyround, hyconfirmed, hyfind⟩ := hwindowAt u hu
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ u, ?_⟩
    simp only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq]
    refine ⟨DecoupledConsensusModel.Protocol.token y, ?_, ?_, ?_, ?_, ?_⟩
    · exact Finset.mem_image_of_mem DecoupledConsensusModel.Protocol.token hy
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hzraw := (Finset.mem_filter.mp hz).1
      change z ∈ DecoupledConsensusModel.Protocol.rawInputs
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc q .g2) w).st.core.toHealing.gradeView
        S.hc.η_SG q (early S.E S.hc q .g2) u at hzraw
      have hzraw' : z ∈ DecoupledConsensusModel.Protocol.rawInputs
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc q .g2) w).st.core.toHealing.gradeView
          S.hc.η_SG (q - 1 + 1) (early S.E S.hc q .g2) u := by
        simpa only [hpred] using hzraw
      obtain ⟨_, _, _, _, _, _, _, _, hzupper⟩ :=
        NamedOutageClosure.honest_rawInput_is_own_round_vote S rho
          adm.toNamedAdmissibleCore (domain S.E S.hc q .g2)
          (early S.E S.hc q .g2) w hw huHon (r := q - 1) hzraw'
      simpa only [DecoupledConsensusModel.Protocol.token, hyround] using hzupper
    · change Protocol.head_covers n.st.core.T P y.confirmed = true
      rw [hyconfirmed]
      simp only [Protocol.head_covers]
      rw [show Block.find? n.st.core.T
          (actionSGBlockAt S rho u (q - 1)).root =
            some (actionSGBlockAt S rho u (q - 1)) by
        simpa only [n, hpred] using hyfind]
      exact hcover u huHon
    · have hclean := NamedOutageClosure.honest_rawView_clean S rho
        adm.toNamedAdmissibleCore (domain S.E S.hc q .g2) la
        w hw huHon (q - 1) (DecoupledConsensusModel.Protocol.token y).round
      rw [hpred] at hclean
      exact hclean
    · intro x hx hlt
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hzraw := (Finset.mem_filter.mp hz).1
      change z ∈ DecoupledConsensusModel.Protocol.rawInputs
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc q .g2) w).st.core.toHealing.gradeView
        S.hc.η_SG q (late S.E S.hc q .g2) u at hzraw
      have hzraw' : z ∈ DecoupledConsensusModel.Protocol.rawInputs
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc q .g2) w).st.core.toHealing.gradeView
          S.hc.η_SG (q - 1 + 1) (late S.E S.hc q .g2) u := by
        simpa only [hpred] using hzraw
      obtain ⟨_, _, _, _, _, _, _, _, hzupper⟩ :=
        NamedOutageClosure.honest_rawInput_is_own_round_vote S rho
          adm.toNamedAdmissibleCore (domain S.E S.hc q .g2)
          (late S.E S.hc q .g2) w hw huHon (r := q - 1) hzraw'
      exfalso
      exact (Nat.not_lt_of_ge hzupper) (by
        simpa only [DecoupledConsensusModel.Protocol.token, hyround] using hlt)
  have hopposing : (Finset.univ.filter fun u =>
      DecoupledConsensusModel.Protocol.opposing gv F S.hc.η_SG q ea la u P = true) ⊆
      (Finset.univ \ rho.honest) ∪
        Internal.NamedOutageEntry.staleHistoricalVoters S rho q := by
    intro u hu
    by_cases huHon : u ∈ rho.honest
    · have huVoter : u ∈ Internal.NamedOutageEntry.honestRoundVoters S rho (q - 1) := by
        apply (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u (q - 1)).mpr
        have hprevHor : S.a (q - 1) ≤ rho.horizon :=
          (NamedOutageClosure.action_le_domain S S.hc.R_ge_three
            (Nat.sub_lt hq (by decide))).trans hhor
        exact ⟨huHon, actionAttestationAt S rho u (q - 1),
          (actionAttestationAt_shape S rho u (q - 1)).1,
          (actionAttestationAt_shape S rho u (q - 1)).2.1,
          honest_emits_exact_actionAttestationAt S adm huHon (q - 1) hprevHor hpost⟩
      have hopp := (Finset.mem_filter.mp hu).2
      simp only [DecoupledConsensusModel.Protocol.opposing, decide_eq_true_eq] at hopp
      rcases hopp with ⟨x, hx, hdom, hnotcover⟩ |
        ⟨x, hx, y, hy, _, hround, hkey⟩
      · simp only [DecoupledConsensusModel.Protocol.readyView, Finset.mem_image] at hx
        obtain ⟨z, hz, rfl⟩ := hx
        have hzraw := (Finset.mem_filter.mp hz).1
        change z ∈ DecoupledConsensusModel.Protocol.rawInputs
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc q .g2) w).st.core.toHealing.gradeView
          S.hc.η_SG q (late S.E S.hc q .g2) u at hzraw
        have hzraw' : z ∈ DecoupledConsensusModel.Protocol.rawInputs
            (NamedRun.stateBeforeTime S rho
              (domain S.E S.hc q .g2) w).st.core.toHealing.gradeView
            S.hc.η_SG (q - 1 + 1) (late S.E S.hc q .g2) u := by
          simpa only [hpred] using hzraw
        obtain ⟨a, haround, _, hemit, _, hconfirmed, _, _, hzupper⟩ :=
          NamedOutageClosure.honest_rawInput_is_own_round_vote S rho
            adm.toNamedAdmissibleCore (domain S.E S.hc q .g2)
            (late S.E S.hc q .g2) w hw huHon (r := q - 1) hzraw'
        obtain ⟨earlyVote, hearly, hearlyRound, _, hfind⟩ :=
          hwindowAt u huVoter
        have hsourceLe : q - 1 ≤ z.round := by
          simpa only [DecoupledConsensusModel.Protocol.token, hearlyRound] using
            hdom (DecoupledConsensusModel.Protocol.token earlyVote)
              (Finset.mem_image_of_mem DecoupledConsensusModel.Protocol.token hearly)
        have hzround : z.round = q - 1 :=
          Nat.le_antisymm hzupper hsourceLe
        have har : a.round = q - 1 := haround.trans hzround
        have hem : NamedRun.emits S rho u (.attest a) (S.a (q - 1)) := by
          simpa only [hzround] using hemit
        have hconfirmedAction := NamedOutageClosure.honest_emitted_round_confirmed
          S rho adm.toNamedAdmissibleCore u huHon (q - 1)
          ((NamedOutageClosure.action_le_domain S S.hc.R_ge_three
            (Nat.sub_lt hq (by decide))).trans hhor) har hem
        exact False.elim (hnotcover (by
          change Protocol.head_covers n.st.core.T P z.confirmed = true
          rw [hconfirmed, hconfirmedAction]
          simp only [Protocol.head_covers]
          rw [show Block.find? n.st.core.T
              (actionSGBlockAt S rho u (q - 1)).root =
                some (actionSGBlockAt S rho u (q - 1)) by
            simpa only [n, hpred] using hfind]
          exact hcover u huHon))
      · have hclean0 := NamedOutageClosure.honest_rawView_clean S rho
          adm.toNamedAdmissibleCore (domain S.E S.hc q .g2) la
          w hw huHon (q - 1) 0
        rw [hpred] at hclean0
        exact False.elim (hkey
          (hclean0 x hx y hy (Nat.zero_le _) hround))
    · exact Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, huHon⟩)
  change DecoupledConsensusModel.Protocol.gradeBool S.E gv F S.hc.η_SG q ea la P = true
  exact phaseGrade_of_gradeFormingMajority S rho q gv F P ea la
    hforming hpositive hopposing

/-- Every honest action immediately after a post-deadline round has a
nonempty raw relative G2 frame entry. -/
theorem nodeRawG2_at_action_after_recovery_deadline
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {c : Round} (hc : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ c)
    (hhor : S.a (c + 1) ≤ rho.horizon) :
    ∀ v ∈ rho.honest,
      Internal.PhaseGrades.nodeRawG2 S
        (actionReadAt S rho v (c + 1)) (c + 1) := by
  have hdeadlineHor :
      S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) ≤ rho.horizon :=
    ((action_strictMono S).monotone
      (hc.trans (Nat.le_succ c))).trans hhor
  obtain ⟨blocked, first, Tprev, hfirst, hbase⟩ :=
    exists_namedHeightRegimeBaseRun_before_fgSafetyProgressDeadline
      S adm hcom hbelow hrec hdelay hpost hdeadlineHor
  have hgst := gstLagged_le_Γ_neg1_of_gst_le_a S rGST hpost
  obtain ⟨i, a, ta, Cfg, T, hreg, haround⟩ :=
    hbase.exists_regime_before_deadline adm hbelow hgst hfirst
  have hac : a.round ≤ c := haround.trans hc
  have hpostc : S.E.t_GST ≤ S.a c :=
    hreg.postPrev.trans (Assembly.a_mono S
      ((Nat.sub_le a.round 1).trans hac))
  have hchor : S.a c ≤ rho.horizon :=
    ((action_strictMono S).monotone (Nat.le_succ c)).trans hhor
  have hhistory : HonestSGEmissionsCompatibleAtRound S rho c T.erase := by
    rcases eq_or_lt_of_le hac with rfl | hlt
    · exact hreg.seed.sgEmissionsCompatible_of_source_of_frame_named
        adm hcom hbelow hreg.crossing hreg.frame hreg.c0le
          hreg.ready hreg.postPrev
    · exact ((hreg.laterHistory_main adm hcom hbelow
        (Nat.succ_le_of_lt hlt)).2 hchor).1
  have hcompat : ∀ v ∈ rho.honest,
      Block.compatible (actionSGBlockAt S rho v c) T.erase = true := by
    intro v hv
    exact hhistory v hv
      (honest_emits_exact_actionAttestationAt S adm hv c hchor (by assumption))
  obtain ⟨P0, hvotes, -⟩ :=
    exists_common_floor_of_compatible_with S rho c T.erase hcompat
  have hdomainHor : domain S.E S.hc (c + 1) .g2 ≤ rho.horizon :=
    (FrameForward.domain_le_a S (c + 1) .g2).trans hhor
  have hwindow : RelativeCarrierWindowAt S rho c .g2 :=
    relativeCarrierWindowAt_after_recovery_deadline
      S adm hcom hbelow hrec hdelay hpost hc hdomainHor
  have hforming : Internal.NamedOutageEntry.GradeFormingMajority S rho (c + 1) :=
    gradeFormingMajority_of_admissible_belowOneThird
      S adm hbelow (Nat.succ_pos c) hdomainHor (by assumption)
  intro v hv
  have hgrade := p6_storeGrade_g2_of_relativeCarrierWindow_and_cover
    S adm (Nat.succ_pos c)
      (by simpa only [Nat.add_sub_cancel] using hpostc)
      hdomainHor hforming
      (by simpa only [Nat.add_sub_cancel] using hwindow)
      (by simpa only [Nat.add_sub_cancel] using hvotes) hv
  obtain ⟨u, hu⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
  have huVoter : u ∈ Internal.NamedOutageEntry.honestRoundVoters S rho c := by
    apply (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u c).mpr
    exact ⟨hu, actionAttestationAt S rho u c,
      (actionAttestationAt_shape S rho u c).1,
      (actionAttestationAt_shape S rho u c).2.1,
      honest_emits_exact_actionAttestationAt S adm hu c hchor (by assumption)⟩
  obtain ⟨y, hy, hyround, hyconfirmed, hyfind⟩ := hwindow v hv u huVoter
  have hcarrierMem : actionSGBlockAt S rho u c ∈
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (c + 1) .g2) v).st.core.T :=
    Proofs.HealingLemmas.find?_mem hyfind
  have hclosed := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime
    S rho (domain S.E S.hc (c + 1) .g2) v
  have hPmem : P0 ∈
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (c + 1) .g2) v).st.core.T :=
    Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hclosed).2
      P0 (actionSGBlockAt S rho u c) hcarrierMem (hvotes u hu)
  obtain ⟨raw, hfreeze, -⟩ := NamedOutageClosure.q10_freeze_of_graded S.E
    (NamedRun.stateBeforeTime S rho
      (domain S.E S.hc (c + 1) .g2) v).st.core.toHealing.gradeView
    (NamedRun.stateBeforeTime S rho
      (domain S.E S.hc (c + 1) .g2) v).st.core.F
    S.hc.η_SG (c + 1)
    (NamedOutageClosure.q10_early_le_late S (c + 1) .g2)
    hPmem (by simpa only [storeGrade] using hgrade)
  have hstoreRoot : PhaseGrades.storeRoot S.E S.hc
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (c + 1) .g2) v).st (c + 1) .g2 = some raw := by
    simpa only [PhaseGrades.storeRoot, PhaseGrades.phaseRoot] using hfreeze
  show ((DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho v (c + 1)).cache
    (actionReadAt S rho v (c + 1)).st.core.toHealing (c + 1)).g2.bind id).isSome = true
  rw [actionFrame_g2 S adm.toNamedAdmissibleCore hv
      (Nat.succ_pos c) hhor,
    hstoreRoot]
  rfl

/-- After the extra boundary round, a selected prepared Q2 is either below
the reader's FG root or remains active at the interior vote-duty read. -/
theorem actionQ2_preceq_fgRoot_or_activeAtVoteDuty_after_deadline
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {c : Round}
    (hc : fgSafetyProgressDeadline S rho rGST gap delayExtra + 1 ≤ c)
    (ready : GradeRoundReady S rho c) (hchor : S.a c ≤ rho.horizon)
    {p : V} (hp : p ∈ rho.honest) {Q : Block V}
    (hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho p c) c = some Q)
    {d : Slot} (hround : S.hc.round_of d = c)
    (hdlo : S.hc.opening_slot c + 1 ≤ d)
    (hvoteHor : Protocol.vote_time S.E d ≤ rho.horizon)
    (hnext : Protocol.vote_time S.E d ≤ S.a (c + 1))
    {w : V} (hw : w ∈ rho.honest) :
    Block.Preceq Q
        (Protocol.get_fg_root
          (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.toFG) ∨
      Q ∈ PhaseGrades.filteredTree
        (Internal.NamedRecoveryRead.voteDutyRead S rho w d) := by
  have hdead : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ c :=
    (Nat.le_succ _).trans hc
  have hread : S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) ≤
      Protocol.vote_time S.E d := by
    exact le_trans
      (le_trans (a_le_Γ_neg1_succ S.hc S.E.Δ_pos _)
        (Γ_neg1_mono S.hc S.E.Δ_pos hc))
      (le_trans (le_of_lt
        (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos c))
        (Γ_0_le_vote_time_of_round_eq S hround))
  have hcut : S.hc.Γ_0 S.E.Δ c ≤ Protocol.vote_time S.E d :=
    Γ_0_le_vote_time_of_round_eq S hround
  have hQtree := actionQ2_mem_filteredTree S rho p c hQ
  have hQcore : Q ∈ (actionReadAt S rho p c).st.core.T :=
    mem_T_of_mem_filteredTree hQtree
  have hcoh := (actionRead_invariant S rho p c).1.1.1
  change Q ∈ (actionStoreAt S rho p c).st.core.T at hQcore
  rw [hcoh] at hQcore
  obtain ⟨Qn, hQnbody, hQnerase⟩ := Finset.mem_image.mp hQcore
  have hQnamed : PhaseGrades.nodeQ2 S (actionReadAt S rho p c) c =
      some Qn.erase := by
    simpa only [hQnerase] using hQ
  have hsplit := selectedG2_filteredMem_or_preceq_root_after_GST_ancestor
    S adm hcom hbelow hrec hdelay hpost hdead ready hchor hread hcut
      hvoteHor hnext hw hp hQnamed
  rcases hsplit with hactive | hroot
  · exact Or.inr (by
      simpa only [hQnerase, PhaseGrades.filteredTree,
        Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock, Run.storeBeforeTime] using hactive)
  · exact Or.inl (by
      simpa only [hQnerase, Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock, Run.storeBeforeTime] using hroot)

#print axioms exists_common_floor_of_compatible_with
#print axioms relativeCarrierWindowAt_after_recovery_deadline
#print axioms nodeRawG2_at_action_after_recovery_deadline
#print axioms actionQ2_preceq_fgRoot_or_activeAtVoteDuty_after_deadline

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
