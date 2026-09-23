module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Store.WeakSGHistory
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGCompatibleHistory
public import DecoupledConsensusProofs.Protocol.Grades.RelativeOneChain
public import DecoupledConsensusProofs.Protocol.Grades.WeakGenesis
public import DecoupledConsensusProofs.Protocol.Grades.Q31_actionSGBlock_tiers
public import DecoupledConsensusProofs.Protocol.Grades.RoundVoterTransportTwoCutoff
public import DecoupledConsensusProofs.Protocol.Grades.RelativeSupporter

@[expose] public section

/-!
# Action induction with an independent history cutoff

The history starts at base and its bootstrap ends at cut. The condition
base <= cut - eta gives the retained SG window. It holds both after a
full expiry interval and at genesis, where base = cut = 0. Round zero
uses its exact initial outputs and has no window-majority premise.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakJoint

open Internal Execution Protocol Proofs.Optimistic Proofs.HealingLemmas
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The regime-neutral grade-formation result used by the action induction. -/
structure ActionGradeFormationAt
    (S : Setup V) (rho : Run V) (r : Round) : Prop where
  action : ∀ w ∈ rho.honest,
    NamedRun.emits S rho w
      (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
    Block.Preceq (actionSGBlockAt S rho w r)
        (actionStoreAt S rho w r).live_confirmed ∨
      actionSGBlockAt S rho w r =
        Protocol.get_fg_root (actionStoreAt S rho w r).toHealing.toFG ∨
      ∃ k ∈ Protocol.latest_window S.hc.η_SG r, ∃ u ∈ rho.honest,
        NamedRun.emits S rho u
            (Object.attest (actionAttestationAt S rho u k)) (S.a k) ∧
          Block.Preceq (actionSGBlockAt S rho w r)
            (actionSGBlockAt S rho u k)
  witness : ∀ w ∈ rho.honest, ∀ T,
    fgConfirmationWitness S (actionStoreAt S rho w r) = some T →
      Block.Preceq T (actionStoreAt S rho w r).live_confirmed ∨
        ∃ k ∈ Protocol.latest_window S.hc.η_SG r, ∃ u ∈ rho.honest,
          NamedRun.emits S rho u
              (Object.attest (actionAttestationAt S rho u k)) (S.a k) ∧
            Block.Preceq T (actionSGBlockAt S rho u k)


private theorem nodeQ2_preceq_honestWindowCarrier
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) {r : Round} (hr : 0 < r)
    (hgrade : ∀ p, domain S.E S.hc r p ≤ rho.horizon →
      RelativeGradeCarrierAt S rho r p)
    {Q : Block V} (hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho w r) r = some Q) :
    ∃ k ∈ Protocol.latest_window S.hc.η_SG r, ∃ u ∈ rho.honest,
      NamedRun.emits S rho u
          (Object.attest (actionAttestationAt S rho u k)) (S.a k) ∧
        Block.Preceq Q (actionSGBlockAt S rho u k) := by
  let i := strictEventIndex rho (S.a r)
  have hread := stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedScheduleWellFormed (S.a r)
  have hreadw := congrFun hread w
  have hQ' := hQ
  simp only [PhaseGrades.nodeQ2, PhaseGrades.nodeRead,
    NamedProfile.gradeContract, DecoupledConsensusModel.Protocol.frameContract] at hQ'
  unfold actionReadAt NamedActionReads.actionReadAt at hQ'
  rw [hreadw] at hQ'
  obtain ⟨j, raw, -, hj, hfreeze, hQraw⟩ :=
    NamedOutageHistory.JointHistoryProducersTime.q2_capture_at_action_read
      S rho i w r hQ'
  have hrawGrade : DecoupledConsensusModel.Protocol.gradeBool S.E
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc r .g2) w).st.core.F
      S.hc.η_SG r (early S.E S.hc r .g2) (late S.E S.hc r .g2) raw = true := by
    have hgrade' : DecoupledConsensusModel.Protocol.gradeBool S.E
        (NamedRun.stateBefore S rho j w).st.core.toHealing.gradeView
        (NamedRun.stateBefore S rho j w).st.core.F S.hc.η_SG r
        (early S.E S.hc r .g2) (late S.E S.hc r .g2) raw = true :=
      (Finset.mem_filter.mp
        (Proofs.Engine.deepest?_mem (by simpa only [DecoupledConsensusModel.Protocol.freezeRoot]
          using hfreeze))).2
    have hjState := Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
      S adm.toNamedScheduleWellFormed hj
    simpa only [← hjState] using hgrade'
  have hdomainHor : domain S.E S.hc r .g2 ≤ rho.horizon := by
    have h := adm.toNamedScheduleWellFormed.in_horizon
      (.tick w (domain S.E S.hc r .g2)) (List.mem_of_getElem? hj)
    simpa only [NamedEvent.time] using h.2
  obtain ⟨k, hk, u, hu, hemit, hpre⟩ :=
    hgrade .g2 hdomainHor w hw raw hrawGrade
  exact ⟨k, hk, u, hu, hemit, Block.preceq_trans hQraw hpre⟩

/-- At GST zero, a protected action history makes every awake-window vote an
interpreted relative-grade input. The common upper bound supplies the
`bodyReady` compatibility check at each phase read. -/
theorem relativeGradeCarrierAt_of_awakeWindowHistory_gstZero
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hgst : S.E.t_GST = 0) {base r : Round} {D : Block V} (hr : 0 < r)
    (hspan : base ≤ r - S.hc.η_SG)
    (hawake : AwakeWindowMajority S.E (fun v => (S.node v).awake)
      rho.honest S.hc.η_SG r)
    (hsg : ∀ k, base ≤ k → k < r → ∀ u ∈ rho.honest,
      NamedRun.emits S rho u
        (Object.attest (actionAttestationAt S rho u k)) (S.a k) →
      Block.Preceq (actionSGBlockAt S rho u k) D)
    (hroots : ∀ w ∈ rho.honest,
      Block.Preceq
        (Protocol.get_fg_root
          (actionStoreAt S rho w r).st.core.toHealing.toFG) D)
    (p : Phase) (hhor : domain S.E S.hc r p ≤ rho.horizon) :
    RelativeGradeCarrierAt S rho r p := by
  refine relativeGradeCarrierAt_of_awakeWindowMajority S adm hr hawake ?_
  intro w hw u hu k hk huk
  have hklt : k < r := mem_latestWindow_lt hk
  have hkbase : base ≤ k :=
    hspan.trans (WeakSG.mem_latestWindow_lower_bound hk)
  have hdeadlineG2 : S.a k + S.E.Δ ≤ early S.E S.hc r .g2 :=
    NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three hklt
  have hG2Phase : early S.E S.hc r .g2 ≤ early S.E S.hc r p := by
    cases p <;>
      simp only [early, Phase.earlyOffset] <;>
      linarith [S.E.Δ_pos]
  have hdeadline : S.a k + S.E.Δ ≤ early S.E S.hc r p :=
    hdeadlineG2.trans hG2Phase
  have hearlyDomain : early S.E S.hc r p ≤ domain S.E S.hc r p := by
    cases p <;>
      simp only [early, domain, Phase.earlyOffset, Phase.domainOffset] <;>
      linarith [S.E.Δ_pos]
  have hactionHor : S.a k ≤ rho.horizon :=
    (Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
      (hdeadline.trans (hearlyDomain.trans hhor))
  have hemit := honest_emits_exact_actionAttestationAt_of_awake
    S adm.toNamedScheduleWellFormed hu k huk hactionHor
  have hvoter : u ∈ Internal.NamedOutageEntry.honestRoundVoters S rho k := by
    apply (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u k).mpr
    refine ⟨hu, actionAttestationAt S rho u k, ?_, ?_, hemit⟩
    · exact (actionAttestationAt_shape S rho u k).1
    · exact (actionAttestationAt_shape S rho u k).2.1
  have hFmono : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) w).st.core.F
      (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.F :=
    NamedOutageClosure.incl_strict_F_mono S rho
      adm.toNamedScheduleWellFormed w (FrameForward.domain_le_a S r p)
  have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
    S rho (S.a r) w
  have hFroot : Block.Preceq
      (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.F
      (Protocol.get_fg_root
        (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.toHealing.toFG) :=
    Proofs.Records.preceq_get_fg_root_of_F
      (st := (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.toHealing.toFG) hFJ
  have hrootD : Block.Preceq
      (Protocol.get_fg_root
        (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.toHealing.toFG) D := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedDuties.update_confirmation_with,
      Protocol.update_confirmation_with,
      Protocol.NamedStore.setClock] using hroots w hw
  have hFD := Block.preceq_trans hFmono (Block.preceq_trans hFroot hrootD)
  have hcarrierD := hsg k hkbase hklt u hu hemit
  have hcompat : Block.compatible
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) w).st.core.F
      (actionSGBlockAt S rho u k) = true :=
    Block.compatible_of_preceq_common hFD hcarrierD
  have hpostEarly : S.E.t_GST ≤ early S.E S.hc r .g2 := by
    rw [hgst]
    exact (Proofs.HealingLemmas.a_nonneg S 0).trans
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
        (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three hr))
  exact NamedOutageClosure.honestRoundVote_interpreted_at_reader_of_twoCutoff_compatible
    S rho adm hgst
      (twoCutoffDelivery_of_core S adm hpostEarly)
      r k p hk w hw hhor hdeadline hvoter hcompat

/-- At a prepared phase-domain read, awake-window participation and a healthy
delivery cap supply the exact relative-grade carrier token. The action and FG
history are passed as the existing common upper block; delivery supplies the
SG row and body at the reader. -/
theorem relativeCarrierWindowAt_of_awakeWindowHistory_of_delivery
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {cap : Time} (hdelivery : NamedHealthyPrefixDelivery S rho cap)
    (hcapHor : cap ≤ rho.horizon)
    {base r : Round} {D : Block V} (_hr : 0 < r)
    (hspan : base ≤ r - S.hc.η_SG)
    (_hawake : AwakeWindowMajority S.E (fun v => (S.node v).awake)
      rho.honest S.hc.η_SG r)
    (hsg : ∀ k, base ≤ k → k < r → ∀ u ∈ rho.honest,
      NamedRun.emits S rho u
        (Object.attest (actionAttestationAt S rho u k)) (S.a k) →
      Block.Preceq (actionSGBlockAt S rho u k) D)
    (hroots : ∀ w ∈ rho.honest,
      Block.Preceq
        (Protocol.get_fg_root
          (actionStoreAt S rho w r).st.core.toHealing.toFG) D)
    (p : Phase) (hcap : domain S.E S.hc r p ≤ cap) :
    ∀ w ∈ rho.honest, ∀ u ∈ rho.honest,
      ∀ k ∈ Protocol.latest_window S.hc.η_SG r,
      (S.node u).awake k = true →
      ∃ y ∈ interpretedInputs
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc r p) w).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc r p) w).st.core.F
          S.hc.η_SG r (early S.E S.hc r p) u,
        y.round = k ∧
        y.confirmed = some (actionSGBlockAt S rho u k).root ∧
        Block.find?
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) w).st.core.T
          (actionSGBlockAt S rho u k).root =
            some (actionSGBlockAt S rho u k) := by
  intro w hw u hu k hk huk
  have hklt : k < r := mem_latestWindow_lt hk
  have hkbase : base ≤ k :=
    hspan.trans (WeakSG.mem_latestWindow_lower_bound hk)
  have hdeadlineG2 : S.a k + S.E.Δ ≤ early S.E S.hc r .g2 :=
    NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three hklt
  have hG2Phase : early S.E S.hc r .g2 ≤ early S.E S.hc r p := by
    cases p <;>
      simp only [early, Phase.earlyOffset] <;>
      linarith [S.E.Δ_pos]
  have hdeadline : S.a k + S.E.Δ ≤ early S.E S.hc r p :=
    hdeadlineG2.trans hG2Phase
  have hearlyDomain : early S.E S.hc r p ≤ domain S.E S.hc r p := by
    cases p <;>
      simp only [early, domain, Phase.earlyOffset, Phase.domainOffset] <;>
      linarith [S.E.Δ_pos]
  have hactionHor : S.a k ≤ rho.horizon :=
    (Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
      (hdeadline.trans (hearlyDomain.trans (hcap.trans hcapHor)))
  have hemit := honest_emits_exact_actionAttestationAt_of_awake
    S adm.toNamedScheduleWellFormed hu k huk hactionHor
  obtain ⟨i, hi, _, hbody⟩ := Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
  dsimp at hbody
  obtain ⟨K, hKstaged, haK⟩ := hbody
  have hKindex : K ∈ (NamedRun.stateBefore S rho i u).st.bodies := by
    change K ∈ (NamedRun.stateBefore S rho i u).st.bodies at hKstaged
    exact hKstaged
  have hstate := NamedActionSources.action_read_index S rho
    adm.toNamedScheduleWellFormed i u k hi
  have hKsource : K ∈
      (NamedRun.stateBeforeTime S rho (S.a k) u).st.bodies := by
    rw [← hstate]
    exact hKindex
  have hKrun : RunBlock S rho K :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hu hKindex
  have hcarrierMem : actionSGBlockAt S rho u k ∈
      (NamedRun.stateBeforeTime S rho (S.a k) u).st.core.T := by
    exact actionSGBlockAt_mem_storeBeforeTime S rho u k
  obtain ⟨D', hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (S.a k) u hcarrierMem
  obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedScheduleWellFormed.sorted (S.a k)
  have hDprefix : D' ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact hDbody
  have hKprefix : K ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact hKsource
  have hDrun : RunBlock S rho D' :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hu hDprefix
  have hKrun' : RunBlock S rho K :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hu hKprefix
  have hDKroot : D'.root = K.root := by
    rw [← Proofs.NamedWire.erase_root D', hDerase]
    exact Option.some.inj ((actionAttestationAt_shape S rho u k).2.2.symm.trans haK)
  have hDK : D' = K :=
    adm.toNamedRootCollisionFree.root_injective D' K hDrun hKrun' D' K
      (Or.inl (Proofs.NamedAncestry.named_self D'))
      (Or.inr (Proofs.NamedAncestry.named_self K)) hDKroot
  have hHErase : K.erase = actionSGBlockAt S rho u k := by
    rw [← hDK, hDerase]
  have hFmono : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) w).st.core.F
      (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.F :=
    NamedOutageClosure.incl_strict_F_mono S rho
      adm.toNamedScheduleWellFormed w (FrameForward.domain_le_a S r p)
  have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
    S rho (S.a r) w
  have hFroot : Block.Preceq
      (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.F
      (Protocol.get_fg_root
        (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.toHealing.toFG) :=
    Proofs.Records.preceq_get_fg_root_of_F
      (st := (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.toHealing.toFG)
      (by simpa only [Protocol.Store.toHealing] using hFJ)
  have hrootD : Block.Preceq
      (Protocol.get_fg_root
        (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.toHealing.toFG) D := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedDuties.update_confirmation_with,
      Protocol.update_confirmation_with,
      Protocol.NamedStore.setClock] using hroots w hw
  have hFD := Block.preceq_trans hFmono (Block.preceq_trans hFroot hrootD)
  have hcarrierD := hsg k hkbase hklt u hu hemit
  have hinput := interpretedInputs_nonempty_of_honest_window_vote_of_delivery_common_upper
    S adm p hdelivery hk (v := u) (w := w)
      (t := domain S.E S.hc r p) (r := r) (k := k) hu hw
      (hvote := by
        refine ⟨(actionAttestationAt_shape S rho u k).1,
          (actionAttestationAt_shape S rho u k).2.1, hemit⟩)
      (hhead := ⟨i, hi, hKstaged, haK⟩)
      (hHC := by
        rw [hHErase]
        exact hcarrierD) (hFC := hFD)
      (by simpa only [actionAttestationAt_shape] using hdeadline)
      hearlyDomain (hearlyDomain.trans hcap)
  obtain ⟨y, hy, hyround, hyconfirmed, hyfind⟩ := hinput
  have hKroot : K.root = (actionSGBlockAt S rho u k).root := by
    rw [← hDK, ← Proofs.NamedWire.erase_root D', hDerase]
  refine ⟨y, ?_, hyround, ?_, ?_⟩
  · simpa only [hHErase] using hy
  · simpa only [hHErase] using hyconfirmed
  · rw [hHErase, hKroot] at hyfind
    exact hyfind

theorem relativeCarrierWindowAt_of_awakeWindowHistory_w
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {lo cap : Time} (_hdelivery : NamedHealthyWindowDelivery S rho lo cap)
    (hgstLo : S.E.t_GST ≤ lo)
    (hcapHor : cap ≤ rho.horizon)
    {base r : Round} {D : Block V} (_hr : 0 < r)
    (hspan : base ≤ r - S.hc.η_SG)
    (hsendLo : ∀ k, base ≤ k → k < r → lo ≤ S.a k)
    (_hawake : AwakeWindowMajority S.E (fun v => (S.node v).awake)
      rho.honest S.hc.η_SG r)
    (hsg : ∀ k, base ≤ k → k < r → ∀ u ∈ rho.honest,
      NamedRun.emits S rho u
        (Object.attest (actionAttestationAt S rho u k)) (S.a k) →
      Block.Preceq (actionSGBlockAt S rho u k) D)
    (hroots : ∀ w ∈ rho.honest,
      Block.Preceq
        (Protocol.get_fg_root
          (actionStoreAt S rho w r).st.core.toHealing.toFG) D)
    (p : Phase) (hcap : domain S.E S.hc r p ≤ cap) :
    ∀ w ∈ rho.honest, ∀ u ∈ rho.honest,
      ∀ k ∈ Protocol.latest_window S.hc.η_SG r,
      (S.node u).awake k = true →
      ∃ y ∈ interpretedInputs
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc r p) w).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc r p) w).st.core.F
          S.hc.η_SG r (early S.E S.hc r p) u,
        y.round = k ∧
        y.confirmed = some (actionSGBlockAt S rho u k).root ∧
        Block.find?
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) w).st.core.T
          (actionSGBlockAt S rho u k).root =
            some (actionSGBlockAt S rho u k) := by
  intro w hw u hu k hk huk
  have hklt : k < r := mem_latestWindow_lt hk
  have hkbase : base ≤ k :=
    hspan.trans (WeakSG.mem_latestWindow_lower_bound hk)
  have hdeadlineG2 : S.a k + S.E.Δ ≤ early S.E S.hc r .g2 :=
    NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three hklt
  have hG2Phase : early S.E S.hc r .g2 ≤ early S.E S.hc r p := by
    cases p <;>
      simp only [early, Phase.earlyOffset] <;>
      linarith [S.E.Δ_pos]
  have hdeadline : S.a k + S.E.Δ ≤ early S.E S.hc r p :=
    hdeadlineG2.trans hG2Phase
  have hearlyDomain : early S.E S.hc r p ≤ domain S.E S.hc r p := by
    cases p <;>
      simp only [early, domain, Phase.earlyOffset, Phase.domainOffset] <;>
      linarith [S.E.Δ_pos]
  have hactionHor : S.a k ≤ rho.horizon :=
    (Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
      (hdeadline.trans (hearlyDomain.trans (hcap.trans hcapHor)))
  have hemit := honest_emits_exact_actionAttestationAt_of_awake
    S adm.toNamedScheduleWellFormed hu k huk hactionHor
  obtain ⟨i, hi, _, hbody⟩ := Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
  dsimp at hbody
  obtain ⟨K, hKstaged, haK⟩ := hbody
  have hKindex : K ∈ (NamedRun.stateBefore S rho i u).st.bodies := by
    change K ∈ (NamedRun.stateBefore S rho i u).st.bodies at hKstaged
    exact hKstaged
  have hstate := NamedActionSources.action_read_index S rho
    adm.toNamedScheduleWellFormed i u k hi
  have hKsource : K ∈
      (NamedRun.stateBeforeTime S rho (S.a k) u).st.bodies := by
    rw [← hstate]
    exact hKindex
  have hKrun : RunBlock S rho K :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hu hKindex
  have hcarrierMem : actionSGBlockAt S rho u k ∈
      (NamedRun.stateBeforeTime S rho (S.a k) u).st.core.T := by
    exact actionSGBlockAt_mem_storeBeforeTime S rho u k
  obtain ⟨D', hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (S.a k) u hcarrierMem
  obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedScheduleWellFormed.sorted (S.a k)
  have hDprefix : D' ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact hDbody
  have hKprefix : K ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact hKsource
  have hDrun : RunBlock S rho D' :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hu hDprefix
  have hKrun' : RunBlock S rho K :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hu hKprefix
  have hDKroot : D'.root = K.root := by
    rw [← Proofs.NamedWire.erase_root D', hDerase]
    exact Option.some.inj ((actionAttestationAt_shape S rho u k).2.2.symm.trans haK)
  have hDK : D' = K :=
    adm.toNamedRootCollisionFree.root_injective D' K hDrun hKrun' D' K
      (Or.inl (Proofs.NamedAncestry.named_self D'))
      (Or.inr (Proofs.NamedAncestry.named_self K)) hDKroot
  have hHErase : K.erase = actionSGBlockAt S rho u k := by
    rw [← hDK, hDerase]
  have hFmono : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) w).st.core.F
      (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.F :=
    NamedOutageClosure.incl_strict_F_mono S rho
      adm.toNamedScheduleWellFormed w (FrameForward.domain_le_a S r p)
  have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
    S rho (S.a r) w
  have hFroot : Block.Preceq
      (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.F
      (Protocol.get_fg_root
        (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.toHealing.toFG) :=
    Proofs.Records.preceq_get_fg_root_of_F
      (st := (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.toHealing.toFG)
      (by simpa only [Protocol.Store.toHealing] using hFJ)
  have hrootD : Block.Preceq
      (Protocol.get_fg_root
        (NamedRun.stateBeforeTime S rho (S.a r) w).st.core.toHealing.toFG) D := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedDuties.update_confirmation_with,
      Protocol.update_confirmation_with,
      Protocol.NamedStore.setClock] using hroots w hw
  have hFD := Block.preceq_trans hFmono (Block.preceq_trans hFroot hrootD)
  have hcarrierD := hsg k hkbase hklt u hu hemit
  have hpostK : S.E.t_GST ≤ S.a k :=
    hgstLo.trans (hsendLo k hkbase hklt)
  have hmaxK : max (S.a k) S.E.t_GST = S.a k := max_eq_left hpostK
  have hinput :=
    interpretedInputs_exact_of_honest_window_vote_after_gst_common_upper
      S adm p hk (v := u) (w := w)
        (t := domain S.E S.hc r p) (r := r) (k := k) hu hw
        (hvote := by
          refine ⟨(actionAttestationAt_shape S rho u k).1,
            (actionAttestationAt_shape S rho u k).2.1, hemit⟩)
        (hhead := ⟨i, hi, hKstaged, haK⟩)
        (hHC := by
          rw [hHErase]
          exact hcarrierD) (hFC := hFD)
        (hpost := by simpa only [actionAttestationAt_shape] using hpostK)
        (by simpa only [actionAttestationAt_shape, hmaxK] using hdeadline)
        hearlyDomain (hearlyDomain.trans (hcap.trans hcapHor))
  obtain ⟨y, hy, hyround, hyconfirmed, hyfind⟩ := hinput
  have hKroot : K.root = (actionSGBlockAt S rho u k).root := by
    rw [← hDK, ← Proofs.NamedWire.erase_root D', hDerase]
  refine ⟨y, ?_, hyround, ?_, ?_⟩
  · simpa only [hHErase] using hy
  · simpa only [hHErase] using hyconfirmed
  · rw [hHErase, hKroot] at hyfind
    exact hyfind

/-- `AwakeWindowMajority` and its transported relative-grade carrier facts
supply the same action-induction input as `GradeFormingMajority`. -/
theorem actionGradeFormationAt_of_awakeWindowMajority
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {r : Round} (hr : 0 < r)
    (_hawake : AwakeWindowMajority S.E (fun v => (S.node v).awake)
      rho.honest S.hc.η_SG r)
    (hgrade : ∀ p, domain S.E S.hc r p ≤ rho.horizon →
      RelativeGradeCarrierAt S rho r p) :
    ActionGradeFormationAt S rho r := by
  constructor
  · intro w hw hemitCurrent
    obtain ⟨i, hi, -⟩ := hemitCurrent
    have hhor : S.a r ≤ rho.horizon := by
      have h := adm.toNamedScheduleWellFormed.in_horizon
        (.tick w (S.a r)) (List.mem_of_getElem? hi)
      simpa only [NamedEvent.time] using h.2
    rcases Proofs.HealingLemmas.Rows.q31_actionsgblock_tiers S rho w r with
      hlive | ⟨Q, hQ, hEq⟩ | hroot | hanchor
    · exact Or.inl hlive.2.1
    · obtain ⟨k, hk, u, hu, hemit, hpre⟩ :=
        nodeQ2_preceq_honestWindowCarrier S adm hw hr hgrade hQ
      exact Or.inr (Or.inr ⟨k, hk, u, hu, hemit, hEq ▸ hpre⟩)
    · exact Or.inr (Or.inl hroot.2.2)
    · rcases hanchor with ⟨-, -, hEq⟩
      have hframe := actionFrame_g1 S adm hw hr hhor
      cases hroot : PhaseGrades.storeRoot S.E S.hc
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) w).st
          r .g1 with
      | none =>
          have hanchorEq : PhaseGrades.nodeAnchor S (actionReadAt S rho w r) r =
              Protocol.get_fg_root
                (actionStoreAt S rho w r).toHealing.toFG := by
            change DecoupledConsensusModel.Protocol.anchor S.E S.hc
                (actionReadAt S rho w r).st.core.toHealing r
                (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho w r).cache
                  (actionReadAt S rho w r).st.core.toHealing r).g1 = _
            rw [show (DecoupledConsensusModel.Protocol.readFrame
                (actionReadAt S rho w r).cache
                (actionReadAt S rho w r).st.core.toHealing r).g1 = some none by
              simpa only [hroot] using hframe]
            rfl
          exact Or.inr (Or.inl (hEq.trans hanchorEq))
      | some raw =>
          let clipped := DecoupledConsensusModel.Protocol.clipGrade raw
            (actionReadAt S rho w r).st.core.F
          have hframe' : (DecoupledConsensusModel.Protocol.readFrame
              (actionReadAt S rho w r).cache
              (actionReadAt S rho w r).st.core.toHealing r).g1 =
                some (some clipped) := by
            simpa only [hroot, Option.map_some, clipped] using hframe
          cases hactive : DecoupledConsensusModel.Protocol.activePrefix
              (Protocol.get_filtered_block_tree
                (actionStoreAt S rho w r).toHealing.toFG) clipped with
          | none =>
              have hactive' : DecoupledConsensusModel.Protocol.activePrefix
                  (Protocol.get_filtered_block_tree
                    (actionReadAt S rho w r).st.core.toHealing.toFG) clipped = none := by
                simpa only [actionStoreAt, actionReadAt] using hactive
              have hanchorEq :
                  PhaseGrades.nodeAnchor S (actionReadAt S rho w r) r =
                    Protocol.get_fg_root
                      (actionReadAt S rho w r).st.core.toHealing.toFG := by
                change DecoupledConsensusModel.Protocol.anchor S.E S.hc
                    (actionReadAt S rho w r).st.core.toHealing r
                    (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho w r).cache
                      (actionReadAt S rho w r).st.core.toHealing r).g1 = _
                rw [hframe']
                simp only [DecoupledConsensusModel.Protocol.anchor, hactive',
                  Option.getD_none]
              exact Or.inr (Or.inl (hEq.trans (by
                simpa only [actionStoreAt, actionReadAt] using hanchorEq)))
          | some A =>
              have hactive' : DecoupledConsensusModel.Protocol.activePrefix
                  (Protocol.get_filtered_block_tree
                    (actionReadAt S rho w r).st.core.toHealing.toFG) clipped = some A := by
                simpa only [actionStoreAt, actionReadAt] using hactive
              have hAclip : Block.Preceq A clipped :=
                (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).2
              have hrawGrade : DecoupledConsensusModel.Protocol.gradeBool S.E
                  (NamedRun.stateBeforeTime S rho
                    (domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
                  (NamedRun.stateBeforeTime S rho
                    (domain S.E S.hc r .g1) w).st.core.F
                  S.hc.η_SG r (early S.E S.hc r .g1)
                    (late S.E S.hc r .g1) raw = true :=
                (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem (by
                  simpa only [PhaseGrades.storeRoot, PhaseGrades.phaseRoot]
                    using hroot))).2
              obtain ⟨k, hk, u, hu, hemit, hrawPre⟩ :=
                hgrade .g1 ((FrameForward.domain_le_a S r .g1).trans hhor)
                  w hw raw hrawGrade
              have hanchorEq :
                  PhaseGrades.nodeAnchor S (actionReadAt S rho w r) r = A := by
                change DecoupledConsensusModel.Protocol.anchor S.E S.hc
                    (actionReadAt S rho w r).st.core.toHealing r
                    (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho w r).cache
                      (actionReadAt S rho w r).st.core.toHealing r).g1 = A
                rw [hframe']
                simp only [DecoupledConsensusModel.Protocol.anchor, hactive',
                  Option.getD_some]
              exact Or.inr (Or.inr ⟨k, hk, u, hu, hemit,
                hEq ▸ hanchorEq ▸ Block.preceq_trans hAclip
                  (Block.preceq_trans
                    (NamedOutageClosure.clip_preceq raw
                      (actionReadAt S rho w r).st.core.F) hrawPre)⟩)
  · intro w hw T hT
    obtain ⟨Cfg, hsource, hTCfg⟩ := Option.map_eq_some_iff.mp hT
    have hpreCfg : Block.Preceq T Cfg := by
      rw [← hTCfg]
      obtain ⟨D, -, hDerase, hDderiv, -⟩ :=
        NamedActionSources.action_witness S rho w r Cfg hsource
      change ((actionReadAt S rho w r).st.core.σ Cfg).T_h ⪯ Cfg
      rw [hDderiv, ← hDerase]
      exact Proofs.Optimistic.derive_named_T_h_preceq S.E S.cfg D
    have hsource' : PhaseGrades.nodeFGSource S
        (actionReadAt S rho w r) r = some Cfg := by
      have hround : S.hc.round_of
          (actionStoreAt S rho w r).st.core.toHealing.s = r := by
        simpa only [Protocol.Store.toHealing] using actionStoreAt_round S rho w r
      have hsource0 := hsource
      change Protocol.fg_source_with
          (NamedProfile.gradeContract (actionStoreAt S rho w r).cache)
          S.E S.hc (actionStoreAt S rho w r).st.core.toHealing
          (S.hc.round_of (actionStoreAt S rho w r).st.core.toHealing.s)
          (Protocol.grade2_block_with
            (NamedProfile.gradeContract (actionStoreAt S rho w r).cache)
            S.E S.hc (actionStoreAt S rho w r).st.core.toHealing
            (S.hc.round_of (actionStoreAt S rho w r).st.core.toHealing.s)) =
        some Cfg at hsource0
      rw [hround] at hsource0
      simpa only [PhaseGrades.nodeFGSource, PhaseGrades.nodeRead] using hsource0
    cases hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho w r) r with
    | none =>
        have hQ' : Protocol.grade2_block_with
            (NamedProfile.gradeContract (actionReadAt S rho w r).cache)
            S.E S.hc (actionReadAt S rho w r).st.core.toHealing r = none := hQ
        rw [PhaseGrades.nodeFGSource, Protocol.fg_source_with.eq_def, hQ'] at hsource'
        cases hsource'
    | some Q =>
        have hQ' : Protocol.grade2_block_with
            (NamedProfile.gradeContract (actionReadAt S rho w r).cache)
            S.E S.hc (actionReadAt S rho w r).st.core.toHealing r = some Q := hQ
        rw [PhaseGrades.nodeFGSource, Protocol.fg_source_with.eq_def, hQ'] at hsource'
        cases hclear : Protocol.deepest_clear (some Q)
            (actionReadAt S rho w r).st.core.toHealing.live_confirmed
            ((NamedProfile.gradeContract (actionReadAt S rho w r).cache).read
              S.E S.hc (actionReadAt S rho w r).st.core.toHealing r).clear with
        | some C =>
            simp only [hclear, Option.some.injEq] at hsource'
            subst Cfg
            exact Or.inl (Block.preceq_trans hpreCfg
              (Proofs.Engine.deepest_clear_preceq hclear))
        | none =>
            simp only [hclear, Option.some.injEq] at hsource'
            subst Cfg
            obtain ⟨k, hk, u, hu, hemit, hQpre⟩ :=
              nodeQ2_preceq_honestWindowCarrier S adm hw hr hgrade hQ
            exact Or.inr ⟨k, hk, u, hu, hemit,
              Block.preceq_trans hpreCfg hQpre⟩

/-- The same action induction covers settled history and the genesis boundary. -/
theorem actionSources_preceq_of_priorConfirmations_and_historyCut
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hmajority : HonestWeightMajority S rho.honest)
    {base cut : Round} {s : Slot} {D : Block V}
    (hspan : base ≤ cut - S.hc.η_SG)
    (hbootstrap : ∀ r, base ≤ r → r < cut →
      S.a r < Protocol.vote_time S.E (s + 1) → ∀ w ∈ rho.honest,
      rho.emits S w (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
        Block.Preceq (actionSGBlockAt S rho w r) D)
    (hprior : ∀ q, S.hc.opening_slot cut ≤ q → q < s →
      ∀ v ∈ rho.honest, ∀ C,
      GenuineConfirmationWith
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadAt S rho v
            (Protocol.confirmation_time S.E q)).cache)
        S.E S.hc (confStore S rho v q) q C →
        Block.Preceq C D)
    (hlegacyRoots : ∀ r, cut ≤ r →
      S.a r < Protocol.vote_time S.E (s + 1) → ∀ w ∈ rho.honest,
      ∀ (C : NamedBlock V) (a : NamedAttestation V),
      let R := Protocol.get_fg_root (actionStoreAt S rho w r).toHealing.toFG
      C ∈ (actionStoreAt S rho w r).st.bodies →
      (Protocol.derive_named S.E S.cfg C).J = R →
      a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (Object.attest a) (S.a a.round) →
      a.round < cut →
      a.height_pair.erase = HeightPair.target
        (Protocol.derive_named S.E S.cfg C).h_j
        (Protocol.derive_named S.E S.cfg C).J.root →
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) = some R →
        Block.Preceq R D)
    (hformation : ∀ r, cut ≤ r → 0 < r →
      S.a r < Protocol.vote_time S.E (s + 1) →
      (∀ k, base ≤ k → k < r → ∀ v ∈ rho.honest,
        NamedRun.emits S rho v
            (Object.attest (actionAttestationAt S rho v k)) (S.a k) →
          Block.Preceq (actionSGBlockAt S rho v k) D) →
      (∀ w ∈ rho.honest, Block.Preceq
        (Protocol.get_fg_root (actionStoreAt S rho w r).toHealing.toFG) D) →
      ActionGradeFormationAt S rho r) :
    ∀ r, base ≤ r → S.a r < Protocol.vote_time S.E (s + 1) →
      (∀ w ∈ rho.honest,
        rho.emits S w (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
          Block.Preceq (actionSGBlockAt S rho w r) D) ∧
      (cut ≤ r → ∀ w ∈ rho.honest,
        Block.Preceq (Protocol.get_fg_root (actionStoreAt S rho w r).toHealing.toFG) D ∧
        ∀ T, fgConfirmationWitness S (actionStoreAt S rho w r) = some T →
          Block.Preceq T D) := by
  have hbaseCut : base ≤ cut := hspan.trans (Nat.sub_le _ _)
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
      intro hbase haction
      by_cases hboot : r < cut
      · refine ⟨hbootstrap r hbase hboot haction, ?_⟩
        intro hcut
        exact False.elim (Nat.not_lt_of_ge hcut hboot)
      · have hcut : cut ≤ r := Nat.le_of_not_gt hboot
        have hsg : ∀ k, base ≤ k → k < r → ∀ v ∈ rho.honest,
            rho.emits S v (Object.attest (actionAttestationAt S rho v k)) (S.a k) →
              Block.Preceq (actionSGBlockAt S rho v k) D := by
          intro k hk hkr
          exact (ih k hkr hk
            ((Assembly.a_mono S hkr.le).trans_lt haction)).1
        have hroots : ∀ w ∈ rho.honest, Block.Preceq
            (Protocol.get_fg_root (actionStoreAt S rho w r).toHealing.toFG) D := by
          intro w hw
          rcases WeakFG.fgRoot_confirmationWitness_at_action S adm hmajority hw r with
              hgen | ⟨C, hC, hJ, a, ha, hemit, har, hpair, hT⟩
          · rw [hgen]
            exact Protocol.preceq_genesis D
          · by_cases haold : a.round < cut
            · exact hlegacyRoots r hcut haction w hw C a hC hJ
                ha hemit haold hpair hT
            · have harecent : cut ≤ a.round := Nat.le_of_not_gt haold
              exact ((ih a.round har (hbaseCut.trans harecent)
                ((Assembly.a_mono S har.le).trans_lt haction)).2
                  harecent a.val_index ha).2 _ hT
        by_cases hrzero : r = 0
        · subst r
          constructor
          · intro w hw _
            rw [WeakGenesis.actionSGBlock_eq_genesis_zero S adm hmajority hw]
            exact Protocol.preceq_genesis D
          · intro _ w hw
            refine ⟨hroots w hw, ?_⟩
            intro T hT
            rw [WeakGenesis.fgConfirmationWitness_zero S adm w] at hT
            cases hT
        · have hr : 0 < r := Nat.pos_of_ne_zero hrzero
          have hwindowStart : base ≤ r - S.hc.η_SG :=
            hspan.trans (Nat.sub_le_sub_right hcut _)
          have hprev : base ≤ r - 1 :=
            hwindowStart.trans (Nat.sub_le_sub_left S.hc.η_SG_ge_one r)
          have hlive : ∀ w ∈ rho.honest,
              Block.Preceq (actionStoreAt S rho w r).live_confirmed D := by
            intro w hw
            have hslot : S.hc.opening_slot r < s :=
              Nat.lt_of_succ_le (openingNext_le_of_action_before_nextVote S haction)
            rcases actionStoreAt_liveConfirmed_genuine_or_fgRoot S rho w r with
                ⟨C, hC, hEq⟩ | ⟨R, hR, hEq⟩
            · rw [← hEq]
              exact hprior (S.hc.opening_slot r)
                (Nat.mul_le_mul_right S.hc.R hcut) hslot w hw C (by
                  simpa only [Setup.a, Protocol.a_eq_confirmation_time]
                    using hC)
            · rw [← hEq, hR]
              have hroot := hroots w hw
              rw [actionStoreAt_fgRoot_eq_openingConfStore] at hroot
              exact hroot
          have hform := hformation r hcut hr haction hsg hroots
          constructor
          · intro w hw hemit
            rcases hform.action w hw hemit with
                hpre | heq | ⟨k, hk, v, hv, hem, hpre⟩
            · exact Block.preceq_trans hpre (hlive w hw)
            · exact heq ▸ hroots w hw
            · exact Block.preceq_trans hpre (hsg k
                (hwindowStart.trans (WeakSG.mem_latestWindow_lower_bound hk))
                (mem_latestWindow_lt hk) v hv hem)
          · intro _ w hw
            refine ⟨hroots w hw, ?_⟩
            intro T hT
            rcases hform.witness w hw T hT with
                hpre | ⟨k, hk, v, hv, hem, hpre⟩
            · exact Block.preceq_trans hpre (hlive w hw)
            · exact Block.preceq_trans hpre
                (hsg k
                  (hwindowStart.trans (WeakSG.mem_latestWindow_lower_bound hk))
                  (mem_latestWindow_lt hk) v hv hem)

#print axioms actionSources_preceq_of_priorConfirmations_and_historyCut
#print axioms actionGradeFormationAt_of_awakeWindowMajority
#print axioms relativeGradeCarrierAt_of_awakeWindowHistory_gstZero
#print axioms relativeCarrierWindowAt_of_awakeWindowHistory_of_delivery
#print axioms relativeCarrierWindowAt_of_awakeWindowHistory_w

end WeakJoint
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
