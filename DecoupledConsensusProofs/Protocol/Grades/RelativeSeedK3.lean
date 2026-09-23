module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.SeedCanonicalAnchor
public import DecoupledConsensusProofs.Protocol.Grades.RelativeSeedSettlement
public import DecoupledConsensusProofs.Protocol.Grades.RelativeCrossReader
public import DecoupledConsensusProofs.Protocol.Grades.Q31_actionSGBlock_tiers

@[expose] public section

/-! # Direct relative-grade K3 transport

Prepared versions of the two transport steps used by the original pointwise
K3 proof. The caller supplies activity at the target action read; the
finalized-prefix guards then follow from monotonicity and local coverage.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Protocol Proofs.HealingLemmas Proofs.Optimistic DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem relativeSeed_actionTiers_of_rawG2
    (S : Setup V) (rho : Run V) (v : V) (r : Round)
    (hraw : nodeRawG2 S (actionReadAt S rho v r) r) :
    letI n := actionReadAt S rho v r
    letI A := nodeAnchor S n r
    (Block.Preceq A (actionSGBlockAt S rho v r) ∧
      Block.Preceq (actionSGBlockAt S rho v r) n.st.core.live_confirmed ∧
      nodeClear S n r (actionSGBlockAt S rho v r) = true) ∨
    (∃ Q, nodeQ2 S n r = some Q ∧ actionSGBlockAt S rho v r = Q) ∨
    actionSGBlockAt S rho v r =
      Protocol.get_fg_root n.st.core.toHealing.toFG := by
  rcases Proofs.HealingLemmas.Rows.q31_actionsgblock_tiers S rho v r with
    h | h | ⟨-, -, h⟩ | ⟨-, hno, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact absurd hraw hno

private theorem relativeSeed_F_mono
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho) (v : V)
    {t t' : Time} (htt' : t ≤ t') :
    Block.Preceq (NamedRun.stateBeforeTime S rho t v).st.core.F
      (NamedRun.stateBeforeTime S rho t' v).st.core.F := by
  rw [NamedOutageClosure.strict_read_eq_index S rho
      core.toNamedScheduleWellFormed.sorted t,
    NamedOutageClosure.strict_read_eq_index S rho
      core.toNamedScheduleWellFormed.sorted t']
  exact Proofs.NamedRuntime.stateBefore_F_mono S rho v
    (NamedOutageClosure.strict_lengths_mono rho htt')

omit [Fintype V] in
private theorem relativeSeed_cover_preceq
    {gv : Protocol.GradeView V} {u : Protocol.SGVote V}
    {root : BlockId} {Q H : Block V}
    (hcover : DecoupledConsensusModel.Protocol.localCovers gv u.confirmed Q = true)
    (hconf : u.confirmed = some root)
    (hfind : Block.find? gv.T root = some H) : Block.Preceq Q H := by
  unfold DecoupledConsensusModel.Protocol.localCovers Protocol.head_covers at hcover
  simp only [hconf] at hcover
  rw [hfind] at hcover
  exact hcover

/-- A relative G0 grade contains its graded block in the G0-domain tree. -/
theorem storeGrade_g0_mem_domainTree
    (S : Setup V) (rho : Run V) {r : Round} {w : V} {Q : Block V}
    (hG0 : storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc r .g0) w).st r .g0 Q = true) :
    Q ∈ (readAt S rho (domain S.E S.hc r .g0) w).st.core.T := by
  let n := readAt S rho (domain S.E S.hc r .g0) w
  have hgrade : DecoupledConsensusModel.Protocol.gradeBool S.E
      n.st.core.toHealing.gradeView n.st.core.F S.hc.η_SG r
      (early S.E S.hc r .g0) (late S.E S.hc r .g0) Q = true := by
    simpa only [storeGrade, phaseGrade, PhaseGrades.readAt, n] using hG0
  simp only [DecoupledConsensusModel.Protocol.gradeBool, decide_eq_true_eq] at hgrade
  have hne : (Finset.univ.filter fun s =>
      DecoupledConsensusModel.Protocol.positive n.st.core.toHealing.gradeView
        n.st.core.F S.hc.η_SG r (early S.E S.hc r .g0)
        (late S.E S.hc r .g0) s Q = true).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hgrade
    simp only [Electorate.weightOf, Finset.sum_empty] at hgrade
    omega
  obtain ⟨s, hs⟩ := hne
  obtain ⟨tok, -, -, hcov, -, -⟩ := by
    simpa only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq] using
      (Finset.mem_filter.mp hs).2
  cases hkey : tok.key with
  | none => simp [DecoupledConsensusModel.Protocol.localCovers, Protocol.head_covers, hkey] at hcov
  | some root =>
      cases hfind : Block.find? n.st.core.toHealing.gradeView.T root with
      | none => simp [DecoupledConsensusModel.Protocol.localCovers, Protocol.head_covers, hkey, hfind] at hcov
      | some H =>
          have hQH : Block.Preceq Q H := by
            simpa [DecoupledConsensusModel.Protocol.localCovers, Protocol.head_covers,
              hkey, hfind] using hcov
          have hHT : H ∈ n.st.core.T := Proofs.HealingLemmas.find?_mem hfind
          have hpc := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
            (domain S.E S.hc r .g0) w
          exact Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2 Q H hHT hQH

/-- Direct prepared G1→G0 transport when the graded block remains active at
the target action read. -/
theorem storeGrade_g0_of_g1_and_targetActionActive
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho) {r : Round} (hr : 0 < r)
    (ready : GradeRoundReady S rho r)
    {source target : V} (hsource : source ∈ rho.honest)
    (htarget : target ∈ rho.honest) {B : Block V}
    (hG1 : storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc r .g1) source).st r .g1 B = true)
    (hactive : B ∈ filteredTree (actionReadAt S rho target r)) :
    storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc r .g0) target).st r .g0 B = true := by
  have hFB : Block.Preceq (actionReadAt S rho target r).st.core.F B :=
    NamedOutageClosure.q10_filtered_F hactive
  have hF0B : Block.Preceq
      (readAt S rho (domain S.E S.hc r .g0) target).st.core.F B :=
    Block.preceq_trans
      (relativeSeed_F_mono S adm.toNamedAdmissibleCore target
        (FrameForward.domain_le_a S r .g0)) hFB
  have hgstG1 : S.E.t_GST ≤ early S.E S.hc r .g1 :=
    ready.1.trans (GradeCutoffMono.early_g2_le_early_g1 S.E S.hc r)
  have hbelow := g1G0CrossReaderFinalizedBelow_of_finalitySafety_and_relay
    S adm hsb hgstG1 ready.2 hsource htarget (B := B) (by
      intro sender u root H _ hcover hconf hfind
      exact Block.preceq_trans hF0B
        (relativeSeed_cover_preceq hcover hconf hfind))
  have hguard := g1G0CrossReaderBodyReadyGuard_of_finalizedBelow
    S adm.toNamedAdmissibleCore hr hgstG1 ready.2 hsource htarget hbelow
  exact storeGrade_g0_of_storeGrade_g1_cross_reader
    S rho adm.toNamedAdmissibleCore r
      (g1G0TwoCutoffDelivery_of_core S adm.toNamedAdmissibleCore hgstG1)
      ready.2 source target hsource htarget B hG1 hguard

/-- Direct prepared G2→G1 transport when the selected block remains active at
the target action read. -/
theorem storeGrade_g1_of_g2_and_targetActionActive
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho) {r : Round} (hr : 0 < r)
    (ready : GradeRoundReady S rho r)
    {source target : V} (hsource : source ∈ rho.honest)
    (htarget : target ∈ rho.honest) {B : Block V}
    (hG2 : storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc r .g2) source).st r .g2 B = true)
    (hactive : B ∈ filteredTree (actionReadAt S rho target r)) :
    storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc r .g1) target).st r .g1 B = true := by
  have hFB : Block.Preceq (actionReadAt S rho target r).st.core.F B :=
    NamedOutageClosure.q10_filtered_F hactive
  have hF1B : Block.Preceq
      (readAt S rho (domain S.E S.hc r .g1) target).st.core.F B :=
    Block.preceq_trans
      (relativeSeed_F_mono S adm.toNamedAdmissibleCore target
        (FrameForward.domain_le_a S r .g1)) hFB
  have hbelow := crossReaderFinalizedBelow_of_finalitySafety_and_relay
    S adm hsb ready.1 ready.2 hsource htarget (B := B) (by
      intro sender u root H _ hcover hconf hfind
      exact Block.preceq_trans hF1B
        (relativeSeed_cover_preceq hcover hconf hfind))
  have hguard := crossReaderBodyReadyGuard_of_finalizedBelow
    S adm.toNamedAdmissibleCore hr ready.1 ready.2 hsource htarget hbelow
  exact storeGrade_g1_of_storeGrade_g2_cross_reader
    S rho adm.toNamedAdmissibleCore r
      (twoCutoffDelivery_of_core S adm.toNamedAdmissibleCore ready.1)
      ready.2 source target hsource htarget B hG2 hguard

theorem relativeG0_compatible_clearSource
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (hr : 0 < r) (hactionHor : S.a r ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) {Q C : Block V}
    (hQgrade : storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc r .g0) w).st r .g0 Q = true)
    (hQtree : Q ∈ (readAt S rho (domain S.E S.hc r .g0) w).st.core.T)
    (hQaction : Q ∈ filteredTree (actionReadAt S rho w r))
    (hCclear : nodeClear S (actionReadAt S rho w r) r C = true) :
    Block.compatible Q C = true := by
  obtain ⟨raw, hraw, hQraw⟩ := NamedOutageClosure.q10_freeze_of_graded S.E
    (readAt S rho (domain S.E S.hc r .g0) w).st.core.toHealing.gradeView
    (readAt S rho (domain S.E S.hc r .g0) w).st.core.F S.hc.η_SG r
    (e := early S.E S.hc r .g0) (l := late S.E S.hc r .g0)
    (by simp [early, late, Phase.earlyOffset, Phase.lateOffset]) hQtree
    (by simpa only [storeGrade] using hQgrade)
  have hactionFrame := actionFrame_g0 S adm.toNamedAdmissibleCore hw hr hactionHor
  have hframe : (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho w r).cache
      (actionReadAt S rho w r).st.core.toHealing r).g0 =
      some (some (DecoupledConsensusModel.Protocol.clipGrade raw
        (actionReadAt S rho w r).st.core.F)) := by
    simpa only [storeRoot, phaseRoot, hraw, Option.map_some] using hactionFrame
  have hFQ : Block.Preceq (actionReadAt S rho w r).st.core.F Q :=
    NamedOutageClosure.q10_filtered_F hQaction
  have hQclip : Block.Preceq Q
      (DecoupledConsensusModel.Protocol.clipGrade raw
        (actionReadAt S rho w r).st.core.F) := by
    apply (NamedOutageClosure.q10_retained_prefix raw
      (actionReadAt S rho w r).st.core.F Q ?_).mpr hQraw
    simpa only [Block.compatible, Bool.or_eq_true] using Or.inr hFQ
  have hCclip : Block.compatible C
      (DecoupledConsensusModel.Protocol.clipGrade raw
        (actionReadAt S rho w r).st.core.F) = true := by
    simpa only [nodeClear, nodeRead, NamedProfile.gradeContract,
      DecoupledConsensusModel.Protocol.frameContract, DecoupledConsensusModel.Protocol.frameGradeRead,
      DecoupledConsensusModel.Protocol.clear, hframe] using hCclear
  simp only [Block.compatible, Bool.or_eq_true] at hCclip ⊢
  rcases hCclip with hCclip | hclipC
  · exact (Block.preceq_linear hQclip hCclip).elim Or.inl Or.inr
  · exact Or.inl (Block.preceq_trans hQclip hclipC)

theorem relativeSeed_sameReaderG1_compatible
    (S : Setup V) (rho : Run V) (r : Round) (w : V) {A Q : Block V}
    (hA : storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc r .g1) w).st r .g1 A = true)
    (hQ : storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc r .g1) w).st r .g1 Q = true) :
    Block.compatible A Q = true := by
  change DecoupledConsensusModel.Protocol.gradeBool S.E
    (readAt S rho (domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
    (readAt S rho (domain S.E S.hc r .g1) w).st.core.F S.hc.η_SG r
    (early S.E S.hc r .g1) (late S.E S.hc r .g1) A = true at hA
  change DecoupledConsensusModel.Protocol.gradeBool S.E
    (readAt S rho (domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
    (readAt S rho (domain S.E S.hc r .g1) w).st.core.F S.hc.η_SG r
    (early S.E S.hc r .g1) (late S.E S.hc r .g1) Q = true at hQ
  apply graded_oneChain_at_reader
    (E := S.E)
    (gv := (readAt S rho (domain S.E S.hc r .g1) w).st.core.toHealing.gradeView)
    (F := (readAt S rho (domain S.E S.hc r .g1) w).st.core.F)
    (eta := S.hc.η_SG) (r := r)
    (early := early S.E S.hc r .g1) (late := late S.E S.hc r .g1)
  · unfold early late Phase.earlyOffset Phase.lateOffset
    linarith [S.E.Δ_pos]
  · exact hA
  · exact hQ

set_option maxHeartbeats 400000 in
/-- Pointwise K3 by the original clear/selected/root argument, with both grade
transports interpreted by the prepared relative contract. -/
theorem preparedAnchor_compatible_carrier_of_relativeSettlement
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {c : Round} (hc : 1 ≤ c)
    (hframe : GateOffFrameAt S rho M (c - 1) (c + 1))
    (hpost : S.E.t_GST ≤ S.a (c - 1))
    (hhorNext : S.a (c + 1) ≤ rho.horizon)
    (ready : GradeRoundReady S rho c)
    (hsettled : NamedLiveG1SettledAt S rho c)
    (hselected : SelectedG2SettledAt S rho c)
    {w v : V} (hw : w ∈ rho.honest) (hv : v ∈ rho.honest) {d : Slot}
    (hd1 : S.hc.opening_slot c + 1 ≤ d)
    (hd2 : d ≤ seedRoundLastSlot S c)
    (hround : S.hc.round_of d = c) :
    Block.compatible (voterAnchorAt S rho w d)
      (actionSGBlockAt S rho v c) = true := by
  have hcPos : 0 < c := Nat.succ_le_iff.mp hc
  have haCSucc : S.a c ≤ S.a (c + 1) := Assembly.a_mono S (Nat.le_succ c)
  have hhorC : S.a c ≤ rho.horizon := haCSucc.trans hhorNext
  have hlo' : S.hc.opening_slot c ≤ d := (Nat.le_succ _).trans hd1
  have hdNext : d ≤ S.hc.opening_slot (c + 1) :=
    hd2.trans (by unfold seedRoundLastSlot; exact Nat.sub_le _ _)
  have hvoteHi : Protocol.vote_time S.E d ≤ S.a (c + 1) := by
    refine (Protocol.vote_time_le_confirmation_time S.E d).trans ?_
    have hm : Protocol.confirmation_time S.E d ≤
        Protocol.confirmation_time S.E (S.hc.opening_slot (c + 1)) := by
      rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E d,
        ← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E
          (S.hc.opening_slot (c + 1))]
      exact Int.add_le_add_right
        (Protocol.vote_time_mono_slots S.E (Nat.succ_le_succ hdNext)) _
    exact hm.trans (by rw [Setup.a, Protocol.a_eq_confirmation_time])
  have hvoteHor := hvoteHi.trans hhorNext
  have hnext : Protocol.vote_time S.E d ≤ opening S.E S.hc (c + 1) := by
    have hlt : d < S.hc.opening_slot (c + 1) :=
      hd2.trans_lt (Nat.sub_lt (by
        unfold Protocol.HealConfig.opening_slot
        exact Nat.mul_pos (Nat.succ_pos c)
          (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)) Nat.one_pos)
    exact (le_of_lt (by
      simpa only [opening] using
        (show Protocol.vote_time S.E d <
          Protocol.proposal_time S.E (S.hc.opening_slot (c + 1)) from
          (by
            exact (by
              have h := Protocol.proposal_time_mono S.E (Nat.succ_le_of_lt hlt)
              exact (lt_of_lt_of_le
                (by
                  simp only [Protocol.vote_time, Protocol.proposal_time,
                    Env.t, slotStart]
                  push_cast
                  nlinarith [S.E.Δ_pos]) h))))))
  rcases preparedAnchor_compatible_carrier_or_activePrefix S adm hfb hc hframe
      hhorNext hw hv hlo' hd2 hround with hdone | ⟨root, A, hframeG1, hactive, hanchor⟩
  · exact hdone
  obtain ⟨hAtree, hAG1⟩ := fixedRoot_activeVoterAnchor_g1_data
    S adm hcPos hlo' hround hnext hvoteHor hw hframeG1 hactive
  have hsb := slashableBound_of_admissible_belowOneThird S adm hfb
  have hraw : nodeRawG2 S (actionReadAt S rho v c) c :=
    nodeRawG2_of_gateOffFrame S adm hfb hcPos hhorC hpost
      (fun u hu => (hframe _ le_rfl
        ((Assembly.a_mono S (Nat.sub_le c 1)).trans haCSucc) u hu).2)
      (fun x hx => (hframe _ (Assembly.a_mono S (Nat.sub_le c 1)) haCSucc x hx).2)
      (fun x hx => (hframe _ (Assembly.a_mono S (Nat.sub_le c 1)) haCSucc x hx).1) v hv
  rw [hanchor]
  rcases relativeSeed_actionTiers_of_rawG2 S rho v c hraw with
    hclear | ⟨Q, hQ, hcarrier⟩ | hrootCarrier
  · obtain ⟨-, -, hCclear⟩ := hclear
    rcases hsettled w hw A hAG1 v hv with hAroot | hAactive
    · have hrootCarrier' := actionFGRoot_preceq_actionSGBlockAt S rho v c
      rw [actionStoreAt_fgRoot_eq_storeBeforeTime] at hrootCarrier'
      simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inl (Block.preceq_trans hAroot hrootCarrier')
    · have hAaction : A ∈ filteredTree (actionReadAt S rho v c) := by
        change A ∈ Protocol.get_filtered_block_tree
          (actionStoreAt S rho v c).toHealing.toFG
        rw [actionStoreAt_filteredTree]
        exact hAactive
      have hAG0 := storeGrade_g0_of_g1_and_targetActionActive
        S adm hsb hcPos ready hw hv hAG1 hAaction
      exact relativeG0_compatible_clearSource S adm hcPos hhorC hv hAG0
        (storeGrade_g0_mem_domainTree S rho hAG0) hAaction hCclear
  · rw [hcarrier]
    have hQG2 := selectedQ2_storeGrade_at_g2Domain S adm hQ
    rcases hsettled w hw A hAG1 w hw with hAroot | hAactive
    · rcases hselected v hv Q hQ w hw with hQroot | hQactive
      · exact Block.compatible_of_preceq_common hAroot hQroot
      · have hQaction : Q ∈ filteredTree (actionReadAt S rho w c) := by
          change Q ∈ Protocol.get_filtered_block_tree
            (actionStoreAt S rho w c).toHealing.toFG
          rw [actionStoreAt_filteredTree]
          exact hQactive
        have hQG1 := storeGrade_g1_of_g2_and_targetActionActive
          S adm hsb hcPos ready hv hw hQG2 hQaction
        exact relativeSeed_sameReaderG1_compatible S rho c w hAG1 hQG1
    · have hAaction : A ∈ filteredTree (actionReadAt S rho w c) := by
        change A ∈ Protocol.get_filtered_block_tree
          (actionStoreAt S rho w c).toHealing.toFG
        rw [actionStoreAt_filteredTree]
        exact hAactive
      rcases hselected v hv Q hQ w hw with hQroot | hQactive
      · have hrootA : Block.Preceq
            (Protocol.get_fg_root (actionStoreAt S rho w c).toHealing.toFG) A :=
          Proofs.Records.preceq_get_fg_root_of_mem_filtered hAaction
        rw [← actionStoreAt_fgRoot_eq_storeBeforeTime] at hQroot
        simp only [Block.compatible, Bool.or_eq_true]
        exact Or.inr (Block.preceq_trans hQroot hrootA)
      · have hQaction : Q ∈ filteredTree (actionReadAt S rho w c) := by
          change Q ∈ Protocol.get_filtered_block_tree
            (actionStoreAt S rho w c).toHealing.toFG
          rw [actionStoreAt_filteredTree]
          exact hQactive
        have hQG1 := storeGrade_g1_of_g2_and_targetActionActive
          S adm hsb hcPos ready hv hw hQG2 hQaction
        exact relativeSeed_sameReaderG1_compatible S rho c w hAG1 hQG1
  · rw [hrootCarrier]
    rcases hsettled w hw A hAG1 v hv with hAroot | hAactive
    · simpa only [Block.compatible, Bool.or_eq_true] using Or.inl hAroot
    · have hrootA : Block.Preceq
          (Protocol.get_fg_root
            (rho.storeBeforeTime S v (S.a c)).toHealing.toFG) A :=
        Proofs.Records.preceq_get_fg_root_of_mem_filtered hAactive
      have hrootEq : Protocol.get_fg_root
          (actionReadAt S rho v c).st.core.toHealing.toFG =
          Protocol.get_fg_root
            (rho.storeBeforeTime S v (S.a c)).toHealing.toFG := by
        change Protocol.get_fg_root (actionStoreAt S rho v c).toHealing.toFG = _
        exact actionStoreAt_fgRoot_eq_storeBeforeTime S rho v c
      rw [hrootEq]
      simpa only [Block.compatible, Bool.or_eq_true] using Or.inr hrootA

/-- Pointwise K3 from the gate-off frame and round open. All relative
settlement and selected-Q2 noninterference facts are derived internally. -/
theorem preparedAnchor_compatible_carrier_of_gateOff_relative
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {c : Round} (hc : 1 ≤ c)
    (hframe : GateOffFrameAt S rho M (c - 1) (c + 1))
    (hpost : S.E.t_GST ≤ S.a (c - 1))
    (hhorNext : S.a (c + 1) ≤ rho.horizon)
    (ready : GradeRoundReady S rho c)
    {w v : V} (hw : w ∈ rho.honest) (hv : v ∈ rho.honest) {d : Slot}
    (hd1 : S.hc.opening_slot c + 1 ≤ d)
    (hd2 : d ≤ seedRoundLastSlot S c)
    (hround : S.hc.round_of d = c) :
    Block.compatible (voterAnchorAt S rho w d)
      (actionSGBlockAt S rho v c) = true := by
  have hcPos : 0 < c := Nat.succ_le_iff.mp hc
  have hpredAction : S.a (c - 1) ≤ S.a c := Assembly.a_mono S (Nat.sub_le c 1)
  have hactionNext : S.a c ≤ S.a (c + 1) := Assembly.a_mono S (Nat.le_succ c)
  have hhorC : S.a c ≤ rho.horizon := hactionNext.trans hhorNext
  have hprev : ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (c - 1))).h_max = M :=
    fun u hu => (hframe _ le_rfl (hpredAction.trans hactionNext) u hu).2
  have hfrontier : ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a c)).h_max = M :=
    fun u hu => (hframe _ hpredAction hactionNext u hu).2
  have hgate : ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a c)).h_j + 2 ≤ M :=
    fun u hu => (hframe _ hpredAction hactionNext u hu).1
  have hsettled : NamedLiveG1SettledAt S rho c :=
    namedLiveG1SettledAt_of_gateOff S adm hfb hcPos hpost hprev hfrontier hgate hhorC
  have hwindow : RelativeCarrierWindowAt S rho (c - 1) .g2 :=
    relativeCarrierWindowAt_of_gateOff S adm hfb hcPos hpost hprev hfrontier hgate
      ((FrameForward.domain_le_a S c .g2).trans hhorC)
  have hmajority : Internal.NamedOutageEntry.GradeFormingMajority S rho c :=
    gradeFormingMajority_of_admissible_belowOneThird S adm hfb hcPos
      ((FrameForward.domain_le_a S c .g2).trans hhorC) (by assumption)
  have hselected : SelectedG2SettledAt S rho c :=
    selectedG2SettledAt_of_gateOff S adm hfb hcPos hwindow hmajority hpost hprev
      hfrontier hgate hhorC
  exact preparedAnchor_compatible_carrier_of_relativeSettlement S adm hfb hc hframe
    hpost hhorNext ready hsettled hselected hw hv hd1 hd2 hround

#print axioms storeGrade_g0_mem_domainTree
#print axioms storeGrade_g0_of_g1_and_targetActionActive
#print axioms storeGrade_g1_of_g2_and_targetActionActive
#print axioms preparedAnchor_compatible_carrier_of_relativeSettlement
#print axioms preparedAnchor_compatible_carrier_of_gateOff_relative

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
