module
public import DecoupledConsensusProofs.ReviewTheorem

@[expose] public section

/-! The checked inclusion bound available under a fresh sleepy regime. -/

namespace DecoupledConsensusModel.Proofs

open DecoupledConsensusModel.Statements.Instantiation
open DecoupledConsensusModel.Statements
open DecoupledConsensusModel.Statements.Generic
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal
open DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Proofs.HealingSurface.Handover
open DecoupledConsensusModel.Proofs.W4StableWrite
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Internal.PhaseGrades

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem fresh_round_length_eq (S : Setup V) :
    S.a 1 - S.a 0 = Statements.Instantiation.roundLength S := by
  rw [NamedOutageClosure.a_succ_roundLength S 0]
  exact add_sub_cancel_left _ _

private theorem fresh_action_lt_vote_two_after (S : Setup V) (r : Round) :
    S.a r < Protocol.vote_time S.E (S.hc.opening_slot r + 1 + 1) := by
  refine lt_of_lt_of_le
    (Protocol.action_lt_proposal_time_two_after S r) ?_
  exact le_of_lt (Protocol.proposal_time_lt_vote_time S.E _)

private theorem fresh_slot_before_next_opening (S : Setup V) (s : Slot) :
    s < S.hc.opening_slot (S.hc.round_of s + 1) := by
  have hR : 0 < S.hc.R :=
    lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two
  have hmod := Nat.mod_lt s hR
  unfold Protocol.HealConfig.round_of Protocol.HealConfig.opening_slot
  calc
    s = s % S.hc.R + S.hc.R * (s / S.hc.R) :=
      (Nat.mod_add_div s S.hc.R).symm
    _ < S.hc.R + S.hc.R * (s / S.hc.R) := Nat.add_lt_add_right hmod _
    _ = (s / S.hc.R + 1) * S.hc.R := by ring

private theorem fresh_confirmation_time_mono_slots (S : Setup V) {a b : Slot}
    (hab : a ≤ b) :
    Protocol.confirmation_time S.E a ≤ Protocol.confirmation_time S.E b := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ,
    Protocol.confirmation_time_eq_support_cutoff_succ]
  exact Proofs.Optimistic.support_cutoff_mono S.E (Nat.add_le_add_right hab 1)


/-- A fresh sleepy regime inherits the established stable inclusion bound. -/
theorem stableIncludedFresh_slow_concrete (S : Setup V) :
    ∀ rho t₀,
      Generic.FreshSleepyRegime (DecoupledConsensusModel.Execution.spec S)
        (Instantiation.env S) (Instantiation.interface S)
        (Instantiation.constants S) rho t₀ →
      Generic.IncludedFrom (DecoupledConsensusModel.Execution.spec S)
        (Instantiation.interface S) rho
        (Instantiation.interface S).stable t₀
        (Instantiation.constants S).stableInclusionDelay := by
  intro rho t₀ h
  have hs := sleepyRegime_of_generic S rho t₀ h.toSleepyRegime
  have hr := recoveredBy_of_generic S rho t₀ h.start
  simpa [stableInclusionDelay_eq_constant] using
    included_of_named S (available_stableIncluded_any S rho t₀ hs hr)

theorem storeGrade_g2_of_relativeCarrierWindow_and_voterCover
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    {q : Round} (hq : 0 < q)
    (hhor : domain S.E S.hc q .g2 ≤ rho.horizon)
    (hforming : Internal.NamedOutageEntry.GradeFormingMajority S rho q)
    (hwindow : RelativeCarrierWindowAt S rho (q - 1) .g2)
    {P : Block V}
    (hcover : ∀ u ∈ Internal.NamedOutageEntry.honestRoundVoters S rho (q - 1),
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
          core (domain S.E S.hc q .g2)
          (early S.E S.hc q .g2) w hw huHon (r := q - 1) hzraw'
      simpa only [DecoupledConsensusModel.Protocol.token, hyround] using hzupper
    · change Protocol.head_covers n.st.core.T P y.confirmed = true
      rw [hyconfirmed]
      simp only [Protocol.head_covers]
      rw [show Block.find? n.st.core.T
          (actionSGBlockAt S rho u (q - 1)).root =
            some (actionSGBlockAt S rho u (q - 1)) by
        simpa only [n, hpred] using hyfind]
      exact hcover u hu
    · have hclean := NamedOutageClosure.honest_rawView_clean S rho
        core (domain S.E S.hc q .g2) la
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
          core (domain S.E S.hc q .g2)
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
    · refine Finset.mem_union_right _ ?_
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
        obtain ⟨a, haround, hval, hemit, _, hconfirmed, _, hzlower, hzupper⟩ :=
          NamedOutageClosure.honest_rawInput_is_own_round_vote S rho
            core (domain S.E S.hc q .g2)
            (late S.E S.hc q .g2) w hw huHon (r := q - 1) hzraw'
        by_cases huVoter : u ∈ Internal.NamedOutageEntry.honestRoundVoters S rho (q - 1)
        · obtain ⟨earlyVote, hearly, hearlyRound, _, hfind⟩ :=
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
            S rho core u huHon (q - 1)
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
            exact hcover u huVoter))
        · have hwindow : z.round ∈ Protocol.latest_window S.hc.η_SG q :=
            NamedOutageClosure.mem_latest_window (by
              simpa only [hpred] using hzlower)
              (by simpa only [Nat.succ_eq_add_one, hpred] using Nat.lt_succ_of_le hzupper)
          have hzvote : u ∈ Internal.NamedOutageEntry.honestRoundVoters S rho z.round :=
            (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u z.round).mpr
              ⟨huHon, a, hval, haround, hemit⟩
          exact Proofs.NamedOutageInputs.stale_of_eligible_vote S rho
            hwindow hzvote (by simpa only [hpred] using huVoter)
      · have hclean0 := NamedOutageClosure.honest_rawView_clean S rho
          core (domain S.E S.hc q .g2) la
          w hw huHon (q - 1) 0
        rw [hpred] at hclean0
        exact False.elim (hkey
          (hclean0 x hx y hy (Nat.zero_le _) hround))
    · exact Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, huHon⟩)
  change DecoupledConsensusModel.Protocol.gradeBool S.E gv F S.hc.η_SG q ea la P = true
  exact phaseGrade_of_gradeFormingMajority S rho q gv F P ea la
    hforming hpositive hopposing


/-- A covered current round gives the next duty its local G2 cover under a
grade-forming majority. Earlier votes can be stale. -/
theorem localG2Cover_of_freshVoterCover
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    {q : Round} (_hq : 0 < q)
    (hhor : domain S.E S.hc (q + 1) .g2 ≤ rho.horizon)
    (hforming : Internal.NamedOutageEntry.GradeFormingMajority S rho (q + 1))
    (hwindow : RelativeCarrierWindowAt S rho q .g2)
    {P : Block V}
    (hcover : ∀ u ∈ Internal.NamedOutageEntry.honestRoundVoters S rho q,
      Block.Preceq P (actionSGBlockAt S rho u q))
    {w : V} (hw : w ∈ rho.honest) :
    W4StableWrite.LocalG2CoverAtDutyRound S rho (q + 1) P w := by
  classical
  have hvoters : (Internal.NamedOutageEntry.honestRoundVoters S rho q).Nonempty := by
    by_contra hne
    have hempty : Internal.NamedOutageEntry.honestRoundVoters S rho q = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    have hlt := hforming
    unfold Internal.NamedOutageEntry.GradeFormingMajority at hlt
    rw [Nat.add_sub_cancel, hempty] at hlt
    simp only [Electorate.weightOf, Finset.sum_empty] at hlt
    omega
  obtain ⟨u, hu⟩ := hvoters
  obtain ⟨y, hy, hyround, hyconfirmed, hyfind⟩ := hwindow w hw u hu
  have hmemVote : actionSGBlockAt S rho u q ∈
      (readAt S rho (domain S.E S.hc (q + 1) .g2) w).st.core.T := by
    exact Proofs.Records.mem_of_bind_find? (o := some (actionSGBlockAt S rho u q).root)
      (by simpa only [relativePhaseRead] using hyfind)
  have hpc := (parentClosed_iff (readAt S rho
      (domain S.E S.hc (q + 1) .g2) w).st.core).mp
    (Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
      (domain S.E S.hc (q + 1) .g2) w)
  have hmem : P ∈ (readAt S rho
      (domain S.E S.hc (q + 1) .g2) w).st.core.T :=
    Proofs.Records.mem_of_preceq hpc.2 P (actionSGBlockAt S rho u q)
      hmemVote (hcover u hu)
  have hgrade := storeGrade_g2_of_relativeCarrierWindow_and_voterCover
    S core (Nat.succ_pos q) hhor hforming hwindow hcover hw
  have hlocal := W4StableWrite.localG2CoverAtDuty_of_storeGrade S hmem hgrade
  simpa only [W4StableWrite.localG2CoverAtDuty_eq_round] using hlocal

/-- A generic fresh majority at an action time yields the named majority at
that round when its predecessor action is inside the run. -/
theorem gradeFormingMajority_of_freshAt
    (S : Setup V) (rho : Run V)
    (sch : NamedScheduleWellFormed S rho) {r : Round}
    (hr : 0 < r) (hcovered : Internal.NamedOutageEntry.RoundCovered S rho r)
    (hfresh : Generic.FreshMajority (E S) rho.honest (C S) (S.a r)) :
    Internal.NamedOutageEntry.GradeFormingMajority S rho r := by
  have hs := hfresh
  unfold Generic.FreshMajority at hs
  have hstale := staleAwake_eq S rho hr
  have ha : S.a r - L S = S.a (r - 1) := by
    have hprevRound : r - 1 + 1 = r :=
      Nat.sub_add_cancel (Nat.succ_le_iff.mpr hr)
    rw [← hprevRound, NamedOutageClosure.a_succ_roundLength]
    unfold L
    rw [fresh_round_length_eq S]
    exact add_sub_cancel_right _ _
  have hprev := awakeAt_action S rho (r - 1)
  have hs' :
      (E S).electorate.weightOf ((Finset.univ \ rho.honest) ∪
        (awakeIn (E S) rho.honest
            (S.a r - (S.hc.η_SG : Time) * L S) (S.a r - L S) \
          awakeAt (E S) rho.honest (S.a r - L S))) <
        (E S).electorate.weightOf (awakeAt (E S) rho.honest (S.a r - L S)) := by
    simpa [C, Instantiation.constants] using hs
  rw [hstale, ha, hprev] at hs'
  have hawake : Internal.NamedOutageEntry.AwakeGradeMajority S rho r := by
    simpa [Internal.NamedOutageEntry.AwakeGradeMajority, E, Instantiation.env]
      using hs'
  exact NamedOutageClosure.gradeFormingMajority_of_awakeAt S rho sch hr
    hcovered hawake

/-- Restrict a phase window transport result to the immediately preceding
round's emitted honest voters. -/
theorem relativeCarrierWindowAt_of_transport
    (S : Setup V) {rho : Run V} {q : Round}
    (htransport : ∀ w ∈ rho.honest, ∀ u ∈ rho.honest,
      ∀ k ∈ Protocol.latest_window S.hc.η_SG (q + 1),
      (S.node u).awake k = true →
      ∃ y ∈ interpretedInputs
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (q + 1) .g2) w).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (q + 1) .g2) w).st.core.F
          S.hc.η_SG (q + 1) (early S.E S.hc (q + 1) .g2) u,
        y.round = k ∧
        y.confirmed = some (actionSGBlockAt S rho u k).root ∧
        Block.find?
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (q + 1) .g2) w).st.core.T
          (actionSGBlockAt S rho u k).root =
            some (actionSGBlockAt S rho u k)) :
    RelativeCarrierWindowAt S rho q .g2 := by
  intro w hw u hu
  obtain ⟨huHon, a, _, haround, hemit⟩ :=
    (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u q).mp hu
  have hawake : (S.node u).awake q = true := by
    simpa only [haround] using Proofs.Optimistic.emits_attest_awake S hemit
  have hwindow : q ∈ Protocol.latest_window S.hc.η_SG (q + 1) := by
    simpa only [Nat.add_sub_cancel] using
      Protocol.pred_mem_latest_window S.hc.η_SG (q + 1)
        S.hc.η_SG_ge_one (Nat.succ_pos q)
  exact htransport w hw u huHon q hwindow hawake

/-- GST-zero delivery puts each round-`q` voter into every next G2 reader's
interpreted view. -/
theorem relativeCarrier_fastDuty_gstZero
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {q : Round} (_hq : 0 < q)
    (hhor : S.a (q + 1) ≤ rho.horizon) :
    RelativeCarrierWindowAt S rho q .g2 := by
  let d := q + 1
  have hdpos : 0 < d := Nat.succ_pos q
  have hdelivery : NamedHealthyPrefixDelivery S rho rho.horizon :=
    NamedGSTZeroHealthy.healthyPrefixDelivery_of_gstZero S rho
      h.core h.gstZero
  have hprevHor : S.a (d - 1) ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.sub_le d 1)).trans hhor
  have hawake : AwakeWindowMajority S.E (fun v => (S.node v).awake)
      rho.honest S.hc.η_SG d := h.windows d hdpos hprevHor
  obtain ⟨x, hx⟩ := Protocol.honest_nonempty_of_honestCommittees
    h.committees
  have hlastHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot d) ≤ rho.horizon := by
    simpa only [Proofs.HealingSurface.opening_confirmation_time_eq_action S d]
      using hhor
  have hdslot : 1 ≤ S.hc.opening_slot d + 1 := Nat.succ_le_succ (Nat.zero_le _)
  have hsg : ∀ j, 0 ≤ j → j < d → ∀ u ∈ rho.honest,
      NamedRun.emits S rho u
        (Object.attest (actionAttestationAt S rho u j)) (S.a j) →
      Block.Preceq (actionSGBlockAt S rho u j)
        (Protocol.voteDutyHead S rho x (S.hc.opening_slot d + 1)) := by
    intro j _ hjd u hu hemit
    have hact : S.a j < Protocol.vote_time S.E
        (S.hc.opening_slot d + 1 + 1) :=
      lt_of_le_of_lt (Assembly.a_mono S (Nat.le_of_lt hjd))
        (Protocol.action_lt_vote_time_two_after S d)
    exact (WeakGenesis.actionSources_preceq_voteDutyHead_of_gstZero S
      h.core h.committees h.gstZero h.windows hlastHor hdslot
      (Nat.le_refl _) hx j hact).1 u hu hemit
  have hroots : ∀ w ∈ rho.honest,
      Block.Preceq (Protocol.get_fg_root
        (actionStoreAt S rho w d).st.core.toHealing.toFG)
        (Protocol.voteDutyHead S rho x (S.hc.opening_slot d + 1)) := by
    intro w hw
    have hact : S.a d < Protocol.vote_time S.E
        (S.hc.opening_slot d + 1 + 1) :=
      Protocol.action_lt_vote_time_two_after S d
    exact (WeakGenesis.actionSources_preceq_voteDutyHead_of_gstZero S
      h.core h.committees h.gstZero h.windows hlastHor hdslot
      (Nat.le_refl _) hx d hact).2 w hw |>.1
  have hcap : domain S.E S.hc d .g2 ≤ rho.horizon :=
    (FrameForward.domain_le_a S d .g2).trans hhor
  apply relativeCarrierWindowAt_of_transport S
  exact Proofs.HealingSurface.WeakJoint.relativeCarrierWindowAt_of_awakeWindowHistory_of_delivery
    S h.core hdelivery le_rfl hdpos (Nat.zero_le _) hawake hsg hroots
      .g2 hcap

/-- The prepared continuation delivers the immediately preceding SG round at
the fast duty, including when older window votes belong to bootstrap. -/
theorem relativeCarrier_fastDuty_afterGST
    (S : Setup V) {rho : Run V} (core : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {Pseed : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start Pseed cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap Pseed.erase)
    {q : Round} (hstartq : start < S.hc.opening_slot q)
    (hhor : S.a (q + 1) ≤ rho.horizon) :
    RelativeCarrierWindowAt S rho q .g2 := by
  classical
  obtain ⟨x, hx⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
  let d := q + 1
  let last := S.hc.opening_slot d
  let target := last + 1
  have hcutq : base + S.hc.η_SG < q :=
    Nat.lt_of_mul_lt_mul_right (hboot.settled.trans_lt hstartq)
  have hcutd : base + S.hc.η_SG ≤ d :=
    (Nat.le_of_lt hcutq).trans (Nat.le_succ q)
  have hdpos : 0 < d := Nat.succ_pos q
  have hspan : base ≤ d - S.hc.η_SG := by
    apply Nat.le_sub_of_add_le
    omega
  have hlastHor : Protocol.confirmation_time S.E last ≤ rho.horizon := by
    simpa only [last, d, Proofs.HealingSurface.opening_confirmation_time_eq_action]
      using hhor
  have hopenqd : S.hc.opening_slot q ≤ last :=
    Nat.mul_le_mul_right S.hc.R (Nat.le_succ q)
  have hstartTarget : start ≤ target :=
    (hstartq.le.trans hopenqd).trans (Nat.le_succ _)
  have hnextVote : S.a d < Protocol.vote_time S.E (target + 1) :=
    fresh_action_lt_vote_two_after S d
  have houts (r : Round) (hr : base + S.hc.η_SG ≤ r)
      (hrt : S.a r < Protocol.vote_time S.E (target + 1)) :=
    SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_core
      S core hcom hboot hawake hfinality hlastHor hstartTarget
      (Nat.le_refl target) hx r hr hrt
  have hseed := (SettledBootstrapPreparedV4.protectedVoteSlots_core
    S core hcom hboot hawake hfinality hlastHor target hstartTarget
      (Nat.le_refl target)).1
  have hsg : ∀ j, base ≤ j → j < d → ∀ u ∈ rho.honest,
      NamedRun.emits S rho u
        (Object.attest (actionAttestationAt S rho u j)) (S.a j) →
      Block.Preceq (actionSGBlockAt S rho u j)
        (voterHeadAt S rho x target) := by
    intro j hbasej hjd u hu hemit
    by_cases hold : j < base + S.hc.η_SG
    · exact Block.preceq_trans (hboot.sgBoot j hbasej hold u hu hemit)
        (hseed.heads x hx)
    · have hjtime : S.a j < Protocol.vote_time S.E (target + 1) :=
        lt_of_le_of_lt (Assembly.a_mono S hjd.le) hnextVote
      exact (houts j (Nat.le_of_not_gt hold) hjtime).1 u hu hemit
  have hroots : ∀ w ∈ rho.honest,
      Block.Preceq (Protocol.get_fg_root
        (actionStoreAt S rho w d).st.core.toHealing.toFG)
        (voterHeadAt S rho x target) := by
    intro w hw
    exact ((houts d hcutd hnextVote).2 w hw).1
  have hprevHor : S.a (d - 1) ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.sub_le d 1)).trans hhor
  have hawakeD := hawake d hcutd hprevHor
  have hdomainHor : domain S.E S.hc d .g2 ≤ rho.horizon :=
    (FrameForward.domain_le_a S d .g2).trans hhor
  have htransport :=
    Proofs.HealingSurface.WeakJoint.relativeCarrierWindowAt_of_awakeWindowHistory_w
      S core (NamedOutageClosure.healthyWindowDelivery_after_gst S rho core)
      (le_refl _) (le_refl _) hdpos hspan
      (fun j hbasej _ => hboot.basePost.trans (Assembly.a_mono S hbasej))
      hawakeD hsg hroots .g2 hdomainHor
  exact relativeCarrierWindowAt_of_transport S htransport

/-- Write a covered proposal at the next duty from the one-round grade. -/
theorem stableWrite_of_freshCover
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    (sch : ScheduleWellFormed S rho) {q : Round} (hq : 0 < q)
    (hhor : S.a (q + 1) ≤ rho.horizon)
    {B : NamedBlock V}
    (hcover : W4Cover S rho B q)
    (hwindow : RelativeCarrierWindowAt S rho q .g2)
    (hforming : Internal.NamedOutageEntry.GradeFormingMajority S rho (q + 1))
    (hviable : ∀ v ∈ rho.honest,
      ProposalViableAtDutyRound S rho (q + 1) B.erase v) :
    ∀ v ∈ rho.honest,
      Block.Preceq B.erase
        (rho.storeAt S v (dutyTime S (q + 1))).latest_stable := by
  have hdom : domain S.E S.hc (q + 1) .g2 ≤ rho.horizon :=
    (FrameForward.domain_le_a S _ .g2).trans hhor
  have hduty : dutyTime S (q + 1) ≤ rho.horizon :=
    (dutyTime_le_action S _).trans hhor
  apply stable_preceq_at_duty_of_dutyCover S core sch (Nat.succ_pos q)
    (by
      intro v hv
      exact dutyCoverAt_of_viable_and_localG2 S (hviable v hv)
        (localG2Cover_of_freshVoterCover S core hq hdom hforming
          hwindow hcover hv)) hduty

theorem stableWrite_anySlot_fresh_gstZero
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {s : Slot} (hs : 0 < s) (hprop : S.E.proposer s ∈ rho.honest)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B)
    {q : Round} (hq : 0 < q) (hsq : s < S.hc.opening_slot q)
    (hconfq : Protocol.confirmation_time S.E s ≤ S.a q)
    (hhor : S.a (q + 1) ≤ rho.horizon)
    (hforming : Internal.NamedOutageEntry.GradeFormingMajority S rho (q + 1)) :
    ∀ v ∈ rho.honest,
      Block.Preceq B.erase
        (rho.storeAt S v
          (W4StableWrite.dutyTime S (q + 1))).latest_stable := by
  let d := q + 1
  have hdpos : 0 < d := Nat.succ_pos q
  have hqd : q < d := Nat.lt_succ_self q
  have hqhor : S.a q ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_add_right q _)).trans hhor
  have hconfHor : Protocol.confirmation_time S.E s ≤ rho.horizon :=
    hconfq.trans hqhor
  have hsafe : GSTZeroGuarantees S rho :=
    gstZeroGuarantees_of_weakGenesis S rho h
  have hreads : HonestProposalReadSafety S rho s :=
    hsafe.proposalReads s hs hconfHor hprop
  have hsource : ∀ v ∈ rho.honest,
      (rho.storeAt S v (Protocol.confirmation_time S.E s)).live_confirmed =
        B.erase := by
    intro v hv
    exact WeakGenesis.honestProposal_liveConfirmed_named_of_gstZero
      S h hs hconfHor hprop hB v hv
  have hlive : ∀ j : Round, q ≤ j → j < d →
      ∀ v ∈ rho.honest,
        Block.Preceq B.erase
          (actionStoreAt S rho v j).st.core.live_confirmed := by
    intro j hqj hjd v hv
    have hjhor : S.a j ≤ rho.horizon :=
      (Assembly.a_mono S (Nat.le_of_lt hjd)).trans hhor
    have htj : Protocol.confirmation_time S.E s ≤ S.a j :=
      hconfq.trans (Assembly.a_mono S hqj)
    have hmono := hsafe.liveMonotone v hv
      (Protocol.confirmation_time S.E s) (S.a j) htj
    rw [w4_actionStore_liveConfirmed_eq_storeAt S
      h.core.toNamedScheduleWellFormed hv j hjhor, ← hsource v hv]
    exact hmono
  have hclear : ∀ j : Round, q ≤ j → j < d →
      ∀ v ∈ rho.honest,
        nodeClear S (actionReadAt S rho v j) j
          (actionStoreAt S rho v j).st.core.live_confirmed = true := by
    intro j hqj hjd v hv
    have hjpos : 0 < j := Nat.lt_of_lt_of_le hq hqj
    have hjhor : S.a j ≤ rho.horizon :=
      (Assembly.a_mono S (Nat.le_of_lt hjd)).trans hhor
    have hnextslot : S.hc.opening_slot j + 1 ≤
        S.hc.opening_slot (j + 1) := by
      simp only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
      exact Nat.add_le_add_left
        ((by decide : (1 : Nat) ≤ 2).trans S.hc.R_ge_two)
        (j * S.hc.R)
    have hnext : Protocol.confirmation_time S.E
        (S.hc.opening_slot j + 1) ≤ rho.horizon :=
      (fresh_confirmation_time_mono_slots S hnextslot).trans (by
        simpa only [opening_confirmation_time_eq_action] using
          (Assembly.a_mono S (Nat.succ_le_of_lt hjd)).trans hhor)
    exact w4_nodeClear_liveConfirmed_gstZero S h hjpos hv hjhor hnext
  have hcoverQ : W4Cover S rho B q := by
    intro u hu
    have huHon :=
      ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u q).mp hu).1
    exact actionSGCover_of_liveBound S (hlive q le_rfl (Nat.lt_succ_self q))
      (hclear q le_rfl (Nat.lt_succ_self q)) u huHon
  have hwindow : RelativeCarrierWindowAt S rho q .g2 :=
    relativeCarrier_fastDuty_gstZero S h hq hhor
  have hslotDuty : s ≤ S.hc.opening_slot d - 1 := by
    have hopen : S.hc.opening_slot q < S.hc.opening_slot d :=
      Nat.mul_lt_mul_of_pos_right hqd
        (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
    exact Nat.le_sub_one_of_lt (hsq.trans hopen)
  have hvoteHor : Protocol.vote_time S.E
      (S.hc.opening_slot d - 1) ≤ rho.horizon := by
    exact (Protocol.vote_time_mono_slots S.E (Nat.sub_le _ 1)).trans
      ((Protocol.vote_time_le_confirmation_time S.E _).trans
        (by simpa only [opening_confirmation_time_eq_action] using hhor))
  have hbelow : ∀ v ∈ rho.honest,
      Block.Preceq B.erase
        (voterHeadAt S rho v (S.hc.opening_slot d - 1)) := by
    intro v hv
    exact hreads.vote B hB _ hslotDuty hvoteHor v hv
  have hviable := stableViableAtDuty_gstZero_of_head S h hdpos hhor hbelow
  exact stableWrite_of_freshCover S h.core h.core.toNamedScheduleWellFormed
    hq hhor hcoverQ hwindow hforming hviable


theorem stableWrite_anySlot_fresh_afterGST
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {Pseed : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start Pseed cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap Pseed.erase)
    (hphase : PhaseShiftSafety S rho (base + S.hc.η_SG) start Pseed.erase)
    {s : Slot} (hstarts : start < s)
    (hprop : S.E.proposer s ∈ rho.honest)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B)
    {q : Round} (hsq : s < S.hc.opening_slot q)
    (hconfq : Protocol.confirmation_time S.E s ≤ S.a q)
    (hhor : S.a (q + 1) ≤ rho.horizon)
    (hforming : Internal.NamedOutageEntry.GradeFormingMajority S rho (q + 1)) :
    ∀ v ∈ rho.honest,
      Block.Preceq B.erase
        (rho.storeAt S v
          (W4StableWrite.dutyTime S (q + 1))).latest_stable := by
  let d := q + 1
  have hqpos : 0 < q := by
    by_contra hn
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos hn
    simp [hq0, Protocol.HealConfig.opening_slot] at hsq
  have hdpos : 0 < d := Nat.succ_pos q
  have hqd : q < d := Nat.lt_succ_self q
  have hqhor : S.a q ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_add_right q _)).trans hhor
  have hconfHor : Protocol.confirmation_time S.E s ≤ rho.horizon :=
    hconfq.trans hqhor
  have hreads := hphase.honestProposalReads s hstarts hconfHor hprop
  obtain ⟨B', hB', hsource⟩ :=
    hphase.honestProposalLive s hstarts hconfHor hprop
  have hBB' : B' = B := Option.some.inj (hB'.symm.trans hB)
  subst B'
  have hstartConf : Protocol.confirmation_time S.E start ≤
      Protocol.confirmation_time S.E s :=
    fresh_confirmation_time_mono_slots S hstarts.le
  have hlive : ∀ j : Round, q ≤ j → j < d →
      ∀ v ∈ rho.honest,
        Block.Preceq B.erase
          (actionStoreAt S rho v j).st.core.live_confirmed := by
    intro j hqj hjd v hv
    have hjhor : S.a j ≤ rho.horizon :=
      (Assembly.a_mono S (Nat.le_of_lt hjd)).trans hhor
    have htj : Protocol.confirmation_time S.E s ≤ S.a j :=
      hconfq.trans (Assembly.a_mono S hqj)
    have hmono := hphase.liveMonotone v hv
      (Protocol.confirmation_time S.E s) (S.a j) hstartConf htj
    rw [w4_actionStore_liveConfirmed_eq_storeAt S
      core.toNamedScheduleWellFormed hv j hjhor]
    rw [hsource v hv] at hmono
    exact hmono
  have hstartq : start < S.hc.opening_slot q := hstarts.trans hsq
  have hcutq : base + S.hc.η_SG < q :=
    Nat.lt_of_mul_lt_mul_right (hboot.settled.trans_lt hstartq)
  have hclear : ∀ j : Round, q ≤ j → j < d →
      ∀ v ∈ rho.honest,
        nodeClear S (actionReadAt S rho v j) j
          (actionStoreAt S rho v j).st.core.live_confirmed = true := by
    intro j hqj hjd v hv
    have hjhor : S.a j ≤ rho.horizon :=
      (Assembly.a_mono S (Nat.le_of_lt hjd)).trans hhor
    have hcutj : base + S.hc.η_SG ≤ j := (Nat.le_of_lt hcutq).trans hqj
    have hstartj : start ≤ S.hc.opening_slot j + 1 :=
      (hstartq.le.trans (Nat.mul_le_mul_right S.hc.R hqj)).trans
        (Nat.le_succ _)
    have hnextslot : S.hc.opening_slot j + 1 ≤
        S.hc.opening_slot (j + 1) := by
      simp only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
      exact Nat.add_le_add_left
        ((by decide : (1 : Nat) ≤ 2).trans S.hc.R_ge_two)
        (j * S.hc.R)
    have hnext : Protocol.confirmation_time S.E
        (S.hc.opening_slot j + 1) ≤ rho.horizon :=
      (fresh_confirmation_time_mono_slots S hnextslot).trans (by
        simpa only [opening_confirmation_time_eq_action] using
          (Assembly.a_mono S (Nat.succ_le_of_lt hjd)).trans hhor)
    exact W4StableWrite.w4_preparedNodeClear_liveConfirmed S core hcom
      hboot hawake hfinality hcutj hstartj hjhor hnext hv
  have hcoverQ : W4Cover S rho B q := by
    intro u hu
    have huHon :=
      ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u q).mp hu).1
    exact actionSGCover_of_liveBound S (hlive q le_rfl (Nat.lt_succ_self q))
      (hclear q le_rfl (Nat.lt_succ_self q)) u huHon
  have hwindow : RelativeCarrierWindowAt S rho q .g2 :=
    relativeCarrier_fastDuty_afterGST S core hcom hboot hawake hfinality
      hstartq hhor
  have hslotPrev : s ≤ S.hc.opening_slot d - 1 := by
    have hopen : S.hc.opening_slot q < S.hc.opening_slot d :=
      Nat.mul_lt_mul_of_pos_right hqd
        (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
    exact Nat.le_sub_one_of_lt (hsq.trans hopen)
  have hslotOpen : s ≤ S.hc.opening_slot d :=
    hsq.le.trans (Nat.mul_le_mul_right S.hc.R (Nat.le_of_lt hqd))
  have hdutyHor : W4StableWrite.dutyTime S d ≤ rho.horizon :=
    (W4StableWrite.dutyTime_le_action S d).trans hhor
  have hopenHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot d) ≤ rho.horizon := by
    simpa only [opening_confirmation_time_eq_action] using hhor
  have hvotePrev : Protocol.vote_time S.E
      (S.hc.opening_slot d - 1) ≤ rho.horizon :=
    (W4StableWrite.voteTime_le_supportCutoff_mono S (Nat.sub_le _ 1)).trans hdutyHor
  have hvoteOpen : Protocol.vote_time S.E
      (S.hc.opening_slot d) ≤ rho.horizon :=
    (W4StableWrite.voteTime_le_supportCutoff_mono S (Nat.le_refl _)).trans hdutyHor
  have hviable : ∀ v ∈ rho.honest,
      W4StableWrite.ProposalViableAtDutyRound S rho d B.erase v := by
    intro v hv
    have hdEq : d - 1 + 1 = d := Nat.sub_add_cancel hdpos
    have hs : start < S.hc.opening_slot (d - 1 + 1) := by
      rw [hdEq]
      exact hstartq.trans (Nat.mul_lt_mul_of_pos_right hqd
        (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two))
    have hhead : W4StableWrite.DutyHeadWitness S rho (d - 1) v := by
      rw [W4StableWrite.DutyHeadWitness, hdEq]
      exact W4StableWrite.dutyHeadWitnessAll_closed S rho core d hdpos v hv
    have hp := W4StableWrite.proposalViableAtDuty_of_package_and_head
      S core hcom hboot hawake hfinality hs
      (by simpa only [hdEq] using hdutyHor)
      (by simpa only [hdEq] using hopenHor) hv hhead
      (by simpa only [hdEq] using hreads.vote B hB _ hslotPrev hvotePrev v hv)
      (by simpa only [hdEq] using hreads.vote B hB _ hslotOpen hvoteOpen v hv)
    simpa only [W4StableWrite.ProposalViableAtDutyRound,
      W4StableWrite.ProposalViableAtDuty, hdEq] using hp
  exact stableWrite_of_freshCover S core core.toNamedScheduleWellFormed
    hqpos hhor hcoverQ hwindow hforming hviable


/-- The fast duty is inside the pinned one-round deadline. -/
theorem fastDuty_before_inclusionDeadline (S : Setup V) (s : Slot) :
    S.a (S.hc.round_of s + 1 + 1) ≤
      Protocol.proposal_time S.E s +
        (Instantiation.constants S).fastStableInclusionDelay := by
  have hlow : S.hc.round_of s * S.hc.R ≤ s := by
    have h := Nat.le_add_left (S.hc.R * (s / S.hc.R)) (s % S.hc.R)
    rw [Nat.mod_add_div] at h
    simpa [Protocol.HealConfig.round_of, Nat.mul_comm] using h
  have hlow' : ((S.hc.round_of s * S.hc.R : Nat) : Time) ≤ (s : Time) := by
    exact_mod_cast hlow
  simp only [Setup.a, Protocol.HealConfig.a, Protocol.HealConfig.opening_slot,
    Protocol.proposal_time, Env.t, slotStart, Instantiation.constants]
  push_cast at hlow' ⊢
  have hΔ : (0 : Time) < S.E.Δ := S.E.Δ_pos
  have hscaled := Int.mul_le_mul_of_nonneg_left hlow'
    (show (0 : Time) ≤ 4 * S.E.Δ by nlinarith)
  ring_nf at hlow' hscaled ⊢
  nlinarith

private theorem fresh_positive_slot (S : Setup V) {s : Slot}
    (hs : 0 < (legacyInterface S).proposalTime s) : 0 < s := by
  cases s with
  | zero =>
      simp [legacyInterface, Statements.«instance», Protocol.proposal_time,
        Env.t, slotStart] at hs
  | succ k => exact Nat.zero_lt_succ _

private theorem fresh_opening_before_boundary (S : Setup V)
    {m q : Round} {s : Slot} (hmq : m ≤ q)
    (hs : healingBoundaryTime S q < Protocol.proposal_time S.E s) :
    S.hc.opening_slot m < s := by
  have hm0 : Protocol.proposal_time S.E (S.hc.opening_slot m) ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q) :=
    Protocol.proposal_time_mono S.E
      (Nat.mul_le_mul_right S.hc.R hmq)
  have hq : Protocol.proposal_time S.E (S.hc.opening_slot q) ≤
      healingBoundaryTime S q := by
    unfold healingBoundaryTime
    exact (Protocol.proposal_time_lt_vote_time S.E
      (S.hc.opening_slot q)).le.trans
      (Protocol.vote_time_mono_slots S.E
        (Nat.le_add_right (S.hc.opening_slot q) 2))
  have hslot : Protocol.proposal_time S.E (S.hc.opening_slot m) <
      Protocol.proposal_time S.E s := (hm0.trans hq).trans_lt hs
  apply Nat.lt_of_not_ge
  intro hle
  exact (not_lt_of_ge (Protocol.proposal_time_mono S.E hle)) hslot

theorem available_stableIncluded_fresh (S : Setup V) :
    ∀ rho t₀, SleepyRegime S (legacyInterface S) (legacyConstants S) rho t₀ →
      RecoveredBy S (legacyInterface S) (legacyConstants S) rho t₀ →
      (∀ t, t₀ ≤ t → (C S).participationLag ≤ t →
        t - (C S).participationLag ≤ rho.horizon →
        Generic.FreshMajority (E S) rho.honest (C S) t) →
        Included S (legacyInterface S) rho (legacyInterface S).stable t₀
          (Instantiation.constants S).fastStableInclusionDelay := by
  intro rho t₀ hsleep hrecovered hfresh s hs hprop hdeadline
  let q : Round := S.hc.round_of s + 1
  let d : Round := q + 1
  let T : Time := Protocol.proposal_time S.E s +
    (Instantiation.constants S).fastStableInclusionDelay
  have hqpos : 0 < q := Nat.zero_lt_succ _
  have hqd : q < d := Nat.lt_succ_self q
  have hsq : s < S.hc.opening_slot q := fresh_slot_before_next_opening S s
  have hconfq : Protocol.confirmation_time S.E s ≤ S.a q := by
    exact (fresh_confirmation_time_mono_slots S hsq.le).trans
      (by rw [opening_confirmation_time_eq_action])
  have hwriteTime : S.a d ≤ T :=
    fastDuty_before_inclusionDeadline S s
  have hhor : S.a d ≤ rho.horizon :=
    hwriteTime.trans (by simpa only [T, legacyInterface] using hdeadline)
  have hqhor : S.a q ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_add_right q _)).trans hhor
  have hconfHor : Protocol.confirmation_time S.E s ≤ rho.horizon :=
    hconfq.trans hqhor
  have hconfirmedHor : (legacyInterface S).proposalTime s +
      (legacyConstants S).confirmationDelay ≤ rho.horizon := by
    simpa [legacyInterface, legacyConstants, Statements.ourConstants,
      Protocol.confirmation_time, Protocol.proposal_time] using hconfHor
  obtain ⟨B, hHon, _⟩ := available_confirmedIncluded S rho t₀
    hsleep hrecovered s hs hprop hconfirmedHor
  have hB : proposedBlockAt S rho s = some B := hHon.2
  have hlagEq : S.a d - (C S).participationLag = S.a q := by
    change S.a (q + 1) - (S.a 1 - S.a 0) = S.a q
    rw [NamedOutageClosure.a_succ_roundLength]
    rw [fresh_round_length_eq S]
    ring
  have hlag : (C S).participationLag ≤ S.a d := by
    have hnonneg : 0 ≤ S.a d - (C S).participationLag := by
      rw [hlagEq]
      exact Proofs.HealingLemmas.a_nonneg S q
    exact sub_nonneg.mp hnonneg
  have ht₀ : t₀ ≤ S.a d := by
    have hpropTime : Protocol.proposal_time S.E s ≤ S.a q :=
      (Protocol.proposal_time_le_confirmation_time S.E s).trans hconfq
    have hqdTime : S.a q ≤ S.a d := Assembly.a_mono S (Nat.le_succ q)
    exact (le_of_lt (by simpa only [legacyInterface] using hs)).trans
      (hpropTime.trans hqdTime)
  have hfreshD : Generic.FreshMajority (E S) rho.honest (C S) (S.a d) :=
    hfresh (S.a d) ht₀ hlag (by rw [hlagEq]; exact hqhor)
  have hforming : Internal.NamedOutageEntry.GradeFormingMajority S rho d := by
    have sch : NamedScheduleWellFormed S rho :=
      hsleep.execution.toNamedScheduleWellFormed
    exact gradeFormingMajority_of_freshAt S rho sch (Nat.succ_pos q)
      (Or.inl ⟨Proofs.HealingLemmas.a_nonneg S d, hhor⟩) hfreshD
  have hdutyToT : W4StableWrite.dutyTime S d ≤ T :=
    (W4StableWrite.dutyTime_le_action S d).trans hwriteTime
  refine ⟨B, hHon, ?_⟩
  intro v hv
  cases hrecovered with
  | genesis =>
      have hweak : WeakGenesis S rho := weakGenesis_of_sleepy S hsleep
      have hwrite := stableWrite_anySlot_fresh_gstZero S hweak
        (by
          exact fresh_positive_slot S
            (by simpa [legacyInterface] using hs))
        hprop hB hqpos hsq hconfq hhor hforming
      have hcanon : StableRecordCanonicalFrom S rho 0 :=
        Handover.stableRecordSafety_gstZero_clean S rho hweak
      have hduty0 : (0 : Time) ≤ W4StableWrite.dutyTime S d :=
        (Proofs.HealingLemmas.a_nonneg S q).trans
          ((W4StableWrite.action_le_nextDuty S q).trans
            (W4StableWrite.dutyTime_mono S hqd))
      have hret := W4StableWrite.stable_retained_of_duty_from S hcanon
        hduty0 hwrite hdutyToT
        (by simpa only [T, legacyInterface] using hdeadline) v hv
      simpa [T, legacyInterface, Statements.«instance», Internal.readAt,
        Internal.stableOutputAt] using hret.2
  | @recovered source tPrefix gap extra hrec hcont hslash =>
      obtain ⟨rGST, n, hstrong, hsum⟩ := strongRecovery_of_recovery S hrec
      have hweak := weakContinuation_of_sleepy_recovered S hrec hstrong
        hsum hcont hsleep hslash
      obtain ⟨m, _hmn, hmhi, hpack⟩ :=
        W4StableWrite.continuationV4Package S
          (W4StableWrite.preparedV4AwakeWindows_closed S)
          source rGST gap extra n hstrong
      obtain ⟨fresh, base, Pseed, cap, hphase, hboot, hfinality,
        hawake, _hstartHor, hlatest⟩ := hpack rho hweak
      have hrecover : (legacyConstants S).recoveryEnd tPrefix gap extra =
          healingBoundaryTime S (n + gap) := by
        simpa [legacyConstants, Statements.ourConstants, recoveryRound, hsum]
      have hstarts : S.hc.opening_slot m < s :=
        fresh_opening_before_boundary S hmhi
          (by simpa [hrecover, legacyInterface] using hs)
      have hwrite := stableWrite_anySlot_fresh_afterGST S hweak.core
        hweak.committees hboot hawake hfinality hphase hstarts
        hprop hB hsq hconfq hhor hforming
      have sch : ScheduleWellFormed S rho := hweak.core.toNamedScheduleWellFormed
      have hcanon : StableRecordCanonicalFrom S rho
          (Protocol.confirmation_time S.E (S.hc.opening_slot m)) :=
        Handover.stableRecordCanonicalFrom_of_phaseShift_latestFinality
          S sch hphase hlatest
      have hmq : m < q :=
        Nat.lt_of_mul_lt_mul_right (hstarts.trans hsq)
      have hdutyStart : Protocol.confirmation_time S.E
          (S.hc.opening_slot m) ≤ W4StableWrite.dutyTime S d := by
        rw [opening_confirmation_time_eq_action]
        exact (Assembly.a_mono S hmq.le).trans
          ((W4StableWrite.action_le_nextDuty S q).trans
            (W4StableWrite.dutyTime_mono S hqd))
      have hret := W4StableWrite.stable_retained_of_duty_from S hcanon
        hdutyStart hwrite hdutyToT
        (by simpa only [T, legacyInterface] using hdeadline) v hv
      simpa [T, legacyInterface, Statements.«instance», Internal.readAt,
        Internal.stableOutputAt] using hret.2


/-- An honest proposal enters the stable output by the fast one-round delay
under a fresh sleepy majority. -/
theorem stableIncludedFast_concrete (S : Setup V) :
    ∀ rho t₀, Generic.FreshSleepyRegime (DecoupledConsensusModel.Execution.spec S)
        (Statements.Instantiation.env S) (Statements.Instantiation.interface S)
        (Statements.Instantiation.constants S) rho t₀ →
      Generic.IncludedFrom (DecoupledConsensusModel.Execution.spec S)
        (Statements.Instantiation.interface S) rho
        (Statements.Instantiation.interface S).stable t₀
        (Statements.Instantiation.constants S).fastStableInclusionDelay := by
  intro rho t₀ h
  have hs := sleepyRegime_of_generic S rho t₀ h.toSleepyRegime
  have hr := recoveredBy_of_generic S rho t₀ h.start
  have hfresh : ∀ t, t₀ ≤ t → (C S).participationLag ≤ t →
      t - (C S).participationLag ≤ rho.horizon →
      Generic.FreshMajority (E S) rho.honest (C S) t := by
    intro t ht hl hh
    exact h.fresh t ht hl hh
  exact included_of_named S (available_stableIncluded_fresh S rho t₀ hs hr hfresh)

#print axioms stableIncludedFast_concrete
#print axioms storeGrade_g2_of_relativeCarrierWindow_and_voterCover
#print axioms localG2Cover_of_freshVoterCover
#print axioms gradeFormingMajority_of_freshAt
#print axioms relativeCarrierWindowAt_of_transport
#print axioms relativeCarrier_fastDuty_gstZero
#print axioms relativeCarrier_fastDuty_afterGST
#print axioms stableWrite_of_freshCover
#print axioms stableIncludedFresh_slow_concrete

end DecoupledConsensusModel.Proofs

end
