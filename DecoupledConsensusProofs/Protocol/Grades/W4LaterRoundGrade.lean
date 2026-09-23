module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.W4StableRecordGrowthFrom
public import DecoupledConsensusProofs.Protocol.Grades.WeakBootstrapAction

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace W4StableWrite

open Internal Execution
open Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. The weight step -/

/-- **The grade forms from an awake-window majority.**

The twin of `phaseGrade_of_gradeFormingMajority` with the awake window as the
positive set and `univ \ honest` as the bound on the opponents. Both
inclusions are strictly easier than the grade-forming pair: the opponents need
only be faulty, not faulty-or-stale, and the supporters need only be awake
somewhere in the window, not voters of the previous round. -/
theorem phaseGrade_of_awakeWindowMajority
    (S : Setup V) {rho : Run V} (r : Round)
    (gv : Protocol.GradeView V) (F C : Block V) (ea la : Time)
    (hmajority : AwakeWindowMajority S.E (fun x => (S.node x).awake)
      rho.honest S.hc.η_SG r)
    (hpositive : honestAwakeWindow (fun x => (S.node x).awake)
        rho.honest S.hc.η_SG r ⊆
      Finset.univ.filter fun v =>
        DecoupledConsensusModel.Protocol.positive gv F S.hc.η_SG r ea la v C = true)
    (hopposing : (Finset.univ.filter fun v =>
      DecoupledConsensusModel.Protocol.opposing gv F S.hc.η_SG r ea la v C = true) ⊆
        Finset.univ \ rho.honest) :
    DecoupledConsensusModel.Protocol.gradeBool S.E gv F S.hc.η_SG r ea la C = true := by
  simp only [DecoupledConsensusModel.Protocol.gradeBool, decide_eq_true_eq]
  exact lt_of_le_of_lt (S.E.electorate.weightOf_mono hopposing)
    (lt_of_lt_of_le (by simpa only [AwakeWindowMajority] using hmajority)
      (S.E.electorate.weightOf_mono hpositive))

#print axioms phaseGrade_of_awakeWindowMajority

/-! ## 2. The same at the duty read's phase surface -/

/-- **The reader's own round-`d` G2 grade from the awake-window majority.** -/
theorem storeGrade_g2_of_awakeWindowMajority
    (S : Setup V) {rho : Run V} {d : Round} {P : Block V} {v : V}
    (hmajority : AwakeWindowMajority S.E (fun x => (S.node x).awake)
      rho.honest S.hc.η_SG d)
    (hpositive : honestAwakeWindow (fun x => (S.node x).awake)
        rho.honest S.hc.η_SG d ⊆
      Internal.PhaseGrades.phaseSupporters S.E S.hc
        (Internal.PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) v).st.core.toHealing.gradeView
        (Internal.PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) v).st.core.F d .g2 P)
    (hopposing : Internal.PhaseGrades.phaseOpponents S.E S.hc
        (Internal.PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) v).st.core.toHealing.gradeView
        (Internal.PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) v).st.core.F d .g2 P ⊆
      Finset.univ \ rho.honest) :
    Internal.PhaseGrades.storeGrade S.E S.hc
      (Internal.PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) v).st d .g2 P = true := by
  simp only [Internal.PhaseGrades.storeGrade, Internal.PhaseGrades.phaseGrade]
  exact phaseGrade_of_awakeWindowMajority S d _ _ P _ _ hmajority
    (by simpa only [Internal.PhaseGrades.phaseSupporters] using hpositive)
    (by simpa only [Internal.PhaseGrades.phaseOpponents] using hopposing)

#print axioms storeGrade_g2_of_awakeWindowMajority

/-- **The per-reader G2 cover at an arbitrary duty round, with no
grade-forming premise.**

The awake-window twin of
`localG2CoverAtDutyRound_of_carrierWindow_and_gradeFormingMajority`. It ends
in the same `localG2CoverAtDuty_of_storeGrade` step; only the source of the
reader's grade changes. -/
theorem localG2CoverAtDutyRound_of_awakeWindowMajority
    (S : Setup V) {rho : Run V} {d : Round} (hd : 0 < d) {P : Block V} {v : V}
    (hmem : P ∈ (Internal.PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) v).st.core.T)
    (hmajority : AwakeWindowMajority S.E (fun x => (S.node x).awake)
      rho.honest S.hc.η_SG d)
    (hpositive : honestAwakeWindow (fun x => (S.node x).awake)
        rho.honest S.hc.η_SG d ⊆
      Internal.PhaseGrades.phaseSupporters S.E S.hc
        (Internal.PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) v).st.core.toHealing.gradeView
        (Internal.PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) v).st.core.F d .g2 P)
    (hopposing : Internal.PhaseGrades.phaseOpponents S.E S.hc
        (Internal.PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) v).st.core.toHealing.gradeView
        (Internal.PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) v).st.core.F d .g2 P ⊆
      Finset.univ \ rho.honest) :
    LocalG2CoverAtDutyRound S rho d P v := by
  have hpred : d - 1 + 1 = d := Nat.sub_add_cancel hd
  have hgrade := storeGrade_g2_of_awakeWindowMajority S hmajority hpositive
    hopposing
  have hcover : LocalG2CoverAtDuty S rho (d - 1) P v := by
    refine localG2CoverAtDuty_of_storeGrade S ?_ ?_
    · rw [hpred]; exact hmem
    · rw [hpred]; exact hgrade
  rw [localG2CoverAtDuty_eq_round, hpred] at hcover
  exact hcover

#print axioms localG2CoverAtDutyRound_of_awakeWindowMajority

/-! ## 3. The window carrier, and the opposing side

The structural gain of the later round is here. At round `d` the SG expiry
window of the G2 read is `[d - η_SG, d - 1]`, and
`honest_rawInput_is_own_round_vote` puts every honest validator's token in
exactly that range. When the window starts at or after the round whose opening
proposal is `B` — which is what `d = c - 1 + η_SG` buys — there is no stale
case left to handle: every honest token names that validator's own SG vote of a
window round, and every such vote is at or above `B`. So the opponents are
faulty outright, not merely faulty-or-stale, and that is the inclusion the
awake-window weight step needs. -/

/-- Every honest SG vote of round `d`'s SG expiry window is at or above `B`,
and each honest reader holds the voted block at the round-`d` G2 read. -/
def W4WindowCarrierAt (S : Setup V) (rho : Run V) (d : Round)
    (B : Block V) : Prop :=
  ∀ w ∈ rho.honest, ∀ k : Round, d - S.hc.η_SG ≤ k → k < d →
    ∀ u ∈ Internal.NamedOutageEntry.honestRoundVoters S rho k,
      Block.Preceq B (actionSGBlockAt S rho u k) ∧
      Block.find?
          (Internal.PhaseGrades.readAt S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) w).st.core.T
          (actionSGBlockAt S rho u k).root =
        some (actionSGBlockAt S rho u k)

/-- **No honest validator opposes `B` at the round-`d` G2 read.** -/
theorem w4_phaseOpponents_subset_faulty_of_windowCarrier
    (S : Setup V) {rho : Run V} (core : AdmissibleCore S rho)
    {d : Round} (hd : 0 < d) {B : Block V}
    (hhor : DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2 ≤ rho.horizon)
    (hwindow : W4WindowCarrierAt S rho d B)
    {w : V} (hw : w ∈ rho.honest) :
    Internal.PhaseGrades.phaseOpponents S.E S.hc
        (Internal.PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) w).st.core.toHealing.gradeView
        (Internal.PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) w).st.core.F d .g2 B ⊆
      Finset.univ \ rho.honest := by
  classical
  have hpred : d - 1 + 1 = d := Nat.sub_add_cancel hd
  set n := Internal.PhaseGrades.readAt S rho
    (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) w with hn
  set gv := n.st.core.toHealing.gradeView with hgv
  set F := n.st.core.F with hF
  intro u hu
  by_cases huHon : u ∈ rho.honest
  · exfalso
    have hopp : DecoupledConsensusModel.Protocol.opposing gv F S.hc.η_SG d
        (DecoupledConsensusModel.Protocol.early S.E S.hc d .g2)
        (DecoupledConsensusModel.Protocol.late S.E S.hc d .g2) u B = true :=
      (Finset.mem_filter.mp hu).2
    simp only [DecoupledConsensusModel.Protocol.opposing, decide_eq_true_eq] at hopp
    rcases hopp with ⟨x, hx, _hdom, hnotcover⟩ |
      ⟨x, hx, y, hy, _, hround, hkey⟩
    · simp only [DecoupledConsensusModel.Protocol.readyView, Finset.mem_image] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      have hzraw := (Finset.mem_filter.mp hz).1
      change z ∈ DecoupledConsensusModel.Protocol.rawInputs
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2)
          w).st.core.toHealing.gradeView
        S.hc.η_SG d (DecoupledConsensusModel.Protocol.late S.E S.hc d .g2) u at hzraw
      have hzraw' : z ∈ DecoupledConsensusModel.Protocol.rawInputs
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2)
            w).st.core.toHealing.gradeView
          S.hc.η_SG (d - 1 + 1) (DecoupledConsensusModel.Protocol.late S.E S.hc d .g2) u := by
        simpa only [hpred] using hzraw
      obtain ⟨a, haround, hval, hemit, _, hconfirmed, _hemitted,
          hzlower, hzupper⟩ :=
        NamedOutageClosure.honest_rawInput_is_own_round_vote S rho core
          (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2)
          (DecoupledConsensusModel.Protocol.late S.E S.hc d .g2) w hw huHon (r := d - 1) hzraw'
      have hzlt : z.round < d := Nat.lt_of_le_of_lt hzupper (Nat.sub_lt hd Nat.one_pos)
      have hzlow : d - S.hc.η_SG ≤ z.round := by
        simpa only [hpred] using hzlower
      have hactionHor : S.a z.round ≤ rho.horizon :=
        (NamedOutageClosure.action_le_domain S S.hc.R_ge_three hzlt).trans hhor
      have huVoter : u ∈ Internal.NamedOutageEntry.honestRoundVoters S rho z.round :=
        (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u z.round).mpr
          ⟨huHon, a, hval, haround, hemit⟩
      obtain ⟨hcover, hfind⟩ := hwindow w hw z.round hzlow hzlt u huVoter
      have hconfirmedAction :=
        NamedOutageClosure.honest_emitted_round_confirmed S rho core
          u huHon z.round hactionHor haround hemit
      exact hnotcover (by
        change Protocol.head_covers n.st.core.T B z.confirmed = true
        rw [hconfirmed, hconfirmedAction]
        simp only [Protocol.head_covers]
        rw [show Block.find? n.st.core.T (actionSGBlockAt S rho u z.round).root =
            some (actionSGBlockAt S rho u z.round) by
          simpa only [hn] using hfind]
        exact hcover)
    · have hclean0 := NamedOutageClosure.honest_rawView_clean S rho core
        (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2)
        (DecoupledConsensusModel.Protocol.late S.E S.hc d .g2) w hw huHon (d - 1) 0
      rw [hpred] at hclean0
      exact hkey (hclean0 x hx y hy (Nat.zero_le _) hround)
  · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, huHon⟩

#print axioms w4_phaseOpponents_subset_faulty_of_windowCarrier

/-! ## 4. The positive side, and the later-round grade

With no honest opponent, the positive side costs one dichotomy: a validator
whose early ready view at the reader is nonempty either supports `B` or opposes
it, and section 3 has just out the second for honest validators. So the
only thing the awake window has to deliver is that each of its validators is
READ by the reader at all — the token itself, not its content. -/

/-- Each honest validator of the awake window has a token in the reader's early
ready view at the round-`d` G2 read. -/
def W4WindowReadyAt (S : Setup V) (rho : Run V) (d : Round) : Prop :=
  ∀ w ∈ rho.honest, ∀ u ∈ Execution.honestAwakeWindow
      (fun x => (S.node x).awake) rho.honest S.hc.η_SG d,
    (DecoupledConsensusModel.Protocol.readyView
        (Internal.PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) w).st.core.toHealing.gradeView
        (Internal.PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) w).st.core.F
        S.hc.η_SG d (DecoupledConsensusModel.Protocol.early S.E S.hc d .g2) u).Nonempty

/-- **Every honest validator of the awake window supports `B`.** -/
theorem w4_awakeWindow_subset_phaseSupporters_of_windowCarrier
    (S : Setup V) {rho : Run V} (core : AdmissibleCore S rho)
    {d : Round} (hd : 0 < d) {B : Block V}
    (hhor : DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2 ≤ rho.horizon)
    (hwindow : W4WindowCarrierAt S rho d B)
    (hready : W4WindowReadyAt S rho d)
    {w : V} (hw : w ∈ rho.honest) :
    Execution.honestAwakeWindow (fun x => (S.node x).awake)
        rho.honest S.hc.η_SG d ⊆
      Internal.PhaseGrades.phaseSupporters S.E S.hc
        (Internal.PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) w).st.core.toHealing.gradeView
        (Internal.PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) w).st.core.F d .g2 B := by
  classical
  intro u hu
  have huHon : u ∈ rho.honest := by
    simpa only [Execution.honestAwakeWindow, Finset.mem_filter] using
      (Finset.mem_filter.mp hu).1
  have hsub := NamedOutageHistory.JointHistoryProducersTime.readyView_mono
    (Internal.PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) w).st.core.toHealing.gradeView
    (Internal.PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) w).st.core.F
    S.hc.η_SG d (NamedOutageClosure.q10_early_le_late S d .g2) u
  rcases NamedOutageHistory.JointHistoryProducersTime.positive_or_opposing
      (Internal.PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) w).st.core.toHealing.gradeView
      (Internal.PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) w).st.core.F
      S.hc.η_SG d (DecoupledConsensusModel.Protocol.early S.E S.hc d .g2)
      (DecoupledConsensusModel.Protocol.late S.E S.hc d .g2) u B hsub
      (hready w hw u hu) with hp | ho
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hp⟩
  · exact absurd huHon
      (Finset.mem_sdiff.mp
        (w4_phaseOpponents_subset_faulty_of_windowCarrier S core hd hhor
          hwindow hw (Finset.mem_filter.mpr ⟨Finset.mem_univ u, ho⟩))).2

#print axioms w4_awakeWindow_subset_phaseSupporters_of_windowCarrier

/-- **The later-round grade step.**

At a duty round `d` whose SG expiry window lies at or after the round that
produced `B`, the awake-window majority forms the relative grade at `B` and the
reader's own frozen round-`d` G2 root reaches `B`. No grade-forming majority,
and so no assumption about who voted in round `d - 1` in particular. -/
theorem w4_localG2CoverAtDutyRound_of_windowCarrier
    (S : Setup V) {rho : Run V} (core : AdmissibleCore S rho)
    {d : Round} (hd : 0 < d) {B : Block V}
    (hhor : DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2 ≤ rho.horizon)
    (hmajority : Execution.AwakeWindowMajority S.E
      (fun x => (S.node x).awake) rho.honest S.hc.η_SG d)
    (hwindow : W4WindowCarrierAt S rho d B)
    (hready : W4WindowReadyAt S rho d)
    {w : V} (hw : w ∈ rho.honest)
    (hmem : B ∈ (Internal.PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) w).st.core.T) :
    LocalG2CoverAtDutyRound S rho d B w :=
  localG2CoverAtDutyRound_of_awakeWindowMajority S hd hmem hmajority
    (w4_awakeWindow_subset_phaseSupporters_of_windowCarrier S core hd hhor
      hwindow hready hw)
    (w4_phaseOpponents_subset_faulty_of_windowCarrier S core hd hhor hwindow hw)

#print axioms w4_localG2CoverAtDutyRound_of_windowCarrier

/-! ## 5. Both window inputs from one delivery producer

`relativeCarrierWindowAt_of_awakeWindowHistory_of_delivery`
(`WeakBootstrapActionRun`) already transports every honest awake validator's
round-`k` SG vote into every honest reader's round-`d` interpreted view, for
every `k` of the window. That single producer supplies the reader's half of
BOTH inputs above: the `find?` clause of the window carrier and the nonempty
early ready view. What it does not supply, and what stays the one protocol
obligation of the later-round step, is the direction of the cover: it bounds
the window's SG votes ABOVE by a common `D`, while the grade needs them BELOW
by `B`. -/

/-- The window carrier and the window open, from the awake-window delivery
producer and the persistence cover. -/
theorem w4_windowCarrier_and_ready_of_delivery
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {cap : Time} (hdelivery : NamedHealthyPrefixDelivery S rho cap)
    (hcapHor : cap ≤ rho.horizon)
    {base d : Round} {D : Block V} (hd : 0 < d)
    (hspan : base ≤ d - S.hc.η_SG)
    (hawake : Execution.AwakeWindowMajority S.E
      (fun v => (S.node v).awake) rho.honest S.hc.η_SG d)
    (hsg : ∀ k, base ≤ k → k < d → ∀ u ∈ rho.honest,
      NamedRun.emits S rho u
        (Object.attest (actionAttestationAt S rho u k)) (S.a k) →
      Block.Preceq (actionSGBlockAt S rho u k) D)
    (hroots : ∀ w ∈ rho.honest,
      Block.Preceq (Protocol.get_fg_root
        (actionStoreAt S rho w d).st.core.toHealing.toFG) D)
    (hcap : DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2 ≤ cap)
    {B : Block V}
    (hcover : ∀ k : Round, d - S.hc.η_SG ≤ k → k < d →
      ∀ u ∈ Internal.NamedOutageEntry.honestRoundVoters S rho k,
        Block.Preceq B (actionSGBlockAt S rho u k)) :
    W4WindowCarrierAt S rho d B ∧ W4WindowReadyAt S rho d := by
  classical
  have hwin := Proofs.HealingSurface.WeakJoint.relativeCarrierWindowAt_of_awakeWindowHistory_of_delivery
    S adm hdelivery hcapHor hd hspan hawake hsg hroots .g2 hcap
  constructor
  · intro w hw k hklo hkhi u hu
    refine ⟨hcover k hklo hkhi u hu, ?_⟩
    obtain ⟨huHon, a, hval, haround, hemit⟩ :=
      (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u k).mp hu
    have hawakeu : (S.node u).awake k = true := by
      simpa only [haround] using Proofs.Optimistic.emits_attest_awake S hemit
    obtain ⟨y, -, -, -, hfind⟩ := hwin w hw u huHon k
      (NamedOutageClosure.mem_latest_window hklo hkhi) hawakeu
    exact hfind
  · intro w hw u hu
    obtain ⟨huHon, k, hkmem, hawakeu⟩ := WeakSG.mem_honestAwakeWindow_iff.mp hu
    obtain ⟨y, hy, -, -, -⟩ := hwin w hw u huHon k hkmem hawakeu
    exact ⟨DecoupledConsensusModel.Protocol.token y,
      Finset.mem_image_of_mem DecoupledConsensusModel.Protocol.token hy⟩

#print axioms w4_windowCarrier_and_ready_of_delivery

end W4StableWrite
end Proofs
end DecoupledConsensusModel

end
