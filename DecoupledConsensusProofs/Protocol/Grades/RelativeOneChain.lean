module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.RoundVoterTransport
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsBridge
public import DecoupledConsensusProofs.Protocol.Grades.Q20_graded_has_honest_supporter
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.WeakSGWindow

@[expose] public section

/-!
# Relative-grade one-chain facts

This module exposes the store-local compatibility law for relative grades.
The cross-reader surface is recorded below at the exact prepared reads where
the runtime freezes G2 and G1.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Execution
open Internal.NamedOutageEntry
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

def relativePhaseRead
    (S : Setup V) (rho : Run V) (r : Round) (p : Phase) (w : V) :
    NamedNodeState V :=
  NamedRun.stateBeforeTime S rho (domain S.E S.hc (r + 1) p) w

/-- Two relative-graded blocks in one view are compatible. -/
theorem graded_oneChain_at_reader
    (E : Env V) (gv : Protocol.GradeView V) (F : Block V)
    (eta r : Round) {early late : Time} (hcut : early ≤ late)
    {B B' : Block V}
    (hB : DecoupledConsensusModel.Protocol.gradeBool E gv F eta r early late B = true)
    (hB' : DecoupledConsensusModel.Protocol.gradeBool E gv F eta r early late B' = true) :
    Block.compatible B B' = true := by
  exact NamedOutageClosure.q10_graded_compatible E gv F eta r hcut hB hB'

/-- Exact transport of the preceding round's honest action carriers into one
relative-grade phase. This is the part of T3 used by the one-chain argument. -/
def RelativeCarrierWindowAt
    (S : Setup V) (rho : Run V) (r : Round) (p : Phase) : Prop :=
  ∀ w ∈ rho.honest, ∀ u ∈ honestRoundVoters S rho r,
    ∃ y ∈ interpretedInputs
        (relativePhaseRead S rho r p w).st.core.toHealing.gradeView
        (relativePhaseRead S rho r p w).st.core.F
        S.hc.η_SG (r + 1) (early S.E S.hc (r + 1) p) u,
      y.round = r ∧
      y.confirmed = some (actionSGBlockAt S rho u r).root ∧
      Block.find?
        (relativePhaseRead S rho r p w).st.core.T
        (actionSGBlockAt S rho u r).root = some (actionSGBlockAt S rho u r)

/-- The grade-formation conclusion consumed by action-source induction. It
does not select a participation regime: every relative grade has an actual
honest action carrier from its SG expiry window. -/
def RelativeGradeCarrierAt
    (S : Setup V) (rho : Run V) (r : Round) (p : Phase) : Prop :=
  ∀ w ∈ rho.honest, ∀ B,
    DecoupledConsensusModel.Protocol.gradeBool S.E
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) w).st.core.F
      S.hc.η_SG r (early S.E S.hc r p) (late S.E S.hc r p) B = true →
    ∃ k ∈ Protocol.latest_window S.hc.η_SG r, ∃ u ∈ rho.honest,
      NamedRun.emits S rho u
          (Object.attest (actionAttestationAt S rho u k)) (S.a k) ∧
        Block.Preceq B (actionSGBlockAt S rho u k)

/-- A relative grade has an honest preceding-round action carrier above it
when every current honest voter is present in the interpreted phase window. -/
theorem relativeGrade_has_roundCarrier
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    {r : Round} {p : Phase} (hwindow : RelativeCarrierWindowAt S rho r p)
    (hmajority : GradeFormingMajority S rho (r + 1))
    {w : V} (hw : w ∈ rho.honest) {B : Block V}
    (hgrade : DecoupledConsensusModel.Protocol.gradeBool S.E
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) p) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) p) w).st.core.F
      S.hc.η_SG (r + 1) (early S.E S.hc (r + 1) p)
      (late S.E S.hc (r + 1) p) B = true) :
    ∃ u ∈ honestRoundVoters S rho r,
      Block.Preceq B (actionSGBlockAt S rho u r) := by
  let n := NamedRun.stateBeforeTime S rho (domain S.E S.hc (r + 1) p) w
  let gv := n.st.core.toHealing.gradeView
  let F := n.st.core.F
  let ea := early S.E S.hc (r + 1) p
  let la := late S.E S.hc (r + 1) p
  let voters := honestRoundVoters S rho r
  let bad := (Finset.univ \ rho.honest) ∪ staleHistoricalVoters S rho (r + 1)
  by_contra hnone
  push Not at hnone
  have hcut : ea ≤ la := NamedOutageClosure.q10_early_le_late S (r + 1) p
  have hvotersOpp : voters ⊆ Finset.univ.filter fun u =>
      DecoupledConsensusModel.Protocol.opposing gv F S.hc.η_SG (r + 1) ea la u B = true := by
    intro u hu
    have huHon : u ∈ rho.honest :=
      ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u r).mp hu).1
    obtain ⟨y, hy, hyround, hyconfirmed, hyfind⟩ := hwindow w hw u hu
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ u, ?_⟩
    simp only [DecoupledConsensusModel.Protocol.opposing, decide_eq_true_eq]
    refine Or.inl ⟨DecoupledConsensusModel.Protocol.token y, ?_, ?_, ?_⟩
    · exact Finset.mem_image_of_mem DecoupledConsensusModel.Protocol.token
        (NamedOutageClosure.q10_interpreted_cut gv F S.hc.η_SG (r + 1)
          hcut u (by simpa only [n, gv, F, ea] using hy))
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hzraw := (Finset.mem_filter.mp hz).1
      obtain ⟨_, _, _, _, _, _, _, _, hzupper⟩ :=
        NamedOutageClosure.honest_rawInput_is_own_round_vote S rho core
          (domain S.E S.hc (r + 1) p) (early S.E S.hc (r + 1) p)
          w hw huHon hzraw
      simpa only [DecoupledConsensusModel.Protocol.token, hyround] using hzupper
    · intro hcover
      change Protocol.head_covers n.st.core.T B y.confirmed = true at hcover
      rw [hyconfirmed] at hcover
      have hyfind' : Block.find? n.st.core.T
          (actionSGBlockAt S rho u r).root =
          some (actionSGBlockAt S rho u r) := by
        simpa only [n, relativePhaseRead] using hyfind
      simp only [Protocol.head_covers, hyfind'] at hcover
      exact hnone u hu hcover
  have hpositiveBad : (Finset.univ.filter fun u =>
      DecoupledConsensusModel.Protocol.positive gv F S.hc.η_SG (r + 1) ea la u B = true) ⊆
      bad := by
    intro u hu
    by_cases huHon : u ∈ rho.honest
    · refine Finset.mem_union_right _ ?_
      have huNotVoter : u ∉ voters := by
        intro huVoter
        have huOpp := (Finset.mem_filter.mp (hvotersOpp huVoter)).2
        have huPos := (Finset.mem_filter.mp hu).2
        have hsupports : DecoupledConsensusModel.Protocol.Supports
            (fun k b => DecoupledConsensusModel.Protocol.localCovers gv k b = true)
            (DecoupledConsensusModel.Protocol.readyView gv F S.hc.η_SG (r + 1) ea u)
            (DecoupledConsensusModel.Protocol.readyView gv F S.hc.η_SG (r + 1) la u)
            (DecoupledConsensusModel.Protocol.rawView gv S.hc.η_SG (r + 1) la u) B := by
          simpa only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq] using huPos
        have hnot := NamedOutageClosure.q10_not_opposes_of_supports
          (fun k b => DecoupledConsensusModel.Protocol.localCovers gv k b = true)
          (NamedOutageClosure.q10_readyView_cut gv F S.hc.η_SG (r + 1) hcut u)
          (NamedOutageClosure.q10_ready_subset_raw gv F S.hc.η_SG (r + 1) la u)
          hsupports
        exact hnot (by simpa only [DecoupledConsensusModel.Protocol.opposing,
          decide_eq_true_eq] using huOpp)
      have huPos := (Finset.mem_filter.mp hu).2
      simp only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq] at huPos
      obtain ⟨x, hx, -, -, -, -⟩ := huPos
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hzraw := (Finset.mem_filter.mp hz).1
      obtain ⟨a, haround, hval, hemit, _, _, _, hlower, hupper⟩ :=
        NamedOutageClosure.honest_rawInput_is_own_round_vote S rho core
          (domain S.E S.hc (r + 1) p) (early S.E S.hc (r + 1) p)
          w hw huHon hzraw
      have hlatest : z.round ∈ Protocol.latest_window S.hc.η_SG (r + 1) :=
        NamedOutageClosure.mem_latest_window hlower (Nat.lt_succ_of_le hupper)
      have hzVoter : u ∈ honestRoundVoters S rho z.round :=
        (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u z.round).mpr
          ⟨huHon, a, hval, haround, hemit⟩
      have hnotPrevious : u ∉ honestRoundVoters S rho (r + 1 - 1) := by
        simpa only [Nat.add_sub_cancel, voters] using huNotVoter
      exact Proofs.NamedOutageInputs.stale_of_eligible_vote S rho
        hlatest hzVoter hnotPrevious
    · exact Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, huHon⟩)
  change DecoupledConsensusModel.Protocol.gradeBool S.E gv F S.hc.η_SG
    (r + 1) ea la B = true at hgrade
  simp only [DecoupledConsensusModel.Protocol.gradeBool, decide_eq_true_eq] at hgrade
  have hVotersWeight := S.E.electorate.weightOf_mono hvotersOpp
  have hPositiveWeight := S.E.electorate.weightOf_mono hpositiveBad
  change S.E.electorate.weightOf bad <
    S.E.electorate.weightOf voters at hmajority
  omega

private theorem honestRoundVoter_emits_action
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    {u : V} {k : Round} (hu : u ∈ honestRoundVoters S rho k) :
    u ∈ rho.honest ∧ NamedRun.emits S rho u
      (Object.attest (actionAttestationAt S rho u k)) (S.a k) := by
  obtain ⟨huHon, a, -, haRound, hemit⟩ :=
    (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u k).mp hu
  have huAwake : (S.node u).awake k = true := by
    simpa only [haRound] using Proofs.Optimistic.emits_attest_awake S hemit
  obtain ⟨i, hi, -⟩ := hemit
  have hhor : S.a k ≤ rho.horizon := by
    have h := core.toNamedScheduleWellFormed.in_horizon
      (.tick u (S.a k)) (List.mem_of_getElem? hi)
    simpa only [NamedEvent.time] using h.2
  exact ⟨huHon, honest_emits_exact_actionAttestationAt_of_awake
    S core.toNamedScheduleWellFormed huHon k huAwake hhor⟩

/-- `GradeFormingMajority` supplies the regime-independent carrier
conclusion. -/
theorem relativeGradeCarrierAt_of_gradeFormingMajority
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    {r : Round} (hr : 0 < r) {p : Phase}
    (hwindow : RelativeCarrierWindowAt S rho (r - 1) p)
    (hmajority : GradeFormingMajority S rho r) :
    RelativeGradeCarrierAt S rho r p := by
  intro w hw B hgrade
  have hpred : r - 1 + 1 = r := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hr)
  have hmajority' : GradeFormingMajority S rho (r - 1 + 1) := by
    simpa only [hpred] using hmajority
  obtain ⟨u, hu, hpre⟩ := relativeGrade_has_roundCarrier
    S core hwindow hmajority' hw (by simpa only [hpred] using hgrade)
  obtain ⟨huHon, hemit⟩ := honestRoundVoter_emits_action S core hu
  refine ⟨r - 1, ?_, u, huHon, hemit, hpre⟩
  exact NamedOutageClosure.mem_latest_window
    (Nat.sub_le_sub_left S.hc.η_SG_ge_one r)
    (Nat.sub_lt hr (by decide))

/-- `AwakeWindowMajority` supplies the same carrier conclusion when each
awake-window vote is interpreted at the phase read. The transport premise
keeps the finalized-prefix compatibility obligation at the caller. -/
theorem relativeGradeCarrierAt_of_awakeWindowMajority
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    {r : Round} (hr : 0 < r) {p : Phase}
    (hmajority : AwakeWindowMajority S.E (fun v => (S.node v).awake)
      rho.honest S.hc.η_SG r)
    (htransport : ∀ w ∈ rho.honest, ∀ u ∈ rho.honest,
      ∀ k ∈ Protocol.latest_window S.hc.η_SG r,
      (S.node u).awake k = true →
      ∃ y ∈ interpretedInputs
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc r p) w).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc r p) w).st.core.F
          S.hc.η_SG r (early S.E S.hc r p) u,
        y.round = k ∧ y.confirmed = some (actionSGBlockAt S rho u k).root ∧
        Block.find?
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) w).st.core.T
          (actionSGBlockAt S rho u k).root = some (actionSGBlockAt S rho u k)) :
    RelativeGradeCarrierAt S rho r p := by
  intro w hw B hgrade
  let n := NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) w
  let awake := honestAwakeWindow (fun v => (S.node v).awake)
    rho.honest S.hc.η_SG r
  have hawakePresent : awake ⊆ Internal.PhaseGrades.honestPresent
      S.hc n.st.core.toHealing.gradeView n.st.core.F rho.honest r
        (early S.E S.hc r p) := by
    intro u hu
    obtain ⟨huHon, k, hk, huk⟩ := WeakSG.mem_honestAwakeWindow_iff.mp hu
    obtain ⟨y, hy, -⟩ := htransport w hw u huHon k hk huk
    exact Finset.mem_filter.mpr ⟨huHon, ⟨y, by simpa only [n] using hy⟩⟩
  have hwindow : Internal.PhaseGrades.WindowMajorityAt S.E S.hc
      n.st.core.toHealing.gradeView n.st.core.F rho.honest r
        (early S.E S.hc r p) := by
    exact lt_of_lt_of_le (by simpa only [awake, AwakeWindowMajority] using hmajority)
      (S.E.electorate.weightOf_mono hawakePresent)
  obtain ⟨u, hu, y, hy, head, hyHead, hfind, hBhead⟩ :=
    Proofs.HealingLemmas.Rows.q20_graded_has_honest_supporter S.E S.hc
      n.st.core.toHealing.gradeView n.st.core.F rho.honest r B p hwindow
      (by simpa only [Internal.PhaseGrades.phaseGrade, n] using hgrade)
  have hyRaw := (Finset.mem_filter.mp hy).1
  have hpred : r - 1 + 1 = r := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hr)
  obtain ⟨a, haRound, haVal, hemit, -, hyConfirmed, -, hlo, hhi⟩ :=
    NamedOutageClosure.honest_rawInput_is_own_round_vote
      S rho core (domain S.E S.hc r p) (early S.E S.hc r p) w hw hu
      (r := r - 1) (by simpa only [hpred, n] using hyRaw)
  have hk : y.round ∈ Protocol.latest_window S.hc.η_SG r :=
    NamedOutageClosure.mem_latest_window (by simpa only [hpred] using hlo)
      (hhi.trans_lt (Nat.sub_lt hr (by decide)))
  have hhor : S.a y.round ≤ rho.horizon := by
    obtain ⟨i, hi, -⟩ := hemit
    have h := core.toNamedScheduleWellFormed.in_horizon
      (.tick u (S.a y.round)) (List.mem_of_getElem? hi)
    simpa only [NamedEvent.time] using h.2
  have haConfirmed := NamedOutageClosure.honest_emitted_round_confirmed
    S rho core u hu y.round hhor haRound hemit
  have hyAction : y.confirmed = some (actionSGBlockAt S rho u y.round).root :=
    hyConfirmed.trans haConfirmed
  have huAwake : (S.node u).awake y.round = true := by
    simpa only [haRound] using Proofs.Optimistic.emits_attest_awake S hemit
  have hemitAction := honest_emits_exact_actionAttestationAt_of_awake
    S core.toNamedScheduleWellFormed hu y.round huAwake hhor
  obtain ⟨z, -, -, hzConfirmed, hzFind⟩ :=
    htransport w hw u hu y.round hk huAwake
  have hroot : head.root = (actionSGBlockAt S rho u y.round).root := by
    exact Option.some.inj (hyHead.symm.trans hyAction)
  have hhead : head = actionSGBlockAt S rho u y.round := by
    apply Option.some.inj
    rw [← hfind, hroot]
    simpa only [n, Protocol.Store.toHealing] using hzFind
  refine ⟨y.round, hk, u, hu, ?_, ?_⟩
  · exact hemitAction
  · simpa only [hhead] using hBhead








end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms graded_oneChain_at_reader
#print axioms relativeGrade_has_roundCarrier
#print axioms relativeGradeCarrierAt_of_gradeFormingMajority
#print axioms relativeGradeCarrierAt_of_awakeWindowMajority
end DecoupledConsensusModel.Proofs.HealingSurface

end
