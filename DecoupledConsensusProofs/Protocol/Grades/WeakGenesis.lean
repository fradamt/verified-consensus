module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.WeakFGRoot
public import DecoupledConsensusProofs.Protocol.Schedule.WeakGoldfishCone
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.GoldfishCone
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionConfirmationCore
public import DecoupledConsensusProofs.Protocol.Grades.SafetySlotInduction
public import DecoupledConsensusProofs.Execution.GSTZeroSlotOne

@[expose] public section

/-!
# The round-zero safety boundary under core execution

There are no earlier honest height rows at the first action. The FG root
is therefore genesis. Slot-zero votes can name only genesis, so the first
confirmation walk also stays at genesis. These facts need no grade,
awake-window majority, or accountable finality bound at round zero.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakGenesis

open Internal Execution Protocol Proofs.Optimistic
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem cacheAtRound_clip_local
    (F : Block V) (c : DecoupledConsensusModel.Protocol.Cache V) (r : Round) :
    DecoupledConsensusModel.Protocol.cacheAtRound (DecoupledConsensusModel.Protocol.clipCache F c) r =
      DecoupledConsensusModel.Protocol.clipFrame F (DecoupledConsensusModel.Protocol.cacheAtRound c r) := by
  unfold DecoupledConsensusModel.Protocol.cacheAtRound DecoupledConsensusModel.Protocol.clipCache
  split_ifs <;> rfl

private theorem readFrame_eq_cacheAtRound_of_clipped
    (st : Protocol.HealingStore V) (c : DecoupledConsensusModel.Protocol.Cache V) (r : Round)
    (hclip : DecoupledConsensusModel.Protocol.clipCache st.F c = c) :
    DecoupledConsensusModel.Protocol.readFrame c st r =
      DecoupledConsensusModel.Protocol.cacheAtRound c r := by
  unfold DecoupledConsensusModel.Protocol.readFrame
  have h := congrArg (fun c' => DecoupledConsensusModel.Protocol.cacheAtRound c' r) hclip
  change DecoupledConsensusModel.Protocol.cacheAtRound (DecoupledConsensusModel.Protocol.clipCache st.F c) r =
    DecoupledConsensusModel.Protocol.cacheAtRound c r at h
  rw [cacheAtRound_clip_local] at h
  exact h

private theorem complete_one_other_local
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (r : Round) (t : Time) (p q : DecoupledConsensusModel.Protocol.Phase)
    (f : DecoupledConsensusModel.Protocol.Frame V) (hpq : q ≠ p) :
    DecoupledConsensusModel.Protocol.phaseResult
        (DecoupledConsensusModel.Protocol.completeOne E hc st r t p f) q =
      DecoupledConsensusModel.Protocol.phaseResult f q := by
  unfold DecoupledConsensusModel.Protocol.completeOne
  split
  · rfl
  · split
    · cases p <;> cases q <;>
        simp_all [DecoupledConsensusModel.Protocol.putPhase, DecoupledConsensusModel.Protocol.phaseResult]
    · rfl

private theorem relative_gradeBool_zero
    (E : Env V) (gv : Protocol.GradeView V) (F : Block V)
    (eta : Round) (early late : Time) (B : Block V) :
    DecoupledConsensusModel.Protocol.gradeBool E gv F eta 0 early late B = false := by
  simp [DecoupledConsensusModel.Protocol.gradeBool,
    DecoupledConsensusModel.Protocol.positive, DecoupledConsensusModel.Protocol.opposing,
    DecoupledConsensusModel.Protocol.readyView, DecoupledConsensusModel.Protocol.rawView,
    DecoupledConsensusModel.Protocol.interpretedInputs, DecoupledConsensusModel.Protocol.rawInputs,
    Protocol.latest_window_zero, DecoupledConsensusModel.Protocol.Supports,
    DecoupledConsensusModel.Protocol.Opposes, DecoupledConsensusModel.Protocol.CleanFrom]

private theorem relative_freezeRoot_zero
    (E : Env V) (gv : Protocol.GradeView V) (F : Block V)
    (eta : Round) (early late : Time) :
    DecoupledConsensusModel.Protocol.freezeRoot E gv F eta 0 early late = none := by
  unfold DecoupledConsensusModel.Protocol.freezeRoot
  have hempty : gv.T.filter (fun B =>
      DecoupledConsensusModel.Protocol.gradeBool E gv F eta 0 early late B = true) = ∅ := by
    ext B
    simp [relative_gradeBool_zero E gv F eta early late B]
  rw [hempty]
  unfold Block.deepest?
  exact pickUnique?_empty rfl

private theorem completeFrame_g2_eq
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (r : Round) (t : Time) (f : DecoupledConsensusModel.Protocol.Frame V)
    (ht : t ≠ domain E hc r .g2) :
    (DecoupledConsensusModel.Protocol.completeFrame E hc st r t f).g2 = f.g2 := by
  change DecoupledConsensusModel.Protocol.phaseResult
      (DecoupledConsensusModel.Protocol.completeFrame E hc st r t f) .g2 =
    DecoupledConsensusModel.Protocol.phaseResult f .g2
  have h2 : DecoupledConsensusModel.Protocol.phaseResult
      (DecoupledConsensusModel.Protocol.completeOne E hc st r t .g2 f) .g2 =
      DecoupledConsensusModel.Protocol.phaseResult f .g2 := by
    unfold DecoupledConsensusModel.Protocol.completeOne
    split
    · rfl
    · simp [ht, DecoupledConsensusModel.Protocol.phaseResult, DecoupledConsensusModel.Protocol.putPhase]
  unfold DecoupledConsensusModel.Protocol.completeFrame
  rw [complete_one_other_local E hc st r t .g0 .g2 _ (by decide),
    complete_one_other_local E hc st r t .g1 .g2 _ (by decide), h2]

private theorem completeFrame_g1_eq
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (r : Round) (t : Time) (f : DecoupledConsensusModel.Protocol.Frame V)
    (ht : t ≠ domain E hc r .g1) :
    (DecoupledConsensusModel.Protocol.completeFrame E hc st r t f).g1 = f.g1 := by
  change DecoupledConsensusModel.Protocol.phaseResult
      (DecoupledConsensusModel.Protocol.completeFrame E hc st r t f) .g1 =
    DecoupledConsensusModel.Protocol.phaseResult f .g1
  have h2 : DecoupledConsensusModel.Protocol.phaseResult
      (DecoupledConsensusModel.Protocol.completeOne E hc st r t .g2 f) .g1 =
      DecoupledConsensusModel.Protocol.phaseResult f .g1 :=
    complete_one_other_local E hc st r t .g2 .g1 f (by decide)
  have h1 : DecoupledConsensusModel.Protocol.phaseResult
      (DecoupledConsensusModel.Protocol.completeOne E hc st r t .g1
        (DecoupledConsensusModel.Protocol.completeOne E hc st r t .g2 f)) .g1 =
      DecoupledConsensusModel.Protocol.phaseResult
        (DecoupledConsensusModel.Protocol.completeOne E hc st r t .g2 f) .g1 := by
    unfold DecoupledConsensusModel.Protocol.completeOne
    split
    · rfl
    · simp [ht, DecoupledConsensusModel.Protocol.phaseResult, DecoupledConsensusModel.Protocol.putPhase]
  unfold DecoupledConsensusModel.Protocol.completeFrame
  rw [complete_one_other_local E hc st r t .g0 .g1 _ (by decide), h1, h2]

private theorem action_zero_ne_domain_g2 (S : Setup V) :
    S.a 0 ≠ domain S.E S.hc 0 .g2 := by
  have ha : S.a 0 = 6 * S.E.Δ := by
    unfold Setup.a Protocol.HealConfig.a
    simp [Protocol.HealConfig.opening_slot, slotStart]
  have hdomain : domain S.E S.hc 0 .g2 = -S.E.Δ := by
    unfold domain opening DecoupledConsensusModel.Protocol.Phase.domainOffset
      Protocol.proposal_time Env.t slotStart Protocol.HealConfig.opening_slot
    norm_num
  rw [ha, hdomain]
  nlinarith [S.E.Δ_pos]

private theorem action_zero_ne_domain_g1 (S : Setup V) :
    S.a 0 ≠ domain S.E S.hc 0 .g1 := by
  have ha : S.a 0 = 6 * S.E.Δ := by
    unfold Setup.a Protocol.HealConfig.a
    simp [Protocol.HealConfig.opening_slot, slotStart]
  have hdomain : domain S.E S.hc 0 .g1 = 0 := by
    unfold domain opening DecoupledConsensusModel.Protocol.Phase.domainOffset
      Protocol.proposal_time Env.t slotStart Protocol.HealConfig.opening_slot
    norm_num
  rw [ha, hdomain]
  nlinarith [S.E.Δ_pos]

private theorem round_zero_g1_capture_impossible
    (S : Setup V) {rho : Run V} (v : V) (read : Time) (root : Block V)
    (hcap : ∃ j : Nat, ∃ tau : Time,
      rho.events[j]? = some (.tick v tau) ∧ tau < read ∧
      tau = domain S.E S.hc 0 .g1 ∧
      some root = (DecoupledConsensusModel.Protocol.freezeRoot S.E
        (NamedRun.stateBeforeTime S rho tau v).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho tau v).st.core.F S.hc.η_SG 0
        (early S.E S.hc 0 .g1) (late S.E S.hc 0 .g1)).map
          (fun B => DecoupledConsensusModel.Protocol.clipGrade B
            (NamedRun.stateBeforeTime S rho read v).st.core.F)) : False := by
  let j := Classical.choose hcap
  have hcapj := Classical.choose_spec hcap
  let tau := Classical.choose hcapj
  have hcapt := Classical.choose_spec hcapj
  have hvalue := hcapt.2.2.2
  rw [relative_freezeRoot_zero S.E
    (NamedRun.stateBeforeTime S rho tau v).st.core.toHealing.gradeView
    (NamedRun.stateBeforeTime S rho tau v).st.core.F S.hc.η_SG
    (early S.E S.hc 0 .g1) (late S.E S.hc 0 .g1)] at hvalue
  have hnone : (some root : Option (Block V)) = none := by
    simpa using hvalue
  simpa using hnone

private theorem readFrame_g1_round_zero_no_root
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (v : V) (t : Time) {root : Block V} :
    (DecoupledConsensusModel.Protocol.readFrame
      (NamedRun.stateBeforeTime S rho t v).cache
      (NamedRun.stateBeforeTime S rho t v).st.core.toHealing 0).g1 ≠
        some (some root) := by
  let n := NamedRun.stateBeforeTime S rho t v
  have hclip : DecoupledConsensusModel.Protocol.clipCache n.st.core.F n.cache = n.cache :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t v).2.2
  have hframe := readFrame_eq_cacheAtRound_of_clipped n.st.core.toHealing
    n.cache 0 (by simpa only [Protocol.Store.toHealing] using hclip)
  intro hroot
  have hphase : DecoupledConsensusModel.Protocol.phaseResult
      (DecoupledConsensusModel.Protocol.cacheAtRound n.cache 0) .g1 = some (some root) := by
    rw [← hframe]
    exact hroot
  have horigin := NamedCacheProvenance.completed_phase_before_read S rho
    adm.sorted adm.nodup t v 0 .g1 (some root) (by
      simpa only [n] using hphase)
  rcases horigin with hzero | hcap
  · have hnone : (some root : Option (Block V)) = none := hzero.2
    simpa using hnone
  · exact round_zero_g1_capture_impossible S v t root hcap

private theorem confirmationRead_g1_round_zero_no_root_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (v : V) (t : Time)
    (hround : S.hc.round_of (S.E.slotOf t) = 0)
    (htime : t ≠ domain S.E S.hc 0 .g1) {root : Block V} :
    (DecoupledConsensusModel.Protocol.readFrame
      (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBeforeTime S rho t v) t).cache
      (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBeforeTime S rho t v) t).st.core.toHealing 0).g1 ≠
      some (some root) := by
  let before := NamedRun.stateBeforeTime S rho t v
  intro hroot
  have hclip : DecoupledConsensusModel.Protocol.clipCache before.st.core.F before.cache = before.cache :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t v).2.2
  have hraw := readFrame_g1_round_zero_no_root S adm v t (root := root)
  unfold DecoupledConsensusModel.Protocol.readFrame at hroot
  change (DecoupledConsensusModel.Protocol.clipFrame
    (NamedActionReads.confirmationReadFrom S
      (NamedRun.stateBeforeTime S rho t v) t).st.core.F
    (DecoupledConsensusModel.Protocol.cacheAtRound
      (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBeforeTime S rho t v) t).cache 0)).g1 =
      some (some root) at hroot
  change (DecoupledConsensusModel.Protocol.clipFrame before.st.core.F
    (DecoupledConsensusModel.Protocol.cacheAtRound
      (NamedActionReads.preparedCache S before t) 0)).g1 =
      some (some root) at hroot
  unfold NamedActionReads.preparedCache DecoupledConsensusModel.Protocol.onPhaseTick at hroot
  rw [hround] at hroot
  let a := DecoupledConsensusModel.Protocol.alignRound before.cache 0
  have ha : a.round = 0 := by
    dsimp [a]
    unfold DecoupledConsensusModel.Protocol.alignRound
    split_ifs <;> simp_all
  change (DecoupledConsensusModel.Protocol.clipFrame before.st.core.F
    (DecoupledConsensusModel.Protocol.cacheAtRound
      (DecoupledConsensusModel.Protocol.clipCache before.st.core.F
        { round := a.round,
          current := DecoupledConsensusModel.Protocol.completeFrame S.E S.hc
            before.st.core.toHealing a.round t a.current,
          next := DecoupledConsensusModel.Protocol.completeFrame S.E S.hc
            before.st.core.toHealing (a.round + 1) t a.next }) 0)).g1 =
      some (some root) at hroot
  simp only [ha, DecoupledConsensusModel.Protocol.cacheAtRound, if_pos] at hroot
  have htime' : t ≠ domain S.E S.hc a.round .g1 := by
    simpa [ha] using htime
  have hcomp := completeFrame_g1_eq S.E S.hc before.st.core.toHealing
    a.round t a.current htime'
  have hcomp0 :
      (DecoupledConsensusModel.Protocol.completeFrame S.E S.hc before.st.core.toHealing
        0 t a.current).g1 = a.current.g1 := by
    simpa [ha] using hcomp
  change DecoupledConsensusModel.Protocol.clipResult before.st.core.F
      (DecoupledConsensusModel.Protocol.clipResult before.st.core.F
        (DecoupledConsensusModel.Protocol.completeFrame S.E S.hc
          before.st.core.toHealing 0 t a.current).g1) =
      some (some root) at hroot
  rw [hcomp0] at hroot
  by_cases hc0 : before.cache.round = 0
  · have hacurrent : a.current = before.cache.current := by
      simp [a, DecoupledConsensusModel.Protocol.alignRound, hc0,
        DecoupledConsensusModel.Protocol.cacheAtRound]
    rw [hacurrent] at hroot
    have hcur := congrArg (fun c => c.current) hclip
    change DecoupledConsensusModel.Protocol.clipFrame before.st.core.F
        before.cache.current = before.cache.current at hcur
    have hcur1 := congrArg (fun f => f.g1) hcur
    change DecoupledConsensusModel.Protocol.clipResult before.st.core.F
        before.cache.current.g1 = before.cache.current.g1 at hcur1
    rw [hcur1] at hroot
    have hraw' := hraw
    change (DecoupledConsensusModel.Protocol.readFrame before.cache
      before.st.core.toHealing 0).g1 ≠ some (some root) at hraw'
    have hc0' : 0 = before.cache.round := hc0.symm
    unfold DecoupledConsensusModel.Protocol.readFrame at hraw'
    simp only [DecoupledConsensusModel.Protocol.cacheAtRound, if_pos hc0'] at hraw'
    change DecoupledConsensusModel.Protocol.clipResult before.st.core.F
        before.cache.current.g1 ≠ some (some root) at hraw'
    exact hraw' hroot
  · have hacurrent : a.current = DecoupledConsensusModel.Protocol.pendingFrame := by
      dsimp [a]
      unfold DecoupledConsensusModel.Protocol.alignRound
      split_ifs <;> simp_all
    rw [hacurrent] at hroot
    simp [DecoupledConsensusModel.Protocol.pendingFrame, DecoupledConsensusModel.Protocol.clipResult] at hroot

/-- A prepared confirmation read cannot contain a completed G1 root in clock
round zero. -/
theorem confirmationRead_g1_round_zero_no_root
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (v : V) (t : Time)
    (hround : S.hc.round_of (S.E.slotOf t) = 0)
    (htime : t ≠ domain S.E S.hc 0 .g1) {root : Block V} :
    (DecoupledConsensusModel.Protocol.readFrame
      (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBeforeTime S rho t v) t).cache
      (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBeforeTime S rho t v) t).st.core.toHealing 0).g1 ≠
      some (some root) :=
  confirmationRead_g1_round_zero_no_root_core
    S adm v t hround htime

private theorem readFrame_g2_round_zero_no_root
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (v : V) (t : Time) {root : Block V} :
    (DecoupledConsensusModel.Protocol.readFrame
      (NamedRun.stateBeforeTime S rho t v).cache
      (NamedRun.stateBeforeTime S rho t v).st.core.toHealing 0).g2 ≠
        some (some root) := by
  let n := NamedRun.stateBeforeTime S rho t v
  have hclip : DecoupledConsensusModel.Protocol.clipCache n.st.core.F n.cache = n.cache :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t v).2.2
  have hframe := readFrame_eq_cacheAtRound_of_clipped n.st.core.toHealing
    n.cache 0 (by simpa only [Protocol.Store.toHealing] using hclip)
  intro hroot
  have hphase : DecoupledConsensusModel.Protocol.phaseResult
      (DecoupledConsensusModel.Protocol.cacheAtRound n.cache 0) .g2 = some (some root) := by
    rw [← hframe]
    exact hroot
  have horigin := NamedCacheProvenance.completed_phase_before_read S rho
    adm.sorted adm.nodup
    t v 0 .g2 (some root) (by simpa only [n] using hphase)
  rcases horigin with hzero | ⟨j, tau, hj, _, htau, _⟩
  · simpa using hzero.2
  · have hnonneg :=
      (adm.toNamedScheduleWellFormed.in_horizon
        _ (List.mem_of_getElem? hj)).1
    rw [htau] at hnonneg
    have hdomain : domain S.E S.hc 0 .g2 = -S.E.Δ := by
      unfold domain opening DecoupledConsensusModel.Protocol.Phase.domainOffset
        Protocol.proposal_time Env.t slotStart Protocol.HealConfig.opening_slot
      norm_num
    rw [hdomain] at hnonneg
    simp only [NamedEvent.time] at hnonneg
    nlinarith [S.E.Δ_pos]

private theorem prepared_frame_g2_round_zero_no_root
    (S : Setup V) (before : NamedNodeState V)
    (hround : S.hc.round_of (S.E.slotOf (S.a 0)) = 0)
    (htime : S.a 0 ≠ domain S.E S.hc 0 .g2) {root : Block V}
    (hclip : DecoupledConsensusModel.Protocol.clipCache before.st.core.F before.cache = before.cache)
    (hraw : (DecoupledConsensusModel.Protocol.readFrame before.cache
      before.st.core.toHealing 0).g2 ≠ some (some root)) :
    (DecoupledConsensusModel.Protocol.readFrame
      (NamedActionReads.preparedCache S before (S.a 0))
      (Protocol.NamedDuties.update_confirmation_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S before (S.a 0)).cache)
        S.E S.hc (NamedActionReads.confirmationReadFrom S before (S.a 0)).st
        (S.E.slotOf (S.a 0) - 1)).core.toHealing 0).g2 ≠
      some (some root) := by
  intro hroot
  have hF :
      (Protocol.NamedDuties.update_confirmation_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S before (S.a 0)).cache)
        S.E S.hc (NamedActionReads.confirmationReadFrom S before (S.a 0)).st
        (S.E.slotOf (S.a 0) - 1)).core.toHealing.F =
      before.st.core.toHealing.F := rfl
  change (DecoupledConsensusModel.Protocol.clipFrame
    (Protocol.NamedDuties.update_confirmation_with
      (NamedProfile.gradeContract
        (NamedActionReads.confirmationReadFrom S before (S.a 0)).cache)
      S.E S.hc (NamedActionReads.confirmationReadFrom S before (S.a 0)).st
      (S.E.slotOf (S.a 0) - 1)).core.toHealing.F
    (DecoupledConsensusModel.Protocol.cacheAtRound
      (NamedActionReads.preparedCache S before (S.a 0)) 0)).g2 =
      some (some root) at hroot
  rw [hF] at hroot
  change (DecoupledConsensusModel.Protocol.clipFrame before.st.core.toHealing.F
    (DecoupledConsensusModel.Protocol.cacheAtRound
      (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc before.st.core.toHealing
        (S.a 0) before.cache) 0)).g2 = some (some root) at hroot
  unfold DecoupledConsensusModel.Protocol.onPhaseTick at hroot
  simp only [hround] at hroot
  let a := DecoupledConsensusModel.Protocol.alignRound before.cache 0
  have ha : a.round = 0 := by
    dsimp [a]
    unfold DecoupledConsensusModel.Protocol.alignRound
    split_ifs <;> simp_all
  change (DecoupledConsensusModel.Protocol.clipFrame before.st.core.toHealing.F
    (DecoupledConsensusModel.Protocol.cacheAtRound
      (DecoupledConsensusModel.Protocol.clipCache before.st.core.toHealing.F
        { round := a.round,
          current := DecoupledConsensusModel.Protocol.completeFrame S.E S.hc
            before.st.core.toHealing a.round (S.a 0) a.current,
          next := DecoupledConsensusModel.Protocol.completeFrame S.E S.hc
            before.st.core.toHealing (a.round + 1) (S.a 0) a.next }) 0)).g2 =
      some (some root) at hroot
  rw [cacheAtRound_clip_local] at hroot
  simp only [ha, DecoupledConsensusModel.Protocol.cacheAtRound, if_pos] at hroot
  have htime' : S.a 0 ≠ domain S.E S.hc a.round .g2 := by
    simpa [ha] using htime
  have hcomp := completeFrame_g2_eq S.E S.hc before.st.core.toHealing
    a.round (S.a 0) a.current htime'
  have hcomp0 :
      (DecoupledConsensusModel.Protocol.completeFrame S.E S.hc before.st.core.toHealing
        0 (S.a 0) a.current).g2 = a.current.g2 := by
    simpa [ha] using hcomp
  change DecoupledConsensusModel.Protocol.clipResult before.st.core.toHealing.F
      (DecoupledConsensusModel.Protocol.clipResult before.st.core.toHealing.F
        (DecoupledConsensusModel.Protocol.completeFrame S.E S.hc before.st.core.toHealing
          0 (S.a 0) a.current).g2) = some (some root) at hroot
  rw [hcomp0] at hroot
  by_cases hc0 : before.cache.round = 0
  · have hacurrent : a.current = before.cache.current := by
      simp [a, DecoupledConsensusModel.Protocol.alignRound, hc0, DecoupledConsensusModel.Protocol.cacheAtRound]
    rw [hacurrent] at hroot
    have hcur := congrArg (fun c => c.current) hclip
    change DecoupledConsensusModel.Protocol.clipFrame before.st.core.toHealing.F
        before.cache.current = before.cache.current at hcur
    have hcur2 := congrArg (fun f => f.g2) hcur
    change DecoupledConsensusModel.Protocol.clipResult before.st.core.toHealing.F
        before.cache.current.g2 = before.cache.current.g2 at hcur2
    rw [hcur2] at hroot
    have hraw' := hraw
    change (DecoupledConsensusModel.Protocol.clipFrame before.st.core.toHealing.F
      (DecoupledConsensusModel.Protocol.cacheAtRound before.cache 0)).g2 ≠
        some (some root) at hraw'
    have hc0' : 0 = before.cache.round := hc0.symm
    simp only [DecoupledConsensusModel.Protocol.cacheAtRound, if_pos hc0'] at hraw'
    change DecoupledConsensusModel.Protocol.clipResult before.st.core.toHealing.F
        before.cache.current.g2 ≠ some (some root) at hraw'
    exact hraw' hroot
  · have hacurrent : a.current = DecoupledConsensusModel.Protocol.pendingFrame := by
      dsimp [a]
      unfold DecoupledConsensusModel.Protocol.alignRound
      split_ifs <;> simp_all
    rw [hacurrent] at hroot
    simp [DecoupledConsensusModel.Protocol.pendingFrame, DecoupledConsensusModel.Protocol.clipResult] at hroot

private theorem actionRead_g2_round_zero_no_root
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (v : V) {root : Block V} :
    (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho v 0).cache
      (actionReadAt S rho v 0).st.core.toHealing 0).g2 ≠
        some (some root) := by
  let before := NamedRun.stateBeforeTime S rho (S.a 0) v
  exact prepared_frame_g2_round_zero_no_root S before
    (Proofs.HealingLemmas.round_of_slotOf_a S 0) (action_zero_ne_domain_g2 S)
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a 0) v).2.2
    (readFrame_g2_round_zero_no_root S adm v (S.a 0))

/-- A prepared confirmation read cannot contain a completed G2 root in clock
round zero. This is the confirmation-read counterpart of
`actionRead_g2_round_zero_no_root`; it is used by the GST-zero stable-root
adapter before the positive-round prepared-walk theorem applies. -/
theorem confirmationRead_g2_round_zero_no_root
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (v : V) (t : Time)
    (hround : S.hc.round_of (S.E.slotOf t) = 0)
    (htime : t ≠ domain S.E S.hc 0 .g2) {root : Block V} :
    (DecoupledConsensusModel.Protocol.readFrame
      (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBeforeTime S rho t v) t).cache
      (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBeforeTime S rho t v) t).st.core.toHealing 0).g2 ≠
      some (some root) := by
  let before := NamedRun.stateBeforeTime S rho t v
  intro hroot
  have hclip : DecoupledConsensusModel.Protocol.clipCache before.st.core.F before.cache = before.cache :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t v).2.2
  have hraw := readFrame_g2_round_zero_no_root S adm v t (root := root)
  unfold DecoupledConsensusModel.Protocol.readFrame at hroot
  change (DecoupledConsensusModel.Protocol.clipFrame before.st.core.F
    (DecoupledConsensusModel.Protocol.cacheAtRound
      (NamedActionReads.preparedCache S before t) 0)).g2 =
      some (some root) at hroot
  unfold NamedActionReads.preparedCache DecoupledConsensusModel.Protocol.onPhaseTick at hroot
  rw [hround] at hroot
  let a := DecoupledConsensusModel.Protocol.alignRound before.cache 0
  have ha : a.round = 0 := by
    dsimp [a]
    unfold DecoupledConsensusModel.Protocol.alignRound
    split_ifs <;> simp_all
  change (DecoupledConsensusModel.Protocol.clipFrame before.st.core.F
    (DecoupledConsensusModel.Protocol.cacheAtRound
      (DecoupledConsensusModel.Protocol.clipCache before.st.core.F
        { round := a.round,
          current := DecoupledConsensusModel.Protocol.completeFrame S.E S.hc
            before.st.core.toHealing a.round t a.current,
          next := DecoupledConsensusModel.Protocol.completeFrame S.E S.hc
            before.st.core.toHealing (a.round + 1) t a.next }) 0)).g2 =
      some (some root) at hroot
  simp only [ha, DecoupledConsensusModel.Protocol.cacheAtRound, if_pos] at hroot
  have htime' : t ≠ domain S.E S.hc a.round .g2 := by
    simpa [ha] using htime
  have hcomp := completeFrame_g2_eq S.E S.hc before.st.core.toHealing
    a.round t a.current htime'
  have hcomp0 :
      (DecoupledConsensusModel.Protocol.completeFrame S.E S.hc before.st.core.toHealing
        0 t a.current).g2 = a.current.g2 := by
    simpa [ha] using hcomp
  change DecoupledConsensusModel.Protocol.clipResult before.st.core.F
      (DecoupledConsensusModel.Protocol.clipResult before.st.core.F
        (DecoupledConsensusModel.Protocol.completeFrame S.E S.hc
          before.st.core.toHealing 0 t a.current).g2) =
      some (some root) at hroot
  rw [hcomp0] at hroot
  by_cases hc0 : before.cache.round = 0
  · have hacurrent : a.current = before.cache.current := by
      simp [a, DecoupledConsensusModel.Protocol.alignRound, hc0,
        DecoupledConsensusModel.Protocol.cacheAtRound]
    rw [hacurrent] at hroot
    have hcur := congrArg (fun c => c.current) hclip
    change DecoupledConsensusModel.Protocol.clipFrame before.st.core.F
        before.cache.current = before.cache.current at hcur
    have hcur2 := congrArg (fun f => f.g2) hcur
    change DecoupledConsensusModel.Protocol.clipResult before.st.core.F
        before.cache.current.g2 = before.cache.current.g2 at hcur2
    rw [hcur2] at hroot
    have hraw' := hraw
    change (DecoupledConsensusModel.Protocol.readFrame before.cache
      before.st.core.toHealing 0).g2 ≠ some (some root) at hraw'
    have hc0' : 0 = before.cache.round := hc0.symm
    unfold DecoupledConsensusModel.Protocol.readFrame at hraw'
    simp only [DecoupledConsensusModel.Protocol.cacheAtRound, if_pos hc0'] at hraw'
    change DecoupledConsensusModel.Protocol.clipResult before.st.core.F
        before.cache.current.g2 ≠ some (some root) at hraw'
    exact hraw' hroot
  · have hacurrent : a.current = DecoupledConsensusModel.Protocol.pendingFrame := by
      dsimp [a]
      unfold DecoupledConsensusModel.Protocol.alignRound
      split_ifs <;> simp_all
    rw [hacurrent] at hroot
    simp [DecoupledConsensusModel.Protocol.pendingFrame, DecoupledConsensusModel.Protocol.clipResult] at hroot

private theorem actionRead_g1_round_zero_no_root
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (v : V) {root : Block V} :
    (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho v 0).cache
      (actionReadAt S rho v 0).st.core.toHealing 0).g1 ≠
        some (some root) := by
  have hno := confirmationRead_g1_round_zero_no_root_core
    S adm v (S.a 0) (Proofs.HealingLemmas.round_of_slotOf_a S 0)
      (action_zero_ne_domain_g1 S) (root := root)
  intro hroot
  apply hno
  simpa only [actionReadAt, NamedActionReads.actionReadAt,
    NamedActionReads.actionReadFrom, DecoupledConsensusModel.Protocol.readFrame,
    Protocol.Store.toHealing] using hroot


/-- The first action has no earlier honest source for a non-genesis FG root. -/
theorem actionFGRoot_eq_genesis_zero (S : Setup V) {rho : Run V}
    (adm : AdmissibleCore S rho) (hmajority : HonestWeightMajority S rho.honest)
    {v : V} (hv : v ∈ rho.honest) :
    Protocol.get_fg_root (actionStoreAt S rho v 0).toHealing.toFG = Block.genesis := by
  rcases WeakFG.fgRoot_confirmationWitness_at_action S adm hmajority hv 0 with
    hgen | ⟨_, _, _, _, _, _, har, _, _⟩
  · exact hgen
  · exact False.elim (Nat.not_lt_zero _ har)

/-- The slot-zero confirmation store has the same genesis root. -/
theorem confRoot_eq_genesis_zero (S : Setup V) {rho : Run V}
    (adm : AdmissibleCore S rho) (hmajority : HonestWeightMajority S rho.honest)
    {v : V} (hv : v ∈ rho.honest) :
    confRoot (Proofs.Optimistic.confStore S rho v 0) = Block.genesis := by
  have hroot := actionFGRoot_eq_genesis_zero S adm hmajority hv
  rw [actionStoreAt_fgRoot_eq_openingConfStore] at hroot
  simpa only [Protocol.HealConfig.opening_slot, Nat.zero_mul, confRoot] using hroot


/-- The prepared frame contract has the same slot-zero genesis anchor. -/
theorem confAnchorWith_eq_genesis_zero
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hmajority : Execution.HonestWeightMajority S rho.honest)
    {v : V} (hv : v ∈ rho.honest) :
    confAnchorWith
      (NamedProfile.gradeContract
        (NamedActionReads.confirmationReadAt S rho v (S.a 0)).cache)
      S.E S.hc (confStore S rho v 0) = Block.genesis := by
  let read := NamedActionReads.confirmationReadAt S rho v (S.a 0)
  have hroot := confRoot_eq_genesis_zero S adm hmajority hv
  have hround : S.hc.round_of (confStore S rho v 0).s = 0 := by
    have hslot : (confStore S rho v 0).s = 1 := by
      simp only [confStore, tickStore, slotOf_confirmation_time]
    rw [hslot]
    exact Nat.div_eq_of_lt
      (lt_of_lt_of_le (by decide : 1 < 2) S.hc.R_ge_two)
  unfold confAnchorWith Protocol.get_sg_root_with
  rw [hround]
  change DecoupledConsensusModel.Protocol.anchor S.E S.hc
      (confStore S rho v 0).toHealing 0
      (DecoupledConsensusModel.Protocol.readFrame read.cache
        (confStore S rho v 0).toHealing 0).g1 = Block.genesis
  cases hframe : (DecoupledConsensusModel.Protocol.readFrame read.cache
      (confStore S rho v 0).toHealing 0).g1 with
  | none => exact hroot
  | some value =>
      cases value with
      | none => exact hroot
      | some root =>
          have hno := confirmationRead_g1_round_zero_no_root_core
            S adm v (S.a 0) (Proofs.HealingLemmas.round_of_slotOf_a S 0)
            (action_zero_ne_domain_g1 S) (root := root)
          exfalso
          apply hno
          simpa only [read, confStore, tickStore,
            ← Protocol.confirmation_time_zero_eq_action_zero S] using hframe

theorem block_eq_genesis_of_mem_confStore_zero
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} {X : Block V}
    (hX : X ∈ (Proofs.Optimistic.confStore S rho v 0).T)
    (hslot : X.slot = 0) :
    X = Block.genesis := by
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed (Protocol.confirmation_time S.E 0)
  have hXn : X ∈ (rho.stateBefore S n v).st.core.T := by
    simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
      Run.storeBeforeTime, hn] using hX
  obtain ⟨Xn, hXnbody, hXne⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n v hXn
  have hprocessed : Object.processed (rho.stateBefore S n v).st
      (.block Xn) = true := by
    simpa only [NamedReceipt.processed, decide_eq_true_eq] using hXnbody
  rcases acceptsAt_block_of_processed S rho v n Xn hprocessed with hgen | hacc
  · rw [← hXne, hgen]
    rfl
  · obtain ⟨i, -, t, hacc⟩ := hacc
    have hparent := parent_slot_lt_of_acceptsAt_block S hacc
    rw [hXne] at hparent
    have hbad : X.parent.slot < 0 := by simpa only [hslot] using hparent
    exact False.elim ((Nat.not_lt_zero _) hbad)

theorem runGoldfishVote_of_mem_confVotes_zero
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} (hv : v ∈ rho.honest) {u : GoldfishVote V}
    (hu : u ∈ confVotes S.E (Proofs.Optimistic.confStore S rho v 0) 0) :
    RunGoldfishVote S rho u := by
  have huLate : u ∈ confLate S.E (Proofs.Optimistic.confStore S rho v 0) 0 :=
    (confNumerator S.E (Proofs.Optimistic.confStore S rho v 0) 0).subset_late hu
  have huPool : u ∈ (Proofs.Optimistic.confStore S rho v 0).pool 0 := by
    rw [confLate, beforeCutoff, Finset.mem_filter] at huLate
    exact huLate.1
  have hvalid : Protocol.VoteSetValid S.E 0
      (confLate S.E (Proofs.Optimistic.confStore S rho v 0) 0) := by
    simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using
      voteSetValid_confLate_stateBeforeTime S adm.toNamedScheduleWellFormed v
        (Protocol.confirmation_time S.E 0) 0
  have hus : u.slot = 0 := (hvalid u huLate).1
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed (Protocol.confirmation_time S.E 0)
  exact Or.inr (Or.inr ⟨v, hv, n, by
    rw [hus]
    simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
      Protocol.Store.pool, Protocol.GoldfishStore.pool, Run.storeBeforeTime, hn] using huPool⟩)

theorem confVotes_zero_target_eq_genesis
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} (hv : v ∈ rho.honest) {u : GoldfishVote V}
    (hu : u ∈ confVotes S.E (Proofs.Optimistic.confStore S rho v 0) 0)
    {X : Block V}
    (hfind : Block.find? (Proofs.Optimistic.confStore S rho v 0).T u.head = some X) :
    X = Block.genesis := by
  have huLate : u ∈ confLate S.E (Proofs.Optimistic.confStore S rho v 0) 0 :=
    (confNumerator S.E (Proofs.Optimistic.confStore S rho v 0) 0).subset_late hu
  have hvalid : Protocol.VoteSetValid S.E 0
      (confLate S.E (Proofs.Optimistic.confStore S rho v 0) 0) := by
    simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using
      voteSetValid_confLate_stateBeforeTime S adm.toNamedScheduleWellFormed v
        (Protocol.confirmation_time S.E 0) 0
  have hus : u.slot = 0 := (hvalid u huLate).1
  have hXmem : X ∈ (Proofs.Optimistic.confStore S rho v 0).T :=
    Proofs.HealingLemmas.find?_mem hfind
  have hslotLe : X.slot ≤ u.slot := by
    have huEarly : u ∈ confEarly S.E (Proofs.Optimistic.confStore S rho v 0) 0 := by
      rw [confVotes, Finset.mem_filter] at hu
      exact hu.1
    rw [confEarly, beforeCutoff, Finset.mem_filter] at huEarly
    exact Protocol.head_slot_le_of_resolution_time hfind huEarly.2
  have hslot : X.slot = 0 := Nat.le_zero.mp (hus ▸ hslotLe)
  exact block_eq_genesis_of_mem_confStore_zero S adm hXmem hslot

theorem confVotes_zero_targets_under_child_false
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} (hv : v ∈ rho.honest) {C : Block V}
    (hparent : C.parent? = some Block.genesis)
    {u : GoldfishVote V}
    (hu : u ∈ confVotes S.E (Proofs.Optimistic.confStore S rho v 0) 0) :
    Protocol.targets_under (Proofs.Optimistic.confStore S rho v 0).T C u = false := by
  unfold Protocol.targets_under
  cases hfind : Block.find? (Proofs.Optimistic.confStore S rho v 0).T u.head with
  | none => rfl
  | some X =>
      have hX := confVotes_zero_target_eq_genesis S adm hv hu hfind
      rw [hX]
      apply Bool.eq_false_of_not_eq_true
      intro hpre
      have hEq : C = (Block.genesis : Block V) :=
        Block.preceq_antisymm hpre (Protocol.preceq_genesis C)
      rw [hEq] at hparent
      simp [Block.parent?] at hparent

theorem confSupporters_zero_child_empty
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} (hv : v ∈ rho.honest) {C : Block V}
    (hparent : C.parent? = some Block.genesis) :
    Protocol.goldfishSupporters S.E (Proofs.Optimistic.confStore S rho v 0).T
      (confVotes S.E (Proofs.Optimistic.confStore S rho v 0) 0)
      (confVotes S.E (Proofs.Optimistic.confStore S rho v 0) 0) 0 C = ∅ := by
  ext x
  constructor
  · intro hx
    exfalso
    rw [mem_supporters_iff] at hx
    obtain ⟨-, u, hu, -, htarget⟩ := hx
    rw [Protocol.votes_by, Finset.mem_filter] at hu
    rw [confVotes_zero_targets_under_child_false S adm hv hparent hu.1] at htarget
    exact Bool.false_ne_true htarget
  · intro hx
    simp at hx

theorem confScore_zero_child
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} (hv : v ∈ rho.honest) {C : Block V}
    (hparent : C.parent? = some Block.genesis) :
    confScore S.E (Proofs.Optimistic.confStore S rho v 0) 0 C = 0 := by
  rw [confScore,
    (confNumerator S.E (Proofs.Optimistic.confStore S rho v 0) 0).score_eq_supporters]
  rw [confSupporters_zero_child_empty S adm hv hparent, Finset.card_empty]

theorem confEligible_zero_child_false
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} (hv : v ∈ rho.honest) {C : Block V}
    (hparent : C.parent? = some Block.genesis) :
    confEligible S.E (Proofs.Optimistic.confStore S rho v 0) 0 C = false := by
  simp only [confEligible, confScore_zero_child S adm hv hparent,
    Nat.mul_zero, decide_eq_false_iff_not, Nat.not_lt_zero]
  exact not_false




/-- The prepared frame has no grade-2 block in round zero. -/
theorem actionGrade2Block_zero
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho) (v : V) :
    Protocol.grade2_block_with
      (NamedProfile.gradeContract (actionReadAt S rho v 0).cache)
      S.E S.hc (actionReadAt S rho v 0).st.core.toHealing 0 = none := by
  change DecoupledConsensusModel.Protocol.grade2Block
    (actionReadAt S rho v 0).st.core.toHealing
    (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho v 0).cache
      (actionReadAt S rho v 0).st.core.toHealing 0) = none
  unfold DecoupledConsensusModel.Protocol.grade2Block
  split
  · cases hframe : (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho v 0).cache
        (actionReadAt S rho v 0).st.core.toHealing 0).g2 with
    | none => rfl
    | some root =>
        cases root with
        | none => rfl
        | some root =>
            exact False.elim (actionRead_g2_round_zero_no_root S adm v hframe)
  · rfl

/-- Round zero has no FG source and therefore no retained FG witness. -/
theorem fgConfirmationWitness_zero
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho) (v : V) :
    fgConfirmationWitness S (actionStoreAt S rho v 0) = none := by
  unfold fgConfirmationWitness actionFGSource
  have hround : S.hc.round_of
      (actionStoreAt S rho v 0).st.core.toHealing.s = 0 := by
    simpa only [Protocol.Store.toHealing] using
      actionStoreAt_round S rho v 0
  dsimp only
  rw [hround]
  have hgrade : Protocol.grade2_block_with
      (NamedProfile.gradeContract (actionStoreAt S rho v 0).cache)
      S.E S.hc (actionStoreAt S rho v 0).st.core.toHealing 0 = none := by
    simpa only [actionStoreAt] using actionGrade2Block_zero S adm v
  rw [hgrade]
  rfl

/-- The first action writes the genesis live confirmation. -/
theorem actionLiveConfirmed_eq_genesis_zero (S : Setup V) {rho : Run V}
    (adm : AdmissibleCore S rho) (hmajority : HonestWeightMajority S rho.honest)
    {v : V} (hv : v ∈ rho.honest) :
    (actionStoreAt S rho v 0).live_confirmed = Block.genesis := by
  change (actionStoreAt S rho v 0).st.core.live_confirmed = Block.genesis
  rw [actionStoreAt_eq_update_confirmation_openingConfStore]
  simp only [Protocol.HealConfig.opening_slot, Nat.zero_mul]
  let contract := NamedProfile.gradeContract
    (NamedActionReads.confirmationReadAt S rho v (S.a 0)).cache
  let st := confStore S rho v 0
  have hanchor : confAnchorWith contract S.E S.hc st = Block.genesis := by
    simpa only [contract, st] using
      confAnchorWith_eq_genesis_zero S adm hmajority hv
  have hnone : Protocol.ghost_step (confTree st) (confScore S.E st 0)
      (confEligible S.E st 0) Block.genesis = none := by
    apply ghost_step_none
    intro C _ hparent
    exact confEligible_zero_child_false S adm hv hparent
  have hwalk : confWalkWith contract S.E S.hc st 0 = Block.genesis := by
    unfold confWalkWith Protocol.ghost
    rw [hanchor]
    cases hcard : (confTree st).card with
    | zero => rfl
    | succ n =>
        simp only [Protocol.ghost_walk]
        rw [hnone]
  rw [update_confirmation_with_live_confirmed, hwalk,
    confRoot_eq_genesis_zero S adm hmajority hv]
  split <;> rfl

/-- The first SG output is genesis even if its empty window has no majority. -/
theorem actionSGBlock_eq_genesis_zero (S : Setup V) {rho : Run V}
    (adm : AdmissibleCore S rho) (hmajority : HonestWeightMajority S rho.honest)
    {v : V} (hv : v ∈ rho.honest) :
    actionSGBlockAt S rho v 0 = Block.genesis := by
  have hlive := actionLiveConfirmed_eq_genesis_zero S adm hmajority hv
  have hroot := actionFGRoot_eq_genesis_zero S adm hmajority hv
  let n := actionReadAt S rho v 0
  let st := n.st.core.toHealing
  let grades := DecoupledConsensusModel.Protocol.frameGradeRead n.cache S.E S.hc st 0
  have hlive' : st.live_confirmed = Block.genesis := by
    simpa only [st, n, actionStoreAt, actionReadAt] using hlive
  have hanchor : grades.anchor = Block.genesis := by
    unfold grades DecoupledConsensusModel.Protocol.frameGradeRead
      DecoupledConsensusModel.Protocol.anchor
    cases hframe : (DecoupledConsensusModel.Protocol.readFrame n.cache st 0).g1 with
    | none => exact hroot
    | some value =>
        cases value with
        | none => exact hroot
        | some root =>
            exact False.elim (actionRead_g1_round_zero_no_root S adm v hframe)
  have htest : grades.clear (Block.genesis : Block V) = true := by
    unfold grades DecoupledConsensusModel.Protocol.frameGradeRead DecoupledConsensusModel.Protocol.clear
    cases hframe : (DecoupledConsensusModel.Protocol.readFrame n.cache st 0).g0 with
    | none => rfl
    | some value =>
        cases value with
        | none => rfl
        | some root =>
            exact Block.compatible_of_preceq_common
              (Protocol.preceq_genesis root) (Block.preceq_self root)
  have hclear : Protocol.deepest_clear (some grades.anchor)
      st.live_confirmed grades.clear = some Block.genesis := by
    rw [hlive', hanchor]
    unfold Protocol.deepest_clear Protocol.chain_of
    have hchain : Protocol.chain_up (Block.genesis : Block V).depth
        (Block.genesis : Block V) = [(Block.genesis : Block V)] := rfl
    rw [hchain]
    unfold Block.deepest?
    apply Protocol.pickUnique?_eq_some
    · refine Finset.mem_filter.mpr ⟨?_, Block.preceq_self _, htest⟩
      simp
    · unfold Block.isDeepestIn
      rw [decide_eq_true_eq]
      intro C hC
      have hCeq : C = (Block.genesis : Block V) := by
        simpa using (Finset.mem_filter.mp hC).1
      subst C
      rfl
    · intro B hB _
      simpa using (Finset.mem_filter.mp hB).1
  have hround : S.hc.round_of
      (actionReadAt S rho v 0).st.core.toHealing.s = 0 := by
    simpa only [Protocol.Store.toHealing, actionStoreAt] using
      actionStoreAt_round S rho v 0
  unfold actionSGBlockAt
  dsimp only
  rw [hround]
  unfold Protocol.get_sg_vote_with NamedProfile.gradeContract
    DecoupledConsensusModel.Protocol.frameContract
  change Protocol.currentSGVote st grades = Block.genesis
  unfold Protocol.currentSGVote
  rw [hclear]


/-- Genesis supplies the canonical seed at every positive scheduled vote slot. -/
theorem protectedVoteSlot_genesis (S : Setup V) {rho : Run V}
    (adm : AdmissibleCore S rho) {s : Slot} (hs : 0 < s)
    (hhor : Protocol.vote_time S.E s ≤ rho.horizon) :
    ProtectedVoteSlot S rho s Block.genesis := by
  refine ⟨fun _ _ => Protocol.preceq_genesis _, ?_⟩
  intro v hv hc
  let read := Internal.NamedRecoveryRead.voteDutyRead S rho v s
  let st := read.st.core
  let tree := voterCandidateTreeAt S rho v s
  let H := voterHeadAt S rho v s
  have hinvPre : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E s) v).st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
      (Protocol.vote_time S.E s) v).1
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg read.st := by
    simpa only [read, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt] using
      Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ _ hinvPre
  have hroot : Protocol.get_fg_root st.toHealing.toFG ∈ st.T :=
    Proofs.NamedStoreRoots.fg_root_mem read.st hinv.1.2
  have hanchor : voterAnchorAt S rho v s ∈ st.T := by
    exact Proofs.NamedConfirmationMembership.runtime_anchor_mem read.cache
      S.E S.hc st.toHealing (S.hc.round_of st.s) hroot
  have htree : tree ⊆ st.T := by
    intro D hD
    have hprocessed := Proofs.Records.get_filtered_block_tree_from_subset
      st.toHealing.toFG
      (Protocol.voter_processed_block_tree S.E st.toHealing.toFG.toSG.toGoldfishStore st.s) hD
    exact (Finset.mem_filter.mp hprocessed).1
  have hHmem : H ∈ st.T := by
    rw [show H = Protocol.ghost (voterAnchorAt S rho v s) tree
        (Protocol.goldfish_score S.E st.T
          (Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (st.s - 1))
        (Protocol.goldfish_eligible S.E st.σ st.h_max st.T st.s
          (Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (st.s - 1)) by rfl]
    exact Proofs.Records.ghost_mem_of _ _ hanchor htree
  have hHpre : H ∈
      (NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E s) v).st.core.T := by
    simpa only [read, st, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using hHmem
  obtain ⟨C, hChead, hCrun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
      adm.toNamedScheduleWellFormed hv (Protocol.vote_time S.E s) hHpre
  have hslot : read.st.core.s = s := Proofs.Optimistic.voteDutyRead_slot S rho v s
  have hout :
      (Protocol.NamedDuties.goldfish_vote_with
        (NamedProfile.gradeContract read.cache) S.E S.hc (S.node v) read.st).2 =
        some ⟨(S.node v).val_index, read.st.core.s, H.root⟩ := by
    simp only [Protocol.NamedDuties.goldfish_vote_with,
      Protocol.goldfish_vote_with]
    rw [if_pos]
    · rfl
    · rw [S.node_val_index, hslot]
      exact hc
  have ho : Object.gfVote
      ⟨(S.node v).val_index, read.st.core.s, H.root⟩ ∈
      (on_tick_emit S v
        (NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E s) v)
        (Protocol.vote_time S.E s)).2 := by
    exact Proofs.Optimistic.on_tick_emit_vote_mem S v
      (NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E s) v) s hs hout
  have hem := Proofs.Optimistic.emits_of_on_tick_emit S adm.toNamedScheduleWellFormed hv
    (Proofs.Optimistic.publicTime_vote_time S s) (Proofs.Optimistic.vote_time_nonneg S.E s)
    hhor ho
  refine ⟨C, Protocol.preceq_genesis _, hCrun, ?_⟩
  simpa only [S.node_val_index, hslot, hChead] using hem

/-- A prepared vote-duty read in round zero uses its FG-root fallback. -/
theorem voterAnchorAt_eq_fgRoot_of_round_zero
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (v : V) (d : Slot) (hround : S.hc.round_of d = 0) :
    voterAnchorAt S rho v d =
      Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho v d).st.core.toHealing.toFG := by
  let read := Internal.NamedRecoveryRead.voteDutyRead S rho v d
  have hslot : read.st.core.s = d := Proofs.Optimistic.voteDutyRead_slot S rho v d
  change ((NamedProfile.gradeContract read.cache).read S.E S.hc
    read.st.core.toHealing (S.hc.round_of read.st.core.s)).anchor = _
  rw [hslot, hround]
  change DecoupledConsensusModel.Protocol.anchor S.E S.hc read.st.core.toHealing 0
    (DecoupledConsensusModel.Protocol.readFrame read.cache read.st.core.toHealing 0).g1 = _
  cases hframe :
      (DecoupledConsensusModel.Protocol.readFrame read.cache read.st.core.toHealing 0).g1 with
  | none => rfl
  | some frameRoot =>
      cases frameRoot with
      | none => rfl
      | some root =>
          have hslotOf : S.hc.round_of
              (S.E.slotOf (Protocol.vote_time S.E d)) = 0 := by
            simpa only [Proofs.Optimistic.slotOf_vote_time] using hround
          have hopen : S.hc.opening_slot 0 ≤ d := by
            simp only [Protocol.HealConfig.opening_slot, Nat.zero_mul,
              Nat.zero_le]
          have htimeLt : DecoupledConsensusModel.Protocol.domain S.E S.hc 0 .g1 <
              Protocol.vote_time S.E d := by
            rw [NamedOutageClosure.domain_g1_eq_opening]
            exact (proposal_time_mono S.E hopen).trans_lt
              (proposal_time_lt_vote_time S.E d)
          have hno := confirmationRead_g1_round_zero_no_root_core
            S adm v (Protocol.vote_time S.E d) hslotOf (ne_of_gt htimeLt)
              (root := root)
          exact False.elim (hno (by
            simpa only [read, Internal.NamedRecoveryRead.voteDutyRead,
              NamedActionReads.confirmationReadAt] using hframe))

#print axioms voterAnchorAt_eq_fgRoot_of_round_zero

#print axioms actionFGRoot_eq_genesis_zero
#print axioms confAnchorWith_eq_genesis_zero
#print axioms actionGrade2Block_zero
#print axioms confirmationRead_g2_round_zero_no_root
#print axioms fgConfirmationWitness_zero
#print axioms actionLiveConfirmed_eq_genesis_zero
#print axioms actionSGBlock_eq_genesis_zero
#print axioms protectedVoteSlot_genesis

end WeakGenesis
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
