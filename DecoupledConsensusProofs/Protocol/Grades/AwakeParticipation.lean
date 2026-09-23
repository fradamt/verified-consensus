module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.OutageInputs
public import DecoupledConsensusProofs.Protocol.Schedule.Action
public import DecoupledConsensusProofs.Execution.HealthyLocalFacts
public import DecoupledConsensusProofs.Protocol.Store.BoundaryRows

@[expose] public section

/-!
# Awake participation closes the named outage inputs

The public outage premise is stated on the environment's awake profile. This
file derives the historical emission predicates used by the existing outage
proof from that premise and the named action schedule.
-/
namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Internal Execution Internal.NamedOutageEntry
open DecoupledConsensusModel.Protocol
open Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- At an action time inside the run, an honest validator emits exactly when it
is awake for that round. -/
theorem honestRoundVoters_eq_awake
    (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (k : Round)
    (hk : S.a k ≤ rho.horizon) :
    honestRoundVoters S rho k = honestAwakeAt S rho k := by
  ext v
  constructor
  · intro hv
    obtain ⟨hvHon, ha⟩ :=
      (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho v k).mp hv
    obtain ⟨a, _, _, hem⟩ := ha
    obtain ⟨_, hawake, _⟩ :=
      (NamedActionSources.action_run_emission S rho sch v k a).mp hem
    exact Finset.mem_filter.mpr ⟨hvHon, hawake⟩
  · intro hv
    obtain ⟨hvHon, hawake⟩ := Finset.mem_filter.mp hv
    have htick : ∃ i : Nat, rho.events[i]? =
        some (NamedEvent.tick v (S.a k)) := by
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp
        (sch.tick_total v hvHon (S.a k) (Proofs.HealingLemmas.publicTime_a S k)
          (Proofs.HealingLemmas.a_nonneg S k) hk)
      exact ⟨i, hi⟩
    have hem : NamedRun.emits S rho v
        (.attest (Proofs.HealingSurface.actionAttestationAt S rho v k)) (S.a k) :=
      (NamedActionSources.action_run_emission S rho sch v k _).mpr
        ⟨htick, hawake, rfl⟩
    apply (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho v k).mpr
    exact ⟨hvHon, ⟨Proofs.HealingSurface.actionAttestationAt S rho v k,
      Proofs.HealingSurface.actionAttestationAt_shape S rho v k |>.1,
      Proofs.HealingSurface.actionAttestationAt_shape S rho v k |>.2.1, hem⟩⟩

private theorem previous_action_le_domain
    (S : Setup V) {r : Round} (hr : 0 < r) (p : Phase) :
    S.a (r - 1) ≤ domain S.E S.hc r p := by
  have hqr : r - 1 < r := Nat.sub_lt hr (by decide)
  have hg2 : S.a (r - 1) ≤ domain S.E S.hc r .g2 :=
    action_le_domain S S.hc.R_ge_three hqr
  have hphase : domain S.E S.hc r .g2 ≤ domain S.E S.hc r p := by
    unfold DecoupledConsensusModel.Protocol.domain
    cases p <;> simp only [Phase.domainOffset]
    all_goals
      exact Int.add_le_add_left
        (Int.mul_le_mul_of_nonneg_right (by norm_num) S.E.Δ_pos.le) _
  exact hg2.trans hphase

private theorem honestAwakeAt_subset_window
    (S : Setup V) (rho : NamedRun V) {r : Round} (hr : 0 < r) :
    honestAwakeAt S rho (r - 1) ⊆
      honestAwakeWindow (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r := by
  intro v hv
  obtain ⟨hvHon, hawake⟩ := Finset.mem_filter.mp hv
  apply Finset.mem_filter.mpr
  refine ⟨hvHon, ?_⟩
  apply List.any_eq_true.mpr
  exact ⟨r - 1,
    Protocol.pred_mem_latest_window S.hc.η_SG r S.hc.η_SG_ge_one hr,
    hawake⟩

/-- The awake grade premise implies the older sleepy-window premise. -/
theorem outageSleepyThroughout_of_awake
    (S : Setup V) (rho : NamedRun V) :
    AwakeGradeMajorityThroughout S rho → OutageSleepyThroughout S rho := by
  intro hawake r hr hcovered
  have hgrade := hawake r hr hcovered
  unfold AwakeGradeMajority at hgrade
  have hfaulty : Finset.univ \ rho.honest ⊆
      (Finset.univ \ rho.honest) ∪ staleAwake S rho r :=
    Finset.subset_union_left
  have hleft := S.E.electorate.weightOf_mono hfaulty
  have hright := S.E.electorate.weightOf_mono
    (honestAwakeAt_subset_window S rho hr)
  exact lt_of_le_of_lt hleft (lt_of_lt_of_le hgrade hright)

/-- A covered round puts its preceding action, and therefore all older eligible
actions, inside the run horizon. This is the schedule fact needed to replace
historical emissions by the awake profile. -/
private theorem previous_action_in_horizon
    (S : Setup V) (rho : NamedRun V) {r : Round} (hr : 0 < r)
    (hcovered : RoundCovered S rho r) :
    S.a (r - 1) ≤ rho.horizon := by
  rcases hcovered with haction | ⟨p, _, hdomain⟩
  · exact (Assembly.a_mono S (Nat.sub_le r 1)).trans haction.2
  · exact (previous_action_le_domain S hr p).trans hdomain

/-- The awake and emitted versions of the stale historical voter set coincide
at every covered positive round. -/
private theorem staleHistoricalVoters_eq_awake
    (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) {r : Round} (hr : 0 < r)
    (hcovered : RoundCovered S rho r) :
    staleHistoricalVoters S rho r = staleAwake S rho r := by
  have hprev : S.a (r - 1) ≤ rho.horizon :=
    previous_action_in_horizon S rho hr hcovered
  have hround : ∀ k : Round,
      k ∈ (Finset.range r).filter
        (fun k => r - S.hc.η_SG ≤ k ∧ k + 1 < r) →
      S.a k ≤ rho.horizon := by
    intro k hk
    obtain ⟨_, ⟨_, hklt⟩⟩ := Finset.mem_filter.mp hk
    have hkprev : k ≤ r - 1 :=
      Nat.le_sub_one_of_lt (Nat.lt_of_succ_lt hklt)
    exact (Assembly.a_mono S hkprev).trans hprev
  have hprevVoters : honestRoundVoters S rho (r - 1) =
      honestAwakeAt S rho (r - 1) :=
    honestRoundVoters_eq_awake S rho sch (r - 1) hprev
  have hhistorical : historicalHonestVoters S rho r =
      ((Finset.range r).filter
        (fun k => r - S.hc.η_SG ≤ k ∧ k + 1 < r)).biUnion
        (fun k => honestAwakeAt S rho k) := by
    unfold historicalHonestVoters
    ext v
    constructor
    · intro hv
      obtain ⟨k, hk, hvk⟩ := Finset.mem_biUnion.mp hv
      have heq := honestRoundVoters_eq_awake S rho sch k (hround k hk)
      rw [heq] at hvk
      exact Finset.mem_biUnion.mpr ⟨k, hk,
        hvk⟩
    · intro hv
      obtain ⟨k, hk, hvk⟩ := Finset.mem_biUnion.mp hv
      have heq := honestRoundVoters_eq_awake S rho sch k (hround k hk)
      rw [← heq] at hvk
      exact Finset.mem_biUnion.mpr ⟨k, hk,
        hvk⟩
  unfold staleHistoricalVoters staleAwake
  rw [hhistorical, hprevVoters]

/-- The awake grade premise implies the historical grade-forming premise. -/
theorem gradeFormingThroughout_of_awake
    (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) :
    AwakeGradeMajorityThroughout S rho → GradeFormingThroughout S rho := by
  intro hawake r hr hcovered
  have hstale := staleHistoricalVoters_eq_awake S rho sch hr hcovered
  have hprev : honestRoundVoters S rho (r - 1) =
      honestAwakeAt S rho (r - 1) :=
    honestRoundVoters_eq_awake S rho sch (r - 1)
      (previous_action_in_horizon S rho hr hcovered)
  have hgrade := hawake r hr hcovered
  unfold GradeFormingMajority
  rw [hstale, hprev]
  exact hgrade

#print axioms honestRoundVoters_eq_awake
#print axioms outageSleepyThroughout_of_awake
#print axioms gradeFormingThroughout_of_awake

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
