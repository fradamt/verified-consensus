module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.OutageInputs
public import DecoupledConsensusProofs.Execution.ClockUniform
public import DecoupledConsensusProofs.Protocol.Handlers.SGArrival
public import DecoupledConsensusProofs.Objects.IntervalInduction
public import DecoupledConsensusProofs.Protocol.Grades.Inclusions
public import DecoupledConsensusProofs.Protocol.Grades.FrameForward
public import DecoupledConsensusProofs.Execution.OutputSeedCore

@[expose] public section


namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedJointOutage
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]


/-! ## Clock bounds at a strict read

`NamedClockUniform` proves the clock facts it needs privately. The three
helpers below are copies of that shape, stated at the granularity this
module uses. They rest only on the public fold lemmas of `NamedRuntime`. -/

/-- Copied from the private helper of the same name in `NamedRuntime`. -/
private theorem fold_clock_bounds (S : Setup V) (lo hi : Time) :
    ∀ (events : List (NamedEvent V)) (w : NamedWorld V),
      (∀ v, lo ≤ (w v).st.core.t ∧ (w v).st.core.t ≤ hi) →
      (∀ e ∈ events, lo ≤ e.time ∧ e.time ≤ hi) →
      ∀ v, lo ≤ (events.foldl (NamedWorld.step S) w v).st.core.t ∧
        (events.foldl (NamedWorld.step S) w v).st.core.t ≤ hi := by
  intro events
  induction events with
  | nil => intro w h _; exact h
  | cons e events ih =>
    intro w h ht
    apply ih
    · intro v
      rw [Proofs.NamedRuntime.step_clock_eq]
      cases e with
      | tick u t =>
        dsimp only
        split_ifs
        · exact ht _ (List.mem_cons_self ..)
        · exact h v
      | deliver u o t => exact h v
    · intro f hf
      exact ht f (List.mem_cons_of_mem _ hf)

/-- A strict read's clock is in `[0, cut]`: it is either the initial zero or
an actual tick time of an event that passed the strict filter. -/
private theorem strict_clock_bounds (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (cut : Time) (hcut : 0 ≤ cut) (reader : V) :
    0 ≤ (NamedRun.stateBeforeTime S rho cut reader).st.core.t ∧
      (NamedRun.stateBeforeTime S rho cut reader).st.core.t ≤ cut := by
  have hinit : ∀ v : V, 0 ≤ (NamedWorld.init v).st.core.t ∧
      (NamedWorld.init (V := V) v).st.core.t ≤ cut := by
    intro v
    constructor
    · simp [NamedWorld.init, NamedNode.initial, Protocol.NamedStore.initial, Protocol.Store.init]
    · simpa [NamedWorld.init, NamedNode.initial, Protocol.NamedStore.initial,
        Protocol.Store.init] using hcut
  have hevents : ∀ e ∈ rho.events.filter (fun e => decide (e.time < cut)),
      0 ≤ e.time ∧ e.time ≤ cut := by
    intro e he
    have hmem := List.mem_filter.mp he
    refine ⟨(sch.in_horizon e hmem.1).1, le_of_lt ?_⟩
    simpa only [decide_eq_true_eq] using hmem.2
  simpa only [NamedRun.stateBeforeTime] using
    fold_clock_bounds S 0 cut (rho.events.filter (fun e => decide (e.time < cut)))
      NamedWorld.init hinit hevents reader

/-- Copied from the private helper of the same name in `NamedClockUniform`. -/
private theorem tick_mem_le_strict_clock (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) {cut : Time} {reader : V} {t : Time}
    (htick : NamedEvent.tick reader t ∈
      rho.events.filter (fun e => decide (e.time < cut))) :
    t ≤ (NamedRun.stateBeforeTime S rho cut reader).st.core.t := by
  let filtered := rho.events.filter (fun e => decide (e.time < cut))
  let filteredRun : NamedRun V := { rho with events := filtered }
  have hsorted : filtered.Pairwise (fun e f => e.key ≤ f.key) := by
    simpa only [filtered] using sch.sorted.filter (fun e => decide (e.time < cut))
  have hnonneg : ∀ e ∈ filteredRun.events, 0 ≤ e.time := by
    intro e he
    change e ∈ filtered at he
    exact (sch.in_horizon e (List.mem_filter.mp he).1).1
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp htick
  have hiLen : i < filtered.length := (List.getElem?_eq_some_iff.mp hi).1
  have hle := Proofs.NamedRuntime.tick_time_le_clock S filteredRun hsorted hnonneg hi hiLen
  simpa only [filteredRun, filtered, NamedRun.stateBeforeTime, NamedRun.stateBefore,
    List.take_length] using hle

/-- `round_of` is `·/R`, hence monotone in the slot. -/
private theorem round_of_mono (hc : Protocol.HealConfig) {c d : Slot} (h : c ≤ d) :
    hc.round_of c ≤ hc.round_of d :=
  Nat.div_le_div_right h

/-- `round(rR) = r`. -/
private theorem round_of_opening (hc : Protocol.HealConfig) (r : Round) :
    hc.round_of (hc.opening_slot r) = r := by
  have hR : 0 < hc.R := lt_of_lt_of_le (by norm_num) hc.R_ge_two
  simp only [Protocol.HealConfig.round_of, Protocol.HealConfig.opening_slot]
  exact Nat.mul_div_cancel _ hR

/-- Copied from the private helper of the same name in `NamedClockUniform`. -/
private theorem stateBefore_slot_clock (S : Setup V) (rho : NamedRun V)
    (i : Nat) (reader : V) :
    (NamedRun.stateBefore S rho i reader).st.core.s =
      S.E.slotOf (NamedRun.stateBefore S rho i reader).st.core.t := by
  induction i with
  | zero =>
      simp [Proofs.NamedRuntime.stateBefore_zero, NamedWorld.init, NamedNode.initial,
        Protocol.NamedStore.initial, Protocol.Store.init, Env.slotOf, slotOfTime]
  | succ i ih =>
      rw [Proofs.NamedRuntime.stateBefore_succ]
      cases he : rho.events[i]? with
      | none => simpa only [Option.toList_none, List.foldl_nil] using ih
      | some e =>
          change (NamedWorld.step S (NamedRun.stateBefore S rho i) e reader).st.core.s =
            S.E.slotOf
              (NamedWorld.step S (NamedRun.stateBefore S rho i) e reader).st.core.t
          by_cases hv : e.node = reader
          · cases e with
            | tick v t =>
                change v = reader at hv
                subst v
                rw [Proofs.NamedRuntime.step_tick]
                rw [(Proofs.NamedNode.tick_clock S reader _ t).1,
                  (Proofs.NamedNode.tick_clock S reader _ t).2]
            | deliver v o t =>
                change v = reader at hv
                subst v
                rw [Proofs.NamedRuntime.step_deliver]
                rw [(Proofs.NamedNode.process_clock S _ o).1,
                  (Proofs.NamedNode.process_clock S _ o).2]
                exact ih
          · rw [Proofs.NamedRuntime.step_other S _ e reader (Ne.symm hv)]
            exact ih

/-- Copied from the private helper of the same name in `NamedClockUniform`. -/
private theorem stateBeforeTime_slot_clock (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (cut : Time) (reader : V) :
    (NamedRun.stateBeforeTime S rho cut reader).st.core.s =
      S.E.slotOf (NamedRun.stateBeforeTime S rho cut reader).st.core.t := by
  obtain ⟨i, hread, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho sch.sorted cut
  rw [hread]
  exact stateBefore_slot_clock S rho i reader

/-! ## The support round

The witness is the common honest clock round at `b0`, as. It is read
off the given honest `v`; `boundaryRound_uniform` is the field's own
`∀ w ∈ honest` clause. -/

/-- The honest clock round at the outage boundary. -/
private def boundaryRound (S : Setup V) (rho : NamedRun V) (b0 : Time) (v : V) : Round :=
  S.hc.round_of (NamedRun.stateBeforeTime S rho b0 v).st.core.s

private theorem boundaryRound_uniform (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (b0 : Time) (v : V) (hv : v ∈ rho.honest) :
    ∀ w ∈ rho.honest,
      S.hc.round_of (NamedRun.stateBeforeTime S rho b0 w).st.core.s =
        boundaryRound S rho b0 v := by
  intro w hw
  exact congrArg S.hc.round_of
    (NamedClockUniform.honest_strict_clock_uniform S rho sch b0 w hw v hv).2

/-- The boundary round is at or below every round whose action is at or after
`b0`: the strict clock at `b0` is at most `b0`. -/
private theorem boundaryRound_le (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (b0 : Time) (hb0 : 0 ≤ b0) (v : V)
    (r : Round) (hr : b0 ≤ S.a r) :
    boundaryRound S rho b0 v ≤ r := by
  obtain ⟨hlo, hhi⟩ := strict_clock_bounds S rho sch b0 hb0 v
  have hslot : S.E.slotOf (NamedRun.stateBeforeTime S rho b0 v).st.core.t ≤
      S.E.slotOf (S.a r) := by
    apply Protocol.slot_le_slotOf_of_proposal_time_le
    exact (Protocol.proposal_time_slotOf_le S.E hlo).trans (hhi.trans hr)
  have := round_of_mono S.hc hslot
  rw [Proofs.HealingLemmas.round_of_slotOf_a] at this
  simpa only [boundaryRound, stateBeforeTime_slot_clock S rho sch b0 v] using this

/-- Whenever the round `s + 1` opening-slot support cutoff is strictly before a
cut, the honest clock at that cut has already entered round `s + 1`. At the
boundary this is the formation margin; at the round-`r` G2 early cutoff it is
the schedule gap of `formation_lt_early` below. -/
private theorem succ_le_boundaryRound (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (b0 : Time) (hb0 : b0 ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) (s : Round)
    (hlt : formationConfirmationTime S (s + 1) < b0) :
    s + 1 ≤ boundaryRound S rho b0 v := by
  set τ : Time := formationConfirmationTime S (s + 1) with hτ
  have hΔ : (0 : Time) < S.E.Δ := S.E.Δ_pos
  have hpublic : PublicTime S τ := by
    refine ⟨4 * S.hc.opening_slot (s + 1) + 2, ?_⟩
    simp only [hτ, formationConfirmationTime, Protocol.support_cutoff, Env.t, slotStart]
    push_cast
    ring
  have hopen : Protocol.proposal_time S.E (S.hc.opening_slot (s + 1)) ≤ τ := by
    simp only [hτ, formationConfirmationTime, Protocol.support_cutoff,
      Protocol.proposal_time]
    exact le_add_of_nonneg_right (Int.mul_nonneg (by norm_num) hΔ.le)
  have hnonneg : (0 : Time) ≤ τ :=
    (Proofs.Optimistic.proposal_time_nonneg S.E (S.hc.opening_slot (s + 1))).trans hopen
  have htick : NamedEvent.tick v τ ∈ rho.events :=
    sch.tick_total v hv τ hpublic hnonneg (hlt.le.trans hb0)
  have hfiltered : NamedEvent.tick v τ ∈
      rho.events.filter (fun e => decide (e.time < b0)) :=
    List.mem_filter.mpr ⟨htick, by simpa only [NamedEvent.time, decide_eq_true_eq]⟩
  have hclock : τ ≤ (NamedRun.stateBeforeTime S rho b0 v).st.core.t :=
    tick_mem_le_strict_clock S rho sch hfiltered
  have hslot : S.hc.opening_slot (s + 1) ≤
      S.E.slotOf (NamedRun.stateBeforeTime S rho b0 v).st.core.t :=
    Protocol.slot_le_slotOf_of_proposal_time_le S.E (hopen.trans hclock)
  have := round_of_mono S.hc hslot
  rw [round_of_opening] at this
  simpa only [boundaryRound, stateBeforeTime_slot_clock S rho sch b0 v] using this
/-- The boundary round's opening proposal time is at or before `b0`: the
honest clock at `b0` has entered round `ρ`, and a strict read's clock is at
most the cut. This is the one schedule fact the two inclusions need. -/
private theorem opening_le_boundary (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (b0 : Time) (hb0 : 0 ≤ b0) (v : V) :
    opening S.E S.hc (boundaryRound S rho b0 v) ≤ b0 := by
  obtain ⟨hlo, hhi⟩ := strict_clock_bounds S rho sch b0 hb0 v
  have hslot : S.hc.opening_slot (boundaryRound S rho b0 v) ≤
      S.E.slotOf (NamedRun.stateBeforeTime S rho b0 v).st.core.t := by
    simp only [boundaryRound, stateBeforeTime_slot_clock S rho sch b0 v,
      Protocol.HealConfig.opening_slot, Protocol.HealConfig.round_of]
    exact Nat.div_mul_le_self _ _
  calc opening S.E S.hc (boundaryRound S rho b0 v)
      = Protocol.proposal_time S.E (S.hc.opening_slot (boundaryRound S rho b0 v)) := rfl
    _ ≤ Protocol.proposal_time S.E
          (S.E.slotOf (NamedRun.stateBeforeTime S rho b0 v).st.core.t) :=
        Protocol.proposal_time_mono S.E hslot
    _ ≤ (NamedRun.stateBeforeTime S rho b0 v).st.core.t :=
        Protocol.proposal_time_slotOf_le S.E hlo
    _ ≤ b0 := hhi

/-! ## Schedule gaps around the round-`r` G2 early cutoff -/

private theorem two_lt_six_mul : ∀ d : Int, 0 < d → 2 * d < 6 * d := by
  intro d h; omega

/-- The support cutoff of a round is four delays before its action time. -/
private theorem formation_lt_action (S : Setup V) (k : Round) :
    formationConfirmationTime S k < S.a k := by
  have ha : S.a k = Protocol.proposal_time S.E (S.hc.opening_slot k) + 6 * S.E.Δ := by
    simp only [Setup.a, Protocol.HealConfig.a, Protocol.proposal_time, Env.t]
  have hf : formationConfirmationTime S k =
      Protocol.proposal_time S.E (S.hc.opening_slot k) + 2 * S.E.Δ := by
    simp only [formationConfirmationTime, Protocol.support_cutoff, Protocol.proposal_time, Env.t,
      slotStart]
  rw [ha, hf]
  exact Int.add_lt_add_left (two_lt_six_mul S.E.Δ S.E.Δ_pos) _

/-- Two rounds of headroom put round `s + 1`'s support cutoff strictly before
round `r`'s G2 early cutoff: the cutoff is inside round `s + 1`'s action, and a
strictly earlier round's action plus one delay is at or before `early r.g2`. -/
private theorem formation_lt_early (S : Setup V) (hR : 3 ≤ S.hc.R) {s r : Round}
    (hsr : s + 1 < r) :
    formationConfirmationTime S (s + 1) < early S.E S.hc r .g2 :=
  lt_of_lt_of_le (formation_lt_action S (s + 1))
    (le_trans (by simpa only [add_zero] using Int.add_le_add_left S.E.Δ_pos.le (S.a (s + 1)))
      (action_delta_le_early S hR hsr))

/-- Round `r`'s G2 early cutoff is nonnegative whenever the round is positive:
round `r - 1`'s action is nonnegative and one delay below it. -/
private theorem early_nonneg (S : Setup V) (hR : 3 ≤ S.hc.R) {r : Round} (hr : 0 < r) :
    (0 : Time) ≤ early S.E S.hc r .g2 :=
  le_trans (Proofs.HealingLemmas.a_nonneg S (r - 1))
    (le_trans (by simpa only [add_zero] using Int.add_le_add_left S.E.Δ_pos.le (S.a (r - 1)))
      (action_delta_le_early S hR (Nat.sub_lt hr Nat.one_pos)))

/-- The round's G2 early cutoff is `11Δ` before its action time. This is what
places the inventory time at or before `S.a r` without any boundary bound. -/
private theorem base_early_le_a (S : Setup V) (r : Round) :
    early S.E S.hc r .g2 ≤ S.a r := by
  have he : S.a r = early S.E S.hc r .g2 + 11 * S.E.Δ := by
    unfold Setup.a Protocol.HealConfig.a early opening Phase.earlyOffset
      Protocol.proposal_time Env.t slotStart
    ring
  rw [he]
  exact le_add_of_nonneg_right (Int.mul_nonneg (by norm_num) S.E.Δ_pos.le)



/-- The G1 domain IS the round opening: its domain offset is zero. -/
theorem base_domain_g1_eq_opening (S : Setup V) (r : Round) :
    domain S.E S.hc r .g1 = opening S.E S.hc r := by
  simp only [domain, Phase.domainOffset]
  ring

/-- The opening is nonnegative: it is the proposal time of the opening slot. -/
theorem base_opening_nonneg (S : Setup V) (r : Round) :
    (0 : Time) ≤ opening S.E S.hc r :=
  Proofs.Optimistic.proposal_time_nonneg S.E (S.hc.opening_slot r)

/-- `opening` is monotone in the round. -/
theorem base_opening_mono (S : Setup V) {q r : Round} (h : q ≤ r) :
    opening S.E S.hc q ≤ opening S.E S.hc r :=
  Protocol.proposal_time_mono S.E
    (by simpa only [Protocol.HealConfig.opening_slot] using
      Nat.mul_le_mul_right S.hc.R h)

/-- The G2 domain is monotone in the round: it is the opening minus one delay. -/
theorem base_domain_g2_mono (S : Setup V) {q r : Round} (h : q ≤ r) :
    domain S.E S.hc q .g2 ≤ domain S.E S.hc r .g2 := by
  have hq : domain S.E S.hc q .g2 = opening S.E S.hc q + (-1) * S.E.Δ := rfl
  have hr : domain S.E S.hc r .g2 = opening S.E S.hc r + (-1) * S.E.Δ := rfl
  rw [hq, hr]
  exact Int.add_le_add_right (base_opening_mono S h) _



private theorem base_pred_bounds : ∀ eta r s p k : Nat,
    r < k + eta + 1 → k ≤ s → s + 1 ≤ p → p ≤ r →
    r - eta ≤ p - 1 ∧ p - 1 < r := by
  intro eta r s p k h1 h2 h3 h4
  exact ⟨by omega, by omega⟩


/-- A strict order between two G2 early cutoffs gives the same round order. -/
theorem round_lt_of_early_lt_early (S : Setup V) {r q : Round}
    (h : early S.E S.hc r .g2 < early S.E S.hc q .g2) : r < q := by
  by_contra hcon
  have hopen : opening S.E S.hc q ≤ opening S.E S.hc r :=
    base_opening_mono S (Nat.le_of_not_gt hcon)
  have hearly : early S.E S.hc q .g2 ≤ early S.E S.hc r .g2 := by
    unfold early
    exact Int.add_le_add_right hopen _
  exact (not_lt_of_ge hearly) h

/-- The retained support predecessor is eligible when the target early cutoff
is strictly before the budget cutoff. -/
theorem predecessor_round_in_window_early (S : Setup V) {s r p k : Round}
    (hbudgetRound : early S.E S.hc r .g2 <
      early S.E S.hc (k + S.hc.η_SG + 1) .g2)
    (hk : k ≤ s) (hlo : s + 1 ≤ p) (hhi : p ≤ r) :
    p - 1 ∈ Protocol.latest_window S.hc.η_SG r := by
  obtain ⟨h1, h2⟩ := base_pred_bounds S.hc.η_SG r s p k
    (round_lt_of_early_lt_early S hbudgetRound) hk hlo hhi
  exact mem_latest_window h1 h2



/-- The weight half of the certificate, at any inventory time `tau ≤ b0` whose
honest clock round `sr` is at or above `s + 1` and whose opening has passed.
Both inclusions are `Inclusions.lean` at `tau`; the pairing is
`GradeFormingMajority` at `sr`, whose stale rounds are exactly the retained
rounds of `sr` below `sr - 1` and whose voter round is `sr - 1`. -/
private theorem common_support_weight (S : Setup V) (rho : NamedRun V) (b0 b1 tau : Time)
    (s sr r : Round) (Pn : NamedBlock V)
    (sch : NamedScheduleWellFormed S rho) (auth : NamedUnforgeable S rho)
    (roots : NamedRootCollisionFree S rho) (hR : 3 ≤ S.hc.R)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho) (hPn : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hentry : IntrinsicHighEntryHistory S rho Pn r)
    (hgrid : OnDeltaGrid S tau) (hcutr : tau ≤ domain S.E S.hc r .g1 + 1)
    (hconf : HonestConfirmedAtOrAbove S rho b0 s Pn.erase)
    (hhead : HonestHeadHeldAbove S rho b0 s Pn.erase) (harr : HealthySGArrival S rho b0)
    (hmaj : GradeFormingMajority S rho sr)
    (htau : tau ≤ b0) (hopen : opening S.E S.hc sr ≤ tau)
    (hlo : s + 1 ≤ sr) (hfirst : S.a (r - 1) < b0)
    (hwindow : sr - 1 ∈ Protocol.latest_window S.hc.η_SG r) :
    S.E.electorate.weightOf ((Finset.univ \ rho.honest) ∪
        commonStaleRisks S rho tau Pn sr r) <
      S.E.electorate.weightOf (commonSupporters S rho tau Pn sr r) := by
  have hleft : S.E.electorate.weightOf ((Finset.univ \ rho.honest) ∪
      commonStaleRisks S rho tau Pn sr r) ≤
      S.E.electorate.weightOf ((Finset.univ \ rho.honest) ∪ staleHistoricalVoters S rho sr) :=
    S.E.electorate.weightOf_mono
      (Finset.union_subset_union_right
        (stale_risks_subset_at S rho sch auth roots hR b0 b1 tau htau hgrid s sr r Pn hexec
          hmargin hsleep hPn hno hcutr hconf hhead harr hlo hopen))
  have hright : S.E.electorate.weightOf (honestRoundVoters S rho (sr - 1)) ≤
      S.E.electorate.weightOf (commonSupporters S rho tau Pn sr r) :=
    S.E.electorate.weightOf_mono
      (voters_subset_supporters_at S rho sch auth roots hR b0 b1 tau htau hgrid s sr r Pn hexec
        hmargin hsleep hPn hno hentry hcutr hconf hhead harr hlo hopen hfirst hwindow)
  exact lt_of_le_of_lt hleft (lt_of_lt_of_le hmaj hright)

/-- **The base certificate, round-condition free (before the boundary frame).**

`DomainIncluded` is replaced by the two round facts its components supply to
this proof: the round is positive (case (b) needs `0 ≤ early r.g2`) and it is
at least two above the stable round (case (b) needs round `s + 1`'s support
cutoff to be strictly before round `r`'s G2 early cutoff). The lower bound
`b0 ≤ S.a r` is gone: `tau ≤ S.a r` reads off the inventory time itself
(`tau ≤ early r.g2 ≤ opening r ≤ S.a r`) and `voters_subset_supporters_at` no
longer asks for it.

The stage-1 fold `HonestConfirmedAbove` is also replaced by the two clauses this
proof consumes. That is what makes the certificate usable inside the discharge
of the pre-boundary frame premise: taking the fold here would be circular.

`hbudget` still enters through the numeric retention bound. The known fresh
round `s` supplies the predecessor-round index directly, so no reader lookup
is needed. -/
theorem common_support_base_at_of_early
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V) (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hseed : OutputSeed S rho b0 s Pn.erase) (hPn : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hconf' : HonestConfirmedAtOrAbove S rho b0 s Pn.erase)
    (hhead : HonestHeadHeldAbove S rho b0 s Pn.erase)
    (hbudget : StableRetentionBudget S rho v s Pn.erase b1)
    (hentry : IntrinsicHighEntryHistory S rho Pn r)
    (hrpos : 0 < r) (hgap : s + 1 < r)
    (hearlyCap : early S.E S.hc r .g2 < b1 + S.E.Δ)
    (hfirst : S.a (r - 1) < b0) :
    ∃ supportBoundary : Time, ∃ supportRound : Round,
      supportBoundary = min b0 (early S.E S.hc r .g2) ∧ supportRound ≤ r ∧
      (∀ w ∈ rho.honest, S.hc.round_of
        (NamedRun.stateBeforeTime S rho supportBoundary w).st.core.s = supportRound) ∧
      S.E.electorate.weightOf ((Finset.univ \ rho.honest) ∪
          commonStaleRisks S rho supportBoundary Pn supportRound r) <
        S.E.electorate.weightOf (commonSupporters S rho supportBoundary Pn supportRound r) := by
  have sch : NamedScheduleWellFormed S rho := hexec.core.toNamedScheduleWellFormed
  have auth : NamedUnforgeable S rho := hexec.core.toNamedUnforgeable
  have roots : NamedRootCollisionFree S rho := hexec.core.toNamedRootCollisionFree
  have hR : 3 ≤ S.hc.R := S.hc.R_ge_three
  
  -- restatement of `Proofs.NamedSGArrival.healthy_emitted_sg_at_next_g2` at the
  -- deadline its own proof consumes (`S.a q + S.E.Δ ≤ b0`, not the margin),
  -- applied to the outage execution already in scope.
  have harr : HealthySGArrival S rho b0 := healthySGArrival_of_exec S rho b0 b1 hexec
  have hb0 : 0 ≤ b0 := hexec.interval.1
  have hhor : b0 ≤ rho.horizon := hexec.interval.2.1.trans hexec.interval.2.2
  have hretention : b1 + S.E.Δ ≤
      early S.E S.hc (s + S.hc.η_SG + 1) .g2 := hbudget.1
  set tau : Time := min b0 (early S.E S.hc r .g2) with htaudef
  
  -- the round-`r` G2 early cutoff are), and it is inside the round-`r` opening
  -- read, which is where `NeedsSG` is tested.
  have hgrid : OnDeltaGrid S tau := by
    rw [htaudef]
    exact onDeltaGrid_min S (onDeltaGrid_of_public S b0 hexec.boundaryPublic)
      (onDeltaGrid_early_g2 S r)
  have hcutr : tau ≤ domain S.E S.hc r .g1 + 1 := by
    rw [htaudef]
    exact (min_le_right _ _).trans ((early_le_domain S r).trans (incl_g2_le_opening_cut S r))
  have htau : tau ≤ b0 := min_le_left _ _
  have htaur : tau ≤ S.a r := (min_le_right _ _).trans (base_early_le_a S r)
  have htauhor : tau ≤ rho.horizon := htau.trans hhor
  have huniform : ∀ w ∈ rho.honest, S.hc.round_of
      (NamedRun.stateBeforeTime S rho tau w).st.core.s = boundaryRound S rho tau v :=
    boundaryRound_uniform S rho sch tau v hv
  -- Both branches need the inventory time to be nonnegative and to lie past
  -- round `s + 1`'s support cutoff; only the second is branch-dependent.
  by_cases hearly : b0 ≤ early S.E S.hc r .g2
  · -- Case (a): the boundary is the earlier of the two, so nothing moves.
    have htaueq : tau = b0 := min_eq_left hearly
    have htau0 : (0 : Time) ≤ tau := htaueq ▸ hb0
    have hcut : formationConfirmationTime S (s + 1) < tau :=
      htaueq ▸ lt_of_lt_of_le (lt_add_of_pos_right _ S.E.Δ_pos)
        (old_margin_of_new S s b0 hmargin)
    set rho0 : Round := boundaryRound S rho tau v with hrho0
    have hlo : s + 1 ≤ rho0 := succ_le_boundaryRound S rho sch tau htauhor v hv s hcut
    have hhi : rho0 ≤ r := boundaryRound_le S rho sch tau htau0 v r htaur
    have hpos : 0 < rho0 := lt_of_lt_of_le (Nat.succ_pos s) hlo
    have hopen : opening S.E S.hc rho0 ≤ tau := opening_le_boundary S rho sch tau htau0 v
    -- The support round is covered at its OPENING. `DomainIncluded` gives no
    -- horizon bound at any action time, so the first disjunct of `RoundCovered`
    -- is unavailable; the opening of `rho0` is at or below `b0`, which is at or
    -- below the round-`r` opening, which is inside the horizon.
    have hcov : RoundCovered S rho rho0 :=
      Or.inr ⟨.g1, by rw [base_domain_g1_eq_opening]; exact base_opening_nonneg S rho0,
        by rw [base_domain_g1_eq_opening]
           exact (hopen.trans htau).trans hhor⟩
    have hmaj : GradeFormingMajority S rho rho0 := hforming rho0 hpos hcov
    exact ⟨tau, rho0, rfl, hhi, huniform,
      common_support_weight S rho b0 b1 tau s rho0 r Pn sch auth roots hR hexec hmargin hsleep
        hPn hno hentry hgrid hcutr hconf' hhead harr hmaj htau hopen hlo hfirst
        (predecessor_round_in_window_early S
          (hearlyCap.trans_le hretention) (k := s) (le_refl s) hlo hhi)⟩
  · -- Case (b): the round-`r` G2 early cutoff precedes the boundary, so the
    -- inventory is taken inside the healthy prefix, at that cutoff.
    have htaueq : tau = early S.E S.hc r .g2 := min_eq_right (le_of_lt (not_le.mp hearly))
    have htau0 : (0 : Time) ≤ tau := htaueq ▸ early_nonneg S hR hrpos
    
    -- that leaves an unresolved placeholder here no longer occurs. The support round is
    -- `r - 1 ≥ s + 1` and the pairing round is `r - 2 ≥ s`, where both
    -- `HonestConfirmedAtOrAbove` and `HonestHeadHeldAbove` apply.
    have hcut : formationConfirmationTime S (s + 1) < tau :=
      htaueq ▸ formation_lt_early S hR hgap
    set rho0 : Round := boundaryRound S rho tau v with hrho0
    have hlo : s + 1 ≤ rho0 := succ_le_boundaryRound S rho sch tau htauhor v hv s hcut
    have hhi : rho0 ≤ r := boundaryRound_le S rho sch tau htau0 v r htaur
    have hpos : 0 < rho0 := lt_of_lt_of_le (Nat.succ_pos s) hlo
    have hopen : opening S.E S.hc rho0 ≤ tau := opening_le_boundary S rho sch tau htau0 v
    -- The support round is covered at its OPENING. `DomainIncluded` gives no
    -- horizon bound at any action time, so the first disjunct of `RoundCovered`
    -- is unavailable; the opening of `rho0` is at or below `b0`, which is at or
    -- below the round-`r` opening, which is inside the horizon.
    have hcov : RoundCovered S rho rho0 :=
      Or.inr ⟨.g1, by rw [base_domain_g1_eq_opening]; exact base_opening_nonneg S rho0,
        by rw [base_domain_g1_eq_opening]
           exact (hopen.trans htau).trans hhor⟩
    have hmaj : GradeFormingMajority S rho rho0 := hforming rho0 hpos hcov
    exact ⟨tau, rho0, rfl, hhi, huniform,
      common_support_weight S rho b0 b1 tau s rho0 r Pn sch auth roots hR hexec hmargin hsleep
        hPn hno hentry hgrid hcutr hconf' hhead harr hmaj htau hopen hlo hfirst
        (predecessor_round_in_window_early S
          (hearlyCap.trans_le hretention) (k := s) (le_refl s) hlo hhi)⟩

/-- The original domain-bounded form of `common_support_base_at_of_early`. -/
theorem common_support_base_at
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hseed : OutputSeed S rho b0 s Pn.erase)
    (hPn : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hconf' : HonestConfirmedAtOrAbove S rho b0 s Pn.erase)
    (hhead : HonestHeadHeldAbove S rho b0 s Pn.erase)
    (hbudget : StableRetentionBudget S rho v s Pn.erase b1)
    (hentry : IntrinsicHighEntryHistory S rho Pn r)
    (hrpos : 0 < r) (hgap : s + 1 < r)
    (hrb1 : domain S.E S.hc r .g2 ≤ b1 + S.E.Δ)
    (hfirst : S.a (r - 1) < b0) :
    ∃ supportBoundary : Time, ∃ supportRound : Round,
      supportBoundary = min b0 (early S.E S.hc r .g2) ∧
      supportRound ≤ r ∧
      (∀ w ∈ rho.honest, S.hc.round_of
        (NamedRun.stateBeforeTime S rho supportBoundary w).st.core.s =
          supportRound) ∧
      S.E.electorate.weightOf ((Finset.univ \ rho.honest) ∪
          commonStaleRisks S rho supportBoundary Pn supportRound r) <
        S.E.electorate.weightOf
          (commonSupporters S rho supportBoundary Pn supportRound r) := by
  have hearlyDomain : early S.E S.hc r .g2 < domain S.E S.hc r .g2 := by
    unfold early domain
    simp only [Phase.earlyOffset, Phase.domainOffset]
    nlinarith [S.E.Δ_pos]
  exact common_support_base_at_of_early S rho b0 b1 v s r Pn hexec
    hsleep hforming hv hmargin hseed hPn hno hconf' hhead hbudget hentry
    hrpos hgap (hearlyDomain.trans_le hrb1) hfirst


#print axioms opening_le_boundary
#print axioms round_lt_of_early_lt_early
#print axioms predecessor_round_in_window_early
#print axioms common_support_weight
#print axioms common_support_base_at_of_early
#print axioms common_support_base_at

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
