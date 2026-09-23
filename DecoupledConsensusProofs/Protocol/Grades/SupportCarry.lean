module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.CommonSupportBase
public import DecoupledConsensusProofs.Protocol.Handlers.NonInterference
public import DecoupledConsensusProofs.Protocol.Grades.FrameCompleted
public import DecoupledConsensusProofs.Protocol.Grades.Q10Frame
public import DecoupledConsensusProofs.Protocol.Grades.Grades
public import DecoupledConsensusProofs.Protocol.Handlers.ConfirmationMembership
public import DecoupledConsensusProofs.Protocol.Grades.ProposalParent
public import DecoupledConsensusInternal.Definitions.NamedJointOutage

@[expose] public section


namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedJointOutage DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]


local instance decidableNeedsSGSupportCarry (S : Setup V) (rho : NamedRun V)
    (P : NamedBlock V) (r : Round) (v : V) :
    Decidable (NeedsSG S rho P r v) :=
  inferInstanceAs (Decidable (¬ Block.Preceq P.erase
    (NamedRun.readAt S rho (domain S.E S.hc r .g1) v).st.core.F))


/-! ## Selector projections (copies of the private helpers of `RoundStep`) -/

omit [Fintype V] in
/-- Every filtered-tree member sits above the FG root. -/
private theorem carry_filtered_root_preceq {st : Protocol.FGStore V} {B : Block V}
    (h : B ∈ Protocol.get_filtered_block_tree st) :
    Block.Preceq (Protocol.get_fg_root st) B := by
  simp only [Protocol.get_filtered_block_tree, Protocol.get_filtered_block_tree_from,
    Finset.mem_filter] at h
  exact h.2

omit [Fintype V] in
/-- `deepest_clear` respects its floor: it ranges over blocks above it. -/
private theorem carry_deepest_clear_floor {floor C B : Block V} {test : Block V → Bool}
    (h : Protocol.deepest_clear (some floor) C test = some B) : Block.Preceq floor B := by
  unfold Protocol.deepest_clear at h
  exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem h)).2.1

/-- The frame anchor is at or above the FG root: it is either the root itself
or a member of the filtered tree, which the root precedes. -/
private theorem carry_root_preceq_anchor (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) (g1 : Option (Option (Block V))) :
    Block.Preceq (Protocol.get_fg_root st.toFG)
      (DecoupledConsensusModel.Protocol.anchor E hc st r g1) := by
  cases g1 with
  | none => exact Block.preceq_self _
  | some opt =>
    cases opt with
    | none => exact Block.preceq_self _
    | some root =>
      change Block.Preceq (Protocol.get_fg_root st.toFG)
        ((DecoupledConsensusModel.Protocol.activePrefix
          (Protocol.get_filtered_block_tree st.toFG) root).getD
            (Protocol.get_fg_root st.toFG))
      cases hp : DecoupledConsensusModel.Protocol.activePrefix
          (Protocol.get_filtered_block_tree st.toFG) root with
      | none => simpa only [hp, Option.getD_none] using Block.preceq_self _
      | some X =>
        simpa only [hp, Option.getD_some] using
          carry_filtered_root_preceq (NamedProposalParent.activePrefix_mem _ root X hp)

/-! ## Round `0` is before the outage boundary -/

private theorem carry_margin_arith : ∀ d M b : Int, 0 < d → 12 * d ≤ M → M + 3 * d ≤ b →
    6 * d < b := by
  intro d M b h1 h2 h3
  omega

private theorem carry_twelve_le : ∀ d n : Int, 0 < d → 3 ≤ n → 12 * d ≤ 4 * d * n := by
  intro d n hd hn
  have h4 : (0 : Int) ≤ 4 * d := by omega
  have hstep := Int.mul_le_mul_of_nonneg_left hn h4
  calc 12 * d = 4 * d * 3 := by ring
    _ ≤ 4 * d * n := hstep

private theorem carry_three_le_mul (s R : Nat) (hR : 3 ≤ R) : 3 ≤ (s + 1) * R := by
  calc 3 ≤ R := hR
    _ = 1 * R := (Nat.one_mul R).symm
    _ ≤ (s + 1) * R := Nat.mul_le_mul_right R (Nat.succ_le_succ (Nat.zero_le s))

/-- The formation margin puts round `0`'s action strictly before the boundary.
`S.a 0 = 6Δ` and the margin already reaches `4ΔR + 3Δ ≥ 15Δ`. -/
private theorem carry_a_zero_lt (S : Setup V) (b0 : Time) (s : Round)
    (hR : 3 ≤ S.hc.R) (hmargin : FormationMargin S s b0) : S.a 0 < b0 := by
  have hd : (0 : Time) < S.E.Δ := S.E.Δ_pos
  have ha0 : S.a 0 = 6 * S.E.Δ := by
    simp only [Setup.a, Protocol.HealConfig.a, Protocol.HealConfig.opening_slot, slotStart,
      Nat.zero_mul, Nat.cast_zero, mul_zero, zero_add]
  have hform : formationConfirmationTime S (s + 1) =
      4 * S.E.Δ * (((s + 1) * S.hc.R : Nat) : Int) + 2 * S.E.Δ := by
    simp only [formationConfirmationTime, Protocol.support_cutoff, Env.t, slotStart,
      Protocol.HealConfig.opening_slot]
  have hn : (3 : Int) ≤ (((s + 1) * S.hc.R : Nat) : Int) := by
    exact_mod_cast carry_three_le_mul s S.hc.R hR
  have hM : 12 * S.E.Δ ≤ 4 * S.E.Δ * (((s + 1) * S.hc.R : Nat) : Int) :=
    carry_twelve_le S.E.Δ _ hd hn
  have hb : 4 * S.E.Δ * (((s + 1) * S.hc.R : Nat) : Int) + 3 * S.E.Δ ≤ b0 := by
    have := old_margin_of_new S s b0 hmargin
    rw [hform] at this
    calc 4 * S.E.Δ * (((s + 1) * S.hc.R : Nat) : Int) + 3 * S.E.Δ
        = 4 * S.E.Δ * (((s + 1) * S.hc.R : Nat) : Int) + 2 * S.E.Δ + S.E.Δ := by ring
      _ ≤ b0 := this
  rw [ha0]
  exact carry_margin_arith S.E.Δ _ b0 hd hM hb


private theorem carry_a_le_next_early : ∀ x d M : Int, 0 < d → 12 * d ≤ M →
    x + 6 * d ≤ x + M + (-5) * d := by
  intro x d M h1 h2
  omega


/-- The next round's G2 early cutoff is at or after this round's action time:
consecutive openings are `4ΔR` apart and `R ≥ 3`, so the gap `4ΔR ≥ 12Δ` covers
the `6Δ` action offset and the `5Δ` early offset together. This is what makes
`min b0 (early (r+1).g2) = b0` at every round after the first included one
(addendum 34 9). -/
private theorem carry_a_le_early_succ (S : Setup V) (r : Round) (hR : 3 ≤ S.hc.R) :
    S.a r ≤ early S.E S.hc (r + 1) .g2 := by
  have hd : (0 : Time) < S.E.Δ := S.E.Δ_pos
  have ha : S.a r = opening S.E S.hc r + 6 * S.E.Δ := by
    simp only [Setup.a, Protocol.HealConfig.a, opening, Protocol.proposal_time, Env.t]
  have hopen : opening S.E S.hc (r + 1) =
      opening S.E S.hc r + 4 * S.E.Δ * (S.hc.R : Int) := by
    simp only [opening, Protocol.proposal_time, Env.t, slotStart, Protocol.HealConfig.opening_slot]
    push_cast
    ring
  have hRint : (3 : Int) ≤ (S.hc.R : Int) := by exact_mod_cast hR
  have hM : 12 * S.E.Δ ≤ 4 * S.E.Δ * (S.hc.R : Int) := carry_twelve_le S.E.Δ _ hd hRint
  have hearly : early S.E S.hc (r + 1) .g2 = opening S.E S.hc (r + 1) + (-5) * S.E.Δ := rfl
  rw [ha, hearly, hopen]
  exact carry_a_le_next_early _ S.E.Δ _ hd hM



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

/-- The formation margin puts the round `s + 1` opening-slot support cutoff
strictly before `b0`, so the honest clock at `b0` has already entered round
`s + 1`. -/
private theorem succ_le_boundaryRound (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (b0 : Time) (hb0 : b0 ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) (s : Round) (hmargin : FormationMargin S s b0) :
    s + 1 ≤ boundaryRound S rho b0 v := by
  set τ : Time := formationConfirmationTime S (s + 1) with hτ
  have hΔ : (0 : Time) < S.E.Δ := S.E.Δ_pos
  have hlt : τ < b0 :=
    lt_of_lt_of_le (lt_add_of_pos_right τ hΔ) (old_margin_of_new S s b0 hmargin)
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


/-! ## The SG vote of one frame read

`Protocol.get_sg_vote_with` on the frame contract is `Protocol.currentSGVote` with
the frame's anchor, the frame's grade-2 block as `Q2`, the frame's `clear` test
and `rawG2`. The two lemmas below cover it by its four tiers. -/

omit [Fintype V] in
/-- All four tiers at once: the walk is above the anchor, the `Q2` tier is
handled by `hQ2`, and the two last-resort tiers are the FG root and the anchor. -/
private theorem carry_currentSGVote_above (st : Protocol.HealingStore V)
    (grades : Protocol.GradeRead V) (P : Block V)
    (hanchor : Block.Preceq P grades.anchor)
    (hQ2 : ∀ q, grades.Q2 = some q → Block.Preceq P q)
    (hroot : Block.Preceq P (Protocol.get_fg_root st.toFG)) :
    Block.Preceq P (Protocol.currentSGVote st grades) := by
  unfold Protocol.currentSGVote
  split
  · rename_i B hB
    exact Block.preceq_trans hanchor (carry_deepest_clear_floor hB)
  · split
    · rename_i q hq
      exact hQ2 q hq
    · split_ifs
      · exact hroot
      · exact hanchor

omit [Fintype V] in
/-- The `Q2` variant: when the grade-2 block exists and sits below the anchor,
only the walk tier and the `Q2` tier are reachable, and both are above `P`. -/
private theorem carry_currentSGVote_above_of_Q2 (st : Protocol.HealingStore V)
    (grades : Protocol.GradeRead V) (P q : Block V)
    (hq : grades.Q2 = some q) (hPq : Block.Preceq P q)
    (hqa : Block.Preceq q grades.anchor) :
    Block.Preceq P (Protocol.currentSGVote st grades) := by
  unfold Protocol.currentSGVote
  split
  · rename_i B hB
    exact Block.preceq_trans (Block.preceq_trans hPq hqa) (carry_deepest_clear_floor hB)
  · split
    · rename_i q' hq'
      rw [hq] at hq'
      exact (Option.some.inj hq') ▸ hPq
    · rename_i hnone
      rw [hq] at hnone
      exact absurd hnone (by simp)

omit [Fintype V] in
/-- A frame grade-2 block is a filtered-tree member. -/
private theorem carry_grade2_mem_tree {st : Protocol.HealingStore V}
    {frame : DecoupledConsensusModel.Protocol.Frame V} {q : Block V}
    (h : DecoupledConsensusModel.Protocol.grade2Block st frame = some q) :
    q ∈ Protocol.get_filtered_block_tree st.toFG := by
  unfold DecoupledConsensusModel.Protocol.grade2Block at h
  by_cases hcl : DecoupledConsensusModel.Protocol.allClosed frame = true
  · rw [if_pos hcl] at h
    obtain ⟨x, _, hx⟩ := Option.bind_eq_some_iff.mp h
    exact NamedProposalParent.activePrefix_mem _ x q hx
  · rw [if_neg hcl] at h
    exact absurd h (by simp)

/-! ## Row Q10: the grade-2 block is at or below the anchor -/

/-- The frames analogue of `Proofs.HealingLemmas.grade2_preceq_fresh_anchor`. In the
default contract the grade-1 anchor and the grade-2 block are `deepest?` values
of two nested grade sets of ONE store, so `G2 ⪯ G1` is single-snapshot algebra
(`G2_imp_G1` plus `G1_compatible`). In the frame runtime the two roots are
frozen at two different phase ticks — `domain r.g2 = opening r − Δ` and
`domain r.g1 = opening r` — so the comparison crosses two stores of the SAME
honest node. `Q10Frame.lean` makes that crossing; the statement below is its
action-read instance, and the `subst` is the only work done here.

The action read is the checkpoint followed by `update_confirmation_with`, which
writes only `live_confirmed` and `latest_confirmed`; the cache, `F`, the tree,
the FG root and the filtered tree are unchanged, so the row Q10 statement at the
checkpoint is the row Q10 statement at the action read by `rfl`. -/
private theorem carry_grade2_preceq_anchor (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) (v : V) (hv : v ∈ rho.honest) (b0 : Time) (r : Round)
    (hinc : RoundIncluded S rho b0 r) (n : NamedNodeState V)
    (hn : n = actionReadFrom S (NamedRun.stateBeforeTime S rho (S.a r) v) r) (q : Block V)
    (hq : DecoupledConsensusModel.Protocol.grade2Block n.st.core.toHealing
      (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r) = some q) :
    Block.Preceq q (DecoupledConsensusModel.Protocol.anchor S.E S.hc n.st.core.toHealing r
      (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g1) := by
  subst hn
  exact grade2_preceq_anchor_at_checkpoint S rho core v hv b0 r hinc q hq

private theorem carry_dom_arith : ∀ x d : Int, 0 < d →
    x + 1 * d < x + 6 * d ∧ x + 0 * d < x + 6 * d ∧ x + (-1) * d < x + 6 * d := by
  intro x d h
  exact ⟨by omega, by omega, by omega⟩

/-- Every phase domain tick of round `r` is strictly before its action time:
the offsets are `Δ`, `0` and `−Δ` against `a_r = opening r + 6Δ`. -/
private theorem carry_domain_lt_a (S : Setup V) (r : Round) (p : Phase) :
    domain S.E S.hc r p < S.a r := by
  have ha : S.a r = opening S.E S.hc r + 6 * S.E.Δ := by
    simp only [Setup.a, Protocol.HealConfig.a, opening, Protocol.proposal_time, Env.t]
  have hdom : domain S.E S.hc r p = opening S.E S.hc r + p.domainOffset * S.E.Δ := rfl
  obtain ⟨h1, h0, hm⟩ := carry_dom_arith (opening S.E S.hc r) S.E.Δ S.E.Δ_pos
  rw [ha, hdom]
  cases p with
  | g0 => exact h1
  | g1 => exact h0
  | g2 => exact hm


/-- Forward cache provenance at the checkpoint, from the L5′ branches
(`FrameCompleted.frame_phase_completed` plus
`FrameForward.frame_phase_checkpoint_eq`): at the round-`r` checkpoint of an
included round all three phase results of the round-`r` frame are completed.
This is what makes `grade2_block_with` agree with `activeG2`. -/
private theorem carry_allClosed_at_checkpoint (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) (v : V) (hv : v ∈ rho.honest)
    (b0 : Time) (r : Round) (hinc : RoundIncluded S rho b0 r) :
    DecoupledConsensusModel.Protocol.allClosed
      (DecoupledConsensusModel.Protocol.readFrame (checkpoint S rho v r).cache
        (checkpoint S rho v r).st.core.toHealing r) = true := by
  have hslot : ∀ p : Phase, ∃ x, phaseResult (DecoupledConsensusModel.Protocol.readFrame
      (checkpoint S rho v r).cache (checkpoint S rho v r).st.core.toHealing r) p = some x := by
    intro p
    exact ⟨_, FrameForward.frame_phase_checkpoint_eq S rho v r p _
      (FrameCompleted.frame_phase_completed S rho core v hv r hinc.1 p (S.a r)
        (carry_domain_lt_a S r p) le_rfl ((carry_domain_lt_a S r p).le.trans hinc.2.2))⟩
  obtain ⟨x0, h0⟩ := hslot .g0
  obtain ⟨x1, h1⟩ := hslot .g1
  obtain ⟨x2, h2⟩ := hslot .g2
  have h0' : (DecoupledConsensusModel.Protocol.readFrame (checkpoint S rho v r).cache
    (checkpoint S rho v r).st.core.toHealing r).g0 = some x0 := h0
  have h1' : (DecoupledConsensusModel.Protocol.readFrame (checkpoint S rho v r).cache
    (checkpoint S rho v r).st.core.toHealing r).g1 = some x1 := h1
  have h2' : (DecoupledConsensusModel.Protocol.readFrame (checkpoint S rho v r).cache
    (checkpoint S rho v r).st.core.toHealing r).g2 = some x2 := h2
  simp only [DecoupledConsensusModel.Protocol.allClosed, h0', h1', h2', Option.isSome_some,
    Bool.and_self]



private theorem carry_a_eq (S : Setup V) (k : Round) :
    S.a k = 4 * S.E.Δ * ((S.hc.opening_slot k : Nat) : Int) + 6 * S.E.Δ := by
  unfold Setup.a Protocol.HealConfig.a slotStart
  ring

private theorem carry_domain_g1_eq (S : Setup V) (k : Round) :
    domain S.E S.hc k .g1 = 4 * S.E.Δ * ((S.hc.opening_slot k : Nat) : Int) := by
  unfold domain opening Phase.domainOffset Protocol.proposal_time Env.t slotStart
  ring

private theorem carry_succ_le_add_six : ∀ x d : Int, 0 < d → x + 1 ≤ x + 6 * d := by
  intro x d hd; omega

/-- The strict cut that realises the round-`r` opening read is still at or
before the round action. -/
private theorem carry_opening_cut_le_a (S : Setup V) (r : Round) :
    domain S.E S.hc r .g1 + 1 ≤ S.a r := by
  rw [carry_domain_g1_eq, carry_a_eq]
  exact carry_succ_le_add_six _ _ S.E.Δ_pos

/-- Copy of the private `readAt_eq_stateBeforeTime_succ` of `NonInterference`:
`readAt` keeps every event with `e.time ≤ t`, so it is the strict fold at
`t + 1`. -/
private theorem carry_readAt_eq_succ (S : Setup V) (rho : NamedRun V) (t : Time) :
    NamedRun.readAt S rho t = NamedRun.stateBeforeTime S rho (t + 1) := by
  have hp : (fun e : NamedEvent V => decide (e.time ≤ t)) =
      fun e : NamedEvent V => decide (e.time < t + 1) := by
    funext e
    exact decide_eq_decide.mpr Int.lt_add_one_iff.symm
  unfold NamedRun.readAt NamedRun.stateBeforeTime
  rw [hp]

omit [Fintype V] in
/-- Copy of the private `sg_clip_preceq` of `SGFromSupport`. -/
private theorem carry_clip_preceq (g F : Block V) :
    Block.Preceq (DecoupledConsensusModel.Protocol.clipGrade g F) g := by
  induction g with
  | genesis => exact Block.preceq_self _
  | node p s root gv gsv ats v ih =>
    simp only [DecoupledConsensusModel.Protocol.clipGrade]
    split
    · exact Block.preceq_self _
    · apply Block.preceq_trans ih
      simp only [Block.preceq, Bool.or_eq_true]
      exact Or.inr (Block.preceq_self p)

omit [Fintype V] in
/-- Copy of the private `sg_retained_prefix` of `SGFromSupport`. -/
private theorem carry_retained_prefix (g F B : Block V)
    (hBF : Block.compatible B F = true) :
    Block.Preceq B (DecoupledConsensusModel.Protocol.clipGrade g F) ↔ Block.Preceq B g := by
  constructor
  · intro h
    exact Block.preceq_trans h (carry_clip_preceq g F)
  · induction g with
    | genesis => exact fun h => h
    | node p s root gv gsv ats v ih =>
      intro hBg
      by_cases hGF : Block.compatible (.node p s root gv gsv ats v) F = true
      · simpa only [DecoupledConsensusModel.Protocol.clipGrade, hGF, ↓reduceIte] using hBg
      · have hBp : Block.Preceq B p := by
          simp only [Block.Preceq, Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at hBg
          rcases hBg with hEq | hBp
          · subst B
            exact False.elim (hGF hBF)
          · exact hBp
        simpa only [DecoupledConsensusModel.Protocol.clipGrade, hGF,
          Bool.eq_false_iff.mpr hGF, ↓reduceIte] using ih hBp

/-- Copy of the private `sg_active_g2_of_frame` of `SGFromSupport`: the active
prefix of a P-covering frame root covers P, provided P is in the reader's
filtered tree. -/
private theorem carry_active_g2_of_frame (S : Setup V) (n : NamedNodeState V) (r : Round)
    (hround : S.hc.round_of n.st.core.s = r) {raw P : Block V}
    (hg2 : (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g2 = some (some raw))
    (hmem : P ∈ Protocol.get_filtered_block_tree n.st.core.toHealing.toFG)
    (hPraw : Block.Preceq P raw) :
    ∃ G : Block V, activeG2 S n = some G ∧ Block.Preceq P G := by
  have hact : activeG2 S n =
      activePrefix (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG) raw := by
    change ((DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing
      (S.hc.round_of n.st.core.s)).g2.bind id).bind _ = _
    rw [hround, hg2]
    rfl
  set T := (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG).filter
    fun B => Block.preceq B raw = true with hT
  have hPT : P ∈ T := Finset.mem_filter.mpr ⟨hmem, hPraw⟩
  have hcmp : ∀ X ∈ T, ∀ Y ∈ T, Block.compatible X Y = true := by
    intro X hX Y hY
    exact Block.compatible_of_preceq_common (Finset.mem_filter.mp hX).2
      (Finset.mem_filter.mp hY).2
  obtain ⟨G, hG⟩ := Option.isSome_iff_exists.mp
    (Proofs.HealingSurface.deepest?_isSome_of_compatible hcmp ⟨P, hPT⟩)
  exact ⟨G, by rw [hact]; exact hG,
    Proofs.HealingLemmas.deepest?_dominates hG hPT (hcmp P hPT G (Proofs.Engine.deepest?_mem hG))⟩

/-- **The `sg` field at the round-`r` checkpoint.** The invariant states its SG
field at the round opening; every consumer that reads a signer's own action
inputs needs it at the checkpoint, `6Δ` later and inside the same round, and in
the candidate form rather than the raw-root form.

Both arms transport, with no added premise.

* The exemption arm is `P ⪯ F` at the opening. `F` is monotone along a run
  (`Proofs.NamedRuntime.stateBefore_F_mono`), so it reaches the checkpoint, and
  `preceq_fg_root_of_preceq_F` turns it into the goal's FG-root disjunct,
  because `get_fg_root` is `J` under the cascade gate and `F` otherwise, with
  `F ⪯ J`.
* The frame arm is the raw frozen root. `FrameForward.frame_g2_at_checkpoint`
  carries the saved round-`r` G2 slot to the checkpoint, clipped against the
  checkpoint's own `F`, and the invariant's `fg` field supplies the two facts
  the `activePrefix` step then needs there: the protected prefix is compatible
  with that `F`, and it is in the reader's filtered tree — or else it is already
  at or below the reader's FG root, which is the goal's first disjunct outright.

`hhor` is the guard of the invariant's `fg` field and is available at every
consumer, because the consumer's read is an actual honest tick of `S.a r`. -/
theorem sg_field_at_checkpoint_of_clauses
    (S : Setup V) (rho : NamedRun V) (_b0 : Time)
    (Pn : NamedBlock V) (r : Round) (core : NamedAdmissibleCore S rho)
    (hsg : ∀ v ∈ rho.honest,
      let n := NamedRun.readAt S rho (domain S.E S.hc r .g1) v
      Block.Preceq Pn.erase n.st.core.F ∨
        ∃ raw : Block V,
          (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g2 =
            some (some raw) ∧ Block.Preceq Pn.erase raw)
    (hjoint : ∀ v ∈ rho.honest,
      (Block.Preceq Pn.erase
          (Protocol.get_fg_root
            (checkpoint S rho v r).st.core.toHealing.toFG) ∨
        Pn.erase ∈ Protocol.get_filtered_block_tree
          (checkpoint S rho v r).st.core.toHealing.toFG) ∧
      Block.compatible Pn.erase (checkpoint S rho v r).st.core.F = true)
    (v : V) (hv : v ∈ rho.honest) :
    Block.Preceq Pn.erase
        (Protocol.get_fg_root (checkpoint S rho v r).st.core.toHealing.toFG) ∨
      ∃ raw G : Block V,
        (DecoupledConsensusModel.Protocol.readFrame (checkpoint S rho v r).cache
          (checkpoint S rho v r).st.core.toHealing r).g2 = some (some raw) ∧
        activeG2 S (checkpoint S rho v r) = some G ∧ Block.Preceq Pn.erase G := by
  have sch : NamedScheduleWellFormed S rho := core.toNamedScheduleWellFormed
  have hsg : Block.Preceq Pn.erase
        (NamedRun.readAt S rho (domain S.E S.hc r .g1) v).st.core.F ∨
      ∃ raw : Block V,
        (DecoupledConsensusModel.Protocol.readFrame
          (NamedRun.readAt S rho (domain S.E S.hc r .g1) v).cache
          (NamedRun.readAt S rho (domain S.E S.hc r .g1) v).st.core.toHealing r).g2 =
            some (some raw) ∧
        Block.Preceq Pn.erase raw := hsg v hv
  have hbridge : NamedRun.readAt S rho (domain S.E S.hc r .g1) v =
      NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1 + 1) v := by
    rw [carry_readAt_eq_succ]
  rcases hsg with hF0 | ⟨raw, hg2, hPraw⟩
  · -- the exemption arm: the finalized block only grows
    left
    have hF0' : Block.Preceq Pn.erase
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1 + 1) v).st.core.F := by
      rw [← hbridge]; exact hF0
    have hFmono : Block.Preceq
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1 + 1) v).st.core.F
        (NamedRun.stateBeforeTime S rho (S.a r) v).st.core.F := by
      rw [strict_read_eq_index S rho sch.sorted (domain S.E S.hc r .g1 + 1),
        strict_read_eq_index S rho sch.sorted (S.a r)]
      exact Proofs.NamedRuntime.stateBefore_F_mono S rho v
        (strict_lengths_mono rho (carry_opening_cut_le_a S r))
    exact preceq_fg_root_of_preceq_F S rho (S.a r) v Pn.erase
      (Block.preceq_trans hF0' hFmono)
  · -- the frame arm: the raw root carries, and the candidate is rebuilt here
    have hjointV : (Block.Preceq Pn.erase
          (Protocol.get_fg_root (checkpoint S rho v r).st.core.toHealing.toFG) ∨
        Pn.erase ∈ Protocol.get_filtered_block_tree
          (checkpoint S rho v r).st.core.toHealing.toFG) ∧
      Block.compatible Pn.erase (checkpoint S rho v r).st.core.F = true :=
      hjoint v hv
    rcases hjointV.1 with hpast | hmem
    · exact Or.inl hpast
    · right
      have hg2strict : (DecoupledConsensusModel.Protocol.readFrame
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1 + 1) v).cache
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1 + 1) v).st.core.toHealing
            r).g2 = some (some raw) := by
        rw [← hbridge]; exact hg2
      have hck : (DecoupledConsensusModel.Protocol.readFrame (checkpoint S rho v r).cache
          (checkpoint S rho v r).st.core.toHealing r).g2 =
          some (some (DecoupledConsensusModel.Protocol.clipGrade raw
            (checkpoint S rho v r).st.core.F)) :=
        FrameForward.frame_g2_at_checkpoint S rho core v r (domain S.E S.hc r .g1 + 1)
          (carry_opening_cut_le_a S r) (some raw) hg2strict
      have hPclip : Block.Preceq Pn.erase (DecoupledConsensusModel.Protocol.clipGrade raw
          (checkpoint S rho v r).st.core.F) :=
        (carry_retained_prefix raw _ Pn.erase hjointV.2).mpr hPraw
      obtain ⟨G, hG, hPG⟩ := carry_active_g2_of_frame S (checkpoint S rho v r) r
        (Proofs.HealingLemmas.round_of_slotOf_a S r) hck hmem hPclip
      exact ⟨_, G, hck, hG, hPG⟩

/-- The invariant form of `sg_field_at_checkpoint_of_clauses`. -/
theorem sg_field_at_checkpoint (S : Setup V) (rho : NamedRun V) (b0 : Time)
    (Pn : NamedBlock V) (r : Round) (core : NamedAdmissibleCore S rho)
    (hinv : RoundInvariant S rho b0 Pn r) (hhor : S.a r ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) :
    Block.Preceq Pn.erase
        (Protocol.get_fg_root (checkpoint S rho v r).st.core.toHealing.toFG) ∨
      ∃ raw G : Block V,
        (DecoupledConsensusModel.Protocol.readFrame (checkpoint S rho v r).cache
          (checkpoint S rho v r).st.core.toHealing r).g2 = some (some raw) ∧
        activeG2 S (checkpoint S rho v r) = some G ∧
        Block.Preceq Pn.erase G := by
  exact sg_field_at_checkpoint_of_clauses S rho b0 Pn r core hinv.sg
    (hinv.fg hhor) v hv

#print axioms sg_field_at_checkpoint_of_clauses
#print axioms sg_field_at_checkpoint

/-! ## Theorem A: post-boundary honest coverage from the invariant -/

omit [Fintype V] in
/-- Copied from the private helper of the same name in `RoundStep`. -/
private theorem carry_named_self (B : NamedBlock V) : NamedBlock.Preceq B B := by
  cases B <;> simp [NamedBlock.Preceq, NamedBlock.preceq]

/-- Every honest SG vote emitted at or after the outage boundary, in a round
below `r`, confirms a block that the protected prefix precedes. This is the
post-boundary half of L5's `(C′)`, derived from the round invariant at every
included round strictly below `r` rather than assumed.

The round of such an emission is included: the action time is at or after `b0`
by hypothesis, at or below the horizon because the tick is a run event, and
positive because `FormationMargin` puts round `0`'s action strictly before
`b0`. The invariant's `sg` field at the signer's own checkpoint is a statement
about that signer's own selector inputs, since the action read is the
checkpoint followed by `update_confirmation_with`. -/
theorem honest_confirmed_above_of_invariant
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s : Round) (Pn : NamedBlock V) (r : Round)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hinv : ∀ q : Round, RoundIncluded S rho b0 q → q < r → RoundInvariant S rho b0 Pn q) :
    ∀ (a : NamedAttestation V) (t : Time), a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (.attest a) t → b0 ≤ t → a.round < r →
      ∀ key, a.confirmed = some key →
        ∀ K : NamedBlock V, NamedRun.blockInRun S rho K → K.root = key →
          Block.Preceq Pn.erase K.erase := by
  intro a t ha hem hb0t hlt key hkey K hKrun hKroot
  obtain ⟨i, hi, _hemAt, hrow, _hval, hro, ht, _hawake⟩ :=
    Proofs.NamedOutageInputs.emitted_attestation_stages S rho hem
  subst ht
  -- the round of the emission is included
  have hmemEv : NamedEvent.tick a.val_index (S.a a.round) ∈ rho.events :=
    List.mem_iff_getElem?.mpr ⟨i, hi⟩
  have hhor : S.a a.round ≤ rho.horizon :=
    (hexec.core.toNamedScheduleWellFormed.in_horizon _ hmemEv).2
  have hpos : 0 < a.round := by
    by_contra hcon
    have hz : a.round = 0 := Nat.le_zero.mp (Nat.le_of_not_lt hcon)
    rw [hz] at hb0t
    exact absurd hb0t (not_le.mpr (carry_a_zero_lt S b0 s S.hc.R_ge_three hmargin))
  have hinvq := hinv a.round ⟨hpos, hb0t, hhor⟩ hlt
  -- the signer's action read is the checkpoint plus `update_confirmation_with`
  have hprefix : NamedRun.stateBefore S rho i a.val_index =
      NamedRun.stateBeforeTime S rho (S.a a.round) a.val_index :=
    Proofs.NamedRuntime.tick_prefix_eq_strict S rho hexec.core.sorted hexec.core.nodup hi
  have hck : checkpoint S rho a.val_index a.round =
      confirmationReadFrom S (NamedRun.stateBefore S rho i a.val_index) (S.a a.round) := by
    rw [hprefix]
    rfl
  set before := NamedRun.stateBefore S rho i a.val_index with hbefore
  set n := actionReadFrom S before a.round with hn
  set gc := NamedProfile.gradeContract n.cache with hgc
  
  -- opening; the signer's own selector inputs are read at the checkpoint.
  have hsg := sg_field_at_checkpoint S rho b0 Pn a.round hexec.core hinvq hhor a.val_index ha
  rw [hck] at hsg
  have hround : S.hc.round_of
      (confirmationReadFrom S before (S.a a.round)).st.core.toHealing.s = a.round :=
    Proofs.HealingLemmas.round_of_slotOf_a S a.round
  -- the emitted row's confirmed key IS the SG vote root of that read
  set Bsg := Protocol.get_sg_vote_with gc S.E S.hc n.st.core.toHealing a.round
    (Protocol.grade2_block_with gc S.E S.hc n.st.core.toHealing a.round) with hBsg
  have hconf : a.confirmed = some Bsg.root := by
    rw [← hrow, hBsg, hro]
    rfl
  have hkeyB : key = Bsg.root := Option.some.inj (hkey.symm.trans hconf)
  -- the SG vote is a retained body, and root collision-freeness pins it to `K`
  have hinvariant := Proofs.NamedOutageInputs.action_read_invariant S rho i a.val_index a.round
  have hBmem : Bsg ∈ n.st.core.T := by
    have hmem := Proofs.NamedConfirmationMembership.sg_head_mem n.cache S.E S.hc S.cfg n.st
      hinvariant
    rw [← hro] at hmem
    exact hmem
  have htree : n.st.core.T = n.st.bodies.image NamedBlock.erase := hinvariant.1.1.1
  rw [htree] at hBmem
  obtain ⟨H, hH, hHe⟩ := Finset.mem_image.mp hBmem
  have hHrun : NamedRun.blockInRun S rho H :=
    Proofs.NamedRuntime.blockInRun_of_direct S rho
      (Proofs.NamedRuntime.directBlock_of_prefix S rho ha i hH)
  have hHroot : H.root = K.root := by
    rw [hKroot, hkeyB, ← hHe, Proofs.NamedWire.erase_root]
  have hHK : H = K :=
    hexec.core.toNamedRootCollisionFree.root_injective H K hHrun hKrun H K
      (Or.inl (carry_named_self H)) (Or.inr (carry_named_self K)) hHroot
  rw [← hHK, hHe]
  -- the coverage of the SG vote itself
  have hanchorRoot : Block.Preceq (Protocol.get_fg_root n.st.core.toHealing.toFG)
      (DecoupledConsensusModel.Protocol.anchor S.E S.hc n.st.core.toHealing a.round
        (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing a.round).g1) :=
    carry_root_preceq_anchor S.E S.hc n.st.core.toHealing a.round _
  rcases hsg with hrootArm | ⟨raw, G, hframe, hG, hPG⟩
  · -- arm 1: the prefix is already below the reader's FG root
    have hrootArm' : Block.Preceq Pn.erase
        (Protocol.get_fg_root n.st.core.toHealing.toFG) := hrootArm
    refine carry_currentSGVote_above n.st.core.toHealing _ Pn.erase
      (Block.preceq_trans hrootArm' hanchorRoot) (fun q hq => ?_) hrootArm'
    exact Block.preceq_trans hrootArm' (carry_filtered_root_preceq (carry_grade2_mem_tree hq))
  · -- arm 2: the prefix is below the reader's active grade-2 block
    have hGn : ((DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing a.round).g2.bind
          id).bind
        (DecoupledConsensusModel.Protocol.activePrefix
          (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG)) = some G := by
      have hGc := hG
      unfold activeG2 DecoupledConsensusModel.Protocol.frameSGCandidate at hGc
      rw [hround] at hGc
      exact hGc
    have hclosed : DecoupledConsensusModel.Protocol.allClosed
        (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing a.round) = true := by
      have hcl := carry_allClosed_at_checkpoint S rho hexec.core a.val_index ha b0 a.round
        ⟨hpos, hb0t, hhor⟩
      rw [hck] at hcl
      exact hcl
    have hQ2eq : DecoupledConsensusModel.Protocol.grade2Block n.st.core.toHealing
        (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing a.round) = some G := by
      unfold DecoupledConsensusModel.Protocol.grade2Block
      rw [if_pos hclosed]
      exact hGn
    have hnstrict : n = actionReadFrom S
        (NamedRun.stateBeforeTime S rho (S.a a.round) a.val_index) a.round := by
      rw [hn, hprefix]
    exact carry_currentSGVote_above_of_Q2 n.st.core.toHealing _ Pn.erase G hQ2eq hPG
      (carry_grade2_preceq_anchor S rho hexec.core a.val_index ha b0 a.round
        ⟨hpos, hb0t, hhor⟩ n hnstrict G hQ2eq)

#print axioms honest_confirmed_above_of_invariant

/-! ## Theorem B: the support carry

The certificate does not carry with the invariant's own witnesses: every
conjunct of `commonSupporters` is guarded by `NeedsSG … r`, whose reader set
changes with the round, and clause 2's window bound `latest_window η r` is not
inherited by `latest_window η (r + 1)`. The step therefore re-runs the base
argument of `CommonSupportBase.common_support_base` at `r + 1`, with the same
two witnesses (`b0` and the honest clock round at `b0`). The single premise of
that argument which fails after the boundary is `hfirst`, the claim that every
row in the round's window is a pre-outage emission; `hpost` replaces it. -/

private theorem carry_sub_eta_le_pred : ∀ n e : Nat, 1 ≤ e → n - e ≤ n - 1 := by
  intro n e h; omega

private theorem carry_pred_succ : ∀ s n : Nat, s + 1 ≤ n → n - 1 + 1 = n := by
  intro s n h; omega

private theorem carry_le_pred : ∀ s n : Nat, s + 1 ≤ n → s ≤ n - 1 := by
  intro s n h; omega

/-- A root that resolves at an honest reader's strict read resolves to a
retained body, hence to a run block. This is the converse of
`NamedHealthyHeadReady.held_find_at_strict`, and it is what lets the
post-boundary premise, which speaks of run blocks, be applied to the reader's
own lookup. -/
private theorem carry_find_body_at_strict (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (reader : V) (hreader : reader ∈ rho.honest)
    (t : Time) {key : BlockId} {Hb : Block V}
    (hfind : Block.find? (NamedRun.stateBeforeTime S rho t reader).st.core.T key = some Hb) :
    ∃ H : NamedBlock V, NamedRun.blockInRun S rho H ∧ H.erase = Hb ∧ H.root = key := by
  obtain ⟨m, hread, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho sch.sorted t
  rw [hread] at hfind
  have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho m reader).1.1.1
  have hmem : Hb ∈ (NamedRun.stateBefore S rho m reader).st.core.T :=
    Proofs.HealingLemmas.find?_mem hfind
  rw [hcoh.1] at hmem
  obtain ⟨H, hH, hHe⟩ := Finset.mem_image.mp hmem
  refine ⟨H, Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hreader m hH), hHe, ?_⟩
  rw [← Proofs.NamedWire.erase_root H, hHe]
  exact Proofs.HealingLemmas.find?_root hfind

/-- Every body-ready input of an honest sender in round `r`'s window covers the
protected prefix at an honest reader's round-`r` G2 store. The sender's row is
either a pre-boundary emission (`hconf`) or a post-boundary emission of a round
below `r` (`hpost`), and the reader's own resolution of the confirmed root
comes from `bodyReady` itself, so `HonestHeadHeldAbove` is not consulted. This
is the `hfirst`-free replacement for `Inclusions.rawInputs_localCovers`. -/
theorem carry_interpreted_localCovers (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (auth : NamedUnforgeable S rho)
    (b0 : Time) (s r : Round) (Pn : NamedBlock V)
    (hconf : HonestConfirmedAtOrAbove S rho b0 s Pn.erase)
    (hpost : ∀ (a : NamedAttestation V) (t : Time), a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (.attest a) t → b0 ≤ t → a.round < r →
      ∀ key, a.confirmed = some key →
        ∀ K : NamedBlock V, NamedRun.blockInRun S rho K → K.root = key →
          Block.Preceq Pn.erase K.erase)
    (w : V) (hw : w ∈ rho.honest) (u : V) (hu : u ∈ rho.honest) (cutoff : Time)
    {z : Protocol.SGVote V}
    (hz : z ∈ DecoupledConsensusModel.Protocol.interpretedInputs
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.F
      S.hc.η_SG r cutoff u)
    (hzs : s ≤ z.round) :
    localCovers
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
      z.confirmed Pn.erase = true := by
  obtain ⟨hzraw, hready⟩ := Finset.mem_filter.mp hz
  obtain ⟨b, hbval, hbround, hbproj, hbwin, _hblt, hbem⟩ :=
    rawInputs_trace S rho sch auth (domain S.E S.hc r .g2) cutoff w S.hc.η_SG r u hu hzraw
  have hzr : z.round < r := (window_bounds hbwin).2
  have hbr : b.round < r := by rw [hbround]; exact hzr
  have hbs : s ≤ b.round := by rw [hbround]; exact hzs
  obtain ⟨_, _, _, K, _, hkey⟩ := Proofs.NamedOutageInputs.emitted_attestation_head S rho hbem
  have hzconf : z.confirmed = some K.root := by rw [← hbproj, sgVote_confirmed, hkey]
  have hfindsome : ∃ Hb : Block V,
      Block.find? (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.T K.root
        = some Hb := by
    cases hf : Block.find?
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.T K.root with
    | some Hb => exact ⟨Hb, rfl⟩
    | none =>
      exfalso
      have hfalse : DecoupledConsensusModel.Protocol.bodyReady
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.F cutoff z
            = false := by
        simp only [DecoupledConsensusModel.Protocol.bodyReady, Protocol.HealingStore.gradeView,
          Protocol.Store.toHealing, hzconf, hf]
      rw [hfalse] at hready
      exact absurd hready (by simp)
  obtain ⟨Hb, hfind⟩ := hfindsome
  obtain ⟨H, hHrun, hHe, hHroot⟩ :=
    carry_find_body_at_strict S rho sch w hw (domain S.E S.hc r .g2) hfind
  have hcover : Block.Preceq Pn.erase H.erase := by
    by_cases hlt : S.a b.round < b0
    · exact hconf b (S.a b.round) (hbval ▸ hu) (hbval ▸ hbem) hlt hbs K.root hkey H hHrun
        hHroot
    · exact hpost b (S.a b.round) (hbval ▸ hu) (hbval ▸ hbem) (not_lt.mp hlt) hbr
        K.root hkey H hHrun hHroot
  change Protocol.head_covers
    (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.T Pn.erase z.confirmed
      = true
  rw [hzconf]
  show (match Block.find?
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.T K.root with
    | some head => Block.preceq Pn.erase head
    | none => false) = true
  rw [hfind, ← hHe]
  exact hcover

/-- `Inclusions.voters_subset_supporters` with `hfirst` replaced by `hpost`.
Only clause 4 changes: a row in round `r`'s window need not be a
pre-outage emission, and the two coverage calls go through
`carry_interpreted_localCovers` instead. -/
theorem carry_voters_subset_supporters (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (auth : NamedUnforgeable S rho)
    (roots : NamedRootCollisionFree S rho) (hR : 3 ≤ S.hc.R)
    (b0 b1 : Time) (s sr r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho) (hPn : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hentry : IntrinsicHighEntryHistory S rho Pn r)
    (hcutr : b0 ≤ domain S.E S.hc r .g1 + 1)
    (hconf : HonestConfirmedAtOrAbove S rho b0 s Pn.erase)
    (hhead : HonestHeadHeldAbove S rho b0 s Pn.erase)
    (harr : HealthySGArrival S rho b0)
    (hpost : ∀ (a : NamedAttestation V) (t : Time), a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (.attest a) t → b0 ≤ t → a.round < r →
      ∀ key, a.confirmed = some key →
        ∀ K : NamedBlock V, NamedRun.blockInRun S rho K → K.root = key →
          Block.Preceq Pn.erase K.erase)
    (hlo : s + 1 ≤ sr) (hopen : opening S.E S.hc sr ≤ b0)
    (hbr : b0 ≤ S.a r)
    (hwindow : sr - 1 ∈ Protocol.latest_window S.hc.η_SG r) :
    honestRoundVoters S rho (sr - 1) ⊆ commonSupporters S rho b0 Pn sr r := by
  intro u hu
  have huh : u ∈ rho.honest := (Finset.mem_filter.mp hu).1
  refine Finset.mem_filter.mpr ⟨huh, ?_⟩
  intro w hw hneeds
  have hgridb0 : OnDeltaGrid S b0 := onDeltaGrid_of_public S b0 hexec.boundaryPublic
  have hFPb0 : Block.Preceq (NamedRun.stateBeforeTime S rho b0 w).st.core.F Pn.erase :=
    finalized_le_before_boundary S rho b0 b1 s r Pn hexec hmargin hsleep hPn hno w hw hneeds
      b0 le_rfl hcutr
  have hFPdom : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.F Pn.erase :=
    finalized_le_at_g2_domain S rho b0 b1 s r Pn hexec hmargin hsleep hentry w hw hneeds
  have hqmem : sr - 1 ∈ Internal.OutageEntryRevision.retainedRounds S sr :=
    mem_retainedRounds S (carry_sub_eta_le_pred sr S.hc.η_SG S.hc.η_SG_ge_one) (Nat.sub_le sr 1)
  have hopen' : opening S.E S.hc (sr - 1 + 1) ≤ b0 := by
    rw [carry_pred_succ s sr hlo]; exact hopen
  have hspred : s ≤ sr - 1 := carry_le_pred s sr hlo
  have hsrlt : sr - 1 < r := (window_bounds hwindow).2
  obtain ⟨a, hval, haround, hem, hdead, hraw⟩ :=
    retained_mem_of_vote S rho sch harr hR sr (sr - 1) u hu hqmem hopen' w hw
  have hsa : s ≤ a.round := by rw [haround]; exact hspred
  have hready : Protocol.sgVote a.erase ∈
      Internal.OutageEntryRevision.retainedReady S
        (NamedRun.stateBeforeTime S rho b0 w).st.core sr b0 u :=
    Finset.mem_filter.mpr ⟨hraw,
      retained_bodyReady S rho sch roots b0 s Pn.erase hhead w hw u huh hval hsa hdead hem
        b0 b0 hdead hFPb0 hdead⟩
  refine ⟨latest_nonempty ⟨_, hready⟩, ?_, ?_, ?_⟩
  · intro y hy
    have hyraw : y ∈ Internal.OutageEntryRevision.retainedRaw S
        (NamedRun.stateBeforeTime S rho b0 w).st.core sr b0 u :=
      (Finset.mem_filter.mp (latest_mem hy).1).1
    have hyge : a.round ≤ y.round := (latest_mem hy).2 _ hready
    have hys : s ≤ y.round := le_trans hsa hyge
    refine ⟨retained_covers S rho sch auth roots b0 hgridb0 s Pn.erase hconf hhead w hw u huh
      hFPb0 sr hyraw hys, ?_⟩
    obtain ⟨c, _, hcround, _, _, hclt, _⟩ := retained_trace S rho sch auth b0 w sr u huh hyraw
    have hylt : y.round < r := by
      by_contra hcon
      have hstep : S.a r ≤ S.a c.round :=
        Assembly.a_mono S (by rw [hcround]; exact Nat.le_of_not_lt hcon)
      exact absurd (lt_of_le_of_lt hstep hclt) (not_lt.mpr hbr)
    exact mem_latest_window (le_trans (window_bounds hwindow).1 (haround ▸ hyge)) hylt
  · refine staleAt_false_of_rounds_ge S rho sch auth roots b0 hgridb0 s Pn.erase hconf hhead w hw
      u huh hFPb0 sr ?_
    intro z hz
    exact le_trans hsa ((latest_mem hz).2 _ hraw)
  · obtain ⟨c, hcval, hcround, hcem, hcdead, hcraw⟩ :=
      rawInputs_mem_of_vote S rho sch harr hR (sr - 1) r u hu hwindow hsrlt hopen' w hw
    have hcs : s ≤ c.round := by rw [hcround]; exact hspred
    have hcrlt : c.round < r := by rw [hcround]; exact hsrlt
    have hcready := retained_bodyReady S rho sch roots b0 s Pn.erase hhead w hw u huh hcval hcs
      hcdead hcem (domain S.E S.hc r .g2) (early S.E S.hc r .g2)
      ((action_delta_le_early S hR hcrlt).trans (early_le_domain S r)) hFPdom
      (action_delta_le_early S hR hcrlt)
    have hcinterp : Protocol.sgVote c.erase ∈ DecoupledConsensusModel.Protocol.interpretedInputs
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.F
        S.hc.η_SG r (early S.E S.hc r .g2) u :=
      Finset.mem_filter.mpr ⟨hcraw, hcready⟩
    obtain ⟨y, hy, hymax⟩ := Finset.exists_max_image
      (DecoupledConsensusModel.Protocol.interpretedInputs
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.F
        S.hc.η_SG r (early S.E S.hc r .g2) u)
      (fun z : Protocol.SGVote V => z.round) ⟨_, hcinterp⟩
    have hys : s ≤ y.round := le_trans hcs (hymax _ hcinterp)
    refine decide_eq_true ⟨DecoupledConsensusModel.Protocol.token y, Finset.mem_image_of_mem _ hy,
      ?_, ?_, ?_, ?_⟩
    · intro z hz
      obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hz
      exact hymax _ hz'
    · exact carry_interpreted_localCovers S rho sch auth b0 s r Pn hconf hpost w hw
        u huh (early S.E S.hc r .g2) hy hys
    · intro tx htx ty hty _ hround
      obtain ⟨x', hx', rfl⟩ := Finset.mem_image.mp htx
      obtain ⟨y', hy', rfl⟩ := Finset.mem_image.mp hty
      obtain ⟨p, _, hpround, hpproj, _, _, hpem⟩ :=
        rawInputs_trace S rho sch auth (domain S.E S.hc r .g2) (late S.E S.hc r .g2) w
          S.hc.η_SG r u huh hx'
      obtain ⟨q, _, hqround, hqproj, _, _, hqem⟩ :=
        rawInputs_trace S rho sch auth (domain S.E S.hc r .g2) (late S.E S.hc r .g2) w
          S.hc.η_SG r u huh hy'
      have hpq : p = q := NamedOutageProvenance.emitted_same_round_unique S rho sch hpem hqem
        (by rw [hpround, hqround]; exact hround)
      show x'.confirmed = y'.confirmed
      rw [← hpproj, ← hqproj, hpq]
    · intro tz htz hltz
      obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp htz
      exact carry_interpreted_localCovers S rho sch auth b0 s r Pn hconf hpost w hw
        u huh (late S.E S.hc r .g2) hz' (le_of_lt (lt_of_le_of_lt hys hltz))


/-- **Theorem B — the support carry.** The `common_support` field of
`RoundInvariant` at `r + 1`.

The witnesses are `b0` and the honest clock round at `b0`, the same pair the
base certificate uses, NOT the witnesses `hinv.common_support` supplies; see the
section header for why the invariant's own certificate does not carry. The
proof is `CommonSupportBase.common_support_base` at `r + 1` with `hfirst`
replaced by `hpost`. -/
theorem common_support_step_of_early
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V) (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hentry : IntrinsicHighEntryHistory S rho Pn (r + 1))
    (hbudget : StableRetentionBudget S rho v s Pn.erase b1)
    (hconf : HonestConfirmedAtOrAbove S rho b0 s Pn.erase)
    (hhead : HonestHeadHeldAbove S rho b0 s Pn.erase)
    (harr : HealthySGArrival S rho b0)
    (hinv : RoundInvariant S rho b0 Pn r) (hnext : DomainIncluded S rho b0 (r + 1))
    (hearlyCap : early S.E S.hc (r + 1) .g2 < b1 + S.E.Δ)
    (hpost : ∀ (a : NamedAttestation V) (t : Time), a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (.attest a) t → b0 ≤ t → a.round < r + 1 →
      ∀ key, a.confirmed = some key →
        ∀ K : NamedBlock V, NamedRun.blockInRun S rho K → K.root = key →
          Block.Preceq Pn.erase K.erase) :
    ∃ supportBoundary : Time, ∃ supportRound : Round,
      supportBoundary = min b0 (early S.E S.hc (r + 1) .g2) ∧ supportRound ≤ r + 1 ∧
      (∀ w ∈ rho.honest,
        S.hc.round_of (NamedRun.stateBeforeTime S rho supportBoundary w).st.core.s =
          supportRound) ∧
      S.E.electorate.weightOf ((Finset.univ \ rho.honest) ∪
          commonStaleRisks S rho supportBoundary Pn supportRound (r + 1)) <
        S.E.electorate.weightOf
          (commonSupporters S rho supportBoundary Pn supportRound (r + 1)) := by
  have sch : NamedScheduleWellFormed S rho := hexec.core.toNamedScheduleWellFormed
  have auth : NamedUnforgeable S rho := hexec.core.toNamedUnforgeable
  have roots : NamedRootCollisionFree S rho := hexec.core.toNamedRootCollisionFree
  have hR : 3 ≤ S.hc.R := S.hc.R_ge_three
  have hb0 : 0 ≤ b0 := hexec.interval.1
  have hhor : b0 ≤ rho.horizon := hexec.interval.2.1.trans hexec.interval.2.2
  -- WEAKENED PREMISE (addendum 34 rulings 12/14). `hnext` is `DomainIncluded`:
  -- the lower bound is at the action as before, but no horizon bound is
  -- available at any action time, only at the round opening.
  have hnexta : b0 ≤ S.a (r + 1) := hnext.2.1
  set rho0 : Round := boundaryRound S rho b0 v with hrho0
  have hlo : s + 1 ≤ rho0 := succ_le_boundaryRound S rho sch b0 hhor v hv s hmargin
  have hhi : rho0 ≤ r + 1 := boundaryRound_le S rho sch b0 hb0 v (r + 1) hnexta
  have hpos : 0 < rho0 := lt_of_lt_of_le (Nat.succ_pos s) hlo
  have hopen : opening S.E S.hc rho0 ≤ b0 := opening_le_boundary S rho sch b0 hb0 v
  have hcovered : RoundCovered S rho rho0 :=
    Or.inr ⟨.g1, by rw [base_domain_g1_eq_opening]; exact base_opening_nonneg S rho0,
      by rw [base_domain_g1_eq_opening]
         exact hopen.trans hhor⟩
  have hmaj : GradeFormingMajority S rho rho0 := hforming rho0 hpos hcovered
  have hretention : b1 + S.E.Δ ≤
      early S.E S.hc (s + S.hc.η_SG + 1) .g2 := hbudget.1
  have hwindow : rho0 - 1 ∈ Protocol.latest_window S.hc.η_SG (r + 1) :=
    predecessor_round_in_window_early S
      (hearlyCap.trans_le hretention) (k := s) (le_refl s) hlo hhi
  have hminb : b0 = min b0 (early S.E S.hc (r + 1) .g2) :=
    (min_eq_left (hinv.included.2.1.trans (carry_a_le_early_succ S r hR))).symm
  
  -- which is where `NeedsSG` is tested.
  have hcutr : b0 ≤ domain S.E S.hc (r + 1) .g1 + 1 :=
    (((hinv.included.2.1.trans (carry_a_le_early_succ S r hR)).trans
      (early_le_domain S (r + 1))).trans (incl_g2_le_opening_cut S (r + 1)))
  refine ⟨b0, rho0, hminb, hhi, boundaryRound_uniform S rho sch b0 v hv, ?_⟩
  have hleft : S.E.electorate.weightOf ((Finset.univ \ rho.honest) ∪
      commonStaleRisks S rho b0 Pn rho0 (r + 1)) ≤
      S.E.electorate.weightOf ((Finset.univ \ rho.honest) ∪ staleHistoricalVoters S rho rho0) :=
    S.E.electorate.weightOf_mono
      (Finset.union_subset_union_right
        (stale_risks_subset S rho sch auth roots hR b0 b1 s rho0 (r + 1) Pn hexec hmargin
          hsleep hinv.prefix_scope hno hcutr hconf hhead harr hlo hopen))
  have hright : S.E.electorate.weightOf (honestRoundVoters S rho (rho0 - 1)) ≤
      S.E.electorate.weightOf (commonSupporters S rho b0 Pn rho0 (r + 1)) :=
    S.E.electorate.weightOf_mono
      (carry_voters_subset_supporters S rho sch auth roots hR b0 b1 s rho0 (r + 1) Pn hexec
        hmargin hsleep hinv.prefix_scope hno hentry hcutr hconf hhead harr hpost hlo hopen
        hnexta hwindow)
  exact lt_of_le_of_lt hleft (lt_of_lt_of_le hmaj hright)

/-- The original domain-bounded form of `common_support_step_of_early`. -/
theorem common_support_step
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hentry : IntrinsicHighEntryHistory S rho Pn (r + 1))
    (hbudget : StableRetentionBudget S rho v s Pn.erase b1)
    (hconf : HonestConfirmedAtOrAbove S rho b0 s Pn.erase)
    (hhead : HonestHeadHeldAbove S rho b0 s Pn.erase)
    (harr : HealthySGArrival S rho b0)
    (hinv : RoundInvariant S rho b0 Pn r)
    (hnext : DomainIncluded S rho b0 (r + 1))
    (hrb1 : domain S.E S.hc (r + 1) .g2 ≤ b1 + S.E.Δ)
    (hpost : ∀ (a : NamedAttestation V) (t : Time),
      a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (.attest a) t →
      b0 ≤ t → a.round < r + 1 → ∀ key, a.confirmed = some key →
      ∀ K : NamedBlock V, NamedRun.blockInRun S rho K → K.root = key →
      Block.Preceq Pn.erase K.erase) :
    ∃ supportBoundary : Time, ∃ supportRound : Round,
      supportBoundary = min b0 (early S.E S.hc (r + 1) .g2) ∧
      supportRound ≤ r + 1 ∧
      (∀ w ∈ rho.honest,
        S.hc.round_of
          (NamedRun.stateBeforeTime S rho supportBoundary w).st.core.s =
            supportRound) ∧
      S.E.electorate.weightOf ((Finset.univ \ rho.honest) ∪
          commonStaleRisks S rho supportBoundary Pn supportRound (r + 1)) <
        S.E.electorate.weightOf
          (commonSupporters S rho supportBoundary Pn supportRound (r + 1)) := by
  have hearlyDomain : early S.E S.hc (r + 1) .g2 <
      domain S.E S.hc (r + 1) .g2 := by
    unfold early domain
    simp only [Phase.earlyOffset, Phase.domainOffset]
    nlinarith [S.E.Δ_pos]
  exact common_support_step_of_early S rho b0 b1 v s r Pn hexec
    hforming hv hmargin hsleep hno hentry hbudget hconf hhead harr hinv
    hnext (hearlyDomain.trans_le hrb1) hpost

#print axioms carry_interpreted_localCovers
#print axioms carry_voters_subset_supporters
#print axioms common_support_step_of_early
#print axioms common_support_step

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
