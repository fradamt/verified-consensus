module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ViabilityFromBand

@[expose] public section

/-!
# Mutual carrier and entry-history induction

 removes the circular all-round K6 premise. The invariant at round `r`
contains the honest carrier floor at `r` and the intrinsic entry history through
round `r + 1`. The history supplies `JointAt` for the next round. The next SG
clause then supplies the next carrier floor, which extends the history again.
-/


namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedJointOutage
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem mutual_phase_domain_nonneg (S : Setup V) {r : Round}
    (hr : 0 < r) {p : Phase} (hp : p = .g1 ∨ p = .g2) :
    (0 : Time) ≤ domain S.E S.hc r p := by
  rcases hp with rfl | rfl
  · rw [base_domain_g1_eq_opening]
    exact base_opening_nonneg S r
  · have hnat : (2 : Nat) ≤ r * S.hc.R := by
      have hmul : (1 : Nat) * S.hc.R ≤ r * S.hc.R :=
        Nat.mul_le_mul_right S.hc.R hr
      rw [one_mul] at hmul
      exact S.hc.R_ge_two.trans hmul
    have hcast : (2 : Time) ≤ ((r * S.hc.R : Nat) : Time) := by
      exact_mod_cast hnat
    unfold domain opening Protocol.proposal_time Env.t
      Protocol.HealConfig.opening_slot slotStart
    simp only [Phase.domainOffset]
    push_cast
    nlinarith [S.E.Δ_pos]

set_option linter.unusedVariables false in

/-- 's conjunctive round invariant. -/
def OutageInvariantAt (S : Setup V) (rho : NamedRun V) (Pn : NamedBlock V)
    (b0 : Time) (s r : Round) : Prop :=
  HonestCarriersAbove S rho Pn.erase r ∧
    IntrinsicHighEntryHistory S rho Pn (r + 1)


/-- Stable output at the next G2 domain, which is the only point consumed by
the next carrier step. -/
def OutageStableAtNextG2 (S : Setup V) (rho : NamedRun V)
    (P : Block V) (r : Round) : Prop :=
  ∀ w ∈ rho.honest, Block.Preceq P
    (Protocol.get_stable (NamedRun.stateBeforeTime S rho
      (domain S.E S.hc (r + 1) .g2) w).st.core)


/-- The opening SG clause stored beside the  invariant while the horizon
still reaches the round. -/
def OutageSGClauseAt (S : Setup V) (rho : NamedRun V)
    (P : Block V) (r : Round) : Prop :=
  ∀ w ∈ rho.honest,
    let n := NamedRun.readAt S rho (domain S.E S.hc r .g1) w
    Block.Preceq P n.st.core.F ∨
      ∃ raw : Block V,
        (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g2 =
          some (some raw) ∧ Block.Preceq P raw


/-- The auxiliary state serves to prove the public two-field  invariant. -/
def OutageMutualStateAt (S : Setup V) (rho : NamedRun V)
    (Pn : NamedBlock V) (b0 : Time) (s r : Round) : Prop :=
  OutageInvariantAt S rho Pn b0 s r ∧
    OutageStableAtNextG2 S rho Pn.erase r ∧
    OutageSGClauseAt S rho Pn.erase r

/-- Exact read-level viability from the history whose upper round is the read's
own round. This is the tight form needed by the mutual induction. -/
private theorem mutual_relativeG2_viability
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round)
    (Pn : NamedBlock V) (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hentry : IntrinsicHighEntryHistory S rho Pn r)
    (hheld0 : ∀ w ∈ rho.honest,
      Pn ∈ (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (hb0 : b0 ≤ domain S.E S.hc r .g2) :
    ∀ w ∈ rho.honest,
      Block.Preceq Pn.erase
          (Protocol.get_fg_root
            (Proofs.HealingSurface.relativeG2Read S rho r w).st.core.toHealing.toFG) ∨
        Pn.erase ∈ Internal.PhaseGrades.filteredTree
          (Proofs.HealingSurface.relativeG2Read S rho r w) := by
  intro w hw
  have h := fgRootAbove_or_filtered_at_stateBeforeTime_of_entry
    S rho b0 b1 s r Pn hexec hslash hmargin hsleep hscope hno hentry
      hheld0 w hw (domain S.E S.hc r .g2) hb0
      (FrameForward.domain_le_a S r .g2)
  simpa only [Proofs.HealingSurface.relativeG2Read,
    Internal.PhaseGrades.filteredTree] using h

/-- Exact confirmation-read compatibility before the action of the history's
upper round. -/
private theorem mutual_fg_compatibility
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round)
    (Pn : NamedBlock V) (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hentry : IntrinsicHighEntryHistory S rho Pn r)
    (hheld0 : ∀ w ∈ rho.honest,
      Pn ∈ (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (w : V) (hw : w ∈ rho.honest) (u : Time)
    (hb0 : b0 ≤ u) (hu : u < S.a r) :
    Block.compatible Pn.erase
      (Protocol.get_fg_root
        (NamedActionReads.confirmationReadAt S rho w u).st.core.toHealing.toFG) = true := by
  have h := fg_compatible_at_read_of_entry S rho b0 b1 s r Pn hexec
    hslash hmargin hsleep hscope hno hentry hheld0 w hw u hb0 hu
  simpa only [NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using h

/-- A G2-domain interval straddles the bounded outage cap. -/
theorem outageCap_g2_straddle_exists
    (S : Setup V) (b0 b1 : Time) (s : Round)
    (hb0b1 : b0 ≤ b1) (hmargin : FormationMargin S s b0) :
    ∃ r : Round, 0 < r ∧
      domain S.E S.hc r .g2 ≤ b1 + S.E.Δ ∧
      b1 + S.E.Δ < domain S.E S.hc (r + 1) .g2 := by
  let cap := b1 + S.E.Δ
  let t := cap + S.E.Δ
  let r := clockRoundAt S t
  have hb00 : (0 : Time) ≤ b0 := by
    have h6 : (0 : Time) ≤ 6 * S.E.Δ := by nlinarith [S.E.Δ_pos]
    exact h6.trans (six_delta_lt_b0 S s b0 hmargin).le
  have ht0 : (0 : Time) ≤ t := by
    dsimp only [t, cap]
    nlinarith [S.E.Δ_pos, hb00, hb0b1]
  have hopen : opening S.E S.hc r ≤ t := opening_le_clockRound S t ht0
  have hnext : t < opening S.E S.hc (r + 1) :=
    clockRound_lt_opening_succ S t
  have hopen1 : opening S.E S.hc 1 ≤ t := by
    calc
      opening S.E S.hc 1 ≤ opening S.E S.hc (s + 1) :=
        base_opening_mono S (Nat.succ_le_succ (Nat.zero_le s))
      _ ≤ S.a (s + 1) := incl_opening_le_a S (s + 1)
      _ ≤ S.a (s + 1) + S.E.Δ :=
        Int.le_add_of_nonneg_right S.E.Δ_pos.le
      _ ≤ b0 := hmargin
      _ ≤ b1 := hb0b1
      _ ≤ t := by
        dsimp only [t, cap]
        nlinarith [S.E.Δ_pos]
  have hr : 0 < r := by
    exact succ_le_clockRound_of_opening S 1 t hopen1
  have hdom : domain S.E S.hc r .g2 ≤ cap := by
    have heq : domain S.E S.hc r .g2 =
        opening S.E S.hc r + (-1) * S.E.Δ := rfl
    rw [heq]
    dsimp only [t] at hopen
    nlinarith
  have hcap : cap < domain S.E S.hc (r + 1) .g2 := by
    have heq : domain S.E S.hc (r + 1) .g2 =
        opening S.E S.hc (r + 1) + (-1) * S.E.Δ := rfl
    rw [heq]
    dsimp only [t] at hnext
    nlinarith
  exact ⟨r, hr, by simpa only [cap] using hdom,
    by simpa only [cap] using hcap⟩


/-- Extend an intrinsic history by the entries named in one carrier-floored
round. -/
theorem entry_history_succ_of_carrierAbove
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (r : Round)
    (Pn : NamedBlock V) (hexec : OutageExecution S rho b0 b1)
    (hscope : NamedRun.blockInRun S rho Pn) (hr : 0 < r)
    (hentry : IntrinsicHighEntryHistory S rho Pn r)
    (hcarriers : HonestCarriersAbove S rho Pn.erase r) :
    IntrinsicHighEntryHistory S rho Pn (r + 1) := by
  intro h entry he
  obtain ⟨i, a, source, ha, har, hs, hheight⟩ := he
  rcases Nat.lt_succ_iff_lt_or_eq.mp har with hlt | heq
  · exact hentry h entry ⟨i, a, source, ha, hlt, hs, hheight⟩
  · exact entry_compatible_of_carrierAbove S rho b0 b1 r Pn hexec
      hscope hr hcarriers ha heq hs


/--  seed: a carrier-floored seed round and the history entering that round
produce the conjunctive invariant. -/
theorem outageInvariant_seed
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r0 : Round)
    (Pn : NamedBlock V) (hexec : OutageExecution S rho b0 b1)
    (hscope : NamedRun.blockInRun S rho Pn) (hr0 : 0 < r0)
    (hcarriers : HonestCarriersAbove S rho Pn.erase r0)
    (hentry : IntrinsicHighEntryHistory S rho Pn r0) :
    OutageInvariantAt S rho Pn b0 s r0 := by
  exact ⟨hcarriers, entry_history_succ_of_carrierAbove S rho b0 b1 r0
    Pn hexec hscope hr0 hentry hcarriers⟩


/-- Seed at the G2-domain interval that straddles `b1 + Δ`. Only the next
domain value is needed by the mutual induction, so the current domain may lie
before `b0`. -/
theorem outageMutualState_seed_at_cap_of_clauses
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r0 : Round)
    (Pn : NamedBlock V) (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hheld0 : ∀ w ∈ rho.honest,
      Pn ∈ (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (hscope : NamedRun.blockInRun S rho Pn) (hr0 : 0 < r0)
    (hentry : IntrinsicHighEntryHistory S rho Pn r0)
    (hcarriers : HonestCarriersAbove S rho Pn.erase r0)
    (hsg : OutageSGClauseAt S rho Pn.erase r0)
    (hout : StableUserOutputs S rho b0 b1 Pn.erase)
    (hdomCap : domain S.E S.hc r0 .g2 ≤ b1 + S.E.Δ)
    (hcapNext : b1 + S.E.Δ < domain S.E S.hc (r0 + 1) .g2)
    (hhor : domain S.E S.hc (r0 + 1) .g2 ≤ rho.horizon) :
    OutageMutualStateAt S rho Pn b0 s r0 := by
  have hmutual := outageInvariant_seed S rho b0 b1 s r0 Pn hexec
    hscope hr0 hcarriers hentry
  have hb0cap : b0 ≤ b1 + S.E.Δ :=
    hexec.interval.2.1.trans (Int.le_add_of_nonneg_right S.E.Δ_pos.le)
  have hb0next : b0 ≤ domain S.E S.hc (r0 + 1) .g2 :=
    hb0cap.trans hcapNext.le
  have hK6next := mutual_relativeG2_viability S rho b0 b1 s (r0 + 1)
    Pn hexec hslash hmargin hsleep hscope hno hmutual.2 hheld0
    hb0next
  have hstableNext : OutageStableAtNextG2 S rho Pn.erase r0 := by
    intro w hw
    let start := b1 + S.E.Δ + 1
    let stop := domain S.E S.hc (r0 + 1) .g2
    let i := (rho.events.filter (fun e => decide (e.time < start))).length
    let j := (rho.events.filter (fun e => decide (e.time < stop))).length
    have hstartStop : start ≤ stop := by
      dsimp only [start, stop]
      exact Int.add_one_le_iff.mpr hcapNext
    have hi : NamedRun.stateBeforeTime S rho start w =
        NamedRun.stateBefore S rho i w :=
      congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S
        hexec.core.toNamedScheduleWellFormed start) w
    have hj : NamedRun.stateBeforeTime S rho stop w =
        NamedRun.stateBefore S rho j w :=
      congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S
        hexec.core.toNamedScheduleWellFormed stop) w
    have hij : i ≤ j := by
      dsimp only [i, j]
      exact strict_lengths_mono rho hstartStop
    have hcapHor : b1 + S.E.Δ ≤ rho.horizon := hcapNext.le.trans hhor
    have hhold : Block.Preceq Pn.erase
        (Protocol.get_stable
          (NamedRun.stateBeforeTime S rho start w).st.core) := by
      have hs := (hout w hw (b1 + S.E.Δ) hb0cap le_rfl hcapHor).1
      have hread : NamedRun.readAt S rho (b1 + S.E.Δ) w =
          NamedRun.stateBeforeTime S rho start w := by
        dsimp only [start]
        rw [readAt_eq_succ]
      rwa [hread] at hs
    have hcases := stateBefore_stable_covered_of_comparable S rho w i j hij
      (by
        rw [← hi]
        unfold Protocol.get_stable at hhold
        split at hhold
        · exact Or.inr hhold
        · exact Or.inl hhold)
      (fun k u hik hkj he hpos hcut G hG _ => by
        have huStart : start ≤ u := Proofs.Optimistic.le_time_of_index_ge S
          hexec.core.toNamedScheduleWellFormed (t := start) (j := k) hik he
        have huStop : u < stop := by
          have hins := Proofs.Optimistic.filter_true_of_index_lt S
            hexec.core.toNamedScheduleWellFormed (fun e => decide (e.time < stop))
            (Proofs.Optimistic.downward_lt stop) hkj he
          simpa only [decide_eq_true_eq, NamedEvent.time] using hins
        have hcapStart : b1 + S.E.Δ ≤ start := by
          dsimp only [start]
          exact Int.le_add_of_nonneg_right (by norm_num)
        have hb0u : b0 ≤ u := hb0cap.trans (hcapStart.trans huStart)
        have huStop' : u < domain S.E S.hc (r0 + 1) .g2 := by
          simpa only [stop] using huStop
        have huAction : u < S.a (r0 + 1) :=
          huStop'.trans (q10_domain_lt_a S (r0 + 1) .g2)
        have hfg := mutual_fg_compatibility S rho b0 b1 s (r0 + 1)
          Pn hexec hslash hmargin hsleep hscope hno hmutual.2
            hheld0 w hw u hb0u huAction
        have hbefore := Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S
          hexec.core.toNamedScheduleWellFormed he
        change NamedRun.stateBefore S rho k w =
          NamedRun.stateBeforeTime S rho u w at hbefore
        have hread : NamedActionReads.confirmationReadFrom S
            (NamedRun.stateBefore S rho k w) u =
            NamedActionReads.confirmationReadAt S rho w u := by
          rw [hbefore]
          rfl
        have hG' : dutyStableRoot S
            (NamedActionReads.confirmationReadAt S rho w u) = some G := by
          rw [← hread]
          exact hG
        exact confirmationDutyRoot_comparable_of_sg_clause S rho b0 b1
          Pn r0 hexec hr0 hsg w hw u
            (hdomCap.trans (hcapStart.trans huStart)) huStop'
            hcut (hK6next w hw) hfg hG')
    have hcompat : Block.compatible Pn.erase
        (NamedRun.stateBeforeTime S rho stop w).st.core.F = true := by
      rcases hK6next w hw with hroot | htree
      · have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
          S rho stop w
        have hFroot := Proofs.Records.preceq_get_fg_root_of_F
          (st := (NamedRun.stateBeforeTime S rho stop w).st.core.toHealing.toFG)
          (by simpa only [Protocol.Store.toHealing] using hFJ)
        have hroot' : Block.Preceq Pn.erase
            (Protocol.get_fg_root
              (NamedRun.stateBeforeTime S rho stop w).st.core.toHealing.toFG) := by
          simpa only [stop, Proofs.HealingSurface.relativeG2Read,
            Internal.PhaseGrades.filteredTree] using hroot
        exact Block.compatible_of_preceq_common hroot' hFroot
      · have hFleP := q10_filtered_F (by
            simpa only [stop, Proofs.HealingSurface.relativeG2Read,
              Internal.PhaseGrades.filteredTree] using htree)
        simp only [Block.compatible, Bool.or_eq_true]
        exact Or.inr hFleP
    rw [hj]
    rw [hj] at hcompat
    rcases hcases with hF | hstable
    · have hFstable : Block.Preceq
          (NamedRun.stateBefore S rho j w).st.core.F
          (Protocol.get_stable (NamedRun.stateBefore S rho j w).st.core) := by
        unfold Protocol.get_stable
        split
        · assumption
        · exact Block.preceq_self _
      exact Block.preceq_trans hF hFstable
    · exact preceq_get_stable_of_cases _ (Or.inr hstable) hcompat
  exact ⟨hmutual, hstableNext, hsg⟩



/-- The next opening SG clause derived from one  invariant and the stable
floor at the next G2 domain. Viability is requested only at that opening read;
there is no all-round K6 premise. -/
theorem opening_sg_clause_of_outageInvariant
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round)
    (Pn : NamedBlock V) (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hheld0 : ∀ w ∈ rho.honest,
      Pn ∈ (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (hinv : OutageInvariantAt S rho Pn b0 s r)
    (hgst : S.E.t_GST ≤ S.a r)
    (hstableG2 : ∀ w ∈ rho.honest, Block.Preceq Pn.erase
      (Protocol.get_stable (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st.core))
    (hb0open : b0 ≤ domain S.E S.hc (r + 1) .g1)
    (hopenHor : domain S.E S.hc (r + 1) .g1 ≤ rho.horizon) :
    ∀ w ∈ rho.honest,
      let n := NamedRun.readAt S rho (domain S.E S.hc (r + 1) .g1) w
      Block.Preceq Pn.erase n.st.core.F ∨
        ∃ raw : Block V,
          (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing
            (r + 1)).g2 = some (some raw) ∧ Block.Preceq Pn.erase raw := by
  have hg2hor : domain S.E S.hc (r + 1) .g2 ≤ rho.horizon :=
    (q10_domain_g2_lt_domain_g1 S (r + 1)).le.trans hopenHor
  have hcovered : RoundCovered S rho (r + 1) :=
    Or.inr ⟨.g1, mutual_phase_domain_nonneg S (Nat.succ_pos r) (Or.inl rfl), hopenHor⟩
  have hmajority : GradeFormingMajority S rho (r + 1) :=
    hforming (r + 1) (Nat.succ_pos r) hcovered
  have hG2 : ∀ w ∈ rho.honest, Block.Preceq Pn.erase
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (r + 1) .g2) w).st.core.F ∨
      ∃ raw, DecoupledConsensusModel.Protocol.freezeRoot S.E
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) .g2) w).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) .g2) w).st.core.F
          S.hc.η_SG (r + 1) (early S.E S.hc (r + 1) .g2)
          (late S.E S.hc (r + 1) .g2) = some raw ∧
        Block.Preceq Pn.erase raw := by
    intro w hw
    exact clause_at_g2_of_deadline S rho b0 b1 hexec Pn.erase r
      (action_deadline_le_next_earlyG2_of_gst S r hgst) hinv.1
      hstableG2 hmajority w hw hg2hor
  have hK6opening : ∀ w ∈ rho.honest,
      Block.Preceq Pn.erase
          (Protocol.get_fg_root
            (NamedRun.readAt S rho
              (domain S.E S.hc (r + 1) .g1) w).st.core.toHealing.toFG) ∨
        Pn.erase ∈ Internal.PhaseGrades.filteredTree
          (NamedRun.readAt S rho (domain S.E S.hc (r + 1) .g1) w) := by
    intro w hw
    exact fgRootAbove_or_filtered_at_read_of_entry S rho b0 b1 s
      (r + 1) Pn hexec hslash hmargin hsleep hscope hno hinv.2 hheld0
      w hw (domain S.E S.hc (r + 1) .g1) hb0open
      (q10_domain_lt_a S (r + 1) .g1)
  exact opening_sg_clause_of_g2_clause S rho hexec.core Pn.erase (r + 1)
    (Nat.succ_pos r) hG2 hK6opening hopenHor


/--  successor. The current entry history supplies the next round's
`JointAt` facts. The next opening SG clause then gives the next carrier floor,
and that floor extends the entry history to the following round. -/
theorem outageInvariant_step_of_clause
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round)
    (Pn : NamedBlock V) (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hheld0 : ∀ w ∈ rho.honest,
      Pn ∈ (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (hinv : OutageInvariantAt S rho Pn b0 s r)
    (hb0next : b0 ≤ S.a (r + 1))
    (hsg : ∀ w ∈ rho.honest,
      let n := NamedRun.readAt S rho (domain S.E S.hc (r + 1) .g1) w
      Block.Preceq Pn.erase n.st.core.F ∨
        ∃ raw : Block V,
          (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing
            (r + 1)).g2 = some (some raw) ∧ Block.Preceq Pn.erase raw) :
    OutageInvariantAt S rho Pn b0 s (r + 1) := by
  have hjoint : S.a (r + 1) ≤ rho.horizon → ∀ w ∈ rho.honest,
      Internal.NamedJointOutage.JointAt S rho Pn (r + 1) w := by
    intro hhor w hw
    exact jointAt_of_entry_history S rho b0 b1 s (r + 1) Pn hexec
      hslash hmargin hsleep hscope hno hinv.2 hheld0 hb0next hhor w hw
  have hcarriers : HonestCarriersAbove S rho Pn.erase (r + 1) :=
    carriersAbove_of_sg_clause S rho b0 b1 Pn (r + 1) hexec
      (Nat.succ_pos r) hsg hjoint
  exact ⟨hcarriers,
    entry_history_succ_of_carrierAbove S rho b0 b1 (r + 1) Pn
      hexec hscope (Nat.succ_pos r) hinv.2 hcarriers⟩


/-- Carry the stable floor from one G2 domain to the next. This is the
pointwise form of `stable_above_P_through_succ_of_floor`; its premise is only
the start value that the proof consumes. -/
private theorem mutual_stable_at_next_g2
    (S : Setup V) (rho : NamedRun V) (P : Block V) (r : Round)
    (core : NamedAdmissibleCore S rho)
    (hstart : ∀ w ∈ rho.honest, Block.Preceq P
      (Protocol.get_stable (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st.core))
    (hviable : ∀ u ∈ rho.honest,
      Block.Preceq P
          (Protocol.get_fg_root
            (Proofs.HealingSurface.relativeG2Read S rho (r + 2) u).st.core.toHealing.toFG) ∨
        P ∈ Internal.PhaseGrades.filteredTree
          (Proofs.HealingSurface.relativeG2Read S rho (r + 2) u))
    (hwrite : ∀ w ∈ rho.honest, ∀ (k : Nat) (u : Time),
      domain S.E S.hc (r + 1) .g2 ≤ u →
      u < domain S.E S.hc (r + 2) .g2 →
      rho.events[k]? = some (.tick w u) →
      0 < S.E.slotOf u →
      u = Protocol.support_cutoff S.E (S.E.slotOf u) →
      ∀ G, dutyStableRoot S
          (NamedActionReads.confirmationReadFrom
            S (NamedRun.stateBefore S rho k w) u) = some G →
        Block.Preceq P (NamedRun.stateBefore S rho k w).st.core.latest_stable →
        Block.Preceq P G ∨ Block.Preceq G P) :
    ∀ w ∈ rho.honest, Block.Preceq P
      (Protocol.get_stable (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 2) .g2) w).st.core) := by
  intro w hw
  let start := domain S.E S.hc (r + 1) .g2
  let stop := domain S.E S.hc (r + 2) .g2
  let i := (rho.events.filter (fun e => decide (e.time < start))).length
  let j := (rho.events.filter (fun e => decide (e.time < stop))).length
  have hstartStop : start ≤ stop := base_domain_g2_mono S (Nat.le_succ (r + 1))
  have hi : NamedRun.stateBeforeTime S rho start w =
      NamedRun.stateBefore S rho i w :=
    congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S
      core.toNamedScheduleWellFormed start) w
  have hj : NamedRun.stateBeforeTime S rho stop w =
      NamedRun.stateBefore S rho j w :=
    congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S
      core.toNamedScheduleWellFormed stop) w
  have hij : i ≤ j := by
    dsimp only [i, j]
    exact strict_lengths_mono rho hstartStop
  have hhold : Block.Preceq P
      (Protocol.get_stable (NamedRun.stateBeforeTime S rho start w).st.core) :=
    hstart w hw
  have hcases := stateBefore_stable_covered_of_comparable S rho w i j hij
    (by
      rw [← hi]
      unfold Protocol.get_stable at hhold
      split at hhold
      · exact Or.inr hhold
      · exact Or.inl hhold)
    (fun k u hik hkj he hpos hcut G hG hlat => by
      have huStart : start ≤ u := Proofs.Optimistic.le_time_of_index_ge S
        core.toNamedScheduleWellFormed (t := start) (j := k) hik he
      have huStop : u < stop := by
        have hins := Proofs.Optimistic.filter_true_of_index_lt S
          core.toNamedScheduleWellFormed (fun e => decide (e.time < stop))
          (Proofs.Optimistic.downward_lt stop) hkj he
        simpa only [decide_eq_true_eq, NamedEvent.time] using hins
      exact hwrite w hw k u (by simpa only [start] using huStart)
        (by simpa only [stop] using huStop) he hpos hcut G hG hlat)
  have hcompat : Block.compatible P
      (NamedRun.stateBeforeTime S rho stop w).st.core.F = true := by
    rcases hviable w hw with hroot | htree
    · have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        S rho stop w
      have hFroot := Proofs.Records.preceq_get_fg_root_of_F
        (st := (NamedRun.stateBeforeTime S rho stop w).st.core.toHealing.toFG)
        (by simpa only [Protocol.Store.toHealing] using hFJ)
      have hroot' : Block.Preceq P
          (Protocol.get_fg_root
            (NamedRun.stateBeforeTime S rho stop w).st.core.toHealing.toFG) := by
        simpa only [stop, Proofs.HealingSurface.relativeG2Read,
          Internal.PhaseGrades.filteredTree] using hroot
      exact Block.compatible_of_preceq_common hroot' hFroot
    · have hFleP := q10_filtered_F (by
          simpa only [stop, Proofs.HealingSurface.relativeG2Read,
            Internal.PhaseGrades.filteredTree] using htree)
      simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr hFleP
  rw [hj]
  rw [hj] at hcompat
  rcases hcases with hF | hstable
  · have hFstable : Block.Preceq
        (NamedRun.stateBefore S rho j w).st.core.F
        (Protocol.get_stable (NamedRun.stateBefore S rho j w).st.core) := by
      unfold Protocol.get_stable
      split
      · assumption
      · exact Block.preceq_self _
    exact Block.preceq_trans hF hFstable
  · exact preceq_get_stable_of_cases _ (Or.inr hstable) hcompat

/-- Full auxiliary successor. After the next carrier/history pair is built,
the new history supplies viability at the following G2 read and compatibility
for every intervening stable-record write. This carries the stable interval
needed by the next application of `outageInvariant_step`. -/
theorem outageMutualState_step
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round)
    (Pn : NamedBlock V) (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hheld0 : ∀ w ∈ rho.honest,
      Pn ∈ (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (hstate : OutageMutualStateAt S rho Pn b0 s r)
    (hgst : S.E.t_GST ≤ S.a r)
    (hb0nextG2 : b0 ≤ domain S.E S.hc (r + 1) .g2)
    (hopenHor : domain S.E S.hc (r + 1) .g1 ≤ rho.horizon) :
    OutageMutualStateAt S rho Pn b0 s (r + 1) := by
  have hstableG2 : ∀ w ∈ rho.honest, Block.Preceq Pn.erase
      (Protocol.get_stable (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g2) w).st.core) := hstate.2.1
  have hb0open : b0 ≤ domain S.E S.hc (r + 1) .g1 :=
    hb0nextG2.trans (q10_domain_g2_lt_domain_g1 S (r + 1)).le
  have hsgNext := opening_sg_clause_of_outageInvariant S rho b0 b1 s r
    Pn hexec hslash hmargin hsleep hforming hscope hno hheld0 hstate.1
    hgst hstableG2 hb0open hopenHor
  have hinvNext := outageInvariant_step_of_clause S rho b0 b1 s r Pn
    hexec hslash hmargin hsleep hscope hno hheld0 hstate.1
    (hb0open.trans (FrameForward.domain_le_a S (r + 1) .g1)) hsgNext
  have hb0next : b0 ≤ domain S.E S.hc (r + 2) .g2 :=
    hb0open.trans (domain_g1_le_next_domain_g2 S (r + 1))
  have hviableNext := mutual_relativeG2_viability S rho b0 b1 s
    (r + 2) Pn hexec hslash hmargin hsleep hscope hno hinvNext.2
      hheld0 hb0next
  have hstableNext : OutageStableAtNextG2 S rho Pn.erase (r + 1) :=
    mutual_stable_at_next_g2 S rho Pn.erase r hexec.core hstate.2.1
      hviableNext (by
        intro w hw k u huLo huHi he hpos hcut G hG hlat
        have hb0u : b0 ≤ u :=
          hb0nextG2.trans huLo
        have huAction : u < S.a (r + 2) :=
          huHi.trans_le (FrameForward.domain_le_a S (r + 2) .g2)
        have hfg := mutual_fg_compatibility S rho b0 b1 s (r + 2) Pn
          hexec hslash hmargin hsleep hscope hno hinvNext.2 hheld0 w hw u
          hb0u huAction
        have hbefore := Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S
          hexec.core.toNamedScheduleWellFormed he
        change NamedRun.stateBefore S rho k w =
          NamedRun.stateBeforeTime S rho u w at hbefore
        have hread : NamedActionReads.confirmationReadFrom S
            (NamedRun.stateBefore S rho k w) u =
            NamedActionReads.confirmationReadAt S rho w u := by
          rw [hbefore]
          rfl
        have hG' : dutyStableRoot S
            (NamedActionReads.confirmationReadAt S rho w u) = some G := by
          rw [← hread]
          exact hG
        exact confirmationDutyRoot_comparable_of_sg_clause S rho b0 b1 Pn
          (r + 1) hexec (Nat.succ_pos r) hsgNext w hw u huLo huHi
          hcut (hviableNext w hw) hfg hG')
  exact ⟨hinvNext, hstableNext, hsgNext⟩


/-- Beyond the last action in the run there are no honest round voters, so the
carrier conjunct is vacuous and the entry history still advances. -/
private theorem outageInvariant_step_after_horizon
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round)
    (Pn : NamedBlock V) (hexec : OutageExecution S rho b0 b1)
    (hscope : NamedRun.blockInRun S rho Pn)
    (hinv : OutageInvariantAt S rho Pn b0 s r)
    (hshort : ¬ domain S.E S.hc (r + 1) .g1 ≤ rho.horizon) :
    OutageInvariantAt S rho Pn b0 s (r + 1) := by
  have hcarriers : HonestCarriersAbove S rho Pn.erase (r + 1) := by
    intro u hu
    obtain ⟨huHon, a, _hval, _hround, i, hi, _hem⟩ :=
      (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u (r + 1)).mp hu
    have hmem : NamedEvent.tick u (S.a (r + 1)) ∈ rho.events :=
      List.mem_iff_getElem?.mpr ⟨i, hi⟩
    have hactHor : S.a (r + 1) ≤ rho.horizon :=
      (hexec.core.toNamedScheduleWellFormed.in_horizon _ hmem).2
    exact False.elim (hshort ((FrameForward.domain_le_a S (r + 1) .g1).trans hactHor))
  exact ⟨hcarriers,
    entry_history_succ_of_carrierAbove S rho b0 b1 (r + 1) Pn
      hexec hscope (Nat.succ_pos r) hinv.2 hcarriers⟩




/--  induction with its stable interval carried internally. Once the next
opening is beyond the run horizon, honest carrier sets are empty and the
induction continues through the vacuous branch. -/
theorem outageInvariant_all
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r0 : Round)
    (Pn : NamedBlock V) (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hheld0 : ∀ w ∈ rho.honest,
      Pn ∈ (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (hseed : OutageMutualStateAt S rho Pn b0 s r0)
    (hgst0 : S.E.t_GST ≤ S.a r0)
    (hb0next0 : b0 ≤ domain S.E S.hc (r0 + 1) .g2) :
    ∀ r : Round, r0 ≤ r → OutageInvariantAt S rho Pn b0 s r := by
  have hstatus : ∀ k : Nat,
      OutageMutualStateAt S rho Pn b0 s (r0 + k) ∨
        (OutageInvariantAt S rho Pn b0 s (r0 + k) ∧
          ¬ domain S.E S.hc (r0 + k) .g1 ≤ rho.horizon) := by
    intro k
    induction k with
    | zero => exact Or.inl (by simpa only [Nat.add_zero] using hseed)
    | succ k ih =>
        rcases ih with hstate | ⟨hinv, hshort⟩
        · by_cases hopen : domain S.E S.hc (r0 + k + 1) .g1 ≤ rho.horizon
          · have hle : r0 ≤ r0 + k := Nat.le_add_right r0 k
            have hgst : S.E.t_GST ≤ S.a (r0 + k) :=
              hgst0.trans (Assembly.a_mono S hle)
            have hb0next : b0 ≤ domain S.E S.hc (r0 + k + 1) .g2 :=
              hb0next0.trans (base_domain_g2_mono S (Nat.add_le_add_right hle 1))
            have hnext := outageMutualState_step S rho b0 b1 s
              (r0 + k) Pn hexec hslash hmargin hsleep hforming hscope
                hno hheld0 hstate hgst hb0next hopen
            exact Or.inl (by simpa only [Nat.add_assoc] using hnext)
          · have hnext := outageInvariant_step_after_horizon S rho b0 b1 s
              (r0 + k) Pn hexec hscope hstate.1 hopen
            have hnext' : OutageInvariantAt S rho Pn b0 s (r0 + (k + 1)) := by
              simpa only [Nat.add_assoc] using hnext
            have hshort' : ¬ domain S.E S.hc (r0 + (k + 1)) .g1 ≤
                rho.horizon := by
              simpa only [Nat.add_assoc] using hopen
            exact Or.inr ⟨hnext', hshort'⟩
        · have hmono : domain S.E S.hc (r0 + k) .g1 ≤
              domain S.E S.hc (r0 + k + 1) .g1 := by
            rw [domain_g1_eq_opening, domain_g1_eq_opening]
            exact base_opening_mono S (Nat.le_succ _)
          have hshortNext : ¬ domain S.E S.hc (r0 + k + 1) .g1 ≤
              rho.horizon := fun h => hshort (hmono.trans h)
          have hnext := outageInvariant_step_after_horizon S rho b0 b1 s
            (r0 + k) Pn hexec hscope hinv hshortNext
          have hnext' : OutageInvariantAt S rho Pn b0 s (r0 + (k + 1)) := by
            simpa only [Nat.add_assoc] using hnext
          have hshort' : ¬ domain S.E S.hc (r0 + (k + 1)) .g1 ≤
              rho.horizon := by
            simpa only [Nat.add_assoc] using hshortNext
          exact Or.inr ⟨hnext', hshort'⟩
  intro r hr
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
  rcases hstatus k with hstate | hshort
  · exact hstate.1
  · exact hshort.1


#print axioms entry_history_succ_of_carrierAbove
#print axioms outageInvariant_seed
#print axioms outageInvariant_all








end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
