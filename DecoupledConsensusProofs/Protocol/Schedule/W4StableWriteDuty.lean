module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.FrameFloorBridge
public import DecoupledConsensusProofs.Protocol.Grades.Interpolation
public import DecoupledConsensusProofs.Protocol.Schedule.RecordAtBoundary
public import DecoupledConsensusProofs.Protocol.Handlers.TickBridges
public import DecoupledConsensusProofs.Protocol.Handlers.ConfirmationRecordOrigin

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace W4StableWrite

open Internal Execution
open Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The opening confirmation duty of a round -/

/-- The support-cutoff confirmation duty at a round's opening slot. -/
def dutyTime (S : Setup V) (r : Round) : Time :=
  Protocol.support_cutoff S.E (S.hc.opening_slot r)

private theorem duty_nonneg (S : Setup V) (r : Round) :
    (0 : Time) ≤ dutyTime S r := by
  have hp := Proofs.Optimistic.proposal_time_nonneg S.E (S.hc.opening_slot r)
  have hΔ : (0 : Time) < S.E.Δ := S.E.Δ_pos
  simp only [dutyTime, Protocol.support_cutoff, Protocol.proposal_time] at hp ⊢
  ring_nf at hp ⊢
  nlinarith

private theorem duty_le_action (S : Setup V) (r : Round) :
    dutyTime S r ≤ S.a r := by
  simp only [dutyTime, Protocol.support_cutoff, Setup.a,
    Protocol.HealConfig.a, Protocol.HealConfig.opening_slot, Env.t, slotStart]
  have hΔ : (0 : Time) < S.E.Δ := S.E.Δ_pos
  ring_nf
  nlinarith

private theorem domain_g2_le_duty (S : Setup V) (r : Round) :
    DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2 ≤ dutyTime S r := by
  simp only [DecoupledConsensusModel.Protocol.domain, DecoupledConsensusModel.Protocol.opening,
    DecoupledConsensusModel.Protocol.Phase.domainOffset, dutyTime,
    Protocol.proposal_time, Protocol.support_cutoff]
  have hΔ : (0 : Time) < S.E.Δ := S.E.Δ_pos
  ring_nf
  nlinarith

private theorem domain_g2_lt_duty (S : Setup V) (r : Round) :
    DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2 < dutyTime S r := by
  simp only [DecoupledConsensusModel.Protocol.domain, DecoupledConsensusModel.Protocol.opening,
    DecoupledConsensusModel.Protocol.Phase.domainOffset, dutyTime,
    Protocol.proposal_time, Protocol.support_cutoff]
  have hΔ : (0 : Time) < S.E.Δ := S.E.Δ_pos
  ring_nf
  nlinarith

private theorem duty_round (S : Setup V) (r : Round) :
    S.hc.round_of (S.E.slotOf (dutyTime S r)) = r := by
  unfold dutyTime
  rw [Proofs.Optimistic.slotOf_support_cutoff]
  simp only [Protocol.HealConfig.round_of, Protocol.HealConfig.opening_slot]
  exact Nat.mul_div_cancel _ (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)

private theorem duty_publicTime (S : Setup V) (r : Round) :
    PublicTime S (dutyTime S r) :=
  (Execution.publicTime_iff S (dutyTime S r)).mpr
    ⟨S.hc.opening_slot r, Or.inr (Or.inr (Or.inl rfl))⟩


/-! ## The tick that runs the duty

Copied verbatim from the private helpers of `StableRecordGrowthRun`, which is
on a red import path (`StableRecordSafetyRun` reaches
`WeakProposalResolvedSnapshotRun`). -/

private theorem stateBefore_latest_stable_of_no_tick
    (S : Setup V) (rho : Run V) (v : V) {m : Nat} :
    ∀ n : Nat, m ≤ n →
      (∀ (j : Nat) (e : Event V), m ≤ j → j < n → rho.events[j]? = some e →
        ∀ t' : Time, e ≠ Event.tick v t') →
      (rho.stateBefore S n v).st.latest_stable =
        (rho.stateBefore S m v).st.latest_stable := by
  intro n
  induction n with
  | zero =>
      intro hm _
      rw [Nat.le_zero.mp hm]
  | succ n ih =>
      intro hm h
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · have hmn : m ≤ n := Nat.lt_succ_iff.mp hlt
        rw [← ih hmn (fun j e h1 h2 h3 => h j e h1 (Nat.lt_succ_of_lt h2) h3)]
        unfold Run.stateBefore NamedRun.stateBefore
        rw [List.take_add_one, List.foldl_append]
        cases hn : rho.events[n]? with
        | none => simp
        | some e =>
            have hne := h n e hmn (Nat.lt_succ_self n) hn
            simp only [Option.toList, List.foldl_cons, List.foldl_nil]
            cases e with
            | tick u t' =>
                by_cases hu : u = v
                · exact absurd (by rw [hu] : Event.tick u t' = Event.tick v t') (hne t')
                · simp only [NamedWorld.step]
                  rw [Function.update_of_ne (Ne.symm hu)]
            | deliver u o t' =>
                by_cases hu : u = v
                · subst hu
                  simp only [NamedWorld.step, Function.update_self]
                  exact NamedOutageClosure.node_process_stable S _ o
                · simp only [NamedWorld.step]
                  rw [Function.update_of_ne (Ne.symm hu)]
      · rw [Nat.le_antisymm hm hge]

private theorem latest_stable_stateAt
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {v : V} (hv : v ∈ rho.honest) {t : Time}
    (hpub : PublicTime S t) (ht0 : 0 ≤ t) (hthor : t ≤ rho.horizon) :
    (rho.storeAt S v t).latest_stable =
      (on_tick_emit S v (rho.stateBeforeTime S t v) t).1.st.latest_stable := by
  obtain ⟨i, hi⟩ :=
    List.mem_iff_getElem?.mp (NamedScheduleWellFormed.tick_total sch v hv t hpub ht0 hthor)
  have hiN : i < (rho.events.filter (fun e => decide (e.time ≤ t))).length := by
    by_contra hcon
    have hp := Proofs.Optimistic.filter_false_of_index_ge S sch _ (Proofs.Optimistic.downward_le t)
      (Nat.le_of_not_lt hcon) hi
    simp only [NamedEvent.time, decide_eq_false_iff_not, not_le] at hp
    exact lt_irrefl _ hp
  have hstep : (rho.stateBefore S (i + 1) v) =
      (on_tick_emit S v (rho.stateBefore S i v) t).1 := by
    unfold Run.stateBefore NamedRun.stateBefore
    rw [List.take_add_one, hi, List.foldl_append]
    simp only [Option.toList, List.foldl_cons, List.foldl_nil, NamedWorld.step,
      Function.update_self]
  have hno : ∀ (j : Nat) (e : Event V), i + 1 ≤ j →
      j < (rho.events.filter (fun e => decide (e.time ≤ t))).length →
      rho.events[j]? = some e → ∀ t' : Time, e ≠ Event.tick v t' := by
    intro j e hij hjN hget t' hcon
    subst hcon
    have hle : t' ≤ t := by
      have hp := Proofs.Optimistic.filter_true_of_index_lt S sch _
        (Proofs.Optimistic.downward_le t) hjN hget
      simpa [NamedEvent.time] using hp
    have hge : t ≤ t' := by
      have hk := Proofs.Optimistic.key_le_of_index_lt S sch (Nat.lt_of_succ_le hij) hi hget
      exact Proofs.Bridges.time_le_of_key_le hk
    have hteq : t' = t := le_antisymm hle hge
    subst hteq
    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hget
    obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
    have hev : rho.events[j] = rho.events[i] := by rw [hje, hie]
    have := (List.Nodup.getElem_inj_iff (NamedScheduleWellFormed.nodup sch)).mp hev
    omega
  rw [Run.storeAt, Proofs.Optimistic.stateAt_eq_take S sch t]
  rw [stateBefore_latest_stable_of_no_tick S rho v _ (by omega) hno, hstep,
    Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S sch hi]


/-! ## The two arms of the duty's own stable root -/

/-- **Fallback arm.** Finality at the reader has already reached the block.
Every root the duty can write is at or above the reader's FG root, so the write
covers the block whichever arm of `frameStableRoot` fires. -/
theorem dutyStableRoot_covers_of_fgRoot (S : Setup V) (n : NamedNodeState V)
    {C : Block V}
    (h : Block.Preceq C (Protocol.get_fg_root n.st.core.toHealing.toFG)) :
    ∃ G, NamedOutageClosure.dutyStableRoot S n = some G ∧ Block.Preceq C G := by
  obtain ⟨G, hG⟩ := NamedOutageClosure.dutyStableRoot_some S n
  exact ⟨G, hG,
    Block.preceq_trans h (NamedOutageClosure.fgRoot_preceq_dutyStableRoot S n hG)⟩

#print axioms dutyStableRoot_covers_of_fgRoot

/-- **Active arm.** The reader's own raw G2 root covers the block and the block
is still in the reader's finality-filtered tree, so the projected stable root
covers it. -/
theorem dutyStableRoot_covers_of_frameG2 (S : Setup V) (n : NamedNodeState V)
    {C raw : Block V}
    (hg2 : (NamedOutageClosure.readFrameAt S n).g2 = some (some raw))
    (hmem : C ∈ Protocol.get_filtered_block_tree n.st.core.toHealing.toFG)
    (hCraw : Block.Preceq C raw) :
    ∃ G, NamedOutageClosure.dutyStableRoot S n = some G ∧ Block.Preceq C G := by
  obtain ⟨G, hG, hCG⟩ := NamedOutageClosure.activeG2_covers S n hg2 hmem hCraw
  refine ⟨G, ?_, hCG⟩
  rw [NamedOutageClosure.dutyStableRoot_eq_activeG2, hG]

#print axioms dutyStableRoot_covers_of_frameG2

/-! ## The write -/

/-- **The stable write at the opening confirmation duty.** Whatever the previous
record was, `advance_confirmed` absorbs a stable root above `C`, so the node's
stable record covers `C` from that duty on. Only the schedule is assumed: the
per-node hypothesis is the whole protocol content. -/
theorem stable_preceq_at_duty
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {r : Round} (hr : 0 < r) {C : Block V}
    (hduty : ∀ v ∈ rho.honest, ∃ G,
      NamedOutageClosure.dutyStableRoot S
        (NamedActionReads.confirmationReadAt S rho v (dutyTime S r)) = some G ∧
        Block.Preceq C G)
    (hhor : dutyTime S r ≤ rho.horizon) :
    ∀ v ∈ rho.honest,
      Block.Preceq C (rho.storeAt S v (dutyTime S r)).latest_stable := by
  intro v hv
  obtain ⟨G, hG, hCG⟩ := hduty v hv
  let duty := dutyTime S r
  have hnonneg : (0 : Time) ≤ duty := duty_nonneg S r
  have hpub : PublicTime S duty := duty_publicTime S r
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp
    (NamedScheduleWellFormed.tick_total sch v hv duty hpub hnonneg hhor)
  have hwritten := NamedOutageClosure.confirmation_write_stable_establishes S
    (NamedActionReads.confirmationReadFrom S
      (NamedRun.stateBeforeTime S rho duty v) duty)
    (S.hc.opening_slot r) hG hCG
  have hstate : NamedRun.stateBefore S rho (i + 1) v =
      (on_tick_emit S v (NamedRun.stateBefore S rho i v) duty).1 :=
    Proofs.NamedRuntime.stateBefore_tick S rho hi
  have hstateTime : NamedRun.stateBefore S rho i v =
      NamedRun.stateBeforeTime S rho duty v :=
    Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S sch hi
  have hstableTick : Block.Preceq C
      (NamedRun.stateBefore S rho (i + 1) v).st.latest_stable := by
    rw [hstate]
    have heq : (on_tick_emit S v (NamedRun.stateBefore S rho i v) duty).1.st.latest_stable =
        (Protocol.NamedDuties.update_confirmation_with
          (NamedProfile.gradeContract
            (NamedActionReads.confirmationReadFrom S
              (NamedRun.stateBefore S rho i v) duty).cache)
          S.E S.hc
          (NamedActionReads.confirmationReadFrom S
            (NamedRun.stateBefore S rho i v) duty).st
          (S.hc.opening_slot r)).core.latest_stable := by
      simpa only [duty, dutyTime] using
        (StableRecord.on_tick_emit_confirmation_stable S v
          (NamedRun.stateBefore S rho i v) (S.hc.opening_slot r)
          (Nat.mul_pos hr (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)))
    rw [heq]
    simpa only [hstateTime] using hwritten
  have hstableEmit : Block.Preceq C
      (on_tick_emit S v (NamedRun.stateBeforeTime S rho duty v) duty).1.st.latest_stable := by
    rw [← hstateTime, ← hstate]
    exact hstableTick
  rw [latest_stable_stateAt S sch hv hpub hnonneg hhor]
  exact hstableEmit

#print axioms stable_preceq_at_duty



/-- The reader-local premise of the write, stated on the reader's own round-`q`
G2 freeze root and its duty read. -/
def DutyCoverAt (S : Setup V) (rho : Run V) (q : Round) (C : Block V) (v : V) :
    Prop :=
  (C ∈ Protocol.get_filtered_block_tree
      (NamedActionReads.confirmationReadAt S rho v (dutyTime S q)).st.core.toHealing.toFG ∧
    ∃ raw : Block V,
      DecoupledConsensusModel.Protocol.freezeRoot S.E
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2) v).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2) v).st.core.F
        S.hc.η_SG q (DecoupledConsensusModel.Protocol.early S.E S.hc q .g2)
        (DecoupledConsensusModel.Protocol.late S.E S.hc q .g2) = some raw ∧
      Block.Preceq C raw) ∨
  Block.Preceq C (Protocol.get_fg_root
    (NamedActionReads.confirmationReadAt S rho v (dutyTime S q)).st.core.toHealing.toFG)

/-- **The per-node write.** Each honest reader's own case of `DutyCoverAt`
gives its duty stable root above `C`, and the duty write absorbs it. -/
theorem stable_preceq_at_duty_of_dutyCover
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    (sch : ScheduleWellFormed S rho) {q : Round} (hq : 0 < q) {C : Block V}
    (hnode : ∀ v ∈ rho.honest, DutyCoverAt S rho q C v)
    (hhor : dutyTime S q ≤ rho.horizon) :
    ∀ v ∈ rho.honest,
      Block.Preceq C (rho.storeAt S v (dutyTime S q)).latest_stable := by
  refine stable_preceq_at_duty S sch hq ?_ hhor
  intro v hv
  have hdomHor : DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2 ≤ rho.horizon :=
    (domain_g2_le_duty S q).trans hhor
  rcases hnode v hv with ⟨hmem, raw, hfreeze, hCraw⟩ | hroot
  · obtain ⟨root, hroot, hCroot⟩ :=
      frameG2_preceq_of_freezeRoot_prepared S rho core v hv q hq (dutyTime S q)
        (duty_round S q) (domain_g2_lt_duty S q) (duty_le_action S q) hdomHor
        hmem hfreeze hCraw
    have hreadRound : NamedOutageClosure.readRound S
        (NamedActionReads.confirmationReadAt S rho v (dutyTime S q)) = q :=
      duty_round S q
    exact dutyStableRoot_covers_of_frameG2 S _
      (by simpa only [NamedOutageClosure.readFrameAt, hreadRound] using hroot)
      hmem hCroot
  · exact dutyStableRoot_covers_of_fgRoot S _ hroot

#print axioms stable_preceq_at_duty_of_dutyCover



end W4StableWrite
end Proofs
end DecoupledConsensusModel

end
