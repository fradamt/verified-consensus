module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.Runtime
public import DecoupledConsensusProofs.Execution.NetworkBindings

@[expose] public section

/-!
Honest strict-read clock and slot uniformity.
The support lemmas reason about the actual filtered event list. They do not
infer an event from equality between folded states.
-/
namespace DecoupledConsensusModel.Proofs.NamedClockUniform
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

private theorem fold_clock_origin (S : Setup V) (events : List (NamedEvent V))
    (reader : V) :
    let out := events.foldl (NamedWorld.step S) NamedWorld.init
    (out reader).st.core.t = 0 ∨
      NamedEvent.tick reader (out reader).st.core.t ∈ events := by
  induction events using List.reverseRecOn with
  | nil =>
      left
      simp [NamedWorld.init, NamedNode.initial, Protocol.NamedStore.initial,
        Protocol.Store.init]
  | append_singleton events e ih =>
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [Proofs.NamedRuntime.step_clock_eq]
      cases e with
      | deliver v o t =>
          rcases ih with hzero | htick
          · exact Or.inl hzero
          · exact Or.inr (List.mem_append_left _ htick)
      | tick v t =>
          by_cases hrv : reader = v
          · subst v
            simp
          · simp only [if_neg hrv]
            rcases ih with hzero | htick
            · exact Or.inl hzero
            · exact Or.inr (List.mem_append_left _ htick)

private theorem strict_clock_origin (S : Setup V) (rho : NamedRun V)
    (cut : Time) (reader : V) :
    let clock := (NamedRun.stateBeforeTime S rho cut reader).st.core.t
    clock = 0 ∨
      NamedEvent.tick reader clock ∈
        rho.events.filter (fun e => decide (e.time < cut)) := by
  simpa only [NamedRun.stateBeforeTime] using
    fold_clock_origin S (rho.events.filter (fun e => decide (e.time < cut))) reader

private theorem strict_clock_nonneg (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (cut : Time) (reader : V) :
    0 ≤ (NamedRun.stateBeforeTime S rho cut reader).st.core.t := by
  rcases strict_clock_origin S rho cut reader with hzero | htick
  · rw [hzero]
  · have hmem := (List.mem_filter.mp htick).1
    exact (sch.in_horizon _ hmem).1

private theorem tick_mem_le_strict_clock (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) {cut : Time} {reader : V} {t : Time}
    (htick : NamedEvent.tick reader t ∈
      rho.events.filter (fun e => decide (e.time < cut))) :
    t ≤ (NamedRun.stateBeforeTime S rho cut reader).st.core.t := by
  let filtered := rho.events.filter (fun e => decide (e.time < cut))
  let filteredRun : NamedRun V := { rho with events := filtered }
  have hsorted : filtered.Pairwise (fun e f => e.key ≤ f.key) := by
    simpa only [filtered] using
      sch.sorted.filter (fun e => decide (e.time < cut))
  have hnonneg : ∀ e ∈ filteredRun.events, 0 ≤ e.time := by
    intro e he
    change e ∈ filtered at he
    exact (sch.in_horizon e (List.mem_filter.mp he).1).1
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp htick
  have hiLen : i < filtered.length := (List.getElem?_eq_some_iff.mp hi).1
  have hle := Proofs.NamedRuntime.tick_time_le_clock S filteredRun hsorted hnonneg hi hiLen
  simpa only [filteredRun, filtered, NamedRun.stateBeforeTime, NamedRun.stateBefore,
    List.take_length] using hle

private theorem strict_clock_le (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (cut : Time)
    (v : V) (_hv : v ∈ rho.honest) (w : V) (hw : w ∈ rho.honest) :
    (NamedRun.stateBeforeTime S rho cut v).st.core.t ≤
      (NamedRun.stateBeforeTime S rho cut w).st.core.t := by
  let clock := (NamedRun.stateBeforeTime S rho cut v).st.core.t
  rcases strict_clock_origin S rho cut v with hzero | htick
  · rw [hzero]
    exact strict_clock_nonneg S rho sch cut w
  · have hfilter := List.mem_filter.mp htick
    have horiginal : NamedEvent.tick v clock ∈ rho.events := hfilter.1
    have hbefore : clock < cut := by
      simpa only [NamedEvent.time, decide_eq_true_eq] using hfilter.2
    have hpublic : PublicTime S clock := sch.tick_public v clock horiginal
    have hbounds := sch.in_horizon _ horiginal
    have hmatching : NamedEvent.tick w clock ∈ rho.events :=
      sch.tick_total w hw clock hpublic hbounds.1 hbounds.2
    have hmatchingFiltered : NamedEvent.tick w clock ∈
        rho.events.filter (fun e => decide (e.time < cut)) :=
      List.mem_filter.mpr ⟨hmatching, by simpa only [NamedEvent.time, decide_eq_true_eq]⟩
    exact tick_mem_le_strict_clock S rho sch hmatchingFiltered

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

private theorem stateBeforeTime_slot_clock (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (cut : Time) (reader : V) :
    (NamedRun.stateBeforeTime S rho cut reader).st.core.s =
      S.E.slotOf (NamedRun.stateBeforeTime S rho cut reader).st.core.t := by
  obtain ⟨i, hread, _⟩ :=
    Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho sch.sorted cut
  rw [hread]
  exact stateBefore_slot_clock S rho i reader

/-- Honest readers have the same clock and slot at every strict read. The
schedule supplies matching ticks; no horizon, public-time, or clock callback is
an input. -/
theorem honest_strict_clock_uniform (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (cut : Time)
    (v : V) (hv : v ∈ rho.honest) (w : V) (hw : w ∈ rho.honest) :
    (NamedRun.stateBeforeTime S rho cut v).st.core.t =
        (NamedRun.stateBeforeTime S rho cut w).st.core.t ∧
      (NamedRun.stateBeforeTime S rho cut v).st.core.s =
        (NamedRun.stateBeforeTime S rho cut w).st.core.s := by
  have hclock : (NamedRun.stateBeforeTime S rho cut v).st.core.t =
      (NamedRun.stateBeforeTime S rho cut w).st.core.t :=
    le_antisymm (strict_clock_le S rho sch cut v hv w hw)
      (strict_clock_le S rho sch cut w hw v hv)
  refine ⟨hclock, ?_⟩
  rw [stateBeforeTime_slot_clock S rho sch cut v,
    stateBeforeTime_slot_clock S rho sch cut w, hclock]

end DecoupledConsensusModel.Proofs.NamedClockUniform

end
