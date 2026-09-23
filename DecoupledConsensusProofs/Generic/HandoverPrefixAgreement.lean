module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Execution.PrefixAgreement
public import DecoupledConsensusProofs.Protocol.Handlers.TickBridges
public import DecoupledConsensusProofs.Generic.Sync

@[expose] public section

/-!
# Execution transfer from local prefix agreement

The protocol step reads and writes only the event's validator. Thus the
local event prefix determines the complete node state, including the
anti-slashing record. No participation or safety premise is used here.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem worldStep_congr_at (S : Setup V) {v : V}
    {left right : World V} (h : left v = right v) (e : Event V) :
    World.step S left e v = World.step S right e v := by
  cases e with
  | tick w t =>
      by_cases hw : w = v
      · subst w
        simp only [NamedWorld.step, Function.update_self, h]
      · simp only [NamedWorld.step, Function.update_of_ne (Ne.symm hw), h]
  | deliver w o t =>
      by_cases hw : w = v
      · subst w
        simp only [NamedWorld.step, Function.update_self, h]
      · simp only [NamedWorld.step, Function.update_of_ne (Ne.symm hw), h]

/-- Equal local states stay equal along the same event list. -/
theorem foldl_worldStep_congr_at (S : Setup V) {v : V}
    {left right : World V} (h : left v = right v) (events : List (Event V)) :
    events.foldl (World.step S) left v = events.foldl (World.step S) right v := by
  induction events generalizing left right with
  | nil => exact h
  | cons e events ih => exact ih (worldStep_congr_at S h e)

/-- Removing other validators' events leaves the local result unchanged. -/
theorem foldl_worldStep_filter_node (S : Setup V) (v : V)
    (events : List (Event V)) (initial : World V) :
    events.foldl (World.step S) initial v =
      (events.filter (fun e => decide (e.node = v))).foldl (World.step S) initial v := by
  induction events generalizing initial with
  | nil => rfl
  | cons e events ih =>
      by_cases he : e.node = v
      · simp only [List.foldl_cons, List.filter_cons, he, decide_true,
          if_true]
        exact ih _
      · have hlocal : World.step S initial e v = initial v := by
          cases e with
          | tick w t =>
              simp only [Event.node] at he
              exact Function.update_of_ne (Ne.symm he) _ _
          | deliver w o t =>
              simp only [Event.node] at he
              exact Function.update_of_ne (Ne.symm he) _ _
        simp only [List.foldl_cons, List.filter_cons, he, decide_false, Bool.false_eq_true,
          if_false]
        exact (ih _).trans (foldl_worldStep_congr_at S hlocal _)

/-- Agreement at the cutoff implies agreement at each earlier cutoff. -/
theorem AgreesUntil.mono {rho rho' : Run V} {cutoff time : Time}
    (h : AgreesUntil rho rho' cutoff) (ht : time ≤ cutoff) :
    AgreesUntil rho rho' time := by
  refine ⟨h.honest_subset, ?_⟩
  intro v hv
  have hfilter (events : List (Event V)) :
      (events.filter (fun e => decide (e.node = v ∧ e.time < cutoff))).filter
        (fun e => decide (e.time < time)) =
      events.filter (fun e => decide (e.node = v ∧ e.time < time)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro e he
    by_cases hn : e.node = v
    · by_cases htime : e.time < time
      · have hcut := htime.trans_le ht
        simp [hn, htime, hcut]
      · simp [hn, htime]
    · simp [hn]
  rw [← hfilter rho'.events, ← hfilter rho.events, h.events v hv]

/-- Every strict-time node state in the retained prefix is identical. -/
theorem AgreesUntil.stateBeforeTime_eq (S : Setup V)
    {rho rho' : Run V} {cutoff time : Time}
    (h : AgreesUntil rho rho' cutoff) (ht : time ≤ cutoff)
    {v : V} (hv : v ∈ rho'.honest) :
    rho'.stateBeforeTime S time v = rho.stateBeforeTime S time v := by
  unfold Run.stateBeforeTime NamedRun.stateBeforeTime
  rw [foldl_worldStep_filter_node S v
    (rho'.events.filter (fun e => decide (e.time < time))) World.init,
    foldl_worldStep_filter_node S v
    (rho.events.filter (fun e => decide (e.time < time))) World.init]
  have hfilter (events : List (Event V)) :
      (events.filter (fun e => decide (e.time < time))).filter
        (fun e => decide (e.node = v)) =
      events.filter (fun e => decide (e.node = v ∧ e.time < time)) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro e he
    by_cases hn : e.node = v <;> by_cases ht : e.time < time <;> simp [hn, ht]
  rw [hfilter, hfilter]
  rw [(AgreesUntil.mono h ht).events v hv]

/-- The store projection also agrees at each retained read. -/
theorem AgreesUntil.storeBeforeTime_eq (S : Setup V)
    {rho rho' : Run V} {cutoff time : Time}
    (h : AgreesUntil rho rho' cutoff) (ht : time ≤ cutoff)
    {v : V} (hv : v ∈ rho'.honest) :
    rho'.storeBeforeTime S v time = rho.storeBeforeTime S v time := by
  exact congrArg NodeState.st (AgreesUntil.stateBeforeTime_eq S h ht hv)

/-- Every event of a retained honest validator occurs in both prefixes. -/
theorem AgreesUntil.event_mem_iff {rho rho' : Run V} {cutoff : Time}
    (h : AgreesUntil rho rho' cutoff) {e : Event V}
    (hv : e.node ∈ rho'.honest) (ht : e.time < cutoff) :
    e ∈ rho'.events ↔ e ∈ rho.events := by
  have heq := h.events e.node hv
  constructor
  · intro he
    have hf : e ∈ rho'.events.filter
        (fun d => decide (d.node = e.node ∧ d.time < cutoff)) := by
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨he, trivial, ht⟩
    rw [heq] at hf
    exact (List.mem_filter.mp hf).1
  · intro he
    have hf : e ∈ rho.events.filter
        (fun d => decide (d.node = e.node ∧ d.time < cutoff)) := by
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨he, trivial, ht⟩
    rw [← heq] at hf
    exact (List.mem_filter.mp hf).1

/-- Prefix transfer preserves the exact emitted object, including timeout rows. -/
theorem AgreesUntil.emits_iff (S : Setup V)
    {rho rho' : Run V} (sch : ScheduleWellFormed S rho)
    (sch' : ScheduleWellFormed S rho') {cutoff time : Time}
    (h : AgreesUntil rho rho' cutoff) (ht : time < cutoff)
    {v : V} (hv : v ∈ rho'.honest) (o : Object V) :
    rho'.emits S v o time ↔ rho.emits S v o time := by
  have hstate := AgreesUntil.stateBeforeTime_eq S h ht.le hv
  have hstateN : NamedRun.stateBeforeTime S rho' time v =
      NamedRun.stateBeforeTime S rho time v := hstate
  have hevent : Event.tick v time ∈ rho'.events ↔ Event.tick v time ∈ rho.events :=
    AgreesUntil.event_mem_iff h hv ht
  constructor
  · rintro ⟨i, hi, ho⟩
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (hevent.mp (List.mem_of_getElem? hi))
    refine ⟨j, hj, ?_⟩
    unfold NamedRun.emittedAt at ho ⊢
    have heqi : NamedRun.stateBefore S rho' i v =
        NamedRun.stateBeforeTime S rho' time v :=
      Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S sch' hi
    have heqj : NamedRun.stateBefore S rho j v =
        NamedRun.stateBeforeTime S rho time v :=
      Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S sch hj
    simpa only [heqi, heqj, hstateN] using ho
  · rintro ⟨i, hi, ho⟩
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (hevent.mpr (List.mem_of_getElem? hi))
    refine ⟨j, hj, ?_⟩
    unfold NamedRun.emittedAt at ho ⊢
    have heqi : NamedRun.stateBefore S rho i v =
        NamedRun.stateBeforeTime S rho time v :=
      Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S sch hi
    have heqj : NamedRun.stateBefore S rho' j v =
        NamedRun.stateBeforeTime S rho' time v :=
      Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S sch' hj
    simpa only [heqi, heqj, hstateN] using ho

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
