module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.TickBridges
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Records
public import DecoupledConsensusProofs.Protocol.Grades.ProposalParent

@[expose] public section

/-! # Candidate safety at a confirmation evaluation
Section 7 writes `live_confirmed` unconditionally, then advances
`latest_confirmed` only when the previous record precedes the selected value. This
module isolates the exact cross-slot fact that this guarded write needs.
The protocol-local part is proved here. If the selected value is compatible
with the previous `latest_confirmed`, the new record contains the selected value:
either the previous record precedes it and the guard writes it, or it precedes the
previous record and the guard keeps an already deeper value. The run bridge then
shows that same result at the public evaluation instant.
What remains is `PriorLatestCompatibleAtEvaluation`: the current candidate is
compatible with the record accumulated before this evaluation. This is the
candidate-safety invariant, not another form of absorption. Its intended GST
zero proof has the same shape as the sibling TSQ monotonicity proof:
same-slot uniqueness, confirmation-to-next-view adoption, ordinary-walk
capture, and slot induction.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Protocol (HealConfig)
open Internal
open Execution
open Internal.NamedRecoveryRead
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Candidate inclusion and compatibility -/

/-- At a support-cutoff tick, the exposed record is the confirmation update's
record, under the contract the tick's own cache determines. The optional
attestation branch follows the update and does not write `latest_confirmed`
(`Protocol.Monotone.attest_with_latest`, the `latest_confirmed` twin of
`TickBridges.attest_with_live_confirmed`). Byte-for-byte
`TickBridges.on_tick_emit_confirmation`, targeting `latest_confirmed`. -/
theorem on_tick_emit_confirmation_latest (S : Setup V) (v : V) (n : NodeState V)
    (s : Slot) (hs : 0 < s) :
    (on_tick_emit S v n (Protocol.support_cutoff S.E s)).1.st.latest_confirmed =
      (Protocol.NamedDuties.update_confirmation_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S n
            (Protocol.support_cutoff S.E s)).cache)
        S.E S.hc
        (NamedActionReads.confirmationReadFrom S n
          (Protocol.support_cutoff S.E s)).st (s - 1)).latest_confirmed := by
  have hslot : S.E.slotOf (Protocol.support_cutoff S.E s) = s := slotOf_support_cutoff S.E s
  simp only [NamedNode.tick, NamedProfile.tick, Protocol.NamedTick.tick,
    Protocol.TickScheduler.runWith, Protocol.NamedTick.namedOps, hslot,
    support_cutoff_ne_proposal_time S.E s, support_cutoff_ne_vote_time S.E s, hs,
    and_true, and_false, false_and, if_true, if_false,
    NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
    Protocol.NamedStore.setClock]
  split
  · exact attest_with_latest _ S.E S.hc _ _ _
  · rfl

/-- `latest_confirmed` is unchanged across an event interval that contains no
tick of the node. Deliveries do not write the field, and events of another
node do not change this node's state. -/
theorem stateBefore_latest_confirmed_of_no_tick (S : Setup V) (rho : Run V) (v : V)
    {m : Nat} :
    ∀ n : Nat, m ≤ n →
      (∀ (j : Nat) (e : Event V), m ≤ j → j < n → rho.events[j]? = some e →
        ∀ t' : Time, e ≠ Event.tick v t') →
      (rho.stateBefore S n v).st.latest_confirmed =
        (rho.stateBefore S m v).st.latest_confirmed := by
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
                  exact node_process_latest S _ o
                · simp only [NamedWorld.step]
                  rw [Function.update_of_ne (Ne.symm hu)]
      · rw [Nat.le_antisymm hm hge]

/-- The exposed record at a public time is the output of that node's tick.
Later same-time events are deliveries, which leave the record unchanged. -/
theorem latest_confirmed_stateAt (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) {v : V} (hv : v ∈ rho.honest) {t : Time}
    (hpub : PublicTime S t) (ht0 : 0 ≤ t) (hthor : t ≤ rho.horizon) :
    (rho.storeAt S v t).latest_confirmed =
      (on_tick_emit S v (rho.stateBeforeTime S t v) t).1.st.latest_confirmed := by
  obtain ⟨i, hi⟩ :=
    List.mem_iff_getElem?.mp (NamedScheduleWellFormed.tick_total sch v hv t hpub ht0 hthor)
  have hiN : i < (rho.events.filter (fun e => decide (e.time ≤ t))).length := by
    by_contra hcon
    have hp := filter_false_of_index_ge S sch _ (downward_le t) (Nat.le_of_not_lt hcon) hi
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
      have hp := filter_true_of_index_lt S sch _ (downward_le t) hjN hget
      simpa [NamedEvent.time] using hp
    have hge : t ≤ t' := by
      have hk := key_le_of_index_lt S sch (Nat.lt_of_succ_le hij) hi hget
      exact Proofs.Bridges.time_le_of_key_le hk
    have hteq : t' = t := le_antisymm hle hge
    subst hteq
    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hget
    obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
    have hev : rho.events[j] = rho.events[i] := by rw [hje, hie]
    have := (List.Nodup.getElem_inj_iff (NamedScheduleWellFormed.nodup sch)).mp hev
    omega
  rw [Run.storeAt, stateAt_eq_take S sch t]
  rw [stateBefore_latest_confirmed_of_no_tick S rho v _ (by omega) hno, hstep,
    stateBefore_tick_eq_stateBeforeTime S sch hi]


/-- **The exposed record at the slot-`s` evaluation is the record written by
`update_confirmation_with` over the confirmation duty's own prepared read**,
under the contract that read's cache determines. Byte-for-byte
`TickBridges.live_confirmed_eq_update`, targeting `latest_confirmed`; `confStore`
does not name the actual duty input (: the running contract is the
cache-derived `frameContract`, not the default), so the statement is phrased
over `confirmationInputRead` directly, as its `live_confirmed` twin already is. -/
theorem latest_confirmed_eq_update (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) {v : V} (hv : v ∈ rho.honest) (s : Slot)
    (hthor : Protocol.confirmation_time S.E s ≤ rho.horizon) :
    (rho.storeAt S v (Protocol.confirmation_time S.E s)).latest_confirmed =
      (Protocol.NamedDuties.update_confirmation_with
        (NamedProfile.gradeContract (confirmationInputRead S rho v s).cache) S.E S.hc
        (confirmationInputRead S rho v s).st s).latest_confirmed := by
  have hsucc : Protocol.confirmation_time S.E s = Protocol.support_cutoff S.E (s + 1) :=
    Protocol.confirmation_time_eq_support_cutoff_succ S.E s
  have hread : confirmationInputRead S rho v s =
      NamedActionReads.confirmationReadFrom S
        (rho.stateBeforeTime S (Protocol.support_cutoff S.E (s + 1)) v)
        (Protocol.support_cutoff S.E (s + 1)) := by
    show NamedActionReads.confirmationReadAt S rho v (Protocol.confirmation_time S.E s) = _
    rw [hsucc]
    rfl
  rw [latest_confirmed_stateAt S sch hv (publicTime_confirmation_time S s)
    (confirmation_time_nonneg S.E s) hthor, hsucc,
    on_tick_emit_confirmation_latest S v
      (rho.stateBeforeTime S (Protocol.support_cutoff S.E (s + 1)) v) (s + 1)
      (Nat.succ_pos s), hread, Nat.add_sub_cancel]

/-! ## The smallest cross-slot invariant -/







end Protocol
end DecoupledConsensusModel

end
