module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.WeakConfirmationWalkNamed
public import DecoupledConsensusProofs.Protocol.Schedule.ConfirmationHistory

@[expose] public section

/-! # Directed monotonicity of the prepared live-confirmed field -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

namespace WeakRecords

private theorem preceq_liveField_at_prefix_of_suffixSelections_named
    (S : Setup V) (rho : Run V) (v : V) (B : Block V) {m : Nat}
    (hbase : Block.Preceq B
      (rho.stateBefore S m v).st.live_confirmed) :
    ∀ n, m ≤ n →
      (∀ i C, m ≤ i → i < n →
        ConfirmationSelectionAt S rho v i C → Block.Preceq B C) →
      Block.Preceq B (rho.stateBefore S n v).st.live_confirmed := by
  intro n
  induction n with
  | zero =>
      intro hm _
      simpa only [Nat.le_zero.mp hm] using hbase
  | succ n ih =>
      intro hm hprior
      by_cases heq : m = n + 1
      · simpa only [← heq] using hbase
      have hmn : m ≤ n := by omega
      have hIH := ih hmn (fun i C hmi hin hsel =>
        hprior i C hmi (Nat.lt_succ_of_lt hin) hsel)
      change Block.Preceq B
        (NamedRun.stateBefore S rho (n + 1) v).st.live_confirmed
      rw [Proofs.NamedRuntime.stateBefore_succ]
      cases hn : rho.events[n]? with
      | none => simpa using hIH
      | some e =>
          simp only [Option.toList, List.foldl_cons, List.foldl_nil]
          cases e with
          | deliver u o time =>
              by_cases hu : v = u
              · subst u
                simp only [NamedWorld.step, Function.update_self]
                rw [Proofs.Optimistic.process_live_confirmed]
                exact hIH
              · simp only [NamedWorld.step]
                rw [Function.update_of_ne hu]
                exact hIH
          | tick u time =>
              by_cases hu : v = u
              · subst u
                simp only [NamedWorld.step, Function.update_self]
                by_cases hbranch : 0 < S.E.slotOf time ∧
                    time = Protocol.support_cutoff S.E (S.E.slotOf time)
                · obtain ⟨hpos, ht⟩ := hbranch
                  have hout := Proofs.Optimistic.on_tick_emit_confirmation
                    S v (rho.stateBefore S n v) (S.E.slotOf time) hpos
                  rw [← ht] at hout
                  rw [hout]
                  exact hprior n _ hmn (Nat.lt_succ_self n)
                    ⟨time, hn, hpos, ht, rfl⟩
                · rw [Proofs.Optimistic.on_tick_emit_live_confirmed_of_ne
                    S v (rho.stateBefore S n v) time hbranch]
                  exact hIH
              · simp only [NamedWorld.step]
                rw [Function.update_of_ne hu]
                exact hIH

private theorem liveConfirmed_preceq_genesis_before_first_confirmation_named
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {v : V} {t : Time} (ht : t < Protocol.confirmation_time S.E 0) :
    Block.Preceq (rho.storeAt S v t).live_confirmed Block.genesis := by
  let n := (rho.events.filter (fun e => decide (e.time ≤ t))).length
  have hprior : PriorSelectionsPreceqAtIndex S rho v n Block.genesis := by
    intro i time hi he hpos hcut
    let q := S.E.slotOf time - 1
    have hqk : q + 1 = S.E.slotOf time := Nat.sub_add_cancel hpos
    have htime : time = Protocol.confirmation_time S.E q := by
      rw [Protocol.confirmation_time_eq_support_cutoff_succ, hqk]
      exact hcut
    have hbefore : time ≤ t := by
      have hmem := filter_true_of_index_lt S sch _ (downward_le t) hi he
      simpa only [decide_eq_true_eq, Event.time] using hmem
    have hzero : Protocol.confirmation_time S.E 0 ≤
        Protocol.confirmation_time S.E q := by
      rw [Protocol.confirmation_time_eq_support_cutoff_succ,
        Protocol.confirmation_time_eq_support_cutoff_succ]
      exact support_cutoff_mono S.E (Nat.succ_le_succ (Nat.zero_le q))
    exact False.elim ((not_lt_of_ge hzero) (by
      rw [← htime]
      exact hbefore.trans_lt ht))
  have hbound := stateBefore_live_preceq_of_priorSelections
    S rho v Block.genesis n hprior
  simpa only [Run.storeAt, stateAt_eq_take S sch, n] using hbound

end WeakRecords

namespace WeakGenesis

/-- The prepared live-confirmed field does not retreat at one honest node. -/
theorem liveConfirmed_mono_of_weakGenesis_named
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {v : V} (hv : v ∈ rho.honest) {t t' : Time} (htt' : t ≤ t') :
    Block.Preceq (rho.storeAt S v t).live_confirmed
      (rho.storeAt S v t').live_confirmed := by
  let m := (rho.events.filter (fun e => decide (e.time ≤ t))).length
  let n := (rho.events.filter (fun e => decide (e.time ≤ t'))).length
  have hbase : Block.Preceq (rho.storeAt S v t).live_confirmed
      (rho.stateBefore S m v).st.live_confirmed := by
    simpa only [Run.storeAt, stateAt_eq_take S h.core.toNamedScheduleWellFormed,
      m] using Block.preceq_self (rho.storeAt S v t).live_confirmed
  have hmn : m ≤ n := filter_le_length_mono rho htt'
  have hfold := WeakRecords.preceq_liveField_at_prefix_of_suffixSelections_named
    S rho v (rho.storeAt S v t).live_confirmed hbase n hmn
  have hresult := hfold (by
    intro i C hmi hin hsel
    obtain ⟨q, hqevent, hqC, hqhor⟩ :=
      confirmationSelectionAt_slot_core S h.core hsel
    have hafter : t < Protocol.confirmation_time S.E q := by
      have hfalse := filter_false_of_index_ge
        S h.core.toNamedScheduleWellFormed _ (downward_le t) hmi hqevent
      simpa only [decide_eq_false_iff_not, not_le, Event.time] using hfalse
    have hbefore : Protocol.confirmation_time S.E q ≤ t' := by
      have htrue := filter_true_of_index_lt
        S h.core.toNamedScheduleWellFormed _ (downward_le t') hin hqevent
      simpa only [decide_eq_true_eq, Event.time] using htrue
    rw [← hqC]
    cases q with
    | zero =>
        exact Block.preceq_trans
          (WeakRecords.liveConfirmed_preceq_genesis_before_first_confirmation_named
            S h.core.toNamedScheduleWellFormed hafter)
          (Protocol.preceq_genesis _)
    | succ q =>
        have hdir := liveConfirmed_preceq_at_confirmation_of_weakGenesis_named
          S h (Nat.succ_pos q) hqhor hv hv hafter
        rw [live_confirmed_eq_update
          S h.core.toNamedScheduleWellFormed hv (q + 1) hqhor] at hdir
        simpa only [confirmationWrite,
          NamedRecoveryRead.confirmationInputRead,
          NamedActionReads.confirmationReadAt,
          Protocol.NamedDuties.update_confirmation_with,
          Proofs.Optimistic.slotOf_confirmation_time, Nat.add_sub_cancel,
          Nat.succ_eq_add_one] using hdir)
  simpa only [Run.storeAt,
    stateAt_eq_take S h.core.toNamedScheduleWellFormed, n] using hresult

#print axioms liveConfirmed_mono_of_weakGenesis_named

end WeakGenesis
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
