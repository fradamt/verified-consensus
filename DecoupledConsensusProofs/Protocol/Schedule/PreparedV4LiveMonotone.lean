module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.PreparedV4LiveSelection
public import DecoupledConsensusProofs.Protocol.Grades.PreparedV4ConfirmationOutputs

@[expose] public section

/-! # Prepared V4 live-confirmed monotonicity -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

namespace PreparedV4Records

private theorem preceq_liveField_at_prefix_of_suffixSelections
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

end PreparedV4Records

namespace Handover

private theorem confirmationTime_mono_live_v4
    (E : Env V) {s t : Slot} (h : s ≤ t) :
    Protocol.confirmation_time E s ≤ Protocol.confirmation_time E t := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ,
    Protocol.confirmation_time_eq_support_cutoff_succ]
  exact support_cutoff_mono E (Nat.add_le_add_right h 1)

/-- The V4 live field does not retreat after the opening refresh. -/
theorem SettledBootstrapPreparedV4.liveConfirmed_mono_core_of_pins
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (_of_liveAtConfirmation : ∀ s, start ≤ s →
      Protocol.confirmation_time S.E s ≤ rho.horizon →
      ∀ v ∈ rho.honest, ∀ w ∈ rho.honest, ∀ t,
        Protocol.confirmation_time S.E
          (S.hc.opening_slot (base + S.hc.η_SG)) ≤ t →
        t < Protocol.confirmation_time S.E s →
          Block.Preceq (rho.storeAt S w t).live_confirmed
            (rho.storeAt S v
              (Protocol.confirmation_time S.E s)).live_confirmed)
    {v : V} (hv : v ∈ rho.honest) {t u : Time}
    (ht : Protocol.confirmation_time S.E start ≤ t) (htu : t ≤ u) :
    Block.Preceq (rho.storeAt S v t).live_confirmed
      (rho.storeAt S v u).live_confirmed := by
  have htlo : Protocol.confirmation_time S.E
      (S.hc.opening_slot (base + S.hc.η_SG)) ≤ t :=
    (confirmationTime_mono_live_v4 S.E hboot.settled).trans ht
  let m := (rho.events.filter (fun e => decide (e.time ≤ t))).length
  let n := (rho.events.filter (fun e => decide (e.time ≤ u))).length
  have hbase : Block.Preceq (rho.storeAt S v t).live_confirmed
      (rho.stateBefore S m v).st.live_confirmed := by
    simpa only [Run.storeAt,
      stateAt_eq_take S adm.toNamedScheduleWellFormed, m] using
        Block.preceq_self (rho.storeAt S v t).live_confirmed
  have hmn : m ≤ n := filter_le_length_mono rho htu
  have hfold :=
    PreparedV4Records.preceq_liveField_at_prefix_of_suffixSelections
      S rho v (rho.storeAt S v t).live_confirmed hbase n hmn
  have hresult := hfold (by
    intro i C hmi hin hsel
    obtain ⟨q, hqevent, hqC, hqhor⟩ :=
      confirmationSelectionAt_slot_core S adm hsel
    have hafter : t < Protocol.confirmation_time S.E q := by
      have hfalse := filter_false_of_index_ge
        S adm.toNamedScheduleWellFormed _ (downward_le t) hmi hqevent
      simpa only [decide_eq_false_iff_not, not_le, Event.time] using hfalse
    have hbefore : Protocol.confirmation_time S.E q ≤ u := by
      have htrue := filter_true_of_index_lt
        S adm.toNamedScheduleWellFormed _ (downward_le u) hin hqevent
      simpa only [decide_eq_true_eq, Event.time] using htrue
    have hstart : start ≤ q := by
      by_contra hnot
      have hqstart := confirmationTime_mono_live_v4 S.E
        (Nat.le_of_lt (Nat.lt_of_not_ge hnot))
      exact (not_lt_of_ge (hqstart.trans ht)) hafter
    have hdir := _of_liveAtConfirmation q hstart hqhor v hv v hv t htlo hafter
    rw [live_confirmed_eq_update
      S adm.toNamedScheduleWellFormed hv q hqhor] at hdir
    rw [← hqC]
    simpa only [confirmationWrite,
      Internal.NamedRecoveryRead.confirmationInputRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedDuties.update_confirmation_with,
      Proofs.Optimistic.slotOf_confirmation_time, Nat.add_sub_cancel,
      Nat.succ_eq_add_one] using hdir)
  simpa only [Run.storeAt,
    stateAt_eq_take S adm.toNamedScheduleWellFormed, n] using hresult

#print axioms SettledBootstrapPreparedV4.liveConfirmed_mono_core_of_pins

/-- Live monotonicity prebuilt over only the named confirmation anchor and band. -/
theorem SettledBootstrapPreparedV4.liveConfirmed_mono_core_of_anchor_band_pins
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (_of_anchor : ∀ {s : Slot}, start ≤ s →
      Protocol.confirmation_time S.E s ≤ rho.horizon →
      ∀ {w x : V}, w ∈ rho.honest → x ∈ rho.honest →
        Block.Preceq
          (namedConfirmationAnchor S
            (Internal.NamedRecoveryRead.confirmationInputRead S rho w s))
          (voterHeadAt S rho x s))
    (_of_band : ∀ {s : Slot}, start ≤ s →
      Protocol.confirmation_time S.E s ≤ rho.horizon →
      ∀ {v x : V}, x ∈ rho.honest →
      ∀ {X : NamedBlock V}, X.erase = voterHeadAt S rho x s →
        NamedRun.blockInRun S rho X →
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).st.core.h_max - 1 ≤
          (Protocol.derive_named S.E S.cfg X).h)
    {v : V} (hv : v ∈ rho.honest) {t u : Time}
    (ht : Protocol.confirmation_time S.E start ≤ t) (htu : t ≤ u) :
    Block.Preceq (rho.storeAt S v t).live_confirmed
      (rho.storeAt S v u).live_confirmed := by
  exact SettledBootstrapPreparedV4.liveConfirmed_mono_core_of_pins
    S adm hcom hboot hawake hfinality
      (fun s hs hhor v hv w hw t htlo hthi =>
        SettledBootstrapPreparedV4.liveConfirmed_preceq_at_confirmation_core_of_anchor_band_pins
          S adm hcom hboot hawake hfinality _of_anchor _of_band
            hs hhor hv hw htlo hthi)
      hv ht htu

#print axioms SettledBootstrapPreparedV4.liveConfirmed_mono_core_of_anchor_band_pins

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
