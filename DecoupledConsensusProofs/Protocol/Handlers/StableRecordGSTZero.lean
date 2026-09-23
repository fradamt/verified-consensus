module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Safety
public import DecoupledConsensusProofs.Objects.AdmissibleCore
public import DecoupledConsensusProofs.Protocol.ChainState.GSTZeroSixFieldBypassNamed
public import DecoupledConsensusProofs.Execution.UserConfirmationHistory
public import DecoupledConsensusProofs.Protocol.Schedule.RecordAtBoundary

@[expose] public section

/-! # Stable-record safety at GST zero on the clean named path -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Statements

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
theorem compatible_of_ancestors_of_compatible_clean {a b c d : Block V}
    (ha : Block.Preceq a b) (hc : Block.Preceq c d)
    (hbd : Block.compatible b d = true) :
    Block.compatible a c = true := by
  simp only [Block.compatible, Bool.or_eq_true] at hbd ⊢
  rcases hbd with hbd | hdb
  · exact Block.preceq_linear (Block.preceq_trans ha hbd) hc
  · exact Block.preceq_linear ha (Block.preceq_trans hc hdb)

private theorem named_update_stable_preserves
    (S : Setup V) (n : NamedNodeState V) (s : Slot) {B : Block V}
    (hold : Block.Preceq B n.st.core.latest_stable)
    (hcompat : Block.compatible B
      (Protocol.NamedDuties.update_confirmation_with
        (NamedProfile.gradeContract n.cache) S.E S.hc n.st s).core.latest_stable = true) :
    Block.Preceq B
      (Protocol.NamedDuties.update_confirmation_with
        (NamedProfile.gradeContract n.cache) S.E S.hc n.st s).core.latest_stable := by
  change Block.Preceq B
    (match NamedOutageClosure.dutyStableRoot S n with
      | some G => Protocol.advance_confirmed n.st.core.latest_stable G
      | none => n.st.core.latest_stable)
  change Block.compatible B
    (match NamedOutageClosure.dutyStableRoot S n with
      | some G => Protocol.advance_confirmed n.st.core.latest_stable G
      | none => n.st.core.latest_stable) = true at hcompat
  cases hroot : NamedOutageClosure.dutyStableRoot S n with
  | none => exact hold
  | some G =>
      simp only [hroot] at hcompat ⊢
      exact Proofs.ConfirmationPolicy.prefix_preceq_advance_of_result_compatible
        hold hcompat

private theorem node_tick_stable_preserves
    (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time) {B : Block V}
    (hold : Block.Preceq B n.st.core.latest_stable)
    (hcompat : Block.compatible B
      (NamedNode.tick S v n t).1.st.core.latest_stable = true) :
    Block.Preceq B (NamedNode.tick S v n t).1.st.core.latest_stable := by
  rcases NamedOutageClosure.node_tick_stable_cases S v n t with hne | hcut
  · rw [hne.2]
    exact hold
  · rw [hcut.2] at hcompat ⊢
    apply named_update_stable_preserves S (NamedActionReads.confirmationReadFrom S n t)
      _ hold
    simpa only [NamedActionReads.confirmationReadFrom] using hcompat

private theorem stable_prefix_preserved
    (S : Setup V) (rho : Run V) (v : V) {B : Block V} {m : Nat}
    (hold : Block.Preceq B (rho.stateBefore S m v).st.core.latest_stable) :
    ∀ n : Nat, m ≤ n →
      (∀ i t, m ≤ i → i < n → rho.events[i]? = some (Event.tick v t) →
        Block.compatible B
          (rho.stateBefore S (i + 1) v).st.core.latest_stable = true) →
      Block.Preceq B (rho.stateBefore S n v).st.core.latest_stable := by
  intro n
  induction n with
  | zero =>
      intro hm _
      simpa only [Nat.le_zero.mp hm] using hold
  | succ n ih =>
      intro hm hcompat
      by_cases hmn : m ≤ n
      · have hprev := ih hmn (fun i t hmi hin he =>
          hcompat i t hmi (Nat.lt_succ_of_lt hin) he)
        unfold Run.stateBefore NamedRun.stateBefore
        rw [List.take_add_one, List.foldl_append]
        cases hn : rho.events[n]? with
        | none => simpa using hprev
        | some e =>
            simp only [Option.toList, List.foldl_cons, List.foldl_nil]
            cases e with
            | tick u t =>
                by_cases huv : u = v
                · subst huv
                  simpa only [NamedWorld.step, Function.update_self] using
                    node_tick_stable_preserves S u
                      (rho.stateBefore S n u) t hprev
                      (by
                        simpa only [Run.stateBefore, NamedRun.stateBefore,
                          List.take_add_one, hn, List.foldl_append, Option.toList,
                          List.foldl_cons, List.foldl_nil, NamedWorld.step,
                          Function.update_self] using
                          hcompat n t hmn (Nat.lt_succ_self n) hn)
                · simpa only [NamedWorld.step,
                    Function.update_of_ne (Ne.symm huv)] using hprev
            | deliver u o t =>
                by_cases huv : u = v
                · subst huv
                  simpa only [NamedWorld.step, Function.update_self,
                    NamedOutageClosure.node_process_stable] using hprev
                · simpa only [NamedWorld.step,
                    Function.update_of_ne (Ne.symm huv)] using hprev
      · have heq : m = n + 1 := by omega
        subst m
        exact hold

private theorem time_filter_eq_take
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho) (t : Time) :
    rho.events.filter (fun e => decide (e.time ≤ t)) =
      rho.events.take (rho.events.filter (fun e => decide (e.time ≤ t))).length := by
  have hpref : rho.events.filter (fun e => decide (e.time ≤ t)) <+: rho.events := by
    rw [Proofs.Bridges.filter_eq_takeWhile_of_pairwise
      (fun e f hk hf => by
        simp only [decide_eq_true_eq] at hf ⊢
        exact (Proofs.Bridges.time_le_of_key_le hk).trans hf) _ sch.sorted]
    exact List.takeWhile_prefix _
  exact List.prefix_iff_eq_take.mp hpref

private theorem readAt_eq_stateBefore_filter
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho) (t : Time) :
    NamedRun.readAt S rho t =
      rho.stateBefore S (rho.events.filter (fun e => decide (e.time ≤ t))).length := by
  unfold NamedRun.readAt Run.stateBefore NamedRun.stateBefore
  rw [← time_filter_eq_take S sch t]

private theorem filter_index_lt_of_time_le
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {t : Time} {i : Nat} {e : Event V} (he : rho.events[i]? = some e)
    (hte : e.time ≤ t) :
    i < (rho.events.filter (fun e => decide (e.time ≤ t))).length := by
  have hmem : e ∈ rho.events.filter (fun e => decide (e.time ≤ t)) :=
    List.mem_filter.mpr ⟨List.mem_of_getElem? he, by simpa using hte⟩
  rw [time_filter_eq_take S sch t] at hmem
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
  have hjlt : j < (rho.events.filter (fun e => decide (e.time ≤ t))).length := by
    have h := (List.getElem?_eq_some_iff.mp hj).1
    rw [List.length_take] at h
    omega
  rw [List.getElem?_take_of_lt hjlt] at hj
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp he
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
  have hij : i = j :=
    (List.Nodup.getElem_inj_iff (NamedScheduleWellFormed.nodup sch)).mp (by rw [hie, hje])
  simpa only [hij] using hjlt

theorem stableRecordMonotoneFrom_of_confirmation_clean
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {t0 : Time} (hconfirm : ConfirmationCompatibleFrom S rho t0) :
    StableRecordMonotoneFrom S rho t0 := by
  intro v hv t t' ht htt' hhor
  have hmle := (Protocol.filter_time_prefix htt' rho.events
    (Protocol.pairwise_time_le S sch)).length_le
  have hmt := readAt_eq_stateBefore_filter S sch t
  have hmt' := readAt_eq_stateBefore_filter S sch t'
  simp only [Run.storeAt] at hmt hmt' ⊢
  rw [hmt, hmt']
  apply stable_prefix_preserved S rho v (Block.preceq_self _) _ hmle
  intro i time hmi _hin he
  have htimeHor : time ≤ rho.horizon :=
    (sch.in_horizon _ (List.mem_of_getElem? he)).2
  have hafter : t < time := by
    by_contra hnot
    have hlt := filter_index_lt_of_time_le S sch he (le_of_not_gt hnot)
    exact (Nat.not_lt_of_ge hmi) hlt
  have hC := hconfirm v hv v hv t time ht (ht.trans hafter.le)
    (hafter.le.trans htimeHor) htimeHor
  change Block.compatible
      (rho.storeAt S v t).latest_confirmed
      (rho.storeAt S v time).latest_confirmed = true at hC
  rw [← Protocol.latest_after_tick_eq_storeAt S sch he] at hC
  change Block.compatible
      (NamedRun.readAt S rho t v).st.core.latest_confirmed
      (rho.stateBefore S (i + 1) v).st.core.latest_confirmed = true at hC
  rw [hmt] at hC
  have hstable0 := ConfirmationOrigin.stateBefore_stable_below_confirmed S rho v
    (rho.events.filter (fun e => decide (e.time ≤ t))).length
  have hstable1 := ConfirmationOrigin.stateBefore_stable_below_confirmed S rho v (i + 1)
  exact compatible_of_ancestors_of_compatible_clean hstable0 hstable1 hC

theorem stableRecordCompatibleFrom_of_confirmation_clean
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {t0 : Time} (hcompat : ConfirmationCompatibleFrom S rho t0) :
    StableRecordCompatibleFrom S rho t0 := by
  intro u hu v hv t t' ht ht' hhor hhor'
  exact compatible_of_ancestors_of_compatible_clean
    (StableRecord.stableBelowConfirmed_storeAt S sch u t)
    (StableRecord.stableBelowConfirmed_storeAt S sch v t')
    (hcompat u hu v hv t t' ht ht' hhor hhor')

namespace WeakGenesis

/-- Finality and user records agree in the genesis regime on the clean path. -/
theorem latest_compatible_finalized_of_gstZero
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest) (hgst : S.E.t_GST = 0)
    (hawake : ∀ r, 0 < r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake) rho.honest S.hc.η_SG r)
    (hzero : Protocol.confirmation_time S.E 0 ≤ rho.horizon)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) (t u : Time) :
    Block.compatible (rho.storeAt S v t).latest_confirmed
      (rho.storeAt S w u).F = true := by
  let h : WeakGenesis S rho :=
    { execution := ExecutionValid.ofNamedAdmissibleCore adm
      synchrony := adm.toNamedSynchrony
      committees := hcom
      gstZero := hgst
      windows := hawake }
  exact latestConfirmed_compatible_finalized_of_weakGenesis S h hzero hv hw t u

/-- Stable records remain compatible with finality at GST zero. -/
theorem stableRecordFinalityCompatibleFrom_of_weakGenesis
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho) :
    StableRecordFinalityCompatibleFrom S rho 0 := by
  intro u hu v hv t t' _ht _ht' hhor _hhor'
  by_cases hzero : Protocol.confirmation_time S.E 0 ≤ rho.horizon
  · exact compatible_of_ancestors_of_compatible_clean
      (StableRecord.stableBelowConfirmed_storeAt
        S h.core.toNamedScheduleWellFormed u t)
      (Block.preceq_self _)
      (latest_compatible_finalized_of_gstZero S h.core h.committees
        h.gstZero h.windows hzero hu hv t t')
  · have hshort : rho.horizon < Protocol.confirmation_time S.E 0 :=
      lt_of_not_ge hzero
    have hlatest := latestConfirmedAt_eq_genesis_of_short_horizon
      S h.core.toNamedScheduleWellFormed hshort u t
    have hstable := StableRecord.stableBelowConfirmed_storeAt
      S h.core.toNamedScheduleWellFormed u t
    change Block.Preceq (rho.storeAt S u t).latest_stable
      (rho.storeAt S u t).latest_confirmed at hstable
    rw [hlatest] at hstable
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inl (Block.preceq_trans hstable (Protocol.preceq_genesis _))

/-- The complete stable-record GST-zero arm. -/
theorem stableRecordCanonicalFrom_of_weakGenesis
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho) :
    StableRecordCanonicalFrom S rho 0 := by
  have hconfirm := confirmationCompatibleFrom_of_weakGenesis_named S h 0
  exact
    { monotone := stableRecordMonotoneFrom_of_confirmation_clean
        S h.core.toNamedScheduleWellFormed hconfirm
      agree := stableRecordCompatibleFrom_of_confirmation_clean
        S h.core.toNamedScheduleWellFormed hconfirm
      finality := stableRecordFinalityCompatibleFrom_of_weakGenesis S h }

end WeakGenesis

#print axioms WeakGenesis.latest_compatible_finalized_of_gstZero
#print axioms stableRecordMonotoneFrom_of_confirmation_clean
#print axioms stableRecordCompatibleFrom_of_confirmation_clean
#print axioms WeakGenesis.stableRecordFinalityCompatibleFrom_of_weakGenesis
#print axioms WeakGenesis.stableRecordCanonicalFrom_of_weakGenesis

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
