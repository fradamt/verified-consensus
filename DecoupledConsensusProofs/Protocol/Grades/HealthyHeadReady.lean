module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.BlockStamp
public import DecoupledConsensusProofs.Execution.OutageProvenance
public import DecoupledConsensusProofs.Protocol.Handlers.RelayGuards
public import DecoupledConsensusProofs.Protocol.Schedule.SlotInduction
public import DecoupledConsensusProofs.Execution.ExcludesRefute

@[expose] public section

/-! Reusable healthy-prefix head relay and lookup/stamp completion.
Uses the cleaned SGArrival import path for healthy reuse.
No outage-entry assumption occurs in this module's theorem or proof. -/
namespace DecoupledConsensusModel.Proofs.NamedHealthyHeadReady
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
private theorem time_le_of_key_le {e f : NamedEvent V} (h : e.key ≤ f.key) :
    e.time ≤ f.time := by
  rcases Prod.Lex.le_iff.mp h with hlt | ⟨heq, _⟩
  · exact hlt.le
  · exact heq.le

omit [DecidableEq V] [Fintype V] in
/-- This is a list-prefix equation, not an inference from folded states. -/
private theorem strict_filter_eq_take (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (cut : Time) :
    rho.events.filter (fun e => decide (e.time < cut)) =
      rho.events.take (rho.events.filter (fun e => decide (e.time < cut))).length := by
  have hdown : ∀ e f : NamedEvent V, e.key ≤ f.key →
      decide (f.time < cut) = true → decide (e.time < cut) = true := by
    intro e f hkey hf
    simp only [decide_eq_true_eq] at hf ⊢
    exact (time_le_of_key_le hkey).trans_lt hf
  refine List.prefix_iff_eq_take.mp ?_
  rw [Proofs.Bridges.filter_eq_takeWhile_of_pairwise hdown _ hsorted]
  exact List.takeWhile_prefix _

omit [DecidableEq V] [Fintype V] in
/-- Every event through j passes the strict filter. Count that actual take
prefix to obtain the post-event index bound, including same-time events. -/
private theorem post_index_le_strict_filter_length (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (cut : Time)
    {j : Nat} {e : NamedEvent V} (he : rho.events[j]? = some e)
    (ht : e.time < cut) :
    j + 1 ≤ (rho.events.filter (fun x => decide (x.time < cut))).length := by
  obtain ⟨hjLen, hjGet⟩ := List.getElem?_eq_some_iff.mp he
  have htake : (rho.events.take (j + 1)).filter (fun x => decide (x.time < cut)) =
      rho.events.take (j + 1) := by
    apply List.filter_eq_self.mpr
    intro x hx
    simp only [decide_eq_true_eq]
    obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hx
    have hklt : k < j + 1 := by
      have hlen := (List.getElem?_eq_some_iff.mp hk).1
      rw [List.length_take] at hlen
      exact hlen.trans_le (Nat.min_le_left _ _)
    have hkRun : rho.events[k]? = some x := by
      simpa only [List.getElem?_take_of_lt hklt] using hk
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hklt) with hkj | rfl
    · obtain ⟨hkLen, hkGet⟩ := List.getElem?_eq_some_iff.mp hkRun
      have hkey := (List.pairwise_iff_getElem.mp hsorted) k j hkLen hjLen hkj
      rw [hkGet, hjGet] at hkey
      exact (time_le_of_key_le hkey).trans_lt ht
    · have hxe : x = e := Option.some.inj (hkRun.symm.trans he)
      simpa only [hxe] using ht
  have hsplit : rho.events.filter (fun x => decide (x.time < cut)) =
      (rho.events.take (j + 1)).filter (fun x => decide (x.time < cut)) ++
      (rho.events.drop (j + 1)).filter (fun x => decide (x.time < cut)) := by
    conv_lhs => rw [← List.take_append_drop (j + 1) rho.events]
    rw [List.filter_append]
  have hlength := congrArg List.length hsplit
  rw [htake, List.length_append, List.length_take,
    Nat.min_eq_left (Nat.succ_le_of_lt hjLen)] at hlength
  omega

private theorem post_event_held_at_strict_read (S : Setup V) (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    (cut : Time) (reader : V) {j : Nat} {e : NamedEvent V} {B : NamedBlock V}
    (he : rho.events[j]? = some e) (ht : e.time < cut)
    (hheld : B ∈ (NamedRun.stateBefore S rho (j + 1) reader).st.bodies) :
    B ∈ (NamedRun.stateBeforeTime S rho cut reader).st.bodies := by
  have hindex := post_index_le_strict_filter_length rho hsorted cut he ht
  have hretained := NamedBodyRetention.stateBefore_bodies_mono S rho reader hindex hheld
  unfold NamedRun.stateBeforeTime
  rw [strict_filter_eq_take rho hsorted cut]
  exact hretained

private theorem strict_read_eq_index (S : Setup V) (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (t : Time) :
    NamedRun.stateBeforeTime S rho t =
      NamedRun.stateBefore S rho (rho.events.filter (fun e => decide (e.time < t))).length :=
  congrArg (fun events => events.foldl (NamedWorld.step S) NamedWorld.init)
    (strict_filter_eq_take rho hsorted t)

omit [DecidableEq V] [Fintype V] in
private theorem strict_lengths_mono (rho : NamedRun V) {early late : Time}
    (ht : early ≤ late) :
    (rho.events.filter (fun e => decide (e.time < early))).length ≤
      (rho.events.filter (fun e => decide (e.time < late))).length := by
  have hsub := List.Sublist.filter (fun e : NamedEvent V => decide (e.time < late))
    (List.filter_sublist (p := fun e : NamedEvent V => decide (e.time < early)) (l := rho.events))
  have hs : (rho.events.filter (fun e => decide (e.time < early))).filter
      (fun e => decide (e.time < late)) = rho.events.filter (fun e => decide (e.time < early)) := by
    apply List.filter_eq_self.mpr
    intro e he
    have hearly : e.time < early := by
      simpa only [decide_eq_true_eq] using (List.mem_filter.mp he).2
    simpa only [decide_eq_true_eq] using hearly.trans_le ht
  rw [hs] at hsub
  exact hsub.length_le

private theorem strict_body_stamp_carry (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (reader : V) {early late : Time}
    (ht : early ≤ late) (H : NamedBlock V)
    (hH : H ∈ (NamedRun.stateBeforeTime S rho early reader).st.bodies) :
    H ∈ (NamedRun.stateBeforeTime S rho late reader).st.bodies ∧
      (NamedRun.stateBeforeTime S rho late reader).st.core.timestamp_block H.erase =
        (NamedRun.stateBeforeTime S rho early reader).st.core.timestamp_block H.erase := by
  rw [strict_read_eq_index S rho sch.sorted early] at hH
  rw [strict_read_eq_index S rho sch.sorted late, strict_read_eq_index S rho sch.sorted early]
  exact NamedBlockStamp.stateBefore_body_stamp_mono S rho reader (strict_lengths_mono rho ht) hH

omit [Fintype V] in
private theorem named_self (H : NamedBlock V) : NamedBlock.Preceq H H := by
  cases H <;> simp [NamedBlock.Preceq, NamedBlock.preceq]

private theorem held_find_at_strict (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (roots : NamedRootCollisionFree S rho)
    (reader : V) (hreader : reader ∈ rho.honest) (t : Time) (H : NamedBlock V)
    (hH : H ∈ (NamedRun.stateBeforeTime S rho t reader).st.bodies) :
    Block.find? (NamedRun.stateBeforeTime S rho t reader).st.core.T H.erase.root =
      some H.erase := by
  obtain ⟨n, hread, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho sch.sorted t
  rw [hread] at hH ⊢
  have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho n reader).1.1.1
  have hHscope := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hreader n hH)
  have hHraw : H.erase ∈ (NamedRun.stateBefore S rho n reader).st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hH
  apply Proofs.Optimistic.find?_eq_some_of_unique hHraw
  intro raw hraw hroot
  rw [hcoh.1] at hraw
  obtain ⟨other, hother, rfl⟩ := Finset.mem_image.mp hraw
  have hotherScope := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hreader n hother)
  have hroots : other.root = H.root :=
    (Proofs.NamedWire.erase_root other).symm.trans (hroot.trans (Proofs.NamedWire.erase_root H))
  have heq : other = H := roots.root_injective other H hotherScope hHscope other H
    (Or.inl (named_self other)) (Or.inr (named_self H)) hroots
  exact congrArg NamedBlock.erase heq

private theorem head_held_at_early
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (healthyCut : Time) (healthy : NamedHealthyPrefixDelivery S rho healthyCut)
    (source : V) (hsource : source ∈ rho.honest) (reader : V) (hreader : reader ∈ rho.honest)
    (H : NamedBlock V) (sourceCut targetEarly targetRead : Time)
    (hHsource : H ∈ (NamedRun.stateBeforeTime S rho sourceCut source).st.bodies)
    (hDeadline : sourceCut + S.E.Δ ≤ targetEarly) (hOrder : targetEarly ≤ targetRead)
    (hHealthy : targetEarly ≤ healthyCut)
    (hF : Block.Preceq (NamedRun.stateBeforeTime S rho targetRead reader).st.core.F H.erase) :
    H ∈ (NamedRun.stateBeforeTime S rho targetEarly reader).st.bodies := by
  by_cases hgen : H = NamedBlock.genesis
  · subst H
    exact (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (targetEarly) reader).1.1.1.2.2.1.1
  · obtain ⟨n, hread, hbefore⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho core.sorted
      (sourceCut)
    rw [hread] at hHsource
    rcases NamedOutageProvenance.held_block_origin S rho n source hHsource with
      hgen' | ⟨i, hin, ta, hacc⟩
    · exact False.elim (hgen hgen')
    · obtain ⟨eSource, heSource, _, htSource⟩ := hacc.1.2
      have hta : ta < sourceCut := by
        simpa only [htSource] using hbefore i eSource hin heSource
      have hdeadline : ta + S.E.Δ < targetEarly :=
        (Int.add_lt_add_right hta S.E.Δ).trans_le hDeadline
      have htaEarly : ta < targetEarly :=
        (lt_add_of_pos_right ta S.E.Δ_pos).trans hdeadline
      have hcut : targetEarly ≤ healthyCut := hHealthy
      by_cases hskip : H ∈ (NamedRun.stateBefore S rho (i + 1) reader).st.bodies
      · exact post_event_held_at_strict_read S rho core.sorted
          (targetEarly) reader heSource
          (by simpa only [htSource] using htaEarly) hskip
      · have hmissing :
            NamedReceipt.processed (NamedRun.stateBefore S rho (i + 1) reader).st (.block H) =
              false := by
          simpa only [NamedReceipt.processed, decide_eq_false_iff_not] using hskip
        have hguard := not_excludes_of_F_preceq_later_time S rho core.sorted
          (hdeadline.le.trans hOrder) hF
        obtain ⟨td, hlo, hhi, j, hcall⟩ := healthy.relay_block source hsource i H ta hacc
          reader hreader hmissing (hdeadline.le.trans hcut) hguard
        obtain ⟨e, he, _, het⟩ := hcall.2
        have htdEarly : td < targetEarly := hhi.trans hdeadline
        have heEarly : e.time < targetEarly := by simpa only [het] using htdEarly
        have heDomain : e.time < targetRead := heEarly.trans_le hOrder
        have hindex := post_index_le_strict_filter_length rho core.sorted
          (targetRead) he heDomain
        have hFmono := Proofs.NamedRuntime.stateBefore_F_mono S rho reader
          ((Nat.le_succ j).trans hindex)
        have hFcall : Block.Preceq (NamedRun.stateBefore S rho j reader).st.core.F H.erase := by
          apply Block.preceq_trans hFmono
          rw [← strict_read_eq_index S rho core.sorted (targetRead)]
          exact hF
        have hpost := NamedRelayGuards.handled_block_held_of_finalized_prefix S rho
          core.toNamedScheduleWellFormed core.toNamedDeliveryWellFormed
          core.toNamedRootCollisionFree hacc hcall hlo hFcall
        exact post_event_held_at_strict_read S rho core.sorted
          (targetEarly) reader he heEarly hpost

private theorem head_held_at_early_after_gst
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (source : V) (hsource : source ∈ rho.honest) (reader : V)
    (hreader : reader ∈ rho.honest) (H : NamedBlock V)
    (sourceCut targetEarly targetRead : Time)
    (hHsource : H ∈ (NamedRun.stateBeforeTime S rho sourceCut source).st.bodies)
    (hDeadline : max sourceCut S.E.t_GST + S.E.Δ ≤ targetEarly)
    (hOrder : targetEarly ≤ targetRead) (hCut : targetEarly ≤ rho.horizon)
    (hF : Block.Preceq
      (NamedRun.stateBeforeTime S rho targetRead reader).st.core.F H.erase) :
    H ∈ (NamedRun.stateBeforeTime S rho targetEarly reader).st.bodies := by
  by_cases hgen : H = NamedBlock.genesis
  · subst H
    exact (Proofs.NamedRuntime.stateBeforeTime_invariants S rho targetEarly reader).1.1.1.2.2.1.1
  · obtain ⟨n, hread, hbefore⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
      core.sorted sourceCut
    rw [hread] at hHsource
    rcases NamedOutageProvenance.held_block_origin S rho n source hHsource with
      hgen' | ⟨i, hin, ta, hacc⟩
    · exact False.elim (hgen hgen')
    · obtain ⟨eSource, heSource, _, htSource⟩ := hacc.1.2
      have hta : ta < sourceCut := by
        simpa only [htSource] using hbefore i eSource hin heSource
      have hmax : max ta S.E.t_GST ≤ max sourceCut S.E.t_GST :=
        max_le_max hta.le (le_refl _)
      have htaDeadline : max ta S.E.t_GST + S.E.Δ ≤ targetEarly :=
        (add_le_add hmax (le_refl _)).trans hDeadline
      have htaMax : ta < max ta S.E.t_GST + S.E.Δ := by
        exact (le_max_left _ _).trans_lt
          (lt_add_of_pos_right (max ta S.E.t_GST) S.E.Δ_pos)
      have htaEarly : ta < targetEarly := htaMax.trans_le htaDeadline
      by_cases hskip : H ∈
          (NamedRun.stateBefore S rho (i + 1) reader).st.bodies
      · exact post_event_held_at_strict_read S rho core.sorted
          targetEarly reader heSource
          (by simpa only [htSource] using htaEarly) hskip
      · have hmissing :
            NamedReceipt.processed
              (NamedRun.stateBefore S rho (i + 1) reader).st (.block H) = false := by
          simpa only [NamedReceipt.processed, decide_eq_false_iff_not] using hskip
        have hguard := not_excludes_of_F_preceq_later_time S rho core.sorted
          (htaDeadline.trans hOrder) hF
        obtain ⟨td, hlo, hhi, j, hcall⟩ := core.toNamedSynchrony.relay_block
          source hsource i H ta hacc reader hreader hmissing
          (htaDeadline.trans hCut) hguard
        obtain ⟨e, he, _, het⟩ := hcall.2
        have htdEarly : td < targetEarly := hhi.trans_le htaDeadline
        have heEarly : e.time < targetEarly := by simpa only [het] using htdEarly
        have heDomain : e.time < targetRead := heEarly.trans_le hOrder
        have hindex := post_index_le_strict_filter_length rho core.sorted
          targetRead he heDomain
        have hFmono := Proofs.NamedRuntime.stateBefore_F_mono S rho reader
          ((Nat.le_succ j).trans hindex)
        have hFcall : Block.Preceq
            (NamedRun.stateBefore S rho j reader).st.core.F H.erase := by
          apply Block.preceq_trans hFmono
          rw [← strict_read_eq_index S rho core.sorted targetRead]
          exact hF
        have hpost := NamedRelayGuards.handled_block_held_of_finalized_prefix S rho
          core.toNamedScheduleWellFormed core.toNamedDeliveryWellFormed
          core.toNamedRootCollisionFree hacc hcall hlo hFcall
        exact post_event_held_at_strict_read S rho core.sorted
          targetEarly reader he heEarly hpost

/-- Reusable healthy-prefix primitive. Source holding, deadlines, and the
target finalized-prefix relation are concrete caller-produced facts. -/
theorem healthy_head_body_at_read
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (healthyCut : Time) (healthy : NamedHealthyPrefixDelivery S rho healthyCut)
    (source : V) (hsource : source ∈ rho.honest) (reader : V) (hreader : reader ∈ rho.honest)
    (H : NamedBlock V) (sourceCut targetEarly targetRead : Time)
    (hHsource : H ∈ (NamedRun.stateBeforeTime S rho sourceCut source).st.bodies)
    (hDeadline : sourceCut + S.E.Δ ≤ targetEarly) (hOrder : targetEarly ≤ targetRead)
    (hHealthy : targetEarly ≤ healthyCut)
    (hF : Block.Preceq (NamedRun.stateBeforeTime S rho targetRead reader).st.core.F H.erase) :
    H ∈ (NamedRun.stateBeforeTime S rho targetRead reader).st.bodies ∧
      stampedBefore (NamedRun.stateBeforeTime S rho targetRead reader).st.core.timestamp_block
        targetEarly H.erase = true ∧
      Block.find? (NamedRun.stateBeforeTime S rho targetRead reader).st.core.T H.erase.root =
        some H.erase := by
  have hEarly := head_held_at_early S rho core healthyCut healthy source hsource reader hreader
    H sourceCut targetEarly targetRead hHsource hDeadline hOrder hHealthy hF
  have hStamp := NamedBlockStamp.held_body_stampedBefore_stateBeforeTime S rho
    core.toNamedScheduleWellFormed reader targetEarly H hEarly
  obtain ⟨hHeld, hCarry⟩ := strict_body_stamp_carry S rho core.toNamedScheduleWellFormed
    reader hOrder H hEarly
  refine ⟨hHeld, ?_, held_find_at_strict S rho core.toNamedScheduleWellFormed
    core.toNamedRootCollisionFree reader hreader targetRead H hHeld⟩
  unfold stampedBefore at hStamp ⊢
  rw [hCarry]
  exact hStamp

/-- Reusable post-GST head relay. The source acceptance may precede GST; the
 synchrony deadline is therefore the model's `max` deadline, not `ta + Δ`. -/
theorem healthy_head_body_at_read_after_gst
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (source : V) (hsource : source ∈ rho.honest) (reader : V)
    (hreader : reader ∈ rho.honest) (H : NamedBlock V)
    (sourceCut targetEarly targetRead : Time)
    (hHsource : H ∈ (NamedRun.stateBeforeTime S rho sourceCut source).st.bodies)
    (hDeadline : max sourceCut S.E.t_GST + S.E.Δ ≤ targetEarly)
    (hOrder : targetEarly ≤ targetRead) (hCut : targetEarly ≤ rho.horizon)
    (hF : Block.Preceq
      (NamedRun.stateBeforeTime S rho targetRead reader).st.core.F H.erase) :
    H ∈ (NamedRun.stateBeforeTime S rho targetRead reader).st.bodies ∧
      stampedBefore
        (NamedRun.stateBeforeTime S rho targetRead reader).st.core.timestamp_block
        targetEarly H.erase = true ∧
      Block.find? (NamedRun.stateBeforeTime S rho targetRead reader).st.core.T H.erase.root =
        some H.erase := by
  have hEarly := head_held_at_early_after_gst S rho core source hsource reader hreader
    H sourceCut targetEarly targetRead hHsource hDeadline hOrder hCut hF
  have hStamp := NamedBlockStamp.held_body_stampedBefore_stateBeforeTime S rho
    core.toNamedScheduleWellFormed reader targetEarly H hEarly
  obtain ⟨hHeld, hCarry⟩ := strict_body_stamp_carry S rho core.toNamedScheduleWellFormed
    reader hOrder H hEarly
  refine ⟨hHeld, ?_, held_find_at_strict S rho core.toNamedScheduleWellFormed
    core.toNamedRootCollisionFree reader hreader targetRead H hHeld⟩
  unfold stampedBefore at hStamp ⊢
  rw [hCarry]
  exact hStamp

#print axioms healthy_head_body_at_read_after_gst

end DecoupledConsensusModel.Proofs.NamedHealthyHeadReady

end
