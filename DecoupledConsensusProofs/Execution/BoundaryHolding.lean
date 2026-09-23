module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ExcludesRefute
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.IntrinsicEntry
public import DecoupledConsensusProofs.Execution.FinalityGuard
public import DecoupledConsensusProofs.Protocol.Handlers.RelayGuards
public import DecoupledConsensusProofs.Execution.BodyRetention
public import DecoupledConsensusProofs.Execution.OutageProvenance
public import DecoupledConsensusProofs.Execution.OutputSeedCore

@[expose] public section

namespace DecoupledConsensusModel.Proofs.NamedBoundaryHolding
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
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

private theorem formation_margin_action_deadline (S : Setup V) (s : Round) (b0 : Time)
    (hmargin : FormationMargin S s b0) : S.a s + S.E.Δ ≤ b0 := by
  have hfirst := Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt S
    (Nat.lt_succ_self s)
  have hnext : Protocol.proposal_time S.E (S.hc.opening_slot (s + 1)) ≤
      formationConfirmationTime S (s + 1) + S.E.Δ := by
    change Protocol.proposal_time S.E (S.hc.opening_slot (s + 1)) ≤
      Protocol.proposal_time S.E (S.hc.opening_slot (s + 1)) + 2 * S.E.Δ + S.E.Δ
    have hd : 0 ≤ S.E.Δ := le_of_lt S.E.Δ_pos
    have hnonneg : 0 ≤ 2 * S.E.Δ + S.E.Δ :=
      add_nonneg (Int.mul_nonneg (by norm_num) hd) hd
    calc
      _ ≤ Protocol.proposal_time S.E (S.hc.opening_slot (s + 1)) +
          (2 * S.E.Δ + S.E.Δ) := le_add_of_nonneg_right hnonneg
      _ = _ := by ring
  have hmargin' : formationConfirmationTime S (s + 1) + S.E.Δ ≤ b0 :=
    old_margin_of_new S s b0 hmargin
  have hfirst' : S.a s + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot (s + 1)) := by
    simpa only [Nat.succ_eq_add_one] using hfirst
  exact hfirst'.trans (hnext.trans hmargin')

/-- Healthy relay from the actual accepted full body. The global i+1 skip
read and each returned call's own post-index are transferred separately. -/
theorem accepted_protected_block_held_at_boundary
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s : Round)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    {i : Nat} {source : V} {B : NamedBlock V} {ta : Time}
    (hsource : source ∈ rho.honest)
    (hacc : NamedRun.acceptsAt S rho i source (.block B) ta)
    (hdeadline : ta + S.E.Δ ≤ b0)
    (hno : NoHonestConflictAbove S rho b0 B.erase) :
    ∀ reader ∈ rho.honest, B ∈ (NamedRun.stateBeforeTime S rho b0 reader).st.bodies := by
  have hsourceHeld : B ∈ (NamedRun.stateBefore S rho (i + 1) source).st.bodies := by
    simpa only [NamedReceipt.processed, decide_eq_true_eq] using hacc.2.2
  have hscope := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hsource (i + 1) hsourceHeld)
  have hta : ta < b0 :=
    (lt_add_of_pos_right ta S.E.Δ_pos).trans_le hdeadline
  obtain ⟨sourceEvent, hsourceEvent, _, hsourceTime⟩ := hacc.1.2
  have hsourceCut : sourceEvent.time < b0 := by simpa only [hsourceTime] using hta
  intro reader hreader
  by_cases hskip : B ∈ (NamedRun.stateBefore S rho (i + 1) reader).st.bodies
  · exact post_event_held_at_strict_read S rho hexec.core.sorted b0 reader
      hsourceEvent hsourceCut hskip
  · have hmissing : NamedReceipt.processed
        (NamedRun.stateBefore S rho (i + 1) reader).st (.block B) = false := by
      simpa only [NamedReceipt.processed, decide_eq_false_iff_not] using hskip
    by_cases hdeadlineHeld : B ∈
        (NamedRun.stateBeforeTime S rho (ta + S.E.Δ) reader).st.bodies
    · exact stateBeforeTime_bodies_mono_of_le S rho hexec.core.sorted
        hdeadline hdeadlineHeld
    · have htimeGuard :=
        NamedFinalityGuard.protected_prefix_held_or_finality_guard_before_boundary_time
          S rho b0 b1 s hexec hmargin hsleep B hscope hno reader hreader
          (ta + S.E.Δ) hdeadline
      rcases htimeGuard with hheld | hF
      · exact False.elim (hdeadlineHeld hheld)
      · have hguard := not_excludes_of_F_preceq_later_time S rho hexec.core.sorted
          le_rfl hF
        obtain ⟨td, htime, htd, j, hcall⟩ :=
          hexec.healthy.relay_block source hsource i B ta hacc reader hreader hmissing
            hdeadline hguard
        have htdCut : td < b0 := htd.trans_le hdeadline
        obtain ⟨e, he, _, het⟩ := hcall.2
        have heCut : e.time < b0 := by simpa only [het] using htdCut
        have hguard := NamedFinalityGuard.protected_prefix_held_or_finality_guard_before_boundary
          S rho b0 b1 s hexec hmargin hsleep B hscope hno reader hreader j e he heCut
        have hpost : B ∈ (NamedRun.stateBefore S rho (j + 1) reader).st.bodies := by
          rcases hguard with hheld | hF
          · exact NamedBodyRetention.stateBefore_bodies_mono S rho reader (Nat.le_succ j) hheld
          · exact NamedRelayGuards.handled_block_held_of_finalized_prefix S rho
              hexec.core.toNamedScheduleWellFormed hexec.core.toNamedDeliveryWellFormed
              hexec.core.toNamedRootCollisionFree hacc hcall htime hF
        exact post_event_held_at_strict_read S rho hexec.core.sorted b0 reader he heCut hpost

/-- The protected full representative comes from the actual stable read.
Non-genesis membership supplies an original acceptance before a_s. -/
theorem stable_prefix_held_at_boundary
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1)
    (hsleep : OutageSleepyThroughout S rho)
    (source : V) (hsource : source ∈ rho.honest) (s : Round) (P : Block V)
    (hmargin : FormationMargin S s b0)
    (hseed : DecoupledConsensusModel.Proofs.NamedOutageClosure.OutputSeed
      S rho b0 s P)
    (hno : NoHonestConflictAbove S rho b0 P) :
    ∃ Pn : NamedBlock V, Pn.erase = P ∧ NamedRun.blockInRun S rho Pn ∧
      ∀ reader ∈ rho.honest, Pn ∈ (NamedRun.stateBeforeTime S rho b0 reader).st.bodies := by
  obtain ⟨Pn, he, hheld, hscope⟩ := hseed.held source hsource
  refine ⟨Pn, he, hscope, ?_⟩
  by_cases hgen : Pn = NamedBlock.genesis
  · subst Pn
    intro reader _
    exact (Proofs.NamedRuntime.stateBeforeTime_invariants S rho b0 reader).1.1.1.2.2.1.1
  · have hstrict : Pn ∈ (NamedRun.stateBeforeTime S rho (S.a s) source).st.bodies := hheld
    obtain ⟨k, hread, hbefore⟩ :=
      Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho hexec.core.sorted (S.a s)
    rw [hread] at hstrict
    rcases NamedOutageProvenance.held_block_origin S rho k source hstrict with
      hgen' | ⟨i, hik, ta, hacc⟩
    · exact False.elim (hgen hgen')
    · obtain ⟨e, hevent, _, het⟩ := hacc.1.2
      have hta : ta < S.a s := by simpa only [het] using hbefore i e hik hevent
      have hdeadline : ta + S.E.Δ ≤ b0 :=
        (Int.add_le_add_right hta.le S.E.Δ).trans
          (formation_margin_action_deadline S s b0 hmargin)
      have hnoNamed : NoHonestConflictAbove S rho b0 Pn.erase := by simpa only [he] using hno
      exact accepted_protected_block_held_at_boundary S rho b0 b1 s hexec hmargin hsleep
        hsource hacc hdeadline hnoNamed

end DecoupledConsensusModel.Proofs.NamedBoundaryHolding

end
