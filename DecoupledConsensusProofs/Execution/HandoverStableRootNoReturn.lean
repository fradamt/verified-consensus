module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.PostGainOpeningStableWrite
public import DecoupledConsensusProofs.Protocol.Grades.PostDeadlineStableRootOrder
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HandoverStableRootCap
public import DecoupledConsensusProofs.Protocol.Handlers.ConfirmationPolicy

@[expose] public section

/-!
# Cap-bounded stable roots do not return

The high post-recovery stable write has named height above the deadline cap.
Compatibility of later post-deadline stable writes preserves that high prefix
through the carrier's opening confirmation read.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Internal.NamedRecoveryRead
open Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

private theorem latestStable_preserves_prefix_of_compatible_roots_noReturn
    (S : Setup V) (rho : Run V) (v : V)
    {lo hi : Nat} {H : Block V}
    (hlo : lo ≤ hi)
    (hbase : Block.Preceq H
      (rho.stateBefore S lo v).st.core.latest_stable)
    (hroots : ∀ i G,
      lo ≤ i → i < hi →
      StableRecord.StableRootAt S rho v i G →
      Block.compatible H G = true) :
    Block.Preceq H
      (rho.stateBefore S hi v).st.core.latest_stable := by
  induction hi with
  | zero =>
      have heq : lo = 0 := Nat.eq_zero_of_le_zero hlo
      simpa only [heq] using hbase
  | succ n ih =>
      by_cases hlon : lo ≤ n
      · have hprev := ih hlon (fun i G hli hin hroot =>
          hroots i G hli (Nat.lt_succ_of_lt hin) hroot)
        unfold Run.stateBefore NamedRun.stateBefore
        rw [List.take_add_one, List.foldl_append]
        cases hn : rho.events[n]? with
        | none => simpa using hprev
        | some e =>
            simp only [Option.toList, List.foldl_cons, List.foldl_nil]
            cases e with
            | deliver u o t =>
                by_cases hu : u = v
                · subst u
                  simpa only [NamedWorld.step, Function.update_self,
                    NamedOutageClosure.node_process_stable] using hprev
                · simpa only [NamedWorld.step,
                    Function.update_of_ne (Ne.symm hu)] using hprev
            | tick u t =>
                by_cases hu : u = v
                · subst u
                  simp only [NamedWorld.step, Function.update_self]
                  by_cases hbranch : 0 < S.E.slotOf t ∧
                      t = Protocol.support_cutoff S.E (S.E.slotOf t)
                  · obtain ⟨hpos, ht⟩ := hbranch
                    have hout := StableRecord.on_tick_emit_confirmation_stable
                      S v (rho.stateBefore S n v) (S.E.slotOf t) hpos
                    rw [← ht] at hout
                    change Block.Preceq H
                      (on_tick_emit S v (rho.stateBefore S n v) t).1.st.latest_stable
                    rw [hout]
                    let nd := NamedActionReads.confirmationReadFrom S
                      (rho.stateBefore S n v) t
                    let root := (NamedProfile.gradeContract nd.cache).stableRoot
                      S.E S.hc nd.st.core.toHealing
                        (S.hc.round_of nd.st.core.s)
                    change Block.Preceq H
                      (match root with
                      | some G => Protocol.advance_confirmed
                          (rho.stateBefore S n v).st.core.latest_stable G
                      | none =>
                          (rho.stateBefore S n v).st.core.latest_stable)
                    cases hroot : root with
                    | none => exact hprev
                    | some G =>
                        have hrootAt : StableRecord.StableRootAt
                            S rho v n G := by
                          refine ⟨t, hn, hpos, ht, ?_⟩
                          simpa only [nd, root,
                            NamedProfile.gradeContract] using hroot
                        exact Proofs.ConfirmationPolicy.prefix_preceq_advance_of_compatible
                          hprev (hroots n G hlon (Nat.lt_succ_self n) hrootAt)
                  · change Block.Preceq H
                      (on_tick_emit S v (rho.stateBefore S n v) t).1.st.latest_stable
                    rw [StableRecord.on_tick_emit_stable_of_ne
                      S v (rho.stateBefore S n v) t hbranch]
                    exact hprev
                · simpa only [NamedWorld.step,
                    Function.update_of_ne (Ne.symm hu)] using hprev
      · have heq : lo = n + 1 := by omega
        simpa only [heq] using hbase

private theorem confirmationSlot_lt_of_later_tick_noReturn
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {v : V} {j i : Nat} {q q' : Slot}
    (hj : rho.events[j]? = some
      (.tick v (Protocol.confirmation_time S.E q)))
    (hi : rho.events[i]? = some
      (.tick v (Protocol.confirmation_time S.E q')))
    (hji : j < i) : q < q' := by
  have htimeLe : Protocol.confirmation_time S.E q ≤
      Protocol.confirmation_time S.E q' := by
    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
    obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
    have hkey := (List.pairwise_iff_getElem.mp sch.sorted) j i hjl hil hji
    rw [hje, hie] at hkey
    exact Proofs.Bridges.time_le_of_key_le hkey
  have htimeLt : Protocol.confirmation_time S.E q <
      Protocol.confirmation_time S.E q' := by
    apply lt_of_le_of_ne htimeLe
    intro heq
    obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj
    obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
    have hevent : rho.events[j] = rho.events[i] := by
      rw [hje, hie, heq]
    have hidx : j = i :=
      (List.Nodup.getElem_inj_iff
        (NamedScheduleWellFormed.nodup sch)).mp hevent
    exact (Nat.ne_of_lt hji) hidx
  by_contra hnot
  have hle : q' ≤ q := Nat.le_of_not_gt hnot
  have hcontra : Protocol.confirmation_time S.E q' ≤
      Protocol.confirmation_time S.E q := by
    rw [Protocol.confirmation_time_eq_support_cutoff_succ,
      Protocol.confirmation_time_eq_support_cutoff_succ]
    exact support_cutoff_mono S.E (Nat.add_le_add_right hle 1)
  exact (not_lt_of_ge hcontra) htimeLt

private theorem index_lt_strictEventIndex_of_time_lt_noReturn
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {t : Time} {i : Nat} {e : Event V}
    (hi : rho.events[i]? = some e) (ht : e.time < t) :
    i < strictEventIndex rho t := by
  have hfilt : rho.events.filter (fun x => decide (x.time < t)) =
      rho.events.take (strictEventIndex rho t) := by
    simpa only [strictEventIndex] using
      Proofs.Optimistic.filter_eq_take S sch _ (Proofs.Optimistic.downward_lt t)
  have hmemF : e ∈ rho.events.filter (fun x => decide (x.time < t)) :=
    List.mem_filter.mpr ⟨List.mem_of_getElem? hi, by simpa using ht⟩
  rw [hfilt] at hmemF
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmemF
  obtain ⟨hjlen, hjget⟩ := List.getElem?_eq_some_iff.mp hj
  have hjn : j < strictEventIndex rho t := by
    have h := hjlen
    rw [List.length_take] at h
    exact lt_of_lt_of_le h (Nat.min_le_left _ _)
  have hj' : rho.events[j]? = some e := by
    rw [← List.getElem?_take_of_lt hjn]
    exact hj
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj'
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  have hji : j = i :=
    (List.Nodup.getElem_inj_iff
      (NamedScheduleWellFormed.nodup sch)).mp (hje.trans hie.symm)
  rw [← hji]
  exact hjn

private theorem postDeadlineStableRoot_prefix_after_noReturn
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {v : V} (hv : v ∈ rho.honest)
    {j : Nat} {q : Slot} {X : Block V}
    (hX : StableRecord.StableRootAt S rho v j X)
    (hj : rho.events[j]? = some
      (.tick v (Protocol.confirmation_time S.E q)))
    (hqpost : S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) <
      Protocol.confirmation_time S.E q)
    (hqround : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤
      S.hc.round_of (q + 1))
    {n : Nat} (hjn : j + 1 ≤ n)
    (hbase : Block.Preceq X
      (rho.stateBefore S (j + 1) v).st.core.latest_stable) :
    Block.Preceq X
      (rho.stateBefore S n v).st.core.latest_stable := by
  apply latestStable_preserves_prefix_of_compatible_roots_noReturn
    S rho v hjn hbase
  intro i G hji hin hG
  have hGdata := hG
  obtain ⟨time, hi, hpos, hcut, hframe⟩ := hGdata
  let q' := S.E.slotOf time - 1
  have hsucc : q' + 1 = S.E.slotOf time :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hpos)
  have htime : time = Protocol.confirmation_time S.E q' := by
    calc
      time = Protocol.support_cutoff S.E (S.E.slotOf time) := hcut
      _ = Protocol.support_cutoff S.E (q' + 1) := by rw [hsucc]
      _ = Protocol.confirmation_time S.E q' :=
        (Protocol.confirmation_time_eq_support_cutoff_succ S.E q').symm
  have hi' : rho.events[i]? = some
      (.tick v (Protocol.confirmation_time S.E q')) := by
    simpa only [htime] using hi
  have hjlt : j < i := (Nat.lt_succ_self j).trans_le hji
  have hslots : q < q' := confirmationSlot_lt_of_later_tick_noReturn
    S adm.toNamedScheduleWellFormed hj hi' hjlt
  have hround' : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤
      S.hc.round_of (q' + 1) := by
    apply hqround.trans
    unfold Protocol.HealConfig.round_of
    exact Nat.div_le_div_right
      (Nat.succ_le_succ (Nat.le_of_lt hslots))
  exact postDeadlineStableRoots_compatible
    S adm hcom hbelow hrec hdelay hpost hv hX hj hG hi' hslots
      hqpost hqround hround'

/-- A stable root with a run-block witness at or below the deadline cap cannot
be the stable record at the later post-recovery carrier read. -/
theorem capBoundedStableRoot_not_retained_at_postRecoveryCarrier
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {m : Round}
    (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra +
        2 * progressLag' gap delayExtra +
        max (1 + S.hc.η_SG) (gap + 3) ≤ m)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot m) ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) {i : Nat} {R : Block V}
    (hi : i < inclusiveEventIndex rho
      (S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2)))
    (hroot : StableRecord.StableRootAt S rho v i R)
    (hcap : ∃ Rn : NamedBlock V, Rn.erase = R ∧ RunBlock S rho Rn ∧
      (Protocol.derive_named S.E S.cfg Rn).h ≤
        honestHMaxAt S rho
          (S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra))) :
    (confirmationInputRead S rho v
      (S.hc.opening_slot m)).st.core.latest_stable ≠ R := by
  classical
  let D := fgSafetyProgressDeadline S rho rGST gap delayExtra
  let start := S.hc.opening_slot m
  let t := Protocol.confirmation_time S.E start
  let n := strictEventIndex rho t
  obtain ⟨q, hqlo, hqhi, hqm, hhigh⟩ :=
    exists_highOpeningStableWrite_before_postRecoveryCarrier
      S adm hcom hbelow hrec hdelay hpost hm hhor
  obtain ⟨G, Gn, hG, hGnErase, hGnRun, hGheight⟩ := hhigh v hv
  let d := S.hc.opening_slot (q + 1)
  let th := S.a (q + 1)
  have hconf : Protocol.confirmation_time S.E d = th := by
    simpa only [d, th] using opening_confirmation_time_eq_action S (q + 1)
  have hmAction : S.a m ≤ rho.horizon := by
    simpa only [opening_confirmation_time_eq_action] using hhor
  have hthHor : th ≤ rho.horizon := by
    exact (Assembly.a_mono S (Nat.le_of_lt hqm)).trans hmAction
  obtain ⟨j, hjAction⟩ := List.mem_iff_getElem?.mp
    (adm.toNamedScheduleWellFormed.tick_total v hv th
      (Proofs.HealingLemmas.publicTime_a S (q + 1))
      (Proofs.HealingLemmas.a_nonneg S (q + 1)) hthHor)
  have hj : rho.events[j]? = some
      (Event.tick v (Protocol.confirmation_time S.E d)) := by
    simpa only [hconf] using hjAction
  have hslotPos : 0 < S.E.slotOf th := by
    rw [← hconf, Proofs.Optimistic.slotOf_confirmation_time]
    exact Nat.succ_pos d
  have hcut : th = Protocol.support_cutoff S.E (S.E.slotOf th) := by
    rw [← hconf, Proofs.Optimistic.slotOf_confirmation_time,
      Protocol.confirmation_time_eq_support_cutoff_succ]
  have hstateTick : rho.stateBefore S j v = rho.stateBeforeTime S th v :=
    Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
      S adm.toNamedScheduleWellFormed hjAction
  have hframeAt : DecoupledConsensusModel.Protocol.frameStableRoot
      (NamedActionReads.confirmationReadAt S rho v th).cache S.E S.hc
      (NamedActionReads.confirmationReadAt S rho v th).st.core.toHealing
      (S.hc.round_of (S.E.slotOf th)) = some G := by
    simpa only [d, hconf] using hG
  have hrootG : StableRecord.StableRootAt S rho v j G := by
    refine ⟨th, hjAction, hslotPos, hcut, ?_⟩
    rw [hstateTick]
    simpa only [NamedActionReads.confirmationReadAt] using hframeAt
  obtain ⟨-, hstableTick⟩ :=
    ConfirmationOrigin.stateBefore_succ_of_confirmation_tick
      S rho v j hjAction hslotPos hcut
  have hstable' : (rho.stateBefore S (j + 1) v).st.latest_stable =
      (Protocol.NamedDuties.update_confirmation_with
        (NamedProfile.gradeContract (confirmationInputRead S rho v d).cache)
        S.E S.hc (confirmationInputRead S rho v d).st d).latest_stable := by
    rw [hstateTick, ← hconf] at hstableTick
    simpa only [confirmationInputRead, NamedActionReads.confirmationReadAt,
      Proofs.Optimistic.slotOf_confirmation_time, Nat.add_sub_cancel] using hstableTick
  have hupdate :
      (Protocol.NamedDuties.update_confirmation_with
        (NamedProfile.gradeContract (confirmationInputRead S rho v d).cache)
        S.E S.hc (confirmationInputRead S rho v d).st d).latest_stable =
        Protocol.advance_confirmed
          (confirmationInputRead S rho v d).st.core.latest_stable G := by
    rw [StableRecord.update_confirmation_latest_stable]
    change (match DecoupledConsensusModel.Protocol.frameStableRoot
        (confirmationInputRead S rho v d).cache S.E S.hc
        (confirmationInputRead S rho v d).st.core.toHealing
        (S.hc.round_of (confirmationInputRead S rho v d).st.core.s) with
      | some Q => Protocol.advance_confirmed
          (confirmationInputRead S rho v d).st.core.latest_stable Q
      | none => (confirmationInputRead S rho v d).st.core.latest_stable) = _
    rw [show DecoupledConsensusModel.Protocol.frameStableRoot
        (confirmationInputRead S rho v d).cache S.E S.hc
        (confirmationInputRead S rho v d).st.core.toHealing
        (S.hc.round_of (confirmationInputRead S rho v d).st.core.s) = some G by
      simpa only [confirmationInputRead, NamedActionReads.confirmationReadAt,
        Protocol.NamedStore.setClock, hconf] using hframeAt]
  have hafter : (rho.stateBefore S (j + 1) v).st.latest_stable =
      Protocol.advance_confirmed
        (confirmationInputRead S rho v d).st.core.latest_stable G :=
    hstable'.trans hupdate
  have hbase : Block.Preceq G
      (rho.stateBefore S (j + 1) v).st.core.latest_stable := by
    change Block.Preceq G (rho.stateBefore S (j + 1) v).st.latest_stable
    rw [hafter]
    exact Proofs.ConfirmationPolicy.candidate_preceq_advance _ _
  have htht : th < t := by
    dsimp only [th, t, start]
    rw [opening_confirmation_time_eq_action]
    exact (FrameForward.a_lt_opening_succ S (q + 1)).trans_le
      ((NamedOutageClosure.incl_opening_le_a S (q + 2)).trans
        (Assembly.a_mono S (Nat.succ_le_iff.mpr hqm)))
  have hjn : j + 1 ≤ n := by
    apply Nat.succ_le_iff.mpr
    exact index_lt_strictEventIndex_of_time_lt_noReturn
      S adm.toNamedScheduleWellFormed hjAction htht
  have hqD : D + 1 ≤ q := by
    exact (Nat.add_le_add_right
      (Nat.le_add_right D (2 * progressLag' gap delayExtra)) 1).trans
        (by simpa only [D] using hqlo)
  have hqPost : S.a D < Protocol.confirmation_time S.E d := by
    rw [hconf]
    exact (FrameForward.a_lt_opening_succ S D).trans_le
      ((NamedOutageClosure.incl_opening_le_a S (D + 1)).trans
        (Assembly.a_mono S (hqD.trans (Nat.le_succ q))))
  have hqRound : D + 2 ≤ S.hc.round_of (d + 1) := by
    have hround : S.hc.round_of d = q + 1 := by
      dsimp only [d]
      simp only [Protocol.HealConfig.round_of, Protocol.HealConfig.opening_slot]
      have hRpos : 0 < S.hc.R := Nat.zero_lt_of_lt S.hc.R_ge_two
      simpa only [Nat.mul_comm] using Nat.mul_div_cancel_left (q + 1) hRpos
    have hmono : S.hc.round_of d ≤ S.hc.round_of (d + 1) := by
      unfold Protocol.HealConfig.round_of
      exact Nat.div_le_div_right (Nat.le_succ d)
    rw [hround] at hmono
    exact (Nat.succ_le_succ hqD).trans hmono
  have hprefix : Block.Preceq G
      (rho.stateBefore S n v).st.core.latest_stable :=
    postDeadlineStableRoot_prefix_after_noReturn
      S adm hcom hbelow hrec hdelay hpost hv hrootG hj hqPost hqRound hjn hbase
  have hreadState : NamedRun.stateBeforeTime S rho t v =
      rho.stateBefore S n v := by
    simpa only [n] using congrFun
      (stateBeforeTime_eq_stateBefore_strictEventIndex
        S adm.toNamedScheduleWellFormed t) v
  have hcurrent : (confirmationInputRead S rho v start).st.core.latest_stable =
      (rho.stateBefore S n v).st.core.latest_stable := by
    unfold confirmationInputRead NamedActionReads.confirmationReadAt
      NamedActionReads.confirmationReadFrom
    rw [hreadState]
    rfl
  intro hretained
  have hGR : Block.Preceq G R := by
    rw [hcurrent] at hretained
    exact hretained ▸ hprefix
  obtain ⟨Rn, hRnErase, hRnRun, hRnHeight⟩ := hcap
  have hnamed : NamedBlock.Preceq Gn Rn :=
    Protocol.namedPreceq_of_runBlock_erase_preceq
      adm hGnRun hRnRun (by simpa only [hGnErase, hRnErase] using hGR)
  have hmono := Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hnamed
  exact (Nat.not_lt_of_ge (hmono.trans hRnHeight)) hGheight

#print axioms capBoundedStableRoot_not_retained_at_postRecoveryCarrier

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
