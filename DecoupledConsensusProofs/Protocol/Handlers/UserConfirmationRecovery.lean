module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.BlockAdmission
public import DecoupledConsensusProofs.Protocol.Handlers.ConfirmationPolicy
public import DecoupledConsensusProofs.Execution.UserConfirmationHistory
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Adoption
public import DecoupledConsensusProofs.Generic.SlotFreshness
public import DecoupledConsensusProofs.Execution.UserConfirmationFreshness
public import DecoupledConsensusProofs.Protocol.Grades.ProposalLifecycleCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.ProposalCore
public import DecoupledConsensusProofs.Generic.CanonicalSuffix
public import DecoupledConsensusProofs.Execution.Wire

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Exact user-record refresh at a genuine proposal duty

The proof keeps the earlier proof scope. The confirmation write uses the prepared
named read, while the public record statements carry the head-extension premise
and the horizon bounds needed by the original route.
-/
namespace DecoupledConsensusModel
namespace Proofs
namespace UserConfirmationFreshness

open Internal Execution Protocol Proofs.Optimistic Internal.NamedRecoveryRead
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The prepared confirmation write -/

private theorem update_confirmation_with_latest_confirmed_of_eligible
    (contract : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.Store V) (s : Slot)
    (hfirst : Block.Preceq
      (Protocol.update_confirmation_with contract E hc st s).latest_stable
      (Protocol.advance_confirmed st.latest_confirmed
        (confWalkWith contract E hc st s)))
    (helig : confEligible E st s (confWalkWith contract E hc st s) = true) :
    (Protocol.update_confirmation_with contract E hc st s).latest_confirmed =
      Protocol.advance_confirmed st.latest_confirmed (confWalkWith contract E hc st s) := by
  have hval : (Protocol.update_confirmation_with contract E hc st s).latest_confirmed =
      Protocol.floor_on_stable
        (Protocol.update_confirmation_with contract E hc st s).latest_stable
        (match contract.confirmationSG with
          | .optional select =>
              if confEligible E st s (confWalkWith contract E hc st s) then
                Protocol.advance_confirmed st.latest_confirmed
                  (confWalkWith contract E hc st s)
              else
                match select E hc st.toHealing s with
                | some candidate => Protocol.advance_confirmed st.latest_confirmed candidate
                | none => st.latest_confirmed)
        st.latest_confirmed := rfl
  cases hmode : contract.confirmationSG with
  | optional select =>
      have hval' := hval
      simp only [hmode, if_pos helig] at hval'
      rw [hval']
      unfold Protocol.floor_on_stable
      have hfirst' : Block.preceq
          (Protocol.update_confirmation_with contract E hc st s).latest_stable
          (Protocol.advance_confirmed st.latest_confirmed
            (confWalkWith contract E hc st s)) = true := hfirst
      rw [if_pos hfirst']

private theorem named_update_latest_mem
    (S : Setup V) (nd : NamedNodeState V) (s : Slot)
    (hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg nd.st) :
    (Protocol.NamedDuties.update_confirmation_with
      (NamedProfile.gradeContract nd.cache) S.E S.hc nd.st s).core.latest_confirmed ∈
      nd.st.core.T := by
  have hmem := Proofs.NamedConfirmationMembership.confirmed_update nd.cache
    S.E S.hc nd.st s hinv.1.2 hinv.2
  exact hmem.2.1

private theorem confirmation_read_invariant
    (S : Setup V) (before : NamedNodeState V) (t : Time)
    (hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg before.st) :
    Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (NamedActionReads.confirmationReadFrom S before t).st := by
  exact Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg before.st t hinv

private theorem confirmation_time_mono_local (E : Env V) {a b : Slot} (h : a ≤ b) :
    Protocol.confirmation_time E a ≤ Protocol.confirmation_time E b := by
  simpa only [Protocol.confirmation_time, Protocol.proposal_time] using
    Int.add_le_add_right (proposal_time_mono E h) (6 * E.Δ)

private theorem support_cutoff_le_proposal_time_succ_local
    (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s ≤ Protocol.proposal_time E (s + 1) := by
  have hstep : Protocol.proposal_time E (s + 1) =
      Protocol.support_cutoff E s + 2 * E.Δ := by
    unfold Protocol.support_cutoff Protocol.proposal_time Env.t slotStart
    push_cast
    ring
  rw [hstep]
  exact le_add_of_nonneg_right
    (Int.mul_nonneg (by norm_num) (le_of_lt E.Δ_pos))

private theorem latest_slot_le_prefix_no_heads
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (v : V) (s : Slot) :
    ∀ n : Nat,
      (∀ i e, i < n → rho.events[i]? = some e →
        e.time < Protocol.confirmation_time S.E s) →
      (rho.stateBefore S n v).st.latest_confirmed.slot ≤ s := by
  intro n
  induction n with
  | zero =>
      intro _
      exact Nat.zero_le s
  | succ n ih =>
      intro hprefix
      unfold Run.stateBefore NamedRun.stateBefore
      rw [List.take_add_one, List.foldl_append]
      cases hn : rho.events[n]? with
      | none =>
          simpa using ih (fun i e hi he =>
            hprefix i e (Nat.lt_succ_of_lt hi) he)
      | some e =>
          simp only [Option.toList_some, List.foldl_cons, List.foldl_nil]
          cases e with
          | deliver u o t =>
              by_cases hu : u = v
              · subst u
                simp only [NamedWorld.step, Function.update_self, node_process_latest]
                exact ih (fun i e hi he =>
                  hprefix i e (Nat.lt_succ_of_lt hi) he)
              · simp only [NamedWorld.step, Function.update_of_ne (Ne.symm hu)]
                exact ih (fun i e hi he =>
                  hprefix i e (Nat.lt_succ_of_lt hi) he)

          | tick u t =>
              by_cases hu : u = v
              · subst u
                simp only [NamedWorld.step, Function.update_self]
                change (on_tick_emit S v (rho.stateBefore S n v) t).1.st.latest_confirmed.slot ≤ s
                by_cases hbranch :
                    0 < S.E.slotOf t ∧
                      t = Protocol.support_cutoff S.E (S.E.slotOf t)
                · obtain ⟨hpos, ht⟩ := hbranch
                  have hout := on_tick_emit_confirmation_latest S v
                    (rho.stateBefore S n v) (S.E.slotOf t) hpos
                  rw [← ht] at hout
                  rw [hout]
                  set nd := NamedActionReads.confirmationReadFrom S
                    (rho.stateBefore S n v) t with hnd
                  have hreadInv := confirmation_read_invariant S
                    (rho.stateBefore S n v) t
                    (Proofs.NamedRuntime.stateBefore_invariants S rho n v).1
                  have hmem := named_update_latest_mem S nd
                    (S.E.slotOf t - 1) (by simpa only [hnd] using hreadInv)
                  have hstate : rho.stateBefore S n v =
                      rho.stateBeforeTime S t v :=
                    Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
                      S adm.toNamedScheduleWellFormed hn
                  have hmemTime :
                      (Protocol.NamedDuties.update_confirmation_with
                        (NamedProfile.gradeContract nd.cache) S.E S.hc nd.st
                        (S.E.slotOf t - 1)).core.latest_confirmed ∈
                        (rho.storeBeforeTime S v t).T := by
                    show (Protocol.NamedDuties.update_confirmation_with
                        (NamedProfile.gradeContract nd.cache) S.E S.hc nd.st
                        (S.E.slotOf t - 1)).core.latest_confirmed ∈
                        (rho.stateBeforeTime S t v).st.core.T
                    rw [← hstate]
                    simpa only [nd, NamedActionReads.confirmationReadFrom] using hmem
                  have hslotlt := block_slot_lt_of_mem_beforeTime_of_le_proposal
                    S adm (s := S.E.slotOf t + 1) (t := t) (Nat.succ_pos _)
                    (by
                      calc
                        t = Protocol.support_cutoff S.E (S.E.slotOf t) := ht
                        _ ≤ Protocol.proposal_time S.E (S.E.slotOf t + 1) :=
                          support_cutoff_le_proposal_time_succ_local S.E
                            (S.E.slotOf t))
                    hmemTime
                  have htimeConf :
                      Protocol.confirmation_time S.E (S.E.slotOf t - 1) <
                        Protocol.confirmation_time S.E s := by
                    rw [Protocol.confirmation_time_eq_support_cutoff_succ]
                    rw [show S.E.slotOf t - 1 + 1 = S.E.slotOf t from
                      Nat.succ_pred_eq_of_pos hpos]
                    have hp := hprefix n _ (Nat.lt_succ_self n) hn
                    change t < Protocol.confirmation_time S.E s at hp
                    rw [ht] at hp
                    exact hp
                  have hksub : S.E.slotOf t - 1 < s := by
                    by_contra hnot
                    have hle : s ≤ S.E.slotOf t - 1 := Nat.le_of_not_gt hnot
                    have hmono := confirmation_time_mono_local S.E hle
                    exact (not_lt_of_ge hmono) htimeConf
                  have hks' := Nat.succ_le_of_lt hksub
                  have hks : S.E.slotOf t ≤ s := by
                    simpa only [Nat.succ_eq_add_one,
                      Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
                        (Nat.ne_of_gt hpos))] using hks'
                  exact (Nat.le_of_lt_succ hslotlt).trans hks
                · rw [on_tick_emit_latest_of_ne S v
                    (rho.stateBefore S n v) t hbranch]
                  exact ih (fun i e hi he =>
                    hprefix i e (Nat.lt_succ_of_lt hi) he)
              · simp only [NamedWorld.step, Function.update_of_ne (Ne.symm hu)]
                exact ih (fun i e hi he =>
                  hprefix i e (Nat.lt_succ_of_lt hi) he)

private theorem latest_slot_le_before_confirmation_no_heads
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (v : V) (s : Slot) :
    (rho.storeBeforeTime S v (Protocol.confirmation_time S.E s)).latest_confirmed.slot ≤ s := by
  obtain ⟨n, hn, hbefore⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed (Protocol.confirmation_time S.E s)
  have hslot := latest_slot_le_prefix_no_heads S adm v s n
  have hslot' := hslot (fun i e hi he => hbefore i e hi he)
  simpa only [Run.storeBeforeTime, hn] using hslot'

theorem _root_.DecoupledConsensusModel.Proofs.ConfirmationOrigin.advance_confirmed_eq_of_read_slot_le
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (v : V) (s : Slot) {candidate : Block V} (hslot : s ≤ candidate.slot) :
    Protocol.advance_confirmed
      (rho.storeBeforeTime S v (Protocol.confirmation_time S.E s)).latest_confirmed
      candidate = candidate := by
  have hold :
      (rho.storeBeforeTime S v (Protocol.confirmation_time S.E s)).latest_confirmed ∈
        (rho.storeBeforeTime S v (Protocol.confirmation_time S.E s)).T := by
    simpa only [Run.storeBeforeTime] using
      Proofs.NamedStoreBridge.latestConfirmed_mem_stateBeforeTime S rho
        (Protocol.confirmation_time S.E s) v
  have hslotOld := latest_slot_le_before_confirmation_no_heads S adm v s
  exact advance_eq_candidate_of_held_slot S adm hold (hslotOld.trans hslot)

/-! ## Exact update at a genuine duty -/

theorem update_confirmation_latest_eq_of_duty
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {t₀ : Time} (hheads : Internal.HonestHeadExtendsStableFrom S rho t₀)
    (hcom : HonestCommittees S rho.honest) {s : Slot} {B : NamedBlock V}
    (hduty : CanonicalProposalDutyAt S rho s B) (hslot : s ≤ B.slot)
    (ht₀ : t₀ ≤ Protocol.confirmation_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) :
    (Protocol.update_confirmation_with
      (NamedProfile.gradeContract (confirmationInputRead S rho v s).cache)
      S.E S.hc (Proofs.Optimistic.confStore S rho v s) s).latest_confirmed = B.erase := by
  let contract := NamedProfile.gradeContract (confirmationInputRead S rho v s).cache
  let st := Proofs.Optimistic.confStore S rho v s
  have hG := genuineConfirmation_of_dutyExecution S hcom hduty hv
  have hlc := update_confirmation_with_live_confirmed contract S.E S.hc st s
  rw [if_pos hG.genuine] at hlc
  have hwalk : confWalkWith contract S.E S.hc st s = B.erase := by
    exact hlc.symm.trans hG.selected
  have hfirst : Block.Preceq
      (Protocol.update_confirmation_with contract S.E S.hc st s).latest_stable
      (Protocol.advance_confirmed st.latest_confirmed
        (confWalkWith contract S.E S.hc st s)) := by
    change Block.Preceq
      (confirmationStableWrite S (confirmationInputRead S rho v s))
      (Protocol.advance_confirmed
        (confirmationInputRead S rho v s).st.core.latest_confirmed
        (namedConfirmationWalk S (confirmationInputRead S rho v s) s))
    exact hheads v hv s ht₀ hhor
  have hlatest := update_confirmation_with_latest_confirmed_of_eligible
    contract S.E S.hc st s hfirst hG.genuine
  rw [hwalk] at hlatest
  rw [hlatest]
  have hadvance :=
    _root_.DecoupledConsensusModel.Proofs.ConfirmationOrigin.advance_confirmed_eq_of_read_slot_le
      S adm v s
    (candidate := B.erase) (by rw [Proofs.NamedWire.erase_slot]; exact hslot)
  simpa only [st, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using hadvance

/-! ## Store-level and proposal-level consequences -/

theorem latest_eq_of_duty
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {t₀ : Time} (hheads : Internal.HonestHeadExtendsStableFrom S rho t₀)
    (hcom : HonestCommittees S rho.honest) {s : Slot} {B : NamedBlock V}
    (hduty : CanonicalProposalDutyAt S rho s B) (hslot : s ≤ B.slot)
    (ht₀ : t₀ ≤ Protocol.confirmation_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) :
    (rho.storeAt S v (Protocol.confirmation_time S.E s)).latest_confirmed = B.erase := by
  rw [latest_confirmed_eq_update S adm.toNamedScheduleWellFormed hv s hhor]
  exact update_confirmation_latest_eq_of_duty S adm hheads hcom hduty hslot ht₀ hhor hv

theorem latest_eq_proposedBlock_of_duty
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {t₀ : Time} (hheads : Internal.HonestHeadExtendsStableFrom S rho t₀)
    (hcom : HonestCommittees S rho.honest) {s : Slot} {B : NamedBlock V}
    (hB : Statements.Instantiation.proposedBlockAt S rho s = some B)
    (hduty : CanonicalProposalDutyAt S rho s B)
    (ht₀ : t₀ ≤ Protocol.confirmation_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) :
    (rho.storeAt S v (Protocol.confirmation_time S.E s)).latest_confirmed = B.erase :=
  latest_eq_of_duty S adm hheads hcom hduty
    (by rw [DecoupledConsensusModel.Proofs.Optimistic.proposedBlockAt_slot S rho s hB]) ht₀ hhor hv







end UserConfirmationFreshness
end Proofs
end DecoupledConsensusModel

end
