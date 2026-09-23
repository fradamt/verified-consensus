module
public import DecoupledConsensusProofs.Bridge.StandardVocabulary
public import DecoupledConsensusProofs.Bridge.GenericVocabulary
public import DecoupledConsensusProofs.Bridge.GenericExecution
public import DecoupledConsensusProofs.Bridge.GenericRegimes
public import DecoupledConsensusProofs.Execution.StoreFinalityRun

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

namespace DecoupledConsensusModel
namespace Proofs

open Internal Execution Statements
open Statements.Generic

variable {V : Type} [DecidableEq V] [Fintype V]


private theorem stateAt_eq_stateBefore_le_finalizedLive (S : Setup V)
    {rho : Run V} (sch : NamedScheduleWellFormed S rho) (t : Time) :
    ∃ n : Nat, Run.stateAt S rho t = rho.stateBefore S n ∧
      ∀ (j : Nat) (e : Event V), j < n → rho.events[j]? = some e → e.time ≤ t :=
  (Proofs.Bridges.filtered_fold_eq_stateBefore S sch
    (p := fun e => decide (e.time ≤ t))
    (fun e f hk hf => by
      simp only [decide_eq_true_eq] at hf ⊢
      exact le_trans (Proofs.Bridges.time_le_of_key_le hk) hf)).imp fun _ h =>
    ⟨h.1, fun j e hj hget => by simpa using h.2 j e hj hget⟩

private theorem proposal_time_le_of_acceptsAt_block_finalizedLive
    (S : Setup V) {rho : Run V} (sch : NamedScheduleWellFormed S rho)
    {i : Nat} {v : V} {B : NamedBlock V} {t : Time}
    (hacc : NamedRun.acceptsAt S rho i v (.block B) t) :
  Protocol.proposal_time S.E B.erase.slot ≤ t := by
  have hacc' := hacc
  obtain ⟨hhandle, hpre, hpost⟩ := hacc
  obtain ⟨hindex, e, he, hnode, htime⟩ := hhandle
  simp only [NamedRun.actualHandlesAtIndex, NamedRun.processesAtIndex] at hindex
  rcases hindex with htick | hdeliver
  · obtain ⟨t', htick, hem⟩ := htick
    have hemit : NamedRun.emits S rho v (.block B) t' := ⟨i, htick, hem⟩
    have hshape := Proofs.HealingSurface.emits_block_shape S rho hemit
    have ht' : t' = t := by
      have heq : Event.tick v t' = e := Option.some.inj (htick.symm.trans he)
      simpa [Event.time] using (congrArg Event.time heq).trans htime
    rw [Proofs.NamedWire.erase_slot]
    exact (hshape.2.1.symm.trans ht').le
  · obtain ⟨t', hdeliver⟩ := hdeliver
    have heq : Event.deliver v (.block B) t' = e :=
      Option.some.inj (hdeliver.symm.trans he)
    have ht' : t' = t := (congrArg Event.time heq).trans htime
    subst t'
    have heDeliver : rho.events[i]? = some (Event.deliver v (.block B) t) := by
      simpa [heq] using he
    have hfuture := (Protocol.delivery_guards_of_acceptsAt_block
      S hacc' heDeliver).1
    have hclock := Proofs.NamedRuntime.stateBefore_clock_le_event S rho sch.sorted
      heDeliver (sch.in_horizon _ (List.mem_of_getElem? heDeliver)).1 v
    have hnonneg : 0 ≤
        (NamedRun.stateBefore S rho i v).st.core.t := by
      exact Proofs.NamedRuntime.stateBefore_clock_mono S rho sch.sorted
        (fun e he => (sch.in_horizon e he).1) v (Nat.zero_le i)
    have hslot := Proofs.NamedStoreBridge.slotOfClock_stateBefore S rho i v
    unfold Proofs.Optimistic.SlotOfClock at hslot
    have hslotle : B.erase.slot ≤
        S.E.slotOf (NamedRun.stateBefore S rho i v).st.core.t := by
      rw [← hslot]
      exact Nat.le_of_not_gt hfuture
    exact (Protocol.proposal_time_mono S.E hslotle).trans
      ((Protocol.proposal_time_slotOf_le S.E hnonneg).trans hclock)

private theorem block_slot_lt_of_mem_storeAt_finalizedLive
    (S : Setup V) {rho : Run V} (sch : NamedScheduleWellFormed S rho)
    {v : V} {s : Slot} {t : Time} (ht : t < Protocol.proposal_time S.E s)
    {C : Block V} (hC : C ∈ (rho.storeAt S v t).core.T)
    (hCgen : C ≠ Block.genesis) : C.slot < s := by
  obtain ⟨n, hn, hbefore⟩ := stateAt_eq_stateBefore_le_finalizedLive S sch t
  have hCn : C ∈ (rho.stateBefore S n v).st.core.T := by
    have hnv : NamedRun.readAt S rho t v = rho.stateBefore S n v := congrFun hn v
    have hC' : C ∈ (NamedRun.readAt S rho t v).st.core.T := hC
    rwa [hnv] at hC'
  obtain ⟨D, hD, hDe⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n v hCn
  have hprocessed : Object.processed (rho.stateBefore S n v).st (.block D) = true := by
    simp only [NamedReceipt.processed, decide_eq_true_eq]
    exact hD
  rcases Protocol.acceptsAt_block_of_processed S rho v n D hprocessed with
    hgen | hacc
  · subst D
    simp only [NamedBlock.erase] at hDe
    subst C
    exact False.elim (hCgen rfl)
  · obtain ⟨i, hin, atime, haccepts⟩ := hacc
    obtain ⟨-, e, he, -, het⟩ := haccepts.1
    have hatime : atime < Protocol.proposal_time S.E s := by
      rw [← het]
      exact lt_of_le_of_lt (hbefore i e hin he) ht
    by_contra hnot
    have hsC : s ≤ D.erase.slot := by
      rw [hDe]
      exact Nat.le_of_not_gt hnot
    exact (not_lt_of_ge ((Protocol.proposal_time_mono S.E hsC).trans
      (proposal_time_le_of_acceptsAt_block_finalizedLive S sch haccepts))) hatime

private theorem named_proposal_of_generic
    (S : Setup V) {rho : Run V} {s : Slot} {B : Block V}
    (h : Generic.HonestProposalAt (I S) rho s B) :
    ∃ D : NamedBlock V, Internal.HonestProposalAt (Statements.«instance» S) rho s D ∧
      D.erase = B := by
  rcases h with ⟨hp, hB⟩
  change S.E.proposer s ∈ rho.honest at hp
  change (Statements.Instantiation.proposedBlockAt S rho s).map NamedBlock.erase = some B at hB
  cases hnamed : Statements.Instantiation.proposedBlockAt S rho s with
  | none => simp [hnamed] at hB
  | some D =>
      simp [hnamed] at hB
      exact ⟨D, ⟨hp, hnamed⟩, hB⟩

private theorem noFutureRead_of_store_mem
    (S : Setup V) {rho : Run V}
    (sch : NamedScheduleWellFormed S rho) (g : Generic.Output (P S))
    (hmem : ∀ v t, Generic.readAt (P S) rho g v t ∈
      (rho.storeAt S v t).core.T) :
    Generic.NoFutureRead (P S) (I S) rho g := by
  intro v hv t s B hproposal hafter
  intro hprec
  obtain ⟨D, hD, hDB⟩ := named_proposal_of_generic S hproposal
  obtain ⟨_, hnamed⟩ := hD
  have hDgen : D ≠ NamedBlock.genesis := by
    intro hgen
    subst D
    have hp := DecoupledConsensusModel.Proofs.HealingSurface.proposedBlockAt_proposer S rho s hnamed
    change none = some (S.E.proposer s) at hp
    cases hp
  have hBgen : B ≠ Block.genesis := by
    intro hgen
    have hDB' := hDB
    rw [hgen] at hDB'
    cases D with
    | genesis => exact hDgen rfl
    | node p slot root votes support rows proposer => cases hDB'
  have hBmem : B ∈ (rho.storeAt S v t).core.T := by
    apply Proofs.Records.mem_of_preceq
      ((parentClosed_iff _).mp (Proofs.NamedStoreBridge.parentClosed_readAt S rho t v)).2
      B (Generic.readAt (P S) rho g v t) (hmem v t)
    exact hprec
  have hslotlt := block_slot_lt_of_mem_storeAt_finalizedLive S sch hafter hBmem hBgen
  have hDslot : D.slot = s := DecoupledConsensusModel.Proofs.Optimistic.proposedBlockAt_slot S rho s hnamed
  have hBslot : B.slot = s := by
    rw [← hDB, Proofs.NamedWire.erase_slot, hDslot]
  exact (Nat.ne_of_lt (hslotlt.trans_eq hBslot.symm)) rfl

private theorem confirmed_read_mem_storeAt (S : Setup V) (rho : Run V)
    (v : V) (t : Time) :
    Generic.readAt (P S) rho (I S).confirmed v t ∈
      (rho.storeAt S v t).core.T := by
  change Generic.readAt (P S) rho
      (fun n => Protocol.get_confirmed n.st.core) v t ∈
    (rho.storeAt S v t).core.T
  rw [readAt_eq S rho (fun st => Protocol.get_confirmed st) v t]
  simpa [Internal.readAt] using
    (show Internal.confirmedOutputAt S rho v t ∈ (rho.storeAt S v t).core.T from by
      have hinv := Proofs.NamedRuntime.readAt_invariants S rho t v
      have hF := hinv.1.1.2.1
      have hL := hinv.1.2.2.1
      have hS := hinv.1.2.2.2
      unfold Internal.confirmedOutputAt Protocol.get_confirmed
      split
      · exact hL
      · unfold Protocol.get_stable
        split
        · exact hS
        · exact hF)

private theorem stable_read_mem_storeAt (S : Setup V) (rho : Run V)
    (v : V) (t : Time) :
    Generic.readAt (P S) rho (I S).stable v t ∈
      (rho.storeAt S v t).core.T := by
  change Generic.readAt (P S) rho
      (fun n => Protocol.get_stable n.st.core) v t ∈
    (rho.storeAt S v t).core.T
  rw [readAt_eq S rho (fun st => Protocol.get_stable st) v t]
  simpa [Internal.readAt] using
    (show Internal.stableOutputAt S rho v t ∈ (rho.storeAt S v t).core.T from by
      have hinv := Proofs.NamedRuntime.readAt_invariants S rho t v
      have hF := hinv.1.1.2.1
      have hS := hinv.1.2.2.2
      unfold Internal.stableOutputAt Protocol.get_stable
      split
      · exact hS
      · exact hF)

private theorem finalized_read_mem_storeAt (S : Setup V) (rho : Run V)
    (v : V) (t : Time) :
    Generic.readAt (P S) rho (I S).finalized v t ∈
      (rho.storeAt S v t).core.T := by
  change Generic.readAt (P S) rho (fun n => n.st.core.F) v t ∈
    (rho.storeAt S v t).core.T
  rw [readAt_eq S rho (fun st => st.F) v t]
  simpa [Internal.readAt] using
    Proofs.NamedStoreBridge.finalizedInTree_readAt S rho t v

theorem noFutureRead_confirmed (S : Setup V) :
    ∀ rho, Generic.ExecutionValid (P S) (E S) (I S) rho →
      Generic.NoFutureRead (P S) (I S) rho (I S).confirmed := by
  intro rho hexec
  exact noFutureRead_of_store_mem S
    (executionValid_of_generic S rho hexec).toNamedScheduleWellFormed
    (I S).confirmed (confirmed_read_mem_storeAt S rho)

theorem noFutureRead_stable (S : Setup V) :
    ∀ rho, Generic.ExecutionValid (P S) (E S) (I S) rho →
      Generic.NoFutureRead (P S) (I S) rho (I S).stable := by
  intro rho hexec
  exact noFutureRead_of_store_mem S
    (executionValid_of_generic S rho hexec).toNamedScheduleWellFormed
    (I S).stable (stable_read_mem_storeAt S rho)

theorem noFutureRead_finalized (S : Setup V) :
    ∀ rho, Generic.ExecutionValid (P S) (E S) (I S) rho →
      Generic.NoFutureRead (P S) (I S) rho (I S).finalized := by
  intro rho hexec
  exact noFutureRead_of_store_mem S
    (executionValid_of_generic S rho hexec).toNamedScheduleWellFormed
    (I S).finalized (finalized_read_mem_storeAt S rho)

theorem growth_of_included (S : Setup V) {rho : Run V}
    {g : Generic.Output (P S)} {t₀ D : Time} {gap : Nat}
    (hmono : Generic.MonotoneFrom (P S) rho g t₀)
    (hfuture : Generic.NoFutureRead (P S) (I S) rho g)
    (hincl : Generic.IncludedFrom (P S) (I S) rho g t₀ D)
    (hrec : Generic.StrongMultiProposerRecurrence (I S) (C S) rho (E S).t_GST gap)
    (ht₀ : 0 ≤ t₀) (hgst : (E S).t_GST ≤ t₀) (hD : 0 ≤ D) :
    Generic.LiveFrom (P S) (I S) rho g t₀
      ((gap : Time) * (C S).period + D) := by
  intro t ht hdeadline
  have hperiod : 0 < (C S).period := by
    simpa [C, Statements.Instantiation.constants] using concretePeriod_pos S
  have ht_nonneg : 0 ≤ t := ht₀.trans ht
  obtain ⟨s, hslo, hsupper, hcarrier, _hlookback⟩ := hrec t
    (hgst.trans ht) (by linarith)
  have htwo : 0 < 2 * (C S).period := by positivity
  have hsAfter : t < (I S).proposalTime s :=
    lt_of_lt_of_le (lt_add_of_pos_right t htwo) hslo
  have htincl : t₀ < (I S).proposalTime s := ht.trans_lt hsAfter
  have hpropD : (I S).proposalTime s + D ≤ rho.horizon := by
    calc
      (I S).proposalTime s + D ≤
          t + ((gap : Time) * (C S).period + D) := by
        simpa [add_assoc, add_comm, add_left_comm] using add_le_add_right hsupper D
      _ ≤ rho.horizon := hdeadline
  have hs_honest : (I S).proposer s ∈ rho.honest := by
    have hzero : 0 < (C S).proposerSlots := by
      simp [C, Statements.Instantiation.constants]
    simpa using hcarrier.2 0 hzero
  obtain ⟨B, hBprop, hBin⟩ := hincl s htincl hs_honest hpropD
  have hfinalle : (I S).proposalTime s + D ≤
      t + ((gap : Time) * (C S).period + D) := by
    simpa [add_assoc, add_comm, add_left_comm] using add_le_add_right hsupper D
  have ht0propD : t₀ ≤ (I S).proposalTime s + D := by
    exact (le_of_lt htincl).trans (le_add_of_nonneg_right hD)
  have hBfinal : ∀ v ∈ rho.honest,
      Block.Preceq B
        (Generic.readAt (P S) rho g v
          (t + ((gap : Time) * (C S).period + D))) := by
    intro v hv
    exact Block.preceq_trans (hBin v hv)
      (hmono v hv ((I S).proposalTime s + D)
        (t + ((gap : Time) * (C S).period + D))
        ht0propD hfinalle hdeadline)
  have hdelay : 0 ≤ (gap : Time) * (C S).period + D := by
    exact add_nonneg (mul_nonneg (by positivity) hperiod.le) hD
  have htfinal : t ≤ t + ((gap : Time) * (C S).period + D) :=
    by nlinarith
  refine ⟨B, ?_, ?_, ?_⟩
  · exact ⟨s, hsAfter, hBprop⟩
  · intro v hv
    have hfuture := hfuture v hv t s B hBprop hsAfter
    have hmono_t := hmono v hv t
      (t + ((gap : Time) * (C S).period + D)) ht htfinal hdeadline
    have hcompat := Block.compatible_of_preceq_common hmono_t (hBfinal v hv)
    simp only [Block.compatible, Bool.or_eq_true] at hcompat
    rcases hcompat with hTB | hBT
    · have hneq : Generic.readAt (P S) rho g v t ≠ B := by
        intro heq
        apply hfuture
        rw [heq]
        exact Block.preceq_self _
      simp only [Block.Prec, Block.prec, hneq, decide_false, Bool.not_false,
        Bool.true_and]
      exact hTB
    · exact False.elim (hfuture hBT)
  · intro v hv
    exact hBfinal v hv

private theorem foldl_finalized_mono (S : Setup V) (v : V)
    (events : List (Event V)) (w : World V) :
    Block.Preceq (w v).st.core.F
      ((events.foldl (World.step S) w) v).st.core.F := by
  induction events generalizing w with
  | nil => exact Block.preceq_self _
  | cons e events ih =>
      exact Block.preceq_trans (Protocol.step_F_mono S w e v)
        (ih (w := World.step S w e))

private theorem finalized_readAt_mono_of_sorted (S : Setup V) {rho : Run V}
    (sorted : rho.events.Pairwise (fun e f => NamedEvent.key e ≤ NamedEvent.key f))
    (v : V) {t t' : Time} (htt' : t ≤ t') :
    Block.Preceq (rho.storeAt S v t).F (rho.storeAt S v t').F := by
  have htime : rho.events.Pairwise (fun e f => e.time ≤ f.time) := by
    refine sorted.imp ?_
    intro e f h
    exact Proofs.Bridges.time_le_of_key_le h
  obtain ⟨events, hevents⟩ := Protocol.filter_time_prefix htt'
    rho.events htime
  have hread : NamedRun.readAt S rho t' =
      events.foldl (World.step S) (NamedRun.readAt S rho t) := by
    simp only [NamedRun.readAt]
    rw [← hevents, List.foldl_append]
  simp only [Run.storeAt, hread]
  exact foldl_finalized_mono S v events (NamedRun.readAt S rho t)

theorem accountable_finalizedMonotone (S : Setup V) :
    ∀ rho, Generic.RunWellFormed (E S) (I S) rho →
      Generic.MonotoneFrom (P S) rho (I S).finalized 0 := by
  intro rho hwell
  have hsorted := (finalityExecution_of_generic_runWellFormed S rho hwell).sorted
  intro v hv t t' ht htt' hhor
  change Block.Preceq
    (Generic.readAt (P S) rho (fun n => n.st.core.F) v t)
    (Generic.readAt (P S) rho (fun n => n.st.core.F) v t')
  rw [readAt_eq S rho (fun st => st.F) v t,
    readAt_eq S rho (fun st => st.F) v t']
  exact finalized_readAt_mono_of_sorted S hsorted v htt'

private theorem boundary_minus_a0_identity (S : Setup V) (k : Round) :
    healingBoundaryTime S (k + 1) - S.a 0 =
      4 * S.E.Δ * (S.hc.R * (k + 1) : Nat) + 3 * S.E.Δ := by
  simp only [healingBoundaryTime, Protocol.vote_time, Env.t, slotStart,
    Setup.a, Protocol.HealConfig.a, Protocol.HealConfig.opening_slot]
  push_cast
  ring

private theorem boundary_minus_a0_nonneg (S : Setup V) (k : Round) :
    0 ≤ healingBoundaryTime S (k + 1) - S.a 0 := by
  rw [boundary_minus_a0_identity S k]
  have hR : (0 : Int) ≤ (S.hc.R : Int) := by positivity
  have hΔ : (0 : Int) ≤ S.E.Δ := S.E.Δ_pos.le
  positivity

theorem finalized_growth (S : Setup V) :
    ∀ rho t₀ gap,
      Generic.FinalityRegime (P S) (E S) (I S) (C S) rho t₀ gap →
      t₀ + (C S).finalityStartup gap ≤ rho.horizon →
      Generic.LiveFrom (P S) (I S) rho (I S).finalized
        (t₀ + (C S).finalityStartup gap)
        ((gap : Time) * (C S).period + (C S).finalityDeadline gap) := by
  intro rho t₀ gap hregime hhorizon
  have ht₀ : 0 ≤ t₀ := by
    have hGST : (0 : Time) ≤ (E S).t_GST := (E S).t_GST_nonneg
    exact hGST.trans hregime.gst
  have hstartup : 0 ≤ (C S).finalityStartup gap := by
    simpa [C, Statements.Instantiation.constants] using
      boundary_minus_a0_nonneg S
        (DecoupledConsensusModel.Statements.Instantiation.finalityStartup S gap S.extraRounds)
  have hdeadline : 0 ≤ (C S).finalityDeadline gap := by
    have hb := boundary_minus_a0_nonneg S
      (DecoupledConsensusModel.Statements.Instantiation.finalityDeadline S gap S.extraRounds)
    simpa [C, Statements.Instantiation.constants] using
      (add_nonneg hb (by nlinarith [S.E.Δ_pos]))
  have hperiod : 0 < (C S).period := by
    simpa [C, Statements.Instantiation.constants] using concretePeriod_pos S
  have hstart : 0 ≤ t₀ + (C S).finalityStartup gap :=
    add_nonneg ht₀ hstartup
  have hwell : Generic.RunWellFormed (E S) (I S) rho :=
    { horizon_nonneg := hregime.execution.toScheduleWellFormed.horizon_nonneg
      sorted := hregime.execution.toScheduleWellFormed.sorted
      idealization := hregime.execution.idealization }
  have hmono0 := accountable_finalizedMonotone S rho hwell
  have hmono : Generic.MonotoneFrom (P S) rho (I S).finalized
      (t₀ + (C S).finalityStartup gap) := by
    intro v hv t t' ht htt hhor
    exact hmono0 v hv t t' (le_trans hstart ht) htt hhor
  have hfuture := noFutureRead_finalized S rho hregime.execution
  have hlegacyRegime := finalityRegime_of_generic S rho t₀ gap hregime
  have hlegacyHorizon :
      t₀ + (Statements.ourConstants S).finalityStartup gap S.extraRounds ≤ rho.horizon := by
    simpa [C, Statements.Instantiation.constants, Statements.ourConstants] using hhorizon
  have hlegacyIncluded := finalized_included S rho t₀ gap S.extraRounds
    hlegacyRegime hlegacyHorizon
  have hincl : Generic.IncludedFrom (P S) (I S) rho (I S).finalized
      (t₀ + (C S).finalityStartup gap)
      ((C S).finalityDeadline gap) := by
    simpa [C, Statements.Instantiation.constants, Statements.ourConstants] using
      included_of_named S hlegacyIncluded
  exact growth_of_included S hmono hfuture hincl hregime.recurrence hstart
    (hregime.gst.trans (le_add_of_nonneg_right hstartup)) hdeadline

end Proofs
end DecoupledConsensusModel

#print axioms DecoupledConsensusModel.Proofs.accountable_finalizedMonotone
#print axioms DecoupledConsensusModel.Proofs.noFutureRead_confirmed
#print axioms DecoupledConsensusModel.Proofs.noFutureRead_stable
#print axioms DecoupledConsensusModel.Proofs.noFutureRead_finalized
#print axioms DecoupledConsensusModel.Proofs.growth_of_included
#print axioms DecoupledConsensusModel.Proofs.finalized_growth

end
