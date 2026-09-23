module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Protocol.Schedule.AdoptionTransport
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RoundZero
public import DecoupledConsensusProofs.Objects.Final
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordTargetHistory
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Canonicality
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HonestMajorityCore
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityCertificates
public import DecoupledConsensusProofs.Protocol.Grades.HonestMajority
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGHistory
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.VoteViewValidity
public import DecoupledConsensusProofs.Protocol.ChainState.Main
public import DecoupledConsensusInternal.Execution.Assumptions
public import DecoupledConsensusProofs.Execution.EmissionShape
public import DecoupledConsensusProofs.Protocol.Handlers.SGArrival
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Execution.BodyRetention

@[expose] public section



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution
open Protocol (derive_named)
open Internal.NamedRecoveryRead

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Directed run history -/




/-! Erased endpoint twins for the HWM frame-history route. An endpoint in the
public selection-history statements is an arbitrary `Block`, not necessarily a
retained named body. -/




/-- Every nonempty height gate in an honest attestation emitted before `t` is
no higher than `B`'s named derived chain-state height.

This predicate deliberately covers both target and timeout pairs. A height
crossing certificate can contain either pair, and honest validators can emit a
timeout. Candidate survival needs only the common numerical gate. -/
def PastHonestHeightGatesBelow (S : Setup V) (rho : Run V) (t : Time)
    (B : NamedBlock V) : Prop :=
  ∀ (a : NamedAttestation V) (t' : Time),
    a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (Object.attest a) t' → t' < t →
        ∀ h, a.height_pair.erase.height? = some h →
          h ≤ (derive_named S.E S.cfg B).h
















/-! ## Directed SG history -/
















/-! ## Proposal visibility and the evaluation-store producer -/

/-- Slot proposal times are monotone. -/
theorem proposal_time_mono_local (E : Env V) {s s' : Slot} (h : s ≤ s') :
    Protocol.proposal_time E s ≤ Protocol.proposal_time E s' := by
  unfold Protocol.proposal_time Env.t slotStart
  have hfactor : (0 : Time) ≤ 4 * E.Δ := by
    have hd : (0 : Time) ≤ E.Δ := le_of_lt E.Δ_pos
    exact Int.mul_nonneg (by norm_num) hd
  apply Int.mul_le_mul_of_nonneg_left
  · exact_mod_cast h
  · exact hfactor

/-- If a round action is earlier than a proposal instant, one more network
delay still ends no later than that proposal. Round actions occur two delays
into their containing slot, while proposals occur at slot boundaries. -/
theorem action_add_delta_le_proposal_of_lt
    (S : Setup V) {r : Round} {s : Slot}
    (hlt : S.a r < Protocol.proposal_time S.E s) :
    S.a r + S.E.Δ ≤ Protocol.proposal_time S.E s := by
  let k := S.hc.opening_slot r
  have hprev : Protocol.proposal_time S.E (k + 1) < S.a r := by
    have heq : Protocol.proposal_time S.E (k + 1) + 2 * S.E.Δ = S.a r := by
      unfold Protocol.proposal_time Env.t Setup.a Protocol.HealConfig.a slotStart
      simp only [k, Protocol.HealConfig.opening_slot]
      push_cast
      ring
    calc
      Protocol.proposal_time S.E (k + 1) <
          Protocol.proposal_time S.E (k + 1) + 2 * S.E.Δ :=
        lt_add_of_pos_right _ (Int.mul_pos (by norm_num) S.E.Δ_pos)
      _ = S.a r := heq
  have hslots : k + 2 ≤ s := by
    by_contra hnot
    have hslt : s < k + 2 := Nat.lt_of_not_ge hnot
    have hs : s ≤ k + 1 := Nat.lt_succ_iff.mp (by
      simpa only [Nat.succ_eq_add_one] using hslt)
    have hm := proposal_time_mono_local S.E hs
    have : S.a r < Protocol.proposal_time S.E (k + 1) :=
      lt_of_lt_of_le hlt hm
    exact (not_lt_of_ge (le_of_lt hprev)) this
  have hnext : S.a r + S.E.Δ ≤ Protocol.proposal_time S.E (k + 2) := by
    have heq : S.a r + 2 * S.E.Δ = Protocol.proposal_time S.E (k + 2) := by
      unfold Protocol.proposal_time Env.t Setup.a Protocol.HealConfig.a slotStart
      simp only [k, Protocol.HealConfig.opening_slot]
      push_cast
      ring
    have hd0 : (0 : Time) ≤ S.E.Δ := le_of_lt S.E.Δ_pos
    have hd12 : S.E.Δ ≤ 2 * S.E.Δ := by
      calc
        S.E.Δ = 1 * S.E.Δ := by ring
        _ ≤ 2 * S.E.Δ :=
          Int.mul_le_mul_of_nonneg_right (by norm_num) hd0
    calc
      S.a r + S.E.Δ ≤ S.a r + 2 * S.E.Δ :=
        add_le_add (le_refl _) hd12
      _ = Protocol.proposal_time S.E (k + 2) := heq
  exact le_trans hnext (proposal_time_mono_local S.E hslots)

/-- A round action earlier than a slot proposal belongs to a round no later
than that proposal's round. -/
theorem action_round_le_of_lt_proposal
    (S : Setup V) {r : Round} {s : Slot}
    (hlt : S.a r < Protocol.proposal_time S.E s) :
    r ≤ S.hc.round_of s := by
  let k := S.hc.opening_slot r
  have hprev : Protocol.proposal_time S.E (k + 1) < S.a r := by
    have heq : Protocol.proposal_time S.E (k + 1) + 2 * S.E.Δ = S.a r := by
      unfold Protocol.proposal_time Env.t Setup.a Protocol.HealConfig.a slotStart
      simp only [k, Protocol.HealConfig.opening_slot]
      push_cast
      ring
    calc
      Protocol.proposal_time S.E (k + 1) <
          Protocol.proposal_time S.E (k + 1) + 2 * S.E.Δ :=
        lt_add_of_pos_right _ (Int.mul_pos (by norm_num) S.E.Δ_pos)
      _ = S.a r := heq
  have hslots : k + 1 ≤ s := by
    by_contra hnot
    have hslt : s < k + 1 := Nat.lt_of_not_ge hnot
    have hs : s ≤ k := Nat.lt_succ_iff.mp (by
      simpa only [Nat.succ_eq_add_one] using hslt)
    have hm := proposal_time_mono_local S.E hs
    have hkk : Protocol.proposal_time S.E k < S.a r :=
      lt_of_le_of_lt (proposal_time_mono_local S.E (Nat.le_succ k)) hprev
    have : S.a r < Protocol.proposal_time S.E k :=
      lt_of_lt_of_le hlt hm
    exact (not_lt_of_ge (le_of_lt hkk)) this
  rw [← Proofs.HealingLemmas.round_of_opening_succ S.hc r]
  exact Nat.div_le_div_right hslots

/-- The emitter's own Section 7 tick holds the exact honest row.

Under the named runtime this is immediate: the emitting tick is itself an
actual handler call on the emitted row, and `Proofs.NamedSGArrival.honest_row_after_
call` retains an honest row delivered inside its own window. The retired
erased form needed a separate pool-provenance and one-per-round uniqueness
argument to identify a matching projection with the emitted attestation; a
named row carries its own payload, so no identification step is left. -/
theorem attest_row_of_emission_exact
    (S : Setup V) {rho : Run V} (hadm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {a : NamedAttestation V} {t : Time}
    (hemit : NamedRun.emits S rho v (Object.attest a) t) :
    ∃ i : Nat,
      rho.events[i]? = some (Event.tick v t) ∧
        a ∈ (rho.stateBefore S (i + 1) v).st.sg_rows a.round := by
  obtain ⟨haVal, ht⟩ := Proofs.Optimistic.emits_attest_shape S hemit
  have haHon : a.val_index ∈ rho.honest := by
    rw [haVal]
    exact hv
  have hem' :
      NamedRun.emits S rho a.val_index (Object.attest a) (S.a a.round) := by
    rw [haVal, ← ht]
    exact hemit
  obtain ⟨i, hi, hmem⟩ := hemit
  refine ⟨i, hi, ?_⟩
  have hcall : NamedRun.actualHandlesAt S rho i v (Object.attest a) t :=
    ⟨Or.inl (Or.inl ⟨t, hi, hmem⟩), ⟨Event.tick v t, hi, rfl, rfl⟩⟩
  have hcall' :
      NamedRun.actualHandlesAt S rho i v (Object.attest a) (S.a a.round) := by
    rw [← ht]
    exact hcall
  exact Proofs.NamedSGArrival.honest_row_after_call S rho
    hadm.toNamedAdmissibleCore.toNamedScheduleWellFormed
    hadm.toNamedAdmissibleCore.toNamedUnforgeable haHon hem' hcall'
    (le_refl _) (lt_add_of_pos_right _ S.E.Δ_pos)


/-- An exact attestation present immediately after an event before `t` remains
in the SG pool read immediately before `t`. -/
theorem attest_mem_stateBeforeTime_of_post
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {w : V} {j : Nat} {e : Event V} {t : Time} {k : Round}
    {a : CombinedAttestation V}
    (hj : rho.events[j]? = some e) (hjt : e.time < t)
    (ha : a ∈ (rho.stateBefore S (j + 1) w).st.sg_pool k) :
    a ∈ (rho.stateBeforeTime S t w).st.sg_pool k := by
  let N := (rho.events.filter (fun x => decide (x.time < t))).length
  have hjN : j < N := by
    by_contra hnot
    have htle : t ≤ e.time :=
      Proofs.Optimistic.le_time_of_index_ge S sch (t := t) (j := j) (e := e)
        (by simpa [N] using Nat.le_of_not_gt hnot) hj
    exact (not_le_of_gt hjt) htle
  have hcarry := Proofs.HealingLemmas.stateBefore_sg_pool_subset S rho w k
    (i := j + 1) N (Nat.succ_le_of_lt hjN)
  rw [Proofs.Optimistic.stateBeforeTime_eq_take S sch t]
  exact hcarry ha

omit [Fintype V] in
/-- A pool member whose round is no later than the store's current round occurs
in the exact list read by the proposal constructor. -/
theorem mem_processed_attestations_of_pool
    (hc : Protocol.HealConfig) (st : Protocol.Store V)
    {a : CombinedAttestation V} (ha : a ∈ st.sg_pool a.round)
    (hr : a.round ≤ hc.round_of st.s) :
    a ∈ st.processed_attestations hc := by
  unfold Protocol.Store.processed_attestations
  apply List.mem_flatMap.mpr
  refine ⟨a.round, ?_, List.mem_toFinset.mp ha⟩
  exact List.mem_range.mpr (Nat.lt_succ_of_le hr)


/-- An attestation acceptance is a time-indexed processing fact, or else the
row arrived on a block the same call processed.

**Named (C-class statement change).** `NamedRun.acceptsAt` now
ranges over `actualHandlesAtIndex`, which admits carried rows as well as direct
calls, so the erased conclusion "the node processed the attestation" does not
cover every branch. The carried branch is reported explicitly: its own block
call is a direct processing fact for the carrier. -/
theorem processes_of_acceptsAt_attest
    (S : Setup V) {rho : Run V} {v : V} {i : Nat}
    {a : NamedAttestation V} {t : Time}
    (hacc : NamedRun.acceptsAt S rho i v (Object.attest a) t) :
    NamedRun.processes S rho v (Object.attest a) t ∨
      ∃ B : NamedBlock V, NamedRun.processes S rho v (Object.block B) t ∧
        a ∈ B.attestations := by
  obtain ⟨⟨hindex, e, he, hnode, htime⟩, -, -⟩ := hacc
  rcases hindex with hdirect | ⟨B, j, before, hcarr⟩
  · left
    rcases hdirect with ⟨t', htick, hmem⟩ | ⟨t', hdeliver⟩
    · have heq : Event.tick v t' = e := Option.some.inj (htick.symm.trans he)
      have htt : t' = t := (congrArg Event.time heq).trans htime
      subst t'
      exact Or.inl ⟨i, htick, hmem⟩
    · have heq : Event.deliver v (Object.attest a) t' = e :=
        Option.some.inj (hdeliver.symm.trans he)
      have htt : t' = t := (congrArg Event.time heq).trans htime
      subst t'
      exact Or.inr ⟨i, hdeliver⟩
  · right
    refine ⟨B, ?_, List.mem_of_getElem? hcarr.2.2.2⟩
    rcases hcarr.1 with ⟨t', hdeliver, -⟩ | ⟨t', htick, hmem, -⟩
    · have heq : Event.deliver v (Object.block B) t' = e :=
        Option.some.inj (hdeliver.symm.trans he)
      have htt : t' = t := (congrArg Event.time heq).trans htime
      subst t'
      exact Or.inr ⟨i, hdeliver⟩
    · have heq : Event.tick v t' = e := Option.some.inj (htick.symm.trans he)
      have htt : t' = t := (congrArg Event.time heq).trans htime
      subst t'
      exact Or.inl ⟨i, htick, hmem⟩

/-! ### The proposal's exact input list -/








/-! ### Candidate survival, the walk path and root resolution -/


/-- Every named derivation has height at least one: genesis derives the initial
chain state, and each node either keeps its parent's height or advances it. -/
theorem one_le_derive_named_h (E : Env V) (cfg : Protocol.HeightConfig) :
    ∀ B : NamedBlock V, 1 ≤ (derive_named E cfg B).h := by
  intro B
  induction B with
  | genesis => exact Nat.le_refl 1
  | node p sl r gv sup rows pr ih =>
      rcases Proofs.NamedEntryHeight.derive_node_height_cases E cfg p sl r gv sup rows pr with
        hstay | hup
      · rw [hstay]
        exact ih
      · rw [hup]
        exact le_trans ih (Nat.le_succ _)



/-- A candidate proposal gives the complete candidate-tree path used by the
confirmation walk, read at the confirmation duty's own contract anchor. -/
theorem confPath_of_candidate
    (S : Setup V) {rho : Run V} {s : Slot} {v : V} {B : NamedBlock V}
    (hB : B.erase ∈ confTree (Proofs.Optimistic.confStore S rho v s)) :
    ∀ C : Block V,
      Block.Preceq
        (namedConfirmationAnchor S (confirmationInputRead S rho v s)) C →
      C ≠ namedConfirmationAnchor S (confirmationInputRead S rho v s) →
      Block.Preceq C B.erase → C ∈ confTree (Proofs.Optimistic.confStore S rho v s) := by
  let t := Protocol.confirmation_time S.E s
  let pre := rho.stateBeforeTime S t v
  have hpc : ParentClosed pre.st.core :=
    Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho t v
  have hFJ : Block.Preceq pre.st.core.F pre.st.core.J :=
    Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho t v
  intro C hAC _ hCB
  have hBT : B.erase ∈ (Proofs.Optimistic.confStore S rho v s).T :=
    Proofs.Records.get_filtered_block_tree_subset
      (Proofs.Optimistic.confStore S rho v s).toHealing.toFG hB
  have hCT : C ∈ (Proofs.Optimistic.confStore S rho v s).T := by
    apply Proofs.Records.mem_of_preceq ((Proofs.parentClosed_iff pre.st.core).mp hpc).2 C B.erase
    · exact hBT
    · exact hCB
  apply Proofs.Records.mem_filtered_of_preceq
    (st := (Proofs.Optimistic.confStore S rho v s).toHealing.toFG) hFJ hB hCT hCB
  refine Block.preceq_trans ?_ hAC
  exact Proofs.HealingSurface.fg_root_preceq_get_sg_root_with_frame
    (confirmationInputRead S rho v s).cache S.E S.hc
    (Proofs.Optimistic.confStore S rho v s).toHealing
    (S.hc.round_of (Proofs.Optimistic.confStore S rho v s).s)

/-- Run-wide root collision freedom resolves a candidate proposal exactly. -/
theorem confFind_of_candidate
    (S : Setup V) {rho : Run V} (hadm : Admissible S rho)
    {s : Slot} {v : V} (hv : v ∈ rho.honest) {B : NamedBlock V}
    (hB : B.erase ∈ confTree (Proofs.Optimistic.confStore S rho v s)) :
    Block.find? (Proofs.Optimistic.confStore S rho v s).T B.erase.root = some B.erase := by
  let t := Protocol.confirmation_time S.E s
  let pre := rho.stateBeforeTime S t v
  have hBT : B.erase ∈ (Proofs.Optimistic.confStore S rho v s).T :=
    Proofs.Records.get_filtered_block_tree_subset
      (Proofs.Optimistic.confStore S rho v s).toHealing.toFG hB
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    hadm.toNamedAdmissibleCore.toNamedScheduleWellFormed t
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg pre.st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t v).1.1.1
  have hrun : ∀ C ∈ pre.st.bodies, RunBlock S rho C := by
    intro C hC
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i := n)
    rw [← congrArg (fun w => (w v).st.bodies) hn]
    exact hC
  have hinj := Proofs.Bridges.rootInjectiveBelow_of_runBlocks S
    hadm.toNamedAdmissibleCore.toNamedRootCollisionFree hrun
  rw [← hcoh.1] at hinj
  exact Proofs.Optimistic.find?_eq_some_of_unique hBT (fun X hX hroot =>
    hinj X B.erase ⟨X, hX, Block.preceq_self X⟩
      ⟨B.erase, hBT, Block.preceq_self B.erase⟩ hroot)




/-! ## Strict honest-weight-majority run producers -/


#print axioms confPath_of_candidate
#print axioms confFind_of_candidate

end Protocol
end DecoupledConsensusModel

end
