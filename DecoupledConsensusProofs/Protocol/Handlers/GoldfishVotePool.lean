module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.Runtime
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.Handlers.Admission
public import DecoupledConsensusProofs.Protocol.Handlers.BlockStamp
public import DecoupledConsensusProofs.Execution.BridgesTail
public import DecoupledConsensusProofs.Protocol.Schedule.NamedTick
public import DecoupledConsensusProofs.Protocol.Handlers.Pool
public import DecoupledConsensusProofs.Protocol.Schedule.AdoptionTransport
public import DecoupledConsensusProofs.Protocol.Handlers.Blocks
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Records
public import DecoupledConsensusProofs.Protocol.Handlers.ConfirmationMembership
public import DecoupledConsensusProofs.Generic.SlotFreshness
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Agreement

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace Optimistic

open Internal Execution
open Protocol
open Proofs.HealingSurface (voterAnchorAt voterCandidateTreeAt)
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Honest vote-head slot validity -/

/-- A block held by the vote-duty store is not from a later slot than the
vote-duty read. This is the run-level form of the block handler's future-slot
guard; it proves that an honest vote head is not from the future at resolution.
The proof follows the accepted-block receipt time back to the vote instant. -/
private theorem slot_le_of_proposal_before_vote (E : Env V) {k s : Slot}
    (h : Protocol.proposal_time E k < Protocol.vote_time E s) : k ≤ s := by
  unfold Protocol.proposal_time Protocol.vote_time Env.t slotStart at h
  by_contra hnot
  have hsk : s + 1 ≤ k := Nat.lt_iff_add_one_le.mp (Nat.lt_of_not_ge hnot)
  have hcast : (s : Int) + 1 ≤ (k : Int) := by exact_mod_cast hsk
  have hmul : 4 * E.Δ * ((s : Int) + 1) ≤ 4 * E.Δ * (k : Int) :=
    Int.mul_le_mul_of_nonneg_left hcast
      (Int.mul_nonneg (by norm_num) (le_of_lt E.Δ_pos))
  have hd4 : E.Δ < 4 * E.Δ := by
    simpa using
      (Int.mul_lt_mul_of_pos_right (show (1 : Int) < 4 by norm_num) E.Δ_pos)
  have hgap : 4 * E.Δ * (s : Int) + E.Δ <
      4 * E.Δ * ((s : Int) + 1) := by
    calc
      4 * E.Δ * (s : Int) + E.Δ <
          4 * E.Δ * (s : Int) + 4 * E.Δ :=
        Int.add_lt_add_left hd4 _
      _ = 4 * E.Δ * ((s : Int) + 1) := by ring
  have hklt := lt_trans h hgap
  exact (not_lt_of_ge hmul) hklt

theorem block_slot_le_of_mem_voteDutyStore
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} {s : Slot} {C : Block V}
    (hC : C ∈ (Proofs.Optimistic.voteDutyStore S rho v s).T) : C.slot ≤ s := by
  obtain ⟨n, hn, hbefore⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed (Protocol.vote_time S.E s)
  have hCn : C ∈ (rho.stateBefore S n v).st.core.T := by
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore,
      Run.storeBeforeTime, hn] using hC
  obtain hgen | ⟨D, hDe, i, hin, t, hacc⟩ :=
    Protocol.acceptsAt_block_of_processed_erased S rho v n hCn
  · subst C
    exact Nat.zero_le s
  · obtain ⟨e, he, -, het⟩ := hacc.1.2
    have ht : t < Protocol.vote_time S.E s := by
      rw [← het]
      exact hbefore i e hin he
    have hslot := Proofs.NamedSlotFreshness.proposal_time_le_of_acceptsAt_block
      S adm hacc
    have hslot' : Protocol.proposal_time S.E C.slot ≤ t := by
      simpa only [hDe] using hslot
    exact slot_le_of_proposal_before_vote S.E (lt_of_le_of_lt hslot' ht)

private theorem voteDutyHead_mem_voteDutyStore_local
    (S : Setup V) (rho : Run V) (v : V) (s : Slot) :
    voterHeadAt S rho v s ∈ (Proofs.Optimistic.voteDutyStore S rho v s).T := by
  let read := Internal.NamedRecoveryRead.voteDutyRead S rho v s
  let st := read.st.core
  have hinvPre : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (rho.stateBeforeTime S (Protocol.vote_time S.E s) v).st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
      (Protocol.vote_time S.E s) v).1
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg read.st := by
    simpa only [read, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt] using
      Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ _ hinvPre
  have hroot : Protocol.get_fg_root st.toHealing.toFG ∈ st.T :=
    Proofs.NamedStoreRoots.fg_root_mem read.st hinv.1.2
  have hanchor : voterAnchorAt S rho v s ∈ st.T :=
    Proofs.NamedConfirmationMembership.runtime_anchor_mem read.cache
      S.E S.hc st.toHealing (S.hc.round_of st.s) hroot
  have htree : voterCandidateTreeAt S rho v s ⊆ st.T := by
    intro D hD
    have hprocessed := Proofs.Records.get_filtered_block_tree_from_subset
      st.toHealing.toFG
      (Protocol.voter_processed_block_tree S.E st.toHealing.toFG.toSG.toGoldfishStore st.s) hD
    exact (Finset.mem_filter.mp hprocessed).1
  have hHmem : voterHeadAt S rho v s ∈ st.T := by
    rw [show voterHeadAt S rho v s = Protocol.ghost (voterAnchorAt S rho v s)
        (voterCandidateTreeAt S rho v s)
        (Protocol.goldfish_score S.E st.T
          (Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (st.s - 1))
        (Protocol.goldfish_eligible S.E st.σ st.h_max st.T st.s
          (Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (st.s - 1)) from rfl]
    exact Proofs.Records.ghost_mem_of _ _ hanchor htree
  have hHpre : voterHeadAt S rho v s ∈
      (rho.stateBeforeTime S (Protocol.vote_time S.E s) v).st.core.T := by
    simpa only [read, st, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hHmem
  simpa only [voteDutyHead, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
    Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hHpre

private theorem emitted_vote_head_eq_voterHeadAt
    (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) {x : V} {u : GoldfishVote V} {t : Time}
    (hemit : rho.emits S x (Object.gfVote u) t) :
    u.head = (voterHeadAt S rho x u.slot).root := by
  have hshape := emits_gfVote_shape S hemit
  have ht : t = Protocol.vote_time S.E u.slot := by
    rw [hshape.2.2.2]
    exact hshape.2.1
  subst t
  obtain ⟨i, hi, hmem⟩ := hemit
  change Object.gfVote u ∈
    (on_tick_emit S x (rho.stateBefore S i x)
      (Protocol.vote_time S.E u.slot)).2 at hmem
  rw [stateBefore_tick_eq_stateBeforeTime S sch hi] at hmem
  have hduty := (gfVote_emitted_shape S x
    (rho.stateBeforeTime S (Protocol.vote_time S.E u.slot) x)
    (Protocol.vote_time S.E u.slot) hmem).2.2.1
  simp only [NamedActionReads.confirmationReadFrom,
    Protocol.NamedStore.setClock, slotOf_vote_time,
    Protocol.NamedDuties.goldfish_vote_with,
    Protocol.goldfish_vote_with] at hduty
  split at hduty
  · simpa only [voteDutyHead, voterHeadAt,
      Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, slotOf_vote_time] using
      (congrArg GoldfishVote.head (Option.some.inj hduty)).symm
  · simp at hduty

/-- An emitted honest vote's named head cannot resolve to a later-slot block in
any honest receiver store. The emitter's vote-duty store supplies the slot
bound; named run-block witnesses and `RootCollisionFree` transfer it to the
receiver's tree. -/
theorem emitted_vote_head_slot_le_of_store_mem
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {x v : V} (hx : x ∈ rho.honest) (hv : v ∈ rho.honest)
    {s : Slot} {u : GoldfishVote V}
    (hemit : rho.emits S x (Object.gfVote u) (Protocol.vote_time S.E s))
    (hus : u.slot = s) {t : Time} {H : Block V}
    (hH : H ∈ (rho.storeBeforeTime S v t).T)
    (hroot : H.root = u.head) : H.slot ≤ u.slot := by
  have hhead := emitted_vote_head_eq_voterHeadAt S adm.toNamedScheduleWellFormed hemit
  have hheadMem := voteDutyHead_mem_voteDutyStore_local S rho x s
  have hheadSlot := block_slot_le_of_mem_voteDutyStore S adm hheadMem
  obtain ⟨C, hCbody, hCrun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
      adm.toNamedScheduleWellFormed hx (Protocol.vote_time S.E s) hheadMem
  obtain ⟨D, hDbody, hDrun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
      adm.toNamedScheduleWellFormed hv t hH
  have hCroot : C.root = u.head := by
    calc
      C.root = C.erase.root := (Proofs.NamedWire.erase_root C).symm
      _ = (voterHeadAt S rho x s).root := congrArg Block.root hCbody
      _ = u.head := by simpa only [hus] using hhead.symm
  have hDroot : D.root = u.head := by
    calc
      D.root = D.erase.root := (Proofs.NamedWire.erase_root D).symm
      _ = H.root := congrArg Block.root hDbody
      _ = u.head := hroot
  have hDC : D = C :=
    adm.toNamedRootCollisionFree.root_injective D C hDrun hCrun D C
      (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self C)) (hDroot.trans hCroot.symm)
  have hslot : H.slot = (voterHeadAt S rho x s).slot := by
    calc
      H.slot = D.erase.slot := by rw [hDbody]
      _ = C.erase.slot := by rw [hDC]
      _ = (voterHeadAt S rho x s).slot := by rw [hCbody]
  simpa only [hslot, hus] using hheadSlot




/-- **A delivery whose checked-committee guard and `on_goldfish_vote` guard all
clear pools the exact vote, with its exact receipt stamp.** The five
hypotheses are, in order: the checked ingress's own committee test (positive),
then the three `on_goldfish_vote` guard disjuncts negated (slot too low, slot
too high, already pooled), then the equivocation-cap test negated. No
admissibility or honesty premise: this states exactly what the two handlers
read, mirroring `attest_pooled_of_delivery`. -/
theorem mem_pool_of_delivery (S : Setup V) (rho : NamedRun V)
    {i : Nat} {w : V} {u : GoldfishVote V} {t : Time}
    (hi : rho.events[i]? = some (.deliver w (Object.gfVote u) t))
    (hcommittee : u.val_index ∈ S.E.committee u.slot)
    (hfresh : ¬ u.slot < (NamedRun.stateBefore S rho i w).st.s - 1)
    (hfuture : ¬ (NamedRun.stateBefore S rho i w).st.s < u.slot)
    (hdup : u ∉ (NamedRun.stateBefore S rho i w).st.gf_votes u.slot)
    (hequiv : ¬ Protocol.equivocates
        ((NamedRun.stateBefore S rho i w).st.pool u.slot) u.val_index = true) :
    u ∈ (NamedRun.stateBefore S rho (i + 1) w).st.gf_votes u.slot ∧
      (NamedRun.stateBefore S rho (i + 1) w).st.timestamp_vote u =
        some ((NamedRun.stateBefore S rho i w).st.t : Stamp) := by
  set st := (NamedRun.stateBefore S rho i w).st.core with hstdef
  have hguard : ¬ (u.slot < st.s - 1 ∨ st.s < u.slot ∨ u ∈ st.gf_votes u.slot) := by
    simp only [not_or]
    exact ⟨hfresh, hfuture, hdup⟩
  have hstep : NamedRun.stateBefore S rho (i + 1) w =
      NamedNode.process S (NamedRun.stateBefore S rho i w) (Object.gfVote u) :=
    Proofs.NamedRuntime.stateBefore_deliver S rho hi
  have hcheck : ¬ (u.val_index ∉ S.E.committee u.slot) := fun hcon => hcon hcommittee
  have hcore : (NamedRun.stateBefore S rho (i + 1) w).st.core =
      Protocol.on_goldfish_vote st u := by
    rw [hstep]
    show Protocol.on_goldfish_vote_checked S.E st u = _
    unfold Protocol.on_goldfish_vote_checked
    rw [if_neg hcheck]
  obtain ⟨hgf, hts, -⟩ := Protocol.on_goldfish_vote_insert st u hguard hequiv
  refine ⟨?_, ?_⟩
  · show u ∈ (NamedRun.stateBefore S rho (i + 1) w).st.core.gf_votes u.slot
    rw [hcore, hgf]
    simp
  · show (NamedRun.stateBefore S rho (i + 1) w).st.core.timestamp_vote u = _
    rw [hcore, hts]
    simp [hstdef]

/-! ## 2. Delivery inside the slot window: the slot guard is shut -/

/-- **The receiver's clock is in `[t_s+Δ, t_s+2Δ)`, so its slot is `s` and the
guard `Σ.s < vote.slot` is shut.** Named twin of earlier's `delivery_store_slot`
(`Optimistic/Alignment.lean`). -/
theorem delivery_store_slot_core (S : Setup V) {rho : NamedRun V}
    (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) {i : Nat} {u : GoldfishVote V} {s : Slot} {t' : Time}
    (hi : rho.events[i]? = some (.deliver w (Object.gfVote u) t'))
    (hlo : Protocol.vote_time S.E s ≤ t')
    (hhi : t' < Protocol.support_cutoff S.E s) :
    (NamedRun.stateBefore S rho i w).st.s = s := by
  have hclock : Protocol.vote_time S.E s ≤ (NamedRun.stateBefore S rho i w).st.t := by
    refine Protocol.tick_le_store_time S adm.toNamedScheduleWellFormed hi ?_ hlo
    refine adm.tick_total w hw _ (publicTime_vote_time S s) (vote_time_nonneg S.E s) ?_
    exact le_trans hlo (adm.in_horizon _ (List.mem_of_getElem? hi)).2
  have hup : (NamedRun.stateBefore S rho i w).st.t ≤ t' := by
    simpa [Event.time] using
      Protocol.store_time_le_event_time S adm.toNamedScheduleWellFormed hi w
  have hslot := Proofs.NamedStoreBridge.slotOfClock_stateBefore S rho i w
  unfold Proofs.Optimistic.SlotOfClock at hslot
  show (NamedRun.stateBefore S rho i w).st.core.s = s
  rw [hslot]
  exact Proofs.Optimistic.slotOf_of_between S.E s hclock (lt_of_le_of_lt hup hhi)

theorem delivery_store_slot (S : Setup V) {rho : NamedRun V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {i : Nat} {u : GoldfishVote V} {s : Slot} {t' : Time}
    (hi : rho.events[i]? = some (.deliver w (Object.gfVote u) t'))
    (hlo : Protocol.vote_time S.E s ≤ t')
    (hhi : t' < Protocol.support_cutoff S.E s) :
    (NamedRun.stateBefore S rho i w).st.s = s :=
  delivery_store_slot_core S adm.toNamedAdmissibleCore hw hi hlo hhi

/-! ## 3. Self-emission: honest votes never equivocate against their own view

`pool_no_honest_equivocation` needs, for the carried half, that an honest
store's tree only ever holds blocks it processed
(`NamedBridgesTail.processes_block_of_mem_T`, now built) and, for the bare
half, that a pooled vote is a processed one (`Protocol.Pool`'s
`processes_gfVote_of_mem_pool`). `Unforgeable` turns either into an emission, and
`emits_gfVote_unique` collapses two emissions by the same honest validator at
the same slot to one vote. -/


/-- A vote visible at a named prefix: held in some pool slot, or carried by
some retained named body. Exported (: the only uses were internal) so that
the core-strength uniqueness below is usable by the weak confirmation branches. -/
def NamedVoteVisible (S : Setup V) (rho : NamedRun V) (w : V) (n : Nat)
    (u : GoldfishVote V) : Prop :=
  (∃ k : Slot, u ∈ (NamedRun.stateBefore S rho n w).st.gf_votes k) ∨
    ∃ B ∈ (NamedRun.stateBefore S rho n w).st.bodies, u ∈ B.gf_votes

/-- An honest sender of a visible vote emitted it. Only `NamedUnforgeable`'s
`unforgeable` and `carried_gf` are used, and both are core fields. -/
theorem named_emits_of_voteVisible (S : Setup V) {rho : NamedRun V}
    (adm : AdmissibleCore S rho) (w : V) (n : Nat) {u : GoldfishVote V}
    (hu : NamedVoteVisible S rho w n u) (hx : u.val_index ∈ rho.honest) :
    ∃ t : Time, NamedRun.emits S rho u.val_index (Object.gfVote u) t := by
  have hblock : ∀ B : NamedBlock V, B ∈ (NamedRun.stateBefore S rho n w).st.bodies →
      u ∈ B.gf_votes → ∃ t : Time, NamedRun.emits S rho u.val_index (Object.gfVote u) t := by
    intro B hB hmem
    rcases Proofs.Bridges.processes_block_of_mem_T S rho w n B hB with
      rfl | ⟨j, e, -, -, hproc⟩
    · exact absurd hmem (by simp [NamedBlock.gf_votes])
    · exact (adm.carried_gf w B e.time hproc u hmem hx).imp fun _ ht => ht.2
  rcases hu with ⟨k, hk⟩ | ⟨B, hB, hmem⟩
  · obtain ⟨j, e, -, -, hproc⟩ :=
      Protocol.processes_gfVote_of_mem_pool S rho w n k u hk
    rcases hproc with hbare | ⟨B, hprocB, hmem⟩
    · exact (adm.unforgeable w (Object.gfVote u) e.time hbare u.val_index hx rfl).imp
        fun _ ht => ht.2
    · exact (adm.carried_gf w B e.time hprocB u hmem hx).imp fun _ ht => ht.2
  · exact hblock B hB hmem

/-- One honest validator has one visible vote per slot at a named prefix.
Core strength: the proof uses `unforgeable`, `carried_gf` and the schedule,
all of which `AdmissibleCore` already carries. -/
theorem named_voteVisible_unique (S : Setup V) {rho : NamedRun V}
    (adm : AdmissibleCore S rho) (w : V) (n : Nat) {u₁ u₂ : GoldfishVote V}
    (h₁ : NamedVoteVisible S rho w n u₁) (h₂ : NamedVoteVisible S rho w n u₂)
    (hx : u₁.val_index ∈ rho.honest) (hval : u₂.val_index = u₁.val_index)
    (hslot : u₁.slot = u₂.slot) : u₁ = u₂ := by
  obtain ⟨t₁, he₁⟩ := named_emits_of_voteVisible S adm w n h₁ hx
  obtain ⟨t₂, he₂⟩ := named_emits_of_voteVisible S adm w n h₂ (by rw [hval]; exact hx)
  rw [hval] at he₂
  exact Proofs.Optimistic.emits_gfVote_unique S adm.toNamedScheduleWellFormed he₁ he₂ hslot

/-- **An honest validator's votes never trip the pool cap, at any named
prefix.** Named twin of earlier's `pool_no_honest_equivocation`
(`Optimistic/Alignment.lean`), rebuilt over `NamedRun`/`Protocol.NamedStore`
now that `NamedBridgesTail.processes_block_of_mem_T` is built. -/
theorem pool_no_honest_equivocation_of_core (S : Setup V) {rho : NamedRun V}
    (adm : AdmissibleCore S rho)
    (w : V) (n : Nat) (k : Slot) {x : V} (hx : x ∈ rho.honest) :
    Protocol.equivocates ((NamedRun.stateBefore S rho n w).st.pool k) x = false := by
  have hps := Protocol.poolStamps_stateBefore S adm.toNamedScheduleWellFormed w n
  rw [Protocol.equivocates, decide_eq_false_iff_not, Nat.not_le]
  refine Nat.lt_succ_of_le (Finset.card_le_one.mpr ?_)
  intro u₁ hu₁ u₂ hu₂
  simp only [Protocol.votes_by, Finset.mem_filter, Protocol.NamedStore.pool,
    Protocol.Store.pool, List.mem_toFinset] at hu₁ hu₂
  refine named_voteVisible_unique S adm w n (Or.inl ⟨k, hu₁.1⟩) (Or.inl ⟨k, hu₂.1⟩)
    (by rw [hu₁.2]; exact hx) (by rw [hu₂.2, hu₁.2]) ?_
  rw [hps.slot k u₁ hu₁.1, hps.slot k u₂ hu₂.1]

/-- The strong-admissibility spelling, for the existing consumers. -/
theorem pool_no_honest_equivocation (S : Setup V) {rho : NamedRun V} (adm : Admissible S rho)
    (w : V) (n : Nat) (k : Slot) {x : V} (hx : x ∈ rho.honest) :
    Protocol.equivocates ((NamedRun.stateBefore S rho n w).st.pool k) x = false :=
  pool_no_honest_equivocation_of_core S adm.toNamedAdmissibleCore w n k hx

/-- A carried support vote is also a raw vote in every named run store. -/
theorem carried_support_subset_of_mem_T_core (S : Setup V) {rho : Run V}
    (adm : AdmissibleCore S rho) (w : V) (n : Nat) {B : Block V}
    (hB : B ∈ (NamedRun.stateBefore S rho n w).st.core.T) :
    ∀ u ∈ B.gf_support_votes, u ∈ B.gf_votes := by
  obtain ⟨D, hD, hDB⟩ := Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n w hB
  have hDsub : ∀ u ∈ D.gf_support_votes, u ∈ D.gf_votes := by
    rcases Proofs.Bridges.processes_block_of_mem_T S rho w n D hD with rfl | ⟨j, e, -, -, hproc⟩
    · intro u hu
      exact absurd hu (by simp [NamedBlock.gf_support_votes])
    · rcases hproc with hem | ⟨i, hi⟩
      · obtain ⟨i, hi, hmem⟩ := hem
        obtain ⟨-, hproposal⟩ := Proofs.HealingSurface.block_mem_on_tick_emit S w
          (NamedRun.stateBefore S rho i w) e.time hmem
        have hproposal' : Protocol.NamedActions.proposal_with
            (NamedProfile.gradeContract
              (NamedActionReads.confirmationReadFrom S
                (NamedRun.stateBefore S rho i w) e.time).cache)
            .poolAndCarried S.E S.hc (S.node w)
            (NamedActionReads.confirmationReadFrom S
              (NamedRun.stateBefore S rho i w) e.time).st = some D := by
          unfold Protocol.NamedDuties.propose_block_with at hproposal
          split at hproposal
          · cases hproposal
          · cases hproposal
            assumption
        simp only [Protocol.NamedActions.proposal_with, Protocol.with_proposal_input,
          Option.map_eq_some_iff] at hproposal'
        obtain ⟨parent, -, hDeq⟩ := hproposal'
        rw [← hDeq]
        intro u hu
        exact (List.mem_filter.mp hu).1
      · have hwire := adm.wire i w (Object.block D) e.time hi
        simp only [Object.wellFormed, NamedReceipt.wellFormed,
          Bool.and_eq_true] at hwire
        have hsupport := hwire.1.2
        simp only [Protocol.carried_support_well_formed, List.all_eq_true,
          decide_eq_true_eq] at hsupport
        simpa only [Proofs.NamedWire.erase_goldfish_support, Proofs.NamedWire.erase_goldfish_votes]
          using hsupport
  intro u hu
  have hu' : u ∈ D.gf_support_votes := by
    rw [← Proofs.NamedWire.erase_goldfish_support, hDB]
    exact hu
  have hu'' := hDsub u hu'
  have hu''' : u ∈ D.erase.gf_votes := by
    simpa only [Proofs.NamedWire.erase_goldfish_votes] using hu''
  simpa only [hDB] using hu'''

theorem carried_support_subset_of_mem_T (S : Setup V) {rho : Run V}
    (adm : Admissible S rho) (w : V) (n : Nat) {B : Block V}
    (hB : B ∈ (NamedRun.stateBefore S rho n w).st.core.T) :
    ∀ u ∈ B.gf_support_votes, u ∈ B.gf_votes :=
  carried_support_subset_of_mem_T_core S adm.toNamedAdmissibleCore w n hB

/-! ## 4. The emitter's own tick pools its own vote -/

/-- The `_with` twin of `Proofs.Optimistic.goldfish_vote_fst_of_snd`: whichever
contract computed the duty, a returned vote is exactly the one the checked
ingress just ran on. -/
private theorem goldfish_vote_with_fst_of_snd (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.Store V)
    {u : GoldfishVote V} (h : (Protocol.goldfish_vote_with contract E hc nd st).2 = some u) :
    (Protocol.goldfish_vote_with contract E hc nd st).1 = Protocol.on_goldfish_vote st u := by
  simp only [Protocol.goldfish_vote_with] at h ⊢
  split_ifs at h ⊢ with hcommittee
  rw [← Option.some_inj.mp h]
  simp [Protocol.on_goldfish_vote_checked, hcommittee]

/-- **The emitter's own tick pools its vote, with a receipt stamp at or before
its own instant.** Named twin of earlier's `mem_pool_of_emits`
(`Optimistic/Alignment.lean`). -/
theorem mem_pool_of_emits_core (S : Setup V) {rho : NamedRun V}
    (adm : AdmissibleCore S rho)
    {w : V} {s : Slot} (hs : 0 < s) {u : GoldfishVote V}
    (hemit : NamedRun.emits S rho w (Object.gfVote u) (Protocol.vote_time S.E s))
    (hus : u.slot = s) (hval : u.val_index ∈ rho.honest) :
    ∃ i : Nat, rho.events[i]? = some (.tick w (Protocol.vote_time S.E s)) ∧
      u ∈ (NamedRun.stateBefore S rho (i + 1) w).st.gf_votes s ∧
      ∃ c : Stamp, (NamedRun.stateBefore S rho (i + 1) w).st.timestamp_vote u = some c ∧
        c ≤ (Protocol.vote_time S.E s : Stamp) := by
  obtain ⟨i, hi, ho⟩ := hemit
  set t := Protocol.vote_time S.E s with htdef
  set n := NamedRun.stateBefore S rho i w with hndef
  obtain ⟨-, -, hduty, -, -⟩ := Proofs.Optimistic.gfVote_emitted_shape S w n t ho
  set gc := NamedProfile.gradeContract
      (NamedActionReads.confirmationReadFrom S n t).cache with hgcdef
  have hreadSteq : (NamedActionReads.confirmationReadFrom S n t).st =
      Protocol.NamedStore.setClock S.E n.st t := rfl
  set st0 := Protocol.NamedStore.setClock S.E n.st t with hst0def
  have hduty' : (Protocol.goldfish_vote_with gc S.E S.hc (S.node w) st0.core).2 = some u := by
    rw [← hreadSteq]
    exact hduty
  have hfst := goldfish_vote_with_fst_of_snd gc S.E S.hc (S.node w) st0.core hduty'
  have hslot0 : st0.core.s = s := by
    show S.E.slotOf t = s
    rw [htdef]; exact slotOf_vote_time S.E s
  have hclock0 : st0.core.t = t := rfl
  have hpoolEq : st0.core.pool s = n.st.core.pool s := rfl
  -- The clock write is a `PoolStep`, so `PoolStamps` transports from the
  -- pre-tick store to the post-clock, pre-duty store `st0`.
  have hclockle : n.st.core.t ≤ t := by
    simpa [Event.time] using
      Protocol.store_time_le_event_time S adm.toNamedScheduleWellFormed hi w
  have hstamps0 : Protocol.PoolStamps st0.core := by
    have hstamp := Protocol.poolStep_tickStore n.st.core t (S.E.slotOf t) hclockle
      (Protocol.poolStamps_stateBefore S adm.toNamedScheduleWellFormed w i)
    exact hstamp.2
  have hfresh : ¬ u.slot < st0.core.s - 1 := by
    rw [hslot0, hus]; exact Nat.not_lt.mpr (Nat.sub_le s 1)
  have hfuture : ¬ st0.core.s < u.slot := by
    rw [hslot0, hus]; exact lt_irrefl s
  have hequiv : Protocol.equivocates (st0.core.pool u.slot) u.val_index = false := by
    rw [hus, hpoolEq]
    exact pool_no_honest_equivocation_of_core S adm w i s hval
  obtain ⟨hmem, c, hc, hle⟩ :=
    Protocol.mem_and_stamp_of_process st0.core u hstamps0 hfresh hfuture hequiv
  rw [hus] at hmem
  -- Step through the tick: proposal does not fire (`vote_time ≠ proposal_time`),
  -- so the duty runs at `st0`; confirmation and attest touch neither
  -- `gf_votes` nor `timestamp_vote`, whichever way their own guards land.
  set s' := S.E.slotOf t with hs'def
  set proposed := Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg (S.node w) st0
    with hproposeddef
  set proposalDue := 0 < s' ∧ t = Protocol.proposal_time S.E s' ∧
    S.E.proposer s' = (S.node w).val_index with hproposalDuedef
  set st1 := if proposalDue then proposed.1 else st0 with hst1def
  set voted := Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc (S.node w) st1
    with hvoteddef
  set voteDue := 0 < s' ∧ t = Protocol.vote_time S.E s' with hvoteDuedef
  set st2 := if voteDue then voted.1 else st1 with hst2def
  set st3 := if 0 < s' ∧ t = Protocol.support_cutoff S.E s' then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (s' - 1) else st2
    with hst3def
  have hs'eq : s' = s := by rw [hs'def, htdef]; exact slotOf_vote_time S.E s
  have hpne : ¬ proposalDue := by
    rw [hproposalDuedef]
    rintro ⟨-, hteq, -⟩
    exact Proofs.Optimistic.vote_time_ne_proposal_time S.E s' (by rw [← hteq, htdef, hs'eq])
  have hst1eq : st1 = st0 := by rw [hst1def, if_neg hpne]
  have hvd : voteDue := by rw [hvoteDuedef, hs'eq]; exact ⟨hs, htdef⟩
  have hst2eq : st2.core = Protocol.on_goldfish_vote st0.core u := by
    rw [hst2def, if_pos hvd, hvoteddef, hst1eq]
    exact hfst
  have hst3fields : st3.core.gf_votes = st2.core.gf_votes ∧
      st3.core.timestamp_vote = st2.core.timestamp_vote := by
    rw [hst3def]
    split_ifs
    · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  have htick1eq : (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node w) n.st n.record t).1 =
      if t = S.hc.a S.E.Δ (S.hc.round_of st3.core.s) ∧
          (S.node w).awake (S.hc.round_of st3.core.s) = true then
        (Protocol.NamedDuties.attest_with gc S.E S.hc (S.node w) st3 n.record).1
      else st3 := by
    rw [Proofs.NamedTick.tick_computed_duties]
    dsimp only [st3, st2, voted, voteDue, st1, proposed, proposalDue, s']
    split_ifs <;> rfl
  have hfinalfields :
      (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node w) n.st n.record t).1.core.gf_votes =
        st3.core.gf_votes ∧
      (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node w) n.st n.record t).1.core.timestamp_vote =
        st3.core.timestamp_vote := by
    rw [htick1eq]
    split_ifs
    · obtain ⟨-, -, -, -, hgfv, htsv⟩ := NamedAdmission.admit_row_fixed_fields S.hc st3
        (Protocol.NamedActions.round_action_with gc S.E S.hc (S.node w) st3.core.toHealing
          n.record).2
      exact ⟨hgfv, htsv⟩
    · exact ⟨rfl, rfl⟩
  have hstepFull : NamedRun.stateBefore S rho (i + 1) w = (NamedNode.tick S w n t).1 :=
    Proofs.NamedRuntime.stateBefore_tick S rho hi
  have hgcstep : (NamedNode.tick S w n t).1.st =
      (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node w) n.st n.record t).1 := rfl
  refine ⟨i, hi, ?_, c, ?_, ?_⟩
  · show u ∈ (NamedRun.stateBefore S rho (i + 1) w).st.core.gf_votes s
    rw [hstepFull, hgcstep, hfinalfields.1, hst3fields.1, hst2eq]
    exact hmem
  · show (NamedRun.stateBefore S rho (i + 1) w).st.core.timestamp_vote u = _
    rw [hstepFull, hgcstep, hfinalfields.2, hst3fields.2, hst2eq]
    exact hc
  · rw [← hclock0]
    exact hle

theorem mem_pool_of_emits (S : Setup V) {rho : NamedRun V} (adm : Admissible S rho)
    {w : V} {s : Slot} (hs : 0 < s) {u : GoldfishVote V}
    (hemit : NamedRun.emits S rho w (Object.gfVote u) (Protocol.vote_time S.E s))
    (hus : u.slot = s) (hval : u.val_index ∈ rho.honest) :
    ∃ i : Nat, rho.events[i]? = some (.tick w (Protocol.vote_time S.E s)) ∧
      u ∈ (NamedRun.stateBefore S rho (i + 1) w).st.gf_votes s ∧
      ∃ c : Stamp, (NamedRun.stateBefore S rho (i + 1) w).st.timestamp_vote u = some c ∧
        c ≤ (Protocol.vote_time S.E s : Stamp) :=
  mem_pool_of_emits_core S adm.toNamedAdmissibleCore hs hemit hus hval

/-- Proposal ticks preserve the Goldfish pool and its receipt stamps through
the later duties of the same tick. -/
theorem tick_fields_from_proposal
    (gc : Protocol.GradeContract V) (S : Setup V) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time)
    (hguard : 0 < S.E.slotOf t ∧
      t = Protocol.proposal_time S.E (S.E.slotOf t) ∧
      S.E.proposer (S.E.slotOf t) = nd.val_index) :
    let s := S.E.slotOf t
    let st0 := Protocol.NamedStore.setClock S.E st t
    let st1 := if 0 < s ∧ t = Protocol.proposal_time S.E s ∧
        S.E.proposer s = nd.val_index then
      (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st0).1 else st0
    (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1.core.gf_votes =
        st1.core.gf_votes ∧
      (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1.core.timestamp_vote =
        st1.core.timestamp_vote := by
  dsimp only
  let s := S.E.slotOf t
  let st0 := Protocol.NamedStore.setClock S.E st t
  let proposed := Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st0
  let proposalDue := 0 < s ∧ t = Protocol.proposal_time S.E s ∧
    S.E.proposer s = nd.val_index
  set st1 := if proposalDue then proposed.1 else st0 with hst1def
  let voted := Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st1
  set voteDue := 0 < s ∧ t = Protocol.vote_time S.E s with hvoteDuedef
  set st2 := if voteDue then voted.1 else st1 with hst2def
  set st3 := if 0 < s ∧ t = Protocol.support_cutoff S.E s then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (s - 1) else st2
    with hst3def
  have hst1 : st1 = proposed.1 := by
    rw [hst1def]
    exact if_pos hguard
  have hvote : ¬ voteDue := by
    rw [hvoteDuedef]
    intro hv
    exact Proofs.Optimistic.proposal_time_ne_vote_time S.E s
      (by rw [← hv.2, ← hguard.2.1])
  have hst2 : st2 = st1 := by rw [hst2def, if_neg hvote]
  have hst3fields : st3.core.gf_votes = st2.core.gf_votes ∧
      st3.core.timestamp_vote = st2.core.timestamp_vote := by
    rw [hst3def]
    split_ifs <;> exact ⟨rfl, rfl⟩
  have hstore : (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 =
      (if t = S.hc.a S.E.Δ (S.hc.round_of st3.core.s) ∧
          nd.awake (S.hc.round_of st3.core.s) = true then
        (Protocol.NamedDuties.attest_with gc S.E S.hc nd st3 record).1 else st3) := by
    rw [Proofs.NamedTick.tick_computed_duties]
    dsimp only [Protocol.NamedTick.tick, Protocol.TickScheduler.runWith,
      Protocol.NamedTick.namedOps, st3, st2, st1, voted, voteDue, proposed,
      proposalDue, st0, s]
    split_ifs <;> rfl
  rw [hstore]
  split_ifs
  · obtain ⟨-, -, -, -, hgf, hts⟩ := NamedAdmission.admit_row_fixed_fields S.hc st3
      (Protocol.NamedActions.round_action_with gc S.E S.hc nd st3.core.toHealing record).2
    exact ⟨hgf.trans (hst3fields.1.trans (by rw [hst2, hst1])),
      hts.trans (hst3fields.2.trans (by rw [hst2, hst1]))⟩
  · exact ⟨hst3fields.1.trans (by rw [hst2, hst1]),
      hst3fields.2.trans (by rw [hst2, hst1])⟩

/-! ## 5. A fresh carried vote settles through `process_block_core`'s inner
Goldfish-vote fold

`Protocol.on_block_carried_beforeCutoff_or_equivocates` already gives this
at the erased `Protocol.on_block E cfg st B`. `process_block_core` runs the
same `on_block_checked_using`/`on_block_using` pair with a custom
`buildState`, which the carried-vote fold never reads — only `σ` changes with
it — so the mirror below generalizes it exactly the way
`AdoptionConstructorRun.lean`'s `checked_new_block_stamp` /
`core_new_body_stamp` / `block_new_body_stamp` chain generalizes
`on_block_new_timestamp` for the write-once block stamp. -/

private theorem checked_carried_settled
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V) (B : Block V)
    (buildState : Protocol.ChainState V → Protocol.ChainState V)
    (u : GoldfishVote V) (Γ : Time)
    (hstamps : Protocol.PoolStamps st) (hpre : B ∉ st.T)
    (hpost : B ∈ (Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using E current B buildState) hc st B).T)
    (hu : u ∈ B.gf_votes) (hcommittee : u.val_index ∈ E.committee u.slot)
    (hfresh : ¬ u.slot < st.s - 1) (hfuture : ¬ st.s < u.slot) (hclock : st.t < Γ) :
    u ∈ beforeCutoff (Protocol.on_block_checked_using
          (fun current => Protocol.on_block_using E current B buildState) hc st B).timestamp_vote Γ
        ((Protocol.on_block_checked_using
          (fun current => Protocol.on_block_using E current B buildState) hc st B).pool u.slot) ∨
      Protocol.equivocates
        (beforeCutoff (Protocol.on_block_checked_using
          (fun current => Protocol.on_block_using E current B buildState) hc st B).timestamp_vote Γ
          ((Protocol.on_block_checked_using
            (fun current => Protocol.on_block_using E current B buildState) hc st B).pool u.slot))
        u.val_index = true := by
  dsimp only [Protocol.on_block_checked_using] at hpost ⊢
  by_cases hvalid : Protocol.carried_attestations_admissible hc B = true
  · simp only [hvalid, if_true] at hpost ⊢
    by_cases hfirst : st.s < B.slot ∨ B ∈ st.T ∨ B.parent ∉ st.T
    · rw [show Protocol.on_block_using E st B buildState = st by
        simp only [Protocol.on_block_using, if_pos hfirst]] at hpost
      exact absurd hpost hpre
    · by_cases hadmit : (!Block.preceq st.F B) = true
      · rw [show Protocol.on_block_using E st B buildState = st by
          simp only [Protocol.on_block_using, if_neg hfirst, if_pos hadmit]] at hpost
        exact absurd hpost hpre
      · by_cases hprop : B.proposer? ≠ some (E.proposer B.slot)
        · rw [show Protocol.on_block_using E st B buildState = st by
            simp only [Protocol.on_block_using, if_neg hfirst, if_neg hadmit,
              if_pos hprop]] at hpost
          exact absurd hpost hpre
        · by_cases hparent : ¬ B.parent.slot < B.slot
          · rw [show Protocol.on_block_using E st B buildState = st by
              simp only [Protocol.on_block_using, if_neg hfirst, if_neg hadmit,
                if_neg hprop, if_pos hparent]] at hpost
            exact absurd hpost hpre
          · let stored : Protocol.Store V :=
              { st with
                σ := fun C => if C = B then buildState (st.σ B.parent) else st.σ C
                T := insert B st.T
                timestamp_block := fun C =>
                  if C = B then some (st.t : Stamp) else st.timestamp_block C }
            let unpacked : Protocol.Store V :=
              B.gf_votes.foldl (Protocol.on_goldfish_vote_checked E) stored
            have hout : Protocol.on_block_using E st B buildState =
                Protocol.update_finality unpacked (unpacked.σ B) := by
              unfold Protocol.on_block_using
              rw [if_neg hfirst, if_neg hadmit, if_neg hprop, if_neg hparent]
            have hstored : Protocol.PoolStamps stored :=
              ⟨hstamps.slot, hstamps.stamped, hstamps.pooled, hstamps.bounded⟩
            have hsettled := Protocol.foldl_on_goldfish_vote_checked_beforeCutoff_or_equivocates
              E stored B.gf_votes u Γ hcommittee hstored hu
              hfresh hfuture hclock
            rw [hout]
            simpa only [Protocol.Store.pool, Protocol.update_finality_timestamp_vote,
              Protocol.update_finality_gf_votes, unpacked] using hsettled
  · have hfalse : Protocol.carried_attestations_admissible hc B = false :=
      Bool.eq_false_of_not_eq_true hvalid
    simp only [hfalse, Bool.false_eq_true, if_false] at hpost
    exact absurd hpost hpre

private theorem core_carried_settled (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (u : GoldfishVote V) (Γ : Time)
    (hstamps : Protocol.PoolStamps st.core) (hpre : B ∉ st.bodies)
    (hpost : B ∈ (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).bodies)
    (hu : u ∈ B.erase.gf_votes) (hcommittee : u.val_index ∈ S.E.committee u.slot)
    (hfresh : ¬ u.slot < st.core.s - 1) (hfuture : ¬ st.core.s < u.slot)
    (hclock : st.core.t < Γ) :
    u ∈ beforeCutoff
        (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).core.timestamp_vote Γ
        ((Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).core.pool u.slot) ∨
      Protocol.equivocates
        (beforeCutoff
          (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).core.timestamp_vote Γ
          ((Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).core.pool u.slot))
        u.val_index = true := by
  unfold Protocol.NamedStore.process_block_core at hpost ⊢
  by_cases hp : B.parent ∉ st.bodies
  · simp only [hp] at hpost
    exact absurd hpost hpre
  · rw [if_neg hp] at hpost ⊢
    let after := Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using S.E current B.erase
        (fun parentState => Protocol.named_transition S.E S.cfg parentState B))
      S.hc st.core B.erase
    change B ∈ (Protocol.NamedStore.commitBlock st after B).bodies at hpost
    have hcoreeq : (Protocol.NamedStore.commitBlock st after B).core = after := by
      unfold Protocol.NamedStore.commitBlock
      split_ifs <;> rfl
    rw [hcoreeq]
    by_cases hfreshB : B.erase ∉ st.core.T ∧ B.erase ∈ after.T
    · exact checked_carried_settled S.E S.hc st.core B.erase _ u Γ hstamps hfreshB.1
        hfreshB.2 hu hcommittee hfresh hfuture hclock
    · unfold Protocol.NamedStore.commitBlock at hpost
      rw [if_neg hfreshB] at hpost
      exact absurd hpost hpre

private theorem admit_rows_bodies_of (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) (rows : List (NamedAttestation V)) :
    (Protocol.NamedAdmission.admit_rows hc st rows).bodies = st.bodies := by
  induction rows generalizing st with
  | nil => rfl
  | cons row rows ih =>
      change (Protocol.NamedAdmission.admit_rows hc
        (Protocol.NamedAdmission.admit_row hc st row) rows).bodies = _
      rw [ih, NamedAdmission.admit_row_bodies]

private theorem admit_rows_gf_votes_of (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) (rows : List (NamedAttestation V)) :
    (Protocol.NamedAdmission.admit_rows hc st rows).core.gf_votes = st.core.gf_votes ∧
      (Protocol.NamedAdmission.admit_rows hc st rows).core.timestamp_vote =
        st.core.timestamp_vote := by
  induction rows generalizing st with
  | nil => exact ⟨rfl, rfl⟩
  | cons row rows ih =>
      change (Protocol.NamedAdmission.admit_rows hc
        (Protocol.NamedAdmission.admit_row hc st row) rows).core.gf_votes = _ ∧
        (Protocol.NamedAdmission.admit_rows hc
          (Protocol.NamedAdmission.admit_row hc st row) rows).core.timestamp_vote = _
      obtain ⟨ihgf, ihts⟩ := ih (Protocol.NamedAdmission.admit_row hc st row)
      obtain ⟨-, -, -, -, hgf, hts⟩ := NamedAdmission.admit_row_fixed_fields hc st row
      exact ⟨ihgf.trans hgf, ihts.trans hts⟩

/-- **A fresh Goldfish vote carried in a processed block receives its pool
membership and `timestamp_vote` stamp before an arbitrary deadline through
`process_block_core`'s inner `on_goldfish_vote_checked` fold.** The missing
half of `HonestWeightMajority.targetCarrierVote_settledInPool`
(`Availability/AdoptionConstructorRun.lean`) is the special cutoff instance.
-/
theorem block_carried_before_deadline_or_equivocates
    (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (u : GoldfishVote V) (Γ : Time)
    (hstamps : Protocol.PoolStamps st.core) (hpre : B ∉ st.bodies)
    (hpost : B ∈ (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B).bodies)
    (hu : u ∈ B.erase.gf_votes) (hcommittee : u.val_index ∈ S.E.committee u.slot)
    (hfresh : ¬ u.slot < st.core.s - 1) (hfuture : ¬ st.core.s < u.slot)
    (hclock : st.core.t < Γ) :
    (let final := Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B
     u ∈ beforeCutoff final.core.timestamp_vote Γ (final.core.pool u.slot) ∨
       Protocol.equivocates
         (beforeCutoff final.core.timestamp_vote Γ (final.core.pool u.slot))
         u.val_index = true) := by
  dsimp only
  let core := Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B
  have hcore : B ∈ core.bodies := by
    unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried at hpost
    split_ifs at hpost
    · simpa only [admit_rows_bodies_of] using hpost
    · exact hpost
  have hs := core_carried_settled S st B u Γ hstamps hpre hcore hu hcommittee hfresh hfuture hclock
  unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried
  split_ifs
  · obtain ⟨hgf, hts⟩ := admit_rows_gf_votes_of S.hc core B.attestations
    have hpoolEq2 :
        (Protocol.NamedAdmission.admit_rows S.hc core B.attestations).core.pool u.slot =
          core.core.pool u.slot := by
      simp only [Protocol.Store.pool, hgf]
    rw [hpoolEq2, hts]
    exact hs
  · exact hs

/-! The vote-duty name remains as a compatibility wrapper. -/

/-- The arbitrary-deadline carried-vote result at the named vote-duty cutoff.
-/
theorem block_carried_beforeCutoff_or_equivocates
    (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (u : GoldfishVote V) (Γ : Time)
    (hstamps : Protocol.PoolStamps st.core) (hpre : B ∉ st.bodies)
    (hpost : B ∈
      (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B).bodies)
    (hu : u ∈ B.erase.gf_votes) (hcommittee : u.val_index ∈ S.E.committee u.slot)
    (hfresh : ¬ u.slot < st.core.s - 1) (hfuture : ¬ st.core.s < u.slot)
    (hclock : st.core.t < Γ) :
    (let final := Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B
     u ∈ beforeCutoff final.core.timestamp_vote Γ (final.core.pool u.slot) ∨
       Protocol.equivocates
         (beforeCutoff final.core.timestamp_vote Γ (final.core.pool u.slot))
         u.val_index = true) := by
  exact block_carried_before_deadline_or_equivocates S st B u Γ hstamps hpre hpost hu
    hcommittee hfresh hfuture hclock



theorem admittedBefore_ancestor_mem_and_stamp_at
    (S : Setup V) {rho : NamedRun V} (adm : Admissible S rho)
    {v : V} {A H : Block V} {Γ Γ' : Time}
    (hadmit : Protocol.AdmittedBefore S rho v H Γ)
    (hAH : Block.Preceq A H) (hle : Γ ≤ Γ') :
    A ∈ (Run.storeBeforeTime S rho v Γ').T ∧
      stampedBefore (Run.storeBeforeTime S rho v Γ').timestamp_block Γ A = true := by
  obtain ⟨C, hCH, i, t, hacc, hlt⟩ := hadmit
  obtain ⟨hindex, e, he, hnode, htime⟩ := hacc.1
  have hpostC : C ∈ (NamedRun.stateBefore S rho (i + 1) v).st.bodies := by
    simpa only [Object.processed, NamedReceipt.processed, decide_eq_true_eq] using hacc.2.2
  have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho (i + 1) v).1.1.1
  have hpostH : H ∈ (NamedRun.stateBefore S rho (i + 1) v).st.T := by
    show H ∈ (NamedRun.stateBefore S rho (i + 1) v).st.core.T
    rw [hcoh.1, ← hCH]
    exact Finset.mem_image_of_mem NamedBlock.erase hpostC
  have hpc : ParentClosed (NamedRun.stateBefore S rho (i + 1) v).st.core :=
    Proofs.NamedStoreBridge.parentClosed_stateBefore S rho (i + 1) v
  have hpostA : A ∈ (NamedRun.stateBefore S rho (i + 1) v).st.T :=
    Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2 A H hpostH hAH
  let N := (rho.events.filter (fun x => decide (x.time < Γ'))).length
  have hiN : i < N := by
    by_contra hnot
    have hNle : N ≤ i := Nat.le_of_not_gt hnot
    have hΓ'e : Γ' ≤ e.time :=
      Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed
        (t := Γ') (j := i) (e := e) (by simpa [N] using hNle) he
    rw [htime] at hΓ'e
    exact (not_le_of_gt (lt_of_lt_of_le hlt hle)) hΓ'e
  have hcarry : Protocol.BlockCarry (NamedRun.stateBefore S rho (i + 1) v).st.core
      (NamedRun.stateBefore S rho N v).st.core :=
    Protocol.block_carry S adm.toNamedScheduleWellFormed v N (Nat.succ_le_of_lt hiN)
  have hsource : Protocol.BlockStamps (NamedRun.stateBefore S rho (i + 1) v).st.core :=
    Protocol.blockStamps_stateBefore S adm.toNamedScheduleWellFormed v (i + 1)
  obtain ⟨c, hc⟩ : ∃ c : Stamp,
      (NamedRun.stateBefore S rho (i + 1) v).st.timestamp_block A = some c :=
    Option.isSome_iff_exists.mp (hsource.stamped A hpostA)
  have hcfinal : (NamedRun.stateBefore S rho N v).st.timestamp_block A = some c :=
    hcarry.stamp A c hc
  have hclock : (NamedRun.stateBefore S rho (i + 1) v).st.t ≤ t := by
    have ht := Protocol.block_store_time_after_event_le
      S adm.toNamedScheduleWellFormed he v
    simpa only [htime] using ht
  have hcΓ : c < (Γ : Stamp) :=
    lt_of_le_of_lt
      (le_trans (hsource.bounded A c hc) (WithBot.coe_le_coe.mpr hclock))
      (WithBot.coe_lt_coe.mpr hlt)
  have hstore : Run.storeBeforeTime S rho v Γ' = (NamedRun.stateBefore S rho N v).st := by
    show (Run.stateBeforeTime S rho Γ' v).st = _
    rw [Proofs.Optimistic.stateBeforeTime_eq_take S adm.toNamedScheduleWellFormed Γ']
  rw [hstore]
  refine ⟨hcarry.mem A hpostA, ?_⟩
  simp only [stampedBefore, hcfinal, decide_eq_true_eq]
  exact hcΓ

#print axioms block_carried_before_deadline_or_equivocates
#print axioms carried_support_subset_of_mem_T
#print axioms tick_fields_from_proposal

end Optimistic
end Proofs
end DecoupledConsensusModel

end
