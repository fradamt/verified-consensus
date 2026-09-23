module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ExcludesRefute
public import DecoupledConsensusProofs.Execution.StoreFinalityCore
public import DecoupledConsensusProofs.Protocol.Handlers.Blocks
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.Acceptance
public import DecoupledConsensusProofs.Protocol.Handlers.AcceptanceTiming
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Canonicality
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.ProposalCore
public import DecoupledConsensusProofs.Protocol.Handlers.Proposer
public import DecoupledConsensusProofs.Protocol.Schedule.SlotInduction
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.StoreFinalityConsequences
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Handlers.GoldfishVotePool

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Vote-store extension transfer

This file isolates the run-facing content of `Proofs.Optimistic.VoteStoreExtends`.
The proposal belongs to the exact frozen voter candidate tree, and the
bookkeeping fields are discharged from that tree with the proposal erased.

A current-slot block has no proper stored descendant at the vote read. The
terminal facts below cover both the composed anchor and every frozen candidate,
so compatible-anchor producers can conclude the exact full frozen head is the
proposal. Intermediate transfer mechanics remain private to their producers.

**Named-runtime proof (design note).** Under  the token
`Proofs.Optimistic.voteDutyStore` is not retired and needs no repair: the two
declarations kept here read it only as the tree a head is resolved in.

 and  restore the proposal, slot, parent-closure, and terminality rows
below using named bodies and the named read invariants. The three transfer
declarations remain a Open under: their `ProposalWalkTransferred.head`
field equates the emitted/proposed head with the bare current-contract head.
The named duty uses the prepared frame contract, and Q-PR2 supplies no such
agreement theorem. No public agreement premise is added.
-/



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]


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

/-! ## Named proposal timing -/


theorem processes_proposedBlock_before_vote_after_gst
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hs : 0 < s) (hprop : S.E.proposer s ∈ rho.honest)
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.vote_time S.E s ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest)
    (hFvote : ∀ B : NamedBlock V,
      Statements.Instantiation.proposedBlockAt S rho s = some B →
      Block.Preceq
        (rho.stateBeforeTime S (Protocol.vote_time S.E s) v).st.core.F B.erase) :
    ∃ B : NamedBlock V, Statements.Instantiation.proposedBlockAt S rho s = some B ∧
      ∃ t, Protocol.proposal_time S.E s ≤ t ∧
        t < Protocol.vote_time S.E s ∧
        NamedRun.processes S rho v (.block B) t := by
  have hpv : Protocol.proposal_time S.E s ≤ Protocol.vote_time S.E s := by
    unfold Protocol.vote_time
    exact le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)
  obtain ⟨B, hB, -, hemit⟩ := DecoupledConsensusModel.Proofs.HealingSurface.proposedBlockAt_emits_of_honest S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed s hs hprop
      (le_trans hpv hhor)
  have hadd : Protocol.proposal_time S.E s + S.E.Δ =
      Protocol.vote_time S.E s := by
    unfold Protocol.proposal_time Protocol.vote_time
    ring
  have hdeadline : max (Protocol.proposal_time S.E s) S.E.t_GST + S.E.Δ ≤
      rho.horizon := by
    rw [max_eq_left hpost, hadd]
    exact hhor
  have hguard : NamedReceipt.excludes
      (NamedRun.stateBeforeTime S rho
        (max (Protocol.proposal_time S.E s) S.E.t_GST + S.E.Δ) v).st (.block B) = false := by
    rw [max_eq_left hpost, hadd]
    exact Proofs.not_excludes_of_F_preceq_later_time S rho
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted le_rfl
      (hFvote B hB)
  obtain ⟨t, hlo, hhi, hhandled⟩ :=
    adm.toNamedAdmissibleCore.toNamedSynchrony.broadcast
      (S.E.proposer s) hprop (.block B) (Protocol.proposal_time S.E s) hemit
      v hv hdeadline hguard
  have hproc : NamedRun.processes S rho v (.block B) t := by
    rcases hhandled with ⟨j, hactual⟩
    change NamedRun.processesAtIndex S rho j v (.block B) ∧
      ∃ e : NamedEvent V, rho.events[j]? = some e ∧ e.node = v ∧ e.time = t at hactual
    change NamedRun.emits S rho v (.block B) t ∨
      ∃ i : Nat, rho.events[i]? = some (.deliver v (.block B) t)
    rcases hactual.1 with htick | hdeliver
    · obtain ⟨t', he', hmem⟩ := htick
      obtain ⟨e, he, -, het⟩ := hactual.2
      have heq : NamedEvent.tick v t' = e := Option.some.inj (he'.symm.trans he)
      have ht' : t' = t := (congrArg NamedEvent.time heq).trans het
      subst t'
      exact Or.inl ⟨j, he', hmem⟩
    · obtain ⟨t', he'⟩ := hdeliver
      obtain ⟨e, he, -, het⟩ := hactual.2
      have heq : NamedEvent.deliver v (.block B) t' = e :=
        Option.some.inj (he'.symm.trans he)
      have ht' : t' = t := (congrArg NamedEvent.time heq).trans het
      subst t'
      exact Or.inr ⟨j, he'⟩
  exact ⟨B, hB, t, hlo, by simpa [max_eq_left hpost, hadd] using hhi, hproc⟩

/-! ## Vote-store terminality at the named read -/

theorem block_slot_le_of_mem_voteStore_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
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


theorem parent_slot_lt_of_mem_voteStore_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {v : V} {s : Slot} {C H : Block V}
    (hC : C ∈ (Proofs.Optimistic.voteDutyStore S rho v s).T)
    (hparent : C.parent? = some H) : H.slot < C.slot := by
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed (Protocol.vote_time S.E s)
  have hCn : C ∈ (rho.stateBefore S n v).st.core.T := by
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore,
      Run.storeBeforeTime, hn] using hC
  obtain hgen | ⟨D, hDe, i, hin, t, hacc⟩ :=
    Protocol.acceptsAt_block_of_processed_erased S rho v n hCn
  · subst C
    simp [Block.parent?] at hparent
  · rw [← Proofs.parent_eq_of_parent? hparent]
    simpa only [hDe] using Protocol.parent_slot_lt_of_acceptsAt_block S hacc


private theorem voteDutyStore_parentClosed_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    (v : V) (s : Slot) :
    ParentClosed (Proofs.Optimistic.voteDutyStore S rho v s) := by
  let pre := rho.storeBeforeTime S v (Protocol.vote_time S.E s)
  have hpc : ParentClosed pre.core :=
    Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
      (Protocol.vote_time S.E s) v
  rw [Proofs.parentClosed_iff] at hpc ⊢
  simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
    Proofs.Optimistic.tickStore, pre] using hpc


theorem voteDutyStore_terminal_of_preceq_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {v : V} {s : Slot} {B X : Block V}
    (hslot : B.slot = s)
    (hX : X ∈ (Proofs.Optimistic.voteDutyStore S rho v s).T)
    (hBX : Block.Preceq B X) : X = B := by
  by_contra hne
  have hBne : B ≠ X := fun h => hne h.symm
  obtain ⟨C, hCparent, hCX⟩ := exists_child_towards X hBX hBne
  have hpc := voteDutyStore_parentClosed_core S adm v s
  have hCT : C ∈ (Proofs.Optimistic.voteDutyStore S rho v s).T :=
    Proofs.Records.mem_of_preceq ((Proofs.parentClosed_iff _).mp hpc).2 C X hX hCX
  have hle := block_slot_le_of_mem_voteStore_core S adm hCT
  have hlt := parent_slot_lt_of_mem_voteStore_core S adm hCT hCparent
  rw [hslot] at hlt
  exact (Nat.not_lt_of_ge hle) hlt

theorem voteDutyStore_terminal_of_preceq
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} {s : Slot} {B X : Block V}
    (hslot : B.slot = s)
    (hX : X ∈ (Proofs.Optimistic.voteDutyStore S rho v s).T)
    (hBX : Block.Preceq B X) : X = B :=
  voteDutyStore_terminal_of_preceq_core S adm.toNamedAdmissibleCore hslot hX hBX

theorem voter_candidate_tree_terminal_of_preceq_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {v : V} {s : Slot} {B X : Block V}
    (hslot : B.slot = s)
    (hX : X ∈ Proofs.Optimistic.voter_candidate_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho v s).toHealing)
    (hBX : Block.Preceq B X) : X = B := by
  refine voteDutyStore_terminal_of_preceq_core S adm (v := v) (s := s) hslot ?_ hBX
  simp only [Proofs.Optimistic.voter_candidate_tree, Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.voter_processed_block_tree, Finset.mem_filter] at hX
  exact hX.1.1.1.1


theorem candidate_leaf_at_vote_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {v : V} {s : Slot} {B : Block V}
    (hslot : B.slot = s) :
    ∀ C ∈ Proofs.Optimistic.voter_candidate_tree S.E
        (Proofs.Optimistic.voteDutyStore S rho v s).toHealing,
      C.parent? ≠ some B := by
  intro C hC hparent
  have hCT : C ∈ (Proofs.Optimistic.voteDutyStore S rho v s).T := by
    simp only [Proofs.Optimistic.voter_candidate_tree, Protocol.get_filtered_block_tree_from,
      Protocol.viable_tree, Protocol.finalized_descendants,
      Protocol.voter_processed_block_tree, Finset.mem_filter] at hC
    exact hC.1.1.1.1
  have hle := block_slot_le_of_mem_voteStore_core S adm hCT
  have hlt := parent_slot_lt_of_mem_voteStore_core S adm hCT hparent
  rw [hslot] at hlt
  exact (Nat.not_lt_of_ge hle) hlt


/-! ## Vote-store terminality at the read -/

end Protocol
end DecoupledConsensusModel

end
