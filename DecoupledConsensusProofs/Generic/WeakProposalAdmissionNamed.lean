module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ExcludesRefute
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.WeakProposalHeadNamed
public import DecoupledConsensusProofs.Objects.WeakLiveConfirmationCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalPivot
public import DecoupledConsensusProofs.Protocol.Handlers.RelayGuards

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Prepared weak-genesis proposal admission -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

namespace WeakGenesis

private theorem finalizedBeforeEvent_preceq_of_fgRootRead_named
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} {i : Nat} {e : Event V} {time : Time} {B : Block V}
    (hi : rho.events[i]? = some e) (hlt : e.time < time)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v time).core.toHealing.toFG) B) :
    Block.Preceq (rho.stateBefore S i v).st.core.F B := by
  let n := (rho.events.filter (fun event => decide (event.time < time))).length
  have hiN : i < n := by
    by_contra hnot
    have htime : time ≤ e.time :=
      le_time_of_index_ge S adm.toNamedScheduleWellFormed
        (by simpa only [n] using Nat.le_of_not_gt hnot) hi
    exact (not_le_of_gt hlt) htime
  let pre := rho.storeBeforeTime S v time
  have hmono : Block.Preceq (rho.stateBefore S i v).st.core.F pre.core.F := by
    have hprefix := stateBefore_F_mono S rho v (Nat.le_of_lt hiN)
    have hstore : pre = (rho.stateBefore S n v).st := by
      simpa only [pre, Run.storeBeforeTime, n] using congrArg NamedNodeState.st
        (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S
          adm.toNamedScheduleWellFormed time) v)
    simpa only [hstore] using hprefix
  have hFJ : Block.Preceq pre.core.F pre.core.J :=
    Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho time v
  exact Block.preceq_trans hmono (Block.preceq_trans
    (Proofs.Records.preceq_get_fg_root_of_F (st := pre.core.toHealing.toFG) hFJ) hroot)

private theorem processes_proposedBlock_before_vote_after_gst_named
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} (hs : 0 < s) (hprop : S.E.proposer s ∈ rho.honest)
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.vote_time S.E s ≤ rho.horizon)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B)
    {v : V} (hv : v ∈ rho.honest)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v (Protocol.vote_time S.E s)).core.toHealing.toFG)
        B.erase) :
    ∃ t, Protocol.proposal_time S.E s ≤ t ∧
      t < Protocol.vote_time S.E s ∧
      NamedRun.processes S rho v (.block B) t := by
  obtain ⟨B₀, hB₀, -, hemit⟩ := proposedBlockAt_emits_of_honest S
    adm.toNamedScheduleWellFormed s hs hprop
      ((proposal_time_lt_vote_time S.E s).le.trans hhor)
  have hB₀B : B₀ = B := proposedBlockAt_unique S rho s hB₀ hB
  subst B₀
  have hadd : Protocol.proposal_time S.E s + S.E.Δ =
      Protocol.vote_time S.E s := by
    unfold Protocol.proposal_time Protocol.vote_time
    ring
  have hdeadline : max (Protocol.proposal_time S.E s) S.E.t_GST + S.E.Δ ≤
      rho.horizon := by
    rw [max_eq_left hpost, hadd]
    exact hhor
  have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
    S rho (Protocol.vote_time S.E s) v
  have hFroot := Proofs.Records.preceq_get_fg_root_of_F
    (st := (rho.storeBeforeTime S v (Protocol.vote_time S.E s)).core.toHealing.toFG) hFJ
  have hFvote : Block.Preceq
      (NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E s) v).st.core.F
        B.erase := Block.preceq_trans hFroot hroot
  have hguard : NamedReceipt.excludes
      (NamedRun.stateBeforeTime S rho
        (max (Protocol.proposal_time S.E s) S.E.t_GST + S.E.Δ) v).st (.block B) = false := by
    rw [max_eq_left hpost, hadd]
    exact not_excludes_of_F_preceq_later_time S rho
      adm.toNamedScheduleWellFormed.sorted le_rfl hFvote
  obtain ⟨t, hlo, hhi, hproc⟩ :=
    adm.broadcast (S.E.proposer s) hprop _ _ hemit v hv hdeadline hguard
  obtain ⟨j, hcall⟩ := hproc
  have hdirect : NamedRun.processes S rho v (.block B) t := by
    rcases hcall with ⟨hindex, e, he, -, het⟩
    rcases hindex with ⟨u, hu, hmem⟩ | ⟨u, hu⟩
    · have hut : u = t := by
        have heq : Event.tick v u = e := Option.some.inj (hu.symm.trans he)
        exact (congrArg Event.time heq).trans het
      subst u
      exact Or.inl ⟨j, hu, hmem⟩
    · have hut : u = t := by
        have heq : Event.deliver v (.block B) u = e :=
          Option.some.inj (hu.symm.trans he)
        exact (congrArg Event.time heq).trans het
      subst u
      exact Or.inr ⟨j, hu⟩
  exact ⟨t, hlo, by simpa only [max_eq_left hpost, hadd] using hhi, hdirect⟩

private theorem acceptsAt_proposedBlock_named
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} (hs : 0 < s) (hprop : S.E.proposer s ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E s ≤ rho.horizon)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B) :
    ∃ i, NamedRun.acceptsAt S rho i (S.E.proposer s) (.block B)
      (Protocol.proposal_time S.E s) := by
  obtain ⟨B₀, hB₀, -, i₁, hi₁, hemem⟩ :=
    proposedBlockAt_emits_of_honest S adm.toNamedScheduleWellFormed
      s hs hprop hhor
  have hB₀B : B₀ = B := proposedBlockAt_unique S rho s hB₀ hB
  subst B₀
  obtain ⟨i₂, hi₂, hmem⟩ :=
    proposedBlockAt_mem_bodies_after_tick_of_admissible
      S adm s hs hprop hhor hB
  have hi : i₁ = i₂ := index_unique_of_nodup
    adm.toNamedScheduleWellFormed.nodup hi₁ hi₂
  subst i₂
  refine ⟨i₁, ⟨Or.inl ⟨Protocol.proposal_time S.E s, hi₁, hemem⟩,
      Event.tick (S.E.proposer s) (Protocol.proposal_time S.E s), hi₁,
      rfl, rfl⟩, ?_, ?_⟩
  · simp only [NamedReceipt.processed, decide_eq_false_iff_not]
    have hstateEq : NamedRun.stateBefore S rho i₁ (S.E.proposer s) =
        NamedRun.stateBeforeTime S rho (Protocol.proposal_time S.E s)
          (S.E.proposer s) :=
      Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S
        adm.toNamedScheduleWellFormed hi₁
    rw [hstateEq]
    intro hmemB
    have htree : (proposerReadAt S rho s).st.core.T =
        (proposerReadAt S rho s).st.bodies.image NamedBlock.erase :=
      (proposerReadAt_invariant S rho s).1.1
    exact proposedBlockErased_fresh_at_tick S adm s hs hB
      (htree ▸ Finset.mem_image_of_mem NamedBlock.erase hmemB)
  · simpa only [NamedReceipt.processed, decide_eq_true_eq] using hmem

private theorem proposedBlock_admittedBefore_vote_of_fgRootRead_named
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} (hs : 0 < s) (hprop : S.E.proposer s ∈ rho.honest)
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.vote_time S.E s ≤ rho.horizon)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B)
    {v : V} (hv : v ∈ rho.honest)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v
          (Protocol.vote_time S.E s)).core.toHealing.toFG) B.erase) :
    AdmittedBefore S rho v B.erase (Protocol.vote_time S.E s) := by
  obtain ⟨isource, hsource⟩ := acceptsAt_proposedBlock_named
    S adm hs hprop ((proposal_time_lt_vote_time S.E s).le.trans hhor) hB
  by_cases hvp : v = S.E.proposer s
  · subst v
    exact ⟨B, rfl, isource, Protocol.proposal_time S.E s, hsource,
      proposal_time_lt_vote_time S.E s⟩
  · obtain ⟨t, hlo, hhi, hproc⟩ :=
      processes_proposedBlock_before_vote_after_gst_named
        S adm hs hprop hpost hhor hB hv hroot
    rcases hproc with hemits | ⟨i, hi⟩
    · have hshape := emits_block_shape S rho hemits
      have hslot : B.slot = s := proposedBlockAt_slot S rho s hB
      have heq : S.E.proposer s = v := by
        rw [← hslot]
        exact hshape.2.2
      exact absurd heq.symm hvp
    · have hF := finalizedBeforeEvent_preceq_of_fgRootRead_named
        S adm hi hhi hroot
      have hcall : NamedRun.actualHandlesAt S rho i v (.block B) t :=
        ⟨Or.inr ⟨t, hi⟩, Event.deliver v (.block B) t, hi, rfl, rfl⟩
      have hheld := NamedRelayGuards.handled_block_held_of_finalized_prefix
        S rho adm.toNamedScheduleWellFormed adm.toNamedDeliveryWellFormed
          adm.toNamedRootCollisionFree hsource hcall hlo hF
      have hfresh : B ∉ (NamedRun.stateBefore S rho i v).st.bodies := by
        have hf := adm.fresh i v (.block B) t hi
        simpa only [NamedReceipt.processed, decide_eq_false_iff_not] using hf
      have haccept : NamedRun.acceptsAt S rho i v (.block B) t := by
        refine ⟨hcall, ?_, ?_⟩
        · simpa only [NamedReceipt.processed, decide_eq_false_iff_not] using hfresh
        · simpa only [NamedReceipt.processed, decide_eq_true_eq] using hheld
      exact ⟨B, rfl, i, t, haccept, hhi⟩

/-- Public core wrapper for seed-abstract proposal-admission ports. -/
theorem proposedBlock_admittedBefore_vote_of_fgRootRead_named_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} (hs : 0 < s) (hprop : S.E.proposer s ∈ rho.honest)
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.vote_time S.E s ≤ rho.horizon)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B)
    {v : V} (hv : v ∈ rho.honest)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v
          (Protocol.vote_time S.E s)).core.toHealing.toFG) B.erase) :
    AdmittedBefore S rho v B.erase (Protocol.vote_time S.E s) :=
  proposedBlock_admittedBefore_vote_of_fgRootRead_named
    S adm hs hprop hpost hhor hB hv hroot

#print axioms proposedBlock_admittedBefore_vote_of_fgRootRead_named_core

/-- Every later honest weak-genesis proposal is admitted at each honest
prepared vote read. -/
theorem proposedBlock_admittedBefore_vote_of_gstZero_named
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {d : Slot} (hd : 1 ≤ d)
    (hhor : Protocol.vote_time S.E (d + 1) ≤ rho.horizon)
    (hprop : S.E.proposer (d + 1) ∈ rho.honest)
    {B : NamedBlock V} (hB : proposedBlockAt S rho (d + 1) = some B)
    {v : V} (hv : v ∈ rho.honest) :
    AdmittedBefore S rho v B.erase (Protocol.vote_time S.E (d + 1)) := by
  have hpost : S.E.t_GST ≤ Protocol.proposal_time S.E (d + 1) := by
    rw [h.gstZero]
    exact proposal_time_nonneg S.E (d + 1)
  let R := Protocol.get_fg_root
    (Internal.NamedRecoveryRead.voteDutyRead S rho v (d + 1)).st.core.toHealing.toFG
  have hdPos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
  have hconfHor : Protocol.confirmation_time S.E (d - 1) ≤ rho.horizon :=
    (confirmationTime_lt_nextVote_of_lt S.E
      (Nat.sub_lt hdPos (by decide))).le.trans hhor
  have hupper : d ≤ (d - 1) + 1 := by
    rw [Nat.sub_add_cancel hd]
  have hheads : ∀ x ∈ rho.honest,
      Block.Preceq R (voterHeadAt S rho x d) := by
    intro x hx
    simpa only [R, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      voteDutyHead] using
      fgRootAtRead_preceq_voteDutyHead_of_gstZero_named
        S h.core h.committees h.gstZero h.windows hconfHor
          hd hupper (t := Protocol.vote_time S.E (d + 1))
          (le_refl _) hv hx
  have hvotePrev : Protocol.vote_time S.E d ≤ rho.horizon :=
    (vote_time_mono_slots S.E (Nat.le_succ d)).trans hhor
  have hprotected : ProtectedVoteSlot S rho d R := by
    refine ⟨hheads, ?_⟩
    intro x hx hxCommittee
    obtain ⟨X, hXerase, hXrun, hXemit⟩ :=
      WeakGoldfish.voterHead_runBlock_and_emits
        S h.core hx hdPos hxCommittee hvotePrev
    exact ⟨X, by simpa only [hXerase] using hheads x hx, hXrun, hXemit⟩
  have hparent : Block.Preceq R (proposedParent S rho (d + 1)) :=
    protected_preceq_proposedParent_of_gstZero_named
      S h hconfHor hd hupper
        ((proposal_time_lt_vote_time S.E (d + 1)).le.trans hhor)
        hprop hprotected
  have hparentBlock : Block.Preceq (proposedParent S rho (d + 1)) B.erase :=
    proposedParent_preceq_proposedBlockAt S rho (d + 1) hB
  apply proposedBlock_admittedBefore_vote_of_fgRootRead_named
    S h.core (Nat.zero_lt_succ d) hprop hpost hhor hB hv
  simpa only [R, Internal.NamedRecoveryRead.voteDutyRead,
    NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
    Block.preceq_trans hparent hparentBlock

#print axioms proposedBlock_admittedBefore_vote_of_gstZero_named

end WeakGenesis
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
