module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ExcludesRefute
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalPivot
public import DecoupledConsensusProofs.Protocol.Handlers.RelayGuards

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Exact prepared selection of the first honest genesis proposal -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakGenesis

open Internal Execution Protocol Proofs.Optimistic Proofs.HealingLemmas Statements

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem finalizedBeforeEvent_preceq_of_fgRootRead_local
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

private theorem processes_proposedBlock_before_vote_after_gst_local
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

private theorem acceptsAt_proposedBlock_named_local
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

private theorem proposedBlock_admittedBefore_vote_of_fgRootRead_local
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
  obtain ⟨isource, hsource⟩ := acceptsAt_proposedBlock_named_local
    S adm hs hprop ((proposal_time_lt_vote_time S.E s).le.trans hhor) hB
  by_cases hvp : v = S.E.proposer s
  · subst v
    exact ⟨B, rfl, isource, Protocol.proposal_time S.E s, hsource,
      proposal_time_lt_vote_time S.E s⟩
  · obtain ⟨t, hlo, hhi, hproc⟩ :=
      processes_proposedBlock_before_vote_after_gst_local
        S adm hs hprop hpost hhor hB hv hroot
    rcases hproc with hemits | ⟨i, hi⟩
    · have hshape := emits_block_shape S rho hemits
      have hslot : B.slot = s := proposedBlockAt_slot S rho s hB
      have heq : S.E.proposer s = v := by
        rw [← hslot]
        exact hshape.2.2
      exact absurd heq.symm hvp
    · have hroot' : Block.Preceq
          (Protocol.get_fg_root
            (rho.storeBeforeTime S v
              (Protocol.vote_time S.E s)).core.toHealing.toFG) B.erase := hroot
      have hF := finalizedBeforeEvent_preceq_of_fgRootRead_local
        S adm hi hhi hroot'
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

private theorem block_eq_genesis_of_mem_stateBefore_slot_zero
    (S : Setup V) (rho : Run V) (v : V) (n : Nat) {C : Block V}
    (hC : C ∈ (rho.stateBefore S n v).st.core.T) (hslot : C.slot = 0) :
    C = Block.genesis := by
  rcases Protocol.acceptsAt_block_of_processed_erased S rho v n hC with
    hgen | ⟨D, hDC, i, hi, t, hacc⟩
  · exact hgen
  · have hparent := Protocol.parent_slot_lt_of_acceptsAt_block S hacc
    have hbad : C.parent.slot < 0 := by
      rw [hDC, hslot] at hparent
      exact hparent
    exact False.elim ((Nat.not_lt_zero _) hbad)

private theorem block_eq_genesis_of_mem_before_proposal_one_named
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} {C : Block V}
    (hC : C ∈ (rho.storeBeforeTime S v
      (Protocol.proposal_time S.E 1)).core.T) :
    C = Block.genesis := by
  have hslotLt := Proofs.NamedSlotFreshness.block_slot_lt_of_mem_before_proposal
    S adm (s := 1) (by decide) hC
  have hslot : C.slot = 0 := Nat.le_zero.mp (Nat.lt_succ_iff.mp hslotLt)
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed (Protocol.proposal_time S.E 1)
  have hCn : C ∈ (rho.stateBefore S n v).st.core.T := by
    simpa only [Run.storeBeforeTime, hn] using hC
  exact block_eq_genesis_of_mem_stateBefore_slot_zero S rho v n hCn hslot

private theorem proposedParent_eq_genesis_one_named
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho) :
    proposedParent S rho 1 = Block.genesis := by
  apply block_eq_genesis_of_mem_before_proposal_one_named S adm
  simpa only [proposerReadAt, NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      proposedParent_mem S rho 1

private theorem mem_voteRead_one_eq_genesis_or_proposal
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hhor : Protocol.vote_time S.E 1 ≤ rho.horizon)
    (hprop : S.E.proposer 1 ∈ rho.honest)
    {B : NamedBlock V} (hB : proposedBlockAt S rho 1 = some B)
    {v : V} {C : Block V}
    (hC : C ∈ (Internal.NamedRecoveryRead.voteDutyRead S rho v 1).st.core.T) :
    C = Block.genesis ∨ C = B.erase := by
  have hCstore : C ∈ (Proofs.Optimistic.voteDutyStore S rho v 1).T := by
    simpa only [Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using hC
  have hslotLe := block_slot_le_of_mem_voteStore_core S adm hCstore
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed (Protocol.vote_time S.E 1)
  have hCn : C ∈ (rho.stateBefore S n v).st.core.T := by
    simpa only [Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Run.storeBeforeTime, hn] using hC
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hslotLe with hslot | hslot
  · exact Or.inl
      (block_eq_genesis_of_mem_stateBefore_slot_zero S rho v n hCn hslot)
  · right
    obtain ⟨i, -, hBbody⟩ := proposedBlockAt_mem_bodies_after_tick_of_admissible
      S adm 1 (by decide) hprop
        ((proposal_time_lt_vote_time S.E 1).le.trans hhor) hB
    have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho (i + 1)
      (S.E.proposer 1)).1.1.1
    have hBtree : B.erase ∈
        (rho.stateBefore S (i + 1) (S.E.proposer 1)).st.core.T := by
      rw [hcoh.1]
      exact Finset.mem_image_of_mem NamedBlock.erase hBbody
    exact unique_slot_block_in_store_core S adm (by decide) hprop
      hCn hBtree hslot (by rw [Proofs.NamedWire.erase_slot,
        proposedBlockAt_slot S rho 1 hB])

/-- At slot one every honest prepared vote store selects the bound proposal. -/
theorem honestVoteStoresExtend_one_of_gstZero_named
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    (hhor : Protocol.confirmation_time S.E 1 ≤ rho.horizon)
    (hprop : S.E.proposer 1 ∈ rho.honest)
    {B : NamedBlock V} (hB : proposedBlockAt S rho 1 = some B) :
    ∀ v ∈ rho.honest,
      Proofs.Optimistic.NamedVoteStoreExtends S rho v 1
        (namedWalkTargetTree S rho 1 v B)
        (proposedParent S rho 1) B := by
  intro v hv
  let read := Internal.NamedRecoveryRead.voteDutyRead S rho v 1
  let st := read.st.core
  let tree := voterCandidateTreeAt S rho v 1
  let tree₀ := namedWalkTargetTree S rho 1 v B
  have hvoteHor : Protocol.vote_time S.E 1 ≤ rho.horizon :=
    (vote_time_le_confirmation_time S.E 1).trans hhor
  have hparentGenesis : proposedParent S rho 1 = (Block.genesis : Block V) :=
    proposedParent_eq_genesis_one_named S h.core
  have hslot : B.slot = 1 := proposedBlockAt_slot S rho 1 hB
  have hslotErase : B.erase.slot = 1 := by
    rw [Proofs.NamedWire.erase_slot, hslot]
  have hcur : B.slot = st.s := by
    rw [hslot]
    symm
    simpa only [st, read] using Proofs.Optimistic.voteDutyRead_slot S rho v 1
  have hparent : B.erase.parent? = some (proposedParent S rho 1) := by
    obtain ⟨P, hP, hPerase⟩ := proposedBlockAt_parent S rho 1 hB
    simpa only [Proofs.NamedWire.erase_parent_optional, hP, Option.map_some, hPerase]
  have hanchorMem : voterAnchorAt S rho v 1 ∈ st.T := by
    exact Proofs.NamedConfirmationMembership.runtime_anchor_mem read.cache
      S.E S.hc st.toHealing (S.hc.round_of st.s)
      (Proofs.NamedStoreRoots.fg_root_mem read.st
        (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
          (Protocol.vote_time S.E 1) v).1.1.2)
  have hanchorCases : voterAnchorAt S rho v 1 = Block.genesis ∨
      voterAnchorAt S rho v 1 = B.erase :=
    mem_voteRead_one_eq_genesis_or_proposal S h.core hvoteHor hprop hB
      (by simpa only [st] using hanchorMem)
  have hanchorB : Block.Preceq (voterAnchorAt S rho v 1) B.erase := by
    rcases hanchorCases with ha | ha
    · rw [ha]
      exact Protocol.preceq_genesis _
    · rw [ha]
      exact Block.preceq_self _
  have hrootAnchor : Block.Preceq
      (Protocol.get_fg_root st.toHealing.toFG)
      (voterAnchorAt S rho v 1) := by
    exact NamedOutageClosure.fg_root_preceq_anchor S.E S.hc st.toHealing
      (S.hc.round_of st.s)
      (DecoupledConsensusModel.Protocol.readFrame read.cache st.toHealing
        (S.hc.round_of st.s)).g1
  have hrootB : Block.Preceq
      (Protocol.get_fg_root st.toHealing.toFG) B.erase :=
    Block.preceq_trans hrootAnchor hanchorB
  have hadmit : AdmittedBefore S rho v B.erase (Protocol.vote_time S.E 1) := by
    apply proposedBlock_admittedBefore_vote_of_fgRootRead_local
      S h.core (by decide) hprop
      (by rw [h.gstZero]; exact proposal_time_nonneg S.E 1)
      hvoteHor hB hv
    simpa only [st, read, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using hrootB
  have hBT : B.erase ∈ st.T := by
    have hmem := (admittedBefore_mem_and_stamp_at S
      h.core.toNamedScheduleWellFormed hadmit (le_refl _)).1
    simpa only [st, read, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using hmem
  have hprocessed : B.erase ∈ Protocol.voter_processed_block_tree S.E
      st.toHealing.toFG.toSG.toGoldfishStore st.s := by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    refine ⟨hBT, Or.inr ⟨B.erase, ?_, Block.preceq_self _⟩⟩
    exact ⟨hBT, hslotErase.trans (by
      symm
      simpa only [st, read] using Proofs.Optimistic.voteDutyRead_slot S rho v 1)⟩
  have hBrun : RunBlock S rho B :=
    proposedBlockAt_blockInRun_of_admissible S h.core 1 (by decide)
      hprop ((proposal_time_lt_vote_time S.E 1).le.trans hvoteHor) hB
  obtain ⟨B', hB'body, hB'erase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (Protocol.vote_time S.E 1) v (by
        simpa only [st, read, Internal.NamedRecoveryRead.voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using hBT)
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S h.core.toNamedScheduleWellFormed (Protocol.vote_time S.E 1)
  have hB'prefix : B' ∈ (rho.stateBefore S n v).st.bodies := by
    rw [← congrArg (fun world => (world v).st.bodies) hn]
    exact hB'body
  have hB'run : RunBlock S rho B' := Proofs.Bridges.runBlock_of_stateBefore_mem S hv hB'prefix
  have hB'eq : B' = B := by
    apply h.core.toNamedRootCollisionFree.root_injective B' B hB'run hBrun
      B' B (Or.inl (Proofs.NamedAncestry.named_self B'))
        (Or.inr (Proofs.NamedAncestry.named_self B))
    rw [← Proofs.NamedWire.erase_root B', ← Proofs.NamedWire.erase_root B, hB'erase]
  have hBbody : B ∈ (rho.stateBeforeTime S
      (Protocol.vote_time S.E 1) v).st.bodies := by
    rw [← hB'eq]
    exact hB'body
  have hBview : st.σ B.erase = Protocol.derive_named S.E S.cfg B := by
    simpa only [st, read, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho
        (Protocol.vote_time S.E 1) v B hBbody
  obtain ⟨D, hDbody, hDmax⟩ := Proofs.NamedStoreBridge.maximum_carrier_stateBeforeTime
    S rho (Protocol.vote_time S.E 1) v
  have hDT : D.erase ∈ st.T := by
    have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
      (Protocol.vote_time S.E 1) v).1.1.1
    have : D.erase ∈ (rho.stateBeforeTime S
        (Protocol.vote_time S.E 1) v).st.core.T := by
      rw [hcoh.1]
      exact Finset.mem_image_of_mem NamedBlock.erase hDbody
    simpa only [st, read, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using this
  have hDheight : (Protocol.derive_named S.E S.cfg D).h ≤
      (Protocol.derive_named S.E S.cfg B).h := by
    rcases mem_voteRead_one_eq_genesis_or_proposal S h.core hvoteHor hprop hB
      (by simpa only [st] using hDT) with hDgen | hDB
    · have hDeq : D = NamedBlock.genesis := by
        cases D <;> simp_all [NamedBlock.erase]
      rw [hDeq]
      change 1 ≤ (Protocol.derive_named S.E S.cfg B).h
      exact Protocol.one_le_derive_named_h S.E S.cfg B
    · have hDprefix : D ∈ (rho.stateBefore S n v).st.bodies := by
        rw [← congrArg (fun world => (world v).st.bodies) hn]
        exact hDbody
      have hDrun : RunBlock S rho D := Proofs.Bridges.runBlock_of_stateBefore_mem S hv hDprefix
      have hDeq : D = B := by
        apply h.core.toNamedRootCollisionFree.root_injective D B hDrun hBrun
          D B (Or.inl (Proofs.NamedAncestry.named_self D))
            (Or.inr (Proofs.NamedAncestry.named_self B))
        rw [← Proofs.NamedWire.erase_root D, ← Proofs.NamedWire.erase_root B, hDB]
      rw [hDeq]
  have hfrontier : st.h_max - 1 ≤ (st.σ B.erase).h := by
    rw [hBview]
    have hDmax' : (Protocol.derive_named S.E S.cfg D).h = st.h_max := by
      simpa only [st, read, Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using hDmax
    rw [← hDmax']
    exact (Nat.sub_le _ _).trans hDheight
  have hFJ : Block.Preceq st.F st.J := by
    simpa only [st, read, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        S rho (Protocol.vote_time S.E 1) v
  have hFB : Block.Preceq st.F B.erase :=
    Block.preceq_trans (Proofs.Records.preceq_get_fg_root_of_F
      (st := st.toHealing.toFG) hFJ) hrootB
  have hcandidate : B.erase ∈ tree := by
    change B.erase ∈ Protocol.get_filtered_block_tree_from
      st.toHealing.toFG
      (Protocol.voter_processed_block_tree S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
    simp only [Protocol.get_filtered_block_tree_from,
      Protocol.viable_tree, Protocol.finalized_descendants,
      Protocol.viable, Finset.mem_filter, decide_eq_true_eq]
    exact ⟨⟨⟨hprocessed, hFB⟩, B.erase, hprocessed,
      Block.preceq_self _, hfrontier⟩, hrootB⟩
  have hall : ∀ C ∈ tree₀, C = (Block.genesis : Block V) := by
    intro C hC
    have hCT : C ∈ st.T := by
      have hprocessedC := Proofs.Records.get_filtered_block_tree_from_subset
        st.toHealing.toFG
        (Protocol.voter_processed_block_tree S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
        (Finset.mem_of_mem_erase hC)
      exact (Finset.mem_filter.mp hprocessedC).1
    rcases mem_voteRead_one_eq_genesis_or_proposal S h.core hvoteHor hprop hB
      (by simpa only [st] using hCT) with hgen | hproposal
    · exact hgen
    · exact False.elim ((Finset.mem_erase.mp hC).1 hproposal)
  have htree : tree = insert B.erase tree₀ := by
    exact (Finset.insert_erase hcandidate).symm
  have hnotin : B.erase ∉ tree₀ := tree.notMem_erase B.erase
  have hleaf : ∀ C ∈ tree₀, C.parent? ≠ some B.erase := by
    intro C hC
    exact candidate_leaf_at_vote_core S h.core hslotErase C
      (Finset.mem_of_mem_erase hC)
  refine ⟨hcur, hparent, htree, hnotin, hleaf, ?_⟩
  change Protocol.get_head_in_tree_with_layer
      (NamedProfile.gradeContract read.cache) S.E S.hc st.toHealing tree
      (Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
      (Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
      (st.s - 1) = B.erase
  rw [Proofs.Optimistic.get_head_in_tree_split_with]
  rcases hanchorCases with hanchor | hanchor
  · rw [htree]
    apply Proofs.Optimistic.goldfish_fork_choice_insert_proposal
    · exact hparent
    · exact hslotErase.trans (by
        symm
        simpa only [st, read] using Proofs.Optimistic.voteDutyRead_slot S rho v 1)
    · exact hnotin
    · intro C hC hCparent
      rw [hparentGenesis, hall C hC] at hCparent
      simp [Block.parent?] at hCparent
    · exact hleaf
    · have hanchor' : Protocol.get_sg_root_with
          (NamedProfile.gradeContract read.cache) S.E S.hc st.toHealing
          (S.hc.round_of st.toHealing.s) = Block.genesis := by
        simpa only [voterAnchorAt, Internal.PhaseGrades.nodeAnchor,
          Internal.PhaseGrades.nodeRead,
          Protocol.get_sg_root_with, read, st, Protocol.Store.toHealing] using hanchor
      rw [hanchor', hparentGenesis, Protocol.goldfish_fork_choice]
      exact Protocol.ghost_eq_anchor_of_all_mem_eq
        Block.genesis tree₀ _ _ hall
  · have hanchor' : Protocol.get_sg_root_with
        (NamedProfile.gradeContract read.cache) S.E S.hc st.toHealing
        (S.hc.round_of st.toHealing.s) = B.erase := by
      simpa only [voterAnchorAt, Internal.PhaseGrades.nodeAnchor,
        Internal.PhaseGrades.nodeRead,
        Protocol.get_sg_root_with, read, st, Protocol.Store.toHealing] using hanchor
    rw [hanchor', Protocol.goldfish_fork_choice]
    apply Proofs.Optimistic.ghost_eq_of_compatible_anchor_and_terminal
      (show Block.compatible B.erase B.erase = true by
        simp [Block.compatible, Block.preceq_self])
    · intro _
      exact ghost_preceq _ _ _ _
    · intro _
      rfl
    · intro X hX hBX
      have hXtree : X ∈ Proofs.Optimistic.voter_candidate_tree S.E
          (Proofs.Optimistic.voteDutyStore S rho v 1).toHealing := by
        simpa only [tree, voterCandidateTreeAt,
          Internal.NamedRecoveryRead.voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock,
          Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore] using hX
      exact voter_candidate_tree_terminal_of_preceq_core
        S h.core hslotErase hXtree hBX

#print axioms honestVoteStoresExtend_one_of_gstZero_named

end WeakGenesis
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
