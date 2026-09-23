module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ConePersistence
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryHandoffCore
public import DecoupledConsensusProofs.Generic.PostGSTCarrierAdmissionCore
public import DecoupledConsensusProofs.Generic.SuffixHistory
public import DecoupledConsensusProofs.Protocol.Schedule.PostHealingReuse
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeDelivery

@[expose] public section

/-!
# Post-healing confirmation continuation

This module reduces the post-healing event step to facts about the exact store
read by one confirmation evaluation. It does not reuse the GST-zero global
history predicate: an aligned boundary does not constrain every pre-boundary
honest target or confirmed head.

The named post-healing availability route now uses the exact prepared vote
read, named block witnesses, named root injectivity, and the settled delivery
and visibility producers. The strict/inclusive store identity, slot placement,
P4 specialization, round-transition guard, and continuation timing facts remain
available below.

The later suffix-endpoint and boundary-canonicality families remain archived
or blocked in their owning modules. This file does not import
`Availability/PostHealingBoundaryCanonicalityRun.lean`; the boundary module
keeps its own `_at` producer and imports this one.
-/



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution
open Internal.NamedRecoveryRead

variable {V : Type} [DecidableEq V] [Fintype V]



private theorem named_emittedHead_mem_voteDutyRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {x : V} (hx : x ∈ rho.honest) {s : Slot} {C : NamedBlock V}
    (hCrun : NamedRun.blockInRun S rho C)
    (hemit : NamedRun.emits S rho x
      (.gfVote ⟨x, s, C.erase.root⟩) (Protocol.vote_time S.E s)) :
    C.erase ∈ (voteDutyRead S rho x s).st.core.T := by
  let t := Protocol.vote_time S.E s
  obtain ⟨i, hi, hmem⟩ := hemit
  have hstate := Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hi
  change Object.gfVote ⟨x, s, C.erase.root⟩ ∈
    (on_tick_emit S x (rho.stateBefore S i x) (Protocol.vote_time S.E s)).2 at hmem
  rw [hstate] at hmem
  let pre := NamedRun.stateBeforeTime S rho t x
  let read := NamedActionReads.confirmationReadFrom S pre t
  let st := read.st.core
  let gc := NamedProfile.gradeContract read.cache
  let tree := Protocol.voter_filtered_block_tree S.E st st.s
  let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  let H := Protocol.get_head_in_tree_with_layer gc S.E S.hc st.toHealing
    tree votes support (st.s - 1)
  have hshape := Proofs.Optimistic.gfVote_emitted_shape S x pre t hmem
  have hrootH : H.root = C.erase.root := by
    have h := hshape.2.2.1
    simp only [Protocol.NamedDuties.goldfish_vote_with,
      Protocol.goldfish_vote_with] at h
    split at h
    · simpa only [H, Protocol.get_head_in_tree_with, tree, votes, support] using
        congrArg GoldfishVote.head (Option.some.inj h)
    · simp at h
  have hinvPre : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg pre.st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t x).1
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg read.st := by
    simpa only [read, pre, NamedActionReads.confirmationReadFrom] using
      Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg pre.st t hinvPre
  have hrootMem : Protocol.get_fg_root st.toHealing.toFG ∈ st.T :=
    Proofs.NamedStoreRoots.fg_root_mem read.st hinv.1.2
  have hanchorMem : Protocol.get_sg_root_with gc S.E S.hc
      st.toHealing (S.hc.round_of st.s) ∈ st.T := by
    exact Proofs.NamedConfirmationMembership.runtime_anchor_mem read.cache
      S.E S.hc st.toHealing (S.hc.round_of st.s) hrootMem
  have htree : tree ⊆ st.T := by
    dsimp only [tree]
    rw [← Proofs.Optimistic.voter_candidate_tree_eq_protocol_voter_filtered_block_tree]
    intro D hD
    simp only [Proofs.Optimistic.voter_candidate_tree,
      Protocol.get_filtered_block_tree_from,
      Protocol.viable_tree, Protocol.finalized_descendants,
      Protocol.viable, Protocol.voter_processed_block_tree,
      Finset.mem_filter, decide_eq_true_eq] at hD
    exact hD.1.1.1.1
  have hHmem : H ∈ st.T := by
    dsimp only [H]
    rw [Proofs.Optimistic.get_head_in_tree_split_with]
    exact Proofs.Records.ghost_mem_of _ _ hanchorMem htree
  have hHpre : H ∈ pre.st.core.T := by
    simpa only [read, st, NamedActionReads.confirmationReadFrom] using hHmem
  obtain ⟨D, hDhead, hDrun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
      adm.toNamedScheduleWellFormed hx t hHpre
  have hDroot : D.root = C.root := by
    rw [← Proofs.NamedWire.erase_root D, hDhead, hrootH, Proofs.NamedWire.erase_root C]
  have hDC : D = C :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective D C
      hDrun hCrun D C (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self C)) hDroot
  have hChead : C.erase = H := by
    simpa only [hDC] using hDhead
  rw [hChead]
  simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom, read, pre, t] using hHmem

/-! ## Finalized-root floor at the confirmation read -/

/-- A later confirmation store whose FG root is below `B` pins the receiver's
finalized root below `B` at every earlier delivery before the support cutoff. -/
theorem finalized_preceq_at_delivery_of_confRoot_preceq
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} {v : V} {B : Block V} {X : NamedBlock V}
    (hroot : Block.Preceq
      (confRoot (Proofs.Optimistic.confStore S rho v s)) B)
    {i : Nat} {t : Time}
    (hi : rho.events[i]? = some (Event.deliver v (Object.block X) t))
    (hlt : t < Protocol.support_cutoff S.E s) :
    Block.Preceq (rho.stateBefore S i v).st.F B := by
  let Gamma := Protocol.confirmation_time S.E s
  let n := (rho.events.filter (fun e => decide (e.time < Gamma))).length
  have hiN : i < n := by
    by_contra hnot
    have hni : n ≤ i := Nat.le_of_not_gt hnot
    have hGamma : Gamma ≤ t :=
      Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed
        (t := Gamma) (j := i) (e := Event.deliver v (Object.block X) t)
        (by simpa only [n] using hni) hi
    exact (not_le_of_gt
      (lt_of_lt_of_le hlt (support_cutoff_le_confirmation_time S.E s))) hGamma
  let pre := rho.storeBeforeTime S v Gamma
  have hmono : Block.Preceq (rho.stateBefore S i v).st.F pre.F := by
    have hprefix := stateBefore_F_mono S rho v (Nat.le_of_lt hiN)
    have hstore : pre = (rho.stateBefore S n v).st :=
      congrArg NamedNodeState.st
        (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S
          adm.toNamedScheduleWellFormed Gamma) v)
    simpa only [hstore] using hprefix
  have hFJ : Block.Preceq pre.F pre.J :=
    (Proofs.NamedJustificationBound.storeFinality_stateBeforeTime S rho Gamma v).2
  have hFroot : Block.Preceq pre.F
      (Protocol.get_fg_root pre.toHealing.toFG) :=
    Proofs.Records.preceq_get_fg_root_of_F (st := pre.toHealing.toFG) hFJ
  have hroot' : Block.Preceq
      (Protocol.get_fg_root pre.toHealing.toFG) B := by
    simpa only [confRoot, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore, pre]
      using hroot
  exact Block.preceq_trans hmono (Block.preceq_trans hFroot hroot')

/-! ## earlier post-healing availability theorem -/

/-- A post-GST honest-vote cone and the later P4 root floor make every honest
head available before the slot's support cutoff. -/
theorem honestHeadsAvailableBefore_of_postHealingCone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} {v : V} (hv : v ∈ rho.honest)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.support_cutoff S.E s ≤ rho.horizon)
    {B : Block V}
    (hroot : Block.Preceq
      (confRoot (Proofs.Optimistic.confStore S rho v s)) B)
    (hvotes : Proofs.HealingSurface.NamedHonestVotesCone S rho s
      (fun X => Block.Preceq B X)) :
    HonestHeadsAvailableBefore S rho s v
      (Protocol.support_cutoff S.E s) := by
  intro X hhead
  by_cases hgen : X = Block.genesis
  · exact Or.inl hgen
  right
  obtain ⟨x, hx, hcommittee, ⟨C, hCX, hCrun⟩, hXemit⟩ := hhead
  have hCemit : NamedRun.emits S rho x
      (.gfVote ⟨x, s, C.erase.root⟩) (Protocol.vote_time S.E s) := by
    simpa only [hCX] using hXemit
  have hCmem := named_emittedHead_mem_voteDutyRead S adm hx hCrun hCemit
  have hXmem : X ∈ (voteDutyRead S rho x s).st.core.T := by
    simpa only [hCX] using hCmem
  obtain ⟨Y, hBY, hYrun, hYemit⟩ := hvotes x hx hcommittee
  have hvoteEq : (⟨x, s, X.root⟩ : GoldfishVote V) =
      ⟨x, s, Y.erase.root⟩ :=
    Proofs.Optimistic.emits_gfVote_unique S adm.toNamedScheduleWellFormed
      hXemit hYemit rfl
  have hrootXY : X.root = Y.erase.root :=
    congrArg GoldfishVote.head hvoteEq
  have hrootNamed : C.root = Y.root := by
    rw [← Proofs.NamedWire.erase_root C, ← Proofs.NamedWire.erase_root Y, hCX]
    exact hrootXY
  have hCY : C = Y :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective C Y
      hCrun hYrun C Y (Or.inl (Proofs.NamedAncestry.named_self C))
      (Or.inr (Proofs.NamedAncestry.named_self Y)) hrootNamed
  have hBX : Block.Preceq B C.erase := by
    rw [hCY]
    exact hBY
  obtain ⟨n, hn, hbefore⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed (Protocol.vote_time S.E s)
  have hXtime : X ∈
      (rho.stateBeforeTime S (Protocol.vote_time S.E s) x).st.core.T := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using hXmem
  have hXn : X ∈ (rho.stateBefore S n x).st.core.T := by
    rw [← hn]
    exact hXtime
  have hCxn : C.erase ∈ (rho.stateBefore S n x).st.core.T := by
    simpa only [hCX] using hXn
  obtain ⟨D, hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n x hCxn
  have hDrun := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hx n hDbody)
  have hrootCD : C.root = D.root := by
    calc
      C.root = C.erase.root := (Proofs.NamedWire.erase_root C).symm
      _ = D.erase.root := (congrArg Block.root hDerase).symm
      _ = D.root := Proofs.NamedWire.erase_root D
  have hCD : C = D :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective C D
      hCrun hDrun C D (Or.inl (Proofs.NamedAncestry.named_self C))
      (Or.inr (Proofs.NamedAncestry.named_self D)) hrootCD
  have hCbody : C ∈ (rho.stateBefore S n x).st.bodies := by
    rw [hCD]
    exact hDbody
  have hprocessed : Object.processed (rho.stateBefore S n x).st
      (Object.block C) = true := by
    simpa only [Object.processed, NamedReceipt.processed,
      decide_eq_true_eq] using hCbody
  rcases acceptsAt_block_of_processed S rho x n C hprocessed with
    hgen' | ⟨j, hjn, t, hacc⟩
  · have hXgen : X = Block.genesis := by
      rw [← hCX, hgen']
      rfl
    exact False.elim (hgen hXgen)
  · obtain ⟨-, e, he, -, het⟩ := hacc.1
    have ht : t < Protocol.vote_time S.E s := by
      rw [← het]
      exact hbefore j e hjn he
    have hCposErase : 0 < C.erase.slot :=
      Nat.zero_lt_of_lt (parent_slot_lt_of_acceptsAt_block S hacc)
    have hCpos : 0 < C.slot := by
      simpa only [Proofs.NamedWire.erase_slot] using hCposErase
    rw [← hCX]
    apply Protocol.block_admittedBefore_of_accepted_after_cutoff
      S adm hx hv hCpos hacc ht hpost
        (Proofs.Optimistic.vote_time_add_delta S.E s) hhor
    intro k hk
    have hkConf := hk.trans (Proofs.strict_filter_length_mono rho
      (support_cutoff_le_confirmation_time S.E s))
    have hroot' : Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S v (Protocol.confirmation_time S.E s)).toHealing.toFG)
          B := by
      simpa only [confRoot, Proofs.Optimistic.confStore,
        Proofs.Optimistic.tickStore] using hroot
    exact Block.preceq_trans
      (Proofs.finalized_preceq_at_prefix_of_storeBeforeRoot_preceq
        S rho adm.toNamedScheduleWellFormed.sorted hroot' hkConf) hBX

/-! ## Confirmation-store resolution -/

/-- The post-GST cone resolves every honest head in the exact confirmation
store. -/
theorem headsResolveIn_confStore_of_postHealingCone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} {v : V} (hv : v ∈ rho.honest)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.support_cutoff S.E s ≤ rho.horizon)
    {B : Block V}
    (hroot : Block.Preceq
      (confRoot (Proofs.Optimistic.confStore S rho v s)) B)
    (hvotes : Proofs.HealingSurface.NamedHonestVotesCone S rho s
      (fun X => Block.Preceq B X)) :
    Proofs.Optimistic.HeadsResolveIn S rho s
      (Proofs.Optimistic.confStore S rho v s).T
      (Proofs.Optimistic.confStore S rho v s).timestamp_block := by
  exact headsResolveIn_confStore_of_availableBefore S adm hv s
    (honestHeadsAvailableBefore_of_postHealingCone
      S adm hv hpost hhor hroot hvotes)

/-! ## Proposal-duty resolution -/

private theorem support_cutoff_lt_proposal_time_succ_local
    (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s < Protocol.proposal_time E (s + 1) := by
  unfold Protocol.support_cutoff Protocol.proposal_time Env.t slotStart
  push_cast
  have h : 2 * E.Δ < 4 * E.Δ :=
    Int.mul_lt_mul_of_pos_right (by decide) E.Δ_pos
  calc
    4 * E.Δ * (s : Time) + 2 * E.Δ <
        4 * E.Δ * (s : Time) + 4 * E.Δ := Int.add_lt_add_left h _
    _ = 4 * E.Δ * ((s : Time) + 1) := by ring

private theorem finalized_preceq_at_delivery_of_proposerRoot_preceq
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} {B : Block V} {X : NamedBlock V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (proposerDutyStore S rho (s + 1)).toHealing.toFG) B)
    {i : Nat} {t : Time}
    (hi : rho.events[i]? = some
      (Event.deliver (S.E.proposer (s + 1)) (Object.block X) t))
    (hlt : t < Protocol.support_cutoff S.E s) :
    Block.Preceq
      (rho.stateBefore S i (S.E.proposer (s + 1))).st.F B := by
  let Gamma := Protocol.proposal_time S.E (s + 1)
  let n := (rho.events.filter (fun e => decide (e.time < Gamma))).length
  have hiN : i < n := by
    by_contra hnot
    have hni : n ≤ i := Nat.le_of_not_gt hnot
    have hGamma : Gamma ≤ t :=
      Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed
        (t := Gamma) (j := i)
        (e := Event.deliver (S.E.proposer (s + 1)) (Object.block X) t)
        (by simpa only [n] using hni) hi
    exact (not_le_of_gt
      (lt_trans hlt (support_cutoff_lt_proposal_time_succ_local S.E s))) hGamma
  let pre := rho.storeBeforeTime S (S.E.proposer (s + 1)) Gamma
  have hmono : Block.Preceq
      (rho.stateBefore S i (S.E.proposer (s + 1))).st.F pre.F := by
    have hprefix := stateBefore_F_mono S rho (S.E.proposer (s + 1))
      (Nat.le_of_lt hiN)
    have hstore : pre =
        (rho.stateBefore S n (S.E.proposer (s + 1))).st :=
      congrArg NamedNodeState.st
        (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S
          adm.toNamedScheduleWellFormed Gamma) (S.E.proposer (s + 1)))
    simpa only [hstore] using hprefix
  have hFJ : Block.Preceq pre.F pre.J :=
    (Proofs.NamedJustificationBound.storeFinality_stateBeforeTime S rho Gamma
      (S.E.proposer (s + 1))).2
  have hFroot : Block.Preceq pre.F
      (Protocol.get_fg_root pre.toHealing.toFG) :=
    Proofs.Records.preceq_get_fg_root_of_F (st := pre.toHealing.toFG) hFJ
  have hroot' : Block.Preceq
      (Protocol.get_fg_root pre.toHealing.toFG) B := by
    simpa only [proposerDutyStore, Proofs.Optimistic.tickStore, pre, Gamma] using hroot
  exact Block.preceq_trans hmono (Block.preceq_trans hFroot hroot')

private theorem honestHeadsAvailableBefore_of_proposerDutyPostHealingCone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot}
    (hprop : S.E.proposer (s + 1) ∈ rho.honest)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.support_cutoff S.E s ≤ rho.horizon)
    {B : Block V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (proposerDutyStore S rho (s + 1)).toHealing.toFG) B)
    (hvotes : Proofs.HealingSurface.NamedHonestVotesCone S rho s
      (fun X => Block.Preceq B X)) :
    HonestHeadsAvailableBefore S rho s (S.E.proposer (s + 1))
      (Protocol.support_cutoff S.E s) := by
  let v := S.E.proposer (s + 1)
  have hv : v ∈ rho.honest := by simpa only [v] using hprop
  intro X hhead
  by_cases hgen : X = Block.genesis
  · exact Or.inl hgen
  right
  obtain ⟨x, hx, hcommittee, ⟨C, hCX, hCrun⟩, hXemit⟩ := hhead
  have hCemit : NamedRun.emits S rho x
      (.gfVote ⟨x, s, C.erase.root⟩) (Protocol.vote_time S.E s) := by
    simpa only [hCX] using hXemit
  have hCmem := named_emittedHead_mem_voteDutyRead S adm hx hCrun hCemit
  have hXmem : X ∈ (voteDutyRead S rho x s).st.core.T := by
    simpa only [hCX] using hCmem
  obtain ⟨Y, hBY, hYrun, hYemit⟩ := hvotes x hx hcommittee
  have hvoteEq : (⟨x, s, X.root⟩ : GoldfishVote V) =
      ⟨x, s, Y.erase.root⟩ :=
    Proofs.Optimistic.emits_gfVote_unique S adm.toNamedScheduleWellFormed
      hXemit hYemit rfl
  have hrootXY : X.root = Y.erase.root :=
    congrArg GoldfishVote.head hvoteEq
  have hrootNamed : C.root = Y.root := by
    rw [← Proofs.NamedWire.erase_root C, ← Proofs.NamedWire.erase_root Y, hCX]
    exact hrootXY
  have hCY : C = Y :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective C Y
      hCrun hYrun C Y (Or.inl (Proofs.NamedAncestry.named_self C))
      (Or.inr (Proofs.NamedAncestry.named_self Y)) hrootNamed
  have hBX : Block.Preceq B C.erase := by
    rw [hCY]
    exact hBY
  obtain ⟨n, hn, hbefore⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed (Protocol.vote_time S.E s)
  have hXtime : X ∈
      (rho.stateBeforeTime S (Protocol.vote_time S.E s) x).st.core.T := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using hXmem
  have hXn : X ∈ (rho.stateBefore S n x).st.core.T := by
    rw [← hn]
    exact hXtime
  have hCxn : C.erase ∈ (rho.stateBefore S n x).st.core.T := by
    simpa only [hCX] using hXn
  obtain ⟨D, hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n x hCxn
  have hDrun := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hx n hDbody)
  have hrootCD : C.root = D.root := by
    calc
      C.root = C.erase.root := (Proofs.NamedWire.erase_root C).symm
      _ = D.erase.root := (congrArg Block.root hDerase).symm
      _ = D.root := Proofs.NamedWire.erase_root D
  have hCD : C = D :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective C D
      hCrun hDrun C D (Or.inl (Proofs.NamedAncestry.named_self C))
      (Or.inr (Proofs.NamedAncestry.named_self D)) hrootCD
  have hCbody : C ∈ (rho.stateBefore S n x).st.bodies := by
    rw [hCD]
    exact hDbody
  have hprocessed : Object.processed (rho.stateBefore S n x).st
      (Object.block C) = true := by
    simpa only [Object.processed, NamedReceipt.processed,
      decide_eq_true_eq] using hCbody
  rcases acceptsAt_block_of_processed S rho x n C hprocessed with
    hgen' | ⟨j, hjn, t, hacc⟩
  · have hXgen : X = Block.genesis := by
      rw [← hCX, hgen']
      rfl
    exact False.elim (hgen hXgen)
  · obtain ⟨-, e, he, -, het⟩ := hacc.1
    have ht : t < Protocol.vote_time S.E s := by
      rw [← het]
      exact hbefore j e hjn he
    have hCposErase : 0 < C.erase.slot :=
      Nat.zero_lt_of_lt (parent_slot_lt_of_acceptsAt_block S hacc)
    have hCpos : 0 < C.slot := by
      simpa only [Proofs.NamedWire.erase_slot] using hCposErase
    rw [← hCX]
    apply Protocol.block_admittedBefore_of_accepted_after_cutoff
      S adm hx hv hCpos hacc ht hpost
        (Proofs.Optimistic.vote_time_add_delta S.E s) hhor
    intro k hk
    have hkProposal := hk.trans (Proofs.strict_filter_length_mono rho
      (support_cutoff_lt_proposal_time_succ_local S.E s).le)
    have hroot' : Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S (S.E.proposer (s + 1))
            (Protocol.proposal_time S.E (s + 1))).toHealing.toFG) B := by
      simpa only [proposerDutyStore, Proofs.Optimistic.tickStore] using hroot
    exact Block.preceq_trans
      (Proofs.finalized_preceq_at_prefix_of_storeBeforeRoot_preceq
        S rho adm.toNamedScheduleWellFormed.sorted hroot' hkProposal) hBX

theorem headsResolveIn_proposerDutyStore_of_postHealingCone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot}
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.support_cutoff S.E s ≤ rho.horizon)
    (hprop : S.E.proposer (s + 1) ∈ rho.honest)
    {B : Block V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (proposerDutyStore S rho (s + 1)).toHealing.toFG) B)
    (hvotes : Proofs.HealingSurface.NamedHonestVotesCone S rho s
      (fun X => Block.Preceq B X)) :
    Proofs.Optimistic.HeadsResolveIn S rho s
      (proposerDutyStore S rho (s + 1)).T
      (proposerDutyStore S rho (s + 1)).timestamp_block := by
  have havailable := honestHeadsAvailableBefore_of_proposerDutyPostHealingCone
    S adm hprop hpost hhor hroot hvotes
  have hresolve := headsResolveIn_storeBeforeTime_of_availableBefore_at
    S adm hprop s (support_cutoff_lt_proposal_time_succ_local S.E s).le havailable
  simpa only [proposerDutyStore, Proofs.Optimistic.tickStore] using hresolve

#print axioms headsResolveIn_proposerDutyStore_of_postHealingCone

/-! ## P4 facts at the exact pre-confirmation store -/











/-- From the second later slot onward, proposal duties are also strictly after
the healed action. -/
theorem action_lt_proposal_time_two_after
    (S : Setup V) (r : Round) :
    S.a r < Protocol.proposal_time S.E (S.hc.opening_slot r + 2) := by
  unfold Setup.a Protocol.HealConfig.a Protocol.proposal_time Env.t slotStart
  push_cast
  have hd := S.E.Δ_pos
  ring_nf
  have h : S.E.Δ * 6 < S.E.Δ * 8 :=
    Int.mul_lt_mul_of_pos_left (show (6 : Int) < 8 by omega) hd
  exact Int.add_lt_add_right h _


end Protocol
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Protocol
#print axioms finalized_preceq_at_delivery_of_confRoot_preceq
#print axioms honestHeadsAvailableBefore_of_postHealingCone
#print axioms headsResolveIn_confStore_of_postHealingCone
end DecoupledConsensusModel.Protocol

end
