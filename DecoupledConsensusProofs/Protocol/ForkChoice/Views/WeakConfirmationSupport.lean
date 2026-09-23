module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.WeakGoldfishCone
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGCompatibleHistory
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryHandoffCore
public import DecoupledConsensusProofs.Protocol.Handlers.ConfirmationMembership
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

/-!
# Honest confirmation support under core admissibility

Every honest committee vote is represented in the late confirmation view.
A genuine strict-majority confirmation therefore has an honest supporter.
Its selected block is compatible with every block already protected by
all honest vote heads. This is the new-confirmation case of the joint fold.
No SG participation, grade, or finality fault bound is needed.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakGoldfish

open Internal Execution
open Internal.NamedRecoveryRead
open Proofs.Optimistic Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem voterHead_emits_of_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) {d : Slot} (hd : 0 < d)
    (hwCommittee : w ∈ S.E.committee d)
    (hhor : Protocol.vote_time S.E d ≤ rho.horizon) :
    NamedRun.emits S rho w
      (Object.gfVote ⟨w, d, (voterHeadAt S rho w d).root⟩)
      (Protocol.vote_time S.E d) := by
  let read := voteDutyRead S rho w d
  have hslot : read.st.core.s = d := voteDutyRead_slot S rho w d
  have hout :
      (Protocol.NamedDuties.goldfish_vote_with
        (NamedProfile.gradeContract read.cache)
        S.E S.hc (S.node w) read.st).2 =
          some ⟨(S.node w).val_index, read.st.core.s,
            (voterHeadAt S rho w d).root⟩ := by
    simp only [Protocol.NamedDuties.goldfish_vote_with,
      Protocol.goldfish_vote_with]
    rw [if_pos]
    · rfl
    · rw [S.node_val_index, hslot]
      exact hwCommittee
  have ho : Object.gfVote
      ⟨(S.node w).val_index, read.st.core.s,
        (voterHeadAt S rho w d).root⟩ ∈
      (on_tick_emit S w
        (NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E d) w)
        (Protocol.vote_time S.E d)).2 := by
    exact on_tick_emit_vote_mem S w
      (NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E d) w) d hd hout
  have hem := emits_of_on_tick_emit S adm.toNamedScheduleWellFormed hw
    (publicTime_vote_time S d) (vote_time_nonneg S.E d) hhor ho
  simpa only [S.node_val_index, hslot] using hem

private theorem voterHead_runBlock_of_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) (d : Slot) :
    ∃ H : NamedBlock V,
      H.erase = voterHeadAt S rho w d ∧ NamedRun.blockInRun S rho H := by
  let read := voteDutyRead S rho w d
  let st := read.st.core
  let tree := voterCandidateTreeAt S rho w d
  let H := voterHeadAt S rho w d
  have hinvPre : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E d) w).st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
      (Protocol.vote_time S.E d) w).1
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg read.st := by
    simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt] using
      Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ _ hinvPre
  have hroot : Protocol.get_fg_root st.toHealing.toFG ∈ st.T :=
    Proofs.NamedStoreRoots.fg_root_mem read.st hinv.1.2
  have hanchor : voterAnchorAt S rho w d ∈ st.T :=
    Proofs.NamedConfirmationMembership.runtime_anchor_mem read.cache
      S.E S.hc st.toHealing (S.hc.round_of st.s) hroot
  have htree : tree ⊆ st.T := by
    intro D hD
    have hprocessed := Proofs.Records.get_filtered_block_tree_from_subset
      st.toHealing.toFG
      (Protocol.voter_processed_block_tree S.E st.toHealing.toFG.toSG.toGoldfishStore st.s) hD
    exact (Finset.mem_filter.mp hprocessed).1
  have hHmem : H ∈ st.T := by
    rw [show H = Protocol.ghost (voterAnchorAt S rho w d) tree
        (Protocol.goldfish_score S.E st.T
          (Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (st.s - 1))
        (Protocol.goldfish_eligible S.E st.σ st.h_max st.T st.s
          (Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (st.s - 1)) by rfl]
    exact Proofs.Records.ghost_mem_of _ _ hanchor htree
  have hHpre : H ∈
      (NamedRun.stateBeforeTime S rho
        (Protocol.vote_time S.E d) w).st.core.T := by
    simpa only [read, st, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hHmem
  exact Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
    adm.toNamedScheduleWellFormed hw (Protocol.vote_time S.E d) hHpre

private theorem genuineConfirmation_exists_honestVoteSupporter_of_receipts
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {v : V} (hv : v ∈ rho.honest) {s : Slot} (hs : 0 < s) {B : Block V}
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hgenuine : GenuineConfirmationWith
      (NamedProfile.gradeContract (confirmationInputRead S rho v s).cache)
      S.E S.hc (confStore S rho v s) s B)
    (hreceipt : ∀ x ∈ S.E.committee s, x ∈ rho.honest →
      (⟨x, s, (voterHeadAt S rho x s).root⟩ : GoldfishVote V) ∈
        confLate S.E (confStore S rho v s) s) :
    ∃ x ∈ rho.honest, x ∈ S.E.committee s ∧
      Block.Preceq B (voterHeadAt S rho x s) := by
  let source := confStore S rho v s
  let late := confLate S.E source s
  let votes := confVotes S.E source s
  let supporters := Protocol.goldfishSupporters S.E source.T votes votes s B
  let participants := Protocol.participants S.E late s
  have hN := confNumerator S.E source s
  have hcut := support_cutoff_le_confirmation_time S.E s
  have hvoteHor : Protocol.vote_time S.E s ≤ rho.horizon :=
    (vote_time_le_confirmation_time S.E s).trans hhor
  have hrepresented : (S.E.committee s) ∩ rho.honest ⊆ participants := by
    intro x hx
    have hraw := hreceipt x (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hx).2
    simp only [participants, Protocol.participants, Protocol.raw_participants,
      Finset.mem_filter, Finset.mem_univ, true_and, Protocol.participates, decide_eq_true_eq]
    apply Finset.card_pos.mpr
    exact ⟨_, Finset.mem_filter.mpr ⟨hraw, rfl⟩⟩
  have hvalid : Protocol.VoteSetValid S.E s late := by
    simpa only [late, source, confStore, tickStore] using
      voteSetValid_confLate_stateBeforeTime S adm.toNamedScheduleWellFormed v
        (Protocol.confirmation_time S.E s) s
  have hsupportRep : supporters ⊆ participants :=
    supporters_subset_participants S.E source.T hN.subset_late s B
  have hex : ∃ x ∈ rho.honest, x ∈ supporters := by
    by_contra hnone
    have hdisjoint : Disjoint ((S.E.committee s) ∩ rho.honest) supporters := by
      apply Finset.disjoint_left.mpr
      intro x hx hsupp
      exact hnone ⟨x, (Finset.mem_inter.mp hx).2, hsupp⟩
    have hsum : ((S.E.committee s) ∩ rho.honest).card + supporters.card ≤
        participants.card := by
      rw [← Finset.card_union_of_disjoint hdisjoint]
      exact Finset.card_le_card (Finset.union_subset hrepresented hsupportRep)
    have hcount : participants.card ≤ (S.E.committee s).card :=
      voters_count_le_committee S.E late s hvalid
    have hmajority := hcom s
    have hgenuine' : GenuineConfirmation
        (contract := NamedProfile.gradeContract
          (confirmationInputRead S rho v s).cache)
        S.E S.hc (confStore S rho v s) s B :=
      ⟨hgenuine.selected, hgenuine.genuine⟩
    have hgate := hgenuine'.eligible
    rw [hN.score_eq_supporters] at hgate
    change participants.card < 2 * supporters.card at hgate
    omega
  obtain ⟨x, hxHon, hxSupport⟩ := hex
  obtain ⟨_, u, hu, hus, htargets⟩ := mem_supporters_iff.mp hxSupport
  have huval : u.val_index = x := (Finset.mem_filter.mp hu).2
  have hul : u ∈ late := hN.subset_late (Finset.mem_filter.mp hu).1
  have hxCommittee : x ∈ S.E.committee s := huval ▸ (hvalid u hul).2
  obtain ⟨H, hfind, hBH⟩ := targets_under_iff.mp htargets
  obtain ⟨n, hn, _⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed (Protocol.confirmation_time S.E s)
  have hpool : u ∈ (NamedRun.stateBefore S rho n v).st.gf_votes s := by
    have hpool' := (Finset.mem_filter.mp hul).1
    simpa only [late, source, confLate, confStore, tickStore,
      Protocol.NamedStore.pool, Protocol.Store.pool, List.mem_toFinset,
      Run.storeBeforeTime, hn] using hpool'
  obtain ⟨tu, huemit⟩ := Protocol.honestVote_emitted_of_mem_pool_stateBefore
    S adm v n s hpool (by rw [huval]; exact hxHon)
  rw [huval] at huemit
  have hxemit := voterHead_emits_of_core S adm hxHon hs hxCommittee hvoteHor
  have huEq : u = ⟨x, s, (voterHeadAt S rho x s).root⟩ :=
    Proofs.Optimistic.emits_gfVote_unique S adm.toNamedScheduleWellFormed
      huemit hxemit hus
  have hroot : H.root = (voterHeadAt S rho x s).root := by
    have h := Proofs.HealingLemmas.find?_root hfind
    simpa only [huEq] using h
  obtain ⟨D, hDerase, hDrun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
      adm.toNamedScheduleWellFormed hv (Protocol.confirmation_time S.E s) (by
        simpa only [source, confStore, tickStore] using
          Proofs.HealingLemmas.find?_mem hfind)
  obtain ⟨X, hXerase, hXrun⟩ := voterHead_runBlock_of_core S adm hxHon s
  have hrootNamed : D.root = X.root := by
    rw [← Proofs.NamedWire.erase_root D, ← Proofs.NamedWire.erase_root X, hDerase, hXerase]
    exact hroot
  have hDX : D = X := adm.toNamedRootCollisionFree.root_injective
    D X hDrun hXrun D X (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self X)) hrootNamed
  refine ⟨x, hxHon, hxCommittee, ?_⟩
  calc
    Block.Preceq B H := hBH.2
    _ = voterHeadAt S rho x s := by rw [← hDerase, hDX, hXerase]

/-- Every genuine post-GST confirmation has an honest same-slot vote supporter. -/
theorem genuineConfirmation_exists_honestVoteSupporter_after_gst
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {v : V} (hv : v ∈ rho.honest) {s : Slot} (hs : 0 < s) {B : Block V}
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hgenuine : GenuineConfirmationWith
      (NamedProfile.gradeContract (confirmationInputRead S rho v s).cache)
      S.E S.hc (confStore S rho v s) s B) :
    ∃ x ∈ rho.honest, x ∈ S.E.committee s ∧
      Block.Preceq B (voterHeadAt S rho x s) := by
  apply genuineConfirmation_exists_honestVoteSupporter_of_receipts
    S adm hcom hv hs hhor hgenuine
  intro x hx hxHon
  have hvoteHor : Protocol.vote_time S.E s ≤ rho.horizon :=
    (vote_time_le_confirmation_time S.E s).trans hhor
  have hemit := voterHead_emits_of_core S adm hxHon hs hx hvoteHor
  have hcut := support_cutoff_le_confirmation_time S.E s
  exact Protocol.gfVote_in_cutoff_view_after_gst S adm hxHon hs
    hpost hemit rfl hv _ _ hcut hcut (hcut.trans hhor)

/-- Delivery-parametric twin of
`genuineConfirmation_exists_honestVoteSupporter_after_gst`. -/
theorem genuineConfirmation_exists_honestVoteSupporter_of_delivery
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {cap : Time} (hdelivery : HonestDeliveryBefore S rho cap)
    (hcom : HonestCommittees S rho.honest)
    {v : V} (hv : v ∈ rho.honest) {s : Slot} (hs : 0 < s) {B : Block V}
    (hcap : Protocol.confirmation_time S.E s ≤ cap)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hgenuine : GenuineConfirmationWith
      (NamedProfile.gradeContract (confirmationInputRead S rho v s).cache)
      S.E S.hc (confStore S rho v s) s B) :
    ∃ x ∈ rho.honest, x ∈ S.E.committee s ∧
      Block.Preceq B (voterHeadAt S rho x s) := by
  apply genuineConfirmation_exists_honestVoteSupporter_of_receipts
    S adm hcom hv hs hhor hgenuine
  intro x hx hxHon
  have hvoteHor : Protocol.vote_time S.E s ≤ rho.horizon :=
    (vote_time_le_confirmation_time S.E s).trans hhor
  have hemit := voterHead_emits_of_core S adm hxHon hs hx hvoteHor
  have hcut := support_cutoff_le_confirmation_time S.E s
  exact Protocol.gfVote_in_cutoff_view_of_delivery S adm hdelivery hxHon hs
    hemit rfl hv _ _ hcut hcut (hcut.trans hcap)

/-- Prior protection of honest vote heads gives compatibility with each new confirmation. -/
theorem genuineConfirmation_compatible_of_priorProtectedHeads
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {v : V} (hv : v ∈ rho.honest) {s : Slot} (hs : 0 < s) {B C : Block V}
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hgenuine : GenuineConfirmationWith
      (NamedProfile.gradeContract (confirmationInputRead S rho v s).cache)
      S.E S.hc (confStore S rho v s) s B)
    (hprotected : ∀ x ∈ rho.honest, x ∈ S.E.committee s →
      Block.Preceq C (voterHeadAt S rho x s)) :
    Block.compatible C B = true := by
  obtain ⟨x, hxHon, hxCommittee, hBX⟩ :=
    genuineConfirmation_exists_honestVoteSupporter_after_gst S adm hcom hv hs hpost hhor hgenuine
  exact Block.compatible_of_preceq_common (hprotected x hxHon hxCommittee) hBX

#print axioms genuineConfirmation_exists_honestVoteSupporter_of_delivery

end WeakGoldfish
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
