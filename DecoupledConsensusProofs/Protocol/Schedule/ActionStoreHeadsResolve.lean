module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Head.WeakActionReadCore
public import DecoupledConsensusProofs.Protocol.Schedule.GSTZeroHeadResolution
public import DecoupledConsensusProofs.Generic.PostGSTCarrierAdmissionCore
public import DecoupledConsensusProofs.Generic.PostGSTCarrierAdmission
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.Wire

@[expose] public section

/-!
# Post-healing head resolution in the exact action store

The action read is the store immediately after the confirmation write at its
scheduled time. Its tree and block timestamps are the strict pre-time fields,
so the post-GST vote cone can be resolved directly in that read.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakAction

open Internal Execution Internal.NamedRecoveryRead Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem honestHeadsAvailableBefore_of_actionStorePostHealingCone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Slot} {v : V} (hv : v ∈ rho.honest)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E q)
    (hhor : Protocol.support_cutoff S.E q ≤ rho.horizon)
    {r : Round} (ha : S.a r = Protocol.support_cutoff S.E q)
    {B : Block V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (actionStoreAt S rho v r).toHealing.toFG) B)
    (hvotes : NamedHonestVotesCone S rho q
      (fun X => Block.Preceq B X)) :
    HonestHeadsAvailableBefore S rho q v
      (Protocol.support_cutoff S.E q) := by
  let Gamma := Protocol.support_cutoff S.E q
  let pre := rho.storeBeforeTime S v (S.a r)
  have hrootPre : Block.Preceq
      (Protocol.get_fg_root pre.toHealing.toFG) B := by
    change Block.Preceq
      (Protocol.get_fg_root pre.toHealing.toFG) B at hroot
    exact hroot
  intro X hhead
  by_cases hgen : X = Block.genesis
  · exact Or.inl hgen
  right
  obtain ⟨x, hx, hcommittee, ⟨C, hCX, hCrun⟩, hXemit⟩ := hhead
  have hCemit : NamedRun.emits S rho x
      (.gfVote ⟨x, q, C.erase.root⟩) (Protocol.vote_time S.E q) := by
    simpa only [hCX] using hXemit
  have hCmem := Protocol.emittedHead_mem_voteDutyStore S adm hx hCrun hCemit
  have hXmem : X ∈ (voteDutyRead S rho x q).st.core.T := by
    simpa only [hCX] using hCmem
  obtain ⟨Y, hBY, hYrun, hYemit⟩ := hvotes x hx hcommittee
  have hvoteEq : (⟨x, q, X.root⟩ : GoldfishVote V) =
      ⟨x, q, Y.erase.root⟩ :=
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
    S adm.toNamedScheduleWellFormed (Protocol.vote_time S.E q)
  have hXtime : X ∈
      (rho.storeBeforeTime S x (Protocol.vote_time S.E q)).T := by
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
    have ht : t < Protocol.vote_time S.E q := by
      rw [← het]
      exact hbefore j e hjn he
    have hCposErase : 0 < C.erase.slot :=
      Nat.zero_lt_of_lt (parent_slot_lt_of_acceptsAt_block S hacc)
    have hCpos : 0 < C.slot := by
      simpa only [Proofs.NamedWire.erase_slot] using hCposErase
    rw [← hCX]
    apply Protocol.block_admittedBefore_of_accepted_after_cutoff
      S adm hx hv hCpos hacc ht hpost
        (Proofs.Optimistic.vote_time_add_delta S.E q) hhor
    intro k hk
    rw [← ha] at hk
    exact Block.preceq_trans
      (finalized_preceq_at_prefix_of_storeBeforeRoot_preceq S rho
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted hrootPre hk) hBX

theorem headsResolveIn_actionStore_of_postHealingCone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Slot} {v : V} (hv : v ∈ rho.honest)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E q)
    (hhor : Protocol.support_cutoff S.E q ≤ rho.horizon)
    {r : Round} (ha : S.a r = Protocol.support_cutoff S.E q)
    {B : Block V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (actionStoreAt S rho v r).toHealing.toFG) B)
    (hvotes : NamedHonestVotesCone S rho q
      (fun X => Block.Preceq B X)) :
    HeadsResolveIn S rho q (actionStoreAt S rho v r).T
      (actionStoreAt S rho v r).timestamp_block := by
  have havailable := honestHeadsAvailableBefore_of_actionStorePostHealingCone
    S adm hv hpost hhor ha hroot hvotes
  have hresolve := Protocol.headsResolveIn_storeBeforeTime_of_availableBefore_at
    (S := S) (rho := rho) (adm := adm) (v := v) (hv := hv) (s := q)
      (Gamma := S.a r) (by rw [ha]) havailable
  exact hresolve.of_eq (actionStoreAt_T S rho v r)
    (actionStoreAt_timestamp_block S rho v r)

#print axioms headsResolveIn_actionStore_of_postHealingCone

end WeakAction
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
