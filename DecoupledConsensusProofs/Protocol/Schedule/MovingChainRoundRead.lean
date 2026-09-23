module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ExcludesRefute
public import DecoupledConsensusProofs.Execution.MovingChainIterate

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.NamedRecoveryRead
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. Round separation -/












/-! ## 2. Availability and membership at a round read

The same availability argument as at a vote read: one honest head of the slot
whose votes are already cast lies above the endpoint, it is available before
the support cutoff, and stores are parent-closed.

`storeBeforeTime_mem_stamp_of_cone` is public in `MovingChainBatchRun`, which
imports this module, so its body is reproduced here privately. -/




/-! ## 2b. Named availability at an arbitrary honest read

`WeakGoldfish.honestHeadsAvailableBefore_of_postHealingCone_atVoteDuty`
(`WeakGoldfishConeRun.lean:1820`) is the same statement with the root read at
the vote-duty store of slot `s + 1`. The root is used at exactly one place, to
bound the reader's finalized root at every delivery before the support cutoff,
and that step only needs the read to be at or after the cutoff. -/

/-- A later FG-root bound supplies the finalized-root guard at an earlier
event. Body of `WeakProposal.finalizedBeforeEvent_preceq_of_fgRootRead`
(`WeakProposalAdmissionRun.lean:21`), reproduced privately: importing that
module would put the whole `Weak`/`Seed` subtree, 94 modules, below every
consumer of the moving chain. -/
private theorem rrFinalizedBeforeEvent_preceq_of_fgRootRead
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} {i : Nat} {e : Event V} {time : Time} {B : Block V}
    (hi : rho.events[i]? = some e) (hlt : e.time < time)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v time).core.toHealing.toFG) B) :
    Block.Preceq (rho.stateBefore S i v).st.core.F B := by
  let n := (rho.events.filter (fun e => decide (e.time < time))).length
  have hiN : i < n := by
    by_contra hnot
    have htime : time ≤ e.time :=
      Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed
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

/-- An honest cone below `B` and a root below `B` at any read at or after the
slot-`s` support cutoff make every honest slot-`s` head available to the reader
before that cutoff. -/
theorem honestHeadsAvailableBefore_of_postHealingCone_at
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} {w : V} (hw : w ∈ rho.honest)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.support_cutoff S.E s ≤ rho.horizon)
    {Gamma : Time}
    (hcutGamma : Protocol.support_cutoff S.E s ≤ Gamma)
    {B : Block V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w Gamma).core.toHealing.toFG) B)
    (hvotes : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq B X)) :
    HonestHeadsAvailableBefore S rho s w
      (Protocol.support_cutoff S.E s) := by
  intro X hhead
  by_cases hgen : X = Block.genesis
  · exact Or.inl hgen
  right
  obtain ⟨x, hx, hcommittee, ⟨C, hCX, hCrun⟩, hXemit⟩ := hhead
  obtain ⟨Y, hBY, hYrun, hYemit⟩ := hvotes x hx hcommittee
  have hvoteEq : (⟨x, s, X.root⟩ : GoldfishVote V) =
      ⟨x, s, Y.erase.root⟩ :=
    Proofs.Optimistic.emits_gfVote_unique S
      adm.toNamedScheduleWellFormed hXemit hYemit rfl
  have hrootEq : X.root = Y.erase.root :=
    congrArg GoldfishVote.head hvoteEq
  have hCY : C = Y := by
    apply adm.toNamedRootCollisionFree.root_injective
      C Y hCrun hYrun C Y (Or.inl (Proofs.NamedAncestry.named_self C))
      (Or.inr (Proofs.NamedAncestry.named_self Y))
    rw [← Proofs.NamedWire.erase_root C, ← Proofs.NamedWire.erase_root Y, hCX]
    exact hrootEq
  have hBX : Block.Preceq B X := by
    simpa only [← hCY, hCX] using hBY
  have hmem : C.erase ∈ (voteDutyRead S rho x s).st.core.T :=
    Proofs.Optimistic.voteDutyHead_mem_of_emission_core S adm hx hCrun
      (u := ⟨x, s, X.root⟩) hXemit (by simpa only [hCX])
  have hmemPre : C.erase ∈
      (rho.storeBeforeTime S x (Protocol.vote_time S.E s)).T := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
      using hmem
  rcases block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTime S
      adm.toNamedScheduleWellFormed x (Protocol.vote_time S.E s) hmemPre with
    hgenC | ⟨D, i, ta, hDeq, hacc, hta⟩
  · have hXgen : X = Block.genesis := by rw [← hCX, hgenC]
    exact False.elim (hgen hXgen)
  · have hDpos : 0 < D.slot := by
      rw [← Proofs.NamedWire.erase_slot D]
      exact Nat.zero_lt_of_lt (parent_slot_lt_of_acceptsAt_block S hacc)
    have hDX : D.erase = X := hDeq.trans hCX
    have hFhist : BlockFinalizedBelowAtDeliveriesBefore S rho w D
        (Protocol.support_cutoff S.E s) := by
      intro q hq
      have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        S rho Gamma w
      have hFroot := Proofs.Records.preceq_get_fg_root_of_F
        (st := (rho.storeBeforeTime S w Gamma).toHealing.toFG) hFJ
      have hFread : Block.Preceq
          (rho.stateBeforeTime S Gamma w).st.core.F B := by
        exact Block.preceq_trans hFroot hroot
      have hFD := finalized_preceq_at_prefix_of_later_read S rho
        adm.toNamedScheduleWellFormed.sorted hcutGamma hq hFread
      have hFDX : Block.Preceq (rho.stateBefore S q w).st.core.F X :=
        Block.preceq_trans hFD hBX
      simpa only [hDX] using hFDX
    have hadmit := block_admittedBefore_of_accepted_after_cutoff_core
      S adm hx hw hDpos hacc hta hpost
      (by rw [← Proofs.Optimistic.vote_time_add_delta]) hhor hFhist
    simpa only [hDX] using hadmit

/-! ## 3. Named bodies behind erased tree membership -/

/- `mem_bodies_of_mem_T` is `MovingChainSupporterRun`'s public theorem (same statement);
the private copy that lived here collided with it once that one became public. -/

/-! ## 4. The four reads at a round action, at a cursor -/





/-- The SG root of a round action store is the SG root of the plain store read
at that instant: the confirmation update the action store applies writes
neither the processed tree, nor the finality fields, nor the SG votes. -/
theorem actionStoreAt_sgRoot_eq_storeBeforeTime
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    Protocol.get_sg_root S.E S.hc
        (actionStoreAt S rho v r).st.core.toHealing r =
      Protocol.get_sg_root S.E S.hc
        (rho.storeBeforeTime S v (S.a r)).core.toHealing r := by
  unfold actionStoreAt actionReadAt NamedActionReads.actionReadAt
    NamedActionReads.actionReadFrom NamedActionReads.confirmationReadFrom
  rfl

/-- The filtered candidate tree of a round action store is the plain store's:
the confirmation update the action store applies writes neither the processed
tree, nor the heights, nor the finality fields. -/
theorem actionStoreAt_filteredTree_eq_storeBeforeTime
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    Protocol.get_filtered_block_tree
        (actionStoreAt S rho v r).st.core.toHealing.toFG =
      Protocol.get_filtered_block_tree
        (rho.storeBeforeTime S v (S.a r)).core.toHealing.toFG := by
  unfold actionStoreAt actionReadAt NamedActionReads.actionReadAt
    NamedActionReads.actionReadFrom NamedActionReads.confirmationReadFrom
  rfl


/-! ## 5. The reads at a round action, from the slot fold

`MovingSlotFoldAt.historyAt` gives the moving history through the strict cursor
of each passed slot's proposal with that slot's family value as its endpoint;
each round read is that history read at the round's own action instant. The
round separation (`action_time_lt_openingProposal`) is the schedule input
the generic cursor reads take. -/












end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms honestHeadsAvailableBefore_of_postHealingCone_at
end DecoupledConsensusModel.Proofs.HealingSurface

end
