module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.PreparedV4LiveSelection
public import DecoupledConsensusInternal.Legacy.Definitions.VoteSafety

@[expose] public section

/-! # Prepared V4 actual vote sources -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem emittedVote_head_eq_voteDutyHead_v4
    (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho) {x : V} {u : GoldfishVote V} {t : Time}
    (hemit : rho.emits S x (Object.gfVote u) t) :
    u.head = (voteDutyHead S rho x u.slot).root := by
  have hshape := emits_gfVote_shape S hemit
  have ht : t = Protocol.vote_time S.E u.slot := by
    rw [hshape.2.2.2]
    exact hshape.2.1
  have hs : 0 < u.slot := by
    rw [hshape.2.2.2]
    exact hshape.1
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

namespace Handover

/-- Exact public vote-source record, prebuilt over the three actual-vote producers. -/
theorem SettledBootstrapPreparedV4.voteSourcesSafeAt_core_of_pins
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start d : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (_of_protectedVoteSlot_at_vote_core : start ≤ d →
      Protocol.vote_time S.E d ≤ rho.horizon →
        ProtectedVoteSlot S rho d P.erase)
    (_of_liveConfirmedAtConfirmation_at_actual_vote_core :
      ∀ q, S.hc.opening_slot (base + S.hc.η_SG) ≤ q → q < d →
        Protocol.confirmation_time S.E q ≤ rho.horizon →
        ∀ w ∈ rho.honest, ∀ v ∈ rho.honest,
          Block.Preceq
            (rho.storeAt S w (Protocol.confirmation_time S.E q)).live_confirmed
            (voteDutyHead S rho v d))
    (_of_actionOutputs_at_actual_vote_core :
      ∀ r, base + S.hc.η_SG ≤ r →
        S.a r < Protocol.vote_time S.E (d + 1) →
        S.a r ≤ rho.horizon → ∀ w ∈ rho.honest, ∀ v ∈ rho.honest,
          Block.Preceq (Protocol.get_fg_root
            (actionStoreAt S rho w r).toHealing.toFG)
            (voteDutyHead S rho v d) ∧
          Block.Preceq (actionStoreAt S rho w r).live_confirmed
            (voteDutyHead S rho v d) ∧
          (rho.emits S w
            (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
            Block.Preceq (actionSGBlockAt S rho w r)
              (voteDutyHead S rho v d)) ∧
          (∀ T, fgConfirmationWitness S (actionStoreAt S rho w r) = some T →
            Block.Preceq T (voteDutyHead S rho v d)))
    (hd : start ≤ d) (hhor : Protocol.vote_time S.E d ≤ rho.horizon) :
    VoteSourcesSafeAt S rho (base + S.hc.η_SG) d P.erase := by
  refine {
    seed := (_of_protectedVoteSlot_at_vote_core hd hhor).heads
    live := _of_liveConfirmedAtConfirmation_at_actual_vote_core
    actions := _of_actionOutputs_at_actual_vote_core
    votes := ?_ }
  intro v _ u t hemit hslot
  simpa only [hslot] using
    emittedVote_head_eq_voteDutyHead_v4 S adm.toNamedScheduleWellFormed hemit

#print axioms SettledBootstrapPreparedV4.voteSourcesSafeAt_core_of_pins

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
