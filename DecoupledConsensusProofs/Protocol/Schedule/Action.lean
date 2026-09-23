module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.ActionSources
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Protocol.ValidatorClient.Schedule
public import DecoupledConsensusProofs.Protocol.Handlers.TickBridges

@[expose] public section

/-!
# Exact round-action run bridge

This low module names the exact store, selected SG block, and combined
attestation used by a scheduled round action. It also connects that value to
the run emission.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol (HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]


/-- The action store is in the round whose action is running. This is
definitional: `actionStoreAt`/`actionReadAt` compose `NamedActionReads
.actionReadFrom`, whose only store write (`update_confirmation_with`)
touches `live_confirmed`/`latest_confirmed`, never the clock fields staged
by `setClock` (/ restatement: `actionStoreAt` now reads a
full named node state, not a bare store). -/
theorem actionStoreAt_round
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    S.hc.round_of (actionStoreAt S rho v r).s = r :=
  Proofs.HealingLemmas.round_of_slotOf_a S r


/-- The actual round action exposes the validator, round, and selected SG
block without referring to the pre-tick `confirmedAt` projection. The
`val_index`/`round`/`confirmed` fields of the named row are copied verbatim
(`Protocol.NamedRecord.encodeRow`) from the prior `create_attestation`
call inside `Protocol.NamedActions.round_action_with`, so each conjunct
is definitional given the store's round. -/
theorem actionAttestationAt_shape
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    (actionAttestationAt S rho v r).val_index = v ∧
      (actionAttestationAt S rho v r).round = r ∧
      (actionAttestationAt S rho v r).confirmed =
        some (actionSGBlockAt S rho v r).root :=
  ⟨S.node_val_index v, Proofs.HealingLemmas.round_of_slotOf_a S r, rfl⟩

/-! ## The action instant's tick shape

`NamedActionSources.tick_at_action`'s Proofs-layer cone is unbuilt in this
worktree, so the scheduler unfolding it rests on (`Protocol.NamedTick.tick`
against the `TickScheduler.runWith` engine, all Model layer) is restated here
as a private local copy — the same reason `Optimistic/Alignment.lean` and
`Availability/Pool.lean` each keep an identical private `named_tick_computed
_duties` copy. Byte-identical to the Model-level scheduler equation, so the
proof script is unchanged. -/
private theorem action_named_tick_computed_duties
    (gc : Protocol.GradeContract V) (E : Env V) (hc : HealConfig)
    (cfg : HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time) :
    Protocol.NamedTick.tick gc E hc cfg nd st record t =
      let s := E.slotOf t
      let st0 := Protocol.NamedStore.setClock E st t
      let proposed := Protocol.NamedDuties.propose_block_with gc E hc cfg nd st0
      let proposalDue := 0 < s ∧ t = Protocol.proposal_time E s ∧ E.proposer s = nd.val_index
      let st1 := if proposalDue then proposed.1 else st0
      let emitted1 := if proposalDue then
        match proposed.2 with
        | none => []
        | some B => [Object.block B]
      else []
      let voted := Protocol.NamedDuties.goldfish_vote_with gc E hc nd st1
      let voteDue := 0 < s ∧ t = Protocol.vote_time E s
      let st2 := if voteDue then voted.1 else st1
      let emitted2 := if voteDue then voted.2.toList.map Object.gfVote else []
      let st3 := if 0 < s ∧ t = Protocol.support_cutoff E s then
        Protocol.NamedDuties.update_confirmation_with gc E hc st2 (s - 1) else st2
      if t = hc.a E.Δ (hc.round_of st3.core.s) ∧ nd.awake (hc.round_of st3.core.s) = true then
        let attested := Protocol.NamedDuties.attest_with gc E hc nd st3 record
        (attested.1, attested.2.1, emitted1 ++ emitted2 ++ [Object.attest attested.2.2])
      else (st3, record, emitted1 ++ emitted2) := by
  simp only [Protocol.NamedTick.tick, Protocol.TickScheduler.runWith, Protocol.NamedTick.namedOps,
    Protocol.NamedStore.setClock]
  unfold Protocol.TickScheduler.runWith.match_1 action_named_tick_computed_duties.match_1
  rfl

/-- The engine wrapper's emission list is the scheduler's own. -/
private theorem action_on_tick_emit_snd_eq (S : Setup V) (v : V) (n : NamedNodeState V)
    (t : Time) :
    (NamedNode.tick S v n t).2 =
      (Protocol.NamedTick.tick
        (NamedProfile.gradeContract
          (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache))
        S.E S.hc S.cfg (S.node v) n.st n.record t).2.2 := rfl

private theorem action_slot_pos (S : Setup V) (r : Round) :
    0 < S.E.slotOf (S.a r) := by
  rw [Setup.a, Protocol.a_eq_support_cutoff_succ, Proofs.Optimistic.slotOf_support_cutoff]
  exact Nat.zero_lt_succ _

private theorem action_support_time (S : Setup V) (r : Round) :
    S.a r = Protocol.support_cutoff S.E (S.E.slotOf (S.a r)) := by
  rw [Setup.a, Protocol.a_eq_support_cutoff_succ, Proofs.Optimistic.slotOf_support_cutoff]

/-- At a round action the proposal and vote branches are absent by their
times, so the remaining duty receives the restricted statement's computed
action read. Restates `NamedActionSources.tick_at_action` locally, for the
same unbuilt-cone reason as the scheduler equation above. -/
private theorem action_tick_at (S : Setup V) (v : V) (before : NamedNodeState V) (r : Round) :
    (NamedNode.tick S v before (S.a r)).2 =
      let n := NamedActionReads.actionReadFrom S before r
      let gc := NamedProfile.gradeContract n.cache
      if (S.node v).awake r = true then
        [Object.attest
          (Protocol.NamedDuties.attest_with gc S.E S.hc (S.node v) n.st n.record).2.2]
      else [] := by
  have hpos := action_slot_pos S r
  have hs := action_support_time S r
  have hp : ¬ (0 < S.E.slotOf (S.a r) ∧
      S.a r = Protocol.proposal_time S.E (S.E.slotOf (S.a r)) ∧
      S.E.proposer (S.E.slotOf (S.a r)) = (S.node v).val_index) := by
    intro h
    exact Proofs.Optimistic.support_cutoff_ne_proposal_time S.E _ (hs.symm.trans h.2.1)
  have hv : ¬ (0 < S.E.slotOf (S.a r) ∧
      S.a r = Protocol.vote_time S.E (S.E.slotOf (S.a r))) := by
    intro h
    exact Proofs.Optimistic.support_cutoff_ne_vote_time S.E _ (hs.symm.trans h.2)
  rw [action_on_tick_emit_snd_eq,
    action_named_tick_computed_duties
      (NamedProfile.gradeContract
        (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc before.st.core.toHealing (S.a r) before.cache))
      S.E S.hc S.cfg (S.node v) before.st before.record (S.a r)]
  simp only [if_neg hp, if_neg hv, if_pos (And.intro hpos hs), List.nil_append]
  have hround : S.hc.round_of (Protocol.NamedDuties.update_confirmation_with
      (NamedProfile.gradeContract
        (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc before.st.core.toHealing (S.a r) before.cache))
      S.E S.hc
      (Protocol.NamedStore.setClock S.E before.st (S.a r)) (S.E.slotOf (S.a r) - 1)).core.s = r :=
    Proofs.HealingLemmas.round_of_slotOf_a S r
  simp only [hround, true_and]
  split_ifs <;> rfl

/-- Every awake scheduled honest action emits the exact attestation computed by
`actionAttestationAt`. This stronger identity bridge is needed when a proof
uses the height or finality pair rather than only the SG projection. -/
theorem honest_emits_exact_actionAttestationAt_of_awake
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {v : V} (hv : v ∈ rho.honest) (r : Round)
    (hA : (S.node v).awake r = true)
    (hhor : S.a r ≤ rho.horizon) :
    rho.emits S v (Object.attest (actionAttestationAt S rho v r))
      (S.a r) := by
  apply Proofs.Optimistic.emits_of_on_tick_emit S sch hv
    (Proofs.HealingLemmas.publicTime_a S r) (Proofs.HealingLemmas.a_nonneg S r) hhor
  show Object.attest (actionAttestationAt S rho v r) ∈
    (NamedNode.tick S v (rho.stateBeforeTime S (S.a r) v) (S.a r)).2
  rw [action_tick_at S v (rho.stateBeforeTime S (S.a r) v) r, if_pos hA]
  exact List.mem_singleton_self _

/-- The existing recovery and safety proofs use the full-participation
specialization. The weak continuation uses the awake form above. -/
theorem honest_emits_exact_actionAttestationAt
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) (r : Round)
    (hhor : S.a r ≤ rho.horizon) (hpost : S.E.t_GST ≤ S.a r) :
    rho.emits S v (Object.attest (actionAttestationAt S rho v r)) (S.a r) :=
  honest_emits_exact_actionAttestationAt_of_awake S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv r
    (adm.all_awake v hv r hpost hhor) hhor

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
