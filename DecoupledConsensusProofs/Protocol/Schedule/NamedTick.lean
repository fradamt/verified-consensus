module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusModel.Protocol.Tick
public import DecoupledConsensusProofs.Protocol.Grades.NamedDuties
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.Actions

@[expose] public section

/-! Local store invariants and exact computed duty equations for the
closed named tick family. All action inputs come from the shared scheduler. -/
namespace DecoupledConsensusModel.Proofs.NamedTick
open Protocol.NamedTick Execution
variable {V : Type} [DecidableEq V] [Fintype V]


/-- This is a definitional equation of the shared scheduler. It identifies
the proposal's returned store and payload from one actual duty input, then
the GF result, then confirmation, then the attestation's returned store,
record, and payload from the actual post-confirmation input. -/
theorem tick_computed_duties (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time) :
    tick gc E hc cfg nd st record t =
      let s := E.slotOf t
      let st0 := Protocol.NamedStore.setClock E st t
      let proposed := Protocol.NamedDuties.propose_block_with gc E hc cfg nd st0
      let proposalDue := 0 < s ∧ t = Protocol.proposal_time E s ∧ E.proposer s = nd.val_index
      let st1 := if proposalDue then proposed.1 else st0
      let emitted1 := if proposalDue then
        match proposed.2 with
        | none => []
        | some B => [NamedObject.block B]
      else []
      let voted := Protocol.NamedDuties.goldfish_vote_with gc E hc nd st1
      let voteDue := 0 < s ∧ t = Protocol.vote_time E s
      let st2 := if voteDue then voted.1 else st1
      let emitted2 := if voteDue then voted.2.toList.map NamedObject.gfVote else []
      let st3 := if 0 < s ∧ t = Protocol.support_cutoff E s then
        Protocol.NamedDuties.update_confirmation_with gc E hc st2 (s - 1) else st2
      if t = hc.a E.Δ (hc.round_of st3.core.s) ∧ nd.awake (hc.round_of st3.core.s) = true then
        let attested := Protocol.NamedDuties.attest_with gc E hc nd st3 record
        (attested.1, attested.2.1, emitted1 ++ emitted2 ++ [NamedObject.attest attested.2.2])
      else (st3, record, emitted1 ++ emitted2) := by
  simp only [tick, Protocol.TickScheduler.runWith, namedOps, Protocol.NamedStore.setClock]
  unfold Protocol.TickScheduler.runWith.match_1 tick_computed_duties.match_1
  rfl



end DecoupledConsensusModel.Proofs.NamedTick

end
