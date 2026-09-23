module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.CarrierAdmissionCore
public import DecoupledConsensusProofs.Protocol.Handlers.AcceptanceTiming
public import DecoupledConsensusProofs.Protocol.ValidatorClient.BlockEmission
public import DecoupledConsensusProofs.Protocol.Schedule.AdoptionTransport
public import DecoupledConsensusProofs.Protocol.Handlers.HonestProposalAdmission

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Accepted carrier admission at GST zero

This leaf joins accepted-block relay with honest-proposal self-admission. A
positive-slot carrier accepted before its slot's vote duty reaches every
honest reader before the support cutoff. The only live delivery guard exposed
to the caller is that the reader's finalized block remains below the carrier.

restated under the named runtime (design note):
`Object.block` now carries a `NamedBlock V`, so every accepted-block statement
binds a named witness and reads `Run.acceptsAt`/`Run.acceptsAt_block_of_*` at
that witness, concluding about its erasure where the caller wants the erased
block (`AdmittedBefore`, `BlockFinalizedBelowAtDeliveriesBefore`). The  grep
against the cone (`union-cone-modules.txt`) finds no consumer for this file's
one-delay-to-proposal chain or its slot-to-slot adoption cluster; those eight
declarations are archived byte-exact to
`the compatibility layer`
under, since porting them needs a genuine restatement (a bound
`proposedBlockAt`/`GFVoteInCutoffView` witness), not a mechanical proof, for a
declaration nothing in the cone calls. The two declarations below keep their
cone consumers (`Protocol.AdoptionConstructorRun`,
`Protocol.GSTZeroSelectionSafetyRun`, `Protocol.ProposalSnapshotBridgeRun`).
-/



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]


/-- A positive-slot carrier in a vote-duty tree has an acceptance event before
that duty. This is the tree-to-acceptance provenance serves to relay the carrier
back to the confirming node.

design note: `Proofs.Optimistic.voteDutyStore`'s `.T` is still an erased `Block V` tree
(the ordinary read is unaffected by grading), so `B` stays erased; the wire
object it was accepted as is a *named* witness whose erasure is `B`
(`Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore`), and the conclusion
existentially binds that witness alongside its acceptance event. -/
theorem acceptsAt_carrier_before_vote_of_mem_voteDutyStore
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} {k : Slot} {B : Block V} (hBpos : 0 < B.slot)
    (hB : B ∈ (Proofs.Optimistic.voteDutyStore S rho w k).T) :
    ∃ (C : NamedBlock V) (i : Nat) (t : Time), C.erase = B ∧
      NamedRun.acceptsAt S rho i w (.block C) t ∧
      Protocol.proposal_time S.E B.slot ≤ t ∧
      t < Protocol.vote_time S.E k := by
  obtain ⟨n, hn, hbefore⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedScheduleWellFormed (Protocol.vote_time S.E k)
  have hBn : B ∈ (rho.stateBefore S n w).st.core.T := by
    simpa [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore,
      Run.storeBeforeTime, hn] using hB
  obtain ⟨C, hCmem, hCerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n w hBn
  have hprocessed : NamedReceipt.processed (rho.stateBefore S n w).st (.block C) = true := by
    simpa only [Object.processed, NamedReceipt.processed, decide_eq_true_eq] using hCmem
  rcases acceptsAt_block_of_processed S rho w n C hprocessed with
    hgen | ⟨i, hin, t, hacc⟩
  · exfalso
    apply Nat.ne_of_gt hBpos
    rw [← hCerase, hgen]
    rfl
  · obtain ⟨-, e, he, -, het⟩ := hacc.1
    refine ⟨C, i, t, hCerase, hacc, ?_, ?_⟩
    · rw [← hCerase]
      exact proposal_time_le_of_acceptsAt_block S adm hacc
    · rw [← het]
      exact hbefore i e hin he


end Protocol
end DecoupledConsensusModel

end
