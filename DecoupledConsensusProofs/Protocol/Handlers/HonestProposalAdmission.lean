module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.StoreFinalityCore
public import DecoupledConsensusProofs.Protocol.Schedule.ProposalTransportCore
public import DecoupledConsensusProofs.Protocol.ValidatorClient.BlockEmission
public import DecoupledConsensusProofs.Protocol.Handlers.BlockAdmission
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.ProposalCore
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Blocks held before a proposal instant -/


/-! ## The proposal's local guards -/





/-- The proposal's claimed proposer is the assigned proposer of its slot.

: `proposedBlock` is gone; bind the named block via `proposedBlockAt` and
conclude about its erasure, matching the shape `admittedBefore_of_delivery_guards`
needs downstream. -/
theorem proposedBlock_proposer
    (S : Setup V) (rho : Run V) (s : Slot) {B : NamedBlock V}
    (hB : Statements.Instantiation.proposedBlockAt S rho s = some B) :
    B.erase.proposer? = some (S.E.proposer B.erase.slot) := by
  have hslot : B.erase.slot = s := by
    rw [Proofs.NamedWire.erase_slot]
    exact DecoupledConsensusModel.Proofs.Optimistic.proposedBlockAt_slot S rho s hB
  rw [hslot, Proofs.NamedWire.erase_proposer]
  exact DecoupledConsensusModel.Proofs.HealingSurface.proposedBlockAt_proposer S rho s hB


/-- The honest proposal's parent satisfies the strict parent-slot assertion.

: the parent is `DecoupledConsensusModel.Proofs.HealingSurface.proposedBlockAt_parent`'s witness, whose
erasure is `Proofs.HealingSurface.proposedParent`; freshness at the proposal time
comes from `Proofs.NamedSlotFreshness.block_slot_lt_of_mem_beforeTime_of_le_proposal`,
the same route `NamedProposalBridge.proposedBlockAt_admit` uses internally. -/
theorem proposedBlock_parent_slot_lt
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hs : 0 < s) {B : NamedBlock V}
    (hB : Statements.Instantiation.proposedBlockAt S rho s = some B) :
    B.erase.parent.slot < B.erase.slot := by
  have hpar : B.erase.parent = Proofs.HealingSurface.proposedParent S rho s :=
    Proofs.HealingSurface.proposedBlockErased_parent S rho s hB
  have hsslot : B.erase.slot = s := by
    rw [Proofs.NamedWire.erase_slot]
    exact DecoupledConsensusModel.Proofs.Optimistic.proposedBlockAt_slot S rho s hB
  rw [hsslot, hpar]
  exact Proofs.NamedSlotFreshness.block_slot_lt_of_mem_beforeTime_of_le_proposal
    S adm.toNamedAdmissibleCore hs (le_refl (Protocol.proposal_time S.E s))
    (Proofs.HealingSurface.proposedParent_mem S rho s)






/-- Reachable proposal stores contain only round-bounded resolved attestations,
and the proposal filter only removes entries. Thus the honest proposal passes
the receiver-side carried-attestation predicate.

design note: this is now `Proofs.HealingSurface.proposedBlockErased_carried_admissible`,
proved from the named selector's own window bound (`selected_row_round_le`),
with no `Admissible`/`SgRounds` premise. -/
theorem proposedBlock_carried_attestations_admissible
    (S : Setup V) (rho : Run V) (s : Slot) {B : NamedBlock V}
    (hB : Statements.Instantiation.proposedBlockAt S rho s = some B) :
    Protocol.carried_attestations_admissible S.hc B.erase = true :=
  Proofs.HealingSurface.proposedBlockErased_carried_admissible S rho s hB




/-! ## Event-indexed self-acceptance -/


/-- The honest proposal tick is the accepting event for its own block. This is
the source event that `Synchrony.relay_block` needs.

: bound at the named block `B` (`proposedBlockAt S rho s = some B`). The
pre-processed guard is freshness at `Statements.Instantiation.proposerReadAt` (via the
store's own tree/bodies coherence); the post-processed guard is
`DecoupledConsensusModel.Proofs.HealingSurface.proposedBlockAt_mem_bodies_after_tick`, unified onto the same
tick index as the emission via `Proofs.HealingSurface.index_unique_of_nodup`. -/
theorem acceptsAt_proposedBlock_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {s : Slot} (hs : 0 < s)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E s ≤ rho.horizon)
    {B : NamedBlock V} (hB : Statements.Instantiation.proposedBlockAt S rho s = some B) :
    ∃ i : Nat, NamedRun.acceptsAt S rho i (S.E.proposer s)
      (.block B) (Protocol.proposal_time S.E s) := by
  obtain ⟨B0, hB0, -, i₁, hi₁, hemem⟩ :=
    DecoupledConsensusModel.Proofs.HealingSurface.proposedBlockAt_emits_of_honest S
      adm.toNamedScheduleWellFormed s hs hprop hhor
  have hBeq : B0 = B := DecoupledConsensusModel.Proofs.HealingSurface.proposedBlockAt_unique S rho s hB0 hB
  subst hBeq
  have hadmit := DecoupledConsensusModel.Proofs.HealingSurface.proposedBlockAt_admit S adm s hs hB
  obtain ⟨i₂, hi₂, hmem⟩ :=
    DecoupledConsensusModel.Proofs.HealingSurface.proposedBlockAt_mem_bodies_after_tick S
      adm.toNamedScheduleWellFormed s hs hprop hhor hB hadmit
  have hij : i₁ = i₂ :=
    Proofs.HealingSurface.index_unique_of_nodup adm.toNamedScheduleWellFormed.nodup hi₁ hi₂
  subst hij
  refine ⟨i₁, ⟨Or.inl ⟨Protocol.proposal_time S.E s, hi₁, hemem⟩,
      ⟨Event.tick (S.E.proposer s) (Protocol.proposal_time S.E s),
        hi₁, rfl, rfl⟩⟩, ?_, ?_⟩
  · simp only [NamedReceipt.processed, decide_eq_false_iff_not]
    have hstateEq : NamedRun.stateBefore S rho i₁ (S.E.proposer s) =
        NamedRun.stateBeforeTime S rho (Protocol.proposal_time S.E s) (S.E.proposer s) :=
      Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S adm.toNamedScheduleWellFormed hi₁
    rw [hstateEq]
    intro hmemB
    have htree : (Statements.Instantiation.proposerReadAt S rho s).st.core.T =
        (Statements.Instantiation.proposerReadAt S rho s).st.bodies.image NamedBlock.erase :=
      (DecoupledConsensusModel.Proofs.HealingSurface.proposerReadAt_invariant S rho s).1.1
    exact Proofs.HealingSurface.proposedBlockErased_fresh_at_tick S adm s hs hB
      (htree ▸ Finset.mem_image_of_mem NamedBlock.erase hmemB)
  · simp only [NamedReceipt.processed, decide_eq_true_eq]
    exact hmem

theorem acceptsAt_proposedBlock
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hs : 0 < s)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E s ≤ rho.horizon)
    {B : NamedBlock V} (hB : Statements.Instantiation.proposedBlockAt S rho s = some B) :
    ∃ i : Nat, NamedRun.acceptsAt S rho i (S.E.proposer s)
      (.block B) (Protocol.proposal_time S.E s) :=
  acceptsAt_proposedBlock_core S adm.toNamedAdmissibleCore hs hprop hhor hB


/-- An honest proposal in the bounded proposal window is a block in the
run-wide collision-freedom scope.

: `RunBlock` is now `NamedRun.blockInRun`, itself a `NamedBlock`-typed
relation; this is exactly `DecoupledConsensusModel.Proofs.HealingSurface.proposedBlockAt_blockInRun_of_admissible`. -/
theorem proposedBlock_runBlock
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hs : 0 < s)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E s ≤ rho.horizon)
    {B : NamedBlock V} (hB : Statements.Instantiation.proposedBlockAt S rho s = some B) :
    RunBlock S rho B :=
  DecoupledConsensusModel.Proofs.HealingSurface.proposedBlockAt_blockInRun_of_admissible S
    adm.toNamedAdmissibleCore s hs hprop hhor hB

/-! ## Admission at every honest reader -/


/-- The event-indexed canonical-history fact needed when the honest proposal is
delivered to another node. Time bounds are included so the predicate says no
more than the GST-zero liveness proof reads.

: `Object.block` now takes a `NamedBlock V` (`Object:= NamedObject`), so
`B` is named, and the conclusion reads the named store's `.core.F` against the
erasure. -/
def ProposalFinalizedBelowAtDeliveries
    (S : Setup V) (rho : Run V) (s : Slot) (B : NamedBlock V) : Prop :=
  ∀ v ∈ rho.honest, ∀ (i : Nat),
    i ≤ (rho.events.filter
      (fun e => decide (e.time < Protocol.vote_time S.E s))).length →
    Block.Preceq (rho.stateBefore S i v).st.core.F B.erase


end Protocol
end DecoupledConsensusModel

end
