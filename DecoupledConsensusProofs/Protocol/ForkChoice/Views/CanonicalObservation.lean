module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.CanonicalSuffix
public import DecoupledConsensusProofs.Execution.StoreFinalityCore
public import DecoupledConsensusProofs.Execution.Acceptance
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.ProposalCore
public import DecoupledConsensusProofs.Protocol.Schedule.ProposalTransportCore
public import DecoupledConsensusProofs.Objects.PostGSTSync
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.VoteViewValidity
public import DecoupledConsensusProofs.Protocol.Schedule.SlotInduction
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.Actions
public import DecoupledConsensusProofs.Execution.Wire

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The proposal chain, restated to the named proposal bridge -/


/-- The indexed records's proposal-stage duty computes exactly the public
`Statements.Instantiation.proposedBlockAt` reader, at an honest proposal tick. Both sides
unfold to `Protocol.NamedActions.proposal_with` at the identical prepared read
(`canonicalTickReadAtIndex` at the proposal instant is
`Statements.Instantiation.proposerReadAt`), so this is an internal-consistency fact, not
a cross-system claim (ledger: statement changed, `proposedBlock` retired
under, target has type `Option (NamedBlock V)`). -/
theorem proposalStageBlockAtIndex_eq_proposedBlock
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {i : Nat} {v : V} {t : Time}
    (hevent : rho.events[i]? = some (Event.tick v t))
    (hactive : 0 < S.E.slotOf t ∧
      t = Protocol.proposal_time S.E (S.E.slotOf t) ∧
      S.E.proposer (S.E.slotOf t) = (S.node v).val_index) :
    proposalStageBlockAtIndex S rho i v t =
      Statements.Instantiation.proposedBlockAt S rho (S.E.slotOf t) := by
  let q := S.E.slotOf t
  have hv : v = S.E.proposer q := by
    simpa only [q, S.node_val_index] using hactive.2.2.symm
  subst hv
  have hpre : NamedRun.stateBefore S rho i (S.E.proposer q) =
      NamedRun.stateBeforeTime S rho t (S.E.proposer q) :=
    Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
      S adm.toNamedScheduleWellFormed hevent
  have ht : t = Protocol.proposal_time S.E q := hactive.2.1
  have hread : canonicalTickReadAtIndex S rho i (S.E.proposer q) t =
      Statements.Instantiation.proposerReadAt S rho q := by
    unfold canonicalTickReadAtIndex Statements.Instantiation.proposerReadAt
      NamedActionReads.confirmationReadAt
    rw [hpre, ht]
  unfold proposalStageBlockAtIndex Statements.Instantiation.proposedBlockAt
  rw [hread]


/-! ## Prepared vote-stage facts -/

/-- The indexed vote-stage head is the head of the exact prepared vote read.
The cache and contract are the ones used by the named vote duty. -/
theorem voteStageHeadAtIndex_eq_voteDutyHead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {i : Nat} {v : V} {t : Time}
    (hevent : rho.events[i]? = some (Event.tick v t))
    (hactive : 0 < S.E.slotOf t ∧
      t = Protocol.vote_time S.E (S.E.slotOf t)) :
    voteStageHeadAtIndex S rho i v t =
      let q := S.E.slotOf t
      let read := NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E q) v)
        (Protocol.vote_time S.E q)
      let st := read.st.core
      Protocol.get_head_in_tree_with_layer (NamedProfile.gradeContract read.cache)
        S.E S.hc st.toHealing
        (Protocol.voter_filtered_block_tree S.E st st.s)
        (Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
        (Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
        (st.s - 1) := by
  let q := S.E.slotOf t
  have hpre : NamedRun.stateBefore S rho i v =
      NamedRun.stateBeforeTime S rho t v :=
    Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
      S adm.toNamedScheduleWellFormed hevent
  have hread : canonicalTickReadAtIndex S rho i v t =
      NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E q) v)
        (Protocol.vote_time S.E q) := by
    unfold canonicalTickReadAtIndex
    rw [hpre, hactive.2]
  unfold voteStageHeadAtIndex
  rw [hread]


/-! ## Exact observation constructors -/


/-- A named in-run proposal tick supplies the exact stage-1 observation, for
whichever retained body the total `Statements.Instantiation.proposedBlockAt` reader
selects at that slot (: the reader is `Option`-valued, so the retained
witness `B` is an explicit premise rather than a value the theorem
produces on its own; ledger: statement changed). -/
theorem proposedBlock_observationAtIndex
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hs : 0 < s) (hprop : S.E.proposer s ∈ rho.honest)
    {i : Nat}
    (hevent : rho.events[i]? = some
      (Event.tick (S.E.proposer s) (Protocol.proposal_time S.E s)))
    {B : NamedBlock V} (hB : Statements.Instantiation.proposedBlockAt S rho s = some B) :
    HonestCanonicalObservationAtIndex S rho i 1 B.erase := by
  have hslot := Proofs.Optimistic.slotOf_proposal_time S.E s
  have hactive : 0 < S.E.slotOf (Protocol.proposal_time S.E s) ∧
      Protocol.proposal_time S.E s =
        Protocol.proposal_time S.E
          (S.E.slotOf (Protocol.proposal_time S.E s)) ∧
      S.E.proposer (S.E.slotOf (Protocol.proposal_time S.E s)) =
        (S.node (S.E.proposer s)).val_index := by
    rw [hslot]
    exact ⟨hs, rfl, (S.node_val_index (S.E.proposer s)).symm⟩
  have heq := proposalStageBlockAtIndex_eq_proposedBlock
    S adm hevent hactive
  rw [hslot] at heq
  have hcomputed : proposalStageBlockAtIndex S rho i (S.E.proposer s)
      (Protocol.proposal_time S.E s) = some B := by
    rw [heq, hB]
  exact HonestCanonicalObservationAtIndex.proposedBlock
    hprop hevent hactive hcomputed

/-! ## Same-event facts -/

omit [DecidableEq V] [Fintype V] in
private theorem tick_node_time_eq_of_same_index
    {rho : Run V} {i : Nat} {v w : V} {t u : Time}
    (h₁ : rho.events[i]? = some (Event.tick v t))
    (h₂ : rho.events[i]? = some (Event.tick w u)) : v = w ∧ t = u := by
  have h := Option.some.inj (h₁.symm.trans h₂)
  simpa using h

/-- The named proposal duty's own parent field is exactly the retained-body
erasure it selected, at any indexed tick (internal-consistency twin of
`DecoupledConsensusModel.Proofs.HealingSurface.proposedBlockAt_parent`, generalised off `proposerReadAt` to
any prepared read `canonicalTickReadAtIndex S rho i v t`). -/
private theorem proposalStageBlockAtIndex_parent
    (S : Setup V) (rho : Run V) (i : Nat) (v : V) (t : Time) {B : NamedBlock V}
    (hB : proposalStageBlockAtIndex S rho i v t = some B) :
    ∃ p : NamedBlock V, NamedBlock.parent? B = some p ∧
      p.erase = proposalStageHeadAtIndex S rho i v t := by
  simp only [proposalStageBlockAtIndex, proposalStageHeadAtIndex,
    Proofs.NamedActions.proposal_shared_read] at hB ⊢
  rw [Option.map_eq_some_iff] at hB
  obtain ⟨p, hp, hBeq⟩ := hB
  subst hBeq
  exact ⟨p, rfl, (Proofs.NamedActions.parent_body_spec _ _ p hp).2⟩

/-- The only proper same-event proposal-stage transition is parent to block. -/
theorem proposalParent_preceq_proposedBlock_atIndex
    (S : Setup V) {rho : Run V} {i : Nat} {P B : Block V}
    (hP : HonestCanonicalObservationAtIndex S rho i 0 P)
    (hB : HonestCanonicalObservationAtIndex S rho i 1 B) :
    Block.Preceq P B := by
  cases hP with
  | proposalParent _ hevent _ =>
      cases hB with
      | proposedBlock _ hevent' _ computed =>
          obtain ⟨rfl, rfl⟩ := tick_node_time_eq_of_same_index hevent hevent'
          obtain ⟨p, hp, hpe⟩ := proposalStageBlockAtIndex_parent
            S rho i _ _ computed
          rw [← hpe]
          apply preceq_of_parent?
          simp only [Proofs.NamedWire.erase_parent_optional, hp, Option.map_some]

/-- Two observations at the same stage and event name the same block. -/
theorem honestCanonicalObservationAtIndex_eq_of_same_stage
    (S : Setup V) {rho : Run V} {i stage : Nat} {B C : Block V}
    (hB : HonestCanonicalObservationAtIndex S rho i stage B)
    (hC : HonestCanonicalObservationAtIndex S rho i stage C) : B = C := by
  cases hB with
  | proposalParent _ hevent _ =>
      cases hC with
      | proposalParent _ hevent' _ =>
          obtain ⟨rfl, rfl⟩ := tick_node_time_eq_of_same_index hevent hevent'
          rfl
  | proposedBlock _ hevent _ computed =>
      cases hC with
      | proposedBlock _ hevent' _ computed' =>
          obtain ⟨rfl, rfl⟩ := tick_node_time_eq_of_same_index hevent hevent'
          rw [computed] at computed'
          exact congrArg NamedBlock.erase (Option.some.inj computed')
  | voteHead _ hevent _ _ _ _ =>
      cases hC with
      | voteHead _ hevent' _ _ _ _ =>
          obtain ⟨rfl, rfl⟩ := tick_node_time_eq_of_same_index hevent hevent'
          rfl
  | confirmationOutput _ hevent _ =>
      cases hC with
      | confirmationOutput _ hevent' _ =>
          obtain ⟨rfl, rfl⟩ := tick_node_time_eq_of_same_index hevent hevent'
          rfl
  | actionHead _ hevent _ =>
      cases hC with
      | actionHead _ hevent' _ =>
          obtain ⟨rfl, rfl⟩ := tick_node_time_eq_of_same_index hevent hevent'
          rfl

private theorem proposalParent_voteHead_sameIndex_false
    (S : Setup V) {rho : Run V} {i : Nat} {P H : Block V}
    (hP : HonestCanonicalObservationAtIndex S rho i 0 P)
    (hH : HonestCanonicalObservationAtIndex S rho i 2 H) : False := by
  cases hP with
  | proposalParent _ hevent hproposal =>
      cases hH with
      | voteHead _ hevent' hvote _ _ _ =>
          obtain ⟨rfl, rfl⟩ := tick_node_time_eq_of_same_index hevent hevent'
          exact Proofs.Optimistic.vote_time_ne_proposal_time S.E _
            (hvote.2.symm.trans hproposal.2.1)

private theorem proposedBlock_voteHead_sameIndex_false
    (S : Setup V) {rho : Run V} {i : Nat} {B H : Block V}
    (hB : HonestCanonicalObservationAtIndex S rho i 1 B)
    (hH : HonestCanonicalObservationAtIndex S rho i 2 H) : False := by
  cases hB with
  | proposedBlock _ hevent hproposal _ =>
      cases hH with
      | voteHead _ hevent' hvote _ _ _ =>
          obtain ⟨rfl, rfl⟩ := tick_node_time_eq_of_same_index hevent hevent'
          exact Proofs.Optimistic.vote_time_ne_proposal_time S.E _
            (hvote.2.symm.trans hproposal.2.1)

/-- Handler order is ancestry order for two proposal-chain observations at the
same event. Proposal and vote duties cannot share a tick. -/
theorem proposalChainObservation_preceq_of_sameIndex
    (S : Setup V) {rho : Run V} {i stage laterStage : Nat}
    {B C : Block V}
    (hstage : ProposalChainStage stage)
    (hlater : ProposalChainStage laterStage)
    (hB : HonestCanonicalObservationAtIndex S rho i stage B)
    (hC : HonestCanonicalObservationAtIndex S rho i laterStage C)
    (hle : stage ≤ laterStage) : Block.Preceq B C := by
  unfold ProposalChainStage at hstage hlater
  have hcases : stage = laterStage ∨
      (stage = 0 ∧ laterStage = 1) ∨
      (stage = 0 ∧ laterStage = 2) ∨
      (stage = 1 ∧ laterStage = 2) := by
    omega
  rcases hcases with heq | h01 | h02 | h12
  · subst laterStage
    have hEq := honestCanonicalObservationAtIndex_eq_of_same_stage S hB hC
    subst C
    exact Block.preceq_self B
  · rcases h01 with ⟨rfl, rfl⟩
    exact proposalParent_preceq_proposedBlock_atIndex S hB hC
  · rcases h02 with ⟨rfl, rfl⟩
    exact False.elim (proposalParent_voteHead_sameIndex_false S hB hC)
  · rcases h12 with ⟨rfl, rfl⟩
    exact False.elim (proposedBlock_voteHead_sameIndex_false S hB hC)

#print axioms voteStageHeadAtIndex_eq_voteDutyHead

end Protocol
end DecoupledConsensusModel

end
