module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusModel.Protocol.Duties.Proposals
public import DecoupledConsensusProofs.Protocol.Handlers.NamedStore
public import DecoupledConsensusProofs.Protocol.Grades.ProposalParent
public import DecoupledConsensusProofs.Protocol.ValidatorClient.Record
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.DutyInputDefaults
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Walk

@[expose] public section

/-! Named constructor equations. Current/frame lookup and proposal
success use the actual parent producer. Generic parent membership appears
only in local helpers. Source fields come from the shared action read. -/
namespace DecoupledConsensusModel.Proofs.NamedActions
open Protocol.NamedActions
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- A successful lookup retains the full stored body and its exact erasure. -/
theorem parent_body_spec (st : Protocol.NamedStore V) (parent : Block V)
    (B : NamedBlock V) (h : parentBody? st parent = some B) :
    B ∈ st.bodies ∧ B.erase = parent := by
  unfold parentBody? pickUnique? at h
  split at h
  · rename_i hex
    rw [Option.some_inj] at h
    subst B
    have hs := Finset.choose_spec (fun B : NamedBlock V => decide (B.erase = parent) = true)
      st.bodies hex
    exact ⟨Finset.choose_mem _ _ hex, of_decide_eq_true hs.2⟩
  · simp at h

omit [Fintype V] in
/-- Uniqueness is restricted to bodies already in this store. -/
theorem parent_body_eq_some (st : Protocol.NamedStore V) (parent : Block V)
    (B : NamedBlock V) (hB : B ∈ st.bodies) (he : B.erase = parent)
    (hu : NamedStore.ErasureUnique st) : parentBody? st parent = some B := by
  apply Protocol.pickUnique?_eq_some hB (by simp [he])
  intro C hC hp
  exact hu C hC B hB ((of_decide_eq_true hp).trans he.symm)


/-- The proposal uses exactly one shared read and the bounded named row selector. -/
theorem proposal_shared_read (contract : Protocol.GradeContract V)
    (source : Protocol.ProposalRowSource) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) :
    proposal_with contract source E hc nd st =
      let input := Protocol.proposal_input_with contract E hc nd st.core.toHealing
      (parentBody? st input.parent).map fun parent =>
        NamedBlock.node parent input.slot input.root input.gf_votes input.gf_support_votes
          (Protocol.NamedProposalRows.proposalRows parent
            (Protocol.NamedProposalRows.select source hc st)) input.proposer := rfl

/-- Lookup success fixes every constructor field, with the retained full parent. -/
theorem proposal_eq_of_parent (contract : Protocol.GradeContract V)
    (source : Protocol.ProposalRowSource) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (parent : NamedBlock V)
    (hp : parentBody? st
      (Protocol.proposal_input_with contract E hc nd st.core.toHealing).parent = some parent) :
    proposal_with contract source E hc nd st =
      some (let input := Protocol.proposal_input_with contract E hc nd st.core.toHealing
        NamedBlock.node parent input.slot input.root input.gf_votes input.gf_support_votes
          (Protocol.NamedProposalRows.proposalRows parent
            (Protocol.NamedProposalRows.select source hc st)) input.proposer) := by
  rw [proposal_shared_read]
  simp only [hp, Option.map_some]

/-- Every produced proposal names the actual retained parent and exact F2 rows. -/
theorem proposal_payload (contract : Protocol.GradeContract V)
    (source : Protocol.ProposalRowSource) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (hout : proposal_with contract source E hc nd st = some B) :
    let input := Protocol.proposal_input_with contract E hc nd st.core.toHealing
    B.parent ∈ st.bodies ∧ B.parent.erase = input.parent ∧
    B.slot = input.slot ∧ B.root = input.root ∧
    B.gf_votes = input.gf_votes ∧ B.gf_support_votes = input.gf_support_votes ∧
    B.attestations = Protocol.NamedProposalRows.proposalRows B.parent
      (Protocol.NamedProposalRows.select source hc st) ∧ B.proposer? = some input.proposer := by
  rw [proposal_shared_read] at hout
  dsimp only at hout ⊢
  cases hp : parentBody? st
      (Protocol.proposal_input_with contract E hc nd st.core.toHealing).parent with
  | none => simp [hp] at hout
  | some parent =>
    rw [hp] at hout
    have he := Option.some.inj hout
    subst B
    obtain ⟨hm, he⟩ := parent_body_spec st _ parent hp
    exact ⟨hm, he, rfl, rfl, rfl, rfl, rfl, rfl⟩


/-- Both concrete modes resolve the actual read to a retained body. There is
no separate head-membership or successful-lookup premise. -/
theorem runtime_parent_body_some
    (cache : DecoupledConsensusModel.Protocol.Cache V) (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (h : Proofs.NamedStoreRoots.Invariant E cfg st) :
    ∃ B ∈ st.bodies, B.erase =
      (Protocol.proposal_input_with (DecoupledConsensusModel.Protocol.frameContract cache)
        E hc nd st.core.toHealing).parent ∧
      parentBody? st (Protocol.proposal_input_with (DecoupledConsensusModel.Protocol.frameContract cache)
        E hc nd st.core.toHealing).parent = some B := by
  obtain ⟨B, ⟨hB, he⟩, _⟩ :=
    NamedProposalParent.proposal_parent_named_body_unique cache E hc cfg nd st h
  exact ⟨B, hB, he, parent_body_eq_some st _ B hB he h.1.2.1⟩

/-- For current and frame contracts the produced local invariant rules out
failed lookup, for any cache. Source choice adds no open condition. -/
theorem runtime_proposal_some
    (cache : DecoupledConsensusModel.Protocol.Cache V) (source : Protocol.ProposalRowSource)
    (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (h : Proofs.NamedStoreRoots.Invariant E cfg st) :
    ∃ B, proposal_with (DecoupledConsensusModel.Protocol.frameContract cache) source E hc nd st = some B := by
  obtain ⟨parent, _, _, hp⟩ := runtime_parent_body_some cache E hc cfg nd st h
  exact ⟨_, proposal_eq_of_parent (DecoupledConsensusModel.Protocol.frameContract cache)
    source E hc nd st parent hp⟩


/-- The named action calls the fixed creator with the actual shared read. -/
theorem round_action_shared_read (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (st : Protocol.HealingStore V) (record : Protocol.NamedRecord) :
    round_action_with contract E hc nd st record =
      Protocol.NamedRecord.create record
        (creatorInput (Protocol.attestation_input_with contract E hc nd st)) := rfl

/-- Erasure is the exact old action at the same store, contract and record. -/
theorem round_action_row_erasure (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (st : Protocol.HealingStore V) (record : Protocol.NamedRecord) :
    (round_action_with contract E hc nd st record).2.erase =
      (Protocol.round_action_with contract E hc nd st record.legacy).2 := by
  rw [round_action_shared_read]
  exact NamedRecord.create_erases record
    (creatorInput (Protocol.attestation_input_with contract E hc nd st))


/-- A nonempty named row identifies fields computed by the actual source read. -/
theorem round_action_names_source (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (st : Protocol.HealingStore V) (record : Protocol.NamedRecord)
    (h : Height) (entry : BlockId) (timeout : Bool)
    (hp : (round_action_with contract E hc nd st record).2.height_pair =
      .vote h entry timeout) :
    ∃ nu, (Protocol.attestation_input_with contract E hc nd st).fields =
      some (h, entry, nu) := by
  rw [round_action_shared_read] at hp
  exact NamedRecord.create_names_source record
    (creatorInput (Protocol.attestation_input_with contract E hc nd st)) hp


#print axioms parent_body_spec
#print axioms parent_body_eq_some
#print axioms proposal_shared_read
#print axioms proposal_eq_of_parent
#print axioms proposal_payload
#print axioms runtime_parent_body_some
#print axioms runtime_proposal_some
#print axioms round_action_shared_read
#print axioms round_action_row_erasure
#print axioms round_action_names_source
end DecoupledConsensusModel.Proofs.NamedActions

end
