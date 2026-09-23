module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.ModelVocabulary.Healing.Action

@[expose] public section

/-! Common read and original-body equations. Callers bind each read to the
actual store. SG, FG-source and finality-head reads stay distinct. -/
namespace DecoupledConsensusModel.Proofs.DutyInputDefaults
open Protocol
variable {V : Type} [DecidableEq V] [Fintype V]



/-- Slot, identity and both GF lists are the actual current proposer reads. -/
theorem proposal_input_fields (contract : GradeContract V) (E : Env V) (hc : HealConfig)
    (nd : Protocol.Node V) (st : HealingStore V) :
    let input := proposal_input_with contract E hc nd st
    input.slot = st.s ∧ input.root = nd.new_root st.s ∧ input.proposer = nd.val_index ∧
    input.gf_votes = Protocol.proposer_view st.toFG.toSG.toGoldfishStore st.s ∧
    input.gf_support_votes = Protocol.proposer_support_view st.toFG.toSG.toGoldfishStore st.s :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- This identifies the selected core parent; it does not assume named lookup succeeds. -/
theorem proposal_input_parent (contract : GradeContract V) (E : Env V) (hc : HealConfig)
    (nd : Protocol.Node V) (st : HealingStore V) :
    (proposal_input_with contract E hc nd st).parent =
      get_head_with contract E hc st (Protocol.proposer_view st.toFG.toSG.toGoldfishStore st.s).toFinset
        (Protocol.proposer_support_view st.toFG.toSG.toGoldfishStore st.s).toFinset (st.s - 1) := rfl




#print axioms proposal_input_fields
#print axioms proposal_input_parent
end DecoupledConsensusModel.Proofs.DutyInputDefaults

end
