module
public import DecoupledConsensusModel
public import DecoupledConsensusModel.Protocol.Duties.Inputs
public import DecoupledConsensusModel.Protocol.ForkChoice.Head

@[expose] public section

/-!
# The proposal and round action

These are the selected contract-parameterised decision cores. The named runtime
supplies the contract and applies the final store writes at the protocol layer.
-/

namespace DecoupledConsensusModel
namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

def proposal_input_with (contract : GradeContract V)
    (E : Env V) (hc : HealConfig) (nd : Protocol.Node V) (st : HealingStore V) : ProposalInput V :=
  with_proposal_input contract E hc nd st id

def attestation_input_with (contract : GradeContract V)
    (E : Env V) (hc : HealConfig) (nd : Protocol.Node V) (st : HealingStore V) :
    AttestationInput V :=
  with_attestation_input contract E hc nd st id

/-- The round-action attestation and its updated finality record. -/
def round_action_with (contract : GradeContract V)
    (E : Env V) (hc : HealConfig) (nd : Protocol.Node V)
    (st : HealingStore V) (Λ : Protocol.Record) :
    Protocol.Record × CombinedAttestation V :=
  with_attestation_input contract E hc nd st (fun input =>
    Protocol.create_attestation Λ input.val_index input.round input.confirmed
      input.fields input.h_j input.J input.h_F)

end Protocol
end DecoupledConsensusModel

end
