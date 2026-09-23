module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.GSTZeroPreparedWalk
public import DecoupledConsensusProofs.Execution.WeakGenesisLatestAtProposal

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # GST-zero latest-at-proposal field, prebuilt over pins -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakGenesis

open Internal Execution Protocol Statements

variable {V : Type} [DecidableEq V] [Fintype V]

theorem latestAtProposalField_of_weakGenesis_of_pins
    (hduty : ∀ (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
      {s : Slot}, 0 < s →
      Protocol.confirmation_time S.E s ≤ rho.horizon →
      S.E.proposer s ∈ rho.honest →
      ∀ {B : NamedBlock V}, proposedBlockAt S rho s = some B →
        CanonicalProposalDutyAt S rho s B)
    (S : Setup V) : ∀ rho, WeakGenesis S rho →
      LatestAtProposalField S rho 0 := by
  intro rho h
  exact latestAtProposalField_of_weakGenesis_of_heads_of_duty S h
    (honestHeadExtendsStableFrom_zero_of_weakGenesis S h)
    (fun {s} hs hhor hprop {B} hB => hduty S h hs hhor hprop hB)

#print axioms latestAtProposalField_of_weakGenesis_of_pins

end WeakGenesis
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
