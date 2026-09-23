module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.HandoverHeight

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Strong-regime opening vote cone

The selected named proposal lifecycle supplies the exact opening vote names.
The proposal witness also supplies the named run block, so the standard named
vote-name bridge gives the geometric cone over the proposal's erasure.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The selected lifecycle names the bound proposal at every honest opening
committee member's voter head. -/
theorem NamedSGProposalLifecycleInputs.committeeOpeningVoterHeads
    (S : Setup V) {rho : Run V}
    (adm : Admissible S rho) (hcom : HonestCommittees S rho.honest)
    {r : Round} {s : Slot} {A : Block V} {P : NamedBlock V}
    (h : NamedSGProposalLifecycleInputs S rho r s A P) :
    ∀ w ∈ rho.honest, w ∈ S.E.committee (s + 1) →
      P.erase = voterHeadAt S rho w (s + 1) := by
  intro w hw hcommittee
  obtain ⟨tree, H, hext⟩ := h.voteStoresExtend adm hcom w hw hcommittee
  exact hext.head.symm

/-- The selected lifecycle produces the exact named opening vote cone. -/
theorem NamedSGProposalLifecycleInputs.openingVoteCone
    (S : Setup V) {rho : Run V}
    (adm : Admissible S rho) (hcom : HonestCommittees S rho.honest)
    {r : Round} {s : Slot} {A : Block V} {P : NamedBlock V}
    (h : NamedSGProposalLifecycleInputs S rho r s A P) :
    NamedHonestVotesCone S rho (s + 1)
      (fun X => Block.Preceq P.erase X) := by
  have hrun : RunBlock S rho P :=
    proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
      (s + 1) (Nat.succ_pos s) h.proposerHonest
      h.openingProposalInHorizon h.proposal
  exact Proofs.Optimistic.honestVotesCone_preceq S rho (s + 1) hrun
    (h.honestVotesName adm hcom)

#print axioms NamedSGProposalLifecycleInputs.committeeOpeningVoterHeads
#print axioms NamedSGProposalLifecycleInputs.openingVoteCone

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
