module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Internal.Observations

@[expose] public section

/-! # Canonical order of actual proposal-chain observations -/

namespace DecoupledConsensusModel
namespace Statements

open DecoupledConsensusModel.Internal DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- After a boundary vote, honest proposal parents, proposals, and committee
votes in honest-proposer slots are ordered by ancestry in execution order.
Raw confirmation and action observations are not part of this order claim. -/
def CanonicalProposalOrderFrom (S : Setup V) (rho : Run V) (t0 : Time) : Prop :=
  ∃ n0, SuffixStartsAfterBoundaryVote S rho t0 n0 ∧
    ∀ i stage B j laterStage C,
      n0 ≤ i → n0 ≤ j → ProposalChainStage stage → ProposalChainStage laterStage →
      HonestCanonicalObservationAtIndex S rho i stage B →
      HonestCanonicalObservationAtIndex S rho j laterStage C →
      (i < j ∨ (i = j ∧ stage ≤ laterStage)) → Block.Preceq B C

end Statements
end DecoupledConsensusModel

end
