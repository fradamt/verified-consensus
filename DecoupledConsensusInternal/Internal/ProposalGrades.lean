module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.PhaseGradeQueries
public import DecoupledConsensusInternal.Definitions.Confirmation
public import DecoupledConsensusInternal.Internal.GradeReads

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Raw grades of honest proposals after recovery

Raw G2 does not require active-tree membership. Each reader separately keeps
the proposal active or has an FG root strictly above it.
-/

namespace DecoupledConsensusModel
namespace Internal

open Execution HealingSurface PhaseGrades DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every sufficiently late action grades an honest post-boundary proposal.
The status alternative is per reader, not synchronized across readers. -/
def HonestProposalGradeTwoFrom (S : Setup V) (rho : Run V) (q : Round) : Prop :=
  ∀ s : Slot, healingBoundaryTime S q < Protocol.proposal_time S.E s →
    S.E.proposer s ∈ rho.honest →
    ∃ B : NamedBlock V, Statements.Instantiation.proposedBlockAt S rho s = some B ∧
    ∀ r : Round, max (q + 3) (S.hc.round_of s + 2) ≤ r →
      S.a r ≤ rho.horizon →
      ∀ v ∈ rho.honest,
        storeGrade S.E S.hc (readAt S rho (domain S.E S.hc r .g2) v).st
          r .g2 B.erase = true ∧
        (B.erase ∈ filteredTree (readAt S rho (domain S.E S.hc r .g2) v) ∨
          Block.Prec B.erase
            (Protocol.get_fg_root
              (readAt S rho (domain S.E S.hc r .g2) v).st.core.toHealing.toFG))

end Internal
end DecoupledConsensusModel

end
