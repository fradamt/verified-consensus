module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Definitions.ProposalSourcesInternal
public import DecoupledConsensusInternal.Definitions.PhaseGrades

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! Proof-side proposal-source queries outside `Statements.Consensus`. -/
namespace DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal DecoupledConsensusModel.Execution
variable {V : Type} [DecidableEq V] [Fintype V]

def ProposedBlockParentQuery (S : Setup V) (rho : Run V) (s : Slot) : Prop :=
  ∀ B : NamedBlock V, proposedBlockAt S rho s = some B →
    ∃ p, NamedBlock.parent? B = some p ∧ p.erase = proposedParent S rho s

def ProposalEmissionQuery (S : Setup V) (rho : Run V) : Prop :=
  NamedScheduleWellFormed S rho →
  ∀ (s : Slot) (i : Nat), 0 < s → S.E.proposer s ∈ rho.honest →
    rho.events[i]? = some (.tick (S.E.proposer s) (Protocol.proposal_time S.E s)) →
    ∀ B : NamedBlock V,
      (NamedObject.block B ∈ NamedRun.emittedAt S rho i (S.E.proposer s)
        (Protocol.proposal_time S.E s)) ↔ proposedBlockAt S rho s = some B

def ProposalParentRetainedQuery (S : Setup V) (rho : Run V) (s : Slot) : Prop :=
  proposedParent S rho s ∈ (proposerReadAt S rho s).st.core.T →
    (proposedBlockAt S rho s).isSome = true

def ProposedParentAboveAnchorQuery (S : Setup V) (rho : Run V) (s : Slot) : Prop :=
  let n := proposerReadAt S rho s
  let r := S.hc.round_of n.st.core.s
  Block.Preceq (Internal.PhaseGrades.nodeAnchor S n r) (proposedParent S rho s)

end DecoupledConsensusModel.Proofs.HealingSurface

end
