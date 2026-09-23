module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusModel.Protocol.Grades
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeBootstrapCore

@[expose] public section

/-! Pure core-store and arithmetic helpers retained in the default library.
the prior runtime statements and proofs are in the compatibility layer. -/


namespace DecoupledConsensusModel
namespace Proofs.FrameStoreRoot
open Internal Execution
open DecoupledConsensusModel.Protocol
open Protocol (HeightConfig)
open Protocol (HealConfig)
variable {V : Type} [DecidableEq V] [Fintype V]




/-- The Goldfish duty changes no finalized viability field for any seam. -/
theorem finalizedViable_goldfish_with (G : Protocol.GradeContract V)
    (S : Setup V) (nd : Protocol.Node V) (st : Protocol.Store V)
    (h : FinalizedViable st) :
    FinalizedViable (Protocol.goldfish_vote_with G S.E S.hc nd st).1 := by
  simp only [Protocol.goldfish_vote_with]
  split_ifs
  · exact finalizedViable_of_eq (on_goldfish_vote_checked_T S.E st _)
      (coreEq_on_goldfish_vote_checked S.E st _).σ_eq
      (coreEq_on_goldfish_vote_checked S.E st _).F_eq
      (on_goldfish_vote_checked_h_max S.E st _) h
  · exact h

/-- Confirmation updates records only, regardless of selected candidate. -/
theorem finalizedViable_confirmation_with (G : Protocol.GradeContract V)
    (S : Setup V) (st : Protocol.Store V) (s : Slot) (h : FinalizedViable st) :
    FinalizedViable (Protocol.update_confirmation_with G S.E S.hc st s) :=
  finalizedViable_of_eq rfl rfl rfl rfl h


end Proofs.FrameStoreRoot
end DecoupledConsensusModel

end
