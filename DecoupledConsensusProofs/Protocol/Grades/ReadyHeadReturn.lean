module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.FinalityCarrier
public import DecoupledConsensusProofs.Protocol.Schedule.HeldSkipProducers
public import DecoupledConsensusProofs.Execution.ViabilityHistory
public import DecoupledConsensusProofs.Protocol.Handlers.NumericStore
public import DecoupledConsensusProofs.Execution.PrefixThroughHistory
public import DecoupledConsensusProofs.Protocol.Handlers.HandlerAdmissionGuards
public import DecoupledConsensusProofs.Protocol.Handlers.MaximumCarrier
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityCertificates
public import DecoupledConsensusProofs.Protocol.Handlers.PrefixCarrier
public import DecoupledConsensusProofs.Protocol.ChainState.JustificationCertificates
public import DecoupledConsensusProofs.Execution.OutageProvenance
public import DecoupledConsensusProofs.Protocol.Handlers.ReceiptCallsGF
public import DecoupledConsensusProofs.Protocol.Grades.HealthyHeadReady
public import DecoupledConsensusProofs.Protocol.Handlers.PublicCutBody
public import DecoupledConsensusProofs.Protocol.Handlers.BlockStamp
public import DecoupledConsensusProofs.Protocol.Grades.Grades
public import DecoupledConsensusInternal.Legacy.Assumptions.AwakeWindow
public import DecoupledConsensusInternal.Legacy.Assumptions.Weight

@[expose] public section

/-! The G1-late ready head returned at the G2 domain read. The directed
finalized-domain order of `ReadyHeadKernelDraft` makes the target's head and the
source's finalized block comparable, so the head is either relayed into the
source inside the healthy window or already held there as a finalized ancestor. -/
namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.ReadyHeadReturnTime
open Execution Protocol DecoupledConsensusModel.Protocol
open Internal.NamedOutageEntry.History
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Structural and schedule ingredients -/

/-- Raw ancestry of an erased body is the erasure of named ancestry: the raw
parent chain of `B.erase` is the erasure of the named parent chain of `B`.
No erasure-injectivity claim is used. -/
theorem named_ancestor_of_erase (A : Block V) (B : NamedBlock V) :
    Block.Preceq A B.erase →
      ∃ A' : NamedBlock V, NamedBlock.Preceq A' B ∧ A'.erase = A := by
  induction B with
  | genesis =>
    intro h
    have hA : A = Block.genesis := by
      simpa only [NamedBlock.erase, Block.Preceq, Block.preceq,
        decide_eq_true_eq] using h
    exact ⟨.genesis, by simp [NamedBlock.Preceq, NamedBlock.preceq], by rw [hA]; rfl⟩
  | node p s root votes support rows proposer ih =>
    intro h
    simp only [NamedBlock.erase, Block.Preceq, Block.preceq, Bool.or_eq_true,
      decide_eq_true_eq] at h
    rcases h with hA | hp
    · exact ⟨.node p s root votes support rows proposer,
        by simp [NamedBlock.Preceq, NamedBlock.preceq], hA.symm⟩
    · obtain ⟨A', hA', hE⟩ := ih hp
      refine ⟨A', ?_, hE⟩
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
      exact Or.inr hA'





/-- One Δ separates the two late cutoffs. -/
theorem late_g1_add_delta (S : Setup V) (r : Round) :
    late S.E S.hc r .g1 + S.E.Δ = late S.E S.hc r .g2 := by
  simp only [late, Phase.lateOffset]
  ring



/-! ## The ready-head return -/


#print axioms named_ancestor_of_erase
end DecoupledConsensusModel.Proofs.NamedOutageHistory.ReadyHeadReturnTime

end
