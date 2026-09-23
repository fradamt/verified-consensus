module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.BlockAdmission
public import DecoupledConsensusProofs.Protocol.Handlers.ConfirmationPolicy
public import DecoupledConsensusProofs.Execution.UserConfirmationHistory
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Adoption
public import DecoupledConsensusProofs.Generic.SlotFreshness
public import DecoupledConsensusProofs.Execution.HandoverHeight
public import DecoupledConsensusProofs.Objects.WeakLegacySources
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedCeilingStep
public import DecoupledConsensusProofs.Protocol.Handlers.HonestProposalAdmission
public import DecoupledConsensusProofs.Generic.HandoverPrefixAgreement
public import DecoupledConsensusProofs.Execution.StrongSeedConfirmation
public import DecoupledConsensusProofs.Execution.HeightFieldAssembly
public import DecoupledConsensusProofs.Execution.FGSafetyProgressDeadline
public import DecoupledConsensusProofs.Objects.FGSafetyRoot
public import DecoupledConsensusProofs.Generic.HeightRegimeNamed
public import DecoupledConsensusProofs.Execution.HeightRegimeNamedClosed
public import DecoupledConsensusProofs.Generic.HandoverFGWitnessesNamedClosed
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.SGLifetimeNamed

@[expose] public section

/-!
# Committee-seeded prepared handover bootstrap

The opening vote-head seed is committee-scoped. The first successor slot is
the boundary at which the all-honest protected-slot invariant starts.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

/-- Protection at the opening vote duty: only emitting committee members have
an opening head, while the named vote cone records all emitted honest votes. -/
structure ProtectedVoteSlotCommittee (S : Setup V) (rho : Run V)
    (d : Slot) (B : Block V) : Prop where
  heads : ∀ w ∈ rho.honest, w ∈ S.E.committee d →
    Block.Preceq B (voterHeadAt S rho w d)
  cone : NamedHonestVotesCone S rho d (fun X => Block.Preceq B X)


#print axioms ProtectedVoteSlotCommittee





end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
