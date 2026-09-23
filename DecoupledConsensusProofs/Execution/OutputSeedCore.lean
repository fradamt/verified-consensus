module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ConfirmationQueryIdxEmitted
public import DecoupledConsensusInternal.Definitions.NamedStableChainOutage
public import DecoupledConsensusInternal.Legacy.Definitions.NamedHeadReads

@[expose] public section

namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Internal Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedOutageEntry.History

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The seed certificate shared by stable-output and stable-witness routes. -/
structure OutputSeed (S : Setup V) (rho : NamedRun V) (b0 : Time) (s : Round)
    (P : Block V) : Prop where
  heads : ∀ w ∈ rho.honest,
    Block.Preceq P (voterHeadAt S rho w (S.hc.opening_slot s))
  noConflict : NoHonestConflictAbove S rho b0 P
  carriers : ∀ u ∈ Internal.NamedOutageEntry.honestRoundVoters S rho s,
    Block.Preceq P (Proofs.HealingSurface.actionSGBlockAt S rho u s)
  held : ∀ u ∈ rho.honest, ∃ Pn : NamedBlock V, Pn.erase = P ∧
    Pn ∈ (NamedRun.stateBeforeTime S rho (S.a s) u).st.bodies ∧
    NamedRun.blockInRun S rho Pn
  history : ∀ C : NamedBlock V,
    LayerAJointHistoryIdxEmitted S rho (boundaryIdx rho b0) C → Block.Preceq P C.erase

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
