module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusStatements.Instantiation.OutageWindow
public import DecoupledConsensusInternal.Legacy.Definitions.NamedOutageEntry
public import DecoupledConsensusInternal.ModelVocabulary.Execution.FrameOperations
public import DecoupledConsensusModel.Protocol.Handlers

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

namespace DecoupledConsensusModel.Internal.NamedStableChainOutage
open Execution NamedOutageEntry DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]


/--: every block below an honest node's stable output at a time `T` before
an SG outage stays below every honest node's stable output from the outage
start through the run horizon. -/
def StableChainOutageResilience (S : Setup V) : Prop :=
  ∀ rho b0 b1 (T : Time) v P,
    OutageExecution S rho b0 b1 → NamedOutageEntry.SlashableBound S rho →
    Execution.HonestCommittees S rho.honest →
    AwakeGradeMajorityThroughout S rho →
    v ∈ rho.honest →
    nextAction S T + roundLength S + S.E.Δ ≤ b0 →
    Block.Preceq P (Protocol.get_stable (Run.storeAt S rho v T).core) →
    b1 + S.E.Δ ≤ nextAction S T + ((S.hc.η_SG : Time) + 1) * roundLength S - 11 * S.E.Δ →
    b1 + S.E.Δ ≤ rho.horizon →
    ∀ w ∈ rho.honest, ∀ t, b0 ≤ t → t ≤ rho.horizon →
      Block.Preceq P (Protocol.get_stable (NamedRun.readAt S rho t w).st.core)

end DecoupledConsensusModel.Internal.NamedStableChainOutage

end
