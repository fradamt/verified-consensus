module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.TickBridges

@[expose] public section

/-!
# Low carrier-admission guard contracts

Receiver-local finality guards for accepted block relay, stated without recovery
or post-healing dependencies.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The only receiver-local guard not transported by accepted-block relay,
restricted to deliveries before one read cutoff. -/
def BlockFinalizedBelowAtDeliveriesBefore
    (S : Setup V) (rho : Run V) (v : V) (B : NamedBlock V) (Gamma : Time) : Prop :=
  ∀ (i : Nat),
    i ≤ (rho.events.filter (fun e => decide (e.time < Gamma))).length →
    Block.Preceq (rho.stateBefore S i v).st.core.F B.erase


end Protocol
end DecoupledConsensusModel

end
