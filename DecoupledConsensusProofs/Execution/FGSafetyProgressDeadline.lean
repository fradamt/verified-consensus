module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightProgressCompose

@[expose] public section

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.Optimistic
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

/-- The last round of the progress prefix serves to establish FG safety.
The named height regime starts two rounds after the given post-GST action,
which is the first round where the lagged-GST bound is available. From that
frontier, the first `K` multiple at least `D + 3` heights above it is at most
`D + K + 2` heights away. Three more height gains cover the closed recovery
join. Thus the deadline needs `D + K + 5` progress lags and is independent of
the absolute frontier height. -/
noncomputable def fgSafetyProgressDeadline
    (S : Setup V) (rho : Run V) (rGST gap : Round) (delayExtra : Nat := 0) : Round :=
  rGST + 1 +
    (1 + (S.cfg.D + S.cfg.K + 5) * progressLag' gap delayExtra)

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
