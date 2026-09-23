module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.Bridges
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.ChainState.RawHeightCoverage
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.RecoverySourceProgress
public import DecoupledConsensusProofs.Protocol.ValidatorClient.SlashableBound

@[expose] public section

/-!
# Successor-height target rows

This file isolates the anti-slashing invariant used after a protected height
boundary. A fresh record at the boundary can first write the common target.
While the same justifiable grade remains active and the raw frontier does not
rise, every later action repeats that target and cannot set the timeout bit.

The argument is suffix-local. It uses neither a nonfinality run nor an
honest-proposer premise.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol (height_pair own_lock)
open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- At one height, an honest record is either still unused or is pinned to the
common target, and its timeout bit is still clear. -/
def SuccessorTargetRecordAt
    (Lambda : Protocol.NamedRecord) (h : Height) (target : BlockId) :
    Prop :=
  (Lambda.legacy.target h = none ∨ Lambda.legacy.target h = some target) ∧
    Lambda.legacy.timeout h = false

/-- **Open (Rule B residual).** The stored lock and a same-height
finality pair, if present, use the successor target. Rule B permits a
finality pair when the target and lock entries are both empty, so
`SuccessorTargetRecordAt` and `Proofs.Records.LockCompatible` do not prove this
alignment. -/
def SuccessorTargetLockAlignmentAt
    (Lambda : Protocol.NamedRecord) (fp : Option FinalityPair)
    (h : Height) (target : BlockId) : Prop :=
  (∀ X : BlockId, Lambda.legacy.lock h = some X → X = target) ∧
    ∀ p : FinalityPair, fp = some p → p.height = h → p.target = target






















end HealingSurface
end Proofs
end DecoupledConsensusModel

end
