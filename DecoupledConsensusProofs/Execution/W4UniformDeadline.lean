module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Execution.FGSafetyProgressDeadline
public import DecoupledConsensusProofs.ModelVocabulary.Execution.Setup
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.VoteStoreExtends

@[expose] public section

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.NamedRecoveryRead
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}









/-- The FG deadline at any caller-selected post-GST round is below the
uniform lag added to that round. -/
theorem w4_fgSafetyProgressDeadline_le_uniform
    (S : Setup V) {rho : Run V} (_adm : Admissible S rho) (rGST gap : Round)
    (_hpost : S.E.t_GST ≤ S.a rGST) :
    fgSafetyProgressDeadline S rho rGST gap delayExtra ≤
      rGST + (2 + (S.cfg.D + S.cfg.K + 5) *
        progressLag' gap delayExtra) := by
  simp only [fgSafetyProgressDeadline, Nat.add_assoc]
  apply Nat.le_of_eq
  ring

#print axioms w4_fgSafetyProgressDeadline_le_uniform

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
