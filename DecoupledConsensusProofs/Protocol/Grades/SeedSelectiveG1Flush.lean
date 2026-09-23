module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeDelivery
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryCapturedActionCarrier
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryHandoffCore
public import DecoupledConsensusProofs.Objects.AdmissibleCore
public import DecoupledConsensusProofs.Protocol.Grades.RelativeOneChain

@[expose] public section

/-!
# Selective-G1 flush and one-chain action carriers

A stamped active grade-0 block that conflicts with the fresh anchor vetoes
every block in the clear walk. Thus, the SG selector uses its selected grade-2
fallback. The run-level section records the settled predicates and isolates the
clear/selected-G2 cases that discharge cross-tier compatibility.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas
open GradeDeliveryRun

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Store-local selective-G1 veto -/




/-! ## Run-level settled predicates -/

/-- Every selected honest grade-2 block is below the target FG root or active
at every honest action read. -/
def SelectedG2SettledAt
    (S : Setup V) (rho : Run V) (r : Round) : Prop :=
  ∀ u ∈ rho.honest, ∀ Q,
    PhaseGrades.nodeQ2 S (actionReadAt S rho u r) r = some Q →
    ∀ w ∈ rho.honest,
      FinalityFilterNoninterferenceAtRead S rho w (S.a r) Q


/-- Honest action SG carriers are pairwise compatible. -/
def HonestActionCarriersOneChainAt
    (S : Setup V) (rho : Run V) (r : Round) : Prop :=
  ∀ u ∈ rho.honest, ∀ v ∈ rho.honest,
    Block.compatible
      (actionSGBlockAt S rho u r)
      (actionSGBlockAt S rho v r) = true

/-! ## Prepared action selector -/






end HealingSurface
end Proofs
end DecoupledConsensusModel

end
