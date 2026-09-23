module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGOpeningFrozenSuffix
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RawExactHeightSeed
public import DecoupledConsensusProofs.Execution.RecoveryGradeProcessedRead
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusInternal.Definitions.NamedLifecycle

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Triple-proposer recurrence height progress composition

This module keeps the strongest named output of the height composition. The
public numeric height-progress contract is a projection of this carrier.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- One bounded higher-grade source, including the exact named Claim-4
proposal that created it. -/
structure BoundedHeightGradeSourceAt
    (S : Setup V) (rho : Run V) (r0 start bound : Round)
    (origin source : Round) (C : NamedBlock V) : Prop where
  startLtOrigin : start < origin
  originLtSource : origin < source
  sourceUpper : source ≤ bound
  lifecycle : NamedRawOpeningLifecycleAt S rho origin C
  originAfterBoundary : healingBoundaryTime S r0 <
    Protocol.proposal_time S.E (S.hc.opening_slot origin)
  grade : NamedGradeFormsAt S rho source C.erase
  sourceAbove : honestHMaxAt S rho (S.a start) <
    (Protocol.derive_named S.E S.cfg C).h
  sourceJustifiable : (Protocol.derive_named S.E S.cfg C).nj = false
  originFresh : Internal.NoLocalHeightPairBefore S rho
    (strictEventIndex rho (S.a origin))
    (Protocol.derive_named S.E S.cfg C).h










end HealingSurface
end Proofs
end DecoupledConsensusModel

end
