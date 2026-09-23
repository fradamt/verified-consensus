module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.OpeningCarrierSelection
public import DecoupledConsensusProofs.Generic.CanonicalRegimeFromChain
public import DecoupledConsensusProofs.Execution.PostHealingProposalLifecycle
public import DecoupledConsensusProofs.Protocol.ChainState.RecurringFinality
public import DecoupledConsensusProofs.Execution.StoreFinalityRun
public import DecoupledConsensusProofs.Protocol.ChainState.CanonicalRegimeRound
public import DecoupledConsensusProofs.Generic.CanonicalSuffix
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightProgressCompose
public import DecoupledConsensusProofs.Protocol.ValidatorClient.MovingChainRow
public import DecoupledConsensusProofs.Protocol.Grades.RawHeightProgressCore
public import DecoupledConsensusProofs.Protocol.ValidatorClient.CanonicalRegimeFirstVote
public import DecoupledConsensusProofs.Protocol.Schedule.W4ExecSuffix

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Round arithmetic (earlier `OpeningCarrierFinalityRun.lean:14-52`) -/









/-! ## The carrier-side pins -/














/-- Pin for the second-carrier finality step: the later carrier of the
recurrence finalizes the selected carrier's opening height. This is earlier's
`carrierJustificationHeight_of_firstHalf`
(`CanonicalRegimeSecondCheckpointRun.lean:236`, blocked), the proposal-chain
link, the justification-height monotonicity
(`derivedJustification_strict_or_eq_of_preceq`, `RecurringFinalityRun.lean:992`,
blocked) and `canonicalCarrier_commonFinalized_of_justifiedPrefix`
(`FinalityFromJustifiedPrefixRun.lean:22`, below the red set).

`ProposerCarrierAt` at the earlier carrier is carried so that the split in
`W4CarrierChainFinalitySplitRun` discharges this pin directly: the honesty of
that round's `+2` proposer is what the proposal-chain link needs, and
`CarrierFinalityFirstHalfAt` has no carrier field. The producer of this theorem
has the fact in scope at the call site. -/
def W4CarrierChainFinalityPin (S : Setup V) (rho : Run V) (q0 : Round) : Prop :=
  ∀ (source c r : Round) (C Cr Endr : Block V),
    q0 + 2 < c → c < r →
    ProposerCarrierAt S rho c →
    CarrierFinalityFirstHalfAt S rho c C →
    (∀ P0 : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot c) = some P0 →
      (Protocol.derive_named S.E S.cfg P0).nj = false) →
    CanonicalRegimeRoundAt S rho q0 r →
    MovingChainAtCarrierFor S rho q0 r Cr Endr →
    ¬ LostRoundAt S rho r →
    S.E.t_GST ≤ Protocol.proposal_time S.E (S.hc.opening_slot r) →
    honestHMaxAt S rho (S.a q0) < carrierOpeningHeight S rho c →
    1 < carrierOpeningHeight S rho c →
    source < r →
    S.a (r + 1) ≤ rho.horizon →
    AlreadyCommonFinalizedAtOrAbove S rho q0 source (r + 1)
      (carrierOpeningHeight S rho c)

/-! ## The finality producer -/

-- `hbelow` is retained because every pinned producer consumes it (through
-- `AlignedRoundLemmas.honestWeightMajority_of_belowOneThird`); the pin-free
-- successor of this theorem reads it directly.

/-! ## Axiom roster. Every public theorem of this file. Each must report a
subset of `propext`, `Classical.choice`, `Quot.sound` and nothing else. A
theorem reporting NO axioms is hollow: it means an import's olean lacked a name
and Lean recovered silently, which still exits zero. -/



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
