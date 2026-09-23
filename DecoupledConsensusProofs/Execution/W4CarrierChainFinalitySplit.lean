module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.W4D2OpeningCarrierFinality
public import DecoupledConsensusProofs.Protocol.ChainState.W4NamedJustificationMonotone
public import DecoupledConsensusProofs.Execution.PreparedReadBridge
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Splitting the corresponding branch's carrier-chain finality pin

`W4CarrierChainFinalityPin` (`W4D2OpeningCarrierFinalityRun.lean`) bundles four
of earlier's steps because the link between the two carriers' proposals crosses
the erased/named boundary. This file removes that reason: the link is proved
here from live clean lemmas, so the bundle splits into the two genuine
producers.

The chain, all live and clean:

* `proposedBlock_emitted_of_admissible` and
  `proposedBlock_preceq_of_canonicalSuffixExecution`
  (`Availability/PostHealingProposalLifecycleRun.lean:105,156`) put the earlier
  carrier's `+2` proposal below the later carrier's `+1` proposal, as erased
  blocks;
* `proposedBlockAt_blockInRun_of_admissible`
  (`NamedProposalBridge.lean:638`) makes both of them run blocks;
* `namedPreceq_iff_erase_preceq` (`PreparedReadBridgeRun.lean:333`) lifts that
  erased ancestry to named ancestry, because run-wide roots are collision-free
  under `Admissible`;
* `namedJustification_le_of_preceq`
  (`W4NamedJustificationMonotoneRun.lean`) then carries the justification
  height along the named chain.

What is left are exactly two producers, one per narrow pin below: the named
form of `carrierJustificationHeight_of_firstHalf`
(`CanonicalRegimeSecondCheckpointRun.lean:236`, parked) and the named form of
`canonicalCarrier_commonFinalized_of_justifiedPrefix`
(`FinalityFromJustifiedPrefixRun.lean:22`, live in source but below the red
set).

The split needs one hypothesis earlier's route also uses,
`ProposerCarrierAt S rho c`, for the honesty of the proposer of the earlier
carrier's `+2` slot; `CarrierFinalityFirstHalfAt` has no carrier field, so it
cannot be recovered inside the pin body. the corresponding branch's producer has it in scope
at the call site, and `W4CarrierChainFinalityPin` now carries it, so
`w4CarrierChainFinalityPin_of_split` below discharges that pin outright. -/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]




/-
/-- Narrow pin A: the named form of `carrierJustificationHeight_of_firstHalf`
(`CanonicalRegimeSecondCheckpointRun.lean:236`, parked). The witness is a named
ancestor of the carrier's `+2` proposal whose named justification height is the
carrier's opening height. -/
def W4CarrierJustificationHeightPin (S: Setup V) (rho: Run V): Prop:=
  ∀ (r: Round) (C: Block V) (P2: NamedBlock V),
    CarrierFinalityFirstHalfAt S rho r C →
    (∀ P0: NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r) = some P0 →
      (Protocol.derive_named S.E S.cfg P0).nj = false) →
    proposedBlockAt S rho (S.hc.opening_slot r + 2) = some P2 →
    ∃ X: NamedBlock V, NamedBlock.Preceq X P2 ∧
      (Protocol.derive_named S.E S.cfg X).h_j = carrierOpeningHeight S rho r

-/

/-- Narrow pin B: the named form of
`canonicalCarrier_commonFinalized_of_justifiedPrefix`
(`FinalityFromJustifiedPrefixRun.lean:22`, below the red set). A non-lost
carrier finalizes a height its `+1` proposal already justifies. -/
def W4CommonFinalizedOfJustifiedPrefixPin
    (S : Setup V) (rho : Run V) (q0 : Round) : Prop :=
  ∀ (source first r : Round) (Cr Endr : Block V) (P1 : NamedBlock V),
    CanonicalRegimeRoundAt S rho q0 r →
    MovingChainAtCarrierFor S rho q0 r Cr Endr →
    ¬ LostRoundAt S rho r →
    S.E.t_GST ≤ Protocol.proposal_time S.E (S.hc.opening_slot r) →
    proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1 →
    carrierOpeningHeight S rho first ≤
      (Protocol.derive_named S.E S.cfg P1).h_j →
    honestHMaxAt S rho (S.a q0) < carrierOpeningHeight S rho first →
    1 < carrierOpeningHeight S rho first →
    source < r →
    S.a (r + 1) ≤ rho.horizon →
    AlreadyCommonFinalizedAtOrAbove S rho q0 source (r + 1)
      (carrierOpeningHeight S rho first)



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
