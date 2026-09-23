module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.W4FKChainSecondCheckpoint
public import DecoupledConsensusProofs.Protocol.ChainState.W4FKChainFinalityWrite
public import DecoupledConsensusProofs.Protocol.ValidatorClient.W4FKChainFinalityRows
public import DecoupledConsensusProofs.Protocol.Grades.W4FKChainCompose

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # W4 branches fk-chain: `W4CommonFinalizedOfJustifiedPrefixPin`

Named proof of `canonicalCarrier_commonFinalized_of_justifiedPrefix`
(`FinalityFromJustifiedPrefixRun.lean:22-115`, live in source but below the red
set and in the erased earlier shape). earlier's route is followed step for step:

1. the second-carrier checkpoint (proof 3a,
   `carrierFinalitySecondCheckpointAt_of_regime_of_pins`) either fires the
   early arm, which IS the witness, or hands out the live justification
   `(hJ, J)` of the carrier's slot-`+1` proposal with the anti-slashing record
   clear at `hJ` at every honest reader;
2. the honest round rows then carry that exact finality pair
   (`actionAttestation_finality_pair_of_recordGuard`, proof 1);
3. the carrier's `+2` proposal carries every honest row
   (`carrierPlusTwoCarriesRoundRows_named`, branches C1) and its named parent is
   the `+1` proposal, so the rows perform the named finality write
   (`namedFinalizedAt_of_actionRows`);
4. the finalized checkpoint is lifted to a named run block with its own named
   height (`namedCheckpoint_of_namedFinalizedAt`), which is the form
   `Internal.CommonFinalizedWitnessAt` asks for;
5. the store-side conclusion is the pinned
   `W4CommonFinalityAtConfirmationPin`.

Two pins remain, both stated in `W4FKChainSecondCheckpointRun`: the carrier's
action-head cone and the named `commonFinalityAtConfirmation`. Everything else
is proved.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

set_option linter.unusedVariables false in
/-- The carrier-chain common-finality step at one carrier round, over the two
named pins.

`hchain` and `hnl` are retained because the pin's shape carries them; the named
route does not consume them. earlier reaches the `+2` row carriage through the
floor's grade and the resolved-attestation list, while the named proposal duty
selects `poolAndCarried` rows, so `carrierPlusTwoCarriesRoundRows_named` needs
no grade and no floor activity at all. -/
theorem canonicalCarrier_commonFinalized_of_justifiedPrefix_of_suffix
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbot : BelowOneThird S rho.honest)
    {q0 : Round}
    (hsuffix : CanonicalSuffixFrom S rho (healingBoundaryTime S q0))
    (hheadPin : ∀ r : Round, CanonicalRegimeRoundAt S rho q0 r →
      W4SecondCarrierActionHeadPin S rho r)
    (hconfPin : W4CommonFinalityAtConfirmationPin S rho q0)
    {source first r : Round} {Cr Endr : Block V} {P1 : NamedBlock V}
    (hround : CanonicalRegimeRoundAt S rho q0 r)
    (hchain : MovingChainAtCarrierFor S rho q0 r Cr Endr)
    (hnl : ¬ LostRoundAt S rho r)
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hP1 : proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1)
    (hjust : carrierOpeningHeight S rho first ≤
      (derive_named S.E S.cfg P1).h_j)
    (habove : honestHMaxAt S rho (S.a q0) < carrierOpeningHeight S rho first)
    (hone : 1 < carrierOpeningHeight S rho first)
    (hsource : source < r)
    (hhor : S.a (r + 1) ≤ rho.horizon) :
    AlreadyCommonFinalizedAtOrAbove S rho q0 source (r + 1)
      (carrierOpeningHeight S rho first) := by
  -- the first carrier's opening proposal names the source height
  have hPfirst := canonicalProposal_spec S rho (S.hc.opening_slot first)
  set Pfirst := canonicalProposal S rho (S.hc.opening_slot first) with hPfirstDef
  have hHeq : carrierOpeningHeight S rho first =
      (derive_named S.E S.cfg Pfirst).h := rfl
  rw [hHeq] at hjust habove hone ⊢
  -- slot and time arithmetic
  have hslotTwo : S.hc.opening_slot r + 2 ≤ S.hc.opening_slot (r + 1) := by
    simpa only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul] using
      Nat.add_le_add_left S.hc.R_ge_two (r * S.hc.R)
  have hconfTwo : Protocol.confirmation_time S.E (S.hc.opening_slot r + 2) ≤
      S.a (r + 1) := by
    simpa only [Setup.a, Protocol.a_eq_confirmation_time] using
      Int.add_le_add_right (Protocol.proposal_time_mono S.E hslotTwo) (6 * S.E.Δ)
  have hconfOne : Protocol.confirmation_time S.E (S.hc.opening_slot r + 1) ≤
      S.a (r + 1) :=
    (Int.add_le_add_right
      (Protocol.proposal_time_mono S.E (Nat.le_succ _)) (6 * S.E.Δ)).trans hconfTwo
  have hsourceOpening : S.a source ≤
      Protocol.proposal_time S.E (S.hc.opening_slot r) :=
    (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
      (Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt S hsource)
  have hhorTwo : Protocol.proposal_time S.E (S.hc.opening_slot r + 2) ≤
      rho.horizon :=
    (Protocol.proposal_time_le_confirmation_time S.E _).trans hround.inHorizon
  have hhorOne : Protocol.proposal_time S.E (S.hc.opening_slot r + 1) ≤
      rho.horizon :=
    (Protocol.proposal_time_mono S.E (Nat.le_succ _)).trans hhorTwo
  -- the second-carrier checkpoint
  have hcheckpoint := carrierFinalitySecondCheckpointAt_of_regime_of_suffix
    S adm hbot hsuffix hround
    (by simpa only [opening_confirmation_time_eq_action] using
      hpost.trans (Protocol.proposal_time_le_confirmation_time S.E _))
    (hheadPin r hround) hconfPin hPfirst hP1 hjust
    habove hone
    (hsourceOpening.trans (Protocol.proposal_time_mono S.E (Nat.le_succ _)))
    hconfOne hhor
  rcases hcheckpoint Pfirst P1 hPfirst hP1 with hearly | ⟨hJ, J, hbound, hready⟩
  · exact hearly
  -- the `+2` proposal and its named parent
  obtain ⟨P2, hP2⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot r + 2)
  obtain ⟨P0r, hP0r⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot r)
  have hplusTwoParent : proposedParent S rho (S.hc.opening_slot r + 2) = P1.erase :=
    (canonicalCarrierParentEqualities_of_canonicalSuffixFrom S adm hsuffix
      hround.afterBoundary hround.carrier hround.inHorizon P0r P1 hP0r hP1).2
  have hP2parent : P2.parent = P1 :=
    namedProposalParent_eq_of_honest S adm (Nat.zero_lt_succ _)
      hround.carrier.2.1 hround.carrier.2.2 hhorTwo hP1 hP2 hplusTwoParent
  -- one honest reader fixes the checkpoint fields
  have hquorum := AlignedRoundLemmas.honestQuorum_of_belowOneThird hbot
  obtain ⟨v0, -, hv0⟩ := AlignedRoundLemmas.honest_member_of_quorum hbot hquorum
  obtain ⟨-, hhj, hJblock, hdebt, -, -, -⟩ := hready v0 hv0
  -- every honest round row carries the exact finality pair
  have hP1run : RunBlock S rho P1 :=
    proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
      (S.hc.opening_slot r + 1) (Nat.zero_lt_succ _) hround.carrier.2.1 hhorOne hP1
  have hrows : ∀ w ∈ rho.honest,
      (actionAttestationAt S rho w r).finality_pair = some ⟨hJ, J.root⟩ := by
    intro w hw
    obtain ⟨hhead, hhjW, hJW, hdebtW, htargetW, htimeoutW, hlockW⟩ := hready w hw
    exact actionAttestation_finality_pair_of_recordGuard S adm hw hP1run hhead
      hhjW hJW hdebtW htargetW htimeoutW hlockW
  -- the named finality write at the `+2` proposal
  have hcarried := carrierPlusTwoCarriesRoundRows_named S adm hround hpost P2 hP2
  have hfinalized : NamedFinalizedAt S.E S.cfg P2 J hJ :=
    namedFinalizedAt_of_actionRows S hbot hP2
      (fun w hw => Or.inr (hcarried w hw))
      (by rw [hP2parent]; exact hhj)
      (by rw [hP2parent]; exact hJblock)
      rfl
      (by rw [hP2parent]; exact hdebt)
      hrows
  -- the checkpoint as a named run block
  have hJone : 1 < hJ := hone.trans_le hbound
  have hJpos : 0 < hJ := Nat.zero_lt_of_lt hJone
  obtain ⟨cp, hcpLe, hcpErase, hcpHeight⟩ :=
    namedCheckpoint_of_namedFinalizedAt S.E S.cfg hfinalized hJpos
  have hP2run : RunBlock S rho P2 :=
    proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
      (S.hc.opening_slot r + 2) (Nat.zero_lt_succ _) hround.carrier.2.2 hhorTwo hP2
  have hcpRun : RunBlock S rho cp :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hP2run hcpLe
  have hcpFinalized : NamedFinalizedAt S.E S.cfg P2 cp.erase hJ := by
    rw [hcpErase]
    exact hfinalized
  have hcpNe : cp.erase ≠ Block.genesis := by
    rw [hcpErase]
    exact namedFinalizedCheckpoint_ne_genesis S.E S.cfg hfinalized hJone
  -- the common store conclusion
  have hafterTwo : healingBoundaryTime S q0 <
      Protocol.proposal_time S.E (S.hc.opening_slot r + 2) :=
    hround.afterBoundary.trans_le
      (Protocol.proposal_time_mono S.E (Nat.le_add_right _ 2))
  have hcommon := hconfPin (S.hc.opening_slot r + 2) P2 cp.erase hJ
    (Nat.zero_lt_succ _) hafterTwo hround.carrier.2.2
    (hconfTwo.trans hhor) hP2 hcpFinalized hJpos hcpNe
  have hlower : S.a source ≤
      Protocol.proposal_time S.E (S.hc.opening_slot r + 2) :=
    hsourceOpening.trans
      (Protocol.proposal_time_mono S.E (Nat.le_add_right _ 2))
  exact ⟨S.hc.opening_slot r + 2, P2, cp, hJ, Nat.zero_lt_succ _, hafterTwo,
    hround.carrier.2.2, hP2, hcpRun, hcpFinalized, hbound, hcpHeight, hcpNe,
    hlower,
    hlower.trans (Protocol.proposal_time_le_confirmation_time S.E _),
    hconfTwo.trans (Assembly.a_mono S (Nat.le_refl _)), hcommon⟩


/-- the corresponding branch's second narrow pin, discharged over the two named pins, stated
over the execution record's `canonicalSuffixFrom` field: the prepared
record shares that field by name, so this serves either record. -/
theorem w4CommonFinalizedOfJustifiedPrefixPin_of_pins_of_suffix
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbot : BelowOneThird S rho.honest) {q0 : Round}
    (hsuffix : CanonicalSuffixFrom S rho (healingBoundaryTime S q0))
    (hheadPin : ∀ r : Round, CanonicalRegimeRoundAt S rho q0 r →
      W4SecondCarrierActionHeadPin S rho r)
    (hconfPin : W4CommonFinalityAtConfirmationPin S rho q0) :
    W4CommonFinalizedOfJustifiedPrefixPin S rho q0 :=
  fun _ _ _ _ _ _ hround hchain hnl hpost hP1 hjust habove hone hsource hhor =>
    canonicalCarrier_commonFinalized_of_justifiedPrefix_of_suffix S adm hbot
      hsuffix hheadPin hconfPin hround hchain hnl hpost hP1 hjust habove hone
      hsource hhor



/-- The whole of item 5: the corresponding branch's carrier-chain pin from the two named
pins of this branches. `W4CarrierJustificationHeightPin` does not appear: its
content is proved in `W4FKChainComposeRun` with the carrier premises the split
pin lacks. -/
theorem w4CarrierChainFinalityPin_of_pins_of_suffix
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbot : BelowOneThird S rho.honest) {q0 : Round}
    (hsuffix : CanonicalSuffixFrom S rho (healingBoundaryTime S q0))
    (hheadPin : ∀ r : Round, CanonicalRegimeRoundAt S rho q0 r →
      W4SecondCarrierActionHeadPin S rho r)
    (hconfPin : W4CommonFinalityAtConfirmationPin S rho q0) :
    W4CarrierChainFinalityPin S rho q0 :=
  w4CarrierChainFinalityPin_of_commonFinalized_of_suffix S adm hbot hsuffix
    (w4CommonFinalizedOfJustifiedPrefixPin_of_pins_of_suffix S adm hbot hsuffix
      hheadPin hconfPin)


#print axioms canonicalCarrier_commonFinalized_of_justifiedPrefix_of_suffix
#print axioms w4CommonFinalizedOfJustifiedPrefixPin_of_pins_of_suffix
#print axioms w4CarrierChainFinalityPin_of_pins_of_suffix

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
