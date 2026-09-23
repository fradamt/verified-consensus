module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.CanonicalRegimeAssembly
public import DecoupledConsensusProofs.Execution.CanonicalRegimeProducer
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.CarrierFirst
public import DecoupledConsensusProofs.Execution.PostHealingProposalLifecycle
public import DecoupledConsensusProofs.Protocol.ChainState.RecurringFinality
public import DecoupledConsensusProofs.Execution.StoreFinalityRun

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# The canonical carrier record from the moving-chain slot state

`CanonicalSuffixExecution` keeps its proposal suffix and its action-output
suffix as two separate existential endpoint chains. The healing track's
moving-chain fold keeps them joined: one endpoint block per event, with the
honest genuine confirmations, the honest SG carriers, the read anchors and the
honest height-gate sources all below it.

This module states that joined data at one carrier's opening slot as the
interface `MovingChainAtCarrier`, and derives the full `CanonicalRegimeRoundAt`
record from it together with FK11's execution core. `MovingChainAtCarrier` is
**not** a review residual: it is the exact hand-off the healing slot fold is
built to produce. Every field is a statement about the moving endpoint `End`
at `opening_slot r`, never about the finality machinery.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}


/-- **A lost round.**

The round's FG root, as some honest reader selects it, is NOT below some
honest previous-round SG carrier.

This is exactly the obstruction to a common floor, and nothing weaker is. A
floor `C` has to satisfy `root_v ⪯ C` for every reader `v` and `C ⪯ carrier_w`
for every author `w`, so transitivity would put every root below every carrier
(`not_roundFloorFieldsAt_of_lost`).

Protocol reading: the round's timeout gate is open at a justified block that
sits above an honest confirmation one height lower. Nothing above that root
then carries a grade, so `grade2_block` is empty at every honest reader, the
height pair is disabled, and the round emits no honest height rows at all. The
round is silent rather than wrong, which is why the records exempt it instead of
asserting a floor that does not exist. -/
def LostRoundAt (S : Setup V) (rho : Run V) (r : Round) : Prop :=
  ∃ v ∈ rho.honest, ∃ w ∈ rho.honest,
    ¬ Block.Preceq
        (Protocol.get_fg_root (healStoreAt S rho v r).toFG)
        (actionSGBlockAt S rho w (r - 1))

/-- The three floor facts a non-lost round supplies.

`floorProcessed` is deliberately absent: viability never needed the floor in
the reader's tree, only a processed descendant of it, which is exactly
`floorWitness`. -/
structure RoundFloorFieldsAt
    (S : Setup V) (rho : Run V) (r : Round) (C : Block V) : Prop where
  /-- The floor is below every honest previous-round SG carrier. -/
  floorBelowCarriers : ∀ w ∈ rho.honest,
    Block.Preceq C (actionSGBlockAt S rho w (r - 1))
  /-- Every honest FG root at the round read is below the floor. -/
  floorAboveRoots : ∀ v ∈ rho.honest,
    Block.Preceq
      (Protocol.get_fg_root (healStoreAt S rho v r).toFG) C
  /-- A processed descendant of the floor sits at the local frontier band. -/
  floorWitness : ∀ v ∈ rho.honest,
    CanonicalConeWitness (rho.storeBeforeTime S v (S.a r)).core C



/-- The moving-chain hand-off at the opening slot of carrier `r`.

`End` is the slot-entry endpoint (the deepest genuine confirmation selected
before the carrier's opening proposal) and `C` is the common SG floor of the
round-`(r-1)` batch. The two blocks are the only data; every field is a
directional or delivery fact the slot fold already carries. -/
structure MovingChainAtCarrierFor
    (S : Setup V) (rho : Run V) (q0 r : Round) (C End : Block V) : Prop where
  /-- The endpoint is below the carrier's honest opening proposal. -/
  endpointBelowOpening : ∀ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P →
      Block.Preceq End P.erase
  /-- Every honest round-`(r-1)` SG carrier is below the endpoint. -/
  carriersBelowEndpoint : ∀ w ∈ rho.honest,
    Block.Preceq (actionSGBlockAt S rho w (r - 1)) End
  
  batchComplete : ∀ v ∈ rho.honest, ∀ w ∈ rho.honest,
    CanonicalBatchVoteAt S rho r
      (actionStoreAt S rho v r).toHealing.gradeView w
  /-- Either the round is lost, or it has a common floor.

  The round is exempt exactly when no floor can exist
  (`not_roundFloorFieldsAt_of_lost`), so this is the weakest possible
  restatement of the four old floor fields. -/
  roundFloor : LostRoundAt S rho r ∨ RoundFloorFieldsAt S rho r C
  /-- Every honest read anchor is below the endpoint. -/
  anchorsBelowEndpoint : ∀ v ∈ rho.honest,
    Block.Preceq
      (Proofs.Optimistic.healAnchor S.E S.hc
        (actionStoreAt S rho v r).toHealing) End
  /-- Every honest named action-read anchor is below the endpoint. -/
  namedAnchorsBelowEndpoint : ∀ v ∈ rho.honest,
    Block.Preceq
      (PhaseGrades.nodeAnchor S (actionReadAt S rho v r) r) End
  /-- At the carrier's `+2` proposal read, the floor is still a candidate or
  is strictly below the selected FG root. -/
  floorActiveAtPlusTwoProposal :
    C ∈ Protocol.get_filtered_block_tree
      (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot r + 2)).toHealing.toFG ∨
      Block.Prec C
        (Protocol.get_fg_root
          (rho.storeBeforeTime S
            (S.E.proposer (S.hc.opening_slot r + 2))
            (Protocol.proposal_time S.E
              (S.hc.opening_slot r + 2))).core.toHealing.toFG)
  /-- The carrier's slot-`+1` proposal is a candidate at every honest read. -/
  plusOneCandidate : ∀ v ∈ rho.honest, ∀ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P →
    P.erase ∈
      Protocol.get_filtered_block_tree
        (actionStoreAt S rho v r).st.core.toHealing.toFG
  /-- Post-boundary honest height sources are below the endpoint. -/
  heightHistory : ∀ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P →
      CanonicalHeightSourceHistoryAt S rho q0 r P
  /-- Recorded target entries have a canonical origin below the endpoint. -/
  targetHistory : ∀ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P →
      CanonicalTargetHistoryAt S rho q0 r P
  /-- Recorded timeout entries have a canonical origin below the endpoint. -/
  timeoutHistory : ∀ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P →
      CanonicalTimeoutHistoryAt S rho q0 r P


/-- The floor fields of a round that is not lost. -/
theorem MovingChainAtCarrierFor.floorFields
    {S : Setup V} {rho : Run V} {q0 r : Round} {C End : Block V}
    (h : MovingChainAtCarrierFor S rho q0 r C End)
    (hnl : ¬ LostRoundAt S rho r) : RoundFloorFieldsAt S rho r C :=
  h.roundFloor.resolve_left hnl

/-- Existential form of the moving-chain hand-off at carrier `r`. -/
def MovingChainAtCarrier
    (S : Setup V) (rho : Run V) (q0 r : Round) : Prop :=
  ∃ C End : Block V, MovingChainAtCarrierFor S rho q0 r C End








/-
/-- The moving-chain floor is the common grade at the carrier round and is
still a candidate at the carrier's `+2` proposal. -/
theorem MovingChainAtCarrierFor.gradeFormsAt
    {S: Setup V} {rho: Run V} (adm: Admissible S rho)
    (hmajority: HonestWeightMajority S rho.honest)
    {q0 r: Round} {C End: Block V}
    (hchain: MovingChainAtCarrierFor S rho q0 r C End)
    (hsole: ∀ v ∈ rho.honest, ∀ w ∈ rho.honest,
      (Protocol.sg_votes_by
        (Protocol.round_batch
          (actionStoreAt S rho v r).toHealing.gradeView r) w).card ≤ 1)
    (hnl: ¬ LostRoundAt S rho r):
    GradeFormsAt S rho r C:=
  gradeFormsAt_of_batchFields_of_active hsole hchain.batchComplete
    hmajority (hchain.floorFields hnl).floorBelowCarriers
    (gradeFloor_active_everywhere S adm
      (hchain.floorFields hnl).floorAboveRoots
      (hchain.floorFields hnl).floorWitness)
-/




/-- Every post-boundary carrier that the moving-chain fold reaches has the full
canonical record. -/
def MovingChainAtCarrierFrom
    (S : Setup V) (rho : Run V) (q0 : Round) : Prop :=
  ∀ r, healingBoundaryTime S q0 <
        Protocol.proposal_time S.E (S.hc.opening_slot r) →
      ProposerCarrierAt S rho r →
      Protocol.confirmation_time S.E
          (S.hc.opening_slot r + 2) ≤ rho.horizon →
      MovingChainAtCarrier S rho q0 r








/-! ## The first-carrier half of a recurring-finality phase -/

/-- Every field of `RecurringFinalityPhaseAt` that speaks about the phase's
first carrier. -/
structure CarrierFinalityFirstHalfAt
    (S : Setup V) (rho : Run V) (r : Round) (C : Block V) : Prop where
  grade : NamedGradeFormsAt S rho r C
  gradeBelowOpening : ∀ P0 : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P0 →
      Block.Preceq C P0.erase
  plusOneParent : ∀ P0 P1 : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P0 →
    proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1 →
      proposedParent S rho (S.hc.opening_slot r + 1) = P0.erase
  checkpointReady : ∀ P0 P1 : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P0 →
    proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1 →
      NamedJustifiedAt S.E S.cfg P1
          (Protocol.derive_named S.E S.cfg P0).T_h
          (Protocol.derive_named S.E S.cfg P0).h ∨
        ((Protocol.derive_named S.E S.cfg P1).h =
            (Protocol.derive_named S.E S.cfg P0).h ∧
          (Protocol.derive_named S.E S.cfg P1).T_h =
            (Protocol.derive_named S.E S.cfg P0).T_h)
  plusTwoParent : ∀ P1 P2 : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1 →
    proposedBlockAt S rho (S.hc.opening_slot r + 2) = some P2 →
      proposedParent S rho (S.hc.opening_slot r + 2) = P1.erase
  actionCoverage : ∀ P0 P2 : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P0 →
    proposedBlockAt S rho (S.hc.opening_slot r + 2) = some P2 →
      NamedHonestActionProposalCoverageAt S rho r P2
        (Protocol.derive_named S.E S.cfg P0).h
        (Protocol.derive_named S.E S.cfg P0).T_h.root
  rowsCarriedAtPlusTwo : ∀ P2 : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r + 2) = some P2 →
    ∀ v ∈ rho.honest, actionAttestationAt S rho v r ∈ P2.attestations
  targetRows : ∀ P0 : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P0 →
    ∀ v ∈ rho.honest,
      (actionAttestationAt S rho v r).height_pair =
        .vote (Protocol.derive_named S.E S.cfg P0).h
          (Protocol.derive_named S.E S.cfg P0).T_h.root false
  actionHeadEq : ∀ P0 P1 : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P0 →
    proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1 →
    ∀ v ∈ rho.honest, actionHeadAt S rho v r = P1.erase


/-
/-- The disjunctive moving-chain floor condition still resolves every honest
round row. In the strict-root branch, the canonical round cones independently
put the row's SG carrier below the `+2` proposal parent. -/
theorem honestPlusTwoBlock_resolvedRoundRows_of_chain_or_prec_root
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {q0 r: Round} {C End: Block V}
    (hforms: GradeFormsAt S rho r C)
    (hround: CanonicalRegimeRoundAt S rho q0 r)
    (hchain: MovingChainAtCarrierFor S rho q0 r C End)
    (hpost: S.E.t_GST ≤ S.a r)
    (hhor: Protocol.proposal_time S.E (S.hc.opening_slot r + 2) ≤ rho.horizon)
    {v: V} (hv: v ∈ rho.honest):
    actionAttestationAt S rho v r ∈
      (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot r + 2)).resolved_attestations S.hc:= by
  rcases honestPlusTwoBlock_resolvedRoundRows_of_gradeFormsAt_or_prec_root
      S adm hforms hround.carrier hpost hhor
        hchain.floorActiveAtPlusTwoProposal hv with hresolved | _hCroot
  · exact hresolved
  · have hcarrierOpening: Block.Preceq (actionSGBlockAt S rho v r)
        (proposedBlock S rho (S.hc.opening_slot r)):= by
      have hsource:= sg_vote_preceq_source S.E S.hc
        (actionStoreAt S rho v r).toHealing r (hround.openingSource v hv)
      simpa only [actionSGBlockAt] using hsource
    have hcarrierParent: Block.Preceq (actionSGBlockAt S rho v r)
        (Protocol.proposedParent S rho (S.hc.opening_slot r + 2)):=
      Block.preceq_trans hcarrierOpening
        (Block.preceq_trans hround.plusOneCone
          (Block.preceq_trans
            (Protocol.proposedParent_preceq_proposedBlock S rho
              (S.hc.opening_slot r + 1))
            hround.plusTwoCone))
    exact
      honestPlusTwoBlock_resolvedRoundRows_of_carrier_preceq_proposedParent
        S adm hround.carrier hpost hhor hv hcarrierParent
-/


/- /-- The complete first-carrier half from the canonical regime, the
moving-chain hand-off, a justifiable opening, and the carrier's slot-`+1`
checkpoint open supplied by the caller.
The two wrappers below give the two ways to supply that last argument: the
recent-entry route, and the unconditional route that keeps a height advance as
a third outcome. -/
/-- The complete first-carrier half from the canonical regime, the
moving-chain hand-off, a justifiable opening, and the carrier's slot-`+1`
checkpoint open supplied by the caller.

The two wrappers below give the two ways to supply that last argument: the
recent-entry route, and the unconditional route that keeps a height advance as
a third outcome. -/
theorem carrierFinalityFirstHalfAt_of_regime_of_checkpointReady
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hbot: BelowOneThird S rho.honest)
    (hmajority: HonestWeightMajority S rho.honest)
    {q0 r: Round} {C End: Block V}
    (hexec: CanonicalSuffixExecution S rho q0)
    (hround: CanonicalRegimeRoundAt S rho q0 r)
    (hchain: MovingChainAtCarrierFor S rho q0 r C End)
    (hnl: ¬ LostRoundAt S rho r)
    (hnj: (derived_state S.E S.cfg
      (proposedBlock S rho (S.hc.opening_slot r))).nj = false)
    (habove: honestHMaxAt S rho (S.a q0) <
      (derived_state S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot r))).h)
    (hcheckpoint:
      JustifiedAt S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r + 1))
          (derived_state S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot r))).T_h
          (derived_state S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot r))).h ∨
        ((derived_state S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot r + 1))).h =
              (derived_state S.E S.cfg
                (proposedBlock S rho (S.hc.opening_slot r))).h ∧
          (derived_state S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot r + 1))).T_h =
              (derived_state S.E S.cfg
                (proposedBlock S rho (S.hc.opening_slot r))).T_h))
    (hpost: S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot r)):
    CarrierFinalityFirstHalfAt S rho r C:= by
  have hquorum:= AlignedRoundLemmas.honestQuorum_of_belowOneThird hbot
  obtain ⟨v0, -, hv0⟩:=
    AlignedRoundLemmas.honest_member_of_quorum hbot hquorum
  have hfloorOpening: Block.Preceq C
      (proposedBlock S rho (S.hc.opening_slot r)):=
    Block.preceq_trans ((hchain.floorFields hnl).floorBelowCarriers v0 hv0)
      (Block.preceq_trans (hchain.carriersBelowEndpoint v0 hv0)
        hchain.endpointBelowOpening)
  have hforms: GradeFormsAt S rho r C:=
    hchain.gradeFormsAt adm hmajority hround.batchSole hnl
  have hplusOneParent:
      Protocol.proposedParent S rho (S.hc.opening_slot r + 1) =
        proposedBlock S rho (S.hc.opening_slot r):=
    proposedParent_eq_previousSlotBlock_of_preceq S adm
      (Protocol.proposedBlock_slot S rho (S.hc.opening_slot r))
      hround.plusOneCone
  have hplusTwoParent:
      Protocol.proposedParent S rho (S.hc.opening_slot r + 2) =
        proposedBlock S rho (S.hc.opening_slot r + 1):= by
    have:= proposedParent_eq_previousSlotBlock_of_preceq S adm
      (Protocol.proposedBlock_slot S rho (S.hc.opening_slot r + 1))
      (by simpa only [Nat.add_assoc] using hround.plusTwoCone)
    simpa only [Nat.add_assoc] using this
  have hactivity: CanonicalGradeFloorActivityResidualAt S rho r:=
    canonicalGradeFloorActivityResidualAt_of_canonicalFloor
      S adm hfloorOpening (hchain.floorFields hnl).floorBelowCarriers
        (hchain.floorFields hnl).floorAboveRoots
        (hchain.floorFields hnl).floorWitness
  have hlockAligned:=
    CanonicalRegimeRoundAt.successorTargetLockAlignment_of_aboveBoundary
      S adm hbot hround habove
  obtain ⟨-, -, hrows⟩:= carrierRows_exactTargets
    S adm hcom hmajority hexec hround hactivity habove hnj hlockAligned
  have hhorProposalTwo: Protocol.proposal_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon:=
    (proposal_time_le_confirmation_time S.E _).trans hround.inHorizon
  have hpostAction: S.E.t_GST ≤ S.a r:= by
    refine hpost.trans ?_
    have hconf: S.a r = Protocol.confirmation_time S.E
        (S.hc.opening_slot r):= by
      simp only [Setup.a, Protocol.a_eq_confirmation_time]
    rw [hconf]
    exact proposal_time_le_confirmation_time S.E _
  have hcone:= canonicalCarrierActionHeadPlusOneConeAt_of_residual
    S adm hcom hexec hround.afterBoundary hround.carrier hpost
      hround.inHorizon hround.actionHistoryResidual
  refine
    { grade:= hforms
      gradeBelowOpening:= hfloorOpening
      plusOneParent:= hplusOneParent
      checkpointReady:= ?_
      plusTwoParent:= hplusTwoParent
      actionCoverage:= ?_
      rowsCarriedAtPlusTwo:= ?_
      targetRows:= hrows
      actionHeadEq:=
        carrierActionHead_eq_plusOne S adm hexec hround.carrier hcone }
  · exact hcheckpoint
  · intro v hv
    have hresolved:=
      honestPlusTwoBlock_resolvedRoundRows_of_chain_or_prec_root
        S adm hforms hround hchain hpostAction hhorProposalTwo hv
    exact ⟨Or.inr (plusTwoProposal_carries_resolvedRoundRow
      S adm hround.carrier hhorProposalTwo hv hresolved),
      Or.inl (hrows v hv)⟩
  · intro v hv
    have hresolved:=
      honestPlusTwoBlock_resolvedRoundRows_of_chain_or_prec_root
        S adm hforms hround hchain hpostAction hhorProposalTwo hv
    exact plusTwoProposal_carries_resolvedRoundRow
      S adm hround.carrier hhorProposalTwo hv hresolved
-/


/-
/-- The two second-carrier facts the phase needs. Neither depends on the
opening being justifiable, so they are available at every carrier. -/
theorem carrierPlusTwoFacts_of_regime
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hmajority: HonestWeightMajority S rho.honest)
    {q0 r: Round} {C End: Block V}
    (hround: CanonicalRegimeRoundAt S rho q0 r)
    (hchain: MovingChainAtCarrierFor S rho q0 r C End)
    (hnl: ¬ LostRoundAt S rho r)
    (hpost: S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot r)):
    Protocol.proposedParent S rho (S.hc.opening_slot r + 2) =
        proposedBlock S rho (S.hc.opening_slot r + 1) ∧
      ∀ v ∈ rho.honest,
        actionAttestationAt S rho v r ∈
          (proposedBlock S rho (S.hc.opening_slot r + 2)).attestations:= by
  have hforms: GradeFormsAt S rho r C:=
    hchain.gradeFormsAt adm hmajority hround.batchSole hnl
  have hhorProposalTwo: Protocol.proposal_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon:=
    (proposal_time_le_confirmation_time S.E _).trans hround.inHorizon
  have hpostAction: S.E.t_GST ≤ S.a r:= by
    refine hpost.trans ?_
    have hconf: S.a r = Protocol.confirmation_time S.E
        (S.hc.opening_slot r):= by
      simp only [Setup.a, Protocol.a_eq_confirmation_time]
    rw [hconf]
    exact proposal_time_le_confirmation_time S.E _
  refine ⟨?_, ?_⟩
  · have:= proposedParent_eq_previousSlotBlock_of_preceq S adm
      (Protocol.proposedBlock_slot S rho (S.hc.opening_slot r + 1))
      (by simpa only [Nat.add_assoc] using hround.plusTwoCone)
    simpa only [Nat.add_assoc] using this
  · intro v hv
    exact plusTwoProposal_carries_resolvedRoundRow
      S adm hround.carrier hhorProposalTwo hv
      (honestPlusTwoBlock_resolvedRoundRows_of_chain_or_prec_root
        S adm hforms hround hchain hpostAction hhorProposalTwo hv)

/-- The recent-entry route: the Rule-A gate is closed at the carrier's slot
`+1`, so its checkpoint is ready. -/
theorem carrierFinalityFirstHalfAt_of_regime
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hbot: BelowOneThird S rho.honest)
    (hmajority: HonestWeightMajority S rho.honest)
    (hdelay: TimeoutDelayBound S delayExtra)
    {q0 r: Round} {C End: Block V}
    (hexec: CanonicalSuffixExecution S rho q0)
    (hround: CanonicalRegimeRoundAt S rho q0 r)
    (hchain: MovingChainAtCarrierFor S rho q0 r C End)
    (hnl: ¬ LostRoundAt S rho r)
    (hnj: (derived_state S.E S.cfg
      (proposedBlock S rho (S.hc.opening_slot r))).nj = false)
    (habove: honestHMaxAt S rho (S.a q0) <
      (derived_state S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot r))).h)
    (hentered: CarrierRecentHeightEntryAt S rho r)
    (hpost: S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot r)):
    CarrierFinalityFirstHalfAt S rho r C:= by
  have hplusOneParent:
      Protocol.proposedParent S rho (S.hc.opening_slot r + 1) =
        proposedBlock S rho (S.hc.opening_slot r):=
    proposedParent_eq_previousSlotBlock_of_preceq S adm
      (Protocol.proposedBlock_slot S rho (S.hc.opening_slot r))
      hround.plusOneCone
  exact carrierFinalityFirstHalfAt_of_regime_of_checkpointReady
    S adm hcom hbot hmajority hexec hround hchain hnl hnj habove
      (carrierPlusOne_checkpointReady S hplusOneParent hdelay hentered hnj)
      hpost

/-- **The unconditional route.** With no recent-entry premise the carrier's
slot-`+1` fold has a third outcome: a progress-only height advance. That arm
is not a failure — the chain height moved — so the producer reports it instead
of excluding it.

This is the form the model actually supports: the recent-entry bound is not
available in general, because an old height-entering block can sit below one
honest live confirmation and not below another at the same read (see
`CanonicalRegimeFirstVoteRun`, section 6). -/
theorem carrierFinalityFirstHalfAt_or_advance_of_regime
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hbot: BelowOneThird S rho.honest)
    (hmajority: HonestWeightMajority S rho.honest)
    {q0 r: Round} {C End: Block V}
    (hexec: CanonicalSuffixExecution S rho q0)
    (hround: CanonicalRegimeRoundAt S rho q0 r)
    (hchain: MovingChainAtCarrierFor S rho q0 r C End)
    (hnl: ¬ LostRoundAt S rho r)
    (hnj: (derived_state S.E S.cfg
      (proposedBlock S rho (S.hc.opening_slot r))).nj = false)
    (habove: honestHMaxAt S rho (S.a q0) <
      (derived_state S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot r))).h)
    (hpost: S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot r)):
    CarrierFinalityFirstHalfAt S rho r C ∨ CarrierAdvanceAt S rho r:= by
  have hplusOneParent:
      Protocol.proposedParent S rho (S.hc.opening_slot r + 1) =
        proposedBlock S rho (S.hc.opening_slot r):=
    proposedParent_eq_previousSlotBlock_of_preceq S adm
      (Protocol.proposedBlock_slot S rho (S.hc.opening_slot r))
      hround.plusOneCone
  rcases carrierPlusOne_checkpointReady_or_advance S hplusOneParent with
      hready | hadvance
  · exact Or.inl (carrierFinalityFirstHalfAt_of_regime_of_checkpointReady
      S adm hcom hbot hmajority hexec hround hchain hnl hnj habove hready
      hpost)
  · exact Or.inr hadvance

/-- **The unconditional route, with the burn's state retained.** Same as
`carrierFinalityFirstHalfAt_or_advance_of_regime`, but the third arm carries
the slot-`+1` state the retry accounting reads: the height moved by one and the
`+1` block is the new height entry. -/
theorem carrierFinalityFirstHalfAt_or_burn_of_regime
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hbot: BelowOneThird S rho.honest)
    (hmajority: HonestWeightMajority S rho.honest)
    {q0 r: Round} {C End: Block V}
    (hexec: CanonicalSuffixExecution S rho q0)
    (hround: CanonicalRegimeRoundAt S rho q0 r)
    (hchain: MovingChainAtCarrierFor S rho q0 r C End)
    (hnl: ¬ LostRoundAt S rho r)
    (hnj: (derived_state S.E S.cfg
      (proposedBlock S rho (S.hc.opening_slot r))).nj = false)
    (habove: honestHMaxAt S rho (S.a q0) <
      (derived_state S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot r))).h)
    (hpost: S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot r)):
    CarrierFinalityFirstHalfAt S rho r C ∨ CarrierBurnAt S rho r:= by
  have hplusOneParent:
      Protocol.proposedParent S rho (S.hc.opening_slot r + 1) =
        proposedBlock S rho (S.hc.opening_slot r):=
    proposedParent_eq_previousSlotBlock_of_preceq S adm
      (Protocol.proposedBlock_slot S rho (S.hc.opening_slot r))
      hround.plusOneCone
  rcases carrierPlusOne_checkpointReady_or_burn S hplusOneParent with
      hready | hburn
  · exact Or.inl (carrierFinalityFirstHalfAt_of_regime_of_checkpointReady
      S adm hcom hbot hmajority hexec hround hchain hnl hnj habove hready
      hpost)
  · exact Or.inr hburn
-/

/-! ## Assembling one recurring-finality phase -/

/-- The remaining producer obligation for the phase's second carrier.

This is the exact `secondCheckpointReady` field of `RecurringFinalityPhaseAt`.
Everything else in the phase is produced by the two first-half records below.
It is stated separately so that the still-open second-carrier chain (the
justification created by the first carrier must reach the second carrier's
slot-`+1` action head with a clear anti-slashing record at its own justified
height) is visible at the producer boundary. -/
def CarrierFinalitySecondCheckpointAt
    (S : Setup V) (rho : Run V) (q source first second : Round) : Prop :=
  ∀ Pfirst Psecond1 : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot first) = some Pfirst →
    proposedBlockAt S rho (S.hc.opening_slot second + 1) = some Psecond1 →
    AlreadyCommonFinalizedAtOrAbove S rho q source (second + 1)
        (Protocol.derive_named S.E S.cfg Pfirst).h ∨
      ∃ hJ J,
        (Protocol.derive_named S.E S.cfg Pfirst).h ≤ hJ ∧
          ∀ v ∈ rho.honest,
            actionHeadAt S rho v second = Psecond1.erase ∧
              (Protocol.derive_named S.E S.cfg Psecond1).h_j = hJ ∧
              (Protocol.derive_named S.E S.cfg Psecond1).J = J ∧
              (Protocol.derive_named S.E S.cfg Psecond1).h_F < hJ ∧
              ((rho.stateBeforeTime S (S.a second) v).Λ.target hJ = none ∨
                (rho.stateBeforeTime S (S.a second) v).Λ.target hJ =
                  some J.root) ∧
              (rho.stateBeforeTime S (S.a second) v).Λ.timeout hJ = false ∧
              ((rho.stateBeforeTime S (S.a second) v).Λ.lock hJ = none ∨
                (rho.stateBeforeTime S (S.a second) v).Λ.lock hJ =
                  some J.root)


/-! ## The recurring-finality phase producer -/

/-- The verified phase lag.

Two raw progress periods lift the selected carrier above the starting
frontier; two more supply the strict height increase that the `K`-band needs;
the three recurrence windows pay for the two candidate carriers and the
finalizing carrier; the final constants pay for the endpoint of the
finalizing `+2` proposal. -/
def recurringFinalityPhaseLag (rawLag recurrenceGap : Round) : Round :=
  4 * rawLag + 4 * recurrenceGap + 7



















/-
/-- Uniform phase production at the verified lag. -/
theorem recurringFinalityPhaseCarrierFrom_of_regime
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hbot: BelowOneThird S rho.honest)
    (hmajority: HonestWeightMajority S rho.honest)
    (hdelay: TimeoutDelayBound S delayExtra)
    {q rawLag gap: Round}
    (hrawPos: 0 < rawLag)
    (hexec: CanonicalSuffixExecution S rho q)
    (hpair: JustifiableCarrierPairFrom S rho q rawLag gap)
    (hrec: MultiProposerRecurrence S rho gap)
    (hafterAll: ∀ r: Round, q + 1 < r →
      healingBoundaryTime S q <
        Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hpostAll: ∀ r: Round, q + 1 < r →
      S.E.t_GST ≤ Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hchain: MovingChainAtCarrierFrom S rho q)
    (hpostBoundary: S.E.t_GST ≤ S.a q)
    (hnotLost: ∀ r: Round, 1 ≤ r → S.E.t_GST ≤ S.a (r - 1) →
      Protocol.confirmation_time S.E (S.hc.opening_slot r + 2) ≤ rho.horizon →
      ¬ LostRoundAt S rho r)
    (hcheckpointAll: ∀ r: Round, q + 2 < r →
      CanonicalRegimeRoundAt S rho q r →
      honestHMaxAt S rho (S.a q) <
        (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r))).h →
      (derived_state S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot r))).nj = false →
      JustifiedAt S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r + 1))
          (derived_state S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot r))).T_h
          (derived_state S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot r))).h ∨
        ((derived_state S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot r + 1))).h =
              (derived_state S.E S.cfg
                (proposedBlock S rho (S.hc.opening_slot r))).h ∧
          (derived_state S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot r + 1))).T_h =
              (derived_state S.E S.cfg
                (proposedBlock S rho (S.hc.opening_slot r))).T_h))
    (hsecondAll: ∀ (start first second: Round) (C: Block V),
      q ≤ start → q + 1 < first → start + 1 < first → first < second →
      S.a (second + 1) ≤ rho.horizon →
      ProposerCarrierAt S rho first → ProposerCarrierAt S rho second →
      CarrierFinalityFirstHalfAt S rho first C →
      (derived_state S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot first))).nj = false →
      honestHMaxAt S rho (S.a start) <
        (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot first))).h →
      CarrierFinalitySecondCheckpointAt S rho q (start + 1) first second):
    RecurringFinalityPhaseCarrierFrom S rho q
      (recurringFinalityPhaseLag rawLag gap):= by
  refine ⟨nat_phaseLag_pos, ?_⟩
  intro start hstart hhor
  exact exists_recurringFinalityPhaseAt_of_regime
    S adm hcom hbot hmajority hdelay hrawPos hexec hpair hrec
      hstart hafterAll hpostAll hchain hpostBoundary hnotLost hcheckpointAll
      (fun first second C h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
        hsecondAll start first second C hstart h1 h2 h3 h4 h5 h6 h7 h8 h9)
      hhor

/-- The declarative recurring-finality contract at the verified deadline. -/
theorem recurringFinalityFrom_of_regime
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hbot: BelowOneThird S rho.honest)
    (hmajority: HonestWeightMajority S rho.honest)
    (hdelay: TimeoutDelayBound S delayExtra)
    {q rawLag gap: Round}
    (hrawPos: 0 < rawLag)
    (hexec: CanonicalSuffixExecution S rho q)
    (hpair: JustifiableCarrierPairFrom S rho q rawLag gap)
    (hrec: MultiProposerRecurrence S rho gap)
    (hafterAll: ∀ r: Round, q + 1 < r →
      healingBoundaryTime S q <
        Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hpostAll: ∀ r: Round, q + 1 < r →
      S.E.t_GST ≤ Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hchain: MovingChainAtCarrierFrom S rho q)
    (hpostBoundary: S.E.t_GST ≤ S.a q)
    (hnotLost: ∀ r: Round, 1 ≤ r → S.E.t_GST ≤ S.a (r - 1) →
      Protocol.confirmation_time S.E (S.hc.opening_slot r + 2) ≤ rho.horizon →
      ¬ LostRoundAt S rho r)
    (hcheckpointAll: ∀ r: Round, q + 2 < r →
      CanonicalRegimeRoundAt S rho q r →
      honestHMaxAt S rho (S.a q) <
        (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r))).h →
      (derived_state S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot r))).nj = false →
      JustifiedAt S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r + 1))
          (derived_state S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot r))).T_h
          (derived_state S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot r))).h ∨
        ((derived_state S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot r + 1))).h =
              (derived_state S.E S.cfg
                (proposedBlock S rho (S.hc.opening_slot r))).h ∧
          (derived_state S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot r + 1))).T_h =
              (derived_state S.E S.cfg
                (proposedBlock S rho (S.hc.opening_slot r))).T_h))
    (hsecondAll: ∀ (start first second: Round) (C: Block V),
      q ≤ start → q + 1 < first → start + 1 < first → first < second →
      S.a (second + 1) ≤ rho.horizon →
      ProposerCarrierAt S rho first → ProposerCarrierAt S rho second →
      CarrierFinalityFirstHalfAt S rho first C →
      (derived_state S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot first))).nj = false →
      honestHMaxAt S rho (S.a start) <
        (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot first))).h →
      CarrierFinalitySecondCheckpointAt S rho q (start + 1) first second):
    RecurringFinalityFrom S rho q
      (recurringFinalityDeadline S
        (recurringFinalityPhaseLag rawLag gap) gap):= by
  refine recurringFinalityFrom_of_phaseCarrier S
    (recurringFinalityPhaseLag rawLag gap) gap adm hcom hbot hexec ?_
  exact (recurringFinalityPhaseCarrierFrom_of_regime
    S adm hcom hbot hmajority hdelay hrawPos hexec hpair hrec
      hafterAll hpostAll hchain hpostBoundary hnotLost hcheckpointAll
      hsecondAll).mono
    (Nat.le_add_right _ _)

/-- Finality of every post-boundary honest proposal at the same deadline. -/
theorem honestProposalFinalityFrom_of_regime
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hbot: BelowOneThird S rho.honest)
    (hmajority: HonestWeightMajority S rho.honest)
    (hdelay: TimeoutDelayBound S delayExtra)
    {q rawLag gap: Round}
    (hrawPos: 0 < rawLag)
    (hexec: CanonicalSuffixExecution S rho q)
    (hpair: JustifiableCarrierPairFrom S rho q rawLag gap)
    (hrec: MultiProposerRecurrence S rho gap)
    (hafterAll: ∀ r: Round, q + 1 < r →
      healingBoundaryTime S q <
        Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hpostAll: ∀ r: Round, q + 1 < r →
      S.E.t_GST ≤ Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hchain: MovingChainAtCarrierFrom S rho q)
    (hpostBoundary: S.E.t_GST ≤ S.a q)
    (hnotLost: ∀ r: Round, 1 ≤ r → S.E.t_GST ≤ S.a (r - 1) →
      Protocol.confirmation_time S.E (S.hc.opening_slot r + 2) ≤ rho.horizon →
      ¬ LostRoundAt S rho r)
    (hcheckpointAll: ∀ r: Round, q + 2 < r →
      CanonicalRegimeRoundAt S rho q r →
      honestHMaxAt S rho (S.a q) <
        (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r))).h →
      (derived_state S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot r))).nj = false →
      JustifiedAt S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r + 1))
          (derived_state S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot r))).T_h
          (derived_state S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot r))).h ∨
        ((derived_state S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot r + 1))).h =
              (derived_state S.E S.cfg
                (proposedBlock S rho (S.hc.opening_slot r))).h ∧
          (derived_state S.E S.cfg
            (proposedBlock S rho (S.hc.opening_slot r + 1))).T_h =
              (derived_state S.E S.cfg
                (proposedBlock S rho (S.hc.opening_slot r))).T_h))
    (hsecondAll: ∀ (start first second: Round) (C: Block V),
      q ≤ start → q + 1 < first → start + 1 < first → first < second →
      S.a (second + 1) ≤ rho.horizon →
      ProposerCarrierAt S rho first → ProposerCarrierAt S rho second →
      CarrierFinalityFirstHalfAt S rho first C →
      (derived_state S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot first))).nj = false →
      honestHMaxAt S rho (S.a start) <
        (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot first))).h →
      CarrierFinalitySecondCheckpointAt S rho q (start + 1) first second):
    HonestProposalFinalityFrom S rho q
      (recurringFinalityDeadline S
        (recurringFinalityPhaseLag rawLag gap) gap):= by
  refine honestProposalFinalityFrom_of_phaseCarrier S
    (recurringFinalityPhaseLag rawLag gap) gap adm hcom hbot hexec ?_
  exact (recurringFinalityPhaseCarrierFrom_of_regime
    S adm hcom hbot hmajority hdelay hrawPos hexec hpair hrec
      hafterAll hpostAll hchain hpostBoundary hnotLost hcheckpointAll
      hsecondAll).mono
    (Nat.le_add_right _ _)
-/


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
