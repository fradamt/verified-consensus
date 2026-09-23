module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightProgressSeedRegime
public import DecoupledConsensusProofs.Protocol.ChainState.RawHeightCoverage
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RawHeightProgress
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGProposalLifecycle
public import DecoupledConsensusProofs.Protocol.Schedule.FixedHeightRootOpeningNextActive
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryConeConfirmation
public import DecoupledConsensusProofs.Generic.RecoveryConcentration
public import DecoupledConsensusProofs.Protocol.Grades.VoteBelowSource
public import DecoupledConsensusProofs.Protocol.Grades.Grades
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGOpeningFrozenSuffix
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusInternal.Definitions.NamedLifecycle
public import DecoupledConsensusProofs.Protocol.Grades.HeightProgressClosureg0ClearAtAction
public import DecoupledConsensusProofs.Protocol.Grades.RelativeCarrierWindowGateOff
public import DecoupledConsensusProofs.Protocol.Grades.HeightProgressClosureBatchAlignedSite

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Gate-off opening adoption

An aligned honest opening transfers the proposal walk to every honest voter.
The resulting exact vote cone confirms the proposal, covers every action SG
carrier, and forms a common grade at the next read.

The alignment record is directional. Pairwise compatibility of the preceding
action carriers is not sufficient to put them below the new proposal parent.
-/

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

variable {V : Type} [DecidableEq V] [Fintype V]


/-- Named replacement for `GateOffOpeningWindowAt`. The proposal witness is a
record parameter, and its parent height uses the named derivation. -/
structure NamedGateOffOpeningWindowAt
    (S : Setup V) (rho : Run V) (M : Height) (q : Round)
    (P : NamedBlock V) : Prop where
  proposal : proposedBlockAt S rho (S.hc.opening_slot q) = some P
  roundPositive : 0 < q
  postPreviousAction : S.E.t_GST ≤ S.a (q - 1)
  postFrozenSnapshot : S.E.t_GST ≤
    Protocol.proposal_time S.E (S.hc.opening_slot q - 1)
  postOpeningVote : S.E.t_GST ≤
    Protocol.vote_time S.E (S.hc.opening_slot q)
  previousCutoffInHorizon : S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon
  nextActionInHorizon : S.a (q + 1) ≤ rho.horizon
  parentHeight : M - 1 ≤
    (Protocol.derive_named S.E S.cfg P.parent).h
  proposerFrontier :
    (proposerDutyStore S rho (S.hc.opening_slot q)).h_max = M
  proposerGateOff :
    (proposerDutyStore S rho (S.hc.opening_slot q)).h_j + 2 ≤ M
  voteFrontier : ∀ v ∈ rho.honest,
    (Proofs.Optimistic.voteDutyStore S rho v (S.hc.opening_slot q)).h_max = M
  voteGateOff : ∀ v ∈ rho.honest,
    (Proofs.Optimistic.voteDutyStore S rho v (S.hc.opening_slot q)).h_j + 2 ≤ M
  proposalAtVote : ∀ v ∈ rho.honest,
    P.erase ∈ (Proofs.Optimistic.voteDutyStore S rho v (S.hc.opening_slot q)).T
  confirmationFrontier : ∀ v ∈ rho.honest,
    (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q)).h_max = M
  confirmationGateOff : ∀ v ∈ rho.honest,
    (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q)).h_j + 2 ≤ M
  proposalAtConfirmation : ∀ v ∈ rho.honest,
    P.erase ∈ (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q)).T
  nextFrontier : ∀ v ∈ rho.honest,
    (healStoreAt S rho v (q + 1)).h_max = M
  nextGateOff : ∀ v ∈ rho.honest,
    (healStoreAt S rho v (q + 1)).h_j + 2 ≤ M
  proposalAtNext : ∀ v ∈ rho.honest,
    P.erase ∈ (healStoreAt S rho v (q + 1)).T

/-- The complete output of gate-off adoption at one selected opening. -/
structure GateOffOpeningAdoption
    (S : Setup V) (rho : Run V) (q : Round) : Prop where
  proposal : ∃ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot q) = some P
  votes : ∀ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot q) = some P →
    NamedHonestVotesCone S rho (S.hc.opening_slot q)
      (fun X => Block.Preceq P.erase X)
  genuineConfirmation : ∀ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot q) = some P →
    ∀ v ∈ rho.honest,
      GenuineConfirmationWith
        (NamedProfile.gradeContract
          (confirmationInputRead S rho v (S.hc.opening_slot q)).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho v
          (S.hc.opening_slot q)) (S.hc.opening_slot q) P.erase
  actionCover : ∀ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot q) = some P →
    ActionCarriersCover S rho q P.erase
  gradeNext : ∀ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot q) = some P →
    NamedGradeFormsAt S rho (q + 1) P.erase
  lifecycle : ∀ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot q) = some P →
    NamedRawOpeningLifecycleAt S rho q P












/-
/-- A gate-off selected opening with directional anchor alignment is adopted
by every honest voter and yields the next common grade. -/
theorem gateOff_openingLifecycle_of_alignedAnchors
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {M: Height} {q: Round} (hcarrier: ProposerCarrierAt S rho q)
    (hwindow: GateOffOpeningWindowAt S rho M q)
    (haligned: OpeningAnchorsAlignedAt S rho q):
    GateOffOpeningAdoption S rho q:= by
  let s:= S.hc.opening_slot q
  let P:= proposedBlock S rho s
  let H:= proposedParent S rho s
  have hs: 0 < s:= by simpa only [s] using hwindow.openingSlotPositive
  have hprop: S.E.proposer s ∈ rho.honest:= by
    simpa only [s] using hcarrier.1
  have hsb: SlashableBound S rho:=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hmajority: HonestWeightMajority S rho.honest:=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S:= S) hfb
  have hactionHor: S.a q ≤ rho.horizon:= hwindow.actionInHorizon
  have hvoteHor: Protocol.vote_time S.E s ≤ rho.horizon:=
    (Protocol.vote_time_le_confirmation_time S.E s).trans
      (by simpa only [s, Protocol.a_eq_confirmation_time] using hactionHor)
  have hconfHor: Protocol.confirmation_time S.E s ≤ rho.horizon:= by
    simpa only [s, Protocol.a_eq_confirmation_time] using hactionHor
  have hproposalHor: Protocol.proposal_time S.E s ≤ rho.horizon:=
    (Protocol.proposal_time_le_confirmation_time S.E s).trans hconfHor
  have hrun: RunBlock S rho P:=
    Protocol.proposedBlock_runBlock S adm hs hprop hproposalHor
  have htransferred: HonestProposalWalksTransferred S rho s:= by
    simpa only [s] using
      gateOffOpening_transferred S adm hfb hcarrier hwindow haligned
  have hstores: VoteStoresExtend S rho s P:= by
    simpa only [P] using
      Protocol.voteStoresExtend_of_transferred S adm htransferred
  have hnames: HonestVotesName S rho s P:= by
    simpa only [P] using
      Protocol.honestVotesName_of_voteStoresExtend
        S adm hs hvoteHor hstores
  have hvotes: HonestVotesCone S rho s (fun X => Block.Preceq P X):=
    Proofs.Optimistic.honestVotesCone_preceq S rho s hrun hnames
  have hPheight: M - 1 ≤ (derived_state S.E S.cfg P).h:= by
    simpa only [P, s] using hwindow.proposalHeight
  have hPconf: ∀ v ∈ rho.honest,
      P ∈ confTree (Proofs.Optimistic.confStore S rho v s):= by
    intro v hv
    have hfiltered:= frontierBlock_filtered_of_gateOff
      S adm hsb hv hconfHor
      (by simpa only [P, s, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore]
        using hwindow.proposalAtConfirmation v hv)
      hrun hPheight hwindow.frontierPositive
      (by simpa only [s, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore]
        using hwindow.confirmationFrontier v hv)
      (by simpa only [s, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore]
        using hwindow.confirmationGateOff v hv)
    simpa only [confTree, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using hfiltered
  have hread: ∀ v ∈ rho.honest,
      RecoveryProposalConfirmationRead S rho s v P:= by
    intro v hv
    have hcandidate:= hPconf v hv
    exact
      { root:= Proofs.Records.preceq_get_fg_root_of_mem_filtered hcandidate
        anchor:= by
          simpa only [P, s] using haligned.confirmationBelowProposal v hv
        candidate:= hcandidate }
  have hlive: ∀ v ∈ rho.honest,
      (actionStoreAt S rho v q).live_confirmed = P:= by
    simpa only [s, P] using
      openingProposal_liveConfirmed_actionStore_after_gst_of_localReads
        S adm hcom hwindow.roundPositive hwindow.postOpeningVote
          hactionHor hprop hstores hread
  have hgenuine: ∀ v ∈ rho.honest,
      GenuineConfirmation (contract:= Protocol.GradeContract.current) S.E S.hc
        (Proofs.Optimistic.confStore S rho v s) s P:= by
    have hall:= genuineConfirmationAndPreceq_of_postHealingCone_all_honest
      S adm hcom hs hwindow.postOpeningVote hconfHor hvotes
        (fun v hv => ⟨(hread v hv).root, (hread v hv).anchor,
          (hread v hv).candidate⟩)
    intro v hv
    have hselected:
        (Protocol.update_confirmation S.E S.hc
          (Proofs.Optimistic.confStore S rho v s) s).live_confirmed = P:= by
      have h:= hlive v hv
      rw [actionStoreAt_eq_update_confirmation_openingConfStore] at h
      simpa only [s] using h
    simpa only [hselected] using (hall v hv).1
  have hHP: Block.Preceq H P:= by
    simpa only [H, P] using Protocol.preceq_of_parent?
      (Protocol.proposedBlock_parent S rho s)
  have hupper: ∀ v ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho v (q - 1)) P:= by
    intro v hv
    exact Block.preceq_trans
      (by simpa only [H, s] using
        haligned.previousCarriersBelowParent v hv) hHP
  have hq: 1 ≤ q:= Nat.succ_le_iff.mpr hwindow.roundPositive
  have hbatchAligned: ∀ v ∈ rho.honest,
      BatchAligned (actionStoreAt S rho v q).toHealing.gradeView
        rho.honest q P:= by
    have hcut: S.hc.Γ_neg1 S.E.Δ (q - 1 + 1) ≤ rho.horizon:= by
      simpa only [Nat.sub_add_cancel hq] using
        hwindow.previousCutoffInHorizon
    have h:= nextActionBatchAligned_of_carriersPreceq
      S adm hwindow.postPreviousAction hcut hupper
    simpa only [Nat.sub_add_cancel hq] using h
  have hroot: ∀ v ∈ rho.honest,
      Block.Preceq
        (Protocol.get_sg_root S.E S.hc
          (actionStoreAt S rho v q).toHealing q) P:= by
    intro v hv
    have hconfRound: S.hc.round_of
        (Proofs.Optimistic.confStore S rho v s).s = q:= by
      simp only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore, s,
        opening_confirmation_time_eq_action]
      exact Proofs.HealingLemmas.round_of_slotOf_a S q
    rw [actionStoreAt_eq_update_confirmation_openingConfStore]
    change Block.Preceq
      (Protocol.get_sg_root S.E S.hc
        (Protocol.update_confirmation S.E S.hc
          (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q))
          (S.hc.opening_slot q)).toHealing q) P
    simpa only [Protocol.update_confirmation, Protocol.Store.toHealing,
      confAnchor, hconfRound, s, P] using
        haligned.confirmationBelowProposal v hv
  have hcover: ActionCarriersCover S rho q P:=
    actionCarriersCover_of_liveFloor_batchCompatible_sgRootFloor
      S rho
      (fun v hv => by
        simpa only [hlive v hv] using Block.preceq_self P)
      hroot
      (fun v hv => BatchCompatible.of_batchAligned (hbatchAligned v hv))
      hfb
  have hnextActive: ∀ v ∈ rho.honest,
      P ∈ Protocol.get_filtered_block_tree
        (healStoreAt S rho v (q + 1)).toFG:= by
    intro v hv
    exact frontierBlock_filtered_at_healStoreAt_of_gateOff
      S adm hsb hv hwindow.nextActionInHorizon
        (by simpa only [P, s] using hwindow.proposalAtNext v hv)
        hrun hPheight hwindow.frontierPositive
        (by simpa only [P, s] using hwindow.nextFrontier v hv)
        (by simpa only [P, s] using hwindow.nextGateOff v hv)
  have hpostAction: S.E.t_GST ≤ S.a q:= by
    exact hwindow.postOpeningVote.trans
      (by simpa only [s] using
        Protocol.vote_time_le_confirmation_time S.E s)
  have hgrade: GradeFormsAt S rho (q + 1) P:=
    gradeFormsAt_succ_of_actionCarriersCover_and_next_active
      S adm hmajority hcover hpostAction
        hwindow.nextCutoffInHorizon hnextActive
  have hlifecycle: RawOpeningLifecycleAt S rho q P:=
    { roundPositive:= hwindow.roundPositive
      proposed:= by rfl
      proposerHonest:= by simpa only [s] using hprop
      proposalInHorizon:= by simpa only [s] using hproposalHor
      runBlock:= hrun
      liveConfirmed:= by simpa only [P, s] using hlive
      actionCover:= hcover
      gradeNext:= hgrade }
  exact
    { votes:= by simpa only [s, P] using hvotes
      genuineConfirmation:= by simpa only [s, P] using hgenuine
      actionCover:= by simpa only [P, s] using hcover
      gradeNext:= by simpa only [P, s] using hgrade
      lifecycle:= by simpa only [P, s] using hlifecycle }
-/

/-! ## The gate-off opening lifecycle at a common ceiling -/

omit [Fintype V] in
/-- A named block is above its own named parent. -/
private theorem seedAdoption_namedParent_preceq (P : NamedBlock V) :
    NamedBlock.Preceq P.parent P := by
  cases P with
  | genesis => exact Proofs.NamedAncestry.named_self _
  | node parent slot root votes support rows proposer =>
      exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
        (Proofs.NamedAncestry.named_self parent)

/-- Every phase domain of round `q` is at or before the round's action. -/
private theorem seedAdoption_domain_le_action
    (S : Setup V) (q : Round) (p : DecoupledConsensusModel.Protocol.Phase) :
    DecoupledConsensusModel.Protocol.domain S.E S.hc q p ≤ S.a q := by
  have hvote : DecoupledConsensusModel.Protocol.domain S.E S.hc q p ≤
      Protocol.vote_time S.E (S.hc.opening_slot q) := by
    have hpos := S.E.Δ_pos
    cases p <;>
      · simp only [DecoupledConsensusModel.Protocol.domain, DecoupledConsensusModel.Protocol.opening,
          DecoupledConsensusModel.Protocol.Phase.domainOffset, Protocol.vote_time,
          Protocol.proposal_time]
        linarith
  exact hvote.trans
    (Protocol.vote_time_le_confirmation_time S.E (S.hc.opening_slot q))

/-- The shared proposal parent is below the named proposal. -/
private theorem seedAdoption_proposedParent_preceq
    (S : Setup V) (rho : Run V) (s : Slot) {P : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P) :
    Block.Preceq (proposedParent S rho s) P.erase := by
  obtain ⟨p, hp, hparent⟩ := proposedBlockAt_parent S rho s hP
  rw [← hparent]
  cases P with
  | genesis => simp only [NamedBlock.parent?, reduceCtorEq] at hp
  | node parent slot root votes support rows proposer =>
      simp only [NamedBlock.parent?, Option.some.injEq] at hp
      subst hp
      apply Protocol.preceq_of_parent?
      rfl


/-- **Gate-off opening adoption at a common round ceiling.**

The ceiling is the frozen proposal-transfer pivot, so no directional relation
between the proposal and vote anchors is needed. The route is the one the
earlier proof used, with the named replacements: the ceiling transfer gives
`VoteStoresExtend`, that gives the exact honest vote name and therefore the
opening cone, the cone and the local confirmation reads give the genuine
confirmations and the exact live confirmation, and the frozen action read
turns that into the carrier cover and the successor grade.

Nothing is pinned. The two extra inputs are ordinary premises. `hprevFrontier`
is the gate-off frontier at the preceding action read; the window record does
not carry it, and the three gate-off producers this proof calls all need it
(`relativeCarrierWindowAt_of_gateOff` for the G0 clearance through
`g0ClearAtAction_of_relativeCarrierWindow`, and `actionBatchAlignedAt_of_gateOff`
for the action batch alignment). `hnextActiveDomain` is the next round's
G2-domain activity: `NamedGradeFormsAt` reads one phase before the action, and
it is the same input the frozen `NamedSGProposalLifecycleInputs` carries as
`nextActive`. -/
theorem gateOff_openingLifecycle_of_roundCeiling
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {q : Round} {C P : NamedBlock V}
    (hcarrier : ProposerCarrierAt S rho q)
    (h : RoundCeilingAt S rho M q C)
    (hwindow : NamedGateOffOpeningWindowAt S rho M q P)
    (hprevFrontier : ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (q - 1))).h_max = M)
    (hnextActiveDomain : ∀ w ∈ rho.honest,
      P.erase ∈ Internal.PhaseGrades.filteredTree
        (relativeG2Read S rho (q + 1) w)) :
    GateOffOpeningAdoption S rho q := by
  have hs : 0 < S.hc.opening_slot q := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos hwindow.roundPositive
      (lt_of_lt_of_le (by decide) S.hc.R_ge_two)
  have hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest := hcarrier.1
  have hactionHor : S.a q ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_succ q)).trans hwindow.nextActionInHorizon
  have hconfHor :
      Protocol.confirmation_time S.E (S.hc.opening_slot q) ≤ rho.horizon :=
    hactionHor
  have hvoteHor :
      Protocol.vote_time S.E (S.hc.opening_slot q) ≤ rho.horizon :=
    (Protocol.vote_time_le_confirmation_time S.E _).trans hconfHor
  have hproposalHor :
      Protocol.proposal_time S.E (S.hc.opening_slot q) ≤ rho.horizon :=
    (Protocol.proposal_time_le_confirmation_time S.E _).trans hconfHor
  have hM : 1 ≤ M := by
    have htwo : 2 ≤ M :=
      (Nat.le_add_left 2
        (proposerDutyStore S rho (S.hc.opening_slot q)).h_j).trans
          hwindow.proposerGateOff
    exact (by decide : 1 ≤ 2).trans htwo
  have hheight : M - 1 ≤ (Protocol.derive_named S.E S.cfg P).h :=
    hwindow.parentHeight.trans
      (Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg
        (seedAdoption_namedParent_preceq P))
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hmajority : HonestWeightMajority S rho.honest :=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S := S) hfb
  have hrun : RunBlock S rho P :=
    proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
      (S.hc.opening_slot q) hs hprop hproposalHor hwindow.proposal
  have hHP : Block.Preceq (proposedParent S rho (S.hc.opening_slot q))
      P.erase :=
    seedAdoption_proposedParent_preceq S rho (S.hc.opening_slot q)
      hwindow.proposal
  have haligned : OpeningCeilingAlignedAt S rho q C.erase :=
    openingAnchorsAligned_of_roundCeiling S adm hcom hcarrier h
  have hstores : Protocol.VoteStoresExtend S rho
      (S.hc.opening_slot q) P :=
    proposalWalkTransferred_of_roundCeiling S adm hcom hfb hcarrier
      hwindow.proposal h haligned hwindow.nextActionInHorizon hheight hM
      hwindow.proposalAtVote hwindow.voteFrontier hwindow.voteGateOff
      hwindow.postFrozenSnapshot hwindow.proposerFrontier
  have hnames : NamedHonestVotesName S rho (S.hc.opening_slot q) P.erase :=
    Protocol.honestVotesName_of_voteStoresExtend S adm hs hvoteHor hstores
  have hvotes : NamedHonestVotesCone S rho (S.hc.opening_slot q)
      (fun X => Block.Preceq P.erase X) :=
    Proofs.Optimistic.honestVotesCone_preceq S rho (S.hc.opening_slot q) hrun hnames
  have hPconf : ∀ v ∈ rho.honest,
      P.erase ∈ confTree (Proofs.Optimistic.confStore S rho v
        (S.hc.opening_slot q)) := by
    intro v hv
    have hfiltered := frontierBlock_filtered_of_gateOff S adm hsb hv hconfHor
      (by simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using
        hwindow.proposalAtConfirmation v hv)
      rfl hrun hheight hM
      (by simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using
        hwindow.confirmationFrontier v hv)
      (by simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using
        hwindow.confirmationGateOff v hv)
    simpa only [confTree, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using
      hfiltered
  have hread : ∀ v ∈ rho.honest,
      RecoveryProposalConfirmationRead S rho (S.hc.opening_slot q) v P := by
    intro v hv
    have hcandidate := hPconf v hv
    exact
      { root := Proofs.Records.preceq_get_fg_root_of_mem_filtered hcandidate
        anchor := haligned.confirmationBelowProposal v hv P hwindow.proposal
        candidate := hcandidate }
  have hlive : ∀ v ∈ rho.honest,
      (actionStoreAt S rho v q).live_confirmed = P.erase :=
    openingProposal_liveConfirmed_actionStore_after_gst_of_localReads
      S adm hcom hwindow.roundPositive hwindow.postOpeningVote hactionHor
      hprop hwindow.proposal hstores hread
  have hgenuine : ∀ v ∈ rho.honest,
      GenuineConfirmationWith
        (NamedProfile.gradeContract
          (confirmationInputRead S rho v (S.hc.opening_slot q)).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q))
          (S.hc.opening_slot q) P.erase := by
    intro v hv
    have hall := genuineConfirmationAndPreceq_of_postHealingCone_all_honest
      S adm hcom hs hwindow.postOpeningVote hconfHor hvotes
      (fun w hw => ⟨(hread w hw).root, (hread w hw).anchor,
        (hread w hw).candidate⟩) v hv
    have hselected :
        (Protocol.update_confirmation_with
          (NamedProfile.gradeContract
            (confirmationInputRead S rho v (S.hc.opening_slot q)).cache)
          S.E S.hc (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q))
          (S.hc.opening_slot q)).live_confirmed = P.erase := by
      have hlocal := hlive v hv
      rw [show (actionStoreAt S rho v q).live_confirmed =
          (actionStoreAt S rho v q).st.core.live_confirmed from rfl,
        actionStoreAt_eq_update_confirmation_openingConfStore] at hlocal
      exact hlocal
    simpa only [hselected] using hall.1
  have hrelWindow : RelativeCarrierWindowAt S rho (q - 1) .g0 :=
    relativeCarrierWindowAt_of_gateOff S adm hfb hwindow.roundPositive
      hwindow.postPreviousAction hprevFrontier
      (fun w hw => by
        simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using
          hwindow.confirmationFrontier w hw)
      (fun w hw => by
        simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using
          hwindow.confirmationGateOff w hw)
      ((seedAdoption_domain_le_action S q .g0).trans hactionHor)
  have hbatch : ∀ v ∈ rho.honest,
      let n := actionReadAt S rho v q
      Internal.PhaseGrades.BatchAlignedAt S.hc n.st.core.toHealing.gradeView
        n.st.core.F rho.honest q
        (Internal.PhaseGrades.allPhasesCutoff S.E S.hc q) P.erase :=
    actionBatchAlignedAt_of_gateOff S adm hfb hwindow.roundPositive
      hwindow.postPreviousAction hactionHor hprevFrontier
      (fun x hx => by
        simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using
          hwindow.confirmationFrontier x hx)
      (fun x hx => by
        simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using
          hwindow.confirmationGateOff x hx)
      (fun u hu => Block.preceq_trans
        (haligned.previousCarriersBelowParent u hu) hHP)
  have hclear : ∀ v ∈ rho.honest,
      Internal.PhaseGrades.nodeClear S (actionReadAt S rho v q) q
        P.erase = true :=
    g0ClearAtAction_of_relativeCarrierWindow S adm hfb hwindow.roundPositive
      hactionHor ((seedAdoption_domain_le_action S q .g2).trans hactionHor)
      hrelWindow hwindow.proposal haligned.previousCarriersBelowParent
  have hcover : ActionCarriersCover S rho q P.erase := by
    intro v hv
    have heq : actionSGBlockAt S rho v q = P.erase := by
      apply actionSGBlockAt_eq_liveConfirmed_of_batchAligned S
        (Can := P.erase) (D := P.erase)
        (A := Internal.PhaseGrades.nodeAnchor S (actionReadAt S rho v q) q)
      · exact hlive v hv
      · exact hbatch v hv
      · exact Block.preceq_self _
      · rfl
      · exact Block.preceq_trans (h.actionAnchor v hv)
          (Block.preceq_trans haligned.ceilingBelowParent hHP)
      · exact hclear v hv
    rw [heq]
    exact Block.preceq_self _
  have hnextActive : ∀ v ∈ rho.honest,
      P.erase ∈ Protocol.get_filtered_block_tree
        (healStoreAt S rho v (q + 1)).toFG := by
    intro v hv
    exact frontierBlock_filtered_at_healStoreAt_of_gateOff S adm hsb hv
      hwindow.nextActionInHorizon (hwindow.proposalAtNext v hv) rfl hrun
      hheight hM (hwindow.nextFrontier v hv) (hwindow.nextGateOff v hv)
  have hpostAction : S.E.t_GST ≤ S.a q :=
    hwindow.postOpeningVote.trans
      (Protocol.vote_time_le_confirmation_time S.E _)
  have hnextCut : S.hc.Γ_neg1 S.E.Δ (q + 1) ≤ rho.horizon :=
    (le_of_lt (next_Γ_neg1_lt_action S q)).trans hwindow.nextActionInHorizon
  have hgrade : NamedGradeFormsAt S rho (q + 1) P.erase :=
    namedGradeFormsAt_succ_of_actionCarriersCover_and_next_active
      S adm hmajority hcover hpostAction hnextCut hnextActive hnextActiveDomain
  have hlifecycle : NamedRawOpeningLifecycleAt S rho q P :=
    { roundPositive := hwindow.roundPositive
      proposal := hwindow.proposal
      proposerHonest := hprop
      proposalInHorizon := hproposalHor
      runBlock := hrun
      liveConfirmed := hlive
      actionCover := hcover
      gradeNext := hgrade }
  have hunique : ∀ P' : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot q) = some P' → P' = P := by
    intro P' hP'
    have := hP'.symm.trans hwindow.proposal
    exact Option.some.inj this
  exact
    { proposal := ⟨P, hwindow.proposal⟩
      votes := by
        intro P' hP'
        rw [hunique P' hP']
        exact hvotes
      genuineConfirmation := by
        intro P' hP'
        rw [hunique P' hP']
        exact hgenuine
      actionCover := by
        intro P' hP'
        rw [hunique P' hP']
        exact hcover
      gradeNext := by
        intro P' hP'
        rw [hunique P' hP']
        exact hgrade
      lifecycle := by
        intro P' hP'
        rw [hunique P' hP']
        exact hlifecycle }

#print axioms gateOff_openingLifecycle_of_roundCeiling


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
