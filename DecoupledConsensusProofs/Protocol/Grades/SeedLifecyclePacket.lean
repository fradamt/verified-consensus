module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedAdoption

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Named lifecycle records for seed promotion

The gate-off adoption proof already supplies the opening's actual votes,
confirmation, carriers, and next grade. This module packages those facts for
the promotion proof, with the preceding frontier and next-domain activity
kept at their local reads.
-/



namespace DecoupledConsensusModel.Proofs.HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Internal.NamedRecoveryRead
open Protocol Proofs.HealingLemmas Proofs.Optimistic DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A prepared genuine confirmation records its named walk at the actual
confirmation event. -/
private theorem genuineConfirmationAt_of_with
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {s : Slot}
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {P : Block V}
    (h : GenuineConfirmationWith
      (NamedProfile.gradeContract (confirmationInputRead S rho v s).cache)
      S.E S.hc (Proofs.Optimistic.confStore S rho v s) s P) :
    GenuineConfirmationAt S rho v s ∧
      (rho.storeAt S v (Protocol.confirmation_time S.E s)).live_confirmed = P := by
  let n := confirmationInputRead S rho v s
  let contract := NamedProfile.gradeContract n.cache
  have hrecord := Proofs.Optimistic.live_confirmed_eq_update S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv s hhor
  have hrecordP :
      (rho.storeAt S v (Protocol.confirmation_time S.E s)).live_confirmed = P := by
    rw [hrecord]
    exact h.selected
  have hwalk : confWalkWith contract S.E S.hc
      (Proofs.Optimistic.confStore S rho v s) s = P := by
    have hselected := h.selected
    rw [update_confirmation_with_live_confirmed, if_pos h.genuine] at hselected
    exact hselected
  refine ⟨?_, hrecordP⟩
  unfold GenuineConfirmationAt
  constructor
  · rw [hrecordP]
    simpa only [namedConfirmationWalk, n, contract,
      Proofs.Optimistic.confStore_eq_confirmationInputRead] using hwalk.symm
  · exact h.genuine


/-- The named records follows from a round ceiling and the local adoption
window. No absolute-grade or erased-height agreement is used. -/
theorem seedLifecyclePacket_of_roundCeiling
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {q : Round} {C P : NamedBlock V}
    (hcarrier : ProposerCarrierAt S rho q)
    (hceiling : RoundCeilingAt S rho M q C)
    (hwindow : NamedGateOffOpeningWindowAt S rho M q P)
    (hprev : ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (q - 1))).h_max = M)
    (hnext : ∀ w ∈ rho.honest,
      P.erase ∈ filteredTree (relativeG2Read S rho (q + 1) w)) :
    NamedSGProposalLifecyclePacket S rho (q - 1)
      (S.hc.opening_slot q - 1) P := by
  have hq : 0 < q := hwindow.roundPositive
  have hqPred : q - 1 + 1 = q := Nat.sub_add_cancel hq
  have hs : 0 < S.hc.opening_slot q := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos hq (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hsPred : S.hc.opening_slot q - 1 + 1 = S.hc.opening_slot q :=
    Nat.sub_add_cancel hs
  have hactionHor : S.a q ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_succ q)).trans hwindow.nextActionInHorizon
  have hfrontier : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a q)).h_max = M := by
    intro w hw
    simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using
      hwindow.confirmationFrontier w hw
  have hgate : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a q)).h_j + 2 ≤ M := by
    intro w hw
    simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using
      hwindow.confirmationGateOff w hw
  have hrelG1 : RelativeCarrierWindowAt S rho (q - 1) .g1 :=
    relativeCarrierWindowAt_of_gateOff S adm hfb hq hwindow.postPreviousAction
      hprev hfrontier hgate ((FrameForward.domain_le_a S q .g1).trans hactionHor)
  have hrelG0 : RelativeCarrierWindowAt S rho (q - 1) .g0 :=
    relativeCarrierWindowAt_of_gateOff S adm hfb hq hwindow.postPreviousAction
      hprev hfrontier hgate ((FrameForward.domain_le_a S q .g0).trans hactionHor)
  have hmajority := gradeFormingMajority_of_admissible_belowOneThird S adm hfb hq
    ((FrameForward.domain_le_a S q .g2).trans hactionHor)
    hwindow.postPreviousAction
  have haligned := openingAnchorsAligned_of_roundCeiling S adm hcom hcarrier hceiling
  have hadopt := gateOff_openingLifecycle_of_roundCeiling
    S adm hcom hfb hcarrier hceiling hwindow hprev hnext
  have hlifecycle := hadopt.lifecycle P hwindow.proposal
  have hclear := g0ClearAtAction_of_relativeCarrierWindow S adm hfb hq hactionHor
    ((FrameForward.domain_le_a S q .g2).trans hactionHor)
    hwindow.postPreviousAction hrelG0
    hwindow.proposal haligned.previousCarriersBelowParent
  have hheight : M - 1 ≤ (Protocol.derive_named S.E S.cfg P).h := by
    have hp : NamedBlock.Preceq P.parent P := by
      cases P with
      | genesis => exact Proofs.NamedAncestry.named_self _
      | node parent slot root votes support rows proposer =>
          exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
            (Proofs.NamedAncestry.named_self parent)
    exact hwindow.parentHeight.trans (Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hp)
  have hM : 1 ≤ M := by
    have htwo : 2 ≤ M :=
      (Nat.le_add_left 2 (proposerDutyStore S rho (S.hc.opening_slot q)).h_j).trans
        hwindow.proposerGateOff
    exact (by decide : 1 ≤ 2).trans htwo
  have hstores := proposalWalkTransferred_of_roundCeiling S adm hcom hfb hcarrier
    hwindow.proposal hceiling haligned hwindow.nextActionInHorizon hheight hM
    hwindow.proposalAtVote hwindow.voteFrontier hwindow.voteGateOff
    hwindow.postFrozenSnapshot hwindow.proposerFrontier
  have hnames := Protocol.honestVotesName_of_voteStoresExtend S adm hs
    ((Protocol.vote_time_le_confirmation_time S.E _).trans hactionHor) hstores
  refine
    { openingSlot := by simpa only [hqPred] using hsPred
      proposal := by simpa only [hqPred] using hwindow.proposal
      actionTargetParent := by
        simpa only [hqPred] using haligned.previousCarriersBelowParent
      liveG1Parent := ?_
      honestVotes := by simpa only [hqPred] using hnames
      genuineConfirmation := ?_
      g0ClearAtAction := by simpa only [hqPred] using hclear
      lifecycle := by simpa only [hqPred] using hlifecycle }
  · intro w hw B hG1
    have hG1q : namedG1At S rho w q B := by simpa only [hqPred] using hG1
    obtain ⟨u, hu, hBu⟩ := relativeGrade_has_roundCarrier
      S adm.toNamedAdmissibleCore hrelG1
        (by simpa only [hqPred] using hmajority) hw
        (by simpa only [namedG1At, PhaseGrades.readAt, hqPred] using hG1q)
    have huHon : u ∈ rho.honest :=
      ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u (q - 1)).mp hu).1
    simpa only [hqPred] using
      Block.preceq_trans hBu (haligned.previousCarriersBelowParent u huHon)
  · intro v hv
    simpa only [hqPred] using genuineConfirmationAt_of_with S adm hv
      hactionHor (hadopt.genuineConfirmation P hwindow.proposal v hv)

end DecoupledConsensusModel.Proofs.HealingSurface

end
