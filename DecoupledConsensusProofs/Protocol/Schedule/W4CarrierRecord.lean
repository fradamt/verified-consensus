module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.CanonicalRegimeFromChain
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalAdoptionNamedClosed
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.SGLifetimeNamed
public import DecoupledConsensusProofs.Objects.FGSafetyRootNamed
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainBatch
public import DecoupledConsensusProofs.Protocol.Grades.MovingChainDispatch
public import DecoupledConsensusProofs.Execution.MovingChainBandCover
public import DecoupledConsensusProofs.Execution.MovingChainRoundFloorFields
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ReaderLocalCone
public import DecoupledConsensusProofs.Protocol.Grades.MovingChainFloorBridge
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainSupporter
public import DecoupledConsensusProofs.Protocol.Grades.HonestProposalRawLifecycleNamed
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.W4HeightSourceHistory
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainHandoffExports
public import DecoupledConsensusProofs.Protocol.Grades.W4FKGrade
public import DecoupledConsensusProofs.Protocol.Grades.W4CarrierGrade
public import DecoupledConsensusProofs.Protocol.Grades.W4CarrierWindowPin

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

/-! ## 0. Schedule helpers

Copies of the private normalisation lemmas of `MovingChainRoundReadRun`
(private there, needed here at the round's own read). -/

private theorem w4cr_action_normal (S : Setup V) (q : Round) :
    S.a q = (4 * ((S.hc.opening_slot q : Slot) : Time) + 6) * S.E.Δ := by
  unfold Setup.a Protocol.HealConfig.a slotStart
  ring

private theorem w4cr_proposal_normal (E : Env V) (s : Slot) :
    Protocol.proposal_time E s = (4 * (s : Time) + 0) * E.Δ := by
  unfold Protocol.proposal_time Env.t slotStart
  ring

private theorem w4cr_confirmation_normal (E : Env V) (s : Slot) :
    Protocol.confirmation_time E s = (4 * (s : Time) + 6) * E.Δ := by
  unfold Protocol.confirmation_time Env.t slotStart
  ring

private theorem w4cr_openingSlot_eq_mul (S : Setup V) (q : Round) :
    S.hc.opening_slot q = q * S.hc.R := rfl

/-- The round action is its opening slot's confirmation instant. -/
private theorem w4cr_action_eq_confirmation (S : Setup V) (r : Round) :
    S.a r = Protocol.confirmation_time S.E (S.hc.opening_slot r) := by
  rw [w4cr_action_normal S r, w4cr_confirmation_normal S.E _]

/-- Confirmation instants are monotone in the slot. -/
private theorem w4cr_confirmation_mono (E : Env V) {s t : Slot} (h : s ≤ t) :
    Protocol.confirmation_time E s ≤ Protocol.confirmation_time E t := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ,
    Protocol.confirmation_time_eq_support_cutoff_succ]
  exact Proofs.Optimistic.support_cutoff_mono E (Nat.add_le_add_right h 1)

/-- The opening proposal instant precedes the round action. -/
private theorem w4cr_openingProposal_le_action (S : Setup V) (r : Round) :
    Protocol.proposal_time S.E (S.hc.opening_slot r) ≤ S.a r := by
  rw [w4cr_action_normal S r, w4cr_proposal_normal S.E _]
  exact Int.mul_le_mul_of_nonneg_right (by omega) (le_of_lt S.E.Δ_pos)

/-- Rounds are at least two slots apart. -/
private theorem w4cr_openingSlot_two_le (S : Setup V) {q r : Round} (hqr : q < r) :
    S.hc.opening_slot q + 2 ≤ S.hc.opening_slot r := by
  have hstep : S.hc.opening_slot q + S.hc.R ≤ S.hc.opening_slot r := by
    rw [w4cr_openingSlot_eq_mul, w4cr_openingSlot_eq_mul]
    calc
      q * S.hc.R + S.hc.R = (q + 1) * S.hc.R := by
        rw [Nat.add_mul, Nat.one_mul]
      _ ≤ r * S.hc.R := Nat.mul_le_mul_right _ hqr
  exact le_trans (Nat.add_le_add_left S.hc.R_ge_two _) hstep

/-- An earlier round's action instant is before this round's opening proposal. -/
private theorem w4cr_action_lt_openingProposal
    (S : Setup V) {q r : Round} (hqr : q < r) :
    S.a q < Protocol.proposal_time S.E (S.hc.opening_slot r) := by
  have hos := w4cr_openingSlot_two_le S hqr
  rw [w4cr_action_normal S q, w4cr_proposal_normal S.E _]
  refine Int.mul_lt_mul_of_pos_right ?_ S.E.Δ_pos
  have hcast : ((S.hc.opening_slot q : Slot) : Int) + 2 ≤
      ((S.hc.opening_slot r : Slot) : Int) := by exact_mod_cast hos
  push_cast at hcast ⊢
  omega

/-- The previous round's opening slot is at least one slot below this one. -/
private theorem w4cr_prevOpening_succ_le (S : Setup V) {r : Round} (hr : 0 < r) :
    S.hc.opening_slot (r - 1) + 1 ≤ S.hc.opening_slot r := by
  exact Nat.le_of_succ_le
    (w4cr_openingSlot_two_le S (Nat.sub_lt hr Nat.one_pos))

/-- `rGST` never exceeds the FG-safety progress deadline. -/
private theorem w4cr_gst_le_deadline (S : Setup V) (rho : Run V)
    (rGST gap : Round) (dx : Nat) :
    rGST ≤ fgSafetyProgressDeadline S rho rGST gap dx := by
  unfold fgSafetyProgressDeadline
  exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)

/-- Isolated `Nat` steps (the FG-safety deadline is opaque to `omega`). -/
private theorem w4cr_three_le {d r : Nat} (h : d + 3 ≤ r) : 3 ≤ r :=
  (Nat.le_add_left 3 d).trans h

private theorem w4cr_sub_two_succ {r : Nat} (h : 3 ≤ r) : r - 2 + 1 = r - 1 := by
  omega

private theorem w4cr_deadline_le_sub_two {d r : Nat} (h : d + 3 ≤ r) :
    d ≤ r - 2 := by
  omega

private theorem w4cr_le_pred {A B : Nat} (h : A + 2 ≤ B) : A + 1 ≤ B - 1 := by
  omega

private theorem w4cr_pos_pred {A B : Nat} (h : A + 2 ≤ B) : 0 < B - 1 := by
  omega

private theorem w4cr_deadline_le_sub_one {d r : Nat} (h : d + 3 ≤ r) :
    d + 2 ≤ r - 1 := by
  omega

private theorem w4cr_sub_two_lt_sub_one {r : Nat} (h : 3 ≤ r) :
    r - 2 < r - 1 := by
  omega

private theorem w4cr_two_le {d m : Nat} (h : d + 2 ≤ m) : 2 ≤ m :=
  (Nat.le_add_left 2 d).trans h

private theorem w4cr_deadline_le_pred {d m : Nat} (h : d + 2 ≤ m) :
    d ≤ m - 1 := by
  omega

/-! ## 1. The standing facts of route D at a carrier round

Everything below is stated over one carrier round `r` and its own honest
opening proposal `P`. The horizon premise is the record's own
(`Protocol.confirmation_time S.E (S.hc.opening_slot r + 2) ≤ rho.horizon`). -/

/-- The carrier round's action instant is inside the horizon. -/
theorem w4cr_actionHorizon (S : Setup V) {rho : Run V} {r : Round}
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon) :
    S.a r ≤ rho.horizon := by
  rw [w4cr_action_eq_confirmation S r]
  exact (w4cr_confirmation_mono S.E (Nat.le_add_right _ 2)).trans hhor

/-- The opening slot's support cutoff is inside the horizon. -/
theorem w4cr_openingCutoffHorizon (S : Setup V) {rho : Run V} {r : Round}
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon) :
    Protocol.vote_time S.E (S.hc.opening_slot r) + S.E.Δ ≤ rho.horizon := by
  rw [Proofs.Optimistic.vote_time_add_delta]
  refine (support_cutoff_le_confirmation_time S.E
    (S.hc.opening_slot r)).trans ?_
  rw [← w4cr_action_eq_confirmation S r]
  exact w4cr_actionHorizon S hhor

/-- **Every honest head at the carrier's opening slot IS the opening
proposal.** `honestProposal_voterHeadAt_eq_after_SG_healing_named`, read at
this round. -/
theorem w4cr_openingHeads
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r : Round}
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ r)
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot r) = some P) :
    ∀ v ∈ rho.honest,
      voterHeadAt S rho v (S.hc.opening_slot r) = P.erase :=
  honestProposal_voterHeadAt_eq_after_SG_healing_named
    (delayExtra := delayExtra) S adm hcom hbelow hrec hdelay hpost hr
    (le_trans (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos))
      (w4cr_openingCutoffHorizon S hhor)) hcarrier hP

/-- The opening slot's honest vote cone sits above the opening proposal. -/
theorem w4cr_openingCone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r : Round}
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ r)
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot r) = some P) :
    NamedHonestVotesCone S rho (S.hc.opening_slot r)
      (fun X => Block.Preceq P.erase X) :=
  honestProposal_openingVoteCone_after_SG_healing_named
    (delayExtra := delayExtra) (rGST := rGST) (gap := gap) S adm hcom hr hcarrier
    (le_trans (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos))
      (w4cr_openingCutoffHorizon S hhor)) hP
    (w4cr_openingHeads S adm hcom hbelow hrec hdelay hpost hr hcarrier hhor hP)

/-- **Every honest FG root at the carrier's own action read is below the
opening proposal.** `fgRoot_preceq_previousHead_through_confirmation_after_GST`
at `read = S.a r`, `s = S.hc.opening_slot r`, closed by the head equality. -/
theorem w4cr_fgRoot_preceq_openingProposal
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r : Round}
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ r)
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot r) = some P) :
    ∀ u ∈ rho.honest,
      Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S u (S.a r)).toHealing.toFG) P.erase := by
  intro u hu
  obtain ⟨w, hw⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
  have hdeadlineLt : fgSafetyProgressDeadline S rho rGST gap delayExtra < r :=
    lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 2)) hr
  have hheads := w4cr_openingHeads S adm hcom hbelow hrec hdelay hpost hr
    hcarrier hhor hP
  have hres := fgRoot_preceq_previousHead_through_confirmation_after_GST
    (delayExtra := delayExtra) S adm hcom hbelow hrec hdelay hpost
    (read := S.a r) ((action_strictMono S).monotone hdeadlineLt.le)
    (w4cr_actionHorizon S hhor)
    (s := S.hc.opening_slot r)
    (Nat.le_of_succ_le (w4cr_openingSlot_two_le S hdeadlineLt))
    (le_of_eq (w4cr_action_eq_confirmation S r))
    (w4cr_openingCutoffHorizon S hhor) hu hw
  have hhead : voteDutyHead S rho w (S.hc.opening_slot r) = P.erase :=
    hheads w hw
  rw [hhead] at hres
  exact hres

/-! ## 2. `endpointBelowOpening` -/

/-- **Field 1.** Free by the choice of endpoint. -/
theorem w4cr_endpointBelowOpening
    (S : Setup V) {rho : Run V} {r : Round} {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot r) = some P) :
    ∀ Q : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r) = some Q →
        Block.Preceq P.erase Q.erase := by
  intro Q hQ
  rw [Option.some.inj (hP.symm.trans hQ)]
  exact Block.preceq_self _

/-! ## 3. `carriersBelowEndpoint` -/

/-- **Field 2.** Every honest round-`(r-1)` SG carrier is below the round's
opening proposal: the SG lifetime bound puts it below every honest head from
the first interior slot of round `r-1` on, and at the opening slot of round
`r` that head IS the proposal. -/
theorem w4cr_carriersBelowEndpoint
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r : Round}
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ r)
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot r) = some P) :
    ∀ w ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho w (r - 1)) P.erase := by
  intro x hx
  obtain ⟨w, hw⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
  have hr3 : 3 ≤ r := w4cr_three_le hr
  have hrpos : 0 < r := Nat.lt_of_lt_of_le (by decide : 0 < 3) hr3
  have hsucc : r - 2 + 1 = r - 1 := w4cr_sub_two_succ hr3
  have hc : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ r - 2 :=
    w4cr_deadline_le_sub_two hr
  have hd : S.hc.opening_slot (r - 2 + 1) + 1 ≤ S.hc.opening_slot r := by
    rw [hsucc]
    exact w4cr_prevOpening_succ_le S hrpos
  have hres := actionSGBlock_preceq_voterHeadAt_after_GST
    (delayExtra := delayExtra) S adm hcom hbelow hrec hdelay hpost hc hd
    (w4cr_openingCutoffHorizon S hhor) hx hw
  rw [hsucc] at hres
  have hheads := w4cr_openingHeads S adm hcom hbelow hrec hdelay hpost
    (Nat.le_trans (Nat.add_le_add_left (by decide : (2 : Nat) ≤ 3) _) hr)
    hcarrier hhor hP
  rw [hheads w hw] at hres
  exact hres

/-! ## 4. The opening proposal is processed at the carrier's own action read

The reader's FG root at that read is below the proposal and the opening slot's
honest votes are all above it, so one honest slot head above the proposal is
available to every honest reader by the slot's support cutoff. This is earlier's
`greatestPreviousHeadFamily_processed_at_read` step with the proposal in place
of the greatest-head endpoint. -/

/-- The opening slot's support cutoff is at or before the round action. -/
theorem w4cr_openingCutoff_le_action (S : Setup V) (r : Round) :
    Protocol.support_cutoff S.E (S.hc.opening_slot r) ≤ S.a r := by
  rw [w4cr_action_eq_confirmation S r]
  exact support_cutoff_le_confirmation_time S.E _

/-- The carrier's opening vote instant is after GST. -/
theorem w4cr_postOpeningVote
    (S : Setup V) {rho : Run V} {rGST gap : Round}
    (hpost : S.E.t_GST ≤ S.a rGST) {r : Round}
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ r) :
    S.E.t_GST ≤ Protocol.vote_time S.E (S.hc.opening_slot r) := by
  have hrpos : 0 < r :=
    Nat.lt_of_lt_of_le (by decide : 0 < 3) (w4cr_three_le hr)
  have hle : rGST ≤ r - 1 :=
    (w4cr_gst_le_deadline S rho rGST gap delayExtra).trans
      ((w4cr_deadline_le_sub_two hr).trans (Nat.sub_le_sub_left (by decide) r))
  refine hpost.trans (((action_strictMono S).monotone hle).trans ?_)
  exact le_trans (w4cr_action_lt_openingProposal S (Nat.sub_lt hrpos Nat.one_pos)).le
    (proposal_time_lt_vote_time S.E (S.hc.opening_slot r)).le

/-- **The opening proposal is in every honest reader's processed tree at the
round action.** -/
theorem w4cr_openingProposal_mem_actionRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r : Round}
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ r)
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot r) = some P) :
    ∀ v ∈ rho.honest, P.erase ∈ (rho.storeBeforeTime S v (S.a r)).T := by
  intro v hv
  have hr2 : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ r :=
    Nat.le_trans (Nat.add_le_add_left (by decide : (2 : Nat) ≤ 3) _) hr
  have hcone := w4cr_openingCone S adm hcom hbelow hrec hdelay hpost hr2
    hcarrier hhor hP
  have hroot := w4cr_fgRoot_preceq_openingProposal S adm hcom hbelow hrec hdelay
    hpost hr2 hcarrier hhor hP v hv
  have hcut := w4cr_openingCutoff_le_action S r
  have havailable := honestHeadsAvailableBefore_of_postHealingCone_at
    S adm.toNamedAdmissibleCore hv
    (w4cr_postOpeningVote (delayExtra := delayExtra) S hpost hr)
    (hcut.trans (w4cr_actionHorizon S hhor)) hcut hroot hcone
  exact (storeBeforeTime_mem_stamp_of_cone S adm hcom havailable hcut hcone
    (Block.preceq_self P.erase)).1

/-! ## 5. `anchorsBelowEndpoint` -/

/-- **Field 5.** earlier's `readAnchor_preceq_of_previousActionCeiling` at the
round's own action read: the previous round's carriers are below the proposal,
the proposal is processed there and the selected root is below it, so both
branches of the anchor selection land on the proposal's chain. -/
theorem w4cr_anchorsBelowEndpoint_current
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r : Round}
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ r)
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot r) = some P) :
    ∀ v ∈ rho.honest,
      Block.Preceq
        (Proofs.Optimistic.healAnchor S.E S.hc
          (actionStoreAt S rho v r).toHealing) P.erase := by
  intro v hv
  have hr2 : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ r :=
    Nat.le_trans (Nat.add_le_add_left (by decide : (2 : Nat) ≤ 3) _) hr
  have hrpos : 0 < r :=
    Nat.lt_of_lt_of_le (by decide : 0 < 3) (w4cr_three_le hr)
  have hsucc : r - 1 + 1 = r := Nat.sub_add_cancel hrpos
  have hArhor := w4cr_actionHorizon S hhor
  have hmem := w4cr_openingProposal_mem_actionRead S adm hcom hbelow hrec hdelay
    hpost hr hcarrier hhor hP v hv
  have hroot := w4cr_fgRoot_preceq_openingProposal S adm hcom hbelow hrec hdelay
    hpost hr2 hcarrier hhor hP v hv
  have hupper := w4cr_carriersBelowEndpoint S adm hcom hbelow hrec hdelay hpost
    hr hcarrier hhor hP
  have hpostPrev : S.E.t_GST ≤ S.a (r - 1) :=
    hpost.trans ((action_strictMono S).monotone
      ((w4cr_gst_le_deadline S rho rGST gap delayExtra).trans
        ((w4cr_deadline_le_sub_two hr).trans
          (Nat.sub_le_sub_left (by decide) r))))
  have hcutΓ : S.hc.Γ_neg1 S.E.Δ (r - 1 + 1) ≤ rho.horizon :=
    (next_Γ_neg1_lt_action S (r - 1)).le.trans
      (by simpa only [hsucc] using hArhor)
  have hread : S.hc.Γ_0 S.E.Δ (r - 1 + 1) ≤ S.a r := by
    rw [hsucc, Protocol.Γ_0_eq_proposal_time]
    exact w4cr_openingProposal_le_action S r
  have hanchor := readAnchor_preceq_of_previousActionCeiling
    S adm hbelow (r := r - 1) (t := S.a r) hpostPrev hcutΓ hread hv hmem hroot
    hupper
  have hround : S.hc.round_of (actionStoreAt S rho v r).toHealing.s = r := by
    simpa only [Protocol.Store.toHealing] using actionStoreAt_round S rho v r
  rw [Proofs.Optimistic.healAnchor_eq_get_sg_root, hround,
    actionStoreAt_sgRoot_eq_storeBeforeTime S rho v r]
  rw [hsucc] at hanchor
  exact hanchor

/-- **Named field 5.** The action read carries the prepared confirmation
anchor. This is the named proof of `readAnchor_preceq_of_previousActionCeiling`;
the action read and the confirmation input at the opening slot are the same
prepared read after the round arithmetic is normalized. -/
theorem w4cr_anchorsBelowEndpoint
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r : Round}
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ r)
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot r) = some P) :
    ∀ v ∈ rho.honest,
      Block.Preceq
        (PhaseGrades.nodeAnchor S (actionReadAt S rho v r) r) P.erase := by
  have hr2 : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ r :=
    Nat.le_trans (Nat.add_le_add_left (by decide : (2 : Nat) ≤ 3) _) hr
  have hrpos : 0 < r :=
    Nat.lt_of_lt_of_le (by decide : 0 < 3) (w4cr_three_le hr)
  have hsucc : r - 1 + 1 = r := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hrpos)
  have hArhor := w4cr_actionHorizon S hhor
  intro v hv
  have hmem := w4cr_openingProposal_mem_actionRead S adm hcom hbelow hrec hdelay
    hpost hr hcarrier hhor hP v hv
  have hroot := w4cr_fgRoot_preceq_openingProposal S adm hcom hbelow hrec hdelay
    hpost hr2 hcarrier hhor hP v hv
  have hupper := w4cr_carriersBelowEndpoint S adm hcom hbelow hrec hdelay hpost
    hr hcarrier hhor hP
  have hpostPrev : S.E.t_GST ≤ S.a (r - 1) :=
    hpost.trans ((action_strictMono S).monotone
      ((w4cr_gst_le_deadline S rho rGST gap delayExtra).trans
        ((w4cr_deadline_le_sub_two hr).trans
          (Nat.sub_le_sub_left (by decide) r))))
  have hcutΓ : S.hc.Γ_neg1 S.E.Δ (r - 1 + 1) ≤ rho.horizon :=
    (next_Γ_neg1_lt_action S (r - 1)).le.trans
      (by simpa only [hsucc] using hArhor)
  have hanchor := confirmationAnchorAt_preceq_of_previousCarriers
    S adm hbelow
      (q := r - 1) (s := S.hc.opening_slot r)
      (by simpa only [hsucc] using Proofs.HealingLemmas.round_of_opening_succ S.hc r)
      hpostPrev hcutΓ
      (by simpa only [opening_confirmation_time_eq_action] using hArhor)
      hupper hv
      (by
        simpa only [Internal.NamedRecoveryRead.confirmationInputRead,
          NamedActionReads.confirmationReadAt, opening_confirmation_time_eq_action]
          using hroot)
  have hct : Protocol.confirmation_time S.E (S.hc.opening_slot r) = S.a r :=
    (Protocol.a_eq_confirmation_time S.hc S.E r).symm
  have hread : Internal.NamedRecoveryRead.confirmationInputRead S rho v
      (S.hc.opening_slot r) =
      NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBeforeTime S rho (S.a r) v) (S.a r) := by
    simp only [Internal.NamedRecoveryRead.confirmationInputRead,
      NamedActionReads.confirmationReadAt, hct]
  rw [confirmationAnchorAt, namedConfirmationAnchor, hread] at hanchor
  have hs : (NamedActionReads.confirmationReadFrom S
      (NamedRun.stateBeforeTime S rho (S.a r) v) (S.a r)).st.core.s =
      S.E.slotOf (S.a r) := rfl
  rw [hs, Proofs.HealingLemmas.ActionRound.round_of_slotOf_a] at hanchor
  have hcache : (actionReadAt S rho v r).cache =
      (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBeforeTime S rho (S.a r) v) (S.a r)).cache := rfl
  have hst : (actionReadAt S rho v r).st =
      Protocol.NamedDuties.update_confirmation_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S
            (NamedRun.stateBeforeTime S rho (S.a r) v) (S.a r)).cache)
        S.E S.hc
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBeforeTime S rho (S.a r) v) (S.a r)).st
        (S.E.slotOf (S.a r) - 1) := rfl
  change Protocol.get_sg_root_with
      (NamedProfile.gradeContract (actionReadAt S rho v r).cache)
      S.E S.hc (actionReadAt S rho v r).st.core.toHealing r ⪯ P.erase
  rw [hcache, hst]
  exact hanchor

/-! ## 6. `roundFloor`

earlier's floor construction is `movingChainRoundFloor_or_lost_of_carrierCeiling`,
whose only content input is a retained named body above the endpoint that
reaches the reader's frontier band. Over route D that body is the opening
proposal itself, so the whole field reduces to the round's frontier band
(earlier's `actionReadBounds_greatestPreviousHead_after_SG_healing.1`, said about
the named derivation of the proposal). -/

/-- A run block whose erasure an honest reader holds is one of that reader's
named bodies. Body of `MovingChainRoundReadRun.mem_bodies_of_mem_T`, private
there. -/
theorem w4cr_mem_bodies_of_mem_T
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {t : Time} {B : NamedBlock V}
    (hBrun : RunBlock S rho B)
    (hmem : B.erase ∈ (rho.storeBeforeTime S v t).core.T) :
    B ∈ (rho.storeBeforeTime S v t).bodies := by
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedScheduleWellFormed t
  have hmemN : B.erase ∈ (rho.stateBefore S n v).st.core.T := by
    simpa only [Run.storeBeforeTime, hn] using hmem
  obtain ⟨D, hDmem, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n v hmemN
  have hDrun : RunBlock S rho D := Proofs.Bridges.runBlock_of_stateBefore_mem S hv hDmem
  have hDB : D = B :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      D B hDrun hBrun D B
      (Or.inl (Proofs.NamedAncestry.named_self D)) (Or.inr (Proofs.NamedAncestry.named_self B))
      (by rw [← Proofs.NamedWire.erase_root D, ← Proofs.NamedWire.erase_root B, hDerase])
  have hBmem : B ∈ (rho.stateBefore S n v).st.bodies := hDB ▸ hDmem
  simpa only [Run.storeBeforeTime, hn] using hBmem

/-- The opening proposal is a run block. -/
theorem w4cr_openingProposal_runBlock
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (hrpos : 0 < r)
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot r) = some P) :
    RunBlock S rho P :=
  proposedBlock_runBlock S adm
    (Nat.mul_pos hrpos (Nat.zero_lt_of_lt S.hc.R_ge_two)) hcarrier.1
    ((w4cr_openingProposal_le_action S r).trans (w4cr_actionHorizon S hhor)) hP

/-- The opening proposal is one of every honest reader's named bodies at the
round action. -/
theorem w4cr_openingProposal_mem_bodies
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r : Round}
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ r)
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot r) = some P) :
    ∀ v ∈ rho.honest, P ∈ (rho.storeBeforeTime S v (S.a r)).bodies := by
  intro v hv
  have hrpos : 0 < r :=
    Nat.lt_of_lt_of_le (by decide : 0 < 3) (w4cr_three_le hr)
  exact w4cr_mem_bodies_of_mem_T S adm hv
    (w4cr_openingProposal_runBlock S adm hrpos hcarrier hhor hP)
    (w4cr_openingProposal_mem_actionRead S adm hcom hbelow hrec hdelay hpost hr
      hcarrier hhor hP v hv)


/-! ## 6b. `plusOneCandidate`

earlier's route (`MovingSlotFoldAt.plusOneCandidate`, `MovingChainRoundReadRun`)
needs three things about the carrier's slot-`+1` proposal at the round action:
the selected root is below it, it is processed, and it reaches the frontier
band. Over route D the first is the FG-safety root bound read at slot
`opening_slot r + 1`, the second follows from that slot's honest vote cone
(whose support cutoff IS the round action), and the third is that slot's
frontier band. -/

/-- The slot-`(s+1)` proposal instant precedes the round action. -/
theorem w4cr_proposalSucc_le_action (S : Setup V) (r : Round) :
    Protocol.proposal_time S.E (S.hc.opening_slot r + 1) ≤ S.a r := by
  rw [w4cr_action_normal S r, w4cr_proposal_normal S.E _]
  refine Int.mul_le_mul_of_nonneg_right ?_ (le_of_lt S.E.Δ_pos)
  push_cast
  omega

/-- The round action precedes the `+2` proposal instant. -/
theorem w4cr_action_le_plusTwoProposal (S : Setup V) (r : Round) :
    S.a r ≤ Protocol.proposal_time S.E (S.hc.opening_slot r + 2) := by
  rw [w4cr_action_normal S r, w4cr_proposal_normal S.E _]
  refine Int.mul_le_mul_of_nonneg_right ?_ (le_of_lt S.E.Δ_pos)
  push_cast
  omega

/-- The `+2` proposal instant precedes the `+1` confirmation instant. -/
theorem w4cr_plusTwoProposal_le_plusOneConfirmation (S : Setup V) (r : Round) :
    Protocol.proposal_time S.E (S.hc.opening_slot r + 2) ≤
      Protocol.confirmation_time S.E (S.hc.opening_slot r + 1) := by
  rw [w4cr_proposal_normal S.E _, w4cr_confirmation_normal S.E _]
  refine Int.mul_le_mul_of_nonneg_right ?_ (le_of_lt S.E.Δ_pos)
  push_cast
  omega

/-- The first interior slot's support cutoff IS the round action. -/
theorem w4cr_interiorCutoff_eq_action (S : Setup V) (r : Round) :
    Protocol.support_cutoff S.E (S.hc.opening_slot r + 1) = S.a r :=
  (Protocol.a_eq_support_cutoff_succ S.hc S.E r).symm

/-- **Field 7 over the first interior slot's heads and band.** -/
theorem w4cr_plusOneCandidate_of_heads
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r : Round}
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ r)
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    {P1 : NamedBlock V}
    (hP1 : proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1)
    (hheads1 : ∀ v ∈ rho.honest,
      voterHeadAt S rho v (S.hc.opening_slot r + 1) = P1.erase)
    (hband1 : ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v (S.a r)).core.h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg P1).h) :
    ∀ v ∈ rho.honest,
      P1.erase ∈
        Protocol.get_filtered_block_tree
          (actionStoreAt S rho v r).st.core.toHealing.toFG := by
  intro v hv
  have hArhor := w4cr_actionHorizon S hhor
  have hcutEq := w4cr_interiorCutoff_eq_action S r
  have hvoteHor1 : Protocol.vote_time S.E (S.hc.opening_slot r + 1) ≤
      rho.horizon := by
    refine le_trans ?_ hArhor
    rw [← hcutEq, ← Proofs.Optimistic.vote_time_add_delta]
    exact Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)
  have hcone1 := honestProposal_slotVoteCone_after_SG_healing_named
    (delayExtra := delayExtra) S adm hcom hbelow hrec hdelay hpost
    (Nat.le_succ_of_le (Nat.mul_le_mul_right S.hc.R
      (Nat.le_trans (Nat.add_le_add_left (by decide : (2 : Nat) ≤ 3) _) hr)))
    hvoteHor1 hcarrier.2.1 hP1
  have hdeadlineLt : fgSafetyProgressDeadline S rho rGST gap delayExtra < r :=
    lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 3)) hr
  have hroot1 : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v (S.a r)).toHealing.toFG) P1.erase := by
    obtain ⟨w, hw⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
    have hres := fgRoot_preceq_previousHead_through_confirmation_after_GST
      (delayExtra := delayExtra) S adm hcom hbelow hrec hdelay hpost
      (read := S.a r) ((action_strictMono S).monotone hdeadlineLt.le) hArhor
      (s := S.hc.opening_slot r + 1)
      (Nat.le_succ_of_le
        (Nat.le_of_succ_le (w4cr_openingSlot_two_le S hdeadlineLt)))
      (by
        rw [w4cr_action_eq_confirmation S r]
        exact w4cr_confirmation_mono S.E (Nat.le_succ _))
      (by rw [Proofs.Optimistic.vote_time_add_delta, hcutEq]; exact hArhor) hv hw
    have hhead1 : voteDutyHead S rho w (S.hc.opening_slot r + 1) = P1.erase :=
      hheads1 w hw
    rw [hhead1] at hres
    exact hres
  have hpostVote1 : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot r + 1) :=
    (w4cr_postOpeningVote (delayExtra := delayExtra) S hpost hr).trans
      (Protocol.vote_time_mono_slots S.E (Nat.le_succ _))
  have havailable1 := honestHeadsAvailableBefore_of_postHealingCone_at
    S adm.toNamedAdmissibleCore hv hpostVote1
    (by rw [hcutEq]; exact hArhor) (le_of_eq hcutEq) hroot1 hcone1
  have hmemT1 := (storeBeforeTime_mem_stamp_of_cone S adm hcom havailable1
    (le_of_eq hcutEq) hcone1 (Block.preceq_self P1.erase)).1
  have hP1run : RunBlock S rho P1 :=
    proposedBlock_runBlock S adm (Nat.succ_pos _) hcarrier.2.1
      ((w4cr_proposalSucc_le_action S r).trans hArhor) hP1
  have hbodies1 := w4cr_mem_bodies_of_mem_T S adm hv hP1run hmemT1
  rw [actionStoreAt_filteredTree_eq_storeBeforeTime S rho v r]
  exact storeBeforeTime_mem_filtered_of_band S adm hbodies1 hroot1 (hband1 v hv)

/-! ## 6c. `batchComplete`

`MovingSlotFoldAt.batchComplete` (`MovingChainBatchRun`) uses the fold only to
produce two facts about the slot before the round's opening slot: that slot's
honest vote cone sits above the previous round's honest SG carriers, and the
slot's honest heads are available to every honest reader by its support
cutoff. Both are per-round statements, so the body is reproduced here over
them directly. -/


/-- The slot before a round's opening slot has its support cutoff before that
round's batch cutoff. Copy of `MovingChainBatchRun.support_cutoff_le_Γ_neg1`,
private there. -/
private theorem w4cr_support_cutoff_normal (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s = (4 * (s : Time) + 2) * E.Δ := by
  unfold Protocol.support_cutoff Env.t slotStart
  ring

private theorem w4cr_Γ_neg1_normal (S : Setup V) (q : Round) :
    S.hc.Γ_neg1 S.E.Δ q =
      (4 * ((S.hc.opening_slot q : Slot) : Time) - 1) * S.E.Δ := by
  unfold Protocol.HealConfig.Γ_neg1 slotStart
  ring

private theorem w4cr_support_cutoff_le_Γ_neg1
    (S : Setup V) {q : Round} {d : Slot}
    (hd : d + 1 = S.hc.opening_slot q) :
    Protocol.support_cutoff S.E d ≤ S.hc.Γ_neg1 S.E.Δ q := by
  rw [w4cr_support_cutoff_normal S.E d, w4cr_Γ_neg1_normal S q, ← hd]
  refine Int.mul_le_mul_of_nonneg_right ?_ (le_of_lt S.E.Δ_pos)
  push_cast
  omega

/-- The same cutoff also precedes that round's action. Copy of
`MovingChainBatchRun.support_cutoff_le_action`, private there. -/
private theorem w4cr_support_cutoff_le_action
    (S : Setup V) {q : Round} {d : Slot}
    (hd : d + 1 = S.hc.opening_slot q) :
    Protocol.support_cutoff S.E d ≤ S.a q := by
  rw [w4cr_support_cutoff_normal S.E d, w4cr_action_normal S q, ← hd]
  refine Int.mul_le_mul_of_nonneg_right ?_ (le_of_lt S.E.Δ_pos)
  push_cast
  omega

/-- **Field 3 over the previous slot's cone and availability.** -/
theorem w4cr_batchComplete_of_cone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {c : Round} {d : Slot} (hd : d + 1 = S.hc.opening_slot (c + 1))
    (hpost : S.E.t_GST ≤ S.a c)
    (hcutHor : S.hc.Γ_neg1 S.E.Δ (c + 1) ≤ rho.horizon)
    (hcone : ∀ w ∈ rho.honest,
      NamedHonestVotesCone S rho d
        (fun X => Block.Preceq (actionSGBlockAt S rho w c) X))
    (havail : ∀ v ∈ rho.honest,
      HonestHeadsAvailableBefore S rho d v
        (Protocol.support_cutoff S.E d)) :
    ∀ v ∈ rho.honest, ∀ w ∈ rho.honest,
      CanonicalBatchVoteAt S rho (c + 1)
        (actionStoreAt S rho v (c + 1)).toHealing.gradeView w := by
  intro v hv w hw
  have hcutAction : Protocol.support_cutoff S.E d ≤ S.a (c + 1) :=
    w4cr_support_cutoff_le_action S hd
  have hcutΓ : Protocol.support_cutoff S.E d ≤ S.hc.Γ_neg1 S.E.Δ (c + 1) :=
    w4cr_support_cutoff_le_Γ_neg1 S hd
  obtain ⟨hmemRaw, hstampRaw⟩ := storeBeforeTime_mem_stamp_of_cone
    S adm hcom (havail v hv) hcutAction (hcone w hw)
    (Block.preceq_self (actionSGBlockAt S rho w c))
  have hgv := actionGradeView_eq_gradeViewAt''' S rho v (c + 1)
  have hTeq : (gradeViewAt S rho v (c + 1)).T =
      (rho.storeBeforeTime S v (S.a (c + 1))).T := rfl
  have htbEq : (gradeViewAt S rho v (c + 1)).timestamp_block =
      (rho.storeBeforeTime S v (S.a (c + 1))).timestamp_block := rfl
  have hmem : actionSGBlockAt S rho w c ∈ (gradeViewAt S rho v (c + 1)).T := by
    rw [hTeq]
    exact hmemRaw
  obtain ⟨C, hCmem, hCerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (S.a (c + 1)) v
      (by simpa only [Run.storeBeforeTime] using hmemRaw)
  obtain ⟨N, hN, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedScheduleWellFormed.sorted (S.a (c + 1))
  have hCrun : RunBlock S rho C := by
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i := N)
    simpa only [hN] using hCmem
  have hfind : Block.find? (gradeViewAt S rho v (c + 1)).T
      (actionSGBlockAt S rho w c).root =
        some (actionSGBlockAt S rho w c) := by
    apply Proofs.Optimistic.find?_eq_some_of_unique hmem
    intro X hX hroot'
    have hXmem : X ∈ (rho.storeBeforeTime S v (S.a (c + 1))).T := by
      rw [hTeq] at hX
      exact hX
    obtain ⟨Xn, hXnmem, hXnerase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
        (S.a (c + 1)) v
        (by simpa only [Run.storeBeforeTime] using hXmem)
    have hXrun : RunBlock S rho Xn := by
      apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i := N)
      simpa only [hN] using hXnmem
    have hrawRoots : Xn.erase.root = C.erase.root := by
      rw [hXnerase, hCerase]
      exact hroot'
    have hroots : Xn.root = C.root :=
      (Proofs.NamedWire.erase_root Xn).symm.trans
        (hrawRoots.trans (Proofs.NamedWire.erase_root C))
    have heq := adm.toNamedRootCollisionFree.root_injective Xn C
      hXrun hCrun Xn C (Or.inl (Proofs.NamedAncestry.named_self Xn))
      (Or.inr (Proofs.NamedAncestry.named_self C)) hroots
    exact hXnerase.symm.trans ((congrArg NamedBlock.erase heq).trans hCerase)
  have hblockStamp : occurrenceBefore
      ((gradeViewAt S rho v (c + 1)).timestamp_block
        (actionSGBlockAt S rho w c))
      (S.hc.Γ_neg1 S.E.Δ (c + 1)) = true := by
    rw [htbEq]
    refine occurrenceBefore_mono hcutΓ ?_
    rw [← stampedBefore_eq_occurrenceBefore]
    exact hstampRaw
  have hvoteStamp := actionSGVote_stamp_before_next_Γ_neg1 S adm hw hv c
    hpost hcutHor
  have hbatch := actionSGVote_mem_next_round_batch S adm hw hv c hpost hcutHor
  rw [hgv]
  refine ⟨actionSGVoteAt S rho w c, hbatch, rfl, rfl, hfind, ?_⟩
  simp only [Protocol.sg_resolution_time, actionSGVoteAt, hfind]
  exact occurrenceBefore_max hvoteStamp hblockStamp

/-- The first interior slot's vote instant is inside the horizon. -/
theorem w4cr_interiorVoteHorizon (S : Setup V) {rho : Run V} {r : Round}
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon) :
    Protocol.vote_time S.E (S.hc.opening_slot r + 1) ≤ rho.horizon := by
  refine le_trans ?_ (w4cr_actionHorizon S hhor)
  rw [← w4cr_interiorCutoff_eq_action S r, ← Proofs.Optimistic.vote_time_add_delta]
  exact Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)


/-- **Every honest head at the carrier's first interior slot IS that slot's
proposal** — the pin-free general-slot head equality (the corresponding branch, b8248b5a)
read at `opening_slot r + 1`. -/
theorem w4cr_interiorHeads
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r : Round}
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ r)
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    {P1 : NamedBlock V}
    (hP1 : proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1) :
    ∀ v ∈ rho.honest,
      voterHeadAt S rho v (S.hc.opening_slot r + 1) = P1.erase :=
  honestProposal_voterHeadAt_eq_after_SG_healing_named_slot
    (delayExtra := delayExtra) S adm hcom hbelow hrec hdelay hpost
    (Nat.le_succ_of_le (Nat.mul_le_mul_right S.hc.R
      (Nat.le_trans (Nat.add_le_add_left (by decide : (2 : Nat) ≤ 3) _) hr)))
    (w4cr_interiorVoteHorizon S hhor) hcarrier.2.1 hP1

/-! ## 6d. The two closers in the record's own shape

`W4CarrierRoundResiduals` asks for fields 3 and 7 verbatim; these two
corollaries discharge them from the named residuals above, so a consumer plugs
in the cone/availability pair and the first interior slot's head equality and
band instead of the fields themselves. -/

/-- Field 3 at the record's own round index. -/
theorem w4cr_batchComplete_field_of_cone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {r : Round} (hrpos : 0 < r)
    (hpost : S.E.t_GST ≤ S.a (r - 1))
    (hcutHor : S.hc.Γ_neg1 S.E.Δ r ≤ rho.horizon)
    (hcone : ∀ w ∈ rho.honest,
      NamedHonestVotesCone S rho (S.hc.opening_slot r - 1)
        (fun X => Block.Preceq (actionSGBlockAt S rho w (r - 1)) X))
    (havail : ∀ v ∈ rho.honest,
      HonestHeadsAvailableBefore S rho (S.hc.opening_slot r - 1) v
        (Protocol.support_cutoff S.E (S.hc.opening_slot r - 1))) :
    ∀ v ∈ rho.honest, ∀ w ∈ rho.honest,
      CanonicalBatchVoteAt S rho r
        (actionStoreAt S rho v r).toHealing.gradeView w := by
  have hsucc : r - 1 + 1 = r := Nat.sub_add_cancel hrpos
  have hopenPos : 0 < S.hc.opening_slot r :=
    Nat.mul_pos hrpos (Nat.zero_lt_of_lt S.hc.R_ge_two)
  have hd : S.hc.opening_slot r - 1 + 1 = S.hc.opening_slot (r - 1 + 1) := by
    rw [hsucc]
    exact Nat.succ_pred_eq_of_pos hopenPos
  have hres := w4cr_batchComplete_of_cone S adm hcom hd
    (by simpa only [hsucc] using hpost)
    (by simpa only [hsucc] using hcutHor)
    (by simpa only [hsucc] using hcone)
    havail
  simpa only [hsucc] using hres

/-- Field 7 in the record's own shape. -/
theorem w4cr_plusOneCandidate_field_of_heads
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r : Round}
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ r)
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    (hheads1 : ∀ P1 : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1 →
      ∀ v ∈ rho.honest,
        voterHeadAt S rho v (S.hc.opening_slot r + 1) = P1.erase)
    (hband1 : ∀ P1 : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1 →
      ∀ v ∈ rho.honest,
        (rho.storeBeforeTime S v (S.a r)).core.h_max - 1 ≤
          (Protocol.derive_named S.E S.cfg P1).h) :
    ∀ v ∈ rho.honest, ∀ P1 : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1 →
      P1.erase ∈
        Protocol.get_filtered_block_tree
          (actionStoreAt S rho v r).st.core.toHealing.toFG := by
  intro v hv P1 hP1
  exact w4cr_plusOneCandidate_of_heads S adm hcom hbelow hrec hdelay hpost hr
    hcarrier hhor hP1 (hheads1 P1 hP1) (hband1 P1 hP1) v hv



/-- Every honest vote of the slot before the round's opening slot names a
block at or above every honest round-`(r-1)` SG carrier. -/
theorem w4cr_previousSlotCone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r : Round}
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon) :
    ∀ w ∈ rho.honest,
      NamedHonestVotesCone S rho (S.hc.opening_slot r - 1)
        (fun X => Block.Preceq (actionSGBlockAt S rho w (r - 1)) X) := by
  intro w hw x hx hxc
  have hr3 : 3 ≤ r := w4cr_three_le hr
  have hrpos : 0 < r := Nat.lt_of_lt_of_le (by decide : 0 < 3) hr3
  have htwo := w4cr_openingSlot_two_le S (Nat.sub_lt hrpos Nat.one_pos)
  have hopenPos : 0 < S.hc.opening_slot r :=
    Nat.mul_pos hrpos (Nat.zero_lt_of_lt S.hc.R_ge_two)
  have hd1 : S.hc.opening_slot r - 1 + 1 = S.hc.opening_slot r :=
    Nat.succ_pred_eq_of_pos hopenPos
  have hcut : Protocol.support_cutoff S.E (S.hc.opening_slot r - 1) ≤ S.a r :=
    w4cr_support_cutoff_le_action S hd1
  have hΔ : Protocol.vote_time S.E (S.hc.opening_slot r - 1) + S.E.Δ ≤
      rho.horizon := by
    rw [Proofs.Optimistic.vote_time_add_delta]
    exact hcut.trans (w4cr_actionHorizon S hhor)
  have hdhor : Protocol.vote_time S.E (S.hc.opening_slot r - 1) ≤ rho.horizon :=
    (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans hΔ
  obtain ⟨X, hXerase, hXrun, hXemit⟩ :=
    voteDutyHead_runBlock_and_emits S adm (w4cr_pos_pred htwo) hdhor hx hxc
  refine ⟨X, ?_, hXrun, hXemit⟩
  have hsucc : r - 2 + 1 = r - 1 := w4cr_sub_two_succ hr3
  have hdlow : S.hc.opening_slot (r - 2 + 1) + 1 ≤ S.hc.opening_slot r - 1 := by
    rw [hsucc]
    exact w4cr_le_pred htwo
  have hres := actionSGBlock_preceq_voterHeadAt_after_GST
    (delayExtra := delayExtra) S adm hcom hbelow hrec hdelay hpost
    (w4cr_deadline_le_sub_two hr) hdlow hΔ hw hx
  rw [hsucc] at hres
  have hXhead : X.erase =
      voterHeadAt S rho x (S.hc.opening_slot r - 1) := hXerase
  rw [hXhead]
  exact hres

/-- The heads of that slot are available to every honest reader by its
support cutoff, given that the round is not lost. -/
theorem w4cr_previousSlotAvailability
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r : Round}
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    (hnl : ¬ LostRoundAt S rho r) :
    ∀ v ∈ rho.honest,
      HonestHeadsAvailableBefore S rho (S.hc.opening_slot r - 1) v
        (Protocol.support_cutoff S.E (S.hc.opening_slot r - 1)) := by
  intro v hv
  obtain ⟨w0, hw0⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
  have hr3 : 3 ≤ r := w4cr_three_le hr
  have hrpos : 0 < r := Nat.lt_of_lt_of_le (by decide : 0 < 3) hr3
  have hopenPos : 0 < S.hc.opening_slot r :=
    Nat.mul_pos hrpos (Nat.zero_lt_of_lt S.hc.R_ge_two)
  have hd1 : S.hc.opening_slot r - 1 + 1 = S.hc.opening_slot r :=
    Nat.succ_pred_eq_of_pos hopenPos
  have hcut : Protocol.support_cutoff S.E (S.hc.opening_slot r - 1) ≤ S.a r :=
    w4cr_support_cutoff_le_action S hd1
  have htwo := w4cr_openingSlot_two_le S (Nat.sub_lt hrpos Nat.one_pos)
  have hroot : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v (S.a r)).core.toHealing.toFG)
      (actionSGBlockAt S rho w0 (r - 1)) := by
    by_contra hbad
    exact hnl ⟨v, hv, w0, hw0, hbad⟩
  have hpostVoteD : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot r - 1) := by
    refine hpost.trans (((action_strictMono S).monotone
      ((w4cr_gst_le_deadline S rho rGST gap delayExtra).trans
        (w4cr_deadline_le_sub_two hr))).trans ?_)
    refine le_trans (w4cr_action_lt_openingProposal S
      (w4cr_sub_two_lt_sub_one hr3)).le ?_
    exact (proposal_time_lt_vote_time S.E
      (S.hc.opening_slot (r - 1))).le.trans
      (Protocol.vote_time_mono_slots S.E
        (Nat.le_of_succ_le (w4cr_le_pred htwo)))
  exact honestHeadsAvailableBefore_of_postHealingCone_at
    S adm.toNamedAdmissibleCore hv hpostVoteD
    (hcut.trans (w4cr_actionHorizon S hhor)) hcut hroot
    (w4cr_previousSlotCone S adm hcom hbelow hrec hdelay hpost hr hhor w0 hw0)

/-- **Field 3 from non-lostness alone.** -/
theorem w4cr_batchComplete_of_notLost
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r : Round}
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    (hnl : ¬ LostRoundAt S rho r) :
    ∀ v ∈ rho.honest, ∀ w ∈ rho.honest,
      CanonicalBatchVoteAt S rho r
        (actionStoreAt S rho v r).toHealing.gradeView w := by
  have hr3 : 3 ≤ r := w4cr_three_le hr
  have hrpos : 0 < r := Nat.lt_of_lt_of_le (by decide : 0 < 3) hr3
  have hpostPrev : S.E.t_GST ≤ S.a (r - 1) :=
    hpost.trans ((action_strictMono S).monotone
      ((w4cr_gst_le_deadline S rho rGST gap delayExtra).trans
        ((w4cr_deadline_le_sub_two hr).trans (Nat.sub_le_sub_left (by decide) r))))
  have hsucc : r - 1 + 1 = r := Nat.sub_add_cancel hrpos
  have hcutHor : S.hc.Γ_neg1 S.E.Δ r ≤ rho.horizon := by
    have hstep : S.hc.Γ_neg1 S.E.Δ (r - 1 + 1) ≤ rho.horizon :=
      (next_Γ_neg1_lt_action S (r - 1)).le.trans
        (by simpa only [hsucc] using w4cr_actionHorizon S hhor)
    simpa only [hsucc] using hstep
  exact w4cr_batchComplete_field_of_cone S adm hcom hrpos hpostPrev hcutHor
    (w4cr_previousSlotCone S adm hcom hbelow hrec hdelay hpost hr hhor)
    (w4cr_previousSlotAvailability S adm hcom hbelow hrec hdelay hpost hr hhor hnl)



/-- **Field 7 over the first interior slot's band alone.** -/
theorem w4cr_plusOneCandidate_of_band
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r : Round}
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ r)
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    (hband1 : ∀ P1 : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1 →
      ∀ v ∈ rho.honest,
        (rho.storeBeforeTime S v (S.a r)).core.h_max - 1 ≤
          (Protocol.derive_named S.E S.cfg P1).h) :
    ∀ v ∈ rho.honest, ∀ P1 : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1 →
      P1.erase ∈
        Protocol.get_filtered_block_tree
          (actionStoreAt S rho v r).st.core.toHealing.toFG := by
  refine w4cr_plusOneCandidate_field_of_heads S adm hcom hbelow hrec hdelay
    hpost hr hcarrier hhor ?_ hband1
  intro P1 hP1
  exact w4cr_interiorHeads S adm hcom hbelow hrec hdelay hpost hr hcarrier
    hhor hP1




/-- Every honest round-`(r-1)` SG carrier IS the previous round's opening
proposal, when that round's proposer is honest. -/
theorem w4cr_previousCarrier_eq_previousOpening
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r : Round}
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    (hprev : S.E.proposer (S.hc.opening_slot (r - 1)) ∈ rho.honest)
    {Q : NamedBlock V}
    (hQ : proposedBlockAt S rho (S.hc.opening_slot (r - 1)) = some Q) :
    ∀ v ∈ rho.honest, actionSGBlockAt S rho v (r - 1) = Q.erase := by
  intro v hv
  have hconfHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot (r - 1)) ≤ rho.horizon := by
    rw [← w4cr_action_eq_confirmation S (r - 1)]
    exact ((action_strictMono S).monotone (Nat.sub_le r 1)).trans
      (w4cr_actionHorizon S hhor)
  exact (honestProposal_actionSelectors_after_SG_healing_named_of_openingProposer
    (delayExtra := delayExtra) S adm hcom hbelow hrec hdelay hpost
    (w4cr_deadline_le_sub_one hr) hprev hQ hconfHor v hv).1

/-- The previous round's opening proposal is below this round's. -/
theorem w4cr_previousOpening_preceq_opening
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r : Round}
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ r)
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    (hprev : S.E.proposer (S.hc.opening_slot (r - 1)) ∈ rho.honest)
    {Q P : NamedBlock V}
    (hQ : proposedBlockAt S rho (S.hc.opening_slot (r - 1)) = some Q)
    (hP : proposedBlockAt S rho (S.hc.opening_slot r) = some P) :
    Block.Preceq Q.erase P.erase := by
  obtain ⟨w, hw⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
  have hsg := w4cr_previousCarrier_eq_previousOpening S adm hcom hbelow hrec
    hdelay hpost hr hhor hprev hQ w hw
  rw [← hsg]
  exact w4cr_carriersBelowEndpoint S adm hcom hbelow hrec hdelay hpost hr
    hcarrier hhor hP w hw

/-- The previous round's opening proposal is below the carrier's first
interior proposal. -/
theorem w4cr_previousOpening_preceq_interior
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r : Round}
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ r)
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    (hprev : S.E.proposer (S.hc.opening_slot (r - 1)) ∈ rho.honest)
    {Q P1 : NamedBlock V}
    (hQ : proposedBlockAt S rho (S.hc.opening_slot (r - 1)) = some Q)
    (hP1 : proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1) :
    Block.Preceq Q.erase P1.erase := by
  obtain ⟨w, hw⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
  have hr3 : 3 ≤ r := w4cr_three_le hr
  have hrpos : 0 < r := Nat.lt_of_lt_of_le (by decide : 0 < 3) hr3
  have hsucc : r - 2 + 1 = r - 1 := w4cr_sub_two_succ hr3
  have htwo := w4cr_openingSlot_two_le S (Nat.sub_lt hrpos Nat.one_pos)
  have hdlow : S.hc.opening_slot (r - 2 + 1) + 1 ≤ S.hc.opening_slot r + 1 := by
    rw [hsucc]
    exact Nat.add_le_add_right (Nat.le_of_succ_le (Nat.le_of_succ_le htwo)) 1
  have hΔ : Protocol.vote_time S.E (S.hc.opening_slot r + 1) + S.E.Δ ≤
      rho.horizon := by
    rw [Proofs.Optimistic.vote_time_add_delta, w4cr_interiorCutoff_eq_action S r]
    exact w4cr_actionHorizon S hhor
  have hres := actionSGBlock_preceq_voterHeadAt_after_GST
    (delayExtra := delayExtra) S adm hcom hbelow hrec hdelay hpost
    (w4cr_deadline_le_sub_two hr) hdlow hΔ hw hw
  rw [hsucc] at hres
  have hsg := w4cr_previousCarrier_eq_previousOpening S adm hcom hbelow hrec
    hdelay hpost hr hhor hprev hQ w hw
  rw [hsg] at hres
  rw [w4cr_interiorHeads S adm hcom hbelow hrec hdelay hpost hr hcarrier hhor
    hP1 w hw] at hres
  exact hres


/-- **Field 4 at the  floor.** -/
theorem w4cr_roundFloorFields_atPreviousOpening
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r : Round}
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ r)
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    (hprev : S.E.proposer (S.hc.opening_slot (r - 1)) ∈ rho.honest)
    (hnl : ¬ LostRoundAt S rho r)
    {Q P : NamedBlock V}
    (hQ : proposedBlockAt S rho (S.hc.opening_slot (r - 1)) = some Q)
    (hP : proposedBlockAt S rho (S.hc.opening_slot r) = some P)
    (hband : ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v (S.a r)).h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg P).h) :
    RoundFloorFieldsAt S rho r Q.erase := by
  obtain ⟨w0, hw0⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
  have hsg := w4cr_previousCarrier_eq_previousOpening S adm hcom hbelow hrec
    hdelay hpost hr hhor hprev hQ
  have hbodies := w4cr_openingProposal_mem_bodies S adm hcom hbelow hrec hdelay
    hpost hr hcarrier hhor hP
  have hQP := w4cr_previousOpening_preceq_opening S adm hcom hbelow hrec hdelay
    hpost hr hcarrier hhor hprev hQ hP
  refine { floorBelowCarriers := ?_, floorAboveRoots := ?_, floorWitness := ?_ }
  · intro w hw
    rw [hsg w hw]
    exact Block.preceq_self _
  · intro v hv
    have h : Block.Preceq
        (Protocol.get_fg_root (healStoreAt S rho v r).toFG)
        (actionSGBlockAt S rho w0 (r - 1)) := by
      by_contra hbad
      exact hnl ⟨v, hv, w0, hw0, hbad⟩
    rw [hsg w0 hw0] at h
    exact h
  · intro v hv
    exact canonicalConeWitness_of_bandDescendant S hQP (hbodies v hv)
      (hband v hv)




/-- **Field 6 at the  floor**, over the `+2` proposal read's band.

The floor is below the carrier's first interior proposal, which the `+2`
proposer holds at the band with its own selected root below it, so the floor is
either active there or the root has already passed it. -/
theorem w4cr_floorActive_atPreviousOpening
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r : Round}
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ r)
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    (hprev : S.E.proposer (S.hc.opening_slot (r - 1)) ∈ rho.honest)
    {Q P1 : NamedBlock V}
    (hQ : proposedBlockAt S rho (S.hc.opening_slot (r - 1)) = some Q)
    (hP1 : proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1)
    (hband2 : ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v
          (Protocol.proposal_time S.E
            (S.hc.opening_slot r + 2))).core.h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg P1).h) :
    Q.erase ∈ Protocol.get_filtered_block_tree
        (Protocol.proposerDutyStore S rho
          (S.hc.opening_slot r + 2)).toHealing.toFG ∨
      Block.Prec Q.erase
        (Protocol.get_fg_root
          (rho.storeBeforeTime S
            (S.E.proposer (S.hc.opening_slot r + 2))
            (Protocol.proposal_time S.E
              (S.hc.opening_slot r + 2))).core.toHealing.toFG) := by
  classical
  have huh : S.E.proposer (S.hc.opening_slot r + 2) ∈ rho.honest := hcarrier.2.2
  have hArhor := w4cr_actionHorizon S hhor
  have hdeadlineLt : fgSafetyProgressDeadline S rho rGST gap delayExtra < r :=
    lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 3)) hr
  have hthor : Protocol.proposal_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon :=
    (proposal_time_le_confirmation_time S.E _).trans hhor
  have hcutT : Protocol.support_cutoff S.E (S.hc.opening_slot r + 1) ≤
      Protocol.proposal_time S.E (S.hc.opening_slot r + 2) := by
    rw [w4cr_interiorCutoff_eq_action S r]
    exact w4cr_action_le_plusTwoProposal S r
  have hsHi : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra) + 1 ≤
      S.hc.opening_slot r + 1 :=
    (Nat.le_of_succ_le (w4cr_openingSlot_two_le S hdeadlineLt)).trans
      (Nat.le_succ _)
  have hΔ1 : Protocol.vote_time S.E (S.hc.opening_slot r + 1) + S.E.Δ ≤
      rho.horizon := by
    rw [Proofs.Optimistic.vote_time_add_delta, w4cr_interiorCutoff_eq_action S r]
    exact hArhor
  have hheads1 := w4cr_interiorHeads S adm hcom hbelow hrec hdelay hpost hr
    hcarrier hhor hP1
  have hroot2 : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S (S.E.proposer (S.hc.opening_slot r + 2))
          (Protocol.proposal_time S.E
            (S.hc.opening_slot r + 2))).core.toHealing.toFG) P1.erase := by
    obtain ⟨w, hw⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
    have hres := fgRoot_preceq_previousHead_through_confirmation_after_GST
      (delayExtra := delayExtra) S adm hcom hbelow hrec hdelay hpost
      (read := Protocol.proposal_time S.E (S.hc.opening_slot r + 2))
      (((action_strictMono S).monotone hdeadlineLt.le).trans
        (w4cr_action_le_plusTwoProposal S r)) hthor
      (s := S.hc.opening_slot r + 1) hsHi
      (w4cr_plusTwoProposal_le_plusOneConfirmation S r) hΔ1 huh hw
    have hhead1 : voteDutyHead S rho w (S.hc.opening_slot r + 1) = P1.erase :=
      hheads1 w hw
    rw [hhead1] at hres
    exact hres
  have hcone1 := honestProposal_slotVoteCone_after_SG_healing_named
    (delayExtra := delayExtra) S adm hcom hbelow hrec hdelay hpost
    (Nat.le_succ_of_le (Nat.mul_le_mul_right S.hc.R
      (Nat.le_trans (Nat.add_le_add_left (by decide : (2 : Nat) ≤ 3) _) hr)))
    (w4cr_interiorVoteHorizon S hhor) hcarrier.2.1 hP1
  have hpostVote1 : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot r + 1) :=
    (w4cr_postOpeningVote (delayExtra := delayExtra) S hpost hr).trans
      (Protocol.vote_time_mono_slots S.E (Nat.le_succ _))
  have havail2 := honestHeadsAvailableBefore_of_postHealingCone_at
    S adm.toNamedAdmissibleCore huh hpostVote1
    (by rw [w4cr_interiorCutoff_eq_action S r]; exact hArhor) hcutT hroot2 hcone1
  have hmemT2 := (storeBeforeTime_mem_stamp_of_cone S adm hcom havail2 hcutT
    hcone1 (Block.preceq_self P1.erase)).1
  have hP1run : RunBlock S rho P1 :=
    proposedBlock_runBlock S adm (Nat.succ_pos _) hcarrier.2.1
      ((w4cr_proposalSucc_le_action S r).trans hArhor) hP1
  have hbodies2 := w4cr_mem_bodies_of_mem_T S adm huh hP1run hmemT2
  have hQP1 := w4cr_previousOpening_preceq_interior S adm hcom hbelow hrec
    hdelay hpost hr hcarrier hhor hprev hQ hP1
  by_cases hrootQ : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S (S.E.proposer (S.hc.opening_slot r + 2))
          (Protocol.proposal_time S.E
            (S.hc.opening_slot r + 2))).core.toHealing.toFG) Q.erase
  · left
    have hpc : ParentClosed
        (rho.storeBeforeTime S (S.E.proposer (S.hc.opening_slot r + 2))
          (Protocol.proposal_time S.E (S.hc.opening_slot r + 2))).core := by
      simpa only [Run.storeBeforeTime] using
        Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
          (Protocol.proposal_time S.E (S.hc.opening_slot r + 2))
          (S.E.proposer (S.hc.opening_slot r + 2))
    have hFJ : Block.Preceq
        (rho.storeBeforeTime S (S.E.proposer (S.hc.opening_slot r + 2))
          (Protocol.proposal_time S.E (S.hc.opening_slot r + 2))).core.F
        (rho.storeBeforeTime S (S.E.proposer (S.hc.opening_slot r + 2))
          (Protocol.proposal_time S.E
            (S.hc.opening_slot r + 2))).core.J := by
      simpa only [Run.storeBeforeTime] using
        Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
          (Protocol.proposal_time S.E (S.hc.opening_slot r + 2))
          (S.E.proposer (S.hc.opening_slot r + 2))
    obtain ⟨W, hWT, hQW, hheightW⟩ :=
      canonicalConeWitness_of_bandDescendant S hQP1 hbodies2 (hband2 _ huh)
    have hmemf := canonicalConeSegment_mem_filtered_of_root_preceq hpc hFJ
      hrootQ hWT hheightW (Block.preceq_self Q.erase) hQW
    simpa only [Protocol.proposerDutyStore, Proofs.Optimistic.tickStore] using hmemf
  · right
    rcases Block.preceq_linear hroot2 hQP1 with h | h
    · exact absurd h hrootQ
    · have hne : Q.erase ≠
          Protocol.get_fg_root
            (rho.storeBeforeTime S (S.E.proposer (S.hc.opening_slot r + 2))
              (Protocol.proposal_time S.E
                (S.hc.opening_slot r + 2))).core.toHealing.toFG := by
        intro heq
        apply hrootQ
        rw [← heq]
        exact Block.preceq_self _
      change (!decide (Q.erase = _) && Block.preceq Q.erase _) = true
      rw [Bool.and_eq_true]
      exact ⟨by simp only [hne, decide_false, Bool.not_false], h⟩








/-- The carrier record at one round, endpoint = the round's own opening
proposal, floor = the previous round's. -/
theorem movingChainAtCarrierFor_atPreviousOpening
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {q0 r : Round}
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ r)
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    (hprev : S.E.proposer (S.hc.opening_slot (r - 1)) ∈ rho.honest)
    (hnl : ¬ LostRoundAt S rho r)
    {Q P : NamedBlock V}
    (hQ : proposedBlockAt S rho (S.hc.opening_slot (r - 1)) = some Q)
    (hP : proposedBlockAt S rho (S.hc.opening_slot r) = some P)
    (hband : ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v (S.a r)).h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg P).h)
    (hband1 : ∀ P1 : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1 →
      ∀ v ∈ rho.honest,
        (rho.storeBeforeTime S v (S.a r)).core.h_max - 1 ≤
          (Protocol.derive_named S.E S.cfg P1).h)
    (hband2 : ∀ P1 : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1 →
      ∀ v ∈ rho.honest,
        (rho.storeBeforeTime S v
            (Protocol.proposal_time S.E
              (S.hc.opening_slot r + 2))).core.h_max - 1 ≤
          (Protocol.derive_named S.E S.cfg P1).h)
    (hheightHistory : CanonicalHeightSourceHistoryAt S rho q0 r P)
    (htargetHistory : CanonicalTargetHistoryAt S rho q0 r P)
    (htimeoutHistory : CanonicalTimeoutHistoryAt S rho q0 r P) :
    MovingChainAtCarrierFor S rho q0 r Q.erase P.erase := by
  obtain ⟨P1, hP1⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot r + 1)
  refine {
    endpointBelowOpening := w4cr_endpointBelowOpening S hP
    carriersBelowEndpoint := w4cr_carriersBelowEndpoint S adm hcom hbelow hrec
      hdelay hpost hr hcarrier hhor hP
    batchComplete := w4cr_batchComplete_of_notLost S adm hcom hbelow hrec hdelay
      hpost hr hhor hnl
    roundFloor := Or.inr (w4cr_roundFloorFields_atPreviousOpening S adm hcom
      hbelow hrec hdelay hpost hr hcarrier hhor hprev hnl hQ hP hband)
    anchorsBelowEndpoint := w4cr_anchorsBelowEndpoint_current S adm hcom hbelow hrec
      hdelay hpost hr hcarrier hhor hP
    namedAnchorsBelowEndpoint := w4cr_anchorsBelowEndpoint S adm hcom hbelow hrec
      hdelay hpost hr hcarrier hhor hP
    floorActiveAtPlusTwoProposal := w4cr_floorActive_atPreviousOpening S adm
      hcom hbelow hrec hdelay hpost hr hcarrier hhor hprev hQ hP1 (hband2 P1 hP1)
    plusOneCandidate := w4cr_plusOneCandidate_of_band S adm hcom hbelow hrec
      hdelay hpost hr hcarrier hhor hband1
    heightHistory := ?_
    targetHistory := ?_
    timeoutHistory := ?_ }
  · intro Z hZ
    rw [← Option.some.inj (hP.symm.trans hZ)]
    exact hheightHistory
  · intro Z hZ
    rw [← Option.some.inj (hP.symm.trans hZ)]
    exact htargetHistory
  · intro Z hZ
    rw [← Option.some.inj (hP.symm.trans hZ)]
    exact htimeoutHistory





/-- From the round action's horizon, the opening slot's support cutoff. -/
theorem w4cr_openingCutoffHorizon_of_action
    (S : Setup V) {rho : Run V} {r : Round} (hhor : S.a r ≤ rho.horizon) :
    Protocol.vote_time S.E (S.hc.opening_slot r) + S.E.Δ ≤ rho.horizon := by
  rw [Proofs.Optimistic.vote_time_add_delta]
  refine (support_cutoff_le_confirmation_time S.E (S.hc.opening_slot r)).trans ?_
  rw [← w4cr_action_eq_confirmation S r]
  exact hhor




/-- **The two carrier-window facts at one action round.** The first component
is the corresponding branch's selected-G2 relation, and the second is its domain-horizon
fact. Both are stated at the same prepared action read and use only the
full-participation fields already carried by the record route. -/
theorem w4cr_carrierWindowFacts_of_action
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r : Round}
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 1 ≤ r)
    (hhor : S.a r ≤ rho.horizon) :
    (∀ v ∈ rho.honest, ∀ A : Block V,
      PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r = some A →
      ∃ u ∈ rho.honest, Block.Preceq A (actionSGBlockAt S rho u (r - 1))) ∧
      DecoupledConsensusModel.Protocol.domain S.E S.hc r DecoupledConsensusModel.Protocol.Phase.g2 ≤ rho.horizon := by
  have hdom := w4uDomainG2_le_horizon_of_action S hhor
  exact ⟨w4uSelectedG2_preceq_honestPreviousCarrier_atRound S adm hcom hbelow
    hrec hdelay hpost hr hdom, hdom⟩

#print axioms w4cr_carrierWindowFacts_of_action

/-- **The prepared FG source below a later honest head at one guarded round.**
This is the body of `w4PreparedFgSource_preceq_laterVoterHead_of_pin`, with
the invalid all-round selected-G2 pin replaced by the carrier-window facts
returned above. -/
theorem w4cr_preparedFgSource_preceq_laterVoterHead_of_carrierWindow
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r : Round} (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ r)
    {d : Slot} (hd : S.hc.opening_slot r + 1 ≤ d)
    (hhor : Protocol.vote_time S.E d + S.E.Δ ≤ rho.horizon)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {Q B : Block V}
    (hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r = some Q)
    (hsource : actionFGSource S (actionStoreAt S rho v r) = some B)
    (hwindow :
      (∀ A : Block V,
        PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r = some A →
        ∃ u ∈ rho.honest, Block.Preceq A (actionSGBlockAt S rho u (r - 1))) ∧
      DecoupledConsensusModel.Protocol.domain S.E S.hc r DecoupledConsensusModel.Protocol.Phase.g2 ≤ rho.horizon) :
    Block.Preceq B (voterHeadAt S rho w d) := by
  have hsourceHor : S.a r ≤ rho.horizon := by
    calc
      S.a r = Protocol.vote_time S.E (S.hc.opening_slot r + 1) + S.E.Δ := by
        rw [vote_time_succ_add_delta_eq_confirmation_time,
          opening_confirmation_time_eq_action]
      _ ≤ Protocol.vote_time S.E d + S.E.Δ :=
        Int.add_le_add_right (vote_time_mono_slots S.E hd) _
      _ ≤ rho.horizon := hhor
  have hdhor : Protocol.vote_time S.E d ≤ rho.horizon :=
    (Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hhor
  have hslot : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 1 + 1) + 1 ≤
      S.hc.opening_slot r :=
    Nat.succ_le_of_lt (Nat.mul_lt_mul_of_pos_right
      (show fgSafetyProgressDeadline S rho rGST gap delayExtra + 1 + 1 < r
        from hr)
      (Nat.zero_lt_of_lt S.hc.R_ge_two))
  rcases actionFGSource_genuineClear_or_selectedG2_named S rho v r hQ hsource
    with ⟨C, hC, _, _, _, hBC⟩ | hBQ
  · exact Block.preceq_trans hBC
      (genuineConfirmationWith_preceq_laterVoterHeads_after_GST S adm hcom
        hbelow hrec hdelay hpost (Nat.le_refl _) hslot
        (by simpa only [opening_confirmation_time_eq_action] using hsourceHor)
        hv hC d hd hdhor w hw)
  · obtain ⟨u, hu, hAu⟩ := hwindow.1 Q hQ
    rw [hBQ]
    apply Block.preceq_trans hAu
    have hprev2 : r - 2 + 1 = r - 1 := by
      have hr3 : 3 ≤ r := (Nat.le_add_left 3 _).trans hr
      have hrpos : 2 ≤ r := (by decide : 2 ≤ 3).trans hr3
      change r - (1 + 1) + 1 = r - 1
      rw [← Nat.sub_sub]
      exact Nat.sub_add_cancel (Nat.le_sub_of_add_le hrpos)
    have hprevSlot : S.hc.opening_slot (r - 1) + 1 ≤ d :=
      (Nat.add_le_add_right
        (Nat.mul_le_mul_right S.hc.R (Nat.sub_le r 1)) 1).trans hd
    simpa only [hprev2] using actionSGBlock_preceq_voterHeadAt_after_GST
      S adm hcom hbelow hrec hdelay hpost (c := r - 2)
        (Nat.le_sub_of_add_le ((Nat.le_succ (_ + 2)).trans hr))
        (by simpa only [hprev2] using hprevSlot) hhor hu hw

#print axioms w4cr_preparedFgSource_preceq_laterVoterHead_of_carrierWindow

/-- **The named height-source history at a later honest head from guarded
carrier windows.** This is an additive prepared-contract twin of
`canonicalHeightSourceHistoryAt_laterHead_after_SG_healing_named`; unlike the
older export, its selected-G2 input is requested only at the round being
processed, after the deadline and inside the horizon. -/
theorem w4cr_canonicalHeightSourceHistoryAt_laterHead_after_SG_healing_named_of_carrierWindows
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {q0 r : Round}
    (hq0 : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ q0)
    {d : Slot} (hd : S.hc.opening_slot (r - 1) + 1 ≤ d)
    (hhor : Protocol.vote_time S.E d + S.E.Δ ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest)
    {P : NamedBlock V} (hPrun : RunBlock S rho P)
    (hP : P.erase = voterHeadAt S rho w d) :
    CanonicalHeightSourceHistoryAt S rho q0 r P := by
  intro k hk hkr v hv height hrow
  have hkd : S.hc.opening_slot k + 1 ≤ d :=
    (Nat.add_le_add_right (Nat.mul_le_mul_right S.hc.R
      (Nat.le_sub_one_of_lt hkr)) 1).trans hd
  obtain ⟨Q, hsource, hmem, hheight⟩ := honestRow_height_le_source S adm hv hrow
  have hQbodyPre : Q ∈ (rho.stateBeforeTime S (S.a k) v).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hmem
  obtain ⟨N, hN, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted (S.a k)
  have hQrun : RunBlock S rho Q := by
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i := N)
    simpa only [hN] using hQbodyPre
  refine ⟨Q, hsource, hQrun, ?_, hheight⟩
  have hsourceStore : actionFGSource S (actionStoreAt S rho v k) =
      some Q.erase := hsource
  obtain ⟨A, hA⟩ := w4NodeQ2_of_actionFGSource S rho v k hsourceStore
  have hsourceHor : S.a k ≤ rho.horizon := by
    calc
      S.a k = Protocol.vote_time S.E (S.hc.opening_slot k + 1) + S.E.Δ := by
        rw [vote_time_succ_add_delta_eq_confirmation_time,
          opening_confirmation_time_eq_action]
      _ ≤ Protocol.vote_time S.E d + S.E.Δ :=
        Int.add_le_add_right (vote_time_mono_slots S.E hkd) _
      _ ≤ rho.horizon := hhor
  have hguard : fgSafetyProgressDeadline S rho rGST gap delayExtra + 1 ≤ k :=
    (Nat.add_le_add_left (by decide : (1 : Nat) ≤ 3) _).trans (hq0.trans hk)
  have hwindow := w4cr_carrierWindowFacts_of_action S adm hcom hbelow hrec
    hdelay hpost hguard hsourceHor
  have herase : Block.Preceq Q.erase P.erase := by
    rw [hP]
    exact w4cr_preparedFgSource_preceq_laterVoterHead_of_carrierWindow S adm
      hcom hbelow hrec hdelay hpost (hq0.trans hk) hkd hhor hv hw hA
      hsourceStore ⟨hwindow.1 v hv, hwindow.2⟩
  exact namedPreceq_of_runBlock_erase_preceq adm hQrun hPrun herase

#print axioms w4cr_canonicalHeightSourceHistoryAt_laterHead_after_SG_healing_named_of_carrierWindows

/-- **The height history at a carrier round, bounded by its own opening
proposal** — the record's field, with the selected-G2 and node-Q2 obligations
closed by the guarded carrier-window producers. -/
theorem w4cr_heightHistory_of_pins
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {q0 r : Round}
    (hq0 : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ q0)
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ r)
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot r) = some P) :
    CanonicalHeightSourceHistoryAt S rho q0 r P := by
  obtain ⟨w, hw⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
  have hrpos : 0 < r :=
    Nat.lt_of_lt_of_le (by decide : 0 < 3) (w4cr_three_le hr)
  have hr2 : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ r :=
    Nat.le_trans (Nat.add_le_add_left (by decide : (2 : Nat) ≤ 3) _) hr
  exact w4cr_canonicalHeightSourceHistoryAt_laterHead_after_SG_healing_named_of_carrierWindows
    (delayExtra := delayExtra) S adm hcom hbelow hrec hdelay hpost hq0
    (w4cr_prevOpening_succ_le S hrpos) (w4cr_openingCutoffHorizon S hhor) hw
    (w4cr_openingProposal_runBlock S adm hrpos hcarrier hhor hP)
    ((w4cr_openingHeads S adm hcom hbelow hrec hdelay hpost hr2 hcarrier hhor
      hP w hw).symm)

/-- **The target history**, pin-free from the height history. -/
theorem w4cr_targetHistory_of_heightHistory
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q0 r : Round} {P : NamedBlock V}
    (hheight : CanonicalHeightSourceHistoryAt S rho q0 r P) :
    CanonicalTargetHistoryAt S rho q0 r P :=
  canonicalTargetHistoryAt_of_heightHistory S adm hheight

/-! The following private helper is copied from the private
`namedTimeoutRow_cases_handoffExport` at
`HealingSurface/MovingChainHandoffExportsRun.lean:893`. The original is not
available across module boundaries, so the record leaf keeps a prefixed twin.
-/
private theorem w4cr_namedTimeoutRow_cases_handoffExport
    (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (st : Protocol.HealingStore V) (record : Protocol.NamedRecord)
    {h : Height} {X : BlockId}
    (hpre : record.legacy.timeout h = false)
    (hp : (Protocol.NamedActions.round_action_with contract E hc nd st record).2.height_pair =
      NamedHeightPair.vote h X true) :
    ∃ (Q : Block V) (T : BlockId),
      Protocol.fg_source_with contract E hc st (hc.round_of st.s)
          (Protocol.grade2_block_with contract E hc st (hc.round_of st.s)) = some Q ∧
        (st.σ Q).h = h ∧ (st.σ Q).T_h.root = T ∧
        ((st.σ Q).nj = true ∨
          ∃ recorded : BlockId, record.legacy.target h = some recorded ∧
            recorded ≠ T) := by
  have herase := Proofs.NamedActions.round_action_row_erasure
    contract E hc nd st record
  have hlegacy :
      (Protocol.round_action_with contract E hc nd st record.legacy).2.height_pair =
        HeightPair.timeout h := by
    rw [← herase]
    show (Protocol.NamedActions.round_action_with contract E hc nd st
      record).2.height_pair.erase = HeightPair.timeout h
    rw [hp]
    rfl
  have hpairEq :
      (Protocol.round_action_with contract E hc nd st record.legacy).2.height_pair =
        Protocol.height_pair record.legacy
          ((Protocol.fg_source_with contract E hc st (hc.round_of st.s)
            (Protocol.grade2_block_with contract E hc st (hc.round_of st.s))).map
              (fun q => ((st.σ q).h, (st.σ q).T_h.root, (st.σ q).nj)))
          (Protocol.round_action_with contract E hc nd st record.legacy).2.finality_pair := rfl
  rw [hpairEq] at hlegacy
  obtain ⟨T, nu, hfields, hcase⟩ := height_pair_timeout_cases hpre hlegacy
  obtain ⟨Q, hQ, hvalues⟩ := Option.map_eq_some_iff.mp hfields
  refine ⟨Q, T, hQ, congrArg Prod.fst hvalues,
    congrArg (fun x : Height × BlockId × Bool => x.2.1) hvalues, ?_⟩
  rcases hcase with hnu | hrec
  · exact Or.inl
      ((congrArg (fun x : Height × BlockId × Bool => x.2.2) hvalues).trans hnu)
  · exact Or.inr hrec

/-- **Timeout provenance from the named height history.** This is an additive
prepared-contract restatement of the existing height-history closer. Its
proof follows the pre-rewrite emission-to-source route, while retaining the
named `derive_named` and prepared action objects. The conflicting reused
target branch is impossible because the target history and the timeout
source have the same height and finality root. -/
theorem w4cr_timeoutHistory_of_heightHistory
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q0 r : Round} {P : NamedBlock V}
    (hheightHistory : CanonicalHeightSourceHistoryAt S rho q0 r P) :
    CanonicalTimeoutHistoryAt S rho q0 r P := by
  intro v hv hh habove hrow
  obtain ⟨N, hN, hbefore⟩ :=
    Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.a r)
  rw [hN] at hrow
  obtain ⟨j, t, hjN, hjev, hfalse, a, hmem, hhp⟩ :=
    stateBefore_timeout_own_emission S rho v N hrow
  have hemits : rho.emits S v (Object.attest a) t := ⟨j, hjev, hmem⟩
  obtain ⟨-, ht⟩ := Proofs.Optimistic.emits_attest_shape S hemits
  have htick : Event.tick v t ∈ rho.events := List.mem_of_getElem? hjev
  have hhorRound : S.a a.round ≤ rho.horizon := by
    have hle := (adm.in_horizon _ htick).2
    rw [ht] at hle
    exact hle
  have hexact := honest_emits_exact_actionAttestationAt
    S adm hv a.round hhorRound
  have haEq : a = actionAttestationAt S rho v a.round := by
    refine Proofs.Optimistic.emits_attest_unique S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      hemits hexact ?_
    exact (actionAttestationAt_shape S rho v a.round).2.1.symm
  have hstateEq : rho.stateBefore S j v = rho.stateBeforeTime S t v :=
    Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hjev
  have htAction : t = S.a a.round := by rw [ht]
  have hfalseTime :
      (rho.stateBeforeTime S (S.a a.round) v).Λ.timeout hh = false := by
    rw [← htAction, ← hstateEq]
    exact hfalse
  have hrowAction :
      (actionAttestationAt S rho v a.round).height_pair.erase =
        HeightPair.timeout hh := by
    rw [← haEq]
    exact hhp
  have hheight :
      (actionAttestationAt S rho v a.round).height_pair.erase.height? = some hh := by
    rw [hrowAction]
    rfl
  have hq0 : q0 < a.round :=
    honestRow_after_frontier S adm hv habove hheight
  have hlt : a.round < r := by
    have hbeforeT : t < S.a r := hbefore j (Event.tick v t) hjN hjev
    rw [ht] at hbeforeT
    exact (action_strictMono S).lt_iff_lt.mp hbeforeT
  obtain ⟨Q, hsource, hrun, hpreceq, hQheight⟩ :=
    hheightHistory a.round (Nat.le_of_lt hq0) hlt v hv hh hheight
  refine ⟨Q, hrun, hpreceq, hQheight, ?_⟩
  generalize hp : (actionAttestationAt S rho v a.round).height_pair = pair
    at hrowAction
  cases pair with
  | empty => simp [hp, NamedHeightPair.erase] at hrowAction
  | vote h' entry timeout =>
      cases htimeout : timeout with
      | false => simp [hp, htimeout, NamedHeightPair.erase] at hrowAction
      | true =>
        have hh' : h' = hh := by
          simpa [hp, htimeout, NamedHeightPair.erase] using hrowAction
        subst h'
        have hpairTimeout : (actionAttestationAt S rho v a.round).height_pair =
            NamedHeightPair.vote hh entry true := by simpa [hp, htimeout]
        obtain ⟨Cfg, T, hCfg, hCfgHeight, hCfgRoot, hcase⟩ :=
          w4cr_namedTimeoutRow_cases_handoffExport
            (NamedProfile.gradeContract
              (actionReadAt S rho v a.round).cache)
            S.E S.hc (S.node v)
            (actionReadAt S rho v a.round).st.core.toHealing
            (actionReadAt S rho v a.round).record hfalseTime hpairTimeout
        have hsourceCfg :
            actionFGSource S (actionReadAt S rho v a.round) = some Cfg := by
          simpa only [actionFGSource,
            actionStoreAt, actionReadAt,
            NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
            NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
            NamedRun.stateBeforeTime] using hCfg
        have hCfgQ : Cfg = Q.erase :=
          Option.some.inj (hsourceCfg.symm.trans hsource)
        obtain ⟨C, hCmem, hCerase, hCderive, -⟩ :=
          NamedActionSources.action_witness S rho v a.round Cfg hsourceCfg
        have hCrun : RunBlock S rho C := by
          have hCmemPre : C ∈
              (rho.stateBeforeTime S (S.a a.round) v).st.bodies := by
            simpa only [actionStoreAt, actionReadAt,
              NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
              NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
              NamedRun.stateBeforeTime] using hCmem
          obtain ⟨N', hN', -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
            adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted (S.a a.round)
          apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i := N')
          simpa only [hN'] using hCmemPre
        have hroots : C.root = Q.root := by
          rw [← Proofs.NamedWire.erase_root C, ← Proofs.NamedWire.erase_root Q,
            hCerase, hCfgQ]
        have hCQ := adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
          C Q hCrun hrun C Q
          (Or.inl (Proofs.NamedAncestry.named_self C))
          (Or.inr (Proofs.NamedAncestry.named_self Q)) hroots
        have hderiveQ :
            (actionReadAt S rho v a.round).st.core.σ Q.erase =
              Protocol.derive_named S.E S.cfg Q := by
          rw [← hCfgQ, hCderive, hCQ]
        have hCheight :
            (Protocol.derive_named S.E S.cfg C).h = hh := by
          rw [← hCderive]
          simpa only [Protocol.Store.toHealing] using hCfgHeight
        have hCroot :
            (Protocol.derive_named S.E S.cfg C).T_h.root = T := by
          rw [← hCderive]
          simpa only [Protocol.Store.toHealing] using hCfgRoot
        rcases hcase with hnj | ⟨recorded, htarget, hne⟩
        · rw [← hderiveQ]
          simpa only [hCfgQ] using hnj
        · exfalso
          have hrowTargetAtRead :
              (rho.stateBeforeTime S (S.a r) v).Λ.target hh = some recorded := by
            rw [hN]
            refine stateBefore_target_mono S rho v N (Nat.le_of_lt hjN) ?_
            rw [hstateEq, ht, ← show
              (actionReadAt S rho v a.round).record =
                (rho.stateBeforeTime S (S.a a.round) v).Λ from rfl]
            exact htarget
          obtain ⟨Q1, hrun1, hpreceq1, hQ1height, hQ1root⟩ :=
            canonicalTargetHistoryAt_of_heightHistory S adm hheightHistory
              v hv hh recorded habove hrowTargetAtRead
          have hheightEq :
              (Protocol.derive_named S.E S.cfg Q1).h =
                (Protocol.derive_named S.E S.cfg C).h := by
            rw [hQ1height, hCheight]
          have hCP : NamedBlock.Preceq C P := by
            simpa only [hCQ] using hpreceq
          have hQ1P : Block.Preceq Q1.erase P.erase :=
            Proofs.NamedWire.erase_preceq hpreceq1
          have hCPraw : Block.Preceq C.erase P.erase :=
            Proofs.NamedWire.erase_preceq hCP
          have hcompat : Block.compatible Q1.erase C.erase = true :=
            Block.compatible_of_preceq_common hQ1P hCPraw
          have hcompare : Block.Preceq Q1.erase C.erase ∨
              Block.Preceq C.erase Q1.erase := by
            simpa only [Block.compatible, Bool.or_eq_true] using hcompat
          have hTeq :
              (Protocol.derive_named S.E S.cfg Q1).T_h =
                (Protocol.derive_named S.E S.cfg C).T_h := by
            rcases hcompare with hle | hle
            · exact Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg
                (Protocol.namedPreceq_of_runBlock_erase_preceq
                  adm hrun1 hCrun hle) hheightEq
            · exact (Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg
                (Protocol.namedPreceq_of_runBlock_erase_preceq
                  adm hCrun hrun1 hle) hheightEq.symm).symm
          exact hne (hQ1root.symm.trans
            ((congrArg (fun B : Block V => B.root) hTeq).trans
              hCroot))

#print axioms w4cr_timeoutHistory_of_heightHistory










/-- The opening vote instant of any post-deadline round is after GST. -/
theorem w4cr_postOpeningVote_atRound
    (S : Setup V) {rho : Run V} {rGST gap : Round}
    (hpost : S.E.t_GST ≤ S.a rGST) {m : Round}
    (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m) :
    S.E.t_GST ≤ Protocol.vote_time S.E (S.hc.opening_slot m) := by
  have hmpos : 0 < m := Nat.lt_of_lt_of_le (by decide : 0 < 2) (w4cr_two_le hm)
  refine hpost.trans (((action_strictMono S).monotone
    ((w4cr_gst_le_deadline S rho rGST gap delayExtra).trans
      (w4cr_deadline_le_pred hm))).trans ?_)
  exact le_trans (w4cr_action_lt_openingProposal S
    (Nat.sub_lt hmpos Nat.one_pos)).le
    (proposal_time_lt_vote_time S.E (S.hc.opening_slot m)).le

/-- Every honest head at a post-deadline honest opening IS that proposal. -/
theorem w4cr_openingHeads_atRound
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {m : Round}
    (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m)
    (hopening : S.E.proposer (S.hc.opening_slot m) ∈ rho.honest)
    (hhorA : S.a m ≤ rho.horizon)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot m) = some P) :
    ∀ v ∈ rho.honest,
      voterHeadAt S rho v (S.hc.opening_slot m) = P.erase :=
  honestProposal_voterHeadAt_eq_after_SG_healing_named_of_openingProposer
    (delayExtra := delayExtra) S adm hcom hbelow hrec hdelay hpost hm
    ((vote_time_le_confirmation_time S.E (S.hc.opening_slot m)).trans
      (by rw [← w4cr_action_eq_confirmation S m]; exact hhorA)) hopening hP

/-- That slot's honest vote cone sits above the proposal. -/
theorem w4cr_openingCone_atRound
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {m : Round}
    (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m)
    (hopening : S.E.proposer (S.hc.opening_slot m) ∈ rho.honest)
    (hhorA : S.a m ≤ rho.horizon)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot m) = some P) :
    NamedHonestVotesCone S rho (S.hc.opening_slot m)
      (fun X => Block.Preceq P.erase X) := by
  have hopenPos : 0 < S.hc.opening_slot m :=
    Nat.mul_pos (Nat.lt_of_lt_of_le (by decide : 0 < 2) (w4cr_two_le hm))
      (Nat.zero_lt_of_lt S.hc.R_ge_two)
  have hsucc : S.hc.opening_slot m - 1 + 1 = S.hc.opening_slot m :=
    Nat.succ_pred_eq_of_pos hopenPos
  have hres := honestProposal_slotVoteCone_after_SG_healing_named
    (delayExtra := delayExtra) S adm hcom hbelow hrec hdelay hpost
    (s := S.hc.opening_slot m - 1)
    (by rw [hsucc]; exact Nat.mul_le_mul_right S.hc.R hm)
    (by
      rw [hsucc]
      exact (vote_time_le_confirmation_time S.E (S.hc.opening_slot m)).trans
        (by rw [← w4cr_action_eq_confirmation S m]; exact hhorA))
    (by rw [hsucc]; exact hopening) (by rw [hsucc]; exact hP)
  rw [hsucc] at hres
  exact hres

/-- Every honest FG root at that round's action read is below the proposal. -/
theorem w4cr_fgRoot_preceq_openingProposal_atRound
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {m : Round}
    (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m)
    (hopening : S.E.proposer (S.hc.opening_slot m) ∈ rho.honest)
    (hhorA : S.a m ≤ rho.horizon)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot m) = some P) :
    ∀ u ∈ rho.honest,
      Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S u (S.a m)).toHealing.toFG) P.erase := by
  intro u hu
  obtain ⟨w, hw⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
  have hdeadlineLt : fgSafetyProgressDeadline S rho rGST gap delayExtra < m :=
    lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 2)) hm
  have hres := fgRoot_preceq_previousHead_through_confirmation_after_GST
    (delayExtra := delayExtra) S adm hcom hbelow hrec hdelay hpost
    (read := S.a m) ((action_strictMono S).monotone hdeadlineLt.le) hhorA
    (s := S.hc.opening_slot m)
    (Nat.le_of_succ_le (w4cr_openingSlot_two_le S hdeadlineLt))
    (le_of_eq (w4cr_action_eq_confirmation S m))
    (w4cr_openingCutoffHorizon_of_action S hhorA) hu hw
  have hhead : voteDutyHead S rho w (S.hc.opening_slot m) = P.erase :=
    w4cr_openingHeads_atRound S adm hcom hbelow hrec hdelay hpost hm hopening
      hhorA hP w hw
  rw [hhead] at hres
  exact hres

/-- The proposal is a run block and sits in every honest reader's bodies at
that round's action read. -/
theorem w4cr_openingProposal_mem_bodies_atRound
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {m : Round}
    (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m)
    (hopening : S.E.proposer (S.hc.opening_slot m) ∈ rho.honest)
    (hhorA : S.a m ≤ rho.horizon)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot m) = some P) :
    ∀ v ∈ rho.honest, P ∈ (rho.storeBeforeTime S v (S.a m)).bodies := by
  intro v hv
  have hmpos : 0 < m := Nat.lt_of_lt_of_le (by decide : 0 < 2) (w4cr_two_le hm)
  have hcone := w4cr_openingCone_atRound S adm hcom hbelow hrec hdelay hpost hm
    hopening hhorA hP
  have hroot := w4cr_fgRoot_preceq_openingProposal_atRound S adm hcom hbelow
    hrec hdelay hpost hm hopening hhorA hP v hv
  have hcut := w4cr_openingCutoff_le_action S m
  have havailable := honestHeadsAvailableBefore_of_postHealingCone_at
    S adm.toNamedAdmissibleCore hv
    (w4cr_postOpeningVote_atRound (delayExtra := delayExtra) S hpost hm)
    (hcut.trans hhorA) hcut hroot hcone
  have hmemT := (storeBeforeTime_mem_stamp_of_cone S adm hcom havailable hcut
    hcone (Block.preceq_self P.erase)).1
  have hrun : RunBlock S rho P :=
    proposedBlock_runBlock S adm
      (Nat.mul_pos hmpos (Nat.zero_lt_of_lt S.hc.R_ge_two)) hopening
      ((w4cr_openingProposal_le_action S m).trans hhorA) hP
  exact w4cr_mem_bodies_of_mem_T S adm hv hrun hmemT



omit [DecidableEq V] [Fintype V] in
/-- Strict prefixes grow with the cut time. -/
private theorem w4cr_filter_lt_length_mono (rho : Run V) {t t' : Time}
    (h : t ≤ t') :
    (rho.events.filter (fun e => decide (e.time < t))).length ≤
      (rho.events.filter (fun e => decide (e.time < t'))).length :=
  (List.monotone_filter_right rho.events
    (fun e he => by
      simp only [decide_eq_true_eq] at he ⊢
      exact lt_of_lt_of_le he h)).length_le

/-- Named bodies are retained as the read time grows. -/
theorem w4cr_bodies_mono_time
    (S : Setup V) {rho : Run V} (adm : Admissible S rho) (v : V)
    {t t' : Time} (h : t ≤ t') :
    (rho.storeBeforeTime S v t).bodies ⊆
      (rho.storeBeforeTime S v t').bodies := by
  have het := congrFun
    (Proofs.Optimistic.stateBeforeTime_eq_take S adm.toNamedScheduleWellFormed t) v
  have het' := congrFun
    (Proofs.Optimistic.stateBeforeTime_eq_take S adm.toNamedScheduleWellFormed t') v
  simp only [Run.storeBeforeTime, het, het']
  exact NamedBodyRetention.stateBefore_bodies_mono S rho v
    (w4cr_filter_lt_length_mono rho h)


/-- **The previous round's opening proposal is in every honest reader's bodies
at the round's G2-domain read** — the corresponding branch's `hmemDomain`. -/
theorem w4cr_prevOpening_mem_bodies_atDomain
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r : Round}
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    (hprev : S.E.proposer (S.hc.opening_slot (r - 1)) ∈ rho.honest)
    {Q : NamedBlock V}
    (hQ : proposedBlockAt S rho (S.hc.opening_slot (r - 1)) = some Q) :
    ∀ w ∈ rho.honest,
      Q ∈ (rho.storeBeforeTime S w
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)).bodies := by
  intro w hw
  have hrpos : 0 < r :=
    Nat.lt_of_lt_of_le (by decide : 0 < 3) (w4cr_three_le hr)
  have hhorPrev : S.a (r - 1) ≤ rho.horizon :=
    ((action_strictMono S).monotone (Nat.sub_le r 1)).trans
      (w4cr_actionHorizon S hhor)
  exact w4cr_bodies_mono_time S adm w (action_pred_le_domain_g2 S hrpos)
    (w4cr_openingProposal_mem_bodies_atRound S adm hcom hbelow hrec hdelay hpost
      (w4cr_deadline_le_sub_one hr) hprev hhorPrev hQ w hw)



omit [Fintype V] in
/-- A named ancestor other than the block itself is an ancestor of its named
parent. -/
theorem w4cr_namedPreceq_parent_of_ne
    {A B : NamedBlock V} (hAB : NamedBlock.Preceq A B) (hne : A ≠ B) :
    NamedBlock.Preceq A B.parent := by
  cases B with
  | genesis =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq,
        decide_eq_true_eq] at hAB
      exact absurd hAB hne
  | node p s root votes support rows proposer =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hparent
      · exact absurd rfl hne
      · exact hparent



/-- **The  floor is below the NAMED parent of the round's own opening
proposal.** The concrete instance the corresponding branch can use at a carrier
round: the previous round's opening proposal is a named ancestor of this
round's proposal and is not that proposal, since their slots differ. -/
theorem w4cr_previousOpening_namedPreceq_openingParent
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r : Round}
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ r)
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    (hprev : S.E.proposer (S.hc.opening_slot (r - 1)) ∈ rho.honest)
    {Q P : NamedBlock V}
    (hQ : proposedBlockAt S rho (S.hc.opening_slot (r - 1)) = some Q)
    (hP : proposedBlockAt S rho (S.hc.opening_slot r) = some P) :
    NamedBlock.Preceq Q P.parent := by
  have hrpos : 0 < r :=
    Nat.lt_of_lt_of_le (by decide : 0 < 3) (w4cr_three_le hr)
  have hhorPrev : S.a (r - 1) ≤ rho.horizon :=
    ((action_strictMono S).monotone (Nat.sub_le r 1)).trans
      (w4cr_actionHorizon S hhor)
  have hQrun : RunBlock S rho Q :=
    proposedBlock_runBlock S adm
      (Nat.mul_pos (Nat.lt_of_lt_of_le (by decide : 0 < 2)
        (w4cr_two_le (w4cr_deadline_le_sub_one hr)))
        (Nat.zero_lt_of_lt S.hc.R_ge_two)) hprev
      ((w4cr_openingProposal_le_action S (r - 1)).trans hhorPrev) hQ
  have hPrun : RunBlock S rho P :=
    w4cr_openingProposal_runBlock S adm hrpos hcarrier hhor hP
  have hne : Q ≠ P := by
    intro heq
    have hQs : Q.slot = S.hc.opening_slot (r - 1) :=
      proposedBlockAt_slot S rho (S.hc.opening_slot (r - 1)) hQ
    have hPs : P.slot = S.hc.opening_slot r :=
      proposedBlockAt_slot S rho (S.hc.opening_slot r) hP
    rw [heq, hPs] at hQs
    exact absurd hQs
      (Nat.ne_of_lt (Nat.lt_of_lt_of_le
        (Nat.lt_succ_of_le (Nat.le_refl _))
        (w4cr_prevOpening_succ_le S hrpos))).symm
  exact w4cr_namedPreceq_parent_of_ne
    (Protocol.namedPreceq_of_runBlock_erase_preceq adm hQrun hPrun
      (w4cr_previousOpening_preceq_opening S adm hcom hbelow hrec hdelay hpost
        hr hcarrier hhor hprev hQ hP)) hne















/-- **The frontier band at a read, from the height gates there.** -/
theorem w4cr_band_of_heightGates
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {t : Time} {P0 : NamedBlock V}
    (hgates : Protocol.PastHonestHeightGatesBelow S rho t P0)
    (hheld : ∀ v ∈ rho.honest, P0 ∈ (rho.storeBeforeTime S v t).bodies) :
    ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v t).core.h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg P0).h := by
  intro v hv
  have hcap := w4HonestFrontier_le_succ_of_heightGates S adm hcom
    (AlignedRoundLemmas.honestQuorum_of_belowOneThird hbelow) hgates
    (fun u hu => by simpa only [Run.storeBeforeTime] using hheld u hu)
  have hsup : (rho.storeBeforeTime S v t).core.h_max ≤
      honestHMaxBeforeIndex S rho (strictEventIndex rho t) := by
    rw [storeBeforeTime_eq_stateBefore_strictEventIndex S
      adm.toNamedScheduleWellFormed v t]
    simpa only [honestHMaxBeforeIndex] using
      (Finset.le_sup
        (f := fun u => (rho.stateBefore S (strictEventIndex rho t) u).st.h_max)
        hv)
  exact Nat.sub_le_iff_le_add.mpr (le_trans hsup hcap)

/-- **The past height gates at any read before the round's action**, from that
round's height history and the boundary cap. Body of
`pastHonestHeightGatesBelow_of_canonicalHeightHistory` (`W4FKGradeRun:596`)
with the G2-domain read replaced by an arbitrary `t ≤ S.a m`. -/
theorem w4cr_pastHeightGates_of_history
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q0 m : Round} {P0 : NamedBlock V} {t : Time}
    (hhist : CanonicalHeightSourceHistoryAt S rho q0 m P0)
    (hcap : honestHMaxAt S rho (S.a q0) ≤
      (Protocol.derive_named S.E S.cfg P0).h)
    (ht : t ≤ S.a m) :
    Protocol.PastHonestHeightGatesBelow S rho t P0 := by
  intro a t' haHonest hemit ht' h hrow
  have htime : t' = S.a a.round := (Proofs.Optimistic.emits_attest_shape S hemit).2
  have haEq : a = actionAttestationAt S rho a.val_index a.round :=
    emittedHonestAttestation_eq_actionAttestationAt S adm hemit
  have hrowAction :
      (actionAttestationAt S rho a.val_index a.round).height_pair.erase.height? =
        some h := by
    rw [← haEq]
    exact hrow
  have hlt : S.a a.round < S.a m := by
    rw [← htime]
    exact lt_of_lt_of_le ht' ht
  have hround : a.round < m := (action_strictMono S).lt_iff_lt.mp hlt
  by_cases habove : honestHMaxAt S rho (S.a q0) < h
  · have hq0 : q0 < a.round :=
      honestRow_after_frontier S adm haHonest habove hrowAction
    obtain ⟨Q, -, -, hQP0, hQheight⟩ :=
      hhist a.round (Nat.le_of_lt hq0) hround a.val_index haHonest h hrowAction
    calc
      h = (Protocol.derive_named S.E S.cfg Q).h := hQheight.symm
      _ ≤ (Protocol.derive_named S.E S.cfg P0).h :=
        Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hQP0
  · exact (Nat.le_of_not_gt habove).trans hcap

/-- The `+2` proposal instant precedes the NEXT round's action. -/
theorem w4cr_plusTwoProposal_le_nextAction (S : Setup V) (r : Round) :
    Protocol.proposal_time S.E (S.hc.opening_slot r + 2) ≤ S.a (r + 1) := by
  have htwo := w4cr_openingSlot_two_le S (Nat.lt_succ_self r)
  rw [w4cr_proposal_normal S.E _, w4cr_action_normal S (r + 1)]
  refine Int.mul_le_mul_of_nonneg_right ?_ (le_of_lt S.E.Δ_pos)
  have hcast : ((S.hc.opening_slot r : Slot) : Int) + 2 ≤
      ((S.hc.opening_slot (r + 1) : Slot) : Int) := by exact_mod_cast htwo
  push_cast at hcast ⊢
  omega

/-- **Every honest FG root at a read through the `+1` confirmation instant is
below the carrier's first interior proposal.** -/
theorem w4cr_fgRoot_preceq_interiorProposal
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r : Round}
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ r)
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    {P1 : NamedBlock V}
    (hP1 : proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1)
    {read : Time}
    (hread : S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) ≤ read)
    (hreadHor : read ≤ rho.horizon)
    (hnext : read ≤ Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 1)) :
    ∀ u ∈ rho.honest,
      Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S u read).toHealing.toFG) P1.erase := by
  intro u hu
  obtain ⟨w, hw⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
  have hdeadlineLt : fgSafetyProgressDeadline S rho rGST gap delayExtra < r :=
    lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 3)) hr
  have hres := fgRoot_preceq_previousHead_through_confirmation_after_GST
    (delayExtra := delayExtra) S adm hcom hbelow hrec hdelay hpost hread
    hreadHor (s := S.hc.opening_slot r + 1)
    ((Nat.le_of_succ_le (w4cr_openingSlot_two_le S hdeadlineLt)).trans
      (Nat.le_succ _))
    hnext
    (by
      rw [Proofs.Optimistic.vote_time_add_delta, w4cr_interiorCutoff_eq_action S r]
      exact w4cr_actionHorizon S hhor) hu hw
  have hhead1 : voteDutyHead S rho w (S.hc.opening_slot r + 1) = P1.erase :=
    w4cr_interiorHeads S adm hcom hbelow hrec hdelay hpost hr hcarrier hhor
      hP1 w hw
  rw [hhead1] at hres
  exact hres

/-- **The first interior proposal is in every honest reader's bodies at any
read at or after the round action and through the `+1` confirmation.** -/
theorem w4cr_interiorProposal_mem_bodies_at
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r : Round}
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ r)
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    {P1 : NamedBlock V}
    (hP1 : proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1)
    {Gamma : Time}
    (hcutGamma : S.a r ≤ Gamma)
    (hGammaHor : Gamma ≤ rho.horizon)
    (hnext : Gamma ≤ Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 1)) :
    ∀ v ∈ rho.honest, P1 ∈ (rho.storeBeforeTime S v Gamma).bodies := by
  intro v hv
  have hArhor := w4cr_actionHorizon S hhor
  have hdeadlineLt : fgSafetyProgressDeadline S rho rGST gap delayExtra < r :=
    lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 3)) hr
  have hcutEq := w4cr_interiorCutoff_eq_action S r
  have hcut : Protocol.support_cutoff S.E (S.hc.opening_slot r + 1) ≤ Gamma := by
    rw [hcutEq]; exact hcutGamma
  have hroot := w4cr_fgRoot_preceq_interiorProposal S adm hcom hbelow hrec
    hdelay hpost hr hcarrier hhor hP1
    (((action_strictMono S).monotone hdeadlineLt.le).trans hcutGamma) hGammaHor
    hnext v hv
  have hcone1 := honestProposal_slotVoteCone_after_SG_healing_named
    (delayExtra := delayExtra) S adm hcom hbelow hrec hdelay hpost
    (Nat.le_succ_of_le (Nat.mul_le_mul_right S.hc.R
      (Nat.le_trans (Nat.add_le_add_left (by decide : (2 : Nat) ≤ 3) _) hr)))
    (w4cr_interiorVoteHorizon S hhor) hcarrier.2.1 hP1
  have hpostVote1 : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot r + 1) :=
    (w4cr_postOpeningVote (delayExtra := delayExtra) S hpost hr).trans
      (Protocol.vote_time_mono_slots S.E (Nat.le_succ _))
  have havail := honestHeadsAvailableBefore_of_postHealingCone_at
    S adm.toNamedAdmissibleCore hv hpostVote1
    (by rw [hcutEq]; exact hArhor) hcut hroot hcone1
  have hmemT := (storeBeforeTime_mem_stamp_of_cone S adm hcom havail hcut
    hcone1 (Block.preceq_self P1.erase)).1
  have hP1run : RunBlock S rho P1 :=
    proposedBlock_runBlock S adm (Nat.succ_pos _) hcarrier.2.1
      ((w4cr_proposalSucc_le_action S r).trans hArhor) hP1
  exact w4cr_mem_bodies_of_mem_T S adm hv hP1run hmemT

/-- **The height history at the NEXT round, bounded by the carrier's first
interior proposal** — the reference the two `P1` bands need. -/
theorem w4cr_interiorHistory_of_pins
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {q0 r : Round}
    (hq0 : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ q0)
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ r)
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    {P1 : NamedBlock V}
    (hP1 : proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1) :
    CanonicalHeightSourceHistoryAt S rho q0 (r + 1) P1 := by
  obtain ⟨w, hw⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
  have hArhor := w4cr_actionHorizon S hhor
  refine w4cr_canonicalHeightSourceHistoryAt_laterHead_after_SG_healing_named_of_carrierWindows
    (delayExtra := delayExtra) S adm hcom hbelow hrec hdelay hpost hq0
    (d := S.hc.opening_slot r + 1) (by rw [Nat.add_sub_cancel])
    (by
      rw [Proofs.Optimistic.vote_time_add_delta, w4cr_interiorCutoff_eq_action S r]
      exact hArhor) hw
    (proposedBlock_runBlock S adm (Nat.succ_pos _) hcarrier.2.1
      ((w4cr_proposalSucc_le_action S r).trans hArhor) hP1)
    ((w4cr_interiorHeads S adm hcom hbelow hrec hdelay hpost hr hcarrier hhor
      hP1 w hw).symm)

/-! ## 17. The whole residual bundle from the caps

Putting sections 9, 10 and 16 together: at an opening carrier the entire
per-round bundle `W4OpeningCarrierResiduals` follows from the guarded
height-history producer, the named timeout closer, and ONE numeric fact per
endpoint — the boundary cap
`honestHMaxAt S rho (S.a q0) ≤ h(P0)`, which says the honest frontier at the
recovery round is no higher than the endpoint the round's own history is
referred to. -/




#print axioms w4cr_actionHorizon
#print axioms w4cr_openingCutoffHorizon
#print axioms w4cr_openingHeads
#print axioms w4cr_openingCone
#print axioms w4cr_fgRoot_preceq_openingProposal
#print axioms w4cr_endpointBelowOpening
#print axioms w4cr_carriersBelowEndpoint
#print axioms w4cr_openingCutoff_le_action
#print axioms w4cr_postOpeningVote
#print axioms w4cr_openingProposal_mem_actionRead
#print axioms w4cr_anchorsBelowEndpoint
#print axioms w4cr_mem_bodies_of_mem_T
#print axioms w4cr_openingProposal_runBlock
#print axioms w4cr_openingProposal_mem_bodies
#print axioms w4cr_proposalSucc_le_action
#print axioms w4cr_interiorCutoff_eq_action
#print axioms w4cr_plusOneCandidate_of_heads
#print axioms w4cr_batchComplete_of_cone
#print axioms w4cr_action_le_plusTwoProposal
#print axioms w4cr_plusTwoProposal_le_plusOneConfirmation
#print axioms w4cr_previousCarrier_eq_previousOpening
#print axioms w4cr_previousOpening_preceq_opening
#print axioms w4cr_previousOpening_preceq_interior
#print axioms w4cr_roundFloorFields_atPreviousOpening
#print axioms w4cr_floorActive_atPreviousOpening
#print axioms w4cr_interiorVoteHorizon
#print axioms w4cr_interiorHeads
#print axioms w4cr_previousSlotCone
#print axioms w4cr_previousSlotAvailability
#print axioms w4cr_batchComplete_of_notLost
#print axioms w4cr_plusOneCandidate_of_band
#print axioms w4cr_batchComplete_field_of_cone
#print axioms w4cr_plusOneCandidate_field_of_heads
#print axioms movingChainAtCarrierFor_atPreviousOpening
#print axioms w4cr_openingCutoffHorizon_of_action
#print axioms w4cr_heightHistory_of_pins
#print axioms w4cr_targetHistory_of_heightHistory
#print axioms w4cr_postOpeningVote_atRound
#print axioms w4cr_openingHeads_atRound
#print axioms w4cr_openingCone_atRound
#print axioms w4cr_fgRoot_preceq_openingProposal_atRound
#print axioms w4cr_openingProposal_mem_bodies_atRound
#print axioms w4cr_bodies_mono_time
#print axioms w4cr_prevOpening_mem_bodies_atDomain
#print axioms w4cr_namedPreceq_parent_of_ne
#print axioms w4cr_previousOpening_namedPreceq_openingParent
#print axioms w4cr_band_of_heightGates
#print axioms w4cr_pastHeightGates_of_history
#print axioms w4cr_plusTwoProposal_le_nextAction
#print axioms w4cr_fgRoot_preceq_interiorProposal
#print axioms w4cr_interiorProposal_mem_bodies_at
#print axioms w4cr_interiorHistory_of_pins



/-! The canonical-suffix proposal link is private in the execution suffix
leaf. Keep a prefixed local copy so this additive carrier record leaf does not
acquire that leaf's import cone. -/

private theorem w4cr_tickIndex_lt_of_time_lt_suffix
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {i j : Nat} {v w : V} {t u : Time}
    (hi : rho.events[i]? = some (Event.tick v t))
    (hj : rho.events[j]? = some (Event.tick w u))
    (htu : t < u) :
    i < j := by
  by_contra hnot
  have hji : j ≤ i := Nat.le_of_not_gt hnot
  rcases lt_or_eq_of_le hji with hji | hji
  · have hkey := Proofs.Optimistic.key_le_of_index_lt S sch hji hj hi
    have htime := Proofs.Bridges.time_le_of_key_le hkey
    simp only [Event.time] at htime
    exact (not_le_of_gt htu) htime
  · subst j
    have hevent : Event.tick v t = Event.tick w u :=
      Option.some.inj (hi.symm.trans hj)
    have htime : t = u := by
      simpa only [Event.time] using congrArg Event.time hevent
    exact (ne_of_lt htu) htime

private theorem w4cr_proposedBlock_preceq_of_canonicalSuffixFrom
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round}
    (hsuffix : CanonicalSuffixFrom S rho (healingBoundaryTime S q))
    {s u : Slot} (hs : 0 < s) (hu : 0 < u)
    (hafter : healingBoundaryTime S q < Protocol.proposal_time S.E s)
    (hpropS : S.E.proposer s ∈ rho.honest)
    (hpropU : S.E.proposer u ∈ rho.honest)
    {P Q : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P)
    (hQ : proposedBlockAt S rho u = some Q)
    (hemitS : rho.emits S (S.E.proposer s) (Object.block P)
      (Protocol.proposal_time S.E s))
    (hemitU : rho.emits S (S.E.proposer u) (Object.block Q)
      (Protocol.proposal_time S.E u))
    (htime : Protocol.proposal_time S.E s ≤
      Protocol.proposal_time S.E u) :
    Block.Preceq P.erase Q.erase := by
  by_cases heq : Protocol.proposal_time S.E s =
      Protocol.proposal_time S.E u
  · have hsu : s = u := by
      have hslot := congrArg S.E.slotOf heq
      simpa only [Proofs.Optimistic.slotOf_proposal_time] using hslot
    subst hsu
    have hPQ : P = Q := Option.some.inj (hP.symm.trans hQ)
    subst hPQ
    exact Block.preceq_self _
  · have htimeLt : Protocol.proposal_time S.E s <
        Protocol.proposal_time S.E u :=
      lt_of_le_of_ne htime heq
    rcases hsuffix with ⟨n0, End, hstart, hchain⟩
    obtain ⟨i, hi, -⟩ := hemitS
    obtain ⟨j, hj, -⟩ := hemitU
    have hobsS : HonestCanonicalObservationAtIndex S rho i 1 P.erase :=
      Protocol.proposedBlock_observationAtIndex S adm hs hpropS hi hP
    have hobsU : HonestCanonicalObservationAtIndex S rho j 1 Q.erase :=
      Protocol.proposedBlock_observationAtIndex S adm hu hpropU hj hQ
    obtain ⟨_, _, k, _, _, _, _, hk, hn0⟩ := hstart
    have hki : k < i := w4cr_tickIndex_lt_of_time_lt_suffix
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hk hi hafter
    have hni : n0 ≤ i := by
      rw [hn0]
      exact Nat.succ_le_of_lt hki
    have hij : i < j := w4cr_tickIndex_lt_of_time_lt_suffix
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hi hj htimeLt
    exact hchain.ordered i 1 P.erase j 1 Q.erase hni
      (hni.trans (Nat.le_of_lt hij))
      (by simp [ProposalChainStage]) (by simp [ProposalChainStage])
      hobsS hobsU (Or.inl hij)

/-- A selected opening carrier whose recovery frontier is below its
opening-plus-one proposal. -/
def W4CarrierCapSeed (S : Setup V) (rho : Run V) (q0 q : Round) : Prop :=
  ∃ D : NamedBlock V,
    ProposerOpeningCarrierAt S rho q ∧
    proposedBlockAt S rho (S.hc.opening_slot q + 1) = some D ∧
    healingBoundaryTime S q0 <
      Protocol.proposal_time S.E (S.hc.opening_slot q + 1) ∧
    honestHMaxAt S rho (S.a q0) <
      (Protocol.derive_named S.E S.cfg D).h

private theorem w4cr_cap_openingSlot_mono
    (S : Setup V) {p q : Round} (h : p ≤ q) :
    S.hc.opening_slot p ≤ S.hc.opening_slot q := by
  simpa only [Protocol.HealConfig.opening_slot] using
    Nat.mul_le_mul_right S.hc.R h

private theorem w4cr_cap_openingSlot_succ_le_of_lt
    (S : Setup V) {p q : Round} (h : p < q) :
    S.hc.opening_slot p + 1 ≤ S.hc.opening_slot q := by
  have hstep : S.hc.opening_slot p + 1 ≤
      S.hc.opening_slot (p + 1) := by
    simpa only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
      using Nat.add_le_add_left
        ((by decide : (1 : Nat) ≤ 2).trans S.hc.R_ge_two)
        (p * S.hc.R)
  exact hstep.trans
    (w4cr_cap_openingSlot_mono S (Nat.succ_le_iff.mpr h))

private theorem w4cr_cap_openingSlot_pos_of_pos
    (S : Setup V) {r : Round} (hr : 0 < r) :
    0 < S.hc.opening_slot r := by
  simpa only [Protocol.HealConfig.opening_slot] using
    Nat.mul_pos hr (Nat.zero_lt_of_lt S.hc.R_ge_two)

private theorem w4cr_cap_horizon_opening
    (S : Setup V) {rho : Run V} {r : Round}
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon) :
    Protocol.proposal_time S.E (S.hc.opening_slot r) ≤ rho.horizon :=
  (Protocol.proposal_time_lt_vote_time S.E _).le.trans
    ((Protocol.vote_time_mono_slots S.E
      (Nat.le_add_right _ 2)).trans
      ((Protocol.vote_time_le_confirmation_time S.E _).trans hhor))




/-- The same selected seed bounds the previous opening proposal of every
later opening carrier. This is the gate input used by the grade producer. -/
theorem w4cr_previousOpeningHeightCap_of_seed
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q0 q : Round}
    (hsuffix : CanonicalSuffixFrom S rho (healingBoundaryTime S q0))
    (hseed : W4CarrierCapSeed S rho q0 q) :
    ∀ r : Round, q + 2 < r → ProposerOpeningCarrierAt S rho r →
      Protocol.confirmation_time S.E
        (S.hc.opening_slot r + 2) ≤ rho.horizon →
      ∀ Q : NamedBlock V,
        proposedBlockAt S rho (S.hc.opening_slot (r - 1)) = some Q →
        honestHMaxAt S rho (S.a q0) ≤
          (Protocol.derive_named S.E S.cfg Q).h := by
  obtain ⟨D, hopeningQ, hD, hafterD, hcapD⟩ := hseed
  intro r hqr hopening hhor Q hQ
  have hq1r : q + 1 < r := by
    exact (Nat.lt_succ_self (q + 1)).trans hqr
  have hqpred : q < r - 1 := by
    apply Nat.lt_sub_of_add_lt
    exact hq1r
  have hDpos : 0 < S.hc.opening_slot q + 1 := Nat.zero_lt_succ _
  have hQpos : 0 < S.hc.opening_slot (r - 1) :=
    w4cr_cap_openingSlot_pos_of_pos S (Nat.zero_lt_of_lt hqpred)
  have hD_le_Q : S.hc.opening_slot q + 1 ≤
      S.hc.opening_slot (r - 1) :=
    w4cr_cap_openingSlot_succ_le_of_lt S hqpred
  have htimeD_Q : Protocol.proposal_time S.E
      (S.hc.opening_slot q + 1) ≤
      Protocol.proposal_time S.E (S.hc.opening_slot (r - 1)) :=
    Protocol.proposal_time_mono S.E hD_le_Q
  have hhorQ : Protocol.proposal_time S.E
      (S.hc.opening_slot (r - 1)) ≤ rho.horizon := by
    have hslot : S.hc.opening_slot (r - 1) ≤
        S.hc.opening_slot r :=
      w4cr_cap_openingSlot_mono S (Nat.sub_le r 1)
    exact (Protocol.proposal_time_mono S.E hslot).trans
      (w4cr_cap_horizon_opening S hhor)
  have hDhor : Protocol.proposal_time S.E
      (S.hc.opening_slot q + 1) ≤ rho.horizon :=
    htimeD_Q.trans hhorQ
  have hDhonest : S.E.proposer (S.hc.opening_slot q + 1) ∈ rho.honest :=
    hopeningQ.2.2.2.1
  have hQhonest : S.E.proposer (S.hc.opening_slot (r - 1)) ∈ rho.honest :=
    hopening.2.1
  have hDemit := Protocol.proposedBlock_emitted_of_admissible
    S adm hDpos hDhonest hDhor hD
  have hQemit := Protocol.proposedBlock_emitted_of_admissible
    S adm hQpos hQhonest hhorQ hQ
  have hD_Q_erase := w4cr_proposedBlock_preceq_of_canonicalSuffixFrom S adm
    hsuffix hDpos hQpos hafterD hDhonest hQhonest hD hQ hDemit hQemit
      htimeD_Q
  have hDrun := proposedBlockAt_blockInRun_of_admissible S
    adm.toNamedAdmissibleCore (S.hc.opening_slot q + 1) hDpos hDhonest
      hDhor hD
  have hQrun := proposedBlockAt_blockInRun_of_admissible S
    adm.toNamedAdmissibleCore (S.hc.opening_slot (r - 1)) hQpos hQhonest
      hhorQ hQ
  have hDQ : NamedBlock.Preceq D Q :=
    Protocol.namedPreceq_of_runBlock_erase_preceq adm hDrun hQrun
      hD_Q_erase
  exact hcapD.le.trans
    (Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hDQ)

#print axioms w4cr_previousOpeningHeightCap_of_seed

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
