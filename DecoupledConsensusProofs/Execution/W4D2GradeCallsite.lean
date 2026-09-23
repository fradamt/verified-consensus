module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.W4D2SourceCallsite
public import DecoupledConsensusProofs.Execution.W4CarrierFinalityField

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # D2 grade callback at its actual selected-carrier call sites
The prepared D2 body grades only two opening carriers: the carrier selected
after two height-progress gains and the later carrier selected to finalize it.
This leaf keeps the strict opening-height cap and the previous-opening gate
cap at those call sites. It does not construct a same-round cap seed at the
handoff round.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.NamedRecoveryRead
open Protocol Proofs.HealingLemmas
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The grade input at D2's two real carrier sites. The current opening cap,
The previous-opening cap used by the height gates, and non-lostness are local
facts at each invocation. -/
def W4PreparedSelectedGradeAt
    (S : Setup V) (rho : Run V) (q : Round) (extra : Nat) : Prop :=
  ∀ (r : Round), q + extra + 4 ≤ r →
    healingBoundaryTime S q <
      Protocol.proposal_time S.E (S.hc.opening_slot r) →
    ProposerOpeningCarrierAt S rho r →
    Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon →
    honestHMaxAt S rho (S.a q) < carrierOpeningHeight S rho r →
    (∀ Q : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot (r - 1)) = some Q →
      honestHMaxAt S rho (S.a q) ≤
        (Protocol.derive_named S.E S.cfg Q).h) →
    ¬ LostRoundAt S rho r →
    ∃ C End : Block V,
      MovingChainAtCarrierFor S rho q r C End ∧
      NamedGradeFormsAt S rho r C

/-- Narrowed analogue of `w4cr_sourceAt_to_actionStoreAt`. -/
theorem w4gc_sourceAt_to_actionStoreAt
    (S : Setup V) {rho : Run V} {q : Round} {extra : Nat}
    (hsourceAt : W4PreparedSelectedSourceAt S rho q extra) :
    ∀ (r : Round), q + extra + 4 ≤ r →
      ProposerOpeningCarrierAt S rho r →
      Protocol.confirmation_time S.E
        (S.hc.opening_slot r + 2) ≤ rho.horizon →
      ∀ {Pprev : NamedBlock V},
        proposedBlockAt S rho (S.hc.opening_slot (r - 1)) = some Pprev →
        S.a (r - 1) ≤ rho.horizon →
        ∀ w ∈ rho.honest, ∀ X : Block V,
          actionFGSource S (actionStoreAt S rho w (r - 1)) = some X →
            X = Pprev.erase := by
  intro r hlate hopening hhor Pprev hPprev hprevHor w hw X hX
  have hsource : actionFGSource S (actionStoreAt S rho w (r - 1)) =
      some Pprev.erase := by
    simpa only [actionStoreAt] using
      (hsourceAt r hlate hopening hhor hPprev hprevHor w hw)
  exact Option.some.inj (hX.symm.trans hsource)

private theorem w4gc_body_run
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {B : NamedBlock V}
    (hB : B ∈ (actionStoreAt S rho v r).st.bodies) :
    RunBlock S rho B := by
  have hBpre : B ∈ (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hB
  obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted (S.a r)
  apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i := n)
  simpa only [hn] using hBpre

/-- Prefixed copy of the private history extension in
`W4CarrierFinalityFieldRun.lean`. -/
private theorem w4gc_heightHistory_extend
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q r : Round} {Q : NamedBlock V}
    (hhistPrev : CanonicalHeightSourceHistoryAt S rho q (r - 1) Q)
    (_hprev : S.E.proposer (S.hc.opening_slot (r - 1)) ∈ rho.honest)
    (_hPprev : proposedBlockAt S rho (S.hc.opening_slot (r - 1)) = some Q)
    (hQrun : RunBlock S rho Q)
    (hsourcePrev : ∀ v ∈ rho.honest,
      actionFGSource S (actionReadAt S rho v (r - 1)) = some Q.erase) :
    CanonicalHeightSourceHistoryAt S rho q r Q := by
  intro k hk hkr v hv h hrow
  have hsplit : k < r - 1 ∨ k = r - 1 :=
    Nat.lt_or_eq_of_le (Nat.le_pred_of_lt hkr)
  rcases hsplit with hkle | rfl
  · exact hhistPrev k hk hkle v hv h hrow
  · obtain ⟨G, hGsource, hGbody, hGheight⟩ :=
      honestRow_height_le_source S adm hv hrow
    have hGrun := w4gc_body_run S adm hv hGbody
    have hGQ : G = Q := by
      apply adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
        G Q hGrun hQrun G Q
        (Or.inl (Proofs.NamedAncestry.named_self G))
        (Or.inr (Proofs.NamedAncestry.named_self Q))
      rw [← Proofs.NamedWire.erase_root G, ← Proofs.NamedWire.erase_root Q]
      exact congrArg Block.root
        (Option.some.inj (hGsource.symm.trans (hsourcePrev v hv)))
    refine ⟨Q, hsourcePrev v hv, hQrun, Proofs.NamedAncestry.named_self Q, ?_⟩
    simpa only [hGQ] using hGheight

private theorem w4gc_deadline_le_selected
    (S : Setup V) {rho : Run V} {rGST gap extra q : Round}
    (hlate : fgSafetyProgressDeadline S rho (rGST) gap extra +
      3 * progressLag' gap extra + 1 ≤ q) :
    fgSafetyProgressDeadline S rho (rGST) gap extra + 3 ≤ q := by
  have hL : 0 < progressLag' gap extra := progressLag'_pos gap
  have hmul : 3 * 1 ≤ 3 * progressLag' gap extra :=
    Nat.mul_le_mul_left 3 (Nat.succ_le_iff.mpr hL)
  have hthree : 3 ≤ 3 * progressLag' gap extra + 1 :=
    (by decide : (3 : Nat) ≤ 3 * 1 + 1) |>.trans
      (Nat.add_le_add_right hmul 1)
  exact (Nat.add_le_add_left hthree _).trans hlate

private theorem w4gc_deadline_le_sub_two {d r : Nat} (h : d + 3 ≤ r) :
    d ≤ r - 2 := by omega

private theorem w4gc_deadline_le_sub_one {d r : Nat} (h : d + 3 ≤ r) :
    d + 2 ≤ r - 1 := by omega

private theorem w4gc_gst_le_deadline (S : Setup V) (rho : Run V)
    (rGST gap extra : Round) :
    rGST ≤ fgSafetyProgressDeadline S rho rGST gap extra := by
  unfold fgSafetyProgressDeadline
  exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)

private theorem w4gc_confirmation_mono
    (E : Env V) {s t : Slot} (h : s ≤ t) :
    Protocol.confirmation_time E s ≤ Protocol.confirmation_time E t := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ,
    Protocol.confirmation_time_eq_support_cutoff_succ]
  exact Proofs.Optimistic.support_cutoff_mono E (Nat.add_le_add_right h 1)

/-- A named honest opening strictly after two progress periods is above the
frontier at the progress base. This is the opening-slot form of
`w4_postGain_secondSlot_height_of_base`. -/
private theorem w4gc_honestOpening_height_of_twoProgress
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap extra q m : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S extra)
    (hpost : S.E.t_GST ≤ S.a (rGST))
    (hdeadline : fgSafetyProgressDeadline S rho (rGST) gap extra +
      3 ≤ q)
    (hprogress : EventualHeightProgressFrom S rho q (progressLag' gap extra))
    (hm : q + 2 * progressLag' gap extra < m)
    (hprop : S.E.proposer (S.hc.opening_slot m) ∈ rho.honest)
    (hhor : S.a m ≤ rho.horizon)
    {Q : NamedBlock V}
    (hQ : proposedBlockAt S rho (S.hc.opening_slot m) = some Q) :
    honestHMaxAt S rho (S.a q) <
      (Protocol.derive_named S.E S.cfg Q).h := by
  classical
  obtain ⟨u, hu⟩ := honest_nonempty_of_honestCommittees hcom
  have hmpos : 0 < m := Nat.zero_lt_of_lt
    ((Nat.zero_le (q + 2 * progressLag' gap extra)).trans_lt hm)
  have hopenPos : 0 < S.hc.opening_slot m := by
    simpa only [Protocol.HealConfig.opening_slot] using
      Nat.mul_pos hmpos
        (Nat.zero_lt_of_lt (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two))
  have hvoteHor : Protocol.vote_time S.E (S.hc.opening_slot m) ≤ rho.horizon :=
    (Protocol.vote_time_le_confirmation_time S.E _).trans
      (by simpa only [opening_confirmation_time_eq_action S m] using hhor)
  have hvoteDelta : Protocol.vote_time S.E (S.hc.opening_slot m) + S.E.Δ ≤
      rho.horizon := by
    rw [Proofs.Optimistic.vote_time_add_delta]
    exact (Protocol.support_cutoff_le_confirmation_time S.E _).trans
      (by simpa only [opening_confirmation_time_eq_action S m] using hhor)
  have hdeadlineLeM :
      fgSafetyProgressDeadline S rho (rGST) gap extra ≤ m :=
    (Nat.le_add_right _ 3).trans (hdeadline.trans (Nat.le_of_lt
      ((Nat.le_add_right q (2 * progressLag' gap extra)).trans_lt hm)))
  have hreadLo : S.a
      (fgSafetyProgressDeadline S rho (rGST) gap extra) ≤ S.a m :=
    Assembly.a_mono S hdeadlineLeM
  have hopenLo : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho (rGST) gap extra) + 1 ≤
      S.hc.opening_slot m := by
    have hlt : fgSafetyProgressDeadline S rho (rGST) gap extra < m :=
      lt_of_le_of_lt
        (Nat.le_add_right
          (fgSafetyProgressDeadline S rho (rGST) gap extra) 3)
        (hdeadline.trans_lt ((Nat.le_add_right q
          (2 * progressLag' gap extra)).trans_lt hm))
    exact (Nat.le_succ _).trans
      (openingSlot_add_two_le_openingSlot_of_lt S hlt)
  obtain ⟨T, hTrun, hTband, hTheads⟩ :=
    exists_namedCommonPreviousHeadAncestor_in_frontierBand_through_confirmation_after_GST
      S adm hcom hbelow hrec hdelay hpost hreadLo hhor hopenLo
      (by simpa only [opening_confirmation_time_eq_action S m] using
        (le_refl (S.a m))) hvoteDelta hu
  have hround2 : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho (rGST) gap extra + 2) ≤
      (S.hc.opening_slot m - 1) + 1 := by
    rw [Nat.sub_add_cancel hopenPos]
    exact Nat.mul_le_mul_right S.hc.R
      ((Nat.add_le_add_left (by decide : (2 : Nat) ≤ 3) _).trans
        (hdeadline.trans (Nat.le_of_lt
          ((Nat.le_add_right q (2 * progressLag' gap extra)).trans_lt hm))))
  have hheads : ∀ w ∈ rho.honest,
      voterHeadAt S rho w (S.hc.opening_slot m) = Q.erase := by
    simpa only [Nat.sub_add_cancel hopenPos] using
      (honestProposal_voterHeadAt_eq_after_SG_healing_named_slot
        S adm hcom hbelow hrec hdelay hpost
        (s := S.hc.opening_slot m - 1) hround2
        (by simpa only [Nat.sub_add_cancel hopenPos] using hvoteHor)
        (by simpa only [Nat.sub_add_cancel hopenPos] using hprop)
        (by simpa only [Nat.sub_add_cancel hopenPos] using hQ))
  have hTQerase : Block.Preceq T.erase Q.erase := by
    have h := hTheads u hu
    rwa [hheads u hu] at h
  have hproposalHor : Protocol.proposal_time S.E (S.hc.opening_slot m) ≤
      rho.horizon :=
    (Protocol.proposal_time_lt_vote_time S.E _).le.trans hvoteHor
  have hQrun : RunBlock S rho Q :=
    proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
      (S.hc.opening_slot m) hopenPos hprop hproposalHor hQ
  have hTQ : NamedBlock.Preceq T Q :=
    namedPreceq_of_runBlock_erase_preceq adm hTrun hQrun hTQerase
  have hTheight : (Protocol.derive_named S.E S.cfg T).h ≤
      (Protocol.derive_named S.E S.cfg Q).h :=
    Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hTQ
  have hprogressHor : S.a (q + 2 * progressLag' gap extra) ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_of_lt hm)).trans hhor
  have hgain : honestHMaxAt S rho (S.a q) + 2 ≤
      honestHMaxAt S rho (S.a (q + 2 * progressLag' gap extra)) :=
    eventualHeightProgress_iterate S hprogress (Nat.le_refl q) 2 hprogressHor
  have hpostProgress : S.E.t_GST ≤
      S.a (q + 2 * progressLag' gap extra) :=
    hpost.trans (Assembly.a_mono S
      ((w4gc_gst_le_deadline S rho (rGST) gap extra).trans
        ((Nat.le_add_right
          (fgSafetyProgressDeadline S rho (rGST) gap extra) 3).trans
          (hdeadline.trans (Nat.le_add_right q _)))))
  have hrelay : S.a (q + 2 * progressLag' gap extra) + 1 + S.E.Δ ≤ S.a m :=
    Handover.action_succ_delta_le_action_of_lt S hm
  have hlocal := Handover.honestHMaxAt_le_localFrontier_after_oneDelay
    S adm hcom (slashableBound_of_admissible_belowOneThird S adm hbelow)
      hpostProgress hrelay hhor u hu
  exact Handover.heightOld_assemble hgain hlocal hTband hTheight

/-- Close the selected-carrier grade callback from the stage-3 carrier record,
the narrowed source callback, and the two call-site caps. -/
theorem w4PreparedSelectedGradeAt_of_chain
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {gap extra q : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S extra)
    (rGST : Round) (hpost : S.E.t_GST ≤ S.a rGST)
    (hlate : fgSafetyProgressDeadline S rho rGST gap extra +
      3 * progressLag' gap extra + 1 ≤ q)
    (hsourceAt : W4PreparedSelectedSourceAt S rho q extra)
    (hchain : MovingChainAtCarrierFrom S rho q) :
    W4PreparedSelectedGradeAt S rho q extra := by
  intro r hguard hafter hopening hhor habove hprevCap hnl
  change q + extra + 4 ≤ r at hguard
  have htwoExtra : 2 < extra + 4 :=
    (by decide : (2 : Nat) < 4) |>.trans_le (Nat.le_add_left 4 extra)
  have hq2r : q + 2 < r :=
    (Nat.add_lt_add_left htwoExtra q).trans_le hguard
  have hdeadlineQ :
      fgSafetyProgressDeadline S rho rGST gap extra + 3 ≤ q :=
    w4gc_deadline_le_selected S hlate
  have hr :
      fgSafetyProgressDeadline S rho rGST gap extra + 3 ≤ r :=
    hdeadlineQ.trans ((Nat.le_add_right q 2).trans hq2r.le)
  have hrpos : 0 < r :=
    Nat.lt_of_lt_of_le (by decide : 0 < 3) (Nat.le_trans (Nat.le_add_left 3 _) hr)
  obtain ⟨C0, End0, hstage⟩ := hchain r hafter hopening.2.2 hhor
  obtain ⟨P, hP⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot r)
  obtain ⟨P1, hP1⟩ := proposedBlockAt_isSome S rho
    (S.hc.opening_slot r + 1)
  obtain ⟨Q, hQ⟩ := proposedBlockAt_isSome S rho
    (S.hc.opening_slot (r - 1))
  have hcapP : honestHMaxAt S rho (S.a q) ≤
      (Protocol.derive_named S.E S.cfg P).h := by
    have hcanon : P = canonicalProposal S rho (S.hc.opening_slot r) := by
      have hspec := canonicalProposal_spec S rho (S.hc.opening_slot r)
      exact Option.some.inj (hP.symm.trans hspec)
    have hstrict := habove
    rw [carrierOpeningHeight, ← hcanon] at hstrict
    exact hstrict.le
  have hArhor := w4cr_actionHorizon S hhor
  have hprevHor : S.a (r - 1) ≤ rho.horizon :=
    ((action_strictMono S).monotone (Nat.sub_le r 1)).trans hArhor
  have hhorOpen : Protocol.confirmation_time S.E
      (S.hc.opening_slot (r - 1)) ≤ rho.horizon := by
    simpa only [opening_confirmation_time_eq_action S (r - 1)] using hprevHor
  have hpostPrev : S.E.t_GST ≤ S.a (r - 1) :=
    hpost.trans ((action_strictMono S).monotone
      ((w4gc_gst_le_deadline S rho rGST gap extra).trans
        ((w4gc_deadline_le_sub_two hr).trans
          (Nat.sub_le_sub_left (by decide) r))))
  have hsucc : r - 1 + 1 = r := Nat.sub_add_cancel hrpos
  have hcut : S.hc.Γ_neg1 S.E.Δ r ≤ rho.horizon := by
    have hstep : S.hc.Γ_neg1 S.E.Δ (r - 1 + 1) ≤ rho.horizon :=
      (next_Γ_neg1_lt_action S (r - 1)).le.trans
        (by simpa only [hsucc] using hArhor)
    simpa only [hsucc] using hstep
  have hprevRoundPos : 0 < r - 1 := by
    rw [Nat.sub_pos_iff_lt]
    exact (by decide : (1 : Nat) < 2) |>.trans
      (lt_of_le_of_lt (Nat.le_add_left 2 q) hq2r)
  have hprevSlotPos : 0 < S.hc.opening_slot (r - 1) := by
    simpa only [Protocol.HealConfig.opening_slot] using
      Nat.mul_pos hprevRoundPos
        (Nat.zero_lt_of_lt (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two))
  have hprevProposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot (r - 1)) ≤ rho.horizon :=
    (Protocol.proposal_time_le_confirmation_time S.E _).trans hhorOpen
  have hQrun : RunBlock S rho Q :=
    proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
      (S.hc.opening_slot (r - 1)) hprevSlotPos hopening.2.1
      hprevProposalHor hQ
  have hP1run : RunBlock S rho P1 :=
    proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
      (S.hc.opening_slot r + 1) (Nat.zero_lt_succ _) hopening.2.2.2.1
      ((Protocol.proposal_time_mono S.E
          (Nat.le_succ (S.hc.opening_slot r + 1))).trans
        ((Protocol.proposal_time_le_confirmation_time S.E _).trans hhor)) hP1
  have hQP1erase : Block.Preceq Q.erase P1.erase :=
    w4cr_previousOpening_preceq_interior S adm hcom hbelow hrec hdelay
      hpost hr hopening.2.2 hhor hopening.2.1 hQ hP1
  have hQP1 : NamedBlock.Preceq Q P1 :=
    Protocol.namedPreceq_of_runBlock_erase_preceq adm hQrun hP1run hQP1erase
  have hcapP1 : honestHMaxAt S rho (S.a q) ≤
      (Protocol.derive_named S.E S.cfg P1).h :=
    (hprevCap Q hQ).trans
      (Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hQP1)
  have hhistP := hstage.heightHistory P hP
  have htargetP := hstage.targetHistory P hP
  have htimeoutP := hstage.timeoutHistory P hP
  have hbandP : ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v (S.a r)).h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg P).h :=
    w4cr_band_of_heightGates S adm hcom hbelow
      (w4cr_pastHeightGates_of_history S adm hhistP hcapP (le_refl (S.a r)))
      (w4cr_openingProposal_mem_bodies S adm hcom hbelow hrec hdelay
        hpost hr hopening.2.2 hhor hP)
  have hhistP1 := w4cr_interiorHistory_of_pins S adm hcom hbelow hrec hdelay
    hpost hdeadlineQ hr hopening.2.2 hhor hP1
  have hnextConf : S.a r ≤
      Protocol.confirmation_time S.E (S.hc.opening_slot r + 1) := by
    rw [← opening_confirmation_time_eq_action S r]
    exact w4gc_confirmation_mono S.E (Nat.le_succ _)
  have hbandP1Action : ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v (S.a r)).core.h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg P1).h :=
    w4cr_band_of_heightGates S adm hcom hbelow
      (w4cr_pastHeightGates_of_history S adm hhistP1 hcapP1
        ((action_strictMono S).monotone (Nat.le_succ r)))
      (w4cr_interiorProposal_mem_bodies_at S adm hcom hbelow hrec hdelay
        hpost hr hopening.2.2 hhor hP1 (le_refl (S.a r)) hArhor hnextConf)
  have hbandP1PlusTwo : ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v
          (Protocol.proposal_time S.E (S.hc.opening_slot r + 2))).core.h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg P1).h :=
    w4cr_band_of_heightGates S adm hcom hbelow
      (w4cr_pastHeightGates_of_history S adm hhistP1 hcapP1
        (w4cr_plusTwoProposal_le_nextAction S r))
      (w4cr_interiorProposal_mem_bodies_at S adm hcom hbelow hrec hdelay
        hpost hr hopening.2.2 hhor hP1
        (w4cr_action_le_plusTwoProposal S r)
        ((Protocol.proposal_time_le_confirmation_time S.E _).trans hhor)
        (w4cr_plusTwoProposal_le_plusOneConfirmation S r))
  have hrecord := movingChainAtCarrierFor_atPreviousOpening S adm hcom hbelow
    hrec hdelay hpost (q0 := q) hr hopening.2.2 hhor hopening.2.1
    hnl hQ hP hbandP
    (fun P1' hP1' => by
      have heq : P1' = P1 := Option.some.inj (hP1'.symm.trans hP1)
      simpa only [heq] using hbandP1Action)
    (fun P1' hP1' => by
      have heq : P1' = P1 := Option.some.inj (hP1'.symm.trans hP1)
      simpa only [heq] using hbandP1PlusTwo)
    hhistP htargetP htimeoutP
  have hsourcePrev := hsourceAt r hguard hopening hhor hQ hprevHor
  have hhistPrev := w4_quietPreviousHistory_of_spine S adm hcom hbelow
    (rGST := rGST) (gap := gap) (extra := extra)
    (q0 := q) (r := r) hrec hdelay hpost hdeadlineQ hq2r hprevHor
    hopening.2.1 hQrun hQ
  have hhistQ := w4gc_heightHistory_extend S adm hhistPrev hopening.2.1
    hQ hQrun hsourcePrev
  have hgates : Protocol.PastHonestHeightGatesBelow S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) Q :=
    w4cr_pastHeightGates_of_history S adm hhistQ (hprevCap Q hQ)
      (FrameForward.domain_le_a S r .g2)
  have hsourceStore := w4gc_sourceAt_to_actionStoreAt S hsourceAt
  have hsource : ∀ w ∈ rho.honest, ∀ X : Block V,
      actionFGSource S (actionStoreAt S rho w (r - 1)) = some X →
        X = Q.erase :=
    hsourceStore r hguard hopening hhor hQ hprevHor
  have hheadsPrev : ∀ v ∈ rho.honest,
      voteDutyHead S rho v (S.hc.opening_slot (r - 1)) = Q.erase :=
    w4cr_openingHeads_atRound S adm hcom hbelow hrec hdelay hpost
      (w4gc_deadline_le_sub_one hr) hopening.2.1 hprevHor hQ
  have hcarrierEq := w4cr_previousCarrier_eq_previousOpening S adm hcom
    hbelow hrec hdelay hpost hr hhor hopening.2.1 hQ
  have hmemDomain := w4cr_prevOpening_mem_bodies_atDomain S adm hcom hbelow
    hrec hdelay hpost hr hhor hopening.2.1 hQ
  have hprevPre := w4cr_previousOpening_preceq_opening S adm hcom hbelow hrec
    hdelay hpost hr hopening.2.2 hhor hopening.2.1 hQ hP
  have hmemP := w4cr_openingProposal_mem_bodies S adm hcom hbelow hrec hdelay
    hpost hr hopening.2.2 hhor hP
  have hgrade := namedGradeFormsAt_prevOpeningProposal_of_heightGates
    (delayExtra := extra) S adm hcom hbelow
      (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S := S)
        hbelow)
      hrec hdelay hpost hrpos (w4gc_deadline_le_sub_one hr)
      hopening.2.1 hQ hhorOpen hheadsPrev hsource hArhor hrecord hnl hgates
      hcarrierEq hmemDomain hprevPre hmemP hbandP hpostPrev hcut
  exact ⟨Q.erase, P.erase, hrecord, hgrade⟩

/-- Additive D2 twin whose source and grade callbacks both have the guards and
local caps present at their only call sites. -/
theorem commonFinalityAboveFrontier_of_openingCarrierRecurrence_of_pins_preparedFactsGradeCallsite
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {gap : Round} {delayExtra : Nat}
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    (hop : ProposerOpeningCarrierRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (rGST : Round) (hpost : S.E.t_GST ≤ S.a rGST)
    (hK : gap + 2 ≤ S.cfg.K)
    {q0 : Round}
    (hexec : CanonicalSuffixExecutionPrepared S rho q0)
    (hqLate : fgSafetyProgressDeadline S rho rGST gap delayExtra +
      3 * progressLag' gap delayExtra + 1 ≤ q0)
    (hgradeAt : W4PreparedSelectedGradeAt S rho q0 delayExtra)
    (hprogress : EventualHeightProgressFrom S rho q0 (progressLag' gap delayExtra))
    (hpostBoundary : S.E.t_GST ≤ S.a q0)
    (hnotLost : ∀ r : Round, q0 + 2 < r →
      S.E.proposer (S.hc.opening_slot (r - 1)) ∈ rho.honest →
      Protocol.confirmation_time S.E (S.hc.opening_slot r + 2) ≤ rho.horizon →
      ¬ LostRoundAt S rho r)
    (hcoreAt : ∀ r : Round,
      healingBoundaryTime S q0 <
        Protocol.proposal_time S.E (S.hc.opening_slot r) →
      ProposerCarrierAt S rho r →
      Protocol.confirmation_time S.E (S.hc.opening_slot r + 2) ≤ rho.horizon →
      CanonicalRegimeRoundExecutionFactsAt S rho q0 r)
    (hregime : W4CanonicalRegimeRoundFactsPinGraded S rho q0)
    (hdensity : CanonicalCarrierDensityFromPrepared S rho q0)
    (hfirstHalf : W4PreparedSelectedFirstHalfAt S rho q0)
    (hcarrierFinality : W4CarrierChainFinalityPin S rho q0)
    (hanchorAt : ∀ (r : Round), q0 + 2 < r →
      ProposerOpeningCarrierAt S rho r →
      ∀ {Pprev : NamedBlock V},
      proposedBlockAt S rho (S.hc.opening_slot (r - 1)) = some Pprev →
      S.a (r - 1) ≤ rho.horizon →
      ∀ v ∈ rho.honest,
        Block.Preceq
          (PhaseGrades.nodeAnchor S (actionReadAt S rho v (r - 1)) (r - 1))
          Pprev.erase)
    (hsourceAt : W4PreparedSelectedSourceAt S rho q0 delayExtra)
    {start : Round}
    (hstart : q0 ≤ start)
    (hhor : S.a (start + recurringFinalityPhaseLag (progressLag' gap delayExtra) gap) ≤
      rho.horizon) :
    ∃ H : Height, honestHMaxAt S rho (S.a start) < H ∧
      AlreadyCommonFinalizedAtOrAbove S rho q0 start
        (start + recurringFinalityPhaseLag (progressLag' gap delayExtra) gap) H := by
  have hrec := proposerRecurrence_of_openingCarrierRecurrence S hop
  have hfirst_window_after : ∀ {q start L : Nat},
      q ≤ start → 0 < L → q + 1 < start + 2 * L + 1 := by
    intro q start L hstart hL
    omega
  have hprevious_round_guard : ∀ {q c e : Nat},
      q + e + 4 ≤ c → q + 2 < c - 1 := by
    intro q c e h
    omega
  have hvoteTime_lt_nextProposal : ∀ (E : Env V) (s : Slot),
      Protocol.vote_time E s < Protocol.proposal_time E (s + 1) := by
    intro E s
    apply lt_trans ?_ (support_cutoff_lt_proposal_time_succ E s)
    rw [← vote_time_add_delta]
    exact Int.lt_add_of_pos_right _ E.Δ_pos
  have hafter_boundary_of_gap : ∀ {q r : Round}, q + 1 < r →
      healingBoundaryTime S q <
        Protocol.proposal_time S.E (S.hc.opening_slot r) := by
    intro q r hr
    have hfirst := Nat.add_le_add_right
      (openingSlot_add_two_le_openingSlot_of_lt S (Nat.lt_succ_self q)) 1
    have hslots : S.hc.opening_slot q + 3 ≤ S.hc.opening_slot r :=
      hfirst.trans ((Nat.le_succ (S.hc.opening_slot (q + 1) + 1)).trans
        (openingSlot_add_two_le_openingSlot_of_lt S hr))
    exact (hvoteTime_lt_nextProposal S.E (S.hc.opening_slot q + 2)).trans_le
      (proposal_time_mono S.E hslots)
  have hconfirmation_two_le_next_action : ∀ (r : Round),
      Protocol.confirmation_time S.E (S.hc.opening_slot r + 2) ≤ S.a (r + 1) := by
    intro r
    have hslot : S.hc.opening_slot r + 2 ≤ S.hc.opening_slot (r + 1) := by
      simpa only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul] using
        Nat.add_le_add_left S.hc.R_ge_two (r * S.hc.R)
    simpa only [Setup.a, Protocol.a_eq_confirmation_time] using
      Int.add_le_add_right (proposal_time_mono S.E hslot) (6 * S.E.Δ)
  have hselected_bounds : ∀ {q start L e gap c : Nat},
      q ≤ start → e + 4 ≤ 2 * L + 1 → start + 1 + 2 * L < c →
      c ≤ start + 1 + 4 * L + 3 * gap + 4 →
      q + e + 4 ≤ c ∧ q + 2 < c ∧ start < c ∧
        c + 1 ≤ start + (4 * L + 4 * gap + 7) := by
    intro q start L e gap c hstart hmargin hlo hhi
    omega
  have hfinal_carrier_bound : ∀ {start L gap c r : Nat},
      c ≤ start + 1 + 4 * L + 3 * gap + 4 → r ≤ c + 1 + gap →
      r + 1 ≤ start + (4 * L + 4 * gap + 7) := by
    intro start L gap c r hc hr
    omega
  have hdensity_window_le_phase : ∀ {start L gap : Nat},
      start + 1 + 4 * L + 3 * gap + 5 ≤
        start + (4 * L + 4 * gap + 7) := by
    intro start L gap
    omega
  set L := progressLag' gap delayExtra with hL
  change S.a (start + (4 * L + 4 * gap + 7)) ≤ rho.horizon at hhor
  have hLpos : 0 < L := progressLag'_pos gap
  have hmargin : delayExtra + 4 ≤ 2 * L + 1 := by
    rw [hL]
    dsimp [progressLag', seedLag]
    omega
  have hstepHor : ∀ r : Round, r ≤ start + (4 * L + 4 * gap + 7) →
      S.a r ≤ rho.horizon := fun r hr => (Assembly.a_mono S hr).trans hhor
  have hafterAll : ∀ r : Round, q0 + 1 < r →
      healingBoundaryTime S q0 < Protocol.proposal_time S.E (S.hc.opening_slot r) :=
    fun _ hr => hafter_boundary_of_gap hr
  have hpostAll : ∀ r : Round, q0 < r →
      S.E.t_GST ≤ Protocol.proposal_time S.E (S.hc.opening_slot r) := by
    intro r hr
    exact hpostBoundary.trans ((Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
      (action_add_delta_le_openingProposal_of_round_lt S hr))
  have hroundAt : ∀ r : Round, q0 + delayExtra + 4 ≤ r → q0 + 2 < r →
      ProposerOpeningCarrierAt S rho r → S.a (r + 1) ≤ rho.horizon →
      honestHMaxAt S rho (S.a q0) < carrierOpeningHeight S rho r →
      (∀ Q : NamedBlock V,
        proposedBlockAt S rho (S.hc.opening_slot (r - 1)) = some Q →
        honestHMaxAt S rho (S.a q0) ≤
          (Protocol.derive_named S.E S.cfg Q).h) →
      ∃ C End : Block V, CanonicalRegimeRoundAt S rho q0 r ∧
        MovingChainAtCarrierFor S rho q0 r C End ∧
        NamedGradeFormsAt S rho r C ∧ ¬ LostRoundAt S rho r := by
    intro r hguard hr hc hh haboveR hprevCap
    have hconf := (hconfirmation_two_le_next_action r).trans hh
    have hafter := hafterAll r ((Nat.le_succ (q0 + 1)).trans_lt hr)
    have hnl := hnotLost r hr hc.2.1 hconf
    obtain ⟨C, End, hchainR, hgradeR⟩ :=
      hgradeAt r hguard hafter hc hconf haboveR hprevCap hnl
    have hcore := hcoreAt r hafter hc.2.2 hconf
    exact ⟨C, End, hregime r C End hcore hchainR hgradeR hnl,
      hchainR, hgradeR, hnl⟩
  have hdensityHor : S.a (start + 1 + 4 * L + 3 * gap + 5) ≤ rho.horizon :=
    hstepHor _ hdensity_window_le_phase
  have hqualified : ∀ k : Round, ∃ c : Round, k ≤ c ∧ c ≤ k + gap ∧
      ProposerCarrierAt S rho c ∧
      (S.E.proposer (S.hc.opening_slot (c - 2)) ∈ rho.honest ∧
       S.E.proposer (S.hc.opening_slot (c - 1)) ∈ rho.honest) := by
    intro k
    obtain ⟨c, hlo, hhi, htwo, hone, hc⟩ := hop k
    exact ⟨c, (Nat.le_add_right k 2).trans hlo, hhi, hc, htwo, hone⟩
  obtain ⟨c1, c2, hc1lo, h12, _, hc2hi, hc1, hc2, ha1, ha2, hnj, hp1, hp2⟩ :=
    exists_justifiableCarrierPair_afterTwoProgress_with_property_prepared
      S adm hdensity hprogress hLpos hqualified hK
        (start := start + 1) (hstart.trans (Nat.le_succ start))
        (hafterAll _ (hfirst_window_after
          (hstart.trans (Nat.le_succ start)) hLpos)) hdensityHor
  have hselected : ∃ c : Round, start + 1 + 2 * L < c ∧
      c ≤ start + 1 + 4 * L + 3 * gap + 4 ∧
      ProposerCarrierAt S rho c ∧
      S.E.proposer (S.hc.opening_slot (c - 2)) ∈ rho.honest ∧
      S.E.proposer (S.hc.opening_slot (c - 1)) ∈ rho.honest ∧
      honestHMaxAt S rho (S.a (start + 1)) < carrierOpeningHeight S rho c ∧
      (∀ P0 : NamedBlock V,
        proposedBlockAt S rho (S.hc.opening_slot c) = some P0 →
        (Protocol.derive_named S.E S.cfg P0).nj = false) := by
    obtain ⟨P1, P2, hP1, hP2, hnjOr⟩ := hnj
    rcases hnjOr with hnj1 | hnj2
    · refine ⟨c1, hc1lo, h12.le.trans hc2hi, hc1, hp1.1, hp1.2, ha1, ?_⟩
      intro P0 hP0
      rw [Option.some.inj (hP0.symm.trans hP1)]
      exact hnj1
    · refine ⟨c2, hc1lo.trans h12, hc2hi, hc2, hp2.1, hp2.2, ha2, ?_⟩
      intro P0 hP0
      rw [Option.some.inj (hP0.symm.trans hP2)]
      exact hnj2
  obtain ⟨c, hclo, hchi, hc, htwo, hpred, haboveStart, hnjC⟩ := hselected
  obtain ⟨hlate, hqc, hstartC, hcEnd⟩ := hselected_bounds hstart hmargin hclo hchi
  have habove : honestHMaxAt S rho (S.a q0) < carrierOpeningHeight S rho c :=
    (honestHMaxAt_mono S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (Assembly.a_mono S (hstart.trans (Nat.le_succ start)))).trans_lt haboveStart
  have hprevHor : S.a (c - 1) ≤ rho.horizon :=
    hstepHor (c - 1) (((Nat.sub_le c 1).trans (Nat.le_succ c)).trans hcEnd)
  have hprevProgress : q0 + 2 * progressLag' gap delayExtra < c - 1 := by
    rw [← hL]
    apply Nat.lt_sub_of_add_lt
    have hbase : q0 + 2 * L + 1 ≤ start + 1 + 2 * L := by
      have h := Nat.add_le_add_right
        (Nat.add_le_add_right hstart (2 * L)) 1
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    exact hbase.trans_lt hclo
  have hprevCap : ∀ Q : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot (c - 1)) = some Q →
      honestHMaxAt S rho (S.a q0) ≤
        (Protocol.derive_named S.E S.cfg Q).h := by
    intro Q hQ
    exact (w4gc_honestOpening_height_of_twoProgress S adm hcom hbelow hrec
      hdelay hpost (w4gc_deadline_le_selected S hqLate) hprogress
      hprevProgress hpred hprevHor hQ).le
  obtain ⟨C, End, hround, hchainC, hgradeC, hnlC⟩ :=
    hroundAt c hlate hqc ⟨htwo, hpred, hc⟩ (hstepHor _ hcEnd)
      habove hprevCap
  have hpostPrev : S.E.t_GST ≤ S.a (c - 1) :=
    hpostBoundary.trans (Assembly.a_mono S
      (Nat.le_sub_of_add_le ((Nat.le_succ (q0 + 1)).trans hqc.le)))
  have hpostC := hpostAll c ((Nat.le_add_right q0 2).trans_lt hqc)
  have hprevLate : q0 + 1 < c - 1 :=
    Nat.lt_sub_of_add_lt (by simpa only [Nat.add_assoc] using hqc)
  have hprevious := canonicalOpeningLifecycleAt_of_executionPrepared S hcom hexec
    (hafterAll _ hprevLate) hpred hprevHor
  have hone : ∀ v ∈ rho.honest, ∀ w ∈ rho.honest,
      (actionStoreAt S rho v (c - 1)).st.core.live_confirmed =
        (actionStoreAt S rho w (c - 1)).st.core.live_confirmed := by
    intro v hv w hw
    obtain ⟨Pprev, hPprev⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot (c - 1))
    rw [(hprevious Pprev hPprev v hv).1, (hprevious Pprev hPprev w hw).1]
  have hnlPrev : ¬ LostRoundAt S rho (c - 1) := by
    refine hnotLost (c - 1) (hprevious_round_guard hlate) ?_ ?_
    · simpa only [Nat.sub_sub, Nat.reduceAdd] using htwo
    · exact (hconfirmation_two_le_next_action (c - 1)).trans
        (hstepHor (c - 1 + 1) ((Nat.add_le_add_right (Nat.sub_le c 1) 1).trans hcEnd))
  obtain ⟨Pprev, hPprev⟩ :=
    proposedBlockAt_isSome S rho (S.hc.opening_slot (c - 1))
  obtain ⟨P0, hP0⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot c)
  obtain ⟨P1, hP1⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot c + 1)
  have hP0run : RunBlock S rho P0 := carrierOpening_runBlock S adm hround hP0
  have hP1run : RunBlock S rho P1 :=
    proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
      (S.hc.opening_slot c + 1) (Nat.zero_lt_succ _) hround.carrier.2.1
      ((Protocol.proposal_time_mono S.E
          (Nat.le_succ (S.hc.opening_slot c + 1))).trans
        ((Protocol.proposal_time_le_confirmation_time S.E _).trans hround.inHorizon)) hP1
  have hparents := w4_parentEqualities_of_canonicalSuffixFrom
    S adm hexec.canonicalSuffixFrom
  have hparentErase := (hparents c hround).1 P0 hP0
  obtain ⟨p, hp, hpe⟩ := proposedBlockAt_parent S rho (S.hc.opening_slot c + 1) hP1
  have hpP1 : NamedBlock.Preceq p P1 := by
    cases P1 with
    | genesis => cases hp
    | node parent slot root votes support rows proposer =>
        have hparent : parent = p := Option.some.inj hp
        rw [← hparent]
        exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
          (Proofs.NamedAncestry.named_self parent)
  have hprun : RunBlock S rho p :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hP1run hpP1
  have hrunUnique : ∀ {A D : NamedBlock V}, RunBlock S rho A →
      RunBlock S rho D → A.erase = D.erase → A = D := by
    intro A D hA hD herase
    exact adm.toNamedRootCollisionFree.root_injective A D hA hD A D
      (Or.inl (Proofs.NamedAncestry.named_self A)) (Or.inr (Proofs.NamedAncestry.named_self D))
      (by rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root D, herase])
  have heq : p = P0 := hrunUnique hprun hP0run (hpe.trans hparentErase)
  have hparent : NamedBlock.parent? P1 = some P0 := by
    rw [← heq]
    exact hp
  have hP0P1 : NamedBlock.Preceq P0 P1 := by
    rw [heq] at hpP1
    exact hpP1
  have hcapP1 : honestHMaxAt S rho (S.a q0) <
      (Protocol.derive_named S.E S.cfg P1).h :=
    habove.trans_le (by
      have hcanon : P0 = canonicalProposal S rho (S.hc.opening_slot c) := by
        have hspec := canonicalProposal_spec S rho (S.hc.opening_slot c)
        exact Option.some.inj (hP0.symm.trans hspec)
      have hmono := Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hP0P1
      simpa only [carrierOpeningHeight, ← hcanon] using hmono)
  have hseedC : W4CarrierCapSeed S rho q0 c :=
    ⟨P1, ⟨htwo, hpred, hc⟩, hP1,
      hround.afterBoundary.trans_le
        (Protocol.proposal_time_mono S.E (Nat.le_succ _)), hcapP1⟩
  have hprevRoundPos : 0 < c - 1 := (Nat.zero_lt_succ q0).trans hprevLate
  have hprevSlotPos : 0 < S.hc.opening_slot (c - 1) := by
    have hRpos : 0 < S.hc.R := Nat.lt_of_lt_of_le (by decide) S.hc.R_ge_two
    simpa only [Protocol.HealConfig.opening_slot] using (Nat.mul_pos hprevRoundPos hRpos)
  have hprevProposalHor :
      Protocol.proposal_time S.E (S.hc.opening_slot (c - 1)) ≤ rho.horizon := by
    have hproposalAction :
        Protocol.proposal_time S.E (S.hc.opening_slot (c - 1)) ≤ S.a (c - 1) := by
      have hconf : S.a (c - 1) = Protocol.confirmation_time S.E
          (S.hc.opening_slot (c - 1)) := by
        simp only [Setup.a, Protocol.a_eq_confirmation_time]
      rw [hconf]
      exact proposal_time_le_confirmation_time S.E _
    exact hproposalAction.trans hprevHor
  have hPprevRun : RunBlock S rho Pprev :=
    proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
      (S.hc.opening_slot (c - 1)) hprevSlotPos hpred hprevProposalHor hPprev
  have hlive : ∀ v ∈ rho.honest,
      (actionStoreAt S rho v (c - 1)).st.core.live_confirmed = Pprev.erase :=
    fun v hv => (hprevious Pprev hPprev v hv).1
  have hopening : ProposerOpeningCarrierAt S rho c := ⟨htwo, hpred, hc⟩
  have hhalf := hfirstHalf c C End hqc hopening hround hchainC hgradeC hnlC hnlPrev
    (hafterAll _ hprevLate) hpostPrev hpostC habove hnjC hone
    (Pprev := Pprev) (P0 := P0) (P1 := P1)
    hPprev hPprevRun hP0 hP1 hparent hP1run hprevHor hpred
    (Nat.lt_or_ge _ _) hlive (hanchorAt c hqc hopening hPprev hprevHor)
    (hsourceAt c hlate hopening hround.inHorizon hPprev hprevHor)
  obtain ⟨rFinal, hrLo, hrHi, hrTwo, hrPred, hrCarrier⟩ := hop (c + 1)
  have hcr : c < rFinal :=
    (Nat.lt_succ_self c).trans_le ((Nat.le_add_right (c + 1) 2).trans hrLo)
  have hrEnd := hfinal_carrier_bound hchi hrHi
  have hlateFinal : q0 + delayExtra + 4 ≤ rFinal :=
    hlate.trans (Nat.le_of_lt hcr)
  have haboveFinalStart : honestHMaxAt S rho (S.a start) <
      carrierOpeningHeight S rho rFinal :=
    carrierOpening_height_gt_of_twoProgress_at_carrier_of_frontierFloor
      S adm hdensity.frontierFloor hprogress hLpos hstart
      (by
        have hbase : start + 2 * L ≤ start + 1 + 2 * L := by
          simpa only [Nat.add_assoc] using
            (Nat.add_le_add_left (Nat.le_add_left (2 * L) 1) start)
        exact (hbase.trans_lt hclo).trans hcr)
      hrCarrier (hstepHor _ hrEnd)
  have haboveFinal : honestHMaxAt S rho (S.a q0) <
      carrierOpeningHeight S rho rFinal :=
    (honestHMaxAt_mono S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (Assembly.a_mono S hstart)).trans_lt haboveFinalStart
  have hcTwoFinal : c + 2 < rFinal := by
    apply Nat.lt_of_succ_le
    simpa only [Nat.add_assoc] using hrLo
  have hprevCapFinal : ∀ Q : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot (rFinal - 1)) = some Q →
      honestHMaxAt S rho (S.a q0) ≤
        (Protocol.derive_named S.E S.cfg Q).h :=
    w4cr_previousOpeningHeightCap_of_seed S adm hexec.canonicalSuffixFrom
      hseedC rFinal hcTwoFinal ⟨hrTwo, hrPred, hrCarrier⟩
        ((hconfirmation_two_le_next_action rFinal).trans (hstepHor _ hrEnd))
  obtain ⟨Cr, Endr, hroundR, hchainR, _, hnlR⟩ :=
    hroundAt rFinal hlateFinal (hqc.trans hcr) ⟨hrTwo, hrPred, hrCarrier⟩
      (hstepHor _ hrEnd) haboveFinal hprevCapFinal
  have hcommon := hcarrierFinality start c rFinal C Cr Endr hqc hcr hc hhalf hnjC
    hroundR hchainR hnlR
    (hpostAll rFinal ((Nat.le_add_right q0 2).trans_lt (hqc.trans hcr)))
    habove ((one_le_honestHMaxAt S adm hcom (S.a q0)).trans_lt habove)
    (hstartC.trans hcr) (hstepHor _ hrEnd)
  refine ⟨carrierOpeningHeight S rho c,
    (honestHMaxAt_mono S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (Assembly.a_mono S (Nat.le_succ start))).trans_lt haboveStart, ?_⟩
  obtain ⟨s, B, checkpoint, height, hs, hafter, hprop, hB, hrun, hfin, hHle,
    hheight, hne, hsource, hsourceConf, hconfEnd, hstores⟩ := hcommon
  exact ⟨s, B, checkpoint, height, hs, hafter, hprop, hB, hrun, hfin, hHle,
    hheight, hne, hsource, hsourceConf,
    hconfEnd.trans (Assembly.a_mono S hrEnd), hstores⟩

#print axioms commonFinalityAboveFrontier_of_openingCarrierRecurrence_of_pins_preparedFactsGradeCallsite


/-! The former fixed-round residual composer was removed here. Its only
recovery spine exports the fixed-post-GST deadline, so it cannot prove the
new `rGST`-anchored public window. It had no consumers; the closed route uses
the generalized call-site lemmas above. -/


#print axioms w4gc_sourceAt_to_actionStoreAt
#print axioms w4PreparedSelectedGradeAt_of_chain

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
