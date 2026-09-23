module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.W4StableRecordGrowthAfterGST
public import DecoupledConsensusProofs.Generic.W4StableContinuationCover

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Prepared-V4 G0 carrier for the selected continuation
At a selected post-start opening, the completed G0 window can still contain
votes from before the bootstrap cut. The V4 bootstrap bounds those early SG
votes by its seed; the prepared action-source theorem bounds later votes by
the same destination head. These two arms supply the relative carrier window.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace W4StableWrite

open Internal Execution Statements
open Proofs.HealingSurface Proofs.HealingSurface.Handover
open Internal.PhaseGrades DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Copy of the private `w4_action_lt_vote_two_after` in
`W4GSTZeroOpeningLifecycleRun`, scoped to this independent continuation leaf. -/
private theorem w4_continuation_action_lt_vote_two_after
    (S : Setup V) (r : Round) :
    S.a r < Protocol.vote_time S.E (S.hc.opening_slot r + 1 + 1) := by
  refine lt_of_lt_of_le
    (Protocol.action_lt_proposal_time_two_after S r) ?_
  exact le_of_lt (Protocol.proposal_time_lt_vote_time S.E _)


/-- The G0 grade has an honest window carrier under the actual prepared-V4
records, including a window that straddles its bootstrap cut. -/
theorem w4_preparedRelativeGradeCarrier_g0
    (S : Setup V) {rho : Run V} (core : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base k : Round} {start : Slot} {Pseed : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start Pseed cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap Pseed.erase)
    (hcut : base + S.hc.η_SG ≤ k)
    (hstart : start ≤ S.hc.opening_slot k + 1)
    (hhor : S.a k ≤ rho.horizon)
    (hnext : Protocol.confirmation_time S.E (S.hc.opening_slot k + 1) ≤
      rho.horizon) :
    RelativeGradeCarrierAt S rho k .g0 := by
  classical
  obtain ⟨x, hx⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
  let d := S.hc.opening_slot k + 1
  have hspan : base ≤ k - S.hc.η_SG := Nat.le_sub_of_add_le hcut
  have hkpos : 0 < k := by
    exact Nat.zero_lt_one.trans_le
      ((S.hc.η_SG_ge_one.trans (Nat.le_add_left _ base)).trans hcut)
  have hnextVote : S.a k < Protocol.vote_time S.E (d + 1) :=
    w4_continuation_action_lt_vote_two_after S k
  have hseed := (SettledBootstrapPreparedV4.protectedVoteSlots_core
    S core hcom hboot hawake hfinality hnext d hstart (Nat.le_succ d)).1
  have houts (r : Round) (hr : base + S.hc.η_SG ≤ r)
      (hrt : S.a r < Protocol.vote_time S.E (d + 1)) :=
    SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_core
      S core hcom hboot hawake hfinality hnext hstart (Nat.le_succ d) hx
      r hr hrt
  have hsg : ∀ r, base ≤ r → r < k → ∀ u ∈ rho.honest,
      NamedRun.emits S rho u
        (Object.attest (actionAttestationAt S rho u r)) (S.a r) →
      Block.Preceq (actionSGBlockAt S rho u r)
        (voterHeadAt S rho x d) := by
    intro r hr hrk u hu hemit
    by_cases hold : r < base + S.hc.η_SG
    · exact Block.preceq_trans (hboot.sgBoot r hr hold u hu hemit)
        (hseed.heads x hx)
    · have hrt : S.a r < Protocol.vote_time S.E (d + 1) :=
        lt_of_le_of_lt (Assembly.a_mono S (Nat.le_of_lt hrk)) hnextVote
      exact (houts r (Nat.le_of_not_gt hold) hrt).1 u hu hemit
  have hroots : ∀ w ∈ rho.honest,
      Block.Preceq (Protocol.get_fg_root
        (actionStoreAt S rho w k).st.core.toHealing.toFG)
        (voterHeadAt S rho x d) := by
    intro w hw
    exact ((houts k hcut hnextVote).2 w hw).1
  have hawakeK : AwakeWindowMajority S.E (fun v => (S.node v).awake)
      rho.honest S.hc.η_SG k :=
    hawake k hcut ((Assembly.a_mono S (Nat.sub_le k 1)).trans hhor)
  have hdomainHor : domain S.E S.hc k .g0 ≤ rho.horizon :=
    (FrameForward.domain_le_a S k .g0).trans hhor
  apply relativeGradeCarrierAt_of_awakeWindowMajority S core hkpos hawakeK
  exact WeakJoint.relativeCarrierWindowAt_of_awakeWindowHistory_w
    S core (NamedOutageClosure.healthyWindowDelivery_after_gst S rho core)
      (le_refl _) (le_refl _) hkpos hspan
      (fun r hr _ => hboot.basePost.trans (Assembly.a_mono S hr))
      hawakeK hsg hroots .g0 hdomainHor

#print axioms w4_preparedRelativeGradeCarrier_g0

set_option maxHeartbeats 400000 in
-- The mixed-window carrier and prepared live-selection elaboration is large.
/-- Prepared-V4 continuation twin of
`w4_nodeClear_liveConfirmed_gstZero`. The completed G0 root has the mixed
bootstrap/post-cut honest carrier above, while the prepared live-confirmation
selection and that carrier are both below the same honest next-slot head. -/
theorem w4_preparedNodeClear_liveConfirmed
    (S : Setup V) {rho : Run V} (core : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base k : Round} {start : Slot} {Pseed : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start Pseed cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap Pseed.erase)
    (hcut : base + S.hc.η_SG ≤ k)
    (hstart : start ≤ S.hc.opening_slot k + 1)
    (hhor : S.a k ≤ rho.horizon)
    (hnext : Protocol.confirmation_time S.E (S.hc.opening_slot k + 1) ≤
      rho.horizon)
    {v : V} (hv : v ∈ rho.honest) :
    nodeClear S (actionReadAt S rho v k) k
      (actionStoreAt S rho v k).st.core.live_confirmed = true := by
  classical
  obtain ⟨x, hx⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
  let d := S.hc.opening_slot k + 1
  have hkpos : 0 < k :=
    Nat.zero_lt_one.trans_le
      ((S.hc.η_SG_ge_one.trans (Nat.le_add_left _ base)).trans hcut)
  have hspan : base ≤ k - S.hc.η_SG := Nat.le_sub_of_add_le hcut
  have hcutSlot : S.hc.opening_slot (base + S.hc.η_SG) ≤
      S.hc.opening_slot k := Nat.mul_le_mul_right S.hc.R hcut
  have hnextVote : S.a k < Protocol.vote_time S.E (d + 1) :=
    w4_continuation_action_lt_vote_two_after S k
  have hread : Internal.NamedRecoveryRead.confirmationInputRead S rho v
      (S.hc.opening_slot k) =
      NamedActionReads.confirmationReadAt S rho v (S.a k) := by
    change NamedActionReads.confirmationReadAt S rho v
      (Protocol.confirmation_time S.E (S.hc.opening_slot k)) = _
    rw [Proofs.HealingSurface.opening_confirmation_time_eq_action S k]
  have hliveHead : Block.Preceq
      (actionStoreAt S rho v k).st.core.live_confirmed
      (voterHeadAt S rho x d) := by
    rw [Proofs.HealingSurface.actionStoreAt_eq_update_confirmation_openingConfStore
      S rho v k]
    have hbound :=
      SettledBootstrapPreparedV4.liveConfirmedSelection_preceq_voteDutyHead_core
        S core hcom hboot hawake hfinality hnext hstart
        (Nat.le_succ d) hcutSlot (Nat.lt_succ_self _) hv hx
    rwa [hread] at hbound
  have hframe := actionFrame_g0 S core hv hkpos hhor
  unfold nodeClear nodeRead
  change DecoupledConsensusModel.Protocol.clear
    (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho v k).cache
      (actionReadAt S rho v k).st.core.toHealing k)
    (actionStoreAt S rho v k).st.core.live_confirmed = true
  unfold DecoupledConsensusModel.Protocol.clear
  rw [hframe]
  cases hroot : storeRoot S.E S.hc
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc k .g0) v).st k .g0 with
  | none => rfl
  | some raw =>
      have hrawGrade : DecoupledConsensusModel.Protocol.gradeBool S.E
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc k .g0)
            v).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc k .g0)
            v).st.core.F
          S.hc.η_SG k (DecoupledConsensusModel.Protocol.early S.E S.hc k .g0)
          (DecoupledConsensusModel.Protocol.late S.E S.hc k .g0) raw = true :=
        (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hroot)).2
      obtain ⟨k', hk', u, huHon, hemit, hrawCarrier⟩ :=
        (w4_preparedRelativeGradeCarrier_g0 S core hcom hboot hawake
          hfinality hcut hstart hhor hnext) v hv raw hrawGrade
      have hk'lt : k' < k := mem_latestWindow_lt hk'
      have hk'base : base ≤ k' :=
        hspan.trans (WeakSG.mem_latestWindow_lower_bound hk')
      have hseed := (SettledBootstrapPreparedV4.protectedVoteSlots_core
        S core hcom hboot hawake hfinality hnext d hstart (Nat.le_succ d)).1
      have hcarrHead : Block.Preceq (actionSGBlockAt S rho u k')
          (voterHeadAt S rho x d) := by
        by_cases hold : k' < base + S.hc.η_SG
        · exact Block.preceq_trans (hboot.sgBoot k' hk'base hold u huHon hemit)
            (hseed.heads x hx)
        · have hact : S.a k' < Protocol.vote_time S.E (d + 1) :=
            lt_of_le_of_lt
              (Assembly.a_mono S (Nat.le_of_lt hk'lt)) hnextVote
          exact (SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_core
            S core hcom hboot hawake hfinality hnext hstart (Nat.le_succ d)
              hx k' (Nat.le_of_not_gt hold) hact).1 u huHon hemit
      have hclipHead : Block.Preceq
          (DecoupledConsensusModel.Protocol.clipGrade raw
            (actionReadAt S rho v k).st.core.F)
          (voterHeadAt S rho x d) :=
        Block.preceq_trans
          (NamedOutageClosure.q10_clip_preceq raw
            (actionReadAt S rho v k).st.core.F)
          (Block.preceq_trans hrawCarrier hcarrHead)
      change Block.compatible
        (actionStoreAt S rho v k).st.core.live_confirmed
        (DecoupledConsensusModel.Protocol.clipGrade raw
          (actionReadAt S rho v k).st.core.F) = true
      exact Block.compatible_of_preceq_common hliveHead hclipHead

#print axioms w4_preparedNodeClear_liveConfirmed


/-- Every honest SG vote in the selected proposal's finite expiry window
covers that proposal. The next-slot horizon for each `k < q + η_SG` comes
from the chosen duty horizon, and the prepared V4 records proves clearance
without a grade-forming premise at `q`. -/
theorem w4_preparedCoverBeforeSelectedDuty
    (S : Setup V) {rho : Run V} (core : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {Pseed : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start Pseed cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap Pseed.erase)
    {q : Round} (hstartq : start < S.hc.opening_slot q)
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    {B : NamedBlock V}
    (hB : proposedBlockAt S rho (S.hc.opening_slot q) = some B)
    (hphase : PhaseShiftSafety S rho (base + S.hc.η_SG) start Pseed.erase)
    (hdhor : S.a (q + S.hc.η_SG) ≤ rho.horizon) :
    ∀ k : Round, q ≤ k → k < q + S.hc.η_SG →
      W4Cover S rho B k := by
  intro k hqk hkd
  have hcutq : base + S.hc.η_SG < q :=
    Nat.lt_of_mul_lt_mul_right (hboot.settled.trans_lt hstartq)
  have hcutk : base + S.hc.η_SG ≤ k :=
    (Nat.le_of_lt hcutq).trans hqk
  have hslotqk : S.hc.opening_slot q ≤ S.hc.opening_slot k :=
    Nat.mul_le_mul_right S.hc.R hqk
  have hstartk : start ≤ S.hc.opening_slot k + 1 :=
    (hstartq.le.trans hslotqk).trans (Nat.le_succ _)
  have hkhor : S.a k ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_of_lt hkd)).trans hdhor
  have hnextSlot : S.hc.opening_slot k + 1 ≤
      S.hc.opening_slot (k + 1) := by
    simp only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add_left
      ((by decide : (1 : Nat) ≤ 2).trans S.hc.R_ge_two) (k * S.hc.R)
  have hnext : Protocol.confirmation_time S.E (S.hc.opening_slot k + 1) ≤
      rho.horizon :=
    (confirmation_start_le_action S hnextSlot).trans
      ((Assembly.a_mono S (Nat.succ_le_of_lt hkd)).trans hdhor)
  intro v hv
  have hvHon := ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho v k).mp hv).1
  exact w4_persistenceCoverStep_afterGST_of_localReads S core hphase
    hstartq hprop hB hqk hkhor
    (fun u hu => w4_preparedNodeClear_liveConfirmed S core hcom hboot
      hawake hfinality hcutk hstartk hkhor hnext hu) v hvHon

#print axioms w4_preparedCoverBeforeSelectedDuty

/-- The one G2 duty read at `q + η_SG` follows from the proved bounded
SG-vote cover and one local post-GST delivery window. The proposal is not
claimed to have a G2 grade at its own opening. -/
theorem w4_preparedLocalG2_at_selectedDuty_of_delivery
    (S : Setup V) {rho : Run V} (core : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {Pseed : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start Pseed cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap Pseed.erase)
    {q : Round} (hstartq : start < S.hc.opening_slot q)
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    {B : NamedBlock V}
    (hB : proposedBlockAt S rho (S.hc.opening_slot q) = some B)
    (hphase : PhaseShiftSafety S rho (base + S.hc.η_SG) start Pseed.erase)
    (hhor : S.a (q + S.hc.η_SG) ≤ rho.horizon)
    (hdel : W4WindowDeliveryAt S rho (q + S.hc.η_SG)) :
    ∀ v ∈ rho.honest,
      LocalG2CoverAtDutyRound S rho (q + S.hc.η_SG) B.erase v := by
  have hcutq : base + S.hc.η_SG < q :=
    Nat.lt_of_mul_lt_mul_right (hboot.settled.trans_lt hstartq)
  have hcutd : base + S.hc.η_SG ≤ q + S.hc.η_SG :=
    (Nat.le_of_lt hcutq).trans (Nat.le_add_right q S.hc.η_SG)
  have hdpos : 0 < q + S.hc.η_SG :=
    Nat.zero_lt_one.trans_le
      (S.hc.η_SG_ge_one.trans (Nat.le_add_left _ q))
  have hprevHor : S.a (q + S.hc.η_SG - 1) ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.sub_le _ 1)).trans hhor
  have hdomainHor : domain S.E S.hc (q + S.hc.η_SG) .g2 ≤ rho.horizon :=
    (FrameForward.domain_le_a S _ .g2).trans hhor
  have hawakeD := hawake (q + S.hc.η_SG) hcutd hprevHor
  have hcover := w4_preparedCoverBeforeSelectedDuty S core hcom hboot
    hawake hfinality hstartq hprop hB hphase hhor
  have hgrade := w4Grade_of_cover_below S core hdpos hprevHor hdomainHor
    hawakeD hdel (by
      intro j hjlo hjhi
      have hqj : q ≤ j := by
        simpa only [Nat.add_sub_cancel_right] using hjlo
      exact hcover j hqj hjhi)
  exact hgrade

#print axioms w4_preparedLocalG2_at_selectedDuty_of_delivery

/-- The selected G2 duty's delivery is local to its post-cut expiry window.
Use the honest head one slot after the duty opening as one common descendant
of the window's honest SG votes and the duty action's FG roots. Its horizon
bound is the duty action itself, not the following confirmation. -/
theorem w4_preparedWindowDelivery_at_selectedDuty
    (S : Setup V) {rho : Run V} (core : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {Pseed : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start Pseed cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap Pseed.erase)
    {q : Round} (hstartq : start < S.hc.opening_slot q)
    (hhor : S.a (q + S.hc.η_SG) ≤ rho.horizon) :
    W4WindowDeliveryAt S rho (q + S.hc.η_SG) := by
  classical
  obtain ⟨x, hx⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
  let d := q + S.hc.η_SG
  let last := S.hc.opening_slot d
  let target := last + 1
  have hcutq : base + S.hc.η_SG < q :=
    Nat.lt_of_mul_lt_mul_right (hboot.settled.trans_lt hstartq)
  have hcutd : base + S.hc.η_SG ≤ d :=
    (Nat.le_of_lt hcutq).trans (Nat.le_add_right q _)
  have hdpos : 0 < d :=
    Nat.zero_lt_one.trans_le
      (S.hc.η_SG_ge_one.trans (Nat.le_add_left _ q))
  have hspan : q ≤ d - S.hc.η_SG := by
    exact (Nat.add_sub_cancel_right q S.hc.η_SG).ge
  have hlastHor : Protocol.confirmation_time S.E last ≤ rho.horizon := by
    simpa only [last, d, Proofs.HealingSurface.opening_confirmation_time_eq_action]
      using hhor
  have hopenqd : S.hc.opening_slot q ≤ last :=
    Nat.mul_le_mul_right S.hc.R (Nat.le_add_right q _)
  have hstartTarget : start ≤ target :=
    (hstartq.le.trans hopenqd).trans (Nat.le_succ _)
  have hnextVote : S.a d < Protocol.vote_time S.E (target + 1) :=
    w4_continuation_action_lt_vote_two_after S d
  have houts (r : Round) (hr : base + S.hc.η_SG ≤ r)
      (hrt : S.a r < Protocol.vote_time S.E (target + 1)) :=
    SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_core
      S core hcom hboot hawake hfinality hlastHor hstartTarget
      (Nat.le_refl target) hx r hr hrt
  have hsg : ∀ j, q ≤ j → j < d → ∀ u ∈ rho.honest,
      NamedRun.emits S rho u
        (Object.attest (actionAttestationAt S rho u j)) (S.a j) →
      Block.Preceq (actionSGBlockAt S rho u j)
        (voterHeadAt S rho x target) := by
    intro j hqj hjd u hu hem
    have hcutj : base + S.hc.η_SG ≤ j :=
      (Nat.le_of_lt hcutq).trans hqj
    have hjtime : S.a j < Protocol.vote_time S.E (target + 1) :=
      lt_of_le_of_lt (Assembly.a_mono S hjd.le) hnextVote
    exact (houts j hcutj hjtime).1 u hu hem
  have hroots : ∀ w ∈ rho.honest,
      Block.Preceq (Protocol.get_fg_root
        (actionStoreAt S rho w d).st.core.toHealing.toFG)
        (voterHeadAt S rho x target) := by
    intro w hw
    exact ((houts d hcutd hnextVote).2 w hw).1
  have hprevHor : S.a (d - 1) ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.sub_le d 1)).trans hhor
  have hawakeD := hawake d hcutd hprevHor
  have hdomainHor : domain S.E S.hc d .g2 ≤ rho.horizon :=
    (FrameForward.domain_le_a S d .g2).trans hhor
  exact w4WindowDeliveryAt_after_gst S core hdpos hspan
    (fun j hqj _ => hboot.basePost.trans
      (Assembly.a_mono S ((Nat.le_add_right base S.hc.η_SG).trans
        ((Nat.le_of_lt hcutq).trans hqj))))
    hawakeD hsg hroots hdomainHor

#print axioms w4_preparedWindowDelivery_at_selectedDuty


/-- The corrected selected duty's local G2 cover follows from the actual
prepared-V4 records alone. Delivery and the mixed pre-cut SG history are both
discharged here. -/
theorem w4_preparedLocalG2_at_selectedDuty
    (S : Setup V) {rho : Run V} (core : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {Pseed : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start Pseed cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap Pseed.erase)
    {q : Round} (hstartq : start < S.hc.opening_slot q)
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    {B : NamedBlock V}
    (hB : proposedBlockAt S rho (S.hc.opening_slot q) = some B)
    (hphase : PhaseShiftSafety S rho (base + S.hc.η_SG) start Pseed.erase)
    (hhor : S.a (q + S.hc.η_SG) ≤ rho.horizon) :
    ∀ v ∈ rho.honest,
      LocalG2CoverAtDutyRound S rho (q + S.hc.η_SG) B.erase v :=
  w4_preparedLocalG2_at_selectedDuty_of_delivery S core hcom hboot hawake
    hfinality hstartq hprop hB hphase hhor
    (w4_preparedWindowDelivery_at_selectedDuty S core hcom hboot hawake
      hfinality hstartq hhor)

#print axioms w4_preparedLocalG2_at_selectedDuty

end W4StableWrite
end Proofs
end DecoupledConsensusModel

end
