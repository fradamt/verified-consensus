module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.PreparedV4ActualLiveSelectionComplete

@[expose] public section

/-! # Prepared V4 action outputs at the actual vote
This leaf carries the source action's own horizon fact through the action-source
induction. It therefore does not need a destination confirmation read.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem actionOutputs_at_actual_vote_aux_v4
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start d : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hd : start ≤ d) (hhor : Protocol.vote_time S.E d ≤ rho.horizon)
    {x : V} (hx : x ∈ rho.honest) :
    ∀ r, base ≤ r →
      S.a r < Protocol.vote_time S.E (d + 1) →
      S.a r ≤ rho.horizon →
      (∀ w ∈ rho.honest,
        NamedRun.emits S rho w
          (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
        Block.Preceq (actionSGBlockAt S rho w r) (voterHeadAt S rho x d)) ∧
      (base + S.hc.η_SG ≤ r → ∀ w ∈ rho.honest,
        Block.Preceq (Protocol.get_fg_root
          (actionStoreAt S rho w r).st.core.toHealing.toFG)
          (voterHeadAt S rho x d) ∧
        Block.Preceq (actionStoreAt S rho w r).live_confirmed
          (voterHeadAt S rho x d) ∧
        ∀ T, fgConfirmationWitness S (actionStoreAt S rho w r) = some T →
          Block.Preceq T (voterHeadAt S rho x d)) := by
  have hcutpos : 0 < base + S.hc.η_SG :=
    Nat.zero_lt_of_lt (Nat.add_lt_add_left S.hc.η_SG_ge_one base)
  have hbaseCut : base ≤ base + S.hc.η_SG := Nat.le_add_right _ _
  have hspan : base ≤ base + S.hc.η_SG - S.hc.η_SG :=
    Nat.le_sub_of_add_le (Nat.le_refl _)
  have hseed := SettledBootstrapPreparedV4.protectedVoteSlot_at_vote_core
    S adm hcom hboot hawake hfinality hd hhor
  obtain ⟨hlegacyActionRoots, -⟩ :=
    WeakJoint.legacyRootCallbacks_of_finiteBootstrap_complete
      S adm (last := d) hboot.oldRows hfinality
        hboot.frontierSeed hboot.fgAll
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
      intro hbase haction hactionHor
      by_cases hbootRound : r < base + S.hc.η_SG
      · refine ⟨?_, ?_⟩
        · intro w hw hemit
          exact Block.preceq_trans
            (hboot.sgBoot r hbase hbootRound w hw hemit)
            (hseed.heads x hx)
        · intro hcut
          exact False.elim (Nat.not_lt_of_ge hcut hbootRound)
      · have hcut : base + S.hc.η_SG ≤ r := Nat.le_of_not_gt hbootRound
        have hawakeCut := hawake (base + S.hc.η_SG) (Nat.le_refl _)
          ((Assembly.a_mono S ((Nat.sub_le _ _).trans hcut)).trans hactionHor)
        have hmajority : HonestWeightMajority S rho.honest :=
          WeakSG.honestWeightMajority_of_awakeWindowMajority S hawakeCut
        have hsg : ∀ k, base ≤ k → k < r → ∀ v ∈ rho.honest,
            NamedRun.emits S rho v
              (Object.attest (actionAttestationAt S rho v k)) (S.a k) →
            Block.Preceq (actionSGBlockAt S rho v k)
              (voterHeadAt S rho x d) := by
          intro k hk hkr
          exact (ih k hkr hk
            ((Assembly.a_mono S hkr.le).trans_lt haction)
            ((Assembly.a_mono S hkr.le).trans hactionHor)).1
        have hroots : ∀ w ∈ rho.honest,
            Block.Preceq (Protocol.get_fg_root
              (actionStoreAt S rho w r).toHealing.toFG)
              (voterHeadAt S rho x d) := by
          intro w hw
          rcases WeakFG.fgRoot_confirmationWitness_at_action
              S adm hmajority hw r with
            hgen | ⟨C, hC, hJ, a, ha, hemit, har, hpair, hT⟩
          · rw [hgen]
            exact Protocol.preceq_genesis _
          · by_cases haold : a.round < base + S.hc.η_SG
            · exact Block.preceq_trans
                (hlegacyActionRoots r hcut haction w hw C a hC hJ
                  ha hemit haold hpair hT)
                (hseed.heads x hx)
            · have harecent : base + S.hc.η_SG ≤ a.round :=
                Nat.le_of_not_gt haold
              have hrecent := ih a.round har (hbaseCut.trans harecent)
                ((Assembly.a_mono S har.le).trans_lt haction)
                ((Assembly.a_mono S har.le).trans hactionHor)
              exact ((hrecent.2 harecent a.val_index ha).2.2 _ hT)
        have hrpos : 0 < r := hcutpos.trans_le hcut
        have hwindowStart : base ≤ r - S.hc.η_SG :=
          hspan.trans (Nat.sub_le_sub_right hcut _)
        have hlive : ∀ w ∈ rho.honest,
            Block.Preceq (actionStoreAt S rho w r).live_confirmed
              (voterHeadAt S rho x d) := by
          intro w hw
          have hslot : S.hc.opening_slot r < d :=
            Nat.lt_of_succ_le
              (openingNext_le_of_action_before_nextVote S haction)
          rcases actionStoreAt_liveConfirmed_genuine_or_fgRoot S rho w r with
            ⟨C, hC, hEq⟩ | ⟨R, hR, hEq⟩
          · have hq : S.hc.opening_slot (base + S.hc.η_SG) ≤
                S.hc.opening_slot r := Nat.mul_le_mul_right S.hc.R hcut
            have hqHor : Protocol.confirmation_time S.E
                (S.hc.opening_slot r) ≤ rho.horizon := by
              simpa only [opening_confirmation_time_eq_action] using hactionHor
            have hprotected :=
              SettledBootstrapPreparedV4.liveConfirmedSelection_at_actual_vote_core
                S adm hcom hboot hawake hfinality hd hhor hq hqHor hslot hw
            have hg : GenuineConfirmationWith
                (NamedProfile.gradeContract
                  (Internal.NamedRecoveryRead.confirmationInputRead S rho w
                    (S.hc.opening_slot r)).cache)
                S.E S.hc (confStore S rho w (S.hc.opening_slot r))
                (S.hc.opening_slot r) C := by
              simpa only [Setup.a, Protocol.a_eq_confirmation_time] using hC
            rw [← hEq]
            exact hg.selected ▸ hprotected.heads x hx
          · rw [← hEq, hR]
            have hroot := hroots w hw
            rw [actionStoreAt_fgRoot_eq_openingConfStore] at hroot
            exact hroot
        have hawakeR := hawake r hcut
          ((Assembly.a_mono S (Nat.sub_le r 1)).trans hactionHor)
        have hform : WeakJoint.ActionGradeFormationAt S rho r := by
          apply WeakJoint.actionGradeFormationAt_of_awakeWindowMajority
            S adm hrpos hawakeR
          intro p hp
          apply relativeGradeCarrierAt_of_awakeWindowMajority
            S adm hrpos hawakeR
          exact WeakJoint.relativeCarrierWindowAt_of_awakeWindowHistory_w
            S adm
              (NamedOutageClosure.healthyWindowDelivery_after_gst S rho adm)
              (le_refl _) (le_refl _) hrpos
              (hspan.trans (Nat.sub_le_sub_right hcut S.hc.η_SG))
              (fun k hk _ => hboot.basePost.trans (Assembly.a_mono S hk))
              hawakeR hsg hroots p hp
        constructor
        · intro w hw hemit
          rcases hform.action w hw hemit with
            hpre | heq | ⟨k, hk, v, hv, hem, hpre⟩
          · exact Block.preceq_trans hpre (hlive w hw)
          · exact heq ▸ hroots w hw
          · exact Block.preceq_trans hpre
              (hsg k
                (hwindowStart.trans (WeakSG.mem_latestWindow_lower_bound hk))
                (mem_latestWindow_lt hk) v hv hem)
        · intro _ w hw
          refine ⟨hroots w hw, hlive w hw, ?_⟩
          intro T hT
          rcases hform.witness w hw T hT with
            hpre | ⟨k, hk, v, hv, hem, hpre⟩
          · exact Block.preceq_trans hpre (hlive w hw)
          · exact Block.preceq_trans hpre
              (hsg k
                (hwindowStart.trans (WeakSG.mem_latestWindow_lower_bound hk))
                (mem_latestWindow_lt hk) v hv hem)

/-- Covered action roots, live values, SG outputs, and timeout witnesses stay
below the destination head at the actual vote horizon. -/
theorem SettledBootstrapPreparedV4.actionOutputs_at_actual_vote_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start d : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hd : start ≤ d) (hhor : Protocol.vote_time S.E d ≤ rho.horizon) :
    ∀ r, base + S.hc.η_SG ≤ r →
      S.a r < Protocol.vote_time S.E (d + 1) →
      S.a r ≤ rho.horizon → ∀ w ∈ rho.honest, ∀ v ∈ rho.honest,
        Block.Preceq (Protocol.get_fg_root
          (actionStoreAt S rho w r).toHealing.toFG)
          (voteDutyHead S rho v d) ∧
        Block.Preceq (actionStoreAt S rho w r).live_confirmed
          (voteDutyHead S rho v d) ∧
        (rho.emits S w
          (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
          Block.Preceq (actionSGBlockAt S rho w r)
            (voteDutyHead S rho v d)) ∧
        (∀ T, fgConfirmationWitness S (actionStoreAt S rho w r) = some T →
          Block.Preceq T (voteDutyHead S rho v d)) := by
  intro r hr haction hactionHor w hw v hv
  have hcurrent := actionOutputs_at_actual_vote_aux_v4
    S adm hcom hboot hawake hfinality hd hhor hv r
      ((Nat.le_add_right base S.hc.η_SG).trans hr) haction hactionHor
  exact ⟨(hcurrent.2 hr w hw).1, (hcurrent.2 hr w hw).2.1,
    hcurrent.1 w hw, (hcurrent.2 hr w hw).2.2⟩

#print axioms SettledBootstrapPreparedV4.actionOutputs_at_actual_vote_core

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
