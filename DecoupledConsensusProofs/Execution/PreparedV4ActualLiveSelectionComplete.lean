module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.PreparedV4ActualLiveSelection

@[expose] public section

/-! # Complete prepared V4 live selection at an actual vote -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem protectedVoteSlot_of_heads_actual_v4
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {d : Slot} (hd : 0 < d)
    (hhor : Protocol.vote_time S.E d ≤ rho.horizon) {B : Block V}
    (hheads : ∀ x ∈ rho.honest, Block.Preceq B (voterHeadAt S rho x d)) :
    ProtectedVoteSlot S rho d B := by
  refine ⟨hheads, ?_⟩
  intro x hx hxc
  obtain ⟨X, hX, hXrun, hXemit⟩ :=
    WeakGoldfish.voterHead_runBlock_and_emits S adm hx hd hxc hhor
  exact ⟨X, by simpa only [hX] using hheads x hx, hXrun, hXemit⟩

private theorem actionTime_lt_nextVote_of_lt_confirmation_actual_v4
    (S : Setup V) {r : Round} {s : Slot}
    (h : S.a r < Protocol.confirmation_time S.E s) :
    S.a r < Protocol.vote_time S.E (s + 1) := by
  exact (action_time_lt_proposal_of_lt_previous_confirmation
    S (s := s + 1) (Nat.zero_lt_succ s)
      (by simpa only [Nat.add_sub_cancel] using h)).trans
        (proposal_time_lt_vote_time S.E (s + 1))

/-- The actual-vote live-selection bound, including the equality case
`d = start`. -/
theorem SettledBootstrapPreparedV4.liveConfirmedSelection_at_actual_vote_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start q d : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hd : start ≤ d) (hhor : Protocol.vote_time S.E d ≤ rho.horizon)
    (hq : S.hc.opening_slot (base + S.hc.η_SG) ≤ q)
    (hqhor : Protocol.confirmation_time S.E q ≤ rho.horizon) (hqd : q < d)
    {w : V} (hw : w ∈ rho.honest) :
    ProtectedVoteSlot S rho d
      (Protocol.update_confirmation_with
        (NamedProfile.gradeContract
          (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
        S.E S.hc (confStore S rho w q) q).live_confirmed := by
  by_cases hstrict : start < d
  · exact SettledBootstrapPreparedV4.liveConfirmedSelection_at_actual_vote_after_start_core
      S adm hcom hboot hawake hfinality hstrict hhor hq hqhor hqd hw
  have heq : d = start := Nat.le_antisymm (Nat.le_of_not_gt hstrict) hd
  subst d
  have hcutpos : 0 < base + S.hc.η_SG :=
    Nat.zero_lt_of_lt (Nat.add_lt_add_left S.hc.η_SG_ge_one base)
  have hstartPos : 0 < start :=
    (Nat.mul_pos hcutpos
      (lt_of_lt_of_le (by decide : 0 < 2) S.hc.R_ge_two)).trans_le hboot.settled
  have hmajority := honestWeightMajority_of_finiteWindowsFrom
    S hawake hcutpos hq (Nat.le_succ q) hqhor
  have hseed : ProtectedVoteSlot S rho start P.erase :=
    ⟨hboot.seedAll, hboot.seed.cone⟩
  have hspan : base ≤ base + S.hc.η_SG - S.hc.η_SG :=
    Nat.le_sub_of_add_le (Nat.le_refl _)
  obtain ⟨hlegacyActionRoots, -⟩ :=
    WeakJoint.legacyRootCallbacks_of_finiteBootstrap_complete
      S adm (last := q) hboot.oldRows hfinality hboot.frontierSeed hboot.fgAll
  have hsources (x : V) (hx : x ∈ rho.honest) :=
    WeakJoint.actionSources_preceq_of_priorConfirmations_and_historyCut
      S adm hmajority (base := base) (cut := base + S.hc.η_SG)
        (s := q) (D := voterHeadAt S rho x start) hspan
        (fun r hr hrcut _ u hu hemit =>
          Block.preceq_trans (hboot.sgBoot r hr hrcut u hu hemit)
            (hboot.seedAll x hx))
        (fun z hz hzq u hu B hB =>
          Block.preceq_trans (hboot.confBoot z hz (hzq.trans hqd) u hu B hB)
            (hboot.seedAll x hx))
        (fun r hr ht u hu C a hC hJ ha hemit hold hpair hT =>
          Block.preceq_trans
            (hlegacyActionRoots r hr ht u hu C a hC hJ ha hemit hold hpair hT)
            (hboot.seedAll x hx))
        (by
          intro r hr hrpos ht hsg hroots
          have hactionHor : S.a r ≤ rho.horizon :=
            (action_le_supportCutoff_of_lt_nextVote S ht).trans
              ((support_cutoff_mono S.E (Nat.le_succ q)).trans (by
                simpa only [Protocol.confirmation_time_eq_support_cutoff_succ]
                  using hqhor))
          have hawakeR := hawake r hr
            ((Assembly.a_mono S (Nat.sub_le r 1)).trans hactionHor)
          apply WeakJoint.actionGradeFormationAt_of_awakeWindowMajority
            S adm hrpos hawakeR
          intro p hp
          apply relativeGradeCarrierAt_of_awakeWindowMajority
            S adm hrpos hawakeR
          exact WeakJoint.relativeCarrierWindowAt_of_awakeWindowHistory_w
            S adm
              (NamedOutageClosure.healthyWindowDelivery_after_gst S rho adm)
              (le_refl _) (le_refl _) hrpos
              (hspan.trans (Nat.sub_le_sub_right hr S.hc.η_SG))
              (fun k hk _ => hboot.basePost.trans (Assembly.a_mono S hk))
              hawakeR hsg hroots p hp)
  let contract := NamedProfile.gradeContract
    (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache
  by_cases hg : confEligible S.E (confStore S rho w q) q
      (confWalkWith contract S.E S.hc (confStore S rho w q) q) = true
  · apply hseed.of_ancestor
    exact hboot.confBoot q hq hqd w hw _ ⟨rfl, hg⟩
  · rw [update_confirmation_with_live_confirmed, if_neg hg]
    apply protectedVoteSlot_of_heads_actual_v4 S adm hstartPos hhor
    intro x hx
    change Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w
          (Protocol.confirmation_time S.E q)).toHealing.toFG)
      (voterHeadAt S rho x start)
    have hread : S.a (base + S.hc.η_SG) ≤
        Protocol.confirmation_time S.E q := by
      change Protocol.confirmation_time S.E
        (S.hc.opening_slot (base + S.hc.η_SG)) ≤ _
      rw [Protocol.confirmation_time_eq_support_cutoff_succ,
        Protocol.confirmation_time_eq_support_cutoff_succ]
      exact support_cutoff_mono S.E (Nat.add_le_add_right hq 1)
    rcases WeakFG.fgRoot_confirmationWitness_at_read
        S adm hmajority hw (Protocol.confirmation_time S.E q) with
      hgen | ⟨C, hC, hJ, a, ta, ha, hemit, ht, hpair, hT⟩
    · rw [hgen]
      exact Protocol.preceq_genesis _
    · by_cases hold : a.round < base + S.hc.η_SG
      · exact Block.preceq_trans
          (WeakJoint.oldFGRoot_preceq_of_finiteBootstrap_at_read S adm
            hboot.oldRows hfinality hboot.frontierSeed hboot.fgAll hw
              ((min_le_left _ _).trans hread) hC hJ ha hemit hold hpair hT)
          (hboot.seedAll x hx)
      · have htime : ta = S.a a.round := (emits_attest_shape S hemit).2
        have hat : S.a a.round < Protocol.vote_time S.E (q + 1) := by
          exact actionTime_lt_nextVote_of_lt_confirmation_actual_v4 S (by
            rw [← htime]
            exact ht)
        have hrecent : base + S.hc.η_SG ≤ a.round := Nat.le_of_not_gt hold
        exact ((((hsources x hx) a.round
          ((Nat.le_add_right base S.hc.η_SG).trans hrecent) hat).2 hrecent)
            a.val_index ha).2 _ hT

#print axioms SettledBootstrapPreparedV4.liveConfirmedSelection_at_actual_vote_core

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
