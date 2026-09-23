module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.W4StableContinuationClear
public import DecoupledConsensusProofs.Protocol.Grades.W4StableRecordGrowthAfterGST
public import DecoupledConsensusProofs.Generic.W4StableContinuationCover

@[expose] public section

/-! # Stable-record continuation from the selected prepared-V4 records

The chosen proposal is strictly after the selected opening. Its SG-vote
window is covered by the prepared records, and its one lagged G2 duty has
post-cut delivery. No global grade-forming or unguarded cover premise is used.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace W4StableWrite

open Internal Execution Statements
open Proofs.HealingSurface Proofs.HealingSurface.Handover

variable {V : Type} [DecidableEq V] [Fintype V]

set_option maxHeartbeats 400000 in
-- The selected write elaborates the complete prepared-V4 viability argument.
/-- The exact after-GST field, with no residual hypothesis. -/
theorem stableRecordGrowth_afterGST_preparedClosed (S : Setup V) :
    ∀ rho rGST gap extra n,
      StrongRecoveryPrefix S rho rGST gap extra n →
      ∃ m, n ≤ m ∧ m ≤ n + gap ∧
        ∀ rho', WeakContinuation S rho rho' (n + gap) →
          ∀ continuationGap,
            ProposerOpeningCarrierRecurrence S rho' continuationGap →
              StableRecordGrowthFrom S rho' (S.hc.opening_slot m)
                (continuationGap + S.hc.η_SG - 1) := by
  intro rho rGST gap extra n hprefix
  obtain ⟨m, hmn, hmhi, hpack⟩ :=
    continuationV4Package S (preparedV4AwakeWindows_closed S)
      rho rGST gap extra n hprefix
  refine ⟨m, hmn, hmhi, ?_⟩
  intro rho' hcont continuationGap hrec
  obtain ⟨fresh, base, Pseed, cap, hphase, hboot, hfinality, hawake,
      hstartHor, hlatest⟩ := hpack rho' hcont
  have sch : ScheduleWellFormed S rho' := hcont.core.toNamedScheduleWellFormed
  have hcanon : StableRecordCanonicalFrom S rho'
      (Protocol.confirmation_time S.E (S.hc.opening_slot m)) :=
    Handover.stableRecordCanonicalFrom_of_phaseShift_latestFinality
      S sch hphase hlatest
  refine stableRecordGrowthFrom_of_openingWriteWithinAbove S hcont.core le_rfl hrec
    hphase.userConfirmation.latestMonotone
    hphase.userConfirmation.proposals hcanon ?_
  refine w4StableWriteWithinFromAbove_of_dutyCover S hcont.core sch ?_
  intro q hqpos hstartq hprop B hB hhorq0
  have hetapos : 0 < S.hc.η_SG :=
    lt_of_lt_of_le Nat.zero_lt_one S.hc.η_SG_ge_one
  have hsumpos : 0 < q + S.hc.η_SG :=
    Nat.lt_of_lt_of_le hetapos (Nat.le_add_left _ q)
  obtain ⟨e, hdeq⟩ : ∃ e : Round, q + S.hc.η_SG = e + 1 :=
    ⟨q + S.hc.η_SG - 1, (Nat.succ_pred_eq_of_pos hsumpos).symm⟩
  have hqd : q < e + 1 := hdeq ▸ Nat.lt_add_of_pos_right hetapos
  have hdle : e + 1 ≤ q + S.hc.η_SG := hdeq.ge
  have hhorq : S.a (e + 1) ≤ rho'.horizon := hdeq ▸ hhorq0
  refine ⟨e + 1, hqd, hdle, ?_⟩
  have hRpos : 0 < S.hc.R := lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two
  have hopenlt : S.hc.opening_slot q < S.hc.opening_slot (e + 1) :=
    Nat.mul_lt_mul_of_pos_right hqd hRpos
  have hs : S.hc.opening_slot m < S.hc.opening_slot (e + 1) :=
    hstartq.trans hopenlt
  have hdutyhor : dutyTime S (e + 1) ≤ rho'.horizon :=
    (dutyTime_le_action S (e + 1)).trans hhorq
  have hhorOpen : Protocol.confirmation_time S.E
      (S.hc.opening_slot (e + 1)) ≤ rho'.horizon := by
    simpa only [Proofs.HealingSurface.opening_confirmation_time_eq_action S
      (e + 1)] using hhorq
  have hqhor : S.a q ≤ rho'.horizon :=
    (Assembly.a_mono S (Nat.le_add_right q S.hc.η_SG)).trans hhorq0
  have hconfq : Protocol.confirmation_time S.E
      (S.hc.opening_slot q) ≤ rho'.horizon := by
    simpa only [Proofs.HealingSurface.opening_confirmation_time_eq_action S q]
      using hqhor
  have hreads := hphase.honestProposalReads (S.hc.opening_slot q) hstartq
    hconfq hprop
  have hprevLe : S.hc.opening_slot q ≤
      S.hc.opening_slot (e + 1) - 1 :=
    Nat.le_sub_one_of_lt hopenlt
  have hvotePrev : Protocol.vote_time S.E
      (S.hc.opening_slot (e + 1) - 1) ≤ rho'.horizon :=
    (voteTime_le_supportCutoff_mono S (Nat.sub_le _ 1)).trans hdutyhor
  have hvoteOpen : Protocol.vote_time S.E
      (S.hc.opening_slot (e + 1)) ≤ rho'.horizon :=
    (voteTime_le_supportCutoff_mono S (Nat.le_refl _)).trans hdutyhor
  intro v hv
  have hviable := proposalViableAtDuty_of_package_and_head S hcont.core
    hcont.committees hboot hawake hfinality hs hdutyhor hhorOpen hv
    (dutyHeadWitnessAll_closed S rho' hcont.core (e + 1)
      (Nat.lt_of_le_of_lt (Nat.zero_le q) hqd) v hv)
    (hreads.vote B hB (S.hc.opening_slot (e + 1) - 1) hprevLe
      hvotePrev v hv)
    (hreads.vote B hB (S.hc.opening_slot (e + 1))
      (Nat.le_of_lt hopenlt) hvoteOpen v hv)
  refine dutyCoverAt_of_viable_and_localG2 S hviable ?_
  have hg := w4_preparedLocalG2_at_selectedDuty S hcont.core
    hcont.committees hboot hawake hfinality hstartq hprop hB hphase
    hhorq0 v hv
  rwa [hdeq] at hg

#print axioms stableRecordGrowth_afterGST_preparedClosed

/-- The exact public field from a GST-zero branch and the proved continuation
branch. The GST-zero input has the frozen field's exact statement. -/
theorem stableRecordGrowth_of_gstZeroPreparedClosed (S : Setup V)
    (hgst : ∀ rho, WeakGenesis S rho →
      ∀ gap, ProposerOpeningCarrierRecurrence S rho gap →
        StableRecordGrowthFrom S rho 0 (gap + S.hc.η_SG - 1)) :
    StableRecordGrowth S :=
  stableRecordGrowth_of_pins S hgst
    (stableRecordGrowth_afterGST_preparedClosed S)

#print axioms stableRecordGrowth_of_gstZeroPreparedClosed

end W4StableWrite
end Proofs
end DecoupledConsensusModel

end
