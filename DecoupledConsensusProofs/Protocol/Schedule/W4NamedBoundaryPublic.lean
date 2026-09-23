module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.W4NamedBoundaryCore
public import DecoupledConsensusProofs.Protocol.Schedule.W4HandoffBoundary

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# The selected named boundary from the public recovery inputs

This is the body of `movingChainHandoffRowCapBoundary_at_carrier_public`
through its named height-history, progress, and row arguments. The result
keeps the named row cap and the exact `M0` target threshold. No erased
derived-state comparison is requested or inferred.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface
open Protocol
open Proofs.Optimistic Proofs.HealingLemmas
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

private theorem w4nb_confirmation_time_mono
    (E : Env V) {s t : Slot} (h : s ≤ t) :
    Protocol.confirmation_time E s ≤ Protocol.confirmation_time E t :=
  Int.add_le_add_right (Protocol.proposal_time_mono E h) _

private theorem w4nb_vote_time_le_support_cutoff
    (E : Env V) (s : Slot) :
    Protocol.vote_time E s ≤ Protocol.support_cutoff E s := by
  rw [← Proofs.Optimistic.vote_time_add_delta]
  exact Int.le_add_of_nonneg_right E.Δ_pos.le

/-- The named selected boundary, with its real floor height. -/
theorem w4NamedHandoffBoundaryCore_at_openingCarrier_public
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hop : ProposerOpeningCarrierRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {q q0 : Round}
    (hq0 : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ q0)
    (hwindow : q0 + 3 * progressLag' gap delayExtra ≤ q)
    (hcarrier : ProposerOpeningCarrierAt S rho q)
    (hhor : Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤
      rho.horizon)
    {D : NamedBlock V}
    (hD : proposedBlockAt S rho (S.hc.opening_slot q + 1) = some D)
    {carrier : V} (hcarrierHon : carrier ∈ rho.honest)
    (hgenuine : GenuineConfirmationWith
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho carrier
          (S.hc.opening_slot q + 1)).cache)
      S.E S.hc (Proofs.Optimistic.confStore S rho carrier
        (S.hc.opening_slot q + 1))
      (S.hc.opening_slot q + 1) D.erase) :
    W4NamedHandoffBoundaryCore S rho q
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2))
      (derive_named S.E S.cfg D).h D := by
  have hrec : MultiProposerRecurrence S rho gap :=
    proposerRecurrence_of_openingCarrierRecurrence S hop
  have hq0q : q0 ≤ q := (Nat.le_add_right q0 _).trans hwindow
  have hq : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ q :=
    hq0.trans hq0q
  have hhor1 : Protocol.confirmation_time S.E
      (S.hc.opening_slot q + 1) ≤ rho.horizon :=
    (w4nb_confirmation_time_mono S.E
      (Nat.add_le_add_left (by decide : 1 ≤ 3)
        (S.hc.opening_slot q))).trans hhor
  have hvoteHor : Protocol.vote_time S.E
      (S.hc.opening_slot q + 1) ≤ rho.horizon :=
    (vote_time_le_confirmation_time S.E _).trans hhor1
  have hpropHor : Protocol.proposal_time S.E
      (S.hc.opening_slot q + 1) ≤ rho.horizon :=
    (Protocol.proposal_time_lt_vote_time S.E _).le.trans hvoteHor
  have hdeltaHor : Protocol.vote_time S.E
      (S.hc.opening_slot q + 1) + S.E.Δ ≤ rho.horizon := by
    rw [Proofs.Optimistic.vote_time_add_delta]
    exact (Protocol.support_cutoff_le_confirmation_time S.E
      (S.hc.opening_slot q + 1)).trans hhor1
  have hqHor : S.a q ≤ rho.horizon := by
    refine le_trans ?_ hhor1
    simpa only [opening_confirmation_time_eq_action] using
      w4nb_confirmation_time_mono S.E
        (Nat.le_succ (S.hc.opening_slot q))
  have hDrun : RunBlock S rho D :=
    Protocol.proposedBlock_runBlock S adm
      (Nat.succ_pos (S.hc.opening_slot q)) hcarrier.2.2.2.1 hpropHor hD
  have hheadEq : ∀ w ∈ rho.honest,
      voteDutyHead S rho w (S.hc.opening_slot q + 1) = D.erase :=
    w4BoundaryHeadEq_at_carrier S adm hcom hbelow hrec hdelay hpost hq
      hcarrier.2.2 hhor hD
  obtain ⟨w0, hw0⟩ := honest_nonempty_of_honestCommittees hcom
  have hhistory : CanonicalHeightSourceHistoryAt S rho q0 (q + 1) D := by
    refine canonicalHeightSourceHistoryAt_laterHead_after_SG_healing_named S adm
      hcom hbelow hrec hdelay hpost hq0
      (d := S.hc.opening_slot q + 1) ?_
      hdeltaHor hw0 hDrun (hheadEq w0 hw0).symm
      (w4NodeQ2_of_actionFGSource_all S rho)
    simpa only [Nat.add_sub_cancel] using
      Nat.le_refl (S.hc.opening_slot q + 1)
  have hLpos : 1 ≤ progressLag' gap delayExtra :=
    progressLag'_pos gap
  have hStrict : q0 + 2 * progressLag' gap delayExtra < q := by
    refine Nat.lt_of_lt_of_le ?_ hwindow
    have : 2 * progressLag' gap delayExtra <
        3 * progressLag' gap delayExtra := by
      have := Nat.mul_lt_mul_of_lt_of_le (Nat.lt_succ_self 2)
        (Nat.le_refl (progressLag' gap delayExtra)) hLpos
      simpa using this
    exact Nat.add_lt_add_left this q0
  have hcap0 : honestHMaxAt S rho (S.a q0) <
      (derive_named S.E S.cfg D).h :=
    w4_postGain_secondSlot_height_of_base S adm hcom hbelow hrec hdelay hpost
      ((Nat.le_add_right _ 3).trans hq0) hStrict
      hcarrier.2.2 hhor1 hD
  have hcapQ : honestHMaxAt S rho (S.a q) ≤
      (derive_named S.E S.cfg D).h + 1 :=
    w4BoundaryFrontierCap_at_carrier S adm hcom
      (AlignedRoundLemmas.honestQuorum_of_belowOneThird hbelow)
      hDrun hheadEq hhistory hcap0.le
  have hgstDeadline : rGST ≤ q0 :=
    ((Nat.le_succ rGST).trans
      (Handover.gstRound_succ_le_deadline S rho rGST gap)).trans
      ((Nat.le_add_right _ 3).trans hq0)
  have hprogAll :=
    heightProgress_public S hdelay adm hcom hbelow hpost hrec
  have hprog : EventualHeightProgressFrom S rho q0
      (progressLag' gap delayExtra) :=
    ⟨hprogAll.1, fun r hr => hprogAll.2 r (hgstDeadline.trans hr)⟩
  have hthreshold : honestHMaxAt S rho (S.a q0) <
      (derive_named S.E S.cfg D).h - 1 :=
    w4Threshold_of_progress_of_debtCap S adm hprog hwindow hqHor hcapQ
  have hheads := w4BoundaryHeads_of_carrierGenuine S adm hcom hbelow
    hrec hdelay hpost hq hhor hcarrierHon hgenuine
  refine {
    height := rfl
    run := hDrun
    processed := w4Processed_of_below_honest_heads S adm hDrun hheads
      (w4nb_vote_time_le_support_cutoff S.E (S.hc.opening_slot q + 2))
    targets := w4Targets_of_heightSourceHistory S adm hhistory hthreshold
    rowCapNamed := ?_
    carrierCeiling := w4CarrierCeiling_of_headEq S adm hcom hbelow hrec
      hdelay hpost hq hhor hheadEq
  }
  intro j a time ha hevent hemit hj hh hrow E hEerase hErun
  have hroot : E.root = D.root := by
    rw [← Proofs.NamedWire.erase_root E, ← Proofs.NamedWire.erase_root D, hEerase]
  have hED : E = D :=
    adm.toNamedRootCollisionFree.root_injective E D hErun hDrun E D
      (Or.inl (Proofs.NamedAncestry.named_self E))
      (Or.inr (Proofs.NamedAncestry.named_self D)) hroot
  rw [hED]
  exact w4RowsLe_of_heightSourceHistory S adm hhistory hthreshold
    ha hevent hemit hj hh hrow

#print axioms w4NamedHandoffBoundaryCore_at_openingCarrier_public

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
