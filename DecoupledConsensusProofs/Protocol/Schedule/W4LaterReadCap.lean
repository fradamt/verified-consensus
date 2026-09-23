module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.W4NamedBoundaryPublic
public import DecoupledConsensusProofs.Protocol.Schedule.W4CarrierRecord
public import DecoupledConsensusProofs.Execution.W4HealedTwoSlotHandoff

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# The selected handoff frontier cap at the later vote read

The named boundary is available through the support cutoff of the opening
plus two slot. Its height history gives the past height gates at that cutoff,
and its processed field keeps the selected endpoint in every honest store.
The time-general frontier bound is then read at the earlier vote instant and
converted from the public inclusive frontier to the strict event prefix that
the prepared adoption theorem consumes.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.NamedRecoveryRead
open Protocol Proofs.HealingLemmas
open Proofs.Optimistic Proofs.HealingLemmas
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

private theorem w4cap_confirmation_time_mono
    (E : Env V) {s t : Slot} (h : s ≤ t) :
    Protocol.confirmation_time E s ≤ Protocol.confirmation_time E t :=
  Int.add_le_add_right (Protocol.proposal_time_mono E h) _

private theorem w4cap_openingSlot_two_after
    (S : Setup V) {d m : Round} (hdm : d + 1 ≤ m) :
    S.hc.opening_slot d + 2 ≤ S.hc.opening_slot m := by
  have hstep : S.hc.opening_slot d + 2 ≤ S.hc.opening_slot (d + 1) := by
    simp only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add_left S.hc.R_ge_two (d * S.hc.R)
  exact hstep.trans (Nat.mul_le_mul_right S.hc.R hdm)

/-- At the selected handoff, the honest frontier at the strict prefix of the
opening-plus-two vote read is at most one above the selected endpoint. -/
theorem w4LaterReadFrontierCap_at_openingCarrier_public
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
    (hD : proposedBlockAt S rho (S.hc.opening_slot q + 1) = some D) :
    honestHMaxBeforeIndex S rho
        (strictEventIndex rho
          (Protocol.vote_time S.E (S.hc.opening_slot q + 2))) ≤
      (derive_named S.E S.cfg D).h + 1 := by
  classical
  have hrec : MultiProposerRecurrence S rho gap :=
    proposerRecurrence_of_openingCarrierRecurrence S hop
  have hq0q : q0 ≤ q := (Nat.le_add_right q0 _).trans hwindow
  have hq : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ q :=
    hq0.trans hq0q
  have hdeadline2Q :
      fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ q :=
    (Nat.add_le_add_left (by decide : (2 : Nat) ≤ 3) _).trans hq
  have hhor1 : Protocol.confirmation_time S.E
      (S.hc.opening_slot q + 1) ≤ rho.horizon :=
    (w4cap_confirmation_time_mono S.E
      (Nat.add_le_add_left (by decide : (1 : Nat) ≤ 3)
        (S.hc.opening_slot q))).trans hhor
  have hpropHor : Protocol.proposal_time S.E
      (S.hc.opening_slot q + 1) ≤ rho.horizon :=
    (proposal_time_lt_vote_time S.E _).le.trans
      ((vote_time_le_confirmation_time S.E _).trans hhor1)
  have hdeltaHor : Protocol.vote_time S.E
      (S.hc.opening_slot q + 1) + S.E.Δ ≤ rho.horizon := by
    rw [Proofs.Optimistic.vote_time_add_delta]
    exact (Protocol.support_cutoff_le_confirmation_time S.E _).trans hhor1
  have hqHor : S.a q ≤ rho.horizon := by
    refine le_trans ?_ hhor1
    simpa only [opening_confirmation_time_eq_action] using
      w4cap_confirmation_time_mono S.E (Nat.le_succ (S.hc.opening_slot q))
  have hrunD : RunBlock S rho D :=
    Protocol.proposedBlock_runBlock S adm
      (Nat.succ_pos (S.hc.opening_slot q)) hcarrier.2.2.2.1 hpropHor hD
  have hheadEq : ∀ w ∈ rho.honest,
      voteDutyHead S rho w (S.hc.opening_slot q + 1) = D.erase :=
    w4BoundaryHeadEq_at_carrier S adm hcom hbelow hrec hdelay hpost hq
      hcarrier.2.2 hhor hD
  have hdeadlineOpen : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤
      S.hc.opening_slot q := by
    simpa only [Protocol.HealConfig.opening_slot] using
      Nat.mul_le_mul_right S.hc.R hdeadline2Q
  have hreads : ∀ v ∈ rho.honest,
      Block.Preceq
          (namedConfirmationAnchor S
            (confirmationInputRead S rho v (S.hc.opening_slot q + 1)))
          D.erase ∧
        D.erase ∈
          confTree (confirmationInputRead S rho v
            (S.hc.opening_slot q + 1)).st.core :=
    honestProposal_confirmationReadFacts_after_SG_healing_named_slot
      S adm hcom hbelow hrec hdelay hpost hdeadlineOpen hhor1
      hcarrier.2.2.2.1 hD
  have hdeadlineTwo : S.hc.opening_slot
        (fgSafetyProgressDeadline S rho rGST gap delayExtra) + 2 ≤
      S.hc.opening_slot q + 1 :=
    (w4cap_openingSlot_two_after S (Nat.le_of_succ_le hdeadline2Q)).trans
      (Nat.le_succ (S.hc.opening_slot q))
  have hgenuine := w4_preparedGenuineSelection_of_namedFacts
    S adm hcom hbelow hrec hdelay hpost hdeadlineTwo hhor1 hrunD hheadEq hreads
  obtain ⟨carrier, hcarrierHon⟩ := honest_nonempty_of_honestCommittees hcom
  have hboundary :=
    w4NamedHandoffBoundaryCore_at_openingCarrier_public S adm hcom hbelow
      hop hdelay hpost hq0 hwindow hcarrier hhor hD hcarrierHon
      (hgenuine carrier hcarrierHon)
  have hhistory : CanonicalHeightSourceHistoryAt S rho q0 (q + 1) D := by
    refine canonicalHeightSourceHistoryAt_laterHead_after_SG_healing_named S adm
      hcom hbelow hrec hdelay hpost hq0
      (d := S.hc.opening_slot q + 1) ?_
      hdeltaHor hcarrierHon hrunD (hheadEq carrier hcarrierHon).symm
      (w4NodeQ2_of_actionFGSource_all S rho)
    simpa only [Nat.add_sub_cancel] using
      Nat.le_refl (S.hc.opening_slot q + 1)
  have hLpos : 1 ≤ progressLag' gap delayExtra := progressLag'_pos gap
  have hStrict : q0 + 2 * progressLag' gap delayExtra < q := by
    refine Nat.lt_of_lt_of_le ?_ hwindow
    have hmul : 2 * progressLag' gap delayExtra <
        3 * progressLag' gap delayExtra := by
      have := Nat.mul_lt_mul_of_lt_of_le (Nat.lt_succ_self 2)
        (Nat.le_refl (progressLag' gap delayExtra)) hLpos
      simpa using this
    exact Nat.add_lt_add_left hmul q0
  have hcap0 : honestHMaxAt S rho (S.a q0) <
      (derive_named S.E S.cfg D).h :=
    w4_postGain_secondSlot_height_of_base S adm hcom hbelow hrec hdelay hpost
      ((Nat.le_add_right _ 3).trans hq0) hStrict hcarrier.2.2 hhor1 hD
  have hcutAction : Protocol.support_cutoff S.E
      (S.hc.opening_slot q + 2) ≤ S.a (q + 1) := by
    calc
      Protocol.support_cutoff S.E (S.hc.opening_slot q + 2) ≤
          Protocol.confirmation_time S.E (S.hc.opening_slot q + 2) :=
        Protocol.support_cutoff_le_confirmation_time S.E _
      _ ≤ Protocol.confirmation_time S.E (S.hc.opening_slot (q + 1)) :=
        w4cap_confirmation_time_mono S.E
          (openingSlot_add_two_le_openingSlot_of_lt S (Nat.lt_succ_self q))
      _ = S.a (q + 1) := opening_confirmation_time_eq_action S (q + 1)
  have hgates : Protocol.PastHonestHeightGatesBelow S rho
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) D :=
    w4cr_pastHeightGates_of_history S adm hhistory hcap0.le hcutAction
  have hheld : ∀ v ∈ rho.honest,
      D ∈ (rho.stateBeforeTime S
        (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) v).st.bodies := by
    intro v hv
    unfold Run.stateBeforeTime
    rw [stateBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed]
    exact hboundary.processed v hv
  have hvoteCut : Protocol.vote_time S.E (S.hc.opening_slot q + 2) <
      Protocol.support_cutoff S.E (S.hc.opening_slot q + 2) := by
    rw [← Proofs.Optimistic.vote_time_add_delta]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  have hfrontierAt : honestHMaxAt S rho
      (Protocol.vote_time S.E (S.hc.opening_slot q + 2)) ≤
      (derive_named S.E S.cfg D).h + 1 :=
    w4HonestFrontierAt_le_succ_of_heightGates S adm hcom
      (AlignedRoundLemmas.honestQuorum_of_belowOneThird hbelow)
      hgates hheld hvoteCut
  calc
    honestHMaxBeforeIndex S rho
        (strictEventIndex rho
          (Protocol.vote_time S.E (S.hc.opening_slot q + 2))) ≤
        honestHMaxBeforeIndex S rho
          (inclusiveEventIndex rho
            (Protocol.vote_time S.E (S.hc.opening_slot q + 2))) :=
      honestHMaxBeforeIndex_mono S rho
        (strictEventIndex_le_inclusiveEventIndex rho _)
    _ = honestHMaxAt S rho
          (Protocol.vote_time S.E (S.hc.opening_slot q + 2)) :=
      (honestHMaxAt_eq_honestHMaxBeforeIndex S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed _).symm
    _ ≤ (derive_named S.E S.cfg D).h + 1 := hfrontierAt

#print axioms w4LaterReadFrontierCap_at_openingCarrier_public

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
