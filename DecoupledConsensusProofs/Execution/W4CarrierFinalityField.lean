module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.W4CarrierRecord
public import DecoupledConsensusProofs.Protocol.Schedule.W4NamedExecution
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.W4CarrierCaughtUpPrepared
public import DecoupledConsensusProofs.Generic.W4D2OpeningCarrierFinality
public import DecoupledConsensusProofs.Protocol.Grades.W4D2PreparedFinality
public import DecoupledConsensusProofs.ModelVocabulary.Execution.Setup

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Selected carrier finality field consumers

This leaf keeps the selected opening-carrier data explicit. The cap seed is
the selected post-gain height fact, and the source supplier is the guarded
prepared predecessor fact. The opening-carrier result is kept separate from
the stronger all-carrier `W4CarrierGradedChainFrom` contract.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.NamedRecoveryRead
open Protocol Proofs.HealingLemmas
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}





private theorem w4cfield_deadline_le_selected
    (S : Setup V) {rho : Run V} {rGST gap q : Round}
    (hlate : fgSafetyProgressDeadline S rho rGST gap delayExtra +
      3 * progressLag' gap delayExtra + 1 ≤ q) :
    fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ q := by
  have hL : 0 < progressLag' gap delayExtra := progressLag'_pos gap
  have hstep : ∀ d L : Nat, 0 < L → d + 3 ≤ d + 3 * L + 1 := by
    intro d L hL'
    have hmul : 3 * 1 ≤ 3 * L :=
      Nat.mul_le_mul_left 3 (Nat.succ_le_iff.mpr hL')
    have h3 : 3 ≤ 3 * L + 1 :=
      (by decide : (3 : Nat) ≤ 3 * 1 + 1) |>.trans
        (Nat.add_le_add_right hmul 1)
    exact Nat.add_le_add_left h3 d
  exact hstep _ _ hL |>.trans hlate

private theorem w4cfield_round_bound
    (S : Setup V) {rho : Run V} {rGST gap q r : Round}
    (hlate : fgSafetyProgressDeadline S rho rGST gap delayExtra +
      3 * progressLag' gap delayExtra + 1 ≤ q)
    (hqr : q + 2 < r) :
    fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ r := by
  exact (w4cfield_deadline_le_selected S hlate).trans
    ((Nat.le_add_right q 2).trans hqr.le)









/-! ## The selected first-half composer -/

/-- Compose the quiet and caught-up checkpoint arms into the selected first-half
pin. The caught-up producer is the direct named coverage route; it does not
use the older parent-store and `chainRows` residuals. -/
theorem w4_firstHalfField_of_arms
    (S : Setup V) {rho : Run V}
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap q : Round}
    (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpostGST : S.E.t_GST ≤ S.a rGST)
    (hqLate : fgSafetyProgressDeadline S rho rGST gap delayExtra +
      3 * progressLag' gap delayExtra + 1 ≤ q)
    (hpostQ : S.E.t_GST ≤ S.a q)
    (hexec : CanonicalSuffixExecutionPrepared S rho q)
    (_hchainFrom : MovingChainAtCarrierFrom S rho q)
    (_hprogress : EventualHeightProgressFrom S rho q
      (progressLag' gap delayExtra))
    (_hnotLost : ∀ r : Round, q + 2 < r →
      S.E.proposer (S.hc.opening_slot (r - 1)) ∈ rho.honest →
      Protocol.confirmation_time S.E (S.hc.opening_slot r + 2) ≤ rho.horizon →
      ¬ LostRoundAt S rho r) :
    W4PreparedSelectedFirstHalfAt S rho q := by
  have hparents := w4_parentEqualities_of_canonicalSuffixFrom S adm
    hexec.canonicalSuffixFrom
  intro r C End hqr hopening hround hchain hgrade hnl hnlPrev
    hafterPrev hpostPrev hpostR habove hnj hone
    Pprev P0 P1 hPprev hPprevRun hP0 hP1 hparent hP1run hprevHor hpred
    hheight hLive hanchor hsource
  have hr := w4cfield_round_bound S hqLate hqr
  have hdeadline := w4cfield_deadline_le_selected S hqLate
  have hPrevParent : NamedBlock.Preceq Pprev P0.parent :=
    w4cr_previousOpening_namedPreceq_openingParent S adm hcom hbelow hrec
      hdelay hpostGST hr hopening.2.2 hround.inHorizon hpred hPprev hP0
  have hhistPrev := w4_quietPreviousHistory_of_spine S adm hcom hbelow
    (rGST := rGST) (gap := gap) (extra := delayExtra)
    (q0 := q) (r := r) hrec hdelay hpostGST hdeadline hqr hprevHor hpred
    hPprevRun hPprev
  have haboveP0 : honestHMaxAt S rho (S.a q) <
      (Protocol.derive_named S.E S.cfg P0).h := by
    have hcanon : P0 = canonicalProposal S rho (S.hc.opening_slot r) := by
      have hspec := canonicalProposal_spec S rho (S.hc.opening_slot r)
      rw [hP0] at hspec
      exact Option.some.inj hspec
    rw [hcanon]
    simpa only [carrierOpeningHeight] using habove
  have hcheckpoint : ∀ P0' P1' : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r) = some P0' →
      proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1' →
      NamedJustifiedAt S.E S.cfg P1'
          (Protocol.derive_named S.E S.cfg P0').T_h
          (Protocol.derive_named S.E S.cfg P0').h ∨
        ((Protocol.derive_named S.E S.cfg P1').h =
            (Protocol.derive_named S.E S.cfg P0').h ∧
          (Protocol.derive_named S.E S.cfg P1').T_h =
            (Protocol.derive_named S.E S.cfg P0').T_h) := by
    intro P0' P1' hP0' hP1'
    have hP0eq : P0' = P0 := proposedBlockAt_unique S rho
      (S.hc.opening_slot r) hP0' hP0
    have hP1eq : P1' = P1 := proposedBlockAt_unique S rho
      (S.hc.opening_slot r + 1) hP1' hP1
    subst P0'
    subst P1'
    rcases hheight with hbelowHeight | hhighHeight
    · have hquiet := w4_quietRows_of_selectedCarrierSpine S adm hcom hbelow
        hrec hdelay hpostGST hdeadline hqr hround hP1 hparent hP1run hPprevRun
        hPprev hprevHor hpred haboveP0 hbelowHeight hLive hanchor
      exact Or.inr (namedPlusOne_quiet_of_faultyOnlyRows S hbelow hparent
        hquiet.1 hquiet.2)
    · exact w4_caughtUp_checkpointReady_of_source S adm hbelow hdelay hqr hround
        hP0 hP1 hparent hPprev hPprevRun hPrevParent hhighHeight
        (hnj P0 hP0) hhistPrev haboveP0 hprevHor hpostPrev hsource
  have habove' : ∀ P0' : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r) = some P0' →
      honestHMaxAt S rho (S.a q) <
        (Protocol.derive_named S.E S.cfg P0').h := by
    intro P0' hP0'
    have hP0eq : P0' = P0 := proposedBlockAt_unique S rho
      (S.hc.opening_slot r) hP0' hP0
    simpa only [hP0eq] using haboveP0
  have hlock : ∀ P0' : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r) = some P0' →
      ∀ v ∈ rho.honest,
        SuccessorTargetLockAlignmentAt
          (rho.stateBeforeTime S (S.a r) v).Λ
          (actionAttestationAt S rho v r).finality_pair
          (Protocol.derive_named S.E S.cfg P0').h
          (Protocol.derive_named S.E S.cfg P0').T_h.root := by
    intro P0' hP0'
    exact CanonicalRegimeRoundAt.successorTargetLockAlignment_of_aboveBoundary
      S adm hbelow hround hP0' (habove' P0' hP0')
  have hrows : ∀ P0' : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r) = some P0' →
      ∀ v ∈ rho.honest,
        (actionAttestationAt S rho v r).height_pair =
          NamedHeightPair.vote
            (Protocol.derive_named S.E S.cfg P0').h
            (Protocol.derive_named S.E S.cfg P0').T_h.root false := by
    intro P0' hP0'
    exact carrierRows_exactTargets_named S adm hround hP0'
      (habove' P0' hP0') (hnj P0' hP0')
      (hlock P0' hP0')
  have hcarry := carrierPlusTwoCarriesRoundRows_named S adm hround hpostR
  have hactionHead : ∀ P0' P1' : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r) = some P0' →
      proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1' →
      ∀ v ∈ rho.honest, actionHeadAt S rho v r = P1'.erase := by
    intro P0' P1' hP0' hP1'
    have hP1eq : P1' = P1 := proposedBlockAt_unique S rho
      (S.hc.opening_slot r + 1) hP1' hP1
    subst P1'
    have hheadAll := w4CarrierActionHeadPin_pinFree S adm hcom hbelow hrec hdelay
      (rGST := rGST) hpostGST hround hchain hpostPrev
      (by
        have hdeadline :
            S.hc.opening_slot
                (fgSafetyProgressDeadline S rho rGST gap
                  delayExtra + 2) ≤ S.hc.opening_slot r + 1 := by
          have hfixed : fgSafetyProgressDeadline S rho
              rGST gap delayExtra + 2 ≤ q := by
            exact (Nat.add_le_add_left (by decide : (2 : Nat) ≤ 3)
              (fgSafetyProgressDeadline S rho rGST gap
                delayExtra)).trans
              (w4cfield_deadline_le_selected S hqLate)
          exact (Nat.mul_le_mul_right S.hc.R
            (hfixed.trans ((Nat.le_add_right q 2).trans hqr.le))).trans
            (Nat.le_add_right _ 1)
        exact hdeadline)
      (hpostR.trans ((Protocol.proposal_time_lt_vote_time S.E _).le.trans
        (Protocol.vote_time_mono_slots S.E (Nat.le_succ _))))
      (by
        rw [w4cr_interiorCutoff_eq_action S r]
        exact (w4_actionRead_le_horizon S hround))
    exact hheadAll P1 hP1
  have hfield : CarrierFinalityFirstHalfAt S rho r C := by
    refine
      { grade := hgrade
        gradeBelowOpening := movingChainFloor_preceq_opening S hbelow hchain hnl
        plusOneParent := ?_
        checkpointReady := hcheckpoint
        plusTwoParent := ?_
        actionCoverage := ?_
        rowsCarriedAtPlusTwo := hcarry
        targetRows := hrows
        actionHeadEq := hactionHead }
    · intro P0' P1' hP0' _hP1'
      exact (hparents r hround).1 P0' hP0'
    · intro P1' _hP2' hP1' _hP2'
      exact (hparents r hround).2 P1' hP1'
    · intro P0' P2' hP0' hP2' v hv
      exact ⟨Or.inr (hcarry P2' hP2' v hv),
        Or.inl (hrows P0' hP0' v hv)⟩
  exact hfield

#print axioms w4_firstHalfField_of_arms

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
