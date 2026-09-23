module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.W4D2OpeningCarrierFinality
public import DecoupledConsensusProofs.Protocol.Grades.W4FKPreparedFrame

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem w4d2ActionFGSourceEqLive
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (hrpos : 0 < r) (hhor : S.a r ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest)
    (hanchorAt : Block.Preceq
      (PhaseGrades.nodeAnchor S (actionReadAt S rho v r) r)
      (actionStoreAt S rho v r).live_confirmed)
    (hclearAt : PhaseGrades.nodeClear S (actionReadAt S rho v r) r
      (actionStoreAt S rho v r).live_confirmed = true)
    {X : Block V}
    (hsource : actionFGSource S (actionReadAt S rho v r) = some X) :
    X = (actionStoreAt S rho v r).live_confirmed := by
  have hround : S.hc.round_of (actionReadAt S rho v r).st.core.toHealing.s = r := by
    simpa only [actionStoreAt, Protocol.Store.toHealing] using
      actionStoreAt_round S rho v r
  have hsource' : PhaseGrades.nodeFGSource S (actionReadAt S rho v r) r = some X := by
    simpa only [actionFGSource, PhaseGrades.nodeFGSource, hround] using hsource
  cases hA : PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r with
  | none =>
      have hQ2 : Protocol.grade2_block_with
          (NamedProfile.gradeContract (actionReadAt S rho v r).cache) S.E S.hc
          (actionReadAt S rho v r).st.core.toHealing r = none := hA
      rw [PhaseGrades.nodeFGSource, Protocol.fg_source_with.eq_def, hQ2] at hsource'
      simp only [reduceCtorEq] at hsource'
  | some A =>
      have hQ2 : Protocol.grade2_block_with
          (NamedProfile.gradeContract (actionReadAt S rho v r).cache) S.E S.hc
          (actionReadAt S rho v r).st.core.toHealing r = some A := hA
      have hAlive : Block.Preceq A (actionStoreAt S rho v r).live_confirmed :=
        Block.preceq_trans
          (actionQ2_preceq_actionAnchor S adm.toNamedAdmissibleCore hv hrpos hhor hA)
          hanchorAt
      have hwalk : Protocol.deepest_clear (some A)
          (actionReadAt S rho v r).st.core.toHealing.live_confirmed
          ((NamedProfile.gradeContract (actionReadAt S rho v r).cache).read S.E S.hc
            (actionReadAt S rho v r).st.core.toHealing r).clear =
          some (actionStoreAt S rho v r).live_confirmed :=
        deepest_clear_eq_tip (by simpa using hAlive) hclearAt
      rw [PhaseGrades.nodeFGSource, Protocol.fg_source_with.eq_def, hQ2] at hsource'
      simp only [hwalk, Option.some.injEq] at hsource'
      exact hsource'.symm

/-- The field-level regime pin used by the prepared D2 twin. -/
def W4CanonicalRegimeRoundFactsPinGraded
    (S : Setup V) (rho : Run V) (q0 : Round) : Prop :=
  ∀ (r : Round) (C End : Block V),
    CanonicalRegimeRoundExecutionFactsAt S rho q0 r →
    MovingChainAtCarrierFor S rho q0 r C End →
    NamedGradeFormsAt S rho r C →
    ¬ LostRoundAt S rho r →
    CanonicalRegimeRoundAt S rho q0 r

theorem w4CanonicalRegimeRoundAt_of_facts_and_chainFor_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbot : BelowOneThird S rho.honest)
    {q0 r : Round} {C End : Block V}
    (hfacts : CanonicalRegimeRoundExecutionFactsAt S rho q0 r)
    (hchain : MovingChainAtCarrierFor S rho q0 r C End)
    (hnl : ¬ LostRoundAt S rho r)
    (hpost : S.E.t_GST ≤ S.a (r - 1))
    (hforms : NamedGradeFormsAt S rho r C) :
    CanonicalRegimeRoundAt S rho q0 r := by
  have hq0r : q0 < r := w4fkRoundLtOfAfterBoundary S hfacts.afterBoundary
  have hrpos : 0 < r := Nat.zero_lt_of_lt hq0r
  have hconf0 : Protocol.confirmation_time S.E
      (S.hc.opening_slot r) ≤ rho.horizon := by
    refine le_trans ?_ hfacts.inHorizon
    rw [Protocol.confirmation_time_eq_support_cutoff_succ,
      Protocol.confirmation_time_eq_support_cutoff_succ]
    exact Proofs.Optimistic.support_cutoff_mono S.E
      (Nat.add_le_add_right (Nat.le_add_right (S.hc.opening_slot r) 2) 1)
  have hactionHor : S.a r ≤ rho.horizon := by
    simpa only [Setup.a, Protocol.a_eq_confirmation_time] using hconf0
  have hcut : S.hc.Γ_neg1 S.E.Δ r ≤ rho.horizon := by
    have hr1 : r - 1 + 1 = r := Nat.succ_pred_eq_of_pos hrpos
    have hlt := next_Γ_neg1_lt_action S (r - 1)
    rw [hr1] at hlt
    exact hlt.le.trans hactionHor
  obtain ⟨P, hP⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot r)
  have hfloor := hchain.floorFields hnl
  have hframe := movingChainPreparedFrameAt_of_fields S adm hbot
    hfacts.afterBoundary hfacts.inHorizon hfacts.openingLive hchain hpost
  have hactive : ∀ v ∈ rho.honest,
      C ∈ PhaseGrades.filteredTree (actionReadAt S rho v r) := by
    intro v hv
    have hheal := gradeFloor_active_everywhere S adm hfloor.floorAboveRoots
      hfloor.floorWitness v hv
    rw [← actionStoreAt_filteredTree S rho v r] at hheal
    simpa only [PhaseGrades.filteredTree, actionStoreAt] using hheal
  obtain ⟨v0, -, hv0⟩ := AlignedRoundLemmas.honest_member_of_quorum hbot
    (AlignedRoundLemmas.honestQuorum_of_belowOneThird hbot)
  have hcarriersBelowOpening : ∀ P' : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r) = some P' →
      ∀ w ∈ rho.honest,
        Block.Preceq (actionSGBlockAt S rho w (r - 1)) P'.erase := by
    intro P' hP' w hw
    exact Block.preceq_trans (hchain.carriersBelowEndpoint w hw)
      (hchain.endpointBelowOpening P' hP')
  refine
    { openingProposal := ⟨P, hP⟩
      carrier := hfacts.carrier
      afterBoundary := hfacts.afterBoundary
      inHorizon := hfacts.inHorizon
      batchSole := hfacts.batchSole
      batchComplete := hchain.batchComplete
      batchHeads := ?_
      openingLive := hfacts.openingLive
      openingSource := ?_
      actionRootBelowOpening := ?_
      actionAnchorBelowOpening := ?_
      namedActionAnchorBelowOpening := ?_
      plusOneCandidate := hchain.plusOneCandidate
      plusOneCone := hfacts.plusOneCone
      plusTwoCone := hfacts.plusTwoCone
      heightHistory := hchain.heightHistory
      targetHistory := hchain.targetHistory
      timeoutHistory := hchain.timeoutHistory }
  · intro v hv w hw u hu P' hP'
    exact batchHeads_of_batchFields hfacts.batchSole hchain.batchComplete
      (hcarriersBelowOpening P' hP') v hv w hw u hu
  · intro v hv P' hP'
    obtain ⟨X, hX⟩ := exists_actionFGSource_of_namedGradeFormsAt S
      adm.toNamedAdmissibleCore hrpos hactionHor hforms hv (hactive v hv)
    have hround : S.hc.round_of
        (actionReadAt S rho v r).st.core.toHealing.s = r := by
      simpa only [actionStoreAt, Protocol.Store.toHealing] using
        actionStoreAt_round S rho v r
    have hsource : actionFGSource S (actionReadAt S rho v r) = some X := by
      simpa only [actionFGSource, PhaseGrades.nodeFGSource, hround] using hX
    rw [hsource, w4d2ActionFGSourceEqLive S adm hrpos hactionHor hv
      (hframe v hv).1 (hframe v hv).2 hsource]
    exact congrArg some (hfacts.openingLive v hv P' hP')
  · intro v hv P' hP'
    have hroot : Block.Preceq
        (Protocol.get_fg_root
          (actionStoreAt S rho v r).st.core.toHealing.toFG) C := by
      change Block.Preceq
        (Protocol.get_fg_root (actionStoreAt S rho v r).toHealing.toFG) C
      rw [actionStoreAt_fgRoot_eq_storeBeforeTime S rho v r]
      simpa only [healStoreAt] using hfloor.floorAboveRoots v hv
    exact Block.preceq_trans hroot
      (Block.preceq_trans (hfloor.floorBelowCarriers v0 hv0)
        (hcarriersBelowOpening P' hP' v0 hv0))
  · intro v hv P' hP'
    exact Block.preceq_trans (hchain.anchorsBelowEndpoint v hv)
      (hchain.endpointBelowOpening P' hP')
  · intro v hv P' hP'
    exact Block.preceq_trans (hchain.namedAnchorsBelowEndpoint v hv)
      (hchain.endpointBelowOpening P' hP')

/- The active producer does not need the previous domain-activity callback: the
  grade forms are already a per-round input of the pin, and the direct facts
  body above is the complete consumer. -/
theorem w4CanonicalRegimeRoundFactsPinGraded_closed
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbot : BelowOneThird S rho.honest)
    {q0 : Round} (hpost : S.E.t_GST ≤ S.a q0) :
    W4CanonicalRegimeRoundFactsPinGraded S rho q0 := by
  intro r C End hfacts hchain hforms hnl
  exact w4CanonicalRegimeRoundAt_of_facts_and_chainFor_named S adm hbot hfacts
    hchain hnl (hpost.trans (Assembly.a_mono S
      (Nat.le_sub_one_of_lt (w4fkRoundLtOfAfterBoundary S hfacts.afterBoundary))))
    hforms

#print axioms w4CanonicalRegimeRoundAt_of_facts_and_chainFor_named
#print axioms w4CanonicalRegimeRoundFactsPinGraded_closed



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
