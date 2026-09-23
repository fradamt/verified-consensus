module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.CanonicalRegimeFromChain
public import DecoupledConsensusProofs.Protocol.ChainState.CarrierTimeoutGate
public import DecoupledConsensusProofs.Protocol.ChainState.RecurringFinality
public import DecoupledConsensusProofs.Protocol.Grades.LifecycleActionSource
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.RecoverySourceProgress
public import DecoupledConsensusProofs.Generic.CanonicalSuffix
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionConfirmationCore
public import DecoupledConsensusProofs.Protocol.ValidatorClient.SuccessorTargetRows
public import DecoupledConsensusProofs.Protocol.Grades.GoldfishConePersistence
public import DecoupledConsensusProofs.Protocol.ChainState.CarrierAlignment
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FreshFGSourceCone
public import DecoupledConsensusProofs.Execution.SeedActionRowCarriage
public import DecoupledConsensusProofs.Protocol.ChainState.CanonicalDensity
public import DecoupledConsensusProofs.Protocol.ChainState.CheckpointAlgebra
public import DecoupledConsensusProofs.Execution.W4FKLockAlignment
public import DecoupledConsensusProofs.Protocol.Grades.W4FKGrade
public import DecoupledConsensusProofs.Protocol.ChainState.NamedNjGap
public import DecoupledConsensusProofs.Protocol.Schedule.ActionStoreHeadsResolve
public import DecoupledConsensusProofs.Protocol.ChainState.MatchingProgress
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalAdoptionNamedClosed
public import DecoupledConsensusProofs.Protocol.ChainState.RawHeightCoverage
public import DecoupledConsensusProofs.Protocol.Schedule.W4ExecSuffix
public import DecoupledConsensusProofs.Protocol.Schedule.W4CarrierRecord
public import DecoupledConsensusProofs.Protocol.Grades.W4FKPreparedFrame

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

/-! ## Pinned statements (wave A) -/




/-! ## Geometry of the floor at a carrier -/

/-- The moving-chain floor is below the carrier's own opening proposal.

`floorBelowCarriers` puts it below every honest round-`(r-1)` SG carrier,
`carriersBelowEndpoint` puts those below the slot endpoint and
`endpointBelowOpening` puts the endpoint below the opening proposal. -/
theorem movingChainFloor_preceq_opening
    (S : Setup V) {rho : Run V} (hbot : BelowOneThird S rho.honest)
    {q0 r : Round} {C End : Block V}
    (hchain : MovingChainAtCarrierFor S rho q0 r C End)
    (hnl : ¬ LostRoundAt S rho r) :
    ∀ P0 : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r) = some P0 →
      Block.Preceq C P0.erase := by
  intro P0 hP0
  obtain ⟨v0, -, hv0⟩ :=
    AlignedRoundLemmas.honest_member_of_quorum hbot
      (AlignedRoundLemmas.honestQuorum_of_belowOneThird hbot)
  exact Block.preceq_trans ((hchain.floorFields hnl).floorBelowCarriers v0 hv0)
    (Block.preceq_trans (hchain.carriersBelowEndpoint v0 hv0)
      (hchain.endpointBelowOpening P0 hP0))


/-! ## The exact honest target rows at a justifiable carrier opening

Named proof of earlier `CarrierTimeoutGateRun.lean:652-705` (`carrierRows_exactTargets`)
composed with earlier `CarrierRegimeRun.lean:227-336`
(`carrierRound_heightPair_eq_openingFields`, `carrierRound_commonTargetRows`).

earlier reaches the honest row through the carrier regime's common grade and its
`g0_clear` walk to the opening proposal. The selection's `CanonicalRegimeRoundAt`
carries the resulting FG source as a field (`openingSource`), so the grade is
not needed here at all: the row's fields are read straight off the opening
proposal, and the only residual input is the Rule-B lock alignment.
-/

omit [Fintype V] in
/-- Copied from the private `SuccessorTargetRowsRun.lean:93`
(`ownLock_none_or_aligned_of_successorRecord`): an aligned record leaves the
own lock empty or at the canonical target. -/
private theorem w4_ownLock_none_or_aligned
    {Lambda : Protocol.NamedRecord} {H : Height} {T : BlockId}
    {fp : Option FinalityPair}
    (haligned : SuccessorTargetLockAlignmentAt Lambda fp H T) :
    Protocol.own_lock Lambda.legacy H fp = none ∨
      Protocol.own_lock Lambda.legacy H fp = some T := by
  cases hfp : fp with
  | none =>
      cases hlock : Lambda.legacy.lock H with
      | none =>
          left
          simp [Protocol.own_lock, hlock]
      | some X =>
          have hXT : X = T := haligned.1 X hlock
          right
          simp [Protocol.own_lock, hlock, hXT]
  | some p =>
      by_cases hpH : p.height = H
      · have hpT : p.target = T := haligned.2 p hfp hpH
        right
        simp [Protocol.own_lock, hpH, hpT]
      · cases hlock : Lambda.legacy.lock H with
        | none =>
            left
            simp [Protocol.own_lock, hpH, hlock]
        | some X =>
            have hXT : X = T := haligned.1 X hlock
            right
            simp [Protocol.own_lock, hpH, hlock, hXT]

/-- Copied from the private `SuccessorTargetRowsRun.lean:122`
(`round_action_height_pair_target_of_successorRecord`): a justifiable selected
source and an aligned successor record force the exact named target row. -/
private theorem w4_round_action_height_pair_target
    (contract : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : Protocol.HealingStore V)
    (Lambda : Protocol.NamedRecord) {H : Height} {T : BlockId}
    {Q : Block V}
    (hsource : Protocol.fg_source_with contract E hc st (hc.round_of st.s)
      (Protocol.grade2_block_with contract E hc st (hc.round_of st.s)) = some Q)
    (hheight : (st.σ Q).h = H)
    (htarget : (st.σ Q).T_h.root = T)
    (hnj : (st.σ Q).nj = false)
    (hrecord : SuccessorTargetRecordAt Lambda H T)
    (haligned : SuccessorTargetLockAlignmentAt Lambda
      (Protocol.NamedActions.round_action_with contract E hc nd st Lambda).2.finality_pair
      H T) :
    (Protocol.NamedActions.round_action_with contract E hc nd st Lambda).2.height_pair =
      NamedHeightPair.vote H T false := by
  let fp := (Protocol.NamedActions.round_action_with contract E hc nd st Lambda).2.finality_pair
  have hown' : Protocol.own_lock Lambda.legacy H fp = none ∨
      Protocol.own_lock Lambda.legacy H fp = some T :=
    w4_ownLock_none_or_aligned (by simpa only [fp] using haligned)
  have hpure : Protocol.height_pair Lambda.legacy (some (H, T, false)) fp =
      HeightPair.target H T := by
    rcases hown' with hnone | hlockAligned
    · rcases hrecord.1 with hnoneTarget | hrecordedTarget
      · exact height_pair_eq_target_of_no_lock_no_target_justifiable
          Lambda.legacy fp hrecord.2 hnone hnoneTarget
      · exact height_pair_eq_target_of_no_lock_recorded_target
          Lambda.legacy fp hrecord.2 hnone hrecordedTarget
    · exact height_pair_eq_target_of_aligned_lock
        Lambda.legacy fp hrecord.2 hlockAligned
  have hsource' : actionSource contract E hc st = some Q := by
    simpa only [actionSource] using hsource
  rw [named_round_action_height_pair contract E hc nd st Lambda,
    hsource', Option.map_some]
  simp only [hheight, htarget, hnj]
  rw [hpure]
  exact encodeHeight_of_target

/-- Copied from the private `CanonicalCarrierConeRun.lean:38`
(`openingSlot_pos_of_after_boundary`). -/
private theorem w4_openingSlot_pos
    (S : Setup V) {q r : Round}
    (hafter : healingBoundaryTime S q <
      Protocol.proposal_time S.E (S.hc.opening_slot r)) :
    0 < S.hc.opening_slot r := by
  by_contra hnot
  have heq : S.hc.opening_slot r = 0 := Nat.eq_zero_of_not_pos hnot
  have hproposalBoundary :
      Protocol.proposal_time S.E (S.hc.opening_slot r) <
        healingBoundaryTime S q := by
    rw [heq]
    unfold healingBoundaryTime
    exact lt_of_lt_of_le (Protocol.proposal_time_lt_vote_time S.E 0)
      (Protocol.vote_time_mono_slots S.E (Nat.zero_le _))
  exact (lt_asymm hafter) hproposalBoundary

/-- Copied from the private `RawHeightProgressRun.lean:209`
(`runBlock_unique_of_erase_eq`). -/
private theorem w4_runBlock_unique_of_erase_eq
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {A D : NamedBlock V} (hA : RunBlock S rho A) (hD : RunBlock S rho D)
    (herase : A.erase = D.erase) : A = D :=
  adm.toNamedRootCollisionFree.root_injective A D hA hD A D
    (Or.inl (Proofs.NamedAncestry.named_self A)) (Or.inr (Proofs.NamedAncestry.named_self D))
    (by rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root D, herase])

/-- The carrier's opening proposal is a named body of every honest reader's
round-`r` action store, and the store's derived view of it is the run's. -/
theorem carrierOpening_mem_actionBodies
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q0 r : Round} (hround : CanonicalRegimeRoundAt S rho q0 r)
    {P0 : NamedBlock V}
    (hP0 : proposedBlockAt S rho (S.hc.opening_slot r) = some P0)
    {v : V} (hv : v ∈ rho.honest) :
    P0 ∈ (actionStoreAt S rho v r).st.bodies := by
  have hspos : 0 < S.hc.opening_slot r :=
    w4_openingSlot_pos S hround.afterBoundary
  have hpropHor : Protocol.proposal_time S.E (S.hc.opening_slot r) ≤
      rho.horizon :=
    (Protocol.proposal_time_mono S.E
        (Nat.le_add_right (S.hc.opening_slot r) 2)).trans
      ((Protocol.proposal_time_le_confirmation_time S.E _).trans
        hround.inHorizon)
  have hP0run : RunBlock S rho P0 :=
    proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
      (S.hc.opening_slot r) hspos hround.carrier.1 hpropHor hP0
  have hk : S.hc.round_of
      (actionReadAt S rho v r).st.core.toHealing.s = r := by
    simpa only [actionReadAt] using Proofs.HealingLemmas.round_of_slotOf_a S r
  have hsource : PhaseGrades.nodeFGSource S (actionReadAt S rho v r) r =
      some P0.erase := by
    have h0 := hround.openingSource v hv P0 hP0
    simp only [actionFGSource] at h0
    rw [hk] at h0
    simpa only [PhaseGrades.nodeFGSource] using h0
  obtain ⟨Cn, hbody, hCerase, hCrun⟩ :=
    freshFGSource_namedSource_witness S adm hv hsource
  have hCn : Cn = P0 := w4_runBlock_unique_of_erase_eq adm hCrun hP0run hCerase
  rw [← hCn]
  exact hbody

/-- **Exact honest target rows at a carrier.** Every honest round-`r` action
emits the opening proposal's height and canonical target, with the timeout bit
clear. This is earlier's `carrierRows_exactTargets` restated over
`proposedBlockAt`/`derive_named`, with an explicit floor: the
selection round record already names the FG source. -/
theorem carrierRows_exactTargets_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q0 r : Round} (hround : CanonicalRegimeRoundAt S rho q0 r)
    {P0 : NamedBlock V}
    (hP0 : proposedBlockAt S rho (S.hc.opening_slot r) = some P0)
    (habove : honestHMaxAt S rho (S.a q0) <
      (Protocol.derive_named S.E S.cfg P0).h)
    (hnj : (Protocol.derive_named S.E S.cfg P0).nj = false)
    (hlockAligned : ∀ v ∈ rho.honest,
      SuccessorTargetLockAlignmentAt
        (rho.stateBeforeTime S (S.a r) v).Λ
        (actionAttestationAt S rho v r).finality_pair
        (Protocol.derive_named S.E S.cfg P0).h
        (Protocol.derive_named S.E S.cfg P0).T_h.root) :
    ∀ v ∈ rho.honest,
      (actionAttestationAt S rho v r).height_pair =
        NamedHeightPair.vote (Protocol.derive_named S.E S.cfg P0).h
          (Protocol.derive_named S.E S.cfg P0).T_h.root false := by
  intro v hv
  let ast := actionStoreAt S rho v r
  let Lambda := (rho.stateBeforeTime S (S.a r) v).Λ
  have hk : S.hc.round_of ast.s = r := actionStoreAt_round S rho v r
  have hsource : Protocol.fg_source_with
      (NamedProfile.gradeContract ast.cache) S.E S.hc ast.st.core.toHealing
      (S.hc.round_of ast.st.core.toHealing.s)
      (Protocol.grade2_block_with (NamedProfile.gradeContract ast.cache) S.E S.hc
        ast.st.core.toHealing (S.hc.round_of ast.st.core.toHealing.s)) =
      some P0.erase := by
    simpa only [actionFGSource, ast] using hround.openingSource v hv P0 hP0
  have hbody : P0 ∈ ast.st.bodies :=
    carrierOpening_mem_actionBodies S adm hround hP0 hv
  have hagree : Internal.NamedDerivedStateAgrees S.E S.cfg ast.st :=
    derivedStateAgrees_actionStoreAt S adm v r
  have hsigma : ast.st.core.σ P0.erase =
      Protocol.derive_named S.E S.cfg P0 := hagree P0 hbody
  have hrecord := hround.successorTargetRecordAt hP0 habove hnj v hv
  have hpair := w4_round_action_height_pair_target
    (NamedProfile.gradeContract ast.cache) S.E S.hc (S.node v)
    ast.st.core.toHealing Lambda hsource
    (by rw [show (ast.st.core.toHealing.σ P0.erase) =
        ast.st.core.σ P0.erase from rfl, hsigma])
    (by rw [show (ast.st.core.toHealing.σ P0.erase) =
        ast.st.core.σ P0.erase from rfl, hsigma])
    (by rw [show (ast.st.core.toHealing.σ P0.erase) =
        ast.st.core.σ P0.erase from rfl, hsigma]; exact hnj)
    (by simpa only [Lambda] using hrecord)
    (by simpa only [ast, Lambda, actionAttestationAt] using hlockAligned v hv)
  simpa only [actionAttestationAt, ast, Lambda] using hpair



/-- The carrier's `+2` proposal carries every honest round-`r` action row.
Pool admission alone does it; no grade and no floor activity is used. -/
theorem carrierPlusTwoCarriesRoundRows_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q0 r : Round} (hround : CanonicalRegimeRoundAt S rho q0 r)
    (hpost : S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot r)) :
    ∀ P2 : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r + 2) = some P2 →
      ∀ v ∈ rho.honest, actionAttestationAt S rho v r ∈ P2.attestations := by
  have hhorTwo : Protocol.proposal_time S.E (S.hc.opening_slot r + 2) ≤
      rho.horizon :=
    (Protocol.proposal_time_le_confirmation_time S.E _).trans
      hround.inHorizon
  have hpostAction : S.E.t_GST ≤ S.a r := by
    refine hpost.trans ?_
    have hconf : S.a r =
        Protocol.confirmation_time S.E (S.hc.opening_slot r) := by
      simp only [Setup.a, Protocol.a_eq_confirmation_time]
    rw [hconf]
    exact Protocol.proposal_time_le_confirmation_time S.E _
  intro P2 hP2 v hv
  exact plusTwoProposal_carries_resolvedRoundRow S adm hround.carrier hhorTwo
    hv hP2
    (actionAttestationAt_mem_selectedRows_at_plusTwo S adm hround.carrier
      hpostAction hhorTwo hv)




/-- The carrier's opening proposal is a run block. -/
theorem carrierOpening_runBlock
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q0 r : Round} (hround : CanonicalRegimeRoundAt S rho q0 r)
    {P0 : NamedBlock V}
    (hP0 : proposedBlockAt S rho (S.hc.opening_slot r) = some P0) :
    RunBlock S rho P0 :=
  proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
    (S.hc.opening_slot r) (w4_openingSlot_pos S hround.afterBoundary)
    hround.carrier.1
    ((Protocol.proposal_time_mono S.E
        (Nat.le_add_right (S.hc.opening_slot r) 2)).trans
      ((Protocol.proposal_time_le_confirmation_time S.E _).trans
        hround.inHorizon))
    hP0



/-! ### The quiet arm's algebra

earlier's quiet arm ends in `carrierPlusOne_checkpointReady_of_faultyOnlyRows`
(`CanonicalRegimeFirstVoteRun.lean:150`). Its selection twin
`plusOne_noHeightEvent_of_faultyOnlyRows` (`:125`) is live, but it concludes
`CarrierPlusOneNoHeightEventAt`, whose two fields read the guards at
`Protocol.afterFin S.E (carrierPlusOneFold …)` while the named
`carrierPlusOneFold` (`CarrierAlignmentRun.lean:111`) is
`Protocol.named_transition`, i.e. the state AFTER the height events.
earlier's erased `carrierPlusOneFold` (`CarrierAlignmentRun.lean:390`) is
`Protocol.foldBlock`, i.e. the state BEFORE them. The named restatement
therefore reads the guards one transition too late and cannot drive the quiet
conclusion; the theorem below states the arm on the pre-event fold instead. -/

private theorem w4_afterFin_target_participation
    (E : Env V) (sigma : Protocol.ChainState V) :
    (Protocol.afterFin E sigma).target_participation =
      sigma.target_participation := by
  unfold Protocol.afterFin
  split_ifs <;> rfl

private theorem w4_afterFin_progress
    (E : Env V) (sigma : Protocol.ChainState V) :
    (Protocol.afterFin E sigma).progress = sigma.progress := by
  unfold Protocol.afterFin
  split_ifs <;> rfl

private theorem w4_derive_named_eq_transition
    (E : Env V) (cfg : Protocol.HeightConfig)
    {P0 P1 : NamedBlock V} (hparent : NamedBlock.parent? P1 = some P0) :
    Protocol.derive_named E cfg P1 =
      Protocol.named_transition E cfg
        (Protocol.derive_named E cfg P0) P1 := by
  cases P1 with
  | genesis => cases hparent
  | node parent slot root votes support rows proposer =>
      have h : parent = P0 := Option.some.inj hparent
      rw [← h]
      rfl

/-- **The quiet arm.** If neither height-participation set of the `+1` block's
row fold contains an honest validator, no height event fires and the `+1`
block preserves its parent's checkpoint height and entry.

Stated on the PRE-height-event fold, which is what the erased earlier twin reads
(see the note above). -/
theorem namedPlusOne_quiet_of_faultyOnlyRows
    (S : Setup V) {rho : Run V} (hbot : BelowOneThird S rho.honest)
    {P0 P1 : NamedBlock V}
    (hparent : NamedBlock.parent? P1 = some P0)
    (htarget : ∀ v ∈ (Protocol.fold_rows
        (Protocol.TimeoutBinding.targeted V)
        (Protocol.derive_named S.E S.cfg P0) P1.erase
        P1.attestations).target_participation, v ∉ rho.honest)
    (hprogress : ∀ v ∈ (Protocol.fold_rows
        (Protocol.TimeoutBinding.targeted V)
        (Protocol.derive_named S.E S.cfg P0) P1.erase
        P1.attestations).progress, v ∉ rho.honest) :
    (Protocol.derive_named S.E S.cfg P1).h =
        (Protocol.derive_named S.E S.cfg P0).h ∧
      (Protocol.derive_named S.E S.cfg P1).T_h =
        (Protocol.derive_named S.E S.cfg P0).T_h := by
  have hfaulty : ∀ Q : Finset V, (∀ v ∈ Q, v ∉ rho.honest) →
      S.E.electorate.quorumCheck Q = false := by
    intro Q hQ
    have hsub : Q ⊆ Finset.univ \ rho.honest := by
      intro v hv
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, hQ v hv⟩
    simp only [Electorate.quorumCheck, decide_eq_false_iff_not]
    exact not_isQuorum_of_subset_faulty hbot hsub
  have hfoldFields := NamedDerivationGeometry.fold_context_fields
    (Protocol.TimeoutBinding.targeted V) P1.attestations
    { Protocol.derive_named S.E S.cfg P0 with s := P1.erase.slot }
  have hfoldH : (Protocol.fold_rows
      (Protocol.TimeoutBinding.targeted V)
      (Protocol.derive_named S.E S.cfg P0) P1.erase P1.attestations).h =
      (Protocol.derive_named S.E S.cfg P0).h := hfoldFields.2.1
  have hfoldT : (Protocol.fold_rows
      (Protocol.TimeoutBinding.targeted V)
      (Protocol.derive_named S.E S.cfg P0) P1.erase
      P1.attestations).T_h =
      (Protocol.derive_named S.E S.cfg P0).T_h := hfoldFields.2.2.1
  have htargetFalse : (Protocol.afterFin S.E (Protocol.fold_rows
      (Protocol.TimeoutBinding.targeted V)
      (Protocol.derive_named S.E S.cfg P0) P1.erase
      P1.attestations)).targetQuorum S.E = false := by
    change S.E.electorate.quorumCheck
      (Protocol.afterFin S.E (Protocol.fold_rows
        (Protocol.TimeoutBinding.targeted V)
        (Protocol.derive_named S.E S.cfg P0) P1.erase
        P1.attestations)).Q_target = false
    unfold Protocol.ChainState.Q_target
    rw [w4_afterFin_target_participation]
    exact hfaulty _ htarget
  have hprogFalse : (Protocol.afterFin S.E (Protocol.fold_rows
      (Protocol.TimeoutBinding.targeted V)
      (Protocol.derive_named S.E S.cfg P0) P1.erase
      P1.attestations)).progQuorum S.E = false := by
    change S.E.electorate.quorumCheck
      (Protocol.afterFin S.E (Protocol.fold_rows
        (Protocol.TimeoutBinding.targeted V)
        (Protocol.derive_named S.E S.cfg P0) P1.erase
        P1.attestations)).Q_prog = false
    unfold Protocol.ChainState.Q_prog
    rw [w4_afterFin_progress]
    exact hfaulty _ hprogress
  have htfalse : Protocol.targetReady S.E
      (Protocol.afterFin S.E (Protocol.fold_rows
        (Protocol.TimeoutBinding.targeted V)
        (Protocol.derive_named S.E S.cfg P0) P1.erase
        P1.attestations)) = false := by
    simp only [Protocol.targetReady, htargetFalse, Bool.and_false]
  have hpfalse : Protocol.progReady S.E S.cfg
      (Protocol.afterFin S.E (Protocol.fold_rows
        (Protocol.TimeoutBinding.targeted V)
        (Protocol.derive_named S.E S.cfg P0) P1.erase
        P1.attestations)) = false := by
    simp only [Protocol.progReady, htargetFalse, hprogFalse,
      Bool.and_false, Bool.or_false]
  rw [w4_derive_named_eq_transition S.E S.cfg hparent]
  unfold Protocol.named_transition Protocol.transition_rows
  rw [Protocol.process_height_events_eq]
  simp only [htfalse, hpfalse, Bool.false_eq_true, ↓reduceIte]
  exact ⟨(Protocol.afterFin_h (E := S.E) (σ := _)).trans hfoldH,
    (Protocol.afterFin_T_h (E := S.E) (σ := _)).trans hfoldT⟩







#print axioms movingChainFloor_preceq_opening
#print axioms carrierOpening_mem_actionBodies
#print axioms carrierRows_exactTargets_named
#print axioms carrierPlusTwoCarriesRoundRows_named
#print axioms carrierOpening_runBlock
#print axioms namedPlusOne_quiet_of_faultyOnlyRows







/-- Copied from the private `CarrierTimeoutGateRun.lean:97`
(`confirmation_time_mono_timeoutGate`). -/
private theorem w4_confirmation_time_mono
    (E : Env V) {s u : Slot} (hsu : s ≤ u) :
    Protocol.confirmation_time E s ≤ Protocol.confirmation_time E u := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ,
    Protocol.confirmation_time_eq_support_cutoff_succ]
  exact Proofs.Optimistic.support_cutoff_mono E (Nat.add_le_add_right hsu 1)

/-- The carrier's action read is inside the horizon. -/
theorem w4_actionRead_le_horizon
    (S : Setup V) {rho : Run V} {q0 r : Round}
    (hround : CanonicalRegimeRoundAt S rho q0 r) :
    S.a r ≤ rho.horizon := by
  have hmono : Protocol.confirmation_time S.E (S.hc.opening_slot r) ≤
      Protocol.confirmation_time S.E (S.hc.opening_slot r + 2) :=
    w4_confirmation_time_mono S.E (Nat.le_add_right (S.hc.opening_slot r) 2)
  have ha : S.a r ≤
      Protocol.confirmation_time S.E (S.hc.opening_slot r + 2) := by
    simpa only [Setup.a, Protocol.a_eq_confirmation_time] using hmono
  exact ha.trans hround.inHorizon


#print axioms w4_actionRead_le_horizon





/-- **Slot terminality at the round action read.** The carrier's slot-`+1`
proposal is the round action's head as soon as it is below it. -/
theorem carrierActionHead_eq_plusOne_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {P1 : NamedBlock V}
    (hcone : CarrierActionHeadPlusOneConeAt S rho r P1) :
    ∀ v ∈ rho.honest, actionHeadAt S rho v r = P1.erase := by
  intro v hv
  have hheadPre : actionHeadAt S rho v r ∈
      (rho.storeBeforeTime S v (S.a r)).T :=
    actionHeadWith_mem_storeBeforeTime S v r
  have hpre : Block.Preceq P1.erase (actionHeadAt S rho v r) :=
    hcone.plusOneCone v hv
  have hslotP1 : P1.erase.slot = S.hc.opening_slot r + 1 := by
    rw [Proofs.NamedWire.erase_slot]
    exact proposedBlockAt_slot S rho (S.hc.opening_slot r + 1) hcone.proposal
  have hactionLe : S.a r ≤
      Protocol.proposal_time S.E (S.hc.opening_slot r + 2) :=
    (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
      (action_add_delta_le_plusTwo_proposal_time S r)
  have hheadUpper : (actionHeadAt S rho v r).slot <
      S.hc.opening_slot r + 2 :=
    Proofs.NamedSlotFreshness.block_slot_lt_of_mem_beforeTime_of_le_proposal S
      adm.toNamedAdmissibleCore (Nat.zero_lt_succ _) hactionLe hheadPre
  by_contra hne
  have hne' : P1.erase ≠ actionHeadAt S rho v r := fun h => hne h.symm
  have hlt : P1.erase.slot < (actionHeadAt S rho v r).slot :=
    Proofs.NamedSlotFreshness.slot_lt_of_preceq_ne_of_mem_storeBeforeTime S
      adm.toNamedAdmissibleCore hheadPre hpre hne'
  rw [hslotP1] at hlt
  exact absurd hheadUpper (Nat.not_lt.mpr hlt)


#print axioms carrierActionHead_eq_plusOne_named



omit [Fintype V] in
/-- A named parent is a named ancestor. -/
private theorem w4_namedPreceq_of_parent
    {A B : NamedBlock V} (h : NamedBlock.parent? B = some A) :
    NamedBlock.Preceq A B := by
  cases B with
  | genesis => cases h
  | node parent slot root votes support rows proposer =>
      have hparent : parent = A := Option.some.inj h
      rw [← hparent]
      exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
        (Proofs.NamedAncestry.named_self parent)

/-- Copied from `W4GeneralSlotAdoptionRun.lean:104`
(`honestProposal_slotVoteCone_after_SG_healing_named_of_heads`): that module
cannot be imported here because it re-declares
`honestProposal_voterHeadAt_eq_after_SG_healing_named_slot`, which
`ProposalAdoptionNamedClosedRun` already exports into this closure. -/
private theorem w4_slotVoteCone_of_heads
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hs : 0 < s)
    (hhor : Protocol.vote_time S.E s ≤ rho.horizon)
    {P : NamedBlock V}
    (hheads : ∀ v ∈ rho.honest, voterHeadAt S rho v s = P.erase) :
    NamedHonestVotesCone S rho s (fun X => Block.Preceq P.erase X) := by
  intro w hw hcommittee
  obtain ⟨X, hXhead, hXrun, hXemit⟩ :=
    voteDutyHead_runBlock_and_emits S adm hs hhor hw hcommittee
  refine ⟨X, ?_, hXrun, hXemit⟩
  simpa only [hXhead, Protocol.voteDutyHead, hheads w hw] using
    Block.preceq_self P.erase

/-- The round-`r` action read sits at the support cutoff of the carrier's
slot `+1`. -/
theorem w4_actionTime_eq_plusOneCutoff
    (S : Setup V) (r : Round) :
    S.a r = Protocol.support_cutoff S.E (S.hc.opening_slot r + 1) := by
  have h : S.a r = Protocol.confirmation_time S.E (S.hc.opening_slot r) := by
    simp only [Setup.a, Protocol.a_eq_confirmation_time]
  rw [h, Protocol.confirmation_time_eq_support_cutoff_succ]


/-- **The slot-`+1` proposal is below every honest round-`r` action head.**

Inputs: the honest vote heads at slot `+1` (the corresponding branch's general-slot head
equality) and the action read's prepared SG root below the carrier's opening
proposal (the `_of_actionRootPreceq` fact, owned elsewhere). -/
theorem carrierPlusOne_preceq_actionHead_of_voteHeads
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {q0 r : Round} (hround : CanonicalRegimeRoundAt S rho q0 r)
    (hpost : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot r + 1))
    (hhor : Protocol.support_cutoff S.E (S.hc.opening_slot r + 1) ≤
      rho.horizon)
    {P0 P1 : NamedBlock V}
    (hP0 : proposedBlockAt S rho (S.hc.opening_slot r) = some P0)
    (hP1 : proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1)
    (hheads : ∀ x ∈ rho.honest,
      voterHeadAt S rho x (S.hc.opening_slot r + 1) = P1.erase)
    (hactionRoot : ∀ v ∈ rho.honest,
      Block.Preceq
        (Protocol.get_sg_root_with
          (NamedProfile.gradeContract (actionStoreAt S rho v r).cache)
          S.E S.hc (actionStoreAt S rho v r).st.core.toHealing
          (S.hc.round_of (actionStoreAt S rho v r).s)) P0.erase) :
    ∀ v ∈ rho.honest, Block.Preceq P1.erase (actionHeadAt S rho v r) := by
  have ha : S.a r = Protocol.support_cutoff S.E (S.hc.opening_slot r + 1) :=
    w4_actionTime_eq_plusOneCutoff S r
  have hvoteHor : Protocol.vote_time S.E (S.hc.opening_slot r + 1) ≤
      rho.horizon := by
    refine le_trans ?_ hhor
    rw [← Proofs.Optimistic.vote_time_add_delta]
    exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
  have hP0P1 : Block.Preceq P0.erase P1.erase := by
    obtain ⟨p, hp, hpe⟩ :=
      proposedBlockAt_parent S rho (S.hc.opening_slot r + 1) hP1
    refine Block.preceq_trans ?_ (Proofs.NamedWire.erase_preceq
      (w4_namedPreceq_of_parent hp))
    rw [hpe]
    exact hround.plusOneCone P0 hP0
  have hcone : NamedHonestVotesCone S rho (S.hc.opening_slot r + 1)
      (fun X => Block.Preceq P1.erase X) :=
    w4_slotVoteCone_of_heads S adm (Nat.succ_pos _) hvoteHor hheads
  intro v hv
  have hrootP1 : Block.Preceq
      (Protocol.get_fg_root
        (actionStoreAt S rho v r).toHealing.toFG) P1.erase :=
    Block.preceq_trans (hround.actionRootBelowOpening v hv P0 hP0) hP0P1
  have hresolve := WeakAction.headsResolveIn_actionStore_of_postHealingCone
    S adm hv hpost hhor ha hrootP1 hcone
  have hsupport := WeakAction.coneSupport_actionStoreAt S
    adm.toNamedAdmissibleCore hcom (Nat.succ_pos _) hpost hhor hcone hv ha
    hresolve
  have hpath := WeakAction.actionPath_to_ancestor_of_candidate S
    adm.toNamedAdmissibleCore (hround.plusOneCandidate v hv P1 hP1)
    (Block.preceq_self P1.erase)
  exact WeakAction.protectedBlock_preceq_actionHead_of_cone_compatible S
    adm.toNamedAdmissibleCore ha hsupport
    (Block.compatible_of_preceq_common
      (Block.preceq_trans (hactionRoot v hv) hP0P1)
      (Block.preceq_self P1.erase))
    (fun _ => hpath)


/-- **The shared action-head fact, produced.**

This is `W4SecondCarrierActionHeadPin S rho r`
(`W4FKChainSecondCheckpointRun.lean:59`) written out, and it is also the
`actionHeadEq` field of `CarrierFinalityFirstHalfAt`. One producer, both
consumers.

Its two inputs are owned elsewhere and are both round-local:

* `hheads` — the corresponding branch's general-slot head equality at slot
  `opening_slot r + 1`
  (`honestProposal_voterHeadAt_eq_after_SG_healing_named_slot`);
* `hactionRoot` — the action read's prepared SG root below the carrier's
  opening proposal, i.e. the `_of_actionRootPreceq` fact of
  `FixedHeightRootClaimFourOuterRun`, produced inside the fixed-height regime
  by `actionRootPreceq_of_namedConfirmationRead`
  (`HeightProgressClosureactionRootPreceqRun.lean:66`) from the round's
  opening confirmation read. -/
theorem w4CarrierActionHeadPin_of_voteHeads_and_actionRoot
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {q0 r : Round} (hround : CanonicalRegimeRoundAt S rho q0 r)
    (hpost : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot r + 1))
    (hhor : Protocol.support_cutoff S.E (S.hc.opening_slot r + 1) ≤
      rho.horizon)
    (hheads : ∀ P1 : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1 →
      ∀ x ∈ rho.honest,
        voterHeadAt S rho x (S.hc.opening_slot r + 1) = P1.erase)
    (hactionRoot : ∀ P0 : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r) = some P0 →
      ∀ v ∈ rho.honest,
        Block.Preceq
          (Protocol.get_sg_root_with
            (NamedProfile.gradeContract (actionStoreAt S rho v r).cache)
            S.E S.hc (actionStoreAt S rho v r).st.core.toHealing
            (S.hc.round_of (actionStoreAt S rho v r).s)) P0.erase) :
    ∀ P1 : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1 →
      ∀ v ∈ rho.honest, actionHeadAt S rho v r = P1.erase := by
  intro P1 hP1
  obtain ⟨P0, hP0⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot r)
  refine carrierActionHead_eq_plusOne_named S adm
    { proposal := hP1
      plusOneCone :=
        carrierPlusOne_preceq_actionHead_of_voteHeads S adm hcom hround hpost
          hhor hP0 hP1 (hheads P1 hP1) (hactionRoot P0 hP0) }


#print axioms w4_slotVoteCone_of_heads
#print axioms w4_actionTime_eq_plusOneCutoff
#print axioms carrierPlusOne_preceq_actionHead_of_voteHeads
#print axioms w4CarrierActionHeadPin_of_voteHeads_and_actionRoot



open NamedMatchingProgress (OnNamedChain MatchingWitnesses)


omit [DecidableEq V] [Fintype V] in
/-- Copied from the private `NamedMatchingProgress.witnesses_mono`. -/
private theorem w4_witnesses_mono
    (pool next : NamedAttestation V → Prop) (st : Protocol.ChainState V)
    (h : MatchingWitnesses pool st) (hsub : ∀ a, pool a → next a) :
    MatchingWitnesses next st := by
  refine ⟨h.1, ?_⟩
  intro signer hs
  obtain ⟨a, ha, hv, hm⟩ := h.2 signer hs
  exact ⟨a, hsub a ha, hv, hm⟩

omit [DecidableEq V] [Fintype V] in
/-- Copied from the private `NamedMatchingProgress.witnesses_congr`. -/
private theorem w4_witnesses_congr
    (pool : NamedAttestation V → Prop)
    (st next : Protocol.ChainState V)
    (h : MatchingWitnesses pool st) (hh : next.h = st.h) (ht : next.T_h = st.T_h)
    (hTarget : next.target_participation = st.target_participation)
    (hProgress : next.progress = st.progress) : MatchingWitnesses pool next := by
  refine ⟨?_, ?_⟩
  · rw [hTarget, hProgress]; exact h.1
  · intro signer hs
    rw [hProgress] at hs
    rw [hh, ht]
    exact h.2 signer hs

/-- Copied from the private `NamedMatchingProgress.witnesses_process`. -/
private theorem w4_witnesses_process
    (pool : NamedAttestation V → Prop)
    (st : Protocol.ChainState V) (a : NamedAttestation V) (ha : pool a)
    (h : MatchingWitnesses pool st) :
    MatchingWitnesses pool
      (Protocol.process_attestation_with
        (Protocol.TimeoutBinding.targeted V) st a) := by
  have fields := TargetedTimeoutBinding.process_height_fields st a
  have context := TimeoutBindingDefaults.process_context_fields
    (Protocol.TimeoutBinding.targeted V) st a
  refine ⟨?_, ?_⟩
  · intro signer hs
    rw [fields.2] at hs
    rw [fields.1]
    have hsubset := h.1
    split_ifs at hs ⊢ <;> simp_all only [Bool.and_eq_true, Finset.mem_insert]
    all_goals aesop
  · intro signer hs
    rw [context.2.1, context.2.2.1]
    rcases NamedMatchingProgress.targeted_progress_origin st a signer hs with
        hold | ⟨heq, hm⟩
    · exact h.2 signer hold
    · exact ⟨a, ha, heq.symm, hm⟩

/-- Copied from the private `NamedMatchingProgress.witnesses_fold`. -/
private theorem w4_witnesses_fold
    (pool : NamedAttestation V → Prop)
    (rows : List (NamedAttestation V)) (st : Protocol.ChainState V)
    (hrows : ∀ a ∈ rows, pool a) (h : MatchingWitnesses pool st) :
    MatchingWitnesses pool
      (rows.foldl (Protocol.process_attestation_with
        (Protocol.TimeoutBinding.targeted V)) st) := by
  induction rows generalizing st with
  | nil => exact h
  | cons a rows ih =>
    exact ih _ (fun b hb => hrows b (List.mem_cons_of_mem a hb))
      (w4_witnesses_process pool st a (hrows a (List.mem_cons_self ..)) h)

/-- Copied from the private `NamedMatchingProgress.witnesses_fold_block`. -/
private theorem w4_witnesses_fold_block
    (pool : NamedAttestation V → Prop)
    (st : Protocol.ChainState V) (B : NamedBlock V)
    (hrows : ∀ a ∈ B.attestations, pool a) (h : MatchingWitnesses pool st) :
    MatchingWitnesses pool
      (Protocol.fold_rows (Protocol.TimeoutBinding.targeted V)
        st B.erase B.attestations) := by
  have hf := w4_witnesses_fold pool B.attestations { st with s := B.erase.slot }
    hrows (w4_witnesses_congr pool st _ h rfl rfl rfl rfl)
  exact w4_witnesses_congr pool _ _ hf rfl rfl rfl rfl

omit [Fintype V] in
/-- Copied from the private `NamedMatchingProgress.chain_parent_subset`. -/
private theorem w4_chain_parent_subset
    (parent : NamedBlock V) (slot : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V))
    (rows : List (NamedAttestation V)) (proposer : V)
    (a : NamedAttestation V) (ha : OnNamedChain parent a) :
    OnNamedChain (.node parent slot root votes support rows proposer) a := by
  obtain ⟨carrier, hc, hrow⟩ := ha
  refine ⟨carrier, ?_, hrow⟩
  simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
  exact Or.inr hc

omit [Fintype V] in
/-- Copied from the private `NamedMatchingProgress.own_rows_on_chain`. -/
private theorem w4_own_rows_on_chain
    (B : NamedBlock V) (a : NamedAttestation V) (ha : a ∈ B.attestations) :
    OnNamedChain B a :=
  ⟨B, Proofs.NamedAncestry.named_self B, ha⟩

/-- **The named `+1` fold's matching witnesses.** Every progress bit of the
carrier's slot-`+1` row fold is signed by a row on the `+1` block's own chain
that matches the opening checkpoint. -/
theorem carrierPlusOneFold_matchingWitnesses
    (S : Setup V) {P0 P1 : NamedBlock V}
    (hparent : NamedBlock.parent? P1 = some P0) :
    MatchingWitnesses (OnNamedChain P1)
      (Protocol.fold_rows (Protocol.TimeoutBinding.targeted V)
        (Protocol.derive_named S.E S.cfg P0) P1.erase P1.attestations) := by
  cases P1 with
  | genesis => cases hparent
  | node parent slot root votes support rows proposer =>
      have hp : parent = P0 := Option.some.inj hparent
      subst hp
      refine w4_witnesses_fold_block _ _ _ (w4_own_rows_on_chain _) ?_
      exact w4_witnesses_mono _ _ _
        (NamedMatchingProgress.derive_matching_witnesses S.E S.cfg parent)
        (w4_chain_parent_subset parent slot root votes support rows proposer)

/-- **The named twin of earlier's `foldProgress_honestActionRow`.**

Every progress bit of the carrier's slot-`+1` fold is a row on the `+1`
block's chain, signed by that validator, matching the opening checkpoint's
height and entry. The target-participation set is inside the progress set, so
the same conclusion covers both quorums. -/
theorem carrierPlusOneFold_progressRow
    (S : Setup V) {P0 P1 : NamedBlock V}
    (hparent : NamedBlock.parent? P1 = some P0) {v : V}
    (hvprog : v ∈ (Protocol.fold_rows
      (Protocol.TimeoutBinding.targeted V)
      (Protocol.derive_named S.E S.cfg P0) P1.erase
      P1.attestations).progress) :
    ∃ (carrier : NamedBlock V) (a : NamedAttestation V),
      NamedBlock.Preceq carrier P1 ∧ a ∈ carrier.attestations ∧
        a.val_index = v ∧
        a.height_pair.matchesEntry
            (Protocol.derive_named S.E S.cfg P0).h
            (Protocol.derive_named S.E S.cfg P0).T_h.root = true := by
  have hw := carrierPlusOneFold_matchingWitnesses S (P0 := P0) (P1 := P1)
    hparent
  obtain ⟨a, ⟨carrier, hcarrier, hrow⟩, hval, hmatch⟩ := hw.2 v hvprog
  have hfields := NamedDerivationGeometry.fold_context_fields
    (Protocol.TimeoutBinding.targeted V) P1.attestations
    { Protocol.derive_named S.E S.cfg P0 with s := P1.erase.slot }
  refine ⟨carrier, a, hcarrier, hrow, hval, ?_⟩
  have hh : (Protocol.fold_rows
      (Protocol.TimeoutBinding.targeted V)
      (Protocol.derive_named S.E S.cfg P0) P1.erase P1.attestations).h =
      (Protocol.derive_named S.E S.cfg P0).h := hfields.2.1
  have ht : (Protocol.fold_rows
      (Protocol.TimeoutBinding.targeted V)
      (Protocol.derive_named S.E S.cfg P0) P1.erase
      P1.attestations).T_h =
      (Protocol.derive_named S.E S.cfg P0).T_h := hfields.2.2.1
  simpa only [hh, ht] using hmatch


#print axioms carrierPlusOneFold_matchingWitnesses
#print axioms carrierPlusOneFold_progressRow

/-! ### Provenance of the fold row

The row `carrierPlusOneFold_progressRow` returns is a named row on the `+1`
block's chain. earlier's `foldProgress_honestActionRow` also returns its
emission, which is what identifies it with `actionAttestationAt`. The named
tool for that is `Proofs.NamedStoreBridge.processes_of_runBlock` composed with
`NamedUnforgeable.carried_attest`; the first is `private`, so it and its three
private helpers are copied here. -/














/-- **The action-head fact with the vote-head input discharged.**

the corresponding branch's `honestProposal_voterHeadAt_eq_after_SG_healing_named_slot`
(`ProposalAdoptionNamedClosedRun.lean:1282`, pin-free) supplies the slot-`+1`
head equality from the ambient recurrence and deadline, so the only input left
is `hactionRoot`. -/
theorem w4CarrierActionHeadPin_of_actionRoot
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpostGST : S.E.t_GST ≤ S.a rGST)
    {q0 r : Round} (hround : CanonicalRegimeRoundAt S rho q0 r)
    (hdeadline : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤
      S.hc.opening_slot r + 1)
    (hpost : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot r + 1))
    (hhor : Protocol.support_cutoff S.E (S.hc.opening_slot r + 1) ≤
      rho.horizon)
    (hactionRoot : ∀ P0 : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r) = some P0 →
      ∀ v ∈ rho.honest,
        Block.Preceq
          (Protocol.get_sg_root_with
            (NamedProfile.gradeContract (actionStoreAt S rho v r).cache)
            S.E S.hc (actionStoreAt S rho v r).st.core.toHealing
            (S.hc.round_of (actionStoreAt S rho v r).s)) P0.erase) :
    ∀ P1 : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1 →
      ∀ v ∈ rho.honest, actionHeadAt S rho v r = P1.erase := by
  have hvoteHor : Protocol.vote_time S.E (S.hc.opening_slot r + 1) ≤
      rho.horizon := by
    refine le_trans ?_ hhor
    rw [← Proofs.Optimistic.vote_time_add_delta]
    exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
  refine w4CarrierActionHeadPin_of_voteHeads_and_actionRoot S adm hcom hround
    hpost hhor ?_ hactionRoot
  intro P1 hP1
  exact honestProposal_voterHeadAt_eq_after_SG_healing_named_slot
    (delayExtra := delayExtra) S adm hcom hbelow hrec hdelay hpostGST
    hdeadline hvoteHor hround.carrier.2.1 hP1

#print axioms w4CarrierActionHeadPin_of_actionRoot









/-- **An honest row of a round strictly before `r - 1` cannot sit at a height
above the round-`(r-1)` endpoint.** This is earlier's early branch of
`carrierPlusOne_checkpointReady_of_honestBelow`
(`CarrierRetryRun.lean:2596-2714`), over the corresponding branch's named endpoint history. -/
theorem w4_rowHeight_le_endpointN
    (S : Setup V) {rho : Run V}
    {q0 r : Round} {EndN : Slot → NamedBlock V}
    (hhist : CanonicalHeightSourceHistoryAt S rho q0 (r - 1)
      (EndN (S.hc.opening_slot (r - 1))))
    {k : Round} (hk : q0 ≤ k) (hkr : k < r - 1)
    {v : V} (hv : v ∈ rho.honest) {h : Height}
    (hrow : (actionAttestationAt S rho v k).height_pair.erase.height? = some h) :
    h ≤ (Protocol.derive_named S.E S.cfg
      (EndN (S.hc.opening_slot (r - 1)))).h := by
  obtain ⟨Q, -, -, hQEnd, hQh⟩ := hhist k hk hkr v hv h hrow
  rw [← hQh]
  exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hQEnd

/-- The early branch's contradiction: at a height strictly above the
round-`(r-1)` endpoint, no honest row of a round before `r - 1` exists. -/
theorem w4_noHonestRowAtHeight_early
    (S : Setup V) {rho : Run V}
    {q0 r : Round} {EndN : Slot → NamedBlock V} {H : Height}
    (hhist : CanonicalHeightSourceHistoryAt S rho q0 (r - 1)
      (EndN (S.hc.opening_slot (r - 1))))
    (hendLt : (Protocol.derive_named S.E S.cfg
      (EndN (S.hc.opening_slot (r - 1)))).h < H)
    {k : Round} (hk : q0 ≤ k) (hkr : k < r - 1)
    {v : V} (hv : v ∈ rho.honest)
    (hrow : (actionAttestationAt S rho v k).height_pair.erase.height? =
      some H) : False :=
  absurd (w4_rowHeight_le_endpointN S hhist hk hkr hv hrow)
    (Nat.not_le_of_lt hendLt)


#print axioms w4_rowHeight_le_endpointN
#print axioms w4_noHonestRowAtHeight_early


/--, closed properly: the corresponding branch available the field-level twin
`canonicalCarrierParentEqualities_of_canonicalSuffixFrom`
(`W4ExecSuffixRun.lean`), so the parent equalities come from
`canonicalSuffixFrom` alone — the one field this result's chain reads. -/
theorem w4_parentEqualities_of_canonicalSuffixFrom
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q0 : Round}
    (hsuffix : CanonicalSuffixFrom S rho (healingBoundaryTime S q0)) :
    ∀ r : Round, CanonicalRegimeRoundAt S rho q0 r →
      (∀ P0 : NamedBlock V,
          proposedBlockAt S rho (S.hc.opening_slot r) = some P0 →
          proposedParent S rho (S.hc.opening_slot r + 1) = P0.erase) ∧
        ∀ P1 : NamedBlock V,
          proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1 →
          proposedParent S rho (S.hc.opening_slot r + 2) = P1.erase := by
  intro r hround
  obtain ⟨P0, hP0⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot r)
  obtain ⟨P1, hP1⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot r + 1)
  have hpair := canonicalCarrierParentEqualities_of_canonicalSuffixFrom S adm
    hsuffix hround.afterBoundary hround.carrier hround.inHorizon P0 P1 hP0 hP1
  constructor
  · intro P0' hP0'
    have : P0' = P0 := by
      rw [hP0] at hP0'
      exact (Option.some.inj hP0').symm
    rw [this]
    exact hpair.1
  · intro P1' hP1'
    have : P1' = P1 := by
      rw [hP1] at hP1'
      exact (Option.some.inj hP1').symm
    rw [this]
    exact hpair.2


#print axioms w4_parentEqualities_of_canonicalSuffixFrom







/-- **The prepared SG root at the carrier's action read is below the opening
proposal.** This is `hactionRoot`, with no pin. -/
theorem w4_actionRoot_of_preparedFrame
    (S : Setup V) {rho : Run V}
    {q0 r : Round}
    (hround : CanonicalRegimeRoundAt S rho q0 r)
    (hframe : ∀ v ∈ rho.honest,
      Block.Preceq (PhaseGrades.nodeAnchor S (actionReadAt S rho v r) r)
        (actionStoreAt S rho v r).st.core.live_confirmed) :
    ∀ P0 : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r) = some P0 →
      ∀ v ∈ rho.honest,
        Block.Preceq
          (Protocol.get_sg_root_with
            (NamedProfile.gradeContract (actionStoreAt S rho v r).cache)
            S.E S.hc (actionStoreAt S rho v r).st.core.toHealing
            (S.hc.round_of (actionStoreAt S rho v r).s)) P0.erase := by
  intro P0 hP0 v hv
  have hlive : (actionStoreAt S rho v r).st.core.live_confirmed = P0.erase :=
    hround.openingLive v hv P0 hP0
  have hk : S.hc.round_of (actionStoreAt S rho v r).s = r :=
    actionStoreAt_round S rho v r
  have hanchor : Block.Preceq
      (PhaseGrades.nodeAnchor S (actionReadAt S rho v r) r) P0.erase := by
    rw [← hlive]
    exact hframe v hv
  rw [hk]
  exact hanchor

#print axioms w4_actionRoot_of_preparedFrame


/-- **The action-head fact over the prepared frame alone.** The slot-`+1`
head equality is discharged from the corresponding branch; the only remaining argument is
fk-regime's prepared-frame conclusion, which that branches proves from
`hround.afterBoundary`, `hround.inHorizon`, `hround.openingLive`, the moving
chain and `S.E.t_GST ≤ S.a (r - 1)` — all held at the discharge site. -/
theorem w4CarrierActionHeadPin_of_preparedFrame
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpostGST : S.E.t_GST ≤ S.a rGST)
    {q0 r : Round}
    (hround : CanonicalRegimeRoundAt S rho q0 r)
    (hframe : ∀ v ∈ rho.honest,
      Block.Preceq (PhaseGrades.nodeAnchor S (actionReadAt S rho v r) r)
        (actionStoreAt S rho v r).st.core.live_confirmed)
    (hdeadline : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤
      S.hc.opening_slot r + 1)
    (hpost : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot r + 1))
    (hhor : Protocol.support_cutoff S.E (S.hc.opening_slot r + 1) ≤
      rho.horizon) :
    ∀ P1 : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1 →
      ∀ v ∈ rho.honest, actionHeadAt S rho v r = P1.erase :=
  w4CarrierActionHeadPin_of_actionRoot S adm hcom hbelow hrec hdelay hpostGST
    hround hdeadline hpost hhor
    (w4_actionRoot_of_preparedFrame S hround hframe)

#print axioms w4CarrierActionHeadPin_of_preparedFrame






/-- **The action-head fact, PIN-FREE.** Both inputs are discharged: the
slot-`+1` head equality from the corresponding branch, and the prepared anchor bound from
the corresponding branch's relocated prepared frame. This closes the corresponding branch's
`W4SecondCarrierActionHeadPin` and this result's `actionHeadEq` outright. -/
theorem w4CarrierActionHeadPin_pinFree
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpostGST : S.E.t_GST ≤ S.a rGST)
    {q0 r : Round} {C End : Block V}
    (hround : CanonicalRegimeRoundAt S rho q0 r)
    (hchain : MovingChainAtCarrierFor S rho q0 r C End)
    (hpostPrev : S.E.t_GST ≤ S.a (r - 1))
    (hdeadline : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤
      S.hc.opening_slot r + 1)
    (hpost : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot r + 1))
    (hhor : Protocol.support_cutoff S.E (S.hc.opening_slot r + 1) ≤
      rho.horizon) :
    ∀ P1 : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1 →
      ∀ v ∈ rho.honest, actionHeadAt S rho v r = P1.erase :=
  w4CarrierActionHeadPin_of_preparedFrame S adm hcom hbelow hrec hdelay
    hpostGST hround
    (fun v hv =>
      (movingChainPreparedFrameAt_of_fields S adm hbelow hround.afterBoundary
        hround.inHorizon hround.openingLive hchain hpostPrev v hv).1)
    hdeadline hpost hhor

#print axioms w4CarrierActionHeadPin_pinFree

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
