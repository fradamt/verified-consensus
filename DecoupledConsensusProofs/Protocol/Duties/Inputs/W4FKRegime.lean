module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.CanonicalDensityDischarge
public import DecoupledConsensusProofs.Protocol.Grades.W4FKPreparedFrame
public import DecoupledConsensusProofs.Execution.W4DensityStructures
public import DecoupledConsensusProofs.Protocol.Grades.PostRecoveryCarrierHeightRead
public import DecoupledConsensusProofs.Protocol.ChainState.CanonicalRegimeRound
public import DecoupledConsensusProofs.Generic.CanonicalSuffix
public import DecoupledConsensusProofs.Protocol.ValidatorClient.CanonicalRegimeFirstVote
public import DecoupledConsensusProofs.Execution.MovingChainRoundFloorFields
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainBatch
public import DecoupledConsensusProofs.Protocol.Grades.VoteBelowSource
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsBridge
public import DecoupledConsensusProofs.Protocol.Grades.SeedRelativeGrade
public import DecoupledConsensusProofs.Protocol.Grades.SeedActionQ2
public import DecoupledConsensusProofs.Protocol.Grades.RelativeSeedK3
public import DecoupledConsensusProofs.Protocol.Grades.RelativeSeedSettlement
public import DecoupledConsensusProofs.Protocol.Schedule.SeedEntry
public import DecoupledConsensusProofs.Protocol.Grades.SeedFlush
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightProgressLadder
public import DecoupledConsensusProofs.Protocol.Grades.RelativeCarrierWindowGateOff
public import DecoupledConsensusProofs.Protocol.Grades.RelativeCarrierWindowFixedRoot
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightProgressClosureBatchAlignedPreceq
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedCeilingStep
public import DecoupledConsensusProofs.Protocol.Handlers.HonestProposalAdmission
public import DecoupledConsensusProofs.Generic.SuffixHistory
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.Schedule.W4ExecSuffix
public import DecoupledConsensusProofs.Protocol.Grades.W4FKGrade
public import DecoupledConsensusProofs.Generic.W4D3FinalitySpineCompose

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation




namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open DecoupledConsensusModel.Proofs
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]


/-! ## 3. The exact opening source at a carrier action -/


/-- Verbatim copy of `MovingChainRoundFloorFor.actionFGSource_some_eq_live`
(`CanonicalActionSourcesRun.lean:138`) with its dead `MovingChainRoundFloorFor`
binder dropped, as branches `w4-nl` already copied it
(`W4NonLostRun.lean:322`, `private`). The body reads only the two
prepared-frame inputs. -/
private theorem w4fkActionFGSourceEqLive
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


/-- **The carrier's height-read record from the execution core and the
moving-chain hand-off.** This is the selection twin of earlier's
`canonicalCarrierHeightReadAt_of_core_and_chain`
(`PostRecoveryCarrierHeightReadRun.lean:90`, blocked).

earlier identifies the source by batch alignment at the DEFAULT grade contract.
The selection's source is the prepared contract's clear walk, so the two prepared
frame inputs replace earlier's `BatchAligned` step; `movingChainPreparedFrameAt`
supplies them from the same hand-off, at the cost of the post-GST premise. -/
theorem canonicalCarrierHeightReadAt_of_fields_and_chain_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbot : BelowOneThird S rho.honest)
    {q0 r : Round}
    (hafter : healingBoundaryTime S q0 <
      Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hinHorizon : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    (hopeningLive : ∀ v ∈ rho.honest, ∀ P : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r) = some P →
      (actionStoreAt S rho v r).st.core.live_confirmed = P.erase)
    (hchain : MovingChainAtCarrier S rho q0 r)
    (hpost : S.E.t_GST ≤ S.a (r - 1)) :
    CanonicalCarrierHeightReadAt S rho q0 r := by
  obtain ⟨C, End, hchain⟩ := hchain
  have hq0r : q0 < r := w4fkRoundLtOfAfterBoundary S hafter
  have hrpos : 0 < r := Nat.zero_lt_of_lt hq0r
  have hconf0 : Protocol.confirmation_time S.E (S.hc.opening_slot r) ≤ rho.horizon := by
    refine le_trans ?_ hinHorizon
    rw [Protocol.confirmation_time_eq_support_cutoff_succ,
      Protocol.confirmation_time_eq_support_cutoff_succ]
    exact Proofs.Optimistic.support_cutoff_mono S.E
      (Nat.add_le_add_right (Nat.le_add_right (S.hc.opening_slot r) 2) 1)
  have hactionHor : S.a r ≤ rho.horizon := by
    simpa only [Setup.a, Protocol.a_eq_confirmation_time] using hconf0
  have hframe := movingChainPreparedFrameAt_of_fields S adm hbot hafter
    hinHorizon hopeningLive hchain hpost
  refine ⟨hopeningLive, ?_, hchain.heightHistory⟩
  intro v hv P hP Q hsource
  have hres := w4fkActionFGSourceEqLive S adm hrpos hactionHor hv
    (hframe v hv).1 (hframe v hv).2 hsource
  rw [hres]
  exact hopeningLive v hv P hP

#print axioms canonicalCarrierHeightReadAt_of_fields_and_chain_named







private theorem w4fkNatOneLeSucc (a : Nat) : 1 ≤ a + 1 := by omega

private theorem w4fkNatTwoLeOfBandGt {H1 H2 c1 c2 : Nat}
    (hgt : H1 + (c2 - c1) < H2) (hc : c1 < c2) : H1 + 2 ≤ H2 := by omega

private theorem w4fkNatPredLtOfTwoLe {H1 H2 : Nat} (h : H1 + 2 ≤ H2) :
    H2 - 1 < H2 := by omega

private theorem w4fkNatOneLePredOfTwoLe {H1 H2 : Nat} (h : H1 + 2 ≤ H2) :
    1 ≤ H2 - 1 := by omega

private theorem w4fkNatHeightSplit {H1 H2 : Nat} (h : H1 + 2 ≤ H2) :
    H2 - 1 = H1 + 1 + (H2 - H1 - 2) := by omega

private theorem w4fkNatNotSuccLeSelf {a : Nat} (h : a + 1 ≤ a) : False := by omega

private theorem w4fkNatBandContradiction
    {H1 H2 c1 c2 k k' d : Nat}
    (hgt : H1 + (c2 - c1) < H2) (hd : d = H2 - H1 - 2) (hc12 : c1 < c2)
    (hk : k < c2) (hk' : k' + d ≤ k) (hanchor : c1 < k') : False := by omega

private theorem w4fkNatSuccLtOfLtOfLt {q0 r c : Nat} (h1 : q0 < r)
    (h2 : r < c) : q0 + 1 < c := by omega

/-- Verbatim copy of the `private` `round_lt_of_action_lt`
(`CanonicalDensityDischargeRun.lean:103`). -/
private theorem w4fkRoundLtOfActionLt (S : Setup V) {k r : Round}
    (h : S.a k < S.a r) : k < r := by
  by_contra hnot
  exact absurd ((Assembly.a_mono S (Nat.le_of_not_gt hnot)).trans_lt h)
    (lt_irrefl _)

/-- Verbatim copy of the `private` `liveConfirmed_mem_storeBeforeTime_action`
(`CanonicalDensityDischargeRun.lean:219`). -/
private theorem w4fkLiveConfirmedMemStoreBeforeTimeAction
    (S : Setup V) {rho : Run V} (_adm : Admissible S rho) (v : V) (r : Round) :
    (actionStoreAt S rho v r).live_confirmed ∈
      (rho.storeBeforeTime S v (S.a r)).T := by
  let n := rho.stateBeforeTime S (S.a r) v
  let cr := NamedActionReads.confirmationReadFrom S n (S.a r)
  have hn : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg n.st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a r) v).1
  have hcr : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg cr.st := by
    exact Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg n.st (S.a r) hn
  have ha := Proofs.NamedConfirmationMembership.invariant_update cr.cache
    S.E S.hc S.cfg cr.st (S.E.slotOf (S.a r) - 1) hcr
  have hmem :
      (Protocol.NamedDuties.update_confirmation_with
        (DecoupledConsensusModel.Protocol.frameContract cr.cache) S.E S.hc cr.st
          (S.E.slotOf (S.a r) - 1)).core.live_confirmed ∈
        (Protocol.NamedDuties.update_confirmation_with
          (DecoupledConsensusModel.Protocol.frameContract cr.cache) S.E S.hc cr.st
            (S.E.slotOf (S.a r) - 1)).core.T := ha.2.1
  change (actionStoreAt S rho v r).st.core.live_confirmed ∈
    (rho.stateBeforeTime S (S.a r) v).st.core.T
  simpa only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
    NamedActionReads.actionReadFrom, NamedActionReads.preparedCache, cr,
    NamedActionReads.confirmationReadFrom,
    NamedDuties.confirmation_core,
    Protocol.NamedStore.setClock, n, Run.storeBeforeTime]
    using hmem


/-- Verbatim copy of branches `w4-nl`'s `w4RunBlockOfMemStoreBeforeTime`
(`W4NonLostRun.lean:69`, `private`). -/
private theorem w4fkRunBlockOfMemStoreBeforeTime
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {t : Time} {D : NamedBlock V}
    (hD : D ∈ (rho.storeBeforeTime S w t).bodies) : RunBlock S rho D := by
  obtain ⟨n, hn, -⟩ :=
    Proofs.Bridges.stateBeforeTime_eq_stateBefore S adm.toNamedScheduleWellFormed t
  have hD' : D ∈ (rho.stateBefore S n w).st.bodies := by
    simpa only [Run.storeBeforeTime, hn] using hD
  exact Proofs.Bridges.runBlock_of_stateBefore_mem S hw hD'

/-- Two named run blocks with one erasure are one block. -/
private theorem w4fkRunBlockUniqueOfEraseEq
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {A D : NamedBlock V} (hA : RunBlock S rho A) (hD : RunBlock S rho D)
    (herase : A.erase = D.erase) : A = D :=
  adm.toNamedRootCollisionFree.root_injective A D hA hD A D
    (Or.inl (Proofs.NamedAncestry.named_self A)) (Or.inr (Proofs.NamedAncestry.named_self D))
    (by rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root D, herase])

/-- The named opening proposal is a retained body at every honest action read
of its own carrier round: the action confirms it, and a confirmed block is
processed, so the tree view returns a named body that root collision freedom
identifies with the proposal itself. -/
private theorem w4fkOpeningProposalMemBodies
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {c : Round} (hcpos : 0 < S.hc.opening_slot c)
    (hprop : S.E.proposer (S.hc.opening_slot c) ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E (S.hc.opening_slot c) ≤ rho.horizon)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot c) = some P)
    {v : V} (hv : v ∈ rho.honest)
    (hlive : (actionStoreAt S rho v c).live_confirmed = P.erase) :
    P ∈ (rho.storeBeforeTime S v (S.a c)).bodies := by
  have hmem : P.erase ∈ (rho.stateBeforeTime S (S.a c) v).st.core.T := by
    have hl := w4fkLiveConfirmedMemStoreBeforeTimeAction S adm v c
    rw [hlive] at hl
    exact hl
  obtain ⟨D, hD, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho (S.a c) v hmem
  have hDrun : RunBlock S rho D :=
    w4fkRunBlockOfMemStoreBeforeTime S adm hv (t := S.a c) hD
  have hPrun : RunBlock S rho P :=
    Protocol.proposedBlock_runBlock S adm hcpos hprop hhor hP
  have hDP : D = P := w4fkRunBlockUniqueOfEraseEq adm hDrun hPrun hDerase
  rw [← hDP]
  exact hD


/-- **Every honest row at a round at or before a carrier is at most that
carrier's opening height.** Named twin of
`CanonicalDensityDischargeRun.lean:284` (blocked). -/
theorem honestHeightRowAt_le_carrierOpeningHeight_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q0 c : Round} (hregime : CanonicalCarrierHeightReadAt S rho q0 c)
    (hcpos : 0 < S.hc.opening_slot c)
    (hprop : S.E.proposer (S.hc.opening_slot c) ∈ rho.honest)
    (hproposalHor : Protocol.proposal_time S.E (S.hc.opening_slot c) ≤ rho.horizon)
    (hold : honestHMaxAt S rho (S.a q0) ≤ carrierOpeningHeight S rho c)
    {h : Height} {k : Round} (hk : k ≤ c)
    (hrow : HonestHeightRowAt S rho h k) :
    h ≤ carrierOpeningHeight S rho c := by
  obtain ⟨v, hv, hrowv⟩ := hrow
  rcases Nat.lt_or_ge k q0 with hprefix | hpost
  · obtain ⟨Q, -, hQbody, hQheight⟩ := honestRow_height_le_source S adm hv hrowv
    have hQpre : Q ∈ (rho.stateBeforeTime S (S.a k) v).st.bodies := by
      simpa only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
        NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hQbody
    have hbound :=
      Proofs.NamedStoreBridge.heights_le_hMax_stateBeforeTime S rho (S.a k) v Q hQpre
    rw [hQheight] at hbound
    have hlocal : h ≤ (actionStoreAt S rho v k).st.core.h_max := hbound
    exact ((hlocal.trans
      (actionStoreHMax_le_honestHMaxAt_action S adm hv k)).trans
        (honestHMaxAt_mono S adm.toNamedScheduleWellFormed
          (Assembly.a_mono S (Nat.le_of_lt hprefix)))).trans hold
  · rcases Nat.lt_or_ge k c with hbefore | hat
    · exact honestHeightRowAt_le_of_heightHistory S hregime hpost hbefore
        ⟨v, hv, hrowv⟩
    · have hkc : k = c := Nat.le_antisymm hk hat
      subst hkc
      obtain ⟨P, hP⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot k)
      obtain ⟨Q, hsource, hQbody, hQheight⟩ :=
        honestRow_height_le_source S adm hv hrowv
      have hQeq : Q.erase = P.erase :=
        hregime.openingSource v hv P hP Q.erase hsource
      have hQpre : Q ∈ (rho.storeBeforeTime S v (S.a k)).bodies := by
        simpa only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
          NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
          NamedActionReads.preparedCache, Run.storeBeforeTime] using hQbody
      have hQrun : RunBlock S rho Q :=
        w4fkRunBlockOfMemStoreBeforeTime S adm hv (t := S.a k) hQpre
      have hPrun : RunBlock S rho P :=
        Protocol.proposedBlock_runBlock S adm hcpos hprop hproposalHor hP
      have hQP : Q = P := w4fkRunBlockUniqueOfEraseEq adm hQrun hPrun hQeq
      have hPcanon : P = canonicalProposal S rho (S.hc.opening_slot k) :=
        Option.some.inj (hP.symm.trans
          (canonicalProposal_spec S rho (S.hc.opening_slot k)))
      rw [carrierOpeningHeight, ← hPcanon, ← hQheight, hQP]

#print axioms honestHeightRowAt_le_carrierOpeningHeight_named


/-- **A height strictly below a carrier's opening height has an honest row at
a strictly earlier round.** Named twin of
`CanonicalDensityDischargeRun.lean:328` (blocked). -/
theorem exists_honestHeightRowAt_below_carrierOpening_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbot : BelowOneThird S rho.honest)
    {q0 c : Round} (hregime : CanonicalCarrierHeightReadAt S rho q0 c)
    (hcpos : 0 < S.hc.opening_slot c)
    (hprop : S.E.proposer (S.hc.opening_slot c) ∈ rho.honest)
    (hproposalHor : Protocol.proposal_time S.E (S.hc.opening_slot c) ≤ rho.horizon)
    {h : Height} (hpos : 1 ≤ h) (hlt : h < carrierOpeningHeight S rho c) :
    ∃ k : Round, k < c ∧ HonestHeightRowAt S rho h k := by
  have hmajority := AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbot
  obtain ⟨v, -, hv⟩ := AlignedRoundLemmas.honest_member_of_quorum hbot
    (AlignedRoundLemmas.honestQuorum_of_belowOneThird hbot)
  obtain ⟨P, hP⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot c)
  have hPcanon : P = canonicalProposal S rho (S.hc.opening_slot c) :=
    Option.some.inj (hP.symm.trans
      (canonicalProposal_spec S rho (S.hc.opening_slot c)))
  have hPbody : P ∈ (rho.storeBeforeTime S v (S.a c)).bodies :=
    w4fkOpeningProposalMemBodies S adm hcpos hprop hproposalHor hP hv
      (hregime.openingLive v hv P hP)
  have hcross : h < (Protocol.derive_named S.E S.cfg P).h := by
    rw [hPcanon]
    simpa only [carrierOpeningHeight] using hlt
  obtain ⟨k, hk, hrow⟩ :=
    exists_honestHeightRowAt_of_crossing S adm hmajority hPbody hpos hcross
  exact ⟨k, w4fkRoundLtOfActionLt S hk, hrow⟩

#print axioms exists_honestHeightRowAt_below_carrierOpening_named


/-- **The carrier density bound.** Named twin of
`CanonicalDensityDischargeRun.lean:389` (blocked); earlier's counting argument
verbatim over the two named row bounds. -/
theorem carrierOpeningHeight_le_add_sub_of_regime_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbot : BelowOneThird S rho.honest)
    {q0 c1 c2 : Round} (hc12 : c1 < c2)
    (hc1pos : 0 < S.hc.opening_slot c1) (hc2pos : 0 < S.hc.opening_slot c2)
    (hprop1 : S.E.proposer (S.hc.opening_slot c1) ∈ rho.honest)
    (hprop2 : S.E.proposer (S.hc.opening_slot c2) ∈ rho.honest)
    (hhor1 : Protocol.proposal_time S.E (S.hc.opening_slot c1) ≤ rho.horizon)
    (hhor2 : Protocol.proposal_time S.E (S.hc.opening_slot c2) ≤ rho.horizon)
    (hregime1 : CanonicalCarrierHeightReadAt S rho q0 c1)
    (hregime2 : CanonicalCarrierHeightReadAt S rho q0 c2)
    (hold : honestHMaxAt S rho (S.a q0) ≤ carrierOpeningHeight S rho c1) :
    carrierOpeningHeight S rho c2 ≤
      carrierOpeningHeight S rho c1 + (c2 - c1) := by
  have hmajority := AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbot
  by_contra hnot
  have hgt : carrierOpeningHeight S rho c1 + (c2 - c1) <
      carrierOpeningHeight S rho c2 := Nat.lt_of_not_ge hnot
  have hge2 : carrierOpeningHeight S rho c1 + 2 ≤
      carrierOpeningHeight S rho c2 := w4fkNatTwoLeOfBandGt hgt hc12
  obtain ⟨k, hk, hrow⟩ :=
    exists_honestHeightRowAt_below_carrierOpening_named S adm hbot hregime2
      hc2pos hprop2 hhor2
      (w4fkNatOneLePredOfTwoLe hge2) (w4fkNatPredLtOfTwoLe hge2)
  rw [w4fkNatHeightSplit hge2] at hrow
  obtain ⟨k', hk', hrow'⟩ :=
    exists_honestHeightRowAt_descend S adm hmajority
      (w4fkNatOneLeSucc (carrierOpeningHeight S rho c1)) _ k hrow
  have hanchor : c1 < k' := by
    by_contra hle
    exact w4fkNatNotSuccLeSelf
      (honestHeightRowAt_le_carrierOpeningHeight_named S adm hregime1
        hc1pos hprop1 hhor1 hold (Nat.le_of_not_gt hle) hrow')
  exact w4fkNatBandContradiction hgt rfl hc12 hk hk' hanchor

#print axioms carrierOpeningHeight_le_add_sub_of_regime_named


/-! ## 5. The density interface and the carrier record -/

/-- Verbatim copy of the `private` `confirmationTime_plusTwo_le_of_action_succ`
(`CanonicalDensityDischargeRun.lean:561`). -/
private theorem w4fkConfirmationPlusTwoLeOfActionSucc
    (S : Setup V) {rho : Run V} {r : Round}
    (h : S.a (r + 1) ≤ rho.horizon) :
    Protocol.confirmation_time S.E (S.hc.opening_slot r + 2) ≤ rho.horizon := by
  have hslot : S.hc.opening_slot r + 2 ≤ S.hc.opening_slot (r + 1) := by
    calc
      S.hc.opening_slot r + 2 ≤ S.hc.opening_slot r + S.hc.R :=
        Nat.add_le_add_left S.hc.R_ge_two _
      _ = S.hc.opening_slot (r + 1) := by
        simp only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
  have hmono : Protocol.confirmation_time S.E (S.hc.opening_slot r + 2) ≤
      Protocol.confirmation_time S.E (S.hc.opening_slot (r + 1)) := by
    rw [Protocol.confirmation_time_eq_support_cutoff_succ,
      Protocol.confirmation_time_eq_support_cutoff_succ]
    exact Proofs.Optimistic.support_cutoff_mono S.E (Nat.add_le_add_right hslot 1)
  have haction : Protocol.confirmation_time S.E
      (S.hc.opening_slot (r + 1)) = S.a (r + 1) := by
    simp only [Setup.a, Protocol.a_eq_confirmation_time]
  rw [haction] at hmono
  exact hmono.trans h

/-- The opening slot of a positive round is positive. -/
private theorem w4fkOpeningSlotPos (S : Setup V) {c : Round} (hc : 0 < c) :
    0 < S.hc.opening_slot c := by
  simp only [Protocol.HealConfig.opening_slot]
  exact Nat.mul_pos hc (Nat.zero_lt_of_lt S.hc.R_ge_two)

/-- The carrier's own opening proposal instant is in the horizon once the next
action instant is. -/
private theorem w4fkOpeningProposalHor
    (S : Setup V) {rho : Run V} {c : Round} (h : S.a (c + 1) ≤ rho.horizon) :
    Protocol.proposal_time S.E (S.hc.opening_slot c) ≤ rho.horizon := by
  have hconf : Protocol.confirmation_time S.E (S.hc.opening_slot c) = S.a c := by
    simp only [Setup.a, Protocol.a_eq_confirmation_time]
  refine (Protocol.proposal_time_le_confirmation_time S.E _).trans ?_
  rw [hconf]
  exact (Assembly.a_mono S (Nat.le_succ c)).trans h

























/-- **: the prepared suffix execution and the moving-chain fold discharge
the prepared density interface.** Same route as
`canonicalCarrierDensityFrom_of_movingChain_named`, with the carrier's
`openingLive` taken from the prepared lifecycle producer
(`canonicalOpeningLifecycleAt_of_executionPrepared`,
`W4ExecSuffixRun.lean:1200`) instead of the plain execution core. -/
theorem canonicalCarrierDensityFromPrepared_of_movingChain_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbot : BelowOneThird S rho.honest)
    {q0 : Round}
    (hexec : CanonicalSuffixExecutionPrepared S rho q0)
    (hafterAll : ∀ r : Round, q0 + 1 < r →
      healingBoundaryTime S q0 <
        Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hchain : MovingChainAtCarrierFrom S rho q0)
    (hpost : S.E.t_GST ≤ S.a q0) :
    CanonicalCarrierDensityFromPrepared S rho q0 := by
  have hmajority := AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbot
  have hregime : ∀ r : Round, q0 + 1 < r → ProposerCarrierAt S rho r →
      Protocol.confirmation_time S.E (S.hc.opening_slot r + 2) ≤ rho.horizon →
      CanonicalCarrierHeightReadAt S rho q0 r := by
    intro r hr hcarrier hhor
    have hafter := hafterAll r hr
    have hprevPost : S.E.t_GST ≤ S.a (r - 1) :=
      hpost.trans (Assembly.a_mono S (Nat.le_sub_one_of_lt (Nat.lt_of_succ_lt hr)))
    have hactionHor : S.a r ≤ rho.horizon := by
      have hconf0 : Protocol.confirmation_time S.E (S.hc.opening_slot r) ≤
          rho.horizon := by
        refine le_trans ?_ hhor
        rw [Protocol.confirmation_time_eq_support_cutoff_succ,
          Protocol.confirmation_time_eq_support_cutoff_succ]
        exact Proofs.Optimistic.support_cutoff_mono S.E
          (Nat.add_le_add_right (Nat.le_add_right (S.hc.opening_slot r) 2) 1)
      simpa only [Setup.a, Protocol.a_eq_confirmation_time] using hconf0
    have hlifecycle := canonicalOpeningLifecycleAt_of_executionPrepared
      S hcom hexec hafter hcarrier.1 hactionHor
    exact canonicalCarrierHeightReadAt_of_fields_and_chain_named S adm hbot
      hafter hhor (fun v hv P hP => (hlifecycle P hP v hv).1)
      (hchain r hafter hcarrier hhor) hprevPost
  refine ⟨hexec, ?_, ?_⟩
  · intro c1 c2 hq1 hc12 hcar1 hcar2 hhor1 hhor2 hold
    exact carrierOpeningHeight_le_add_sub_of_regime_named S adm hbot hc12
      (w4fkOpeningSlotPos S (Nat.zero_lt_of_lt hq1))
      (w4fkOpeningSlotPos S (Nat.zero_lt_of_lt (hq1.trans hc12)))
      hcar1.1 hcar2.1
      (w4fkOpeningProposalHor S hhor1) (w4fkOpeningProposalHor S hhor2)
      (hregime c1 hq1 hcar1 (w4fkConfirmationPlusTwoLeOfActionSucc S hhor1))
      (hregime c2 (hq1.trans hc12) hcar2
        (w4fkConfirmationPlusTwoLeOfActionSucc S hhor2)) hold
  · intro r c hq0 hrc hcar hhor hgain
    exact honestHMaxAt_sub_one_le_carrierOpeningHeight_of_gain S adm hmajority
      (Nat.le_of_lt hq0) hrc
      (hregime c (w4fkNatSuccLtOfLtOfLt hq0 hrc) hcar
        (w4fkConfirmationPlusTwoLeOfActionSucc S hhor)) hgain

#print axioms canonicalCarrierDensityFromPrepared_of_movingChain_named

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
