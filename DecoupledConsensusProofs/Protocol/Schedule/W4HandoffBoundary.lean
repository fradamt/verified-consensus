module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainHandoffExports
public import DecoupledConsensusProofs.Execution.W4HandoffStructures
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.SGLifetimeNamed
public import DecoupledConsensusProofs.Protocol.ChainState.RowFreshness
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.W4HeightSourceHistory
public import DecoupledConsensusProofs.Generic.W4RecordPins
public import DecoupledConsensusProofs.Protocol.Grades.W4FKGrade
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalAdoptionNamedClosed
public import DecoupledConsensusProofs.Execution.SeedBaseCone
public import DecoupledConsensusProofs.Execution.OpeningCarrierSelection

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# The moving-chain handoff boundary at a post-deadline carrier ( h1)

`MovingChainHandoffBoundary` (`MovingChainBaseRun.lean:178`) is the input all
three moving-chain record exports share, and neither earlier nor the selection has a
producer for it: earlier's live route goes through `MovingChainSplitBoundary`,
whose floor block and endpoint block are allowed to differ, and converts in the
other direction (`MovingChainSplitBoundaryRun.lean:67`).

This leaf closes the two mechanical fields and names the three protocol fields.

* `height` is the definition of `M0`.
* `processed` is earlier's own all-honest head bound at the boundary slot
  (`hDheads` in `exists_uniformHandoffBoundary`, `PostSafetyHandoffRun.lean:251`,
  red import path), pushed through the vote-duty store. That bound's producer
  is `genuineConfirmation_allHonestHeads_succ_after_GST`
  (`ConfirmationCanonicalRun.lean:275`, red behind `FGSafetySourceRun` and
  `RecoveryInitialSourceJoinRun`) at `c = deadline + 1`, `s = opening_slot q + 1`,
  and its only handoff-side input is `HealedTwoSlotHandoff.carrier_genuine`. The generalized copy of
  `processed_at_next_proposal_of_below_honest_heads`
  (`MovingChainSplitBoundaryRun.lean:178`, red import path) is
  `w4ProcessedErased_of_below_honest_heads`: the original fixes the cutoff at
  the next proposal instant, the handoff boundary reads it at the support
  cutoff of the same slot, which is earlier.
* `targets`, `frontierCap` and `carrierCeiling` stay hypotheses.

`frontierCap` is reported as a Open by this branches: see
`the proof record`. The row-cap half of this file is the
additive repair, and shows that the fold never needs more than the row cap.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.NamedRecoveryRead
open Protocol
open Proofs.Optimistic
open Proofs.HealingLemmas
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

theorem w4ProcessedErased_of_below_honest_heads
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {d : Slot} {D : Block V} {t1 : Time}
    (hheads : ∀ v ∈ rho.honest, Block.Preceq D (voteDutyHead S rho v d))
    (ht1 : Protocol.vote_time S.E d ≤ t1) :
    ∀ v ∈ rho.honest,
      D ∈ (rho.stateBefore S (strictEventIndex rho t1) v).st.core.T := by
  intro v hv
  have hheadMem : voteDutyHead S rho v d ∈
      (rho.storeBeforeTime S v (Protocol.vote_time S.E d)).T :=
    voteDutyHead_mem_voteDutyStore S adm v d
  have hpc := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
    (Protocol.vote_time S.E d) v
  change voteDutyHead S rho v d ∈
      (rho.storeBeforeTime S v (Protocol.vote_time S.E d)).core.T at hheadMem
  have hDmem := Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2 _ _
    hheadMem (hheads v hv)
  have hDmem' : D ∈
      (rho.storeBeforeTime S v (Protocol.vote_time S.E d)).core.T := by
    simpa only [Run.storeBeforeTime] using hDmem
  rw [storeBeforeTime_eq_stateBefore_strictEventIndex S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed] at hDmem'
  exact stateBefore_T_subset S rho v _ (strictEventIndex_mono rho ht1) hDmem'


theorem w4Processed_of_below_honest_heads
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {d : Slot} {D : NamedBlock V} {t1 : Time}
    (hDrun : RunBlock S rho D)
    (hheads : ∀ v ∈ rho.honest, Block.Preceq D.erase (voteDutyHead S rho v d))
    (ht1 : Protocol.vote_time S.E d ≤ t1) :
    ∀ v ∈ rho.honest,
      D ∈ (rho.stateBefore S (strictEventIndex rho t1) v).st.bodies := by
  intro v hv
  have hmem := w4ProcessedErased_of_below_honest_heads S adm hheads ht1 v hv
  have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho
    (strictEventIndex rho t1) v).1.1.1
  rw [hcoh.1] at hmem
  obtain ⟨X, hX, hXerase⟩ := Finset.mem_image.mp hmem
  have hXrun : RunBlock S rho X := Proofs.Bridges.runBlock_of_stateBefore_mem S hv hX
  have hroot : X.root = D.root := by
    rw [← Proofs.NamedWire.erase_root X, ← Proofs.NamedWire.erase_root D, hXerase]
  have hXD : X = D :=
    adm.toNamedRootCollisionFree.root_injective X D hXrun hDrun X D
      (Or.inl (Proofs.NamedAncestry.named_self X))
      (Or.inr (Proofs.NamedAncestry.named_self D)) hroot
  exact hXD ▸ hX


/-- Verbatim copy of the private `confirmation_mono`
(`PostSafetyHandoffRun.lean:116`, red import path). -/
private theorem w4_confirmation_time_mono (E : Env V) {s t : Slot} (h : s ≤ t) :
    Protocol.confirmation_time E s ≤ Protocol.confirmation_time E t :=
  Int.add_le_add_right (Protocol.proposal_time_mono E h) _













theorem w4BoundaryHeads_of_carrierGenuine
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {q : Round}
    (hq : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ q)
    (hhor : Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤
      rho.horizon)
    {carrier : V} (hcarrier : carrier ∈ rho.honest) {D : NamedBlock V}
    (hgenuine : GenuineConfirmationWith
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho carrier
          (S.hc.opening_slot q + 1)).cache)
      S.E S.hc (Proofs.Optimistic.confStore S rho carrier (S.hc.opening_slot q + 1))
      (S.hc.opening_slot q + 1) D.erase) :
    ∀ w ∈ rho.honest,
      Block.Preceq D.erase
        (voteDutyHead S rho w (S.hc.opening_slot q + 2)) := by
  have hqTwo : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ q :=
    (Nat.le_succ _).trans hq
  have hslots : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 1 + 1) + 1 ≤
      S.hc.opening_slot q + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul_right S.hc.R hqTwo) 1
  have hconfOne : Protocol.confirmation_time S.E (S.hc.opening_slot q + 1) ≤
      rho.horizon :=
    (w4_confirmation_time_mono S.E
      (Nat.add_le_add_left (by decide : 1 ≤ 3) (S.hc.opening_slot q))).trans hhor
  have hvoteTwo : Protocol.vote_time S.E (S.hc.opening_slot q + 2) ≤
      rho.horizon :=
    (vote_time_le_confirmation_time S.E (S.hc.opening_slot q + 2)).trans
      ((w4_confirmation_time_mono S.E
        (Nat.add_le_add_left (by decide : 2 ≤ 3) (S.hc.opening_slot q))).trans
        hhor)
  intro w hw
  exact genuineConfirmationWith_preceq_laterVoterHeads_after_GST S adm hcom
    hbelow hrec hdelay hpost (Nat.le_refl _) hslots hconfOne hcarrier hgenuine
    (S.hc.opening_slot q + 2) (Nat.le_refl _) hvoteTwo w hw

#print axioms w4BoundaryHeads_of_carrierGenuine




/-- Verbatim copy of the private `handoff_carrier_round_bounds`
(`MovingChainProtectedBoundaryRun.lean:68`, red import path). -/
private theorem w4_handoff_carrier_round_bounds {R q r deadline : Nat}
    (hR : 2 ≤ R) (hlate : deadline + 2 ≤ q)
    (hr : (q * R + 3) / R = r + 1) :
    deadline ≤ r - 1 ∧ 0 < r ∧ r ≤ q := by
  have hpos : 0 < R := lt_of_lt_of_le (by decide : 0 < 2) hR
  have hlo : q ≤ (q * R + 3) / R :=
    (Nat.le_div_iff_mul_le hpos).2 (Nat.le_add_right _ _)
  have hhi : (q * R + 3) / R < q + 2 := by
    apply (Nat.div_lt_iff_lt_mul hpos).2
    rw [Nat.add_mul]
    omega
  rw [hr] at hlo hhi
  omega

/-- **The carrier ceiling**, both arms, from the head equality at the
endpoint's own slot. -/
theorem w4CarrierCeiling_of_headEq
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {q : Round}
    (hq : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ q)
    (hhor : Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤
      rho.horizon)
    {D : NamedBlock V}
    (hheadEq : ∀ w ∈ rho.honest,
      voteDutyHead S rho w (S.hc.opening_slot q + 1) = D.erase) :
    ∀ r : Round, S.hc.round_of (S.hc.opening_slot q + 3) = r + 1 →
      ∀ u ∈ rho.honest, Block.Preceq (actionSGBlockAt S rho u r) D.erase := by
  intro r hr u hu
  obtain ⟨hrLate, hrpos, hrq⟩ :=
    w4_handoff_carrier_round_bounds S.hc.R_ge_two
      ((Nat.le_succ _).trans hq) hr
  obtain ⟨w, hw⟩ := honest_nonempty_of_honestCommittees hcom
  have hrsucc : r - 1 + 1 = r := Nat.sub_add_cancel hrpos
  have hdead : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ r - 1 := by
    omega
  have hd : S.hc.opening_slot (r - 1 + 1) + 1 ≤ S.hc.opening_slot q + 1 := by
    rw [hrsucc]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right S.hc.R hrq) 1
  have hdhor : Protocol.vote_time S.E (S.hc.opening_slot q + 1) + S.E.Δ ≤
      rho.horizon := by
    rw [Proofs.Optimistic.vote_time_add_delta]
    exact (Protocol.support_cutoff_le_confirmation_time S.E
      (S.hc.opening_slot q + 1)).trans
      ((w4_confirmation_time_mono S.E
        (Nat.add_le_add_left (by decide : 1 ≤ 3) (S.hc.opening_slot q))).trans
        hhor)
  have hstep := actionSGBlock_preceq_voterHeadAt_after_GST S adm hcom hbelow
    hrec hdelay hpost hdead hd hdhor hu hw
  rw [hrsucc] at hstep
  have hhead : voterHeadAt S rho w (S.hc.opening_slot q + 1) = D.erase :=
    hheadEq w hw
  rw [hhead] at hstep
  exact hstep

#print axioms w4CarrierCeiling_of_headEq


#print axioms w4ProcessedErased_of_below_honest_heads
#print axioms w4Processed_of_below_honest_heads


/-! ## The row-cap boundary: the additive repair for `frontierCap`

`frontierCap` is consumed in exactly one place. `MovingChainHandoffBoundary.
toSplitBoundary` turns it into the two row caps, and
`movingSlotFoldAt_base_of_handoff` (`MovingChainExecutionRun.lean:459`, parked)
hands it to `movingBoundaryHistory_toFreeze` (`MovingChainBoundaryRun.lean:196`)
as `hold`, whose only use is `movingFrontierChainState_bootstrapAt`, which
immediately weakens it to the same two row caps through
`namedRowCap_of_namedEndpointHeight` and calls
`movingFrontierChainState_bootstrapAt_of_rowCap`.

The row caps say that honest height rows emitted before the cutoff are at or
below the boundary block's height. `frontierCap` says that no honest STORE
holds a block above that height at the cutoff, which is a strictly stronger
claim: a quorum of rows at `M0` justifies height `M0 + 1` for any later block
carrying it, and the block is in honest stores before the cutoff. The
structure below is the same record with the two row caps in place of
`frontierCap`; every downstream use is reproduced from it.
-/






























/-- A round action emitted strictly before the boundary cutoff belongs to a
round at or below the handoff round. -/
private theorem w4_round_le_of_action_lt_supportCutoff
    (S : Setup V) {r q : Round}
    (h : S.a r < Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) :
    r ≤ q := by
  by_contra hnot
  have hqr : q + 1 ≤ r := Nat.succ_le_of_lt (Nat.lt_of_not_ge hnot)
  have hstep : S.hc.opening_slot q + 2 ≤ S.hc.opening_slot (q + 1) := by
    simp only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add_left S.hc.R_ge_two (q * S.hc.R)
  have hslot : S.hc.opening_slot q + 2 ≤ S.hc.opening_slot r :=
    hstep.trans (Nat.mul_le_mul_right S.hc.R hqr)
  have hle : Protocol.support_cutoff S.E (S.hc.opening_slot q + 2) ≤ S.a r := by
    rw [Setup.a, Protocol.a_eq_confirmation_time]
    exact (Protocol.support_cutoff_le_confirmation_time S.E _).trans
      (w4_confirmation_time_mono S.E hslot)
  exact absurd h (not_lt.mpr hle)

/-- **The `targets` field from the named height-source history.** -/
theorem w4Targets_of_heightSourceHistory
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q q0 : Round} {D : NamedBlock V}
    (hheightHistory : CanonicalHeightSourceHistoryAt S rho q0 (q + 1) D)
    (hthreshold : honestHMaxAt S rho (S.a q0) <
      (derive_named S.E S.cfg D).h - 1) :
    ∀ (a : NamedAttestation V) (ta : Time),
      a.val_index ∈ rho.honest →
      rho.emits S a.val_index (Object.attest a) ta →
      ta < Protocol.support_cutoff S.E (S.hc.opening_slot q + 2) →
      ∀ (hh : Height) (target : BlockId),
      (derive_named S.E S.cfg D).h - 1 ≤ hh →
      a.height_pair = NamedHeightPair.vote hh target false →
      ∀ X : NamedBlock V, RunBlock S rho X → X.erase.root = target →
      Block.Preceq X.erase D.erase := by
  intro a ta ha hemit hta hh target hhigh hrow X hXrun hXroot
  obtain ⟨j, hjev, hmem⟩ := hemit
  have hemits : rho.emits S a.val_index (Object.attest a) ta := ⟨j, hjev, hmem⟩
  obtain ⟨-, ht⟩ := Proofs.Optimistic.emits_attest_shape S hemits
  have htick : Event.tick a.val_index ta ∈ rho.events :=
    List.mem_of_getElem? hjev
  have hhorRound : S.a a.round ≤ rho.horizon := by
    have hle := (adm.in_horizon _ htick).2
    rw [ht] at hle
    exact hle
  have hexact := honest_emits_exact_actionAttestationAt S adm ha a.round hhorRound
  have haEq : a = actionAttestationAt S rho a.val_index a.round := by
    refine Proofs.Optimistic.emits_attest_unique S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hemits hexact ?_
    exact (actionAttestationAt_shape S rho a.val_index a.round).2.1.symm
  have hpair : (actionAttestationAt S rho a.val_index a.round).height_pair =
      NamedHeightPair.vote hh target false := by
    rw [← haEq]; exact hrow
  have hheight :
      (actionAttestationAt S rho a.val_index a.round).height_pair.erase.height? =
        some hh := by
    rw [hpair]; rfl
  have habove : honestHMaxAt S rho (S.a q0) < hh :=
    lt_of_lt_of_le hthreshold hhigh
  have hq0 : q0 < a.round := honestRow_after_frontier S adm ha habove hheight
  have hlt : a.round < q + 1 :=
    Nat.lt_succ_of_le (w4_round_le_of_action_lt_supportCutoff S (ht ▸ hta))
  obtain ⟨Q, hsource, hrun, hpreceq, hQheight⟩ :=
    hheightHistory a.round (Nat.le_of_lt hq0) hlt a.val_index ha hh hheight
  obtain ⟨Cfg, hCfg, hCfgHeight, hCfgRoot⟩ :=
    NamedActionSources.action_source S rho a.val_index a.round hh target false hpair
  obtain ⟨Q', hQbody, hQerase, hQderive, -⟩ :=
    NamedActionSources.action_witness S rho a.val_index a.round Cfg hCfg
  have hQbodyPre : Q' ∈
      (rho.stateBeforeTime S (S.a a.round) a.val_index).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hQbody
  obtain ⟨N, hN, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted (S.a a.round)
  have hQrun : RunBlock S rho Q' := by
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S ha (i := N)
    simpa only [hN] using hQbodyPre
  have hCfgQ : Cfg = Q.erase := Option.some.inj (hCfg.symm.trans hsource)
  have hroots : Q'.root = Q.root := by
    rw [← Proofs.NamedWire.erase_root Q', ← Proofs.NamedWire.erase_root Q, hQerase, hCfgQ]
  have hQQ := adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
    Q' Q hQrun hrun Q' Q
    (Or.inl (Proofs.NamedAncestry.named_self Q'))
    (Or.inr (Proofs.NamedAncestry.named_self Q)) hroots
  have hderiveQ :
      (actionReadAt S rho a.val_index a.round).st.core.σ Q.erase =
        derive_named S.E S.cfg Q := by
    rw [← hCfgQ, hQderive, hQQ]
  have hTroot : (derive_named S.E S.cfg Q).T_h.root = target := by
    rw [← hderiveQ]
    simpa only [hCfgQ] using hCfgRoot
  have hTpre : Block.Preceq (derive_named S.E S.cfg Q).T_h Q.erase := by
    have h := NamedDerivationGeometry.chainOrder_derive_named S.E S.cfg Q
    simpa only [NamedDerivationGeometry.derive_named_latest] using
      h.target_preceq_latest
  obtain ⟨A, hAQ, hAerase⟩ := Proofs.NamedAncestry.erased_ancestor_lift Q hTpre
  have hArun : RunBlock S rho A :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hrun hAQ
  have hrootXA : X.root = A.root := by
    rw [← Proofs.NamedWire.erase_root X, ← Proofs.NamedWire.erase_root A, hAerase, hXroot,
      hTroot]
  have hXA : X = A :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective X A hXrun
      hArun X A (Or.inl (Proofs.NamedAncestry.named_self X))
      (Or.inr (Proofs.NamedAncestry.named_self A)) hrootXA
  rw [hXA]
  exact Block.preceq_trans (Proofs.NamedWire.erase_preceq hAQ)
    (Proofs.NamedWire.erase_preceq hpreceq)


/-- **The single named row cap from the same height-source history.** Rows
above the `q0` frontier get their height from the history's source, which is
below the endpoint; rows at or below it are under the threshold already. -/
theorem w4RowsLe_of_heightSourceHistory
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q q0 : Round} {D : NamedBlock V}
    (hheightHistory : CanonicalHeightSourceHistoryAt S rho q0 (q + 1) D)
    (hthreshold : honestHMaxAt S rho (S.a q0) <
      (derive_named S.E S.cfg D).h - 1) :
    ∀ {j : Nat} {a : NamedAttestation V} {time : Time},
      a.val_index ∈ rho.honest →
      rho.events[j]? = some (Event.tick a.val_index time) →
      Object.attest a ∈ NamedRun.emittedAt S rho j a.val_index time →
      j < strictEventIndex rho
        (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) →
      ∀ hh : Height, a.height_pair.erase.height? = some hh →
        hh ≤ (derive_named S.E S.cfg D).h := by
  intro j a time ha hevent hemit hj hh hrow
  by_cases habove : honestHMaxAt S rho (S.a q0) < hh
  · have hemits : rho.emits S a.val_index (Object.attest a) time :=
      ⟨j, hevent, hemit⟩
    obtain ⟨-, ht⟩ := Proofs.Optimistic.emits_attest_shape S hemits
    have htick : Event.tick a.val_index time ∈ rho.events :=
      List.mem_of_getElem? hevent
    have hhorRound : S.a a.round ≤ rho.horizon := by
      have hle := (adm.in_horizon _ htick).2
      rw [ht] at hle
      exact hle
    have hexact :=
      honest_emits_exact_actionAttestationAt S adm ha a.round hhorRound
    have haEq : a = actionAttestationAt S rho a.val_index a.round := by
      refine Proofs.Optimistic.emits_attest_unique S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hemits hexact ?_
      exact (actionAttestationAt_shape S rho a.val_index a.round).2.1.symm
    have hheight :
        (actionAttestationAt S rho a.val_index a.round).height_pair.erase.height? =
          some hh := by
      rw [← haEq]; exact hrow
    have hq0 : q0 < a.round := honestRow_after_frontier S adm ha habove hheight
    have hta : time < Protocol.support_cutoff S.E (S.hc.opening_slot q + 2) :=
      eventTime_lt_of_index_lt_strictEventIndex S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hevent hj
    have hlt : a.round < q + 1 :=
      Nat.lt_succ_of_le (w4_round_le_of_action_lt_supportCutoff S (ht ▸ hta))
    obtain ⟨Q, -, -, hpreceq, hQheight⟩ :=
      hheightHistory a.round (Nat.le_of_lt hq0) hlt a.val_index ha hh hheight
    rw [← hQheight]
    exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hpreceq
  · exact le_trans (Nat.le_of_not_lt habove)
      (le_trans (Nat.le_of_lt hthreshold) (Nat.sub_le _ 1))

#print axioms w4Targets_of_heightSourceHistory
#print axioms w4RowsLe_of_heightSourceHistory














/-- `hheadEq` at the endpoint's own slot, pin-free, from the corresponding branch's
general-slot head equality (`ProposalAdoptionNamedClosedRun`, b8248b5a). -/
theorem w4BoundaryHeadEq_at_carrier
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {q : Round}
    (hq : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ q)
    (hcarrier : ProposerCarrierAt S rho q)
    (hhor : Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤
      rho.horizon)
    {D : NamedBlock V}
    (hD : proposedBlockAt S rho (S.hc.opening_slot q + 1) = some D) :
    ∀ w ∈ rho.honest,
      voteDutyHead S rho w (S.hc.opening_slot q + 1) = D.erase := by
  have hround2 : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤
      S.hc.opening_slot q + 1 :=
    (Nat.mul_le_mul_right S.hc.R ((Nat.le_succ _).trans hq)).trans
      (Nat.le_succ _)
  have hvoteHor : Protocol.vote_time S.E (S.hc.opening_slot q + 1) ≤
      rho.horizon :=
    (vote_time_le_confirmation_time S.E (S.hc.opening_slot q + 1)).trans
      ((w4_confirmation_time_mono S.E
        (Nat.add_le_add_left (by decide : 1 ≤ 3) (S.hc.opening_slot q))).trans
        hhor)
  intro w hw
  exact honestProposal_voterHeadAt_eq_after_SG_healing_named_slot S adm hcom
    hbelow hrec hdelay hpost (s := S.hc.opening_slot q) hround2 hvoteHor
    hcarrier.2.1 hD w hw


#print axioms w4BoundaryHeadEq_at_carrier





/-- **The frontier threshold over the debt-form cap.** Three iterations of the
public height-progress field absorb the gate route's one unit, so the carrier
sits three progress windows past the window start and the cap is the shared
debt form rather than the debt-free one. -/
theorem w4Threshold_of_progress_of_debtCap
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q0 lag q : Round} {D : NamedBlock V}
    (hprogress : EventualHeightProgressFrom S rho q0 lag)
    (hwindow : q0 + 3 * lag ≤ q)
    (hhor : S.a q ≤ rho.horizon)
    (hcap : honestHMaxAt S rho (S.a q) ≤ (derive_named S.E S.cfg D).h + 1) :
    honestHMaxAt S rho (S.a q0) < (derive_named S.E S.cfg D).h - 1 := by
  have hhor3 : S.a (q0 + 3 * lag) ≤ rho.horizon :=
    (Assembly.a_mono S hwindow).trans hhor
  have h3 := eventualHeightProgress_iterate S hprogress (Nat.le_refl q0) 3 hhor3
  have hmono : honestHMaxAt S rho (S.a (q0 + 3 * lag)) ≤
      honestHMaxAt S rho (S.a q) :=
    honestHMaxAt_mono S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (Assembly.a_mono S hwindow)
  have hchain : honestHMaxAt S rho (S.a q0) + 3 ≤
      (derive_named S.E S.cfg D).h + 1 :=
    le_trans (le_trans h3 hmono) hcap
  have hfinal : honestHMaxAt S rho (S.a q0) + 2 ≤
      (derive_named S.E S.cfg D).h := by
    have hsucc : honestHMaxAt S rho (S.a q0) + 2 + 1 ≤
        (derive_named S.E S.cfg D).h + 1 := hchain
    exact Nat.le_of_succ_le_succ hsucc
  exact Nat.lt_sub_of_add_lt hfinal

#print axioms w4Threshold_of_progress_of_debtCap


/-- **The debt-form frontier cap at the carrier's action.** The gate history at
the endpoint comes from the named height-source history and a window-start cap;
the endpoint is held at the round's grade-2 domain read because every honest
head at its own slot is it; and that read is strictly after the carrier's
action, by one delivery delay. -/
theorem w4BoundaryFrontierCap_at_carrier
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hquorum : HonestQuorum S rho.honest)
    {q q0 : Round} {D : NamedBlock V}
    (hDrun : RunBlock S rho D)
    (hheadEq : ∀ w ∈ rho.honest,
      voteDutyHead S rho w (S.hc.opening_slot q + 1) = D.erase)
    (hhist : CanonicalHeightSourceHistoryAt S rho q0 (q + 1) D)
    (hcap0 : honestHMaxAt S rho (S.a q0) ≤
      (derive_named S.E S.cfg D).h) :
    honestHMaxAt S rho (S.a q) ≤ (derive_named S.E S.cfg D).h + 1 := by
  have hgates := pastHonestHeightGatesBelow_of_canonicalHeightHistory S adm
    hhist hcap0
  have hdelta : S.a q + S.E.Δ ≤
      DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) DecoupledConsensusModel.Protocol.Phase.g2 := by
    have h := action_add_delta_le_next_Γ_neg1 S q
    rwa [gammaNeg1_eq_domain_g2_succ S q] at h
  have hlt : S.a q <
      DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) DecoupledConsensusModel.Protocol.Phase.g2 :=
    lt_of_lt_of_le (Int.lt_add_of_pos_right _ S.E.Δ_pos) hdelta
  have hvoteLe : Protocol.vote_time S.E (S.hc.opening_slot q + 1) ≤
      DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) DecoupledConsensusModel.Protocol.Phase.g2 := by
    refine le_trans ?_ hdelta
    refine le_trans ?_ (Int.le_add_of_nonneg_right S.E.Δ_pos.le)
    rw [Setup.a, Protocol.a_eq_confirmation_time]
    have hv : Protocol.vote_time S.E (S.hc.opening_slot q + 1) =
        (4 * ((S.hc.opening_slot q + 1 : Slot) : Time) + 1) * S.E.Δ := by
      unfold Protocol.vote_time Env.t slotStart
      ring
    have hc : Protocol.confirmation_time S.E (S.hc.opening_slot q) =
        (4 * ((S.hc.opening_slot q : Slot) : Time) + 6) * S.E.Δ := by
      unfold Protocol.confirmation_time Env.t slotStart
      ring
    rw [hv, hc]
    refine Int.mul_le_mul_of_nonneg_right ?_ (le_of_lt S.E.Δ_pos)
    push_cast
    omega
  have hheads : ∀ v ∈ rho.honest,
      Block.Preceq D.erase (voteDutyHead S rho v (S.hc.opening_slot q + 1)) :=
    fun v hv => (hheadEq v hv) ▸ Block.preceq_self D.erase
  have hprocessed := w4Processed_of_below_honest_heads S adm hDrun hheads
    hvoteLe
  have hheld : ∀ v ∈ rho.honest,
      D ∈ (rho.stateBeforeTime S
        (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) DecoupledConsensusModel.Protocol.Phase.g2)
        v).st.bodies := by
    intro v hv
    have hbridge := congrArg (fun x => x.bodies)
      (storeBeforeTime_eq_stateBefore_strictEventIndex S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v
        (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) DecoupledConsensusModel.Protocol.Phase.g2))
    simp only [Run.storeBeforeTime] at hbridge
    rw [hbridge]
    exact hprocessed v hv
  exact w4HonestFrontierAt_le_succ_of_heightGates S adm hcom hquorum hgates
    hheld hlt

#print axioms w4BoundaryFrontierCap_at_carrier


/-- **The window-start cap, read at the carrier's second slot.** The same
post-gain argument that `w4_exists_postGain_carrier_height_of_base` runs at a
carrier's opening proposal, run instead at the proposal of its next slot: the
global frontier witness is taken at the same round read `S.a q` but for the
slot `opening_slot q + 1`, so the honest frontier at the window start stays
strictly below the endpoint's own height. This is the base case the height
gates need, and it is not the boundary's `hthreshold` read backwards: the
carrier round is given here, not chosen. -/
theorem w4_postGain_secondSlot_height_of_base
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {b q : Round}
    (hb : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ b)
    (hqStrict : b + 2 * progressLag' gap delayExtra < q)
    (hcarrier : ProposerCarrierAt S rho q)
    (hhor : Protocol.confirmation_time S.E (S.hc.opening_slot q + 1) ≤
      rho.horizon)
    {D : NamedBlock V}
    (hD : proposedBlockAt S rho (S.hc.opening_slot q + 1) = some D) :
    honestHMaxAt S rho (S.a b) < (Protocol.derive_named S.E S.cfg D).h := by
  classical
  obtain ⟨u, hu⟩ := honest_nonempty_of_honestCommittees hcom
  have hLpos : 1 ≤ progressLag' gap delayExtra := progressLag'_pos gap
  have h2L : 2 ≤ 2 * progressLag' gap delayExtra := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left 2 hLpos
  have hDtwoQ : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ q :=
    (Nat.add_le_add hb h2L).trans hqStrict.le
  have hDq : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ q :=
    (Nat.le_add_right _ 2).trans hDtwoQ
  -- horizon slices at the endpoint's own slot
  have hqHor : S.a q ≤ rho.horizon := by
    refine le_trans ?_ hhor
    simpa only [opening_confirmation_time_eq_action] using
      w4_confirmation_time_mono S.E (Nat.le_succ (S.hc.opening_slot q))
  have hvoteHor : Protocol.vote_time S.E (S.hc.opening_slot q + 1) ≤
      rho.horizon :=
    (vote_time_le_confirmation_time S.E (S.hc.opening_slot q + 1)).trans hhor
  have hvoteDelta : Protocol.vote_time S.E (S.hc.opening_slot q + 1) + S.E.Δ ≤
      rho.horizon := by
    rw [Proofs.Optimistic.vote_time_add_delta]
    exact (Protocol.support_cutoff_le_confirmation_time S.E
      (S.hc.opening_slot q + 1)).trans hhor
  -- the global frontier witness at the round read, for the endpoint's slot
  have hreadLo : S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) ≤
      S.a q := Assembly.a_mono S hDq
  have hopenLo : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra) + 1 ≤
      S.hc.opening_slot q + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul_right S.hc.R hDq) 1
  have hnext : S.a q ≤
      Protocol.confirmation_time S.E (S.hc.opening_slot q + 1) := by
    simpa only [opening_confirmation_time_eq_action] using
      w4_confirmation_time_mono S.E (Nat.le_succ (S.hc.opening_slot q))
  obtain ⟨T, hTrun, hTband, hTheads⟩ :=
    exists_namedCommonPreviousHeadAncestor_in_frontierBand_through_confirmation_after_GST
      S adm hcom hbelow hrec hdelay hpost hreadLo hqHor hopenLo hnext
        hvoteDelta hu
  -- every honest head at the endpoint's slot is the endpoint
  have hround2 : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤
      S.hc.opening_slot q + 1 :=
    (Nat.mul_le_mul_right S.hc.R hDtwoQ).trans (Nat.le_succ _)
  have hheads : ∀ w ∈ rho.honest,
      voterHeadAt S rho w (S.hc.opening_slot q + 1) = D.erase :=
    honestProposal_voterHeadAt_eq_after_SG_healing_named_slot S adm hcom hbelow
      hrec hdelay hpost (s := S.hc.opening_slot q) hround2 hvoteHor
      hcarrier.2.1 hD
  have hTD : Block.Preceq T.erase D.erase := by
    have h := hTheads u hu
    rwa [hheads u hu] at h
  have hproposalHor : Protocol.proposal_time S.E (S.hc.opening_slot q + 1) ≤
      rho.horizon :=
    (Protocol.proposal_time_lt_vote_time S.E _).le.trans hvoteHor
  have hDrun : RunBlock S rho D :=
    proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
      (S.hc.opening_slot q + 1) (Nat.succ_pos _) hcarrier.2.1 hproposalHor hD
  have hTDn : NamedBlock.Preceq T D :=
    namedPreceq_of_runBlock_erase_preceq adm hTrun hDrun hTD
  have hTheight : (Protocol.derive_named S.E S.cfg T).h ≤
      (Protocol.derive_named S.E S.cfg D).h :=
    Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hTDn
  -- two progress gains between the window start and the carrier's action
  have hr0Hor : S.a (b + 2 * progressLag' gap delayExtra) ≤ rho.horizon :=
    (Assembly.a_mono S hqStrict.le).trans hqHor
  have hprog := heightProgress_public S hdelay adm hcom hbelow hpost hrec
  have hstart : rGST + 1 ≤ b :=
    (Handover.gstRound_succ_le_deadline S rho rGST gap).trans hb
  have hgain : honestHMaxAt S rho (S.a b) + 2 ≤
      honestHMaxAt S rho (S.a (b + 2 * progressLag' gap delayExtra)) :=
    eventualHeightProgress_iterate S hprog
      ((Nat.le_succ rGST).trans hstart) 2 hr0Hor
  have hr0Post : S.E.t_GST ≤ S.a (b + 2 * progressLag' gap delayExtra) :=
    hpost.trans (Assembly.a_mono S
      ((Nat.le_succ rGST).trans (hstart.trans (Nat.le_add_right b _))))
  have hrelay : S.a (b + 2 * progressLag' gap delayExtra) + 1 + S.E.Δ ≤ S.a q :=
    Handover.action_succ_delta_le_action_of_lt S hqStrict
  have hlocal := Handover.honestHMaxAt_le_localFrontier_after_oneDelay S adm hcom
    (slashableBound_of_admissible_belowOneThird S adm hbelow)
      hr0Post hrelay hqHor u hu
  exact Handover.heightOld_assemble hgain hlocal hTband hTheight

#print axioms w4_postGain_secondSlot_height_of_base
















end HealingSurface
end Proofs
end DecoupledConsensusModel

end
