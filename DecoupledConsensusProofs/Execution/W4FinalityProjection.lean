module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.PostHealingProposalLifecycle
public import DecoupledConsensusProofs.Protocol.ChainState.RecurringFinality
public import DecoupledConsensusProofs.Execution.StoreFinalityRun
public import DecoupledConsensusProofs.Protocol.Schedule.W4ExecSuffix

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Protocol
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 0. Named-run geometry

Copied from the private core of `RecoverySelectedSourceRun.lean:140-176`
(that module's helpers are `private`, so they are restated here rather than
imported). -/

omit [Fintype V] in
private theorem named_preceq_trans {A B C : NamedBlock V}
    (hAB : NamedBlock.Preceq A B) (hBC : NamedBlock.Preceq B C) :
    NamedBlock.Preceq A C := by
  induction C with
  | genesis =>
      have hB : B = .genesis := by
        simpa [NamedBlock.Preceq, NamedBlock.preceq] using hBC
      simpa only [← hB] using hAB
  | node p s root votes support rows proposer ih =>
      have hcases : B = .node p s root votes support rows proposer ∨
          NamedBlock.Preceq B p := by
        simpa only [NamedBlock.Preceq, NamedBlock.preceq,
          Bool.or_eq_true, decide_eq_true_eq] using hBC
      rcases hcases with hEq | hParent
      · simpa only [← hEq] using hAB
      · change (decide (A = .node p s root votes support rows proposer) ||
          NamedBlock.preceq A p) = true
        simp only [Bool.or_eq_true]
        exact Or.inr (ih hParent)

private theorem runBlock_ancestor
    (S : Setup V) {rho : Run V} {A B : NamedBlock V}
    (hB : RunBlock S rho B) (hAB : NamedBlock.Preceq A B) :
    RunBlock S rho A := by
  rcases hB with ⟨D, hD, hDB⟩
  exact ⟨D, hD, named_preceq_trans hAB hDB⟩

/-- Root-collision freedom: two run blocks with the same erasure are equal. -/
private theorem runBlock_eq_of_erase_eq
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {A B : NamedBlock V} (hA : RunBlock S rho A) (hB : RunBlock S rho B)
    (he : A.erase = B.erase) : A = B :=
  adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective A B hA hB A B
    (Or.inl (Proofs.NamedAncestry.named_self A)) (Or.inr (Proofs.NamedAncestry.named_self B))
    (by rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root B, he])

/-- A named body retained at an honest read is a run block. -/
private theorem runBlock_of_bodies_stateAt
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {v : V} (hv : v ∈ rho.honest) (t : Time) {D : NamedBlock V}
    (hD : D ∈ (Run.stateAt S rho t v).st.bodies) : RunBlock S rho D := by
  obtain ⟨n, hn⟩ := Proofs.Bridges.stateAt_eq_stateBefore S sch t
  have hn' : Run.stateAt S rho t = Run.stateBefore S rho n := hn
  rw [hn'] at hD
  exact Proofs.Bridges.runBlock_of_stateBefore_mem S hv hD

/-- Named height is monotone along erased ancestry between run blocks. The
erased ancestor is lifted to a named one and identified with `A` by root
injectivity, so `Proofs.NamedEntryHeight.derive_height_mono` applies. -/
private theorem derive_named_h_mono_of_erased_preceq
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {A B : NamedBlock V} (hA : RunBlock S rho A) (hB : RunBlock S rho B)
    (hpre : Block.Preceq A.erase B.erase) :
    (derive_named S.E S.cfg A).h ≤ (derive_named S.E S.cfg B).h := by
  obtain ⟨C, hCB, hCe⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hpre
  have hAC : A = C := runBlock_eq_of_erase_eq S adm hA
    (runBlock_ancestor S hB hCB) hCe.symm
  rw [hAC]
  exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hCB

/-- Strict named height orients two compatible run blocks. Named twin of
`RecurringArithmeticCore.preceq_of_compatible_of_derived_h_lt`. -/
private theorem preceq_of_compatible_of_derive_named_h_lt
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {A B : NamedBlock V} (hA : RunBlock S rho A) (hB : RunBlock S rho B)
    (hcmp : Block.compatible A.erase B.erase = true)
    (hlt : (derive_named S.E S.cfg A).h < (derive_named S.E S.cfg B).h) :
    Block.Preceq A.erase B.erase := by
  simp only [Block.compatible, Bool.or_eq_true] at hcmp
  rcases hcmp with hAB | hBA
  · exact hAB
  · exact absurd hlt (Nat.not_lt_of_ge
      (derive_named_h_mono_of_erased_preceq S adm hB hA hBA))

/-! ## 1. The common finalized height is under the honest frontier

earlier `RecurringFinalityRun.lean:325-350`, with the conclusion weakened from
`<` to `≤` (see the module header). -/

/-- Every common finalized-height lower bound is at most the current honest
processed-height frontier. -/
theorem commonFinalizedHeight_le_honestHMaxAt
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbot : BelowOneThird S rho.honest)
    {r : Round} {h : Height}
    (hcommon : ∀ v ∈ rho.honest,
      h ≤ (rho.storeAt S v (S.a r)).core.finalized_height) :
    h ≤ honestHMaxAt S rho (S.a r) := by
  obtain ⟨v, -, hv⟩ := AlignedRoundLemmas.honest_member_of_quorum hbot
    (AlignedRoundLemmas.honestQuorum_of_belowOneThird hbot)
  have hlocal : (rho.storeAt S v (S.a r)).core.finalized_height ≤
      (rho.storeAt S v (S.a r)).h_max := by
    show (Run.stateAt S rho (S.a r) v).st.core.finalized_height ≤
      (Run.stateAt S rho (S.a r) v).st.core.h_max
    by_cases hF : (Run.stateAt S rho (S.a r) v).st.core.F = Block.genesis
    · simp only [Protocol.Store.finalized_height, if_pos hF]
      exact Nat.zero_le _
    · obtain ⟨D, hD, hDe⟩ := Proofs.NamedStoreBridge.exists_named_of_mem_stateAt
        S rho (S.a r) v (Proofs.NamedStoreBridge.finalizedInTree_stateAt S rho (S.a r) v)
      have hview := Proofs.NamedStoreBridge.derivedView_stateAt S rho (S.a r) v D hD
      have hheights := Proofs.NamedStoreBridge.heights_le_hMax_stateAt S rho (S.a r) v D hD
      rw [Protocol.Store.finalized_height, if_neg hF, ← hDe, hview]
      exact hheights
  exact (hcommon v hv).trans
    (hlocal.trans (localHMax_le_honestHMaxAt S rho (S.a r) hv))

#print axioms commonFinalizedHeight_le_honestHMaxAt

/-! ## 2. Whole-run safety orients an old prefix below a higher new one

earlier `RecurringFinalityRun.lean:393-413`, with both blocks carried as named
run blocks and both heights read through `derive_named`. -/

/-- Whole-run store safety orients an old common finalized prefix below a
strictly higher new common finalized prefix. -/
theorem preceq_of_commonFinalityAdvance
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsafe : WholeRunFinalitySafety S rho)
    {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest)
    {t t' : Time} (ht : t ≤ rho.horizon) (ht' : t' ≤ rho.horizon)
    {D P : NamedBlock V} {h : Height}
    (hDrun : RunBlock S rho D) (hPrun : RunBlock S rho P)
    (hD : Block.Preceq D.erase (rho.storeAt S u t).F)
    (hP : Block.Preceq P.erase (rho.storeAt S v t').F)
    (hDheight : (derive_named S.E S.cfg D).h ≤ h)
    (hadvance : h < (derive_named S.E S.cfg P).h) :
    Block.Preceq D.erase P.erase := by
  have hstores := hsafe.2 u hu v hv t t'
  have hcompat : Block.compatible D.erase P.erase = true := by
    simp only [Block.compatible, Bool.or_eq_true] at hstores
    rcases hstores with hforward | hbackward
    · exact Block.compatible_of_preceq_common
        (Block.preceq_trans hD hforward) hP
    · exact Block.compatible_of_preceq_common
        hD (Block.preceq_trans hP hbackward)
  exact preceq_of_compatible_of_derive_named_h_lt S adm hDrun hPrun hcompat
    (hDheight.trans_lt hadvance)

#print axioms preceq_of_commonFinalityAdvance

/-! ## 3. The recurring-finality projection

earlier `CommonFinalityFrontierRun.lean:33`, closing `W4RecurringProjectionPin`
(`W4D3FinalitySpineComposeRun.lean:132`). -/

/-- A bounded advance above the current honest frontier supplies recurring
finality. No selected phase record or non-lostness premise is needed here. -/
theorem recurringFinalityCarrierFrom_of_commonFinalityAboveFrontier
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbot : BelowOneThird S rho.honest) {q lag : Round}
    {deadline : Round}
    (hlag : lag ≤ deadline)
    (hproduce : ∀ start : Round, q ≤ start → S.a (start + lag) ≤ rho.horizon →
      ∃ H : Height, honestHMaxAt S rho (S.a start) < H ∧
        AlreadyCommonFinalizedAtOrAbove S rho q start (start + lag) H) :
    RecurringFinalityCarrierFrom S rho q (healingBoundaryTime S q) deadline := by
  intro r B h hqr hcommon hhor
  have htime : S.a (r + lag) ≤ S.a (r + deadline) :=
    Assembly.a_mono S (Nat.add_le_add_left hlag r)
  obtain ⟨H, hfrontier, slot, Pblk, checkpoint, height, hspos, hafter, hproposer,
    hPblk, hrun, hfin, hHle, hheight, hne, hsource, hsourceConf, hconfEnd,
    hstores⟩ := hproduce r hqr (htime.trans hhor)
  have hhorR : S.a r ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_add_right r lag)).trans (htime.trans hhor)
  have hconfHor : Protocol.confirmation_time S.E slot ≤ rho.horizon :=
    hconfEnd.trans (htime.trans hhor)
  have hfrontierAdvance : honestHMaxAt S rho (S.a r) < height :=
    hfrontier.trans_le hHle
  obtain ⟨w, hw, D, hD, hDe, hDh⟩ :=
    commonFinalizedBlock_height_le_honestHMaxAt S adm hbot
      (fun v hv => (hcommon v hv).1)
  have hsch : ScheduleWellFormed S rho :=
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
  have hDrun : RunBlock S rho D := runBlock_of_bodies_stateAt S hsch hw (S.a r) hD
  have hsafe := wholeRunFinalitySafety_of_belowOneThird S adm.toNamedAdmissibleCore hbot
  have hadvance : h < height :=
    (commonFinalizedHeight_le_honestHMaxAt S adm hbot
      (fun v hv => (hcommon v hv).2)).trans_lt hfrontierAdvance
  have hBP : Block.Preceq B checkpoint.erase := by
    rw [← hDe]
    refine preceq_of_commonFinalityAdvance S adm hsafe hw hw hhorR hconfHor
      (h := honestHMaxAt S rho (S.a r)) hDrun hrun ?_ (hstores w hw).1 hDh ?_
    · rw [hDe]
      exact (hcommon w hw).1
    · rw [hheight]
      exact hfrontierAdvance
  exact ⟨slot, Pblk, checkpoint, height, hspos, hafter, hproposer, hconfHor,
    hPblk, hfin, hrun, hBP, hadvance, hheight, hsource, hsourceConf,
    hconfEnd.trans htime, hstores⟩

#print axioms recurringFinalityCarrierFrom_of_commonFinalityAboveFrontier

/-! ## 4. The honest-proposal lifecycle, live-confirmation half

earlier `Availability/PostHealingProposalLifecycleRun.lean:216-238` produces the
whole `Internal.HonestProposalLifecycleFrom`, whose second conjunct
(`latest_confirmed = B.erase`) is
`UserConfirmationFreshness.latest_eq_proposedBlock_of_duty` and needs
`Internal.HonestHeadExtendsStableFrom`. That premise has no producer under this
pin's hypotheses (`Admissible`, `HonestCommittees`, `CanonicalSuffixExecution`),
and the projection below never reads the `latest_confirmed` conjunct: it uses
only the emission and the live confirmation. So the live half is produced on
its own and no head-extension premise enters the surface. -/

/-- Every strictly post-boundary honest proposal is emitted by its proposer and
is the exact protocol live confirmation at every honest confirmation duty. -/
theorem proposedBlock_emitted_and_liveConfirmed_of_canonicalSuffixExecution
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {q : Round}
    (hdutyAt : ∀ s : Slot, 0 < s →
      healingBoundaryTime S q < Protocol.proposal_time S.E s →
      S.E.proposer s ∈ rho.honest →
      Protocol.confirmation_time S.E s ≤ rho.horizon →
      ∀ B : NamedBlock V, proposedBlockAt S rho s = some B →
        Protocol.CanonicalProposalDutyAt S rho s B)
    {s : Slot} (hs : 0 < s)
    (hafter : healingBoundaryTime S q < Protocol.proposal_time S.E s)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B) :
    rho.emits S (S.E.proposer s) (Object.block B) (Protocol.proposal_time S.E s) ∧
      ∀ v ∈ rho.honest,
        (rho.storeAt S v
          (Protocol.confirmation_time S.E s)).live_confirmed = B.erase := by
  have hduty := hdutyAt s hs hafter hprop hhor B hB
  refine ⟨Protocol.proposedBlock_emitted_of_admissible S adm hs hprop
      ((Protocol.proposal_time_le_confirmation_time S.E s).trans hhor) hB,
    fun v hv => ?_⟩
  exact Protocol.storeAt_liveConfirmed_eq_proposedBlock_of_dutyExecution
    S adm hcom hhor hduty hv

#print axioms proposedBlock_emitted_and_liveConfirmed_of_canonicalSuffixExecution

/-! ## 5. The honest-proposal finality projection

earlier `HonestProposalFinalityRun.lean:144`, closing `W4ProposalProjectionPin`
(`W4D3FinalitySpineComposeRun.lean:143`). The five arithmetic helpers below are
the `private` helpers of the selection's own `HonestProposalFinalityRun.lean:28,
57, 67, 83, 92`, restated because they are not exported. -/

/-- A proposal strictly after the boundary belongs to a round no earlier than
the healing round. -/
private theorem postBoundaryProposal_roundStart
    (S : Setup V) {q : Round} {s : Slot}
    (hafter : healingBoundaryTime S q <
      Protocol.proposal_time S.E s) :
    q ≤ S.hc.round_of s + 1 := by
  have hboundary : Protocol.vote_time S.E
      (S.hc.opening_slot q + 2) <
        Protocol.proposal_time S.E s := by
    simpa only [healingBoundaryTime] using hafter
  have hopen : S.hc.opening_slot q ≤ s := by
    by_contra hnot
    have hslt : s < S.hc.opening_slot q := Nat.lt_of_not_ge hnot
    have hslots : s ≤ S.hc.opening_slot q + 2 :=
      hslt.le.trans (Nat.le_add_right _ 2)
    have hreverse : Protocol.proposal_time S.E s <
        Protocol.vote_time S.E (S.hc.opening_slot q + 2) :=
      (Protocol.proposal_time_mono S.E hslots).trans_lt (by
        unfold Protocol.proposal_time Protocol.vote_time
        exact Int.lt_add_of_pos_right _ S.E.Δ_pos)
    exact (not_lt_of_ge hboundary.le) hreverse
  have hRpos : 0 < S.hc.R :=
    lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two
  have hqround : q ≤ S.hc.round_of s := by
    unfold Protocol.HealConfig.round_of
    unfold Protocol.HealConfig.opening_slot at hopen
    exact (Nat.le_div_iff_mul_le hRpos).mpr hopen
  exact hqround.trans (Nat.le_add_right _ 1)

/-- Confirmation times are monotone in their duty slots. -/
private theorem confirmation_time_mono_slots_projection
    (E : Env V) {s u : Slot} (hsu : s ≤ u) :
    Protocol.confirmation_time E s ≤
      Protocol.confirmation_time E u := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ,
    Protocol.confirmation_time_eq_support_cutoff_succ]
  exact Proofs.Optimistic.support_cutoff_mono E
    (Nat.add_le_add_right hsu 1)

/-- Every slot is before the opening slot of its following round. -/
private theorem slot_lt_nextRoundOpening_projection
    (hc : Protocol.HealConfig) (s : Slot) :
    s < hc.opening_slot (hc.round_of s + 1) := by
  have hRpos : 0 < hc.R :=
    lt_of_lt_of_le Nat.zero_lt_two hc.R_ge_two
  have hmod : s % hc.R < hc.R := Nat.mod_lt s hRpos
  unfold Protocol.HealConfig.round_of
    Protocol.HealConfig.opening_slot
  calc
    s = s % hc.R + hc.R * (s / hc.R) :=
      (Nat.mod_add_div s hc.R).symm
    _ < hc.R + hc.R * (s / hc.R) :=
      Nat.add_lt_add_right hmod _
    _ = (s / hc.R + 1) * hc.R := by ring

/-- A proposal is confirmed no later than the following round action. -/
private theorem confirmation_time_le_nextRoundAction_projection
    (S : Setup V) (s : Slot) :
    Protocol.confirmation_time S.E s ≤
      S.a (S.hc.round_of s + 1) := by
  simpa only [Setup.a, Protocol.a_eq_confirmation_time] using
    confirmation_time_mono_slots_projection S.E
      (slot_lt_nextRoundOpening_projection S.hc s).le

/-- Round action times are monotone without an Assembly-level dependency. -/
private theorem action_time_mono_projection
    (S : Setup V) {r u : Round} (hru : r ≤ u) :
    S.a r ≤ S.a u := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hru
  rw [Proofs.HealingLemmas.a_add_rounds]
  exact Int.le_add_of_nonneg_right (Proofs.HealingLemmas.bound_nonneg S k)

/-- A run block processed at an honest read is no higher than the public honest
frontier there, its height read through the named derivation. -/
private theorem derive_named_h_le_honestHMaxAt_of_mem_T
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) (t : Time) {A : NamedBlock V}
    (hA : RunBlock S rho A) (hmem : A.erase ∈ (rho.storeAt S v t).core.T) :
    (derive_named S.E S.cfg A).h ≤ honestHMaxAt S rho t := by
  obtain ⟨D, hD, hDe⟩ := Proofs.NamedStoreBridge.exists_named_of_mem_stateAt S rho t v hmem
  have hDrun : RunBlock S rho D := runBlock_of_bodies_stateAt S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv t hD
  have hAD : A = D := runBlock_eq_of_erase_eq S adm hA hDrun hDe.symm
  rw [hAD]
  exact (Proofs.NamedStoreBridge.heights_le_hMax_stateAt S rho t v D hD).trans
    (localHMax_le_honestHMaxAt S rho t hv)

/-- Common finality above the current frontier finalizes every earlier
post-boundary honest proposal. Source time and canonical ordering place the
proposal below the new finalized checkpoint. -/
theorem honestProposalFinalityFrom_of_commonFinalityAboveFrontier
    (S : Setup V) {deadline : Round}
    {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {q : Round}
    (hsuffix : CanonicalSuffixFrom S rho (healingBoundaryTime S q))
    (hdutyAt : ∀ s : Slot, 0 < s →
      healingBoundaryTime S q < Protocol.proposal_time S.E s →
      S.E.proposer s ∈ rho.honest →
      Protocol.confirmation_time S.E s ≤ rho.horizon →
      ∀ B : NamedBlock V, proposedBlockAt S rho s = some B →
        Protocol.CanonicalProposalDutyAt S rho s B)
    (hproduce : ∀ start : Round, q ≤ start →
      S.a (start + deadline) ≤ rho.horizon →
      ∃ H : Height, honestHMaxAt S rho (S.a start) < H ∧
        AlreadyCommonFinalizedAtOrAbove S rho q start (start + deadline) H) :
    HonestProposalFinalityFrom S rho q deadline := by
  intro s hs hafter hproposer
  obtain ⟨B, hB⟩ := proposedBlockAt_isSome S rho s
  refine ⟨B, hB, ?_⟩
  dsimp only
  intro hhor
  have hroundStart : q ≤ S.hc.round_of s + 1 :=
    postBoundaryProposal_roundStart S hafter
  have hconfirmationStart :
      Protocol.confirmation_time S.E s ≤ S.a (S.hc.round_of s + 1) :=
    confirmation_time_le_nextRoundAction_projection S s
  have hphaseHorizon :
      S.a (S.hc.round_of s + 1 + deadline) ≤ rho.horizon := hhor
  have hconfirmationHorizon :
      Protocol.confirmation_time S.E s ≤ rho.horizon :=
    hconfirmationStart.trans ((action_time_mono_projection S
      (Nat.le_add_right (S.hc.round_of s + 1) deadline)).trans hphaseHorizon)
  obtain ⟨hemit, hlive⟩ :=
    proposedBlock_emitted_and_liveConfirmed_of_canonicalSuffixExecution
      S adm hcom hdutyAt hs hafter hproposer hconfirmationHorizon hB
  have hBrun : RunBlock S rho B :=
    Protocol.proposedBlock_runBlock S adm hs hproposer
      ((Protocol.proposal_time_le_confirmation_time S.E s).trans
        hconfirmationHorizon) hB
  have hBmemConfirmation : B.erase ∈
      (rho.storeAt S (S.E.proposer s)
        (Protocol.confirmation_time S.E s)).core.T := by
    rw [← hlive (S.E.proposer s) hproposer]
    exact Proofs.NamedStoreBridge.liveConfirmed_mem_stateAt S rho
      (Protocol.confirmation_time S.E s) (S.E.proposer s)
  have hBmemAction : B.erase ∈
      (rho.storeAt S (S.E.proposer s)
        (S.a (S.hc.round_of s + 1))).core.T :=
    StoreFinality.stateAt_T_subset S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (S.E.proposer s) hconfirmationStart hBmemConfirmation
  have hBfrontier : (derive_named S.E S.cfg B).h ≤
      honestHMaxAt S rho (S.a (S.hc.round_of s + 1)) :=
    derive_named_h_le_honestHMaxAt_of_mem_T S adm hproposer _ hBrun hBmemAction
  obtain ⟨H, hfrontier, u, Pu, checkpoint, height, hupos, hafterU, hproposerU,
    hPu, hrunU, hfinU, hHle, hheightU, hneU, hsourceU, hsourceConfU, hconfEndU,
    hstoresU⟩ := hproduce (S.hc.round_of s + 1) hroundStart hphaseHorizon
  have hfrontierAdvance : honestHMaxAt S rho (S.a (S.hc.round_of s + 1)) < height :=
    hfrontier.trans_le hHle
  have hconfirmationU : Protocol.confirmation_time S.E u ≤ rho.horizon :=
    hconfEndU.trans hphaseHorizon
  obtain ⟨hemitU, -⟩ :=
    proposedBlock_emitted_and_liveConfirmed_of_canonicalSuffixExecution
      S adm hcom hdutyAt hupos hafterU hproposerU hconfirmationU hPu
  have hproposalOrder : Protocol.proposal_time S.E s ≤
      Protocol.proposal_time S.E u :=
    (Protocol.proposal_time_le_confirmation_time S.E s).trans
      (hconfirmationStart.trans hsourceU)
  have hBcarrier : Block.Preceq B.erase Pu.erase :=
    proposedBlock_preceq_of_canonicalSuffixFrom
      S adm hsuffix hs hupos hafter hproposer hproposerU hB hPu hemit hemitU
      hproposalOrder
  have hPcarrier : Block.Preceq checkpoint.erase Pu.erase := by
    rw [← hfinU.1]
    exact (Proofs.NamedStoreRoots.derive_named_anchors_preceq S.E S.cfg Pu).1
  have hcompatible : Block.compatible B.erase checkpoint.erase = true :=
    Block.compatible_of_preceq_common hBcarrier hPcarrier
  have hstrict : (derive_named S.E S.cfg B).h <
      (derive_named S.E S.cfg checkpoint).h := by
    rw [hheightU]
    exact hBfrontier.trans_lt hfrontierAdvance
  have hBP : Block.Preceq B.erase checkpoint.erase :=
    preceq_of_compatible_of_derive_named_h_lt S adm hBrun hrunU hcompatible hstrict
  refine ⟨Protocol.confirmation_time S.E u, hconfirmationStart.trans hsourceConfU,
    ?_, ?_⟩
  · exact hconfEndU
  · intro v hv
    exact Block.preceq_trans hBP (hstoresU v hv).1

#print axioms honestProposalFinalityFrom_of_commonFinalityAboveFrontier

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
