module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.W4StableGrowthGSTZero
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.W4StableRecordGrowthFrom
public import DecoupledConsensusProofs.Execution.WeakConfirmationReadBandNamed
public import DecoupledConsensusProofs.Objects.WeakFGRoot
public import DecoupledConsensusProofs.Protocol.Grades.WeakConfirmationReadAnchorsNamed
public import DecoupledConsensusProofs.Protocol.Grades.WeakBootstrapAction
public import DecoupledConsensusProofs.Protocol.ChainState.GSTZeroSixFieldBypassNamed
public import DecoupledConsensusProofs.Execution.WeakConfirmationReadRootsCore
public import DecoupledConsensusProofs.Protocol.Grades.W4A2GSTZeroLiveConfirmation
public import DecoupledConsensusProofs.Protocol.Schedule.GSTZeroReorgResilienceCoreNamed
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryCapturedNextActionExact
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionConfirmationCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Execution.W4CoverGradeInduction

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel
namespace Proofs

open Internal Execution Statements
open Proofs.HealingSurface
open Internal.NamedRecoveryRead Internal.PhaseGrades DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The live confirmation at the action read -/

/-- The action read and the round's own confirmation-time store record the same
live confirmation: the action read IS the opening confirmation write, and the
attestation that follows it in the same tick does not touch the record. -/
theorem w4_actionStore_liveConfirmed_eq_storeAt
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {v : V} (hv : v ∈ rho.honest) (r : Round)
    (hhor : S.a r ≤ rho.horizon) :
    (actionStoreAt S rho v r).st.core.live_confirmed =
      (rho.storeAt S v (S.a r)).live_confirmed := by
  have hct : Protocol.confirmation_time S.E (S.hc.opening_slot r) = S.a r :=
    Proofs.HealingSurface.opening_confirmation_time_eq_action S r
  have hread : confirmationInputRead S rho v (S.hc.opening_slot r) =
      NamedActionReads.confirmationReadAt S rho v (S.a r) := by
    show NamedActionReads.confirmationReadAt S rho v
        (Protocol.confirmation_time S.E (S.hc.opening_slot r)) = _
    rw [hct]
  have h1 := Proofs.Optimistic.live_confirmed_eq_update S sch hv (S.hc.opening_slot r)
    (by rw [hct]; exact hhor)
  rw [hct, hread] at h1
  rw [h1, Proofs.HealingSurface.actionStoreAt_eq_update_confirmation_openingConfStore
    S rho v r]
  rfl

#print axioms w4_actionStore_liveConfirmed_eq_storeAt

private theorem w4_prepared_deepest_clear_eq_tip
    {floor : Option (Block V)} {C : Block V} {test : Block V → Bool}
    (hfloor : floor.elim True (fun a => Block.preceq a C = true))
    (htest : test C = true) :
    Protocol.deepest_clear floor C test = some C := by
  have hmem : C ∈ Protocol.chain_of C := by
    cases C with
    | genesis => simp [Protocol.chain_of, Protocol.chain_up, Block.depth]
    | node p s root gv gsv ats i =>
        simp [Protocol.chain_of, Protocol.chain_up, Block.depth, Block.parent?]
  have hsome : (Protocol.deepest_clear floor C test).isSome = true :=
    deepest_clear_isSome_of_mem hfloor hmem htest
  obtain ⟨L, hL⟩ := Option.isSome_iff_exists.mp hsome
  have hCmem : C ∈ (Protocol.chain_of C).toFinset.filter (fun B =>
      floor.elim true (fun anchor => Block.preceq anchor B) = true ∧
        test B = true) := by
    refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hmem, ?_, htest⟩
    cases floor with
    | none => rfl
    | some a => simpa using hfloor
  have hLC : Block.Preceq L C := Proofs.Engine.deepest_clear_preceq hL
  have hCL : Block.Preceq C L := by
    refine Proofs.HealingLemmas.deepest?_dominates hL hCmem ?_
    exact Block.compatible_of_preceq_common (Block.preceq_self C) hLC
  have hEq : L = C := Block.preceq_antisymm hLC hCL
  simpa [hEq] using hL




set_option maxHeartbeats 400000 in

/-- `RecoveryCapturedNextActionExactRun.actionSGBlockAt_eq_liveConfirmed_of_batchAligned`
without its batch-alignment hypothesis, which that proof binds as `_hbatch` and
never uses. Dropping it removes the only reason to proof the
full-participation batch-alignment helper to GST zero. The body below is that
proof verbatim, minus the dead binding. -/
theorem w4_actionSGBlockAt_eq_liveConfirmed
    (S : Setup V) {rho : Run V} {v : V} {r : Round}
    {Can D A : Block V}
    (hconfirmed : (actionStoreAt S rho v r).st.core.live_confirmed = D)
    (hCanD : Block.Preceq Can D)
    (hanchor : nodeAnchor S (actionReadAt S rho v r) r = A)
    (hACan : Block.Preceq A Can)
    (hclear : nodeClear S (actionReadAt S rho v r) r D = true) :
    actionSGBlockAt S rho v r = D := by
  let ast := actionStoreAt S rho v r
  have hconfirmed' : ast.st.core.live_confirmed = D := by
    simpa only [ast] using hconfirmed
  have hanchor' : nodeAnchor S ast r = A := by
    simpa only [ast, actionStoreAt] using hanchor
  have hclear' : nodeClear S ast r D = true := by
    simpa only [ast, actionStoreAt] using hclear
  have hanchorLive : Block.Preceq (nodeAnchor S ast r)
      ast.st.core.live_confirmed := by
    rw [hanchor', hconfirmed']
    exact Block.preceq_trans hACan hCanD
  have hclearLive : nodeClear S ast r ast.st.core.live_confirmed = true := by
    rw [hconfirmed']
    exact hclear'
  have hwalk : Protocol.deepest_clear (some (nodeAnchor S ast r))
      ast.st.core.toHealing.live_confirmed
      (nodeClear S ast r) = some ast.st.core.live_confirmed :=
    w4_prepared_deepest_clear_eq_tip (by simpa using hanchorLive) hclearLive
  have hround : S.hc.round_of ast.st.core.toHealing.s = r := by
    simpa only [ast, Protocol.Store.toHealing] using actionStoreAt_round S rho v r
  change Protocol.get_sg_vote_with (NamedProfile.gradeContract ast.cache)
      S.E S.hc ast.st.core.toHealing (S.hc.round_of ast.st.core.toHealing.s)
      (Protocol.grade2_block_with (NamedProfile.gradeContract ast.cache)
        S.E S.hc ast.st.core.toHealing
        (S.hc.round_of ast.st.core.toHealing.s)) = D
  rw [hround]
  unfold Protocol.get_sg_vote_with NamedProfile.gradeContract
    DecoupledConsensusModel.Protocol.frameContract
  change Protocol.currentSGVote ast.st.core.toHealing
      { nodeRead S ast r with Q2 := nodeQ2 S ast r } = D
  letI := (nodeRead S ast r).rawG2_decidable
  unfold Protocol.currentSGVote
  change (match Protocol.deepest_clear (some (nodeAnchor S ast r))
      ast.st.core.toHealing.live_confirmed (nodeClear S ast r) with
    | some B => B
    | none =>
      match nodeQ2 S ast r with
      | some B => B
      | none =>
        if (nodeRead S ast r).rawG2 then
          Protocol.get_fg_root ast.st.core.toHealing.toFG
        else nodeAnchor S ast r) = D
  rw [hwalk, hconfirmed']

#print axioms w4_actionSGBlockAt_eq_liveConfirmed

/-! ## The clearance step under weak participation -/




/-! ## The GST-zero opening carriers -/



private theorem w4_openingSlot_pos (S : Setup V) {q : Round} (hq : 0 < q) :
    0 < S.hc.opening_slot q := by
  simpa only [Protocol.HealConfig.opening_slot] using
    Nat.mul_pos hq (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)



/-! ## The SG-vote equality at a GST-zero honest opening -/




/-! ## The proposal at the next round's G2 domain read -/





/-! ## The residual, reduced to the duty read -/







/-! ## The duty-read arm, reduced to one held band head -/






/-! ## The head is held at the duty read -/

/-- `SeedBaseConeRun.voteDutyHead_mem_voteDutyStore` without its `Admissible`
hypothesis, which that proof never uses (the same dead-hypothesis pattern as
`_hbatch`). The body is that proof verbatim. -/
theorem w4_voteDutyHead_mem_voteDutyStore
    (S : Setup V) (rho : Run V) (v : V) (s : Slot) :
    Protocol.voteDutyHead S rho v s ∈
      (Proofs.Optimistic.voteDutyStore S rho v s).T := by
  let read := Internal.NamedRecoveryRead.voteDutyRead S rho v s
  let st := read.st.core
  have hinvPre : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (rho.stateBeforeTime S (Protocol.vote_time S.E s) v).st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
      (Protocol.vote_time S.E s) v).1
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg read.st := by
    simpa only [read, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt] using
      Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ _ hinvPre
  have hroot : Protocol.get_fg_root st.toHealing.toFG ∈ st.T :=
    Proofs.NamedStoreRoots.fg_root_mem read.st hinv.1.2
  have hanchor : voterAnchorAt S rho v s ∈ st.T :=
    Proofs.NamedConfirmationMembership.runtime_anchor_mem read.cache
      S.E S.hc st.toHealing (S.hc.round_of st.s) hroot
  have htree : voterCandidateTreeAt S rho v s ⊆ st.T := by
    intro D hD
    have hprocessed := Proofs.Records.get_filtered_block_tree_from_subset
      st.toHealing.toFG
      (Protocol.voter_processed_block_tree S.E st.toHealing.toFG.toSG.toGoldfishStore st.s) hD
    exact (Finset.mem_filter.mp hprocessed).1
  have hHmem : voterHeadAt S rho v s ∈ st.T := by
    rw [show voterHeadAt S rho v s = Protocol.ghost (voterAnchorAt S rho v s)
        (voterCandidateTreeAt S rho v s)
        (Protocol.goldfish_score S.E st.T
          (Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (st.s - 1))
        (Protocol.goldfish_eligible S.E st.σ st.h_max st.T st.s
          (Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (st.s - 1)) from rfl]
    exact Proofs.Records.ghost_mem_of _ _ hanchor htree
  have hHpre : voterHeadAt S rho v s ∈
      (rho.stateBeforeTime S (Protocol.vote_time S.E s) v).st.core.T := by
    simpa only [read, st, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hHmem
  simpa only [Protocol.voteDutyHead, Proofs.Optimistic.voteDutyStore,
    Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hHpre

#print axioms w4_voteDutyHead_mem_voteDutyStore





/-- The duty head witness under `WeakGenesis`: the reader's vote head
of the slot below the round-`(q+1)` opening is a named body it still holds at
that round's confirmation duty. The vote instant of slot `o - 1` is three Δ
before the duty's support cutoff, and the tree only grows; the named body and
its run membership come from the store bridge. No participation premise. -/
theorem w4_dutyHeadWitness
    (S : Setup V) {rho : Run V} (core : AdmissibleCore S rho)
    {r : Round} (hr : 0 < r) {v : V} (hv : v ∈ rho.honest) :
    ∃ X : NamedBlock V,
      X ∈ (NamedRun.stateBeforeTime S rho
        (w4StableDutyTime S r) v).st.bodies ∧
      X.erase = voterHeadAt S rho v (S.hc.opening_slot r - 1) ∧
      RunBlock S rho X := by
  set d : Slot := S.hc.opening_slot r - 1 with hd
  set t : Time := w4StableDutyTime S r with ht
  have hopos : 0 < S.hc.opening_slot r := w4_openingSlot_pos S hr
  have hdlt : d < S.hc.opening_slot r := Nat.sub_lt hopos (by decide)
  have hvoteLe : Protocol.vote_time S.E d ≤ t := by
    have hstep : Protocol.vote_time S.E d ≤
        Protocol.vote_time S.E (S.hc.opening_slot r) :=
      Protocol.vote_time_mono_slots S.E (Nat.le_of_lt hdlt)
    refine hstep.trans ?_
    rw [ht, w4StableDutyTime, ← Proofs.Optimistic.vote_time_add_delta]
    exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
  have hHvote : voterHeadAt S rho v d ∈
      (rho.storeBeforeTime S v (Protocol.vote_time S.E d)).T := by
    simpa only [Protocol.voteDutyHead, Proofs.Optimistic.voteDutyStore,
      Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using
      w4_voteDutyHead_mem_voteDutyStore S rho v d
  have hHmem : voterHeadAt S rho v d ∈
      (NamedRun.stateBeforeTime S rho t v).st.core.T := by
    change voterHeadAt S rho v d ∈ (rho.storeBeforeTime S v t).T
    rw [Proofs.HealingSurface.storeBeforeTime_eq_stateBefore_strictEventIndex
      S core.toNamedScheduleWellFormed] at hHvote
    rw [Proofs.HealingSurface.storeBeforeTime_eq_stateBefore_strictEventIndex
      S core.toNamedScheduleWellFormed]
    exact stateBefore_T_subset S rho v _
      (Proofs.HealingSurface.strictEventIndex_mono rho hvoteLe) hHvote
  obtain ⟨X, hXbody, hXerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho t v hHmem
  refine ⟨X, hXbody, hXerase, ?_⟩
  obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
    S rho core.toNamedScheduleWellFormed.sorted t
  apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i := i)
  exact (congrArg (fun w => X ∈ (w v).st.bodies) hi).mp hXbody

#print axioms w4_dutyHeadWitness



/-- The proposal is at or below that same head: the GST-zero vote-call family
at the slot below the next opening, which is still after the proposal's own
slot because `R ≥ 2`. -/
theorem w4_proposal_preceq_dutyHead
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {q r : Round} (hq : 0 < q) (hqr : q < r)
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot q) = some P)
    (hhor : S.a r ≤ rho.horizon) :
    ∀ v ∈ rho.honest,
      Block.Preceq P.erase
        (voterHeadAt S rho v (S.hc.opening_slot r - 1)) := by
  intro v hv
  have hslotPos : 0 < S.hc.opening_slot q := w4_openingSlot_pos S hq
  have hqhor : S.a q ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_of_lt hqr)).trans hhor
  have hsourceHor :
      Protocol.confirmation_time S.E (S.hc.opening_slot q) ≤ rho.horizon := by
    rw [Proofs.HealingSurface.opening_confirmation_time_eq_action S q]
    exact hqhor
  have hstepSucc : S.hc.opening_slot q + 1 ≤ S.hc.opening_slot (q + 1) := by
    simp only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add_left
      (le_trans (by decide : 1 ≤ 2) S.hc.R_ge_two) (q * S.hc.R)
  have hstep : S.hc.opening_slot q + 1 ≤ S.hc.opening_slot r :=
    hstepSucc.trans (Nat.mul_le_mul_right S.hc.R (Nat.succ_le_of_lt hqr))
  have hsk : S.hc.opening_slot q ≤ S.hc.opening_slot r - 1 :=
    Nat.le_sub_of_add_le hstep
  have hvoteHor : Protocol.vote_time S.E
      (S.hc.opening_slot r - 1) ≤ rho.horizon := by
    refine (Protocol.vote_time_mono_slots S.E
      (Nat.sub_le (S.hc.opening_slot r) 1)).trans ?_
    refine (Protocol.vote_time_le_confirmation_time S.E _).trans ?_
    rw [Proofs.HealingSurface.opening_confirmation_time_eq_action S r]
    exact hhor
  exact (Protocol.honestProposal_proposalVoteResilience_gstZero_core
    S h hslotPos hsourceHor hprop).vote_calls hsk hvoteHor P hP hv

#print axioms w4_proposal_preceq_dutyHead



/-! ## The frontier band at the duty read, at GST zero -/

/-- The round-`(q+1)` confirmation duty read IS the prepared confirmation input
read at the slot one below that round's opening, because
`confirmation_time s = support_cutoff (s + 1)`. -/
theorem w4_confirmationInputRead_pred_eq_dutyRead
    (S : Setup V) (rho : Run V) (v : V) {r : Round} (hr : 0 < r) :
    Internal.NamedRecoveryRead.confirmationInputRead S rho v
        (S.hc.opening_slot r - 1) =
      NamedActionReads.confirmationReadAt S rho v
        (w4StableDutyTime S r) := by
  have hpos : 1 ≤ S.hc.opening_slot r := w4_openingSlot_pos S hr
  simp only [Internal.NamedRecoveryRead.confirmationInputRead, w4StableDutyTime,
    Protocol.confirmation_time_eq_support_cutoff_succ,
    Nat.sub_add_cancel hpos]

#print axioms w4_confirmationInputRead_pred_eq_dutyRead

/-- **The frontier band at the duty read, at GST zero.** The weak-genesis band
(`WeakGenesis.confirmationReadBand_le_voterHeadHeight_of_gstZero_named`) is
already stated at the prepared confirmation input read of a slot, and the
previous lemma identifies that read, at the slot below the opening, with the
duty read. No participation premise beyond `WeakGenesis`. -/
theorem w4_openingSlot_two_le (S : Setup V) {r : Round} (hr : 0 < r) :
    2 ≤ S.hc.opening_slot r := by
  have hmul : 1 * 2 ≤ r * S.hc.R := Nat.mul_le_mul hr S.hc.R_ge_two
  simpa only [Protocol.HealConfig.opening_slot, Nat.one_mul] using hmul

theorem w4_dutyBand_gstZero
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {r : Round} (hr : 0 < r) (v : V) {x : V} (hx : x ∈ rho.honest)
    (hhor : S.a r ≤ rho.horizon)
    {X : NamedBlock V}
    (hX : X.erase = voterHeadAt S rho x (S.hc.opening_slot r - 1))
    (hXrun : RunBlock S rho X) :
    (NamedActionReads.confirmationReadAt S rho v
        (w4StableDutyTime S r)).st.core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg X).h := by
  have hopos : 0 < S.hc.opening_slot r := w4_openingSlot_pos S hr
  have hspos : 0 < S.hc.opening_slot r - 1 :=
    Nat.lt_of_lt_of_le Nat.zero_lt_one
      (Nat.le_sub_of_add_le (w4_openingSlot_two_le S hr))
  have hreadHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r - 1) ≤ rho.horizon := by
    have hduty : w4StableDutyTime S r ≤ rho.horizon := by
      rw [w4StableDutyTime_eq_dutyTime]
      exact (W4StableWrite.dutyTime_le_action S r).trans hhor
    simpa only [Protocol.confirmation_time_eq_support_cutoff_succ,
      Nat.sub_add_cancel hopos, w4StableDutyTime] using hduty
  have hband := WeakGenesis.confirmationReadBand_le_voterHeadHeight_of_gstZero_named
    S h hspos hreadHor (v := v) hx hX hXrun
  simpa only [w4_confirmationInputRead_pred_eq_dutyRead S rho v hr] using hband

#print axioms w4_dutyBand_gstZero


/-- The band head at an ARBITRARY duty round `r` above the opening `q`, so it
composes with the corresponding branch's round-indexed duty predicates and with the lagged
write shape. -/
def W4DutyBandHeadAt (S : Setup V) (rho : Run V) : Prop :=
  ∀ q r : Round, 0 < q → q < r →
    S.E.proposer (S.hc.opening_slot q) ∈ rho.honest →
    ∀ P : NamedBlock V, proposedBlockAt S rho (S.hc.opening_slot q) = some P →
      S.a r ≤ rho.horizon →
      ∀ v ∈ rho.honest,
        ∃ H : NamedBlock V,
          H ∈ (NamedRun.stateBeforeTime S rho
            (w4StableDutyTime S r) v).st.bodies ∧
          Block.Preceq P.erase H.erase ∧
          Block.Preceq (Protocol.get_fg_root
            (NamedRun.stateBeforeTime S rho
              (w4StableDutyTime S r) v).st.core.toHealing.toFG) H.erase ∧
          (NamedRun.stateBeforeTime S rho
            (w4StableDutyTime S r) v).st.core.h_max - 1 ≤
            (Protocol.derive_named S.E S.cfg H).h

theorem w4_dutyBandHeadAt_of_fgRoot
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    (hfg : ∀ q r : Round, 0 < q → q < r →
      S.E.proposer (S.hc.opening_slot q) ∈ rho.honest →
      ∀ P : NamedBlock V, proposedBlockAt S rho (S.hc.opening_slot q) = some P →
        S.a r ≤ rho.horizon →
        ∀ v ∈ rho.honest,
          Block.Preceq (Protocol.get_fg_root
            (NamedRun.stateBeforeTime S rho
              (w4StableDutyTime S r) v).st.core.toHealing.toFG)
            (voterHeadAt S rho v (S.hc.opening_slot r - 1))) :
    W4DutyBandHeadAt S rho := by
  intro q r hq hqr hprop P hP hhor v hv
  have hr : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le q) hqr
  obtain ⟨X, hXbody, hXerase, hXrun⟩ := w4_dutyHeadWitness S h.core hr hv
  refine ⟨X, hXbody, ?_, ?_, ?_⟩
  · rw [hXerase]
    exact w4_proposal_preceq_dutyHead S h hq hqr hprop hP hhor v hv
  · rw [hXerase]
    exact hfg q r hq hqr hprop P hP hhor v hv
  · have hband := w4_dutyBand_gstZero S h hr v hv hhor hXerase hXrun
    simpa only [NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
      using hband

#print axioms w4_dutyBandHeadAt_of_fgRoot



theorem w4_fgRootAtConfirmationRead_preceq_voteDutyHead_of_gstZero
    (S : Setup V) {rho : Run V}
    (adm : AdmissibleCore S rho) (hcom : HonestCommittees S rho.honest)
    (hgst : S.E.t_GST = 0)
    (hawake : ∀ r, 0 < r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake) rho.honest S.hc.η_SG r)
    {last d : Slot} (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hd : 1 ≤ d) (hupper : d ≤ last + 1) {t : Time}
    (ht : t ≤ Protocol.confirmation_time S.E d)
    {w x : V} (hw : w ∈ rho.honest) (hx : x ∈ rho.honest) :
    Block.Preceq
      (Protocol.get_fg_root (rho.storeBeforeTime S w t).toHealing.toFG)
      (Protocol.voteDutyHead S rho x d) := by
  have hmajority := WeakGenesis.honestWeightMajority_of_finiteWindows S hawake hhor
  rcases Proofs.HealingSurface.fgRoot_confirmationWitness_at_read S adm hmajority hw t with
    hgen | ⟨_C, _hCmem, _hCJ, a, ta, ha, hemit, hat, _hpair, hT⟩
  · rw [hgen]
    exact Protocol.preceq_genesis _
  · have haTime : S.a a.round < Protocol.vote_time S.E (d + 1) := by
      have htime : ta = S.a a.round := (Proofs.Optimistic.emits_attest_shape S hemit).2
      rw [htime] at hat
      exact (action_time_lt_proposal_of_lt_previous_confirmation S
        (Nat.zero_lt_succ d)
        (by simpa only [Nat.add_sub_cancel] using hat.trans_le ht)).trans
        (Protocol.proposal_time_lt_vote_time S.E (d + 1))
    exact ((WeakGenesis.actionSources_preceq_voteDutyHead_of_gstZero
      S adm hcom hgst hawake hhor hd hupper hx a.round haTime).2 a.val_index ha).2 _ hT

#print axioms w4_fgRootAtConfirmationRead_preceq_voteDutyHead_of_gstZero

/-- **The band head at GST zero, pin-free.** The FG-root component is the copy
above at the duty read `t = support_cutoff (opening_slot (q+1)) =
confirmation_time (opening_slot (q+1) - 1)`, with `d` the same slot below the
opening that carries the head. -/
theorem w4_dutyBandHeadAt_gstZero
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho) :
    W4DutyBandHeadAt S rho := by
  refine w4_dutyBandHeadAt_of_fgRoot S h ?_
  intro q r hq hqr hprop P hP hhor v hv
  have hr : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le q) hqr
  have hopos : 0 < S.hc.opening_slot r := w4_openingSlot_pos S hr
  have hspos : 1 ≤ S.hc.opening_slot r - 1 :=
    Nat.le_sub_of_add_le (w4_openingSlot_two_le S hr)
  have hduty : w4StableDutyTime S r ≤ rho.horizon := by
    rw [w4StableDutyTime_eq_dutyTime]
    exact (W4StableWrite.dutyTime_le_action S r).trans hhor
  have hreadHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r - 1) ≤ rho.horizon := by
    simpa only [Protocol.confirmation_time_eq_support_cutoff_succ,
      Nat.sub_add_cancel hopos, w4StableDutyTime] using hduty
  have hteq : w4StableDutyTime S r =
      Protocol.confirmation_time S.E (S.hc.opening_slot r - 1) := by
    simp only [w4StableDutyTime,
      Protocol.confirmation_time_eq_support_cutoff_succ,
      Nat.sub_add_cancel hopos]
  have hroot := w4_fgRootAtConfirmationRead_preceq_voteDutyHead_of_gstZero
    S h.core h.committees h.gstZero h.windows
    (last := S.hc.opening_slot r - 1)
    (d := S.hc.opening_slot r - 1) hreadHor hspos (Nat.le_succ _)
    (t := w4StableDutyTime S r) (le_of_eq hteq) hv hv
  simpa only [Run.storeBeforeTime, Protocol.voteDutyHead] using hroot

#print axioms w4_dutyBandHeadAt_gstZero









/-! ## One component of the band head, discharged -/











/-! ## The widened public field over the grade alone -/






set_option maxHeartbeats 400000 in

/-- `W4StableWrite.ProposalViableAtDutyRound` at an arbitrary duty round, from
the round-indexed band head. This is the interface the corresponding branch's awake-window
grade side and the corresponding branch's lagged write shape both compose with. -/
theorem w4_proposalViableAtDutyRound_of_bandHeadAt
    (S : Setup V) {rho : Run V} (hband : W4DutyBandHeadAt S rho)
    {q r : Round} (hq : 0 < q) (hqr : q < r)
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot q) = some P)
    (hhor : S.a r ≤ rho.horizon) :
    ∀ v ∈ rho.honest,
      W4StableWrite.ProposalViableAtDutyRound S rho r P.erase v := by
  intro v hv
  obtain ⟨H, hHbody, hPH, hrootH, hHband⟩ :=
    hband q r hq hqr hprop P hP hhor v hv
  set t : Time := w4StableDutyTime S r with ht
  set n := NamedRun.stateBeforeTime S rho t v with hn
  have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t v).1.1.1
  have hHmem : H.erase ∈ n.st.core.T := by
    rw [hn, hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hHbody
  have hPmem : P.erase ∈ n.st.core.T :=
    Proofs.Records.mem_of_preceq
      ((parentClosed_iff _).mp
        (Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho t v)).2
      P.erase H.erase hHmem hPH
  have hSigmaH : n.st.core.σ H.erase =
      Protocol.derive_named S.E S.cfg H :=
    Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho t v H hHbody
  have hPviable : Protocol.viable n.st.core.σ n.st.core.h_max
      n.st.core.T P.erase = true := by
    simp only [Protocol.viable, decide_eq_true_eq]
    refine ⟨H.erase, hHmem, hPH, ?_⟩
    rw [hSigmaH]
    exact hHband
  have hcompat : Block.compatible P.erase
      (Protocol.get_fg_root n.st.core.toHealing.toFG) = true :=
    Block.compatible_of_preceq_common hPH hrootH
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hn, ht, w4StableDutyTime_eq_dutyTime,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
      using hPmem
  · simpa only [hn, ht, w4StableDutyTime_eq_dutyTime,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
      using hPviable
  · simpa only [hn, ht, w4StableDutyTime_eq_dutyTime,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
      using hcompat

#print axioms w4_proposalViableAtDutyRound_of_bandHeadAt

/-- **Viability at any duty round, under `WeakGenesis`, pin-free.** -/
theorem w4_proposalViableAtDutyRound_gstZero
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {q r : Round} (hq : 0 < q) (hqr : q < r)
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot q) = some P)
    (hhor : S.a r ≤ rho.horizon) :
    ∀ v ∈ rho.honest,
      W4StableWrite.ProposalViableAtDutyRound S rho r P.erase v :=
  w4_proposalViableAtDutyRound_of_bandHeadAt S
    (w4_dutyBandHeadAt_gstZero S h) hq hqr hprop hP hhor

#print axioms w4_proposalViableAtDutyRound_gstZero




/-- The honest opening proposal is at or below every honest reader's live
confirmation at every later round's action read: it IS that record at its own
round (A2), and the GST-zero live record only grows. -/
theorem w4_proposal_preceq_actionLiveConfirmed_gstZero
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {q : Round} (hq : 0 < q)
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot q) = some P)
    {k : Round} (hqk : q ≤ k) (hhor : S.a k ≤ rho.horizon) :
    ∀ v ∈ rho.honest,
      Block.Preceq P.erase
        (actionStoreAt S rho v k).st.core.live_confirmed := by
  intro v hv
  have hsafe : GSTZeroGuarantees S rho :=
    Proofs.HealingSurface.gstZeroGuarantees_of_weakGenesis S rho h
  have hak : S.a q ≤ S.a k := Assembly.a_mono S hqk
  have hqhor : S.a q ≤ rho.horizon := hak.trans hhor
  have hslotPos : 0 < S.hc.opening_slot q := w4_openingSlot_pos S hq
  have hconfHor :
      Protocol.confirmation_time S.E (S.hc.opening_slot q) ≤ rho.horizon := by
    rw [Proofs.HealingSurface.opening_confirmation_time_eq_action S q]
    exact hqhor
  have hA2 := WeakGenesis.honestProposal_liveConfirmed_named_of_gstZero
    S h hslotPos hconfHor hprop hP v hv
  rw [Proofs.HealingSurface.opening_confirmation_time_eq_action S q] at hA2
  have hmono : Block.Preceq (rho.storeAt S v (S.a q)).live_confirmed
      (rho.storeAt S v (S.a k)).live_confirmed :=
    hsafe.liveMonotone v hv (S.a q) (S.a k) hak
  rw [w4_actionStore_liveConfirmed_eq_storeAt S
    h.core.toNamedScheduleWellFormed hv k hhor, ← hA2]
  exact hmono

#print axioms w4_proposal_preceq_actionLiveConfirmed_gstZero


/-- Persistence input 3: at every round at or after the proposal's own, the
round's SG anchor is comparable with the proposal. Both sit at or below the
same honest vote head of that round's opening slot — the anchor by the
GST-zero prepared-anchor bound, the proposal by the GST-zero vote-call family
— so `compatible_of_preceq_common` closes it. This is what lets the tier-one
walk reach `B`: either the anchor is below `B`, and the deepest clear block
dominates it, or `B` is below the anchor and hence below the vote. -/
theorem w4_actionAnchor_compatible_openingProposal_gstZero
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {q : Round} (hq : 0 < q)
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot q) = some P)
    {k : Round} (hqk : q ≤ k) (hhor : S.a k ≤ rho.horizon) :
    ∀ v ∈ rho.honest,
      Block.compatible (nodeAnchor S (actionReadAt S rho v k) k) P.erase
        = true := by
  intro v hv
  have hk : 0 < k := Nat.lt_of_lt_of_le hq hqk
  have hslotPosK : 0 < S.hc.opening_slot k := w4_openingSlot_pos S hk
  have hslotPosQ : 0 < S.hc.opening_slot q := w4_openingSlot_pos S hq
  have hqhor : S.a q ≤ rho.horizon := (Assembly.a_mono S hqk).trans hhor
  have hconfK :
      Protocol.confirmation_time S.E (S.hc.opening_slot k) ≤ rho.horizon := by
    rw [Proofs.HealingSurface.opening_confirmation_time_eq_action S k]
    exact hhor
  have hconfQ :
      Protocol.confirmation_time S.E (S.hc.opening_slot q) ≤ rho.horizon := by
    rw [Proofs.HealingSurface.opening_confirmation_time_eq_action S q]
    exact hqhor
  have hroundConf : S.hc.round_of
      (Internal.NamedRecoveryRead.confirmationInputRead S rho v
        (S.hc.opening_slot k)).st.core.s = k := by
    simpa only [Internal.NamedRecoveryRead.confirmationInputRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Proofs.HealingSurface.opening_confirmation_time_eq_action,
      Protocol.NamedStore.setClock] using Proofs.HealingLemmas.round_of_slotOf_a S k
  have hconfAnchor : namedConfirmationAnchor S
      (Internal.NamedRecoveryRead.confirmationInputRead S rho v
        (S.hc.opening_slot k)) =
      nodeAnchor S (Internal.NamedRecoveryRead.confirmationInputRead S rho v
        (S.hc.opening_slot k)) k := by
    simpa only [namedConfirmationAnchor, nodeAnchor, nodeRead,
      Protocol.get_sg_root_with, hroundConf]
  have hnode : nodeAnchor S (actionReadAt S rho v k) k =
      nodeAnchor S (Internal.NamedRecoveryRead.confirmationInputRead S rho v
        (S.hc.opening_slot k)) k := rfl
  have hanchorHead : Block.Preceq
      (namedConfirmationAnchor S
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v
          (S.hc.opening_slot k)))
      (voterHeadAt S rho v (S.hc.opening_slot k)) :=
    WeakGenesis.preparedConfirmationAnchor_preceq_voterHeadAt_of_gstZero
      S h hslotPosK hconfK hv hv
  have hsk : S.hc.opening_slot q ≤ S.hc.opening_slot k :=
    Nat.mul_le_mul_right S.hc.R hqk
  have hvoteHor : Protocol.vote_time S.E
      (S.hc.opening_slot k) ≤ rho.horizon :=
    (Protocol.vote_time_le_confirmation_time S.E _).trans hconfK
  have hPhead : Block.Preceq P.erase
      (voterHeadAt S rho v (S.hc.opening_slot k)) :=
    (Protocol.honestProposal_proposalVoteResilience_gstZero_core
      S h hslotPosQ hconfQ hprop).vote_calls hsk hvoteHor P hP hv
  rw [hnode, ← hconfAnchor]
  exact Block.compatible_of_preceq_common hanchorHead hPhead

#print axioms w4_actionAnchor_compatible_openingProposal_gstZero




private theorem w4_domain_g2_le (S : Setup V) (r : Round) (p : Phase) :
    DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2 ≤ DecoupledConsensusModel.Protocol.domain S.E S.hc r p := by
  cases p <;> simp only [DecoupledConsensusModel.Protocol.domain,
    DecoupledConsensusModel.Protocol.Phase.domainOffset] <;> linarith [S.E.Δ_pos]

/-- The slot whose vote head bounds every source of a round. -/
private theorem w4_action_lt_vote_two_after (S : Setup V) (r : Round) :
    S.a r < Protocol.vote_time S.E (S.hc.opening_slot r + 1 + 1) := by
  refine lt_of_lt_of_le
    (Protocol.action_lt_proposal_time_two_after S r) ?_
  exact le_of_lt (Protocol.proposal_time_lt_vote_time S.E _)

/-- **Every relative grade of a round has an honest window carrier, under
`WeakGenesis` alone.** No grade-forming majority. -/
theorem w4_relativeGradeCarrierAt_gstZero
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {r : Round} (hr : 0 < r) (p : Phase)
    (hhor : DecoupledConsensusModel.Protocol.domain S.E S.hc r p ≤ rho.horizon)
    (hnext : Protocol.confirmation_time S.E (S.hc.opening_slot r + 1) ≤
      rho.horizon) :
    RelativeGradeCarrierAt S rho r p := by
  obtain ⟨x, hx⟩ := Protocol.honest_nonempty_of_honestCommittees h.committees
  refine WeakJoint.relativeGradeCarrierAt_of_awakeWindowHistory_gstZero
    S h.core h.gstZero (base := 0) (D := Protocol.voteDutyHead S rho x
      (S.hc.opening_slot r + 1)) hr (Nat.zero_le _)
    (h.windows r hr ?_) ?_ ?_ p hhor
  · exact (NamedOutageClosure.action_le_domain S S.hc.R_ge_three
      (Nat.sub_lt hr (by decide))).trans ((w4_domain_g2_le S r p).trans hhor)
  · intro k _ hkr u huHon hemit
    have hact : S.a k < Protocol.vote_time S.E (S.hc.opening_slot r + 1 + 1) :=
      lt_of_le_of_lt (Assembly.a_mono S (Nat.le_of_lt hkr))
        (w4_action_lt_vote_two_after S r)
    exact (WeakGenesis.actionSources_preceq_voteDutyHead_of_gstZero S h.core
      h.committees h.gstZero h.windows hnext
      (Nat.succ_le_succ (Nat.zero_le _)) (Nat.le_succ _) hx k hact).1
      u huHon hemit
  · intro w hw
    exact ((WeakGenesis.actionSources_preceq_voteDutyHead_of_gstZero S h.core
      h.committees h.gstZero h.windows hnext
      (Nat.succ_le_succ (Nat.zero_le _)) (Nat.le_succ _) hx r
      (w4_action_lt_vote_two_after S r)).2 w hw).1

#print axioms w4_relativeGradeCarrierAt_gstZero


set_option maxHeartbeats 400000 in
/-- **The round's live confirmation is clear, under `WeakGenesis` alone.** The
grade-forming replacement for `w4_nodeClear_live_of_commonEndpoint`: the round's
G0 grade root has an honest window carrier by
`w4_relativeGradeCarrierAt_gstZero`, that carrier and the reader's live
confirmation both sit at or below the same honest vote head one slot after the
round's opening, and the clipped root is below the carrier, so the two are
compatible. No grade-forming majority and no common-endpoint premise. -/
theorem w4_nodeClear_liveConfirmed_gstZero
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {k : Round} (hk : 0 < k) {v : V} (hv : v ∈ rho.honest)
    (hhor : S.a k ≤ rho.horizon)
    (hnext : Protocol.confirmation_time S.E (S.hc.opening_slot k + 1) ≤
      rho.horizon) :
    nodeClear S (actionReadAt S rho v k) k
      (actionStoreAt S rho v k).st.core.live_confirmed = true := by
  classical
  obtain ⟨x, hx⟩ := Protocol.honest_nonempty_of_honestCommittees h.committees
  have hdomG0 : DecoupledConsensusModel.Protocol.domain S.E S.hc k .g0 ≤ rho.horizon :=
    (FrameForward.domain_le_a S k .g0).trans hhor
  have hread : Internal.NamedRecoveryRead.confirmationInputRead S rho v
      (S.hc.opening_slot k) =
      NamedActionReads.confirmationReadAt S rho v (S.a k) := by
    show NamedActionReads.confirmationReadAt S rho v
      (Protocol.confirmation_time S.E (S.hc.opening_slot k)) = _
    rw [Proofs.HealingSurface.opening_confirmation_time_eq_action S k]
  have hliveHead : Block.Preceq
      (actionStoreAt S rho v k).st.core.live_confirmed
      (voterHeadAt S rho x (S.hc.opening_slot k + 1)) := by
    rw [Proofs.HealingSurface.actionStoreAt_eq_update_confirmation_openingConfStore
      S rho v k]
    have hbound :=
      WeakGenesis.liveConfirmedSelection_preceq_voteDutyHead_of_weakGenesis_named
        S h (last := S.hc.opening_slot k + 1) (q := S.hc.opening_slot k)
        (d := S.hc.opening_slot k + 1) hnext (Nat.lt_succ_self _)
        (Nat.le_succ _) hv hx
    rwa [hread] at hbound
  have hframe := actionFrame_g0 S h.core hv hk hhor
  unfold nodeClear nodeRead
  change DecoupledConsensusModel.Protocol.clear
    (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho v k).cache
      (actionReadAt S rho v k).st.core.toHealing k)
    (actionStoreAt S rho v k).st.core.live_confirmed = true
  unfold DecoupledConsensusModel.Protocol.clear
  rw [hframe]
  cases hroot : storeRoot S.E S.hc
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc k .g0) v).st k .g0 with
  | none => rfl
  | some raw =>
      have hrawGrade : DecoupledConsensusModel.Protocol.gradeBool S.E
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc k .g0)
            v).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc k .g0) v).st.core.F
          S.hc.η_SG k (DecoupledConsensusModel.Protocol.early S.E S.hc k .g0)
          (DecoupledConsensusModel.Protocol.late S.E S.hc k .g0) raw = true :=
        (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hroot)).2
      obtain ⟨k', hk', u, huHon, hemit, hrawCarrier⟩ :=
        w4_relativeGradeCarrierAt_gstZero S h hk .g0 hdomG0 hnext v hv raw
          hrawGrade
      have hk'lt : k' < k := mem_latestWindow_lt hk'
      have hact : S.a k' < Protocol.vote_time S.E (S.hc.opening_slot k + 1 + 1) :=
        lt_of_le_of_lt (Assembly.a_mono S (Nat.le_of_lt hk'lt))
          (w4_action_lt_vote_two_after S k)
      have hcarrHead : Block.Preceq (actionSGBlockAt S rho u k')
          (voterHeadAt S rho x (S.hc.opening_slot k + 1)) :=
        (WeakGenesis.actionSources_preceq_voteDutyHead_of_gstZero S h.core
          h.committees h.gstZero h.windows hnext
          (Nat.succ_le_succ (Nat.zero_le _)) (Nat.le_succ _) hx k' hact).1
          u huHon hemit
      have hclipHead : Block.Preceq
          (DecoupledConsensusModel.Protocol.clipGrade raw
            (actionReadAt S rho v k).st.core.F)
          (voterHeadAt S rho x (S.hc.opening_slot k + 1)) :=
        Block.preceq_trans
          (NamedOutageClosure.q10_clip_preceq raw
            (actionReadAt S rho v k).st.core.F)
          (Block.preceq_trans hrawCarrier hcarrHead)
      change Block.compatible
        (actionStoreAt S rho v k).st.core.live_confirmed
        (DecoupledConsensusModel.Protocol.clipGrade raw
          (actionReadAt S rho v k).st.core.F) = true
      exact Block.compatible_of_preceq_common hliveHead hclipHead

#print axioms w4_nodeClear_liveConfirmed_gstZero








/-- **The prepared confirmation anchor at a round's opening slot IS the action
read's `nodeAnchor`.** Three rewrites and no protocol content: the confirmation
store is the confirmation input read's core, that read at the opening slot is
the action read, and the store's own slot sits in round `k`. -/
theorem w4_confAnchorWith_eq_nodeAnchor
    (S : Setup V) (rho : Run V) (v : V) (k : Round) :
    Protocol.confAnchorWith
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadAt S rho v (S.a k)).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot k)) =
      nodeAnchor S (actionReadAt S rho v k) k := by
  have hread : Internal.NamedRecoveryRead.confirmationInputRead S rho v
      (S.hc.opening_slot k) =
      NamedActionReads.confirmationReadAt S rho v (S.a k) := by
    simp only [Internal.NamedRecoveryRead.confirmationInputRead, Setup.a,
      Protocol.a_eq_confirmation_time]
  have hround : S.hc.round_of
      (NamedActionReads.confirmationReadAt S rho v (S.a k)).st.core.s = k := by
    simpa only [NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Proofs.HealingSurface.opening_confirmation_time_eq_action,
      Protocol.NamedStore.setClock] using Proofs.HealingLemmas.round_of_slotOf_a S k
  have hstore : Proofs.Optimistic.confStore S rho v (S.hc.opening_slot k) =
      (NamedActionReads.confirmationReadAt S rho v (S.a k)).st.core := by
    rw [← hread]; rfl
  have hnode : nodeAnchor S (actionReadAt S rho v k) k =
      nodeAnchor S (NamedActionReads.confirmationReadAt S rho v (S.a k)) k := by
    rw [← hread]; rfl
  rw [hnode, hstore]
  simpa only [Protocol.confAnchorWith, nodeAnchor, nodeRead,
    Protocol.get_sg_root_with] using congrArg Protocol.GradeRead.anchor
      (congrArg _ hround)

#print axioms w4_confAnchorWith_eq_nodeAnchor


/-- **The confirmation write at an action read, as the cover needs it.** Either
the round's anchor is at or below the live confirmation, or the live
confirmation IS the reader's own FG root. No premise at all: this is the shape
of the write.

Both arms feed the persistence cover, and neither needs the anchor bridge 
forbids. On the walk arm the ghost descent starts at the prepared confirmation
anchor, which `w4_confAnchorWith_eq_nodeAnchor` identifies with `nodeAnchor` at
the same read. On the root arm the write is `confRoot`, the reader's FG root
unchanged by the confirmation duty. -/
theorem w4_anchor_preceq_liveConfirmed_or_fgRoot
    (S : Setup V) (rho : Run V) (v : V) (k : Round) :
    Block.Preceq (nodeAnchor S (actionReadAt S rho v k) k)
        (actionStoreAt S rho v k).st.core.live_confirmed ∨
      (actionStoreAt S rho v k).st.core.live_confirmed =
        Protocol.get_fg_root
          (actionReadAt S rho v k).st.core.toHealing.toFG := by
  classical
  set contract := NamedProfile.gradeContract
    (NamedActionReads.confirmationReadAt S rho v (S.a k)).cache with hcontract
  set st := Proofs.Optimistic.confStore S rho v (S.hc.opening_slot k) with hst
  have hcore : (actionStoreAt S rho v k).st.core =
      Protocol.update_confirmation_with contract S.E S.hc st
        (S.hc.opening_slot k) :=
    Proofs.HealingSurface.actionStoreAt_eq_update_confirmation_openingConfStore S rho v k
  have hlive : (actionStoreAt S rho v k).st.core.live_confirmed =
      if Protocol.confEligible S.E st (S.hc.opening_slot k)
          (Protocol.confWalkWith contract S.E S.hc st
            (S.hc.opening_slot k)) then
        Protocol.confWalkWith contract S.E S.hc st (S.hc.opening_slot k)
      else Protocol.confRoot st := by
    rw [hcore]
    exact Protocol.update_confirmation_with_live_confirmed contract S.E S.hc
      st (S.hc.opening_slot k)
  by_cases helig : Protocol.confEligible S.E st (S.hc.opening_slot k)
      (Protocol.confWalkWith contract S.E S.hc st (S.hc.opening_slot k))
  · refine Or.inl ?_
    rw [hlive, if_pos helig, ← w4_confAnchorWith_eq_nodeAnchor S rho v k]
    exact Protocol.ghost_preceq _ _ _ _
  · refine Or.inr ?_
    rw [hlive, if_neg helig]
    have hstore : st =
        (NamedActionReads.confirmationReadAt S rho v (S.a k)).st.core := by
      have hread : Internal.NamedRecoveryRead.confirmationInputRead S rho v
          (S.hc.opening_slot k) =
          NamedActionReads.confirmationReadAt S rho v (S.a k) := by
        simp only [Internal.NamedRecoveryRead.confirmationInputRead, Setup.a,
          Protocol.a_eq_confirmation_time]
      rw [hst, ← hread]; rfl
    have hfg : Protocol.get_fg_root
          (actionReadAt S rho v k).st.core.toHealing.toFG =
        Protocol.get_fg_root st.toHealing.toFG := by
      rw [hstore]
      simp only [Proofs.HealingSurface.actionReadAt, NamedActionReads.actionReadAt,
        NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadAt,
        Protocol.NamedDuties.update_confirmation_with,
        Protocol.update_confirmation_with, Protocol.get_fg_root,
        Protocol.Store.toHealing]
    simp only [Protocol.confRoot]
    exact hfg.symm

#print axioms w4_anchor_preceq_liveConfirmed_or_fgRoot

/-! ## The cover step, both arms

With the write dichotomy the cover no longer takes an order fact. It cases on
the two arms of the write, and only ONE of the four SG-vote tiers ever reaches
for the round's grade. -/


/-- **The FG root is at or below the prepared-frame anchor.**  copy of the
private `NamedOutageClosure.SupportCarry.carry_root_preceq_anchor`; its two
support lemmas are public. -/
theorem w4_fgRoot_preceq_anchor
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V) (r : Round)
    (g1 : Option (Option (Block V))) :
    Block.Preceq (Protocol.get_fg_root st.toFG)
      (DecoupledConsensusModel.Protocol.anchor E hc st r g1) := by
  cases g1 with
  | none => exact Block.preceq_self _
  | some opt =>
    cases opt with
    | none => exact Block.preceq_self _
    | some root =>
      change Block.Preceq (Protocol.get_fg_root st.toFG)
        ((DecoupledConsensusModel.Protocol.activePrefix
          (Protocol.get_filtered_block_tree st.toFG) root).getD
            (Protocol.get_fg_root st.toFG))
      cases hp : DecoupledConsensusModel.Protocol.activePrefix
          (Protocol.get_filtered_block_tree st.toFG) root with
      | none => simpa only [hp, Option.getD_none] using Block.preceq_self _
      | some X =>
        simpa only [hp, Option.getD_some] using
          Proofs.Records.preceq_get_fg_root_of_mem_filtered
            (NamedProposalParent.activePrefix_mem _ root X hp)

#print axioms w4_fgRoot_preceq_anchor

/-- The same at a named read's own `nodeAnchor`. -/
theorem w4_fgRoot_preceq_nodeAnchor
    (S : Setup V) (n : NamedNodeState V) (r : Round) :
    Block.Preceq (Protocol.get_fg_root n.st.core.toHealing.toFG)
      (nodeAnchor S n r) :=
  w4_fgRoot_preceq_anchor S.E S.hc n.st.core.toHealing r _

#print axioms w4_fgRoot_preceq_nodeAnchor











end Proofs
end DecoupledConsensusModel

end
