module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.TimeoutDelay
public import DecoupledConsensusProofs.Generic.EvaluationStore
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordTargetHistory
public import DecoupledConsensusProofs.Objects.PostGSTSync
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.ProposalCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionActivity
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsProducers
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeDelivery
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityQuorumCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FrontierRise
public import DecoupledConsensusProofs.Generic.FrontierCoverage
public import DecoupledConsensusProofs.Execution.FixedHeightRootRetry
public import DecoupledConsensusProofs.Protocol.ValidatorClient.HeightPairCases
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordFresh
public import DecoupledConsensusProofs.Execution.RawHeightAdapters
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordClean
public import DecoupledConsensusProofs.Protocol.Handlers.StoreFinality
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge
public import DecoupledConsensusProofs.Protocol.Handlers.JustificationBound
public import DecoupledConsensusProofs.Execution.EmissionShape
public import DecoupledConsensusProofs.Protocol.Handlers.SGArrival
public import DecoupledConsensusProofs.Generic.SlotFreshness
public import DecoupledConsensusProofs.Protocol.ChainState.TargetedTimeoutBinding

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Exact raw-height action coverage -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol (ChainState HeightConfig)
open Protocol (Record height_pair own_lock record_attestation)
open Internal
open Execution
open Internal.HealingSurface
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}












/-- Named action coverage with timeout rows bound to the parent's exact entry.
The older generic named coverage permits an arbitrary timeout entry and cannot
by itself advance the targeted height transition. -/
def NamedTargetedHonestActionProposalCoverageAt
    (S : Setup V) (rho : Run V) (r : Round)
    (B : NamedBlock V) (H : Height) (T : BlockId) : Prop :=
  let sigma := Protocol.derive_named S.E S.cfg B.parent
  ∀ v ∈ rho.honest,
    ((actionAttestationAt S rho v r ∈
          Protocol.named_chain_attestations B.parent ∧
        v ∈ sigma.progress ∧
        ((actionAttestationAt S rho v r).height_pair = .vote H T false →
          v ∈ sigma.target_participation)) ∨
      actionAttestationAt S rho v r ∈ B.attestations) ∧
      ((actionAttestationAt S rho v r).height_pair = .vote H T false ∨
        (actionAttestationAt S rho v r).height_pair = .vote H T true)

omit [Fintype V] in
private theorem named_progress_subset_foldl
    (rows : List (NamedAttestation V))
    (sigma : Protocol.ChainState V) :
    sigma.progress ⊆
      (rows.foldl (Protocol.process_attestation_with
        (Protocol.TimeoutBinding.targeted V)) sigma).progress := by
  induction rows generalizing sigma with
  | nil => exact Finset.Subset.refl _
  | cons row rows ih =>
      rw [List.foldl_cons]
      apply Finset.Subset.trans _ (ih _)
      intro signer hsigner
      rw [(TargetedTimeoutBinding.process_height_fields sigma row).1]
      split_ifs
      · exact Finset.mem_insert_of_mem hsigner
      · exact hsigner

omit [Fintype V] in
private theorem named_mem_progress_foldl_of_matching
    {a : NamedAttestation V} :
    ∀ (rows : List (NamedAttestation V))
      (sigma : Protocol.ChainState V),
      a ∈ rows →
      a.height_pair.matchesEntry sigma.h sigma.T_h.root = true →
      a.val_index ∈
        (rows.foldl (Protocol.process_attestation_with
          (Protocol.TimeoutBinding.targeted V)) sigma).progress := by
  intro rows
  induction rows with
  | nil => intro sigma ha _; simp at ha
  | cons row rows ih =>
      intro sigma ha hmatch
      rw [List.foldl_cons]
      rcases List.mem_cons.mp ha with rfl | htail
      · apply named_progress_subset_foldl
        rw [(TargetedTimeoutBinding.process_height_fields sigma a).1,
          if_pos hmatch]
        exact Finset.mem_insert_self _ _
      · apply ih _ htail
        have hfields := TimeoutBindingDefaults.process_context_fields
          (Protocol.TimeoutBinding.targeted V) sigma row
        rw [hfields.2.1, hfields.2.2.1]
        exact hmatch

omit [Fintype V] in
private theorem named_foldl_s
    (rows : List (NamedAttestation V))
    (sigma : Protocol.ChainState V) :
    (rows.foldl (Protocol.process_attestation_with
      (Protocol.TimeoutBinding.targeted V)) sigma).s = sigma.s := by
  induction rows generalizing sigma with
  | nil => rfl
  | cons row rows ih =>
      rw [List.foldl_cons, ih]
      unfold Protocol.process_attestation_with
      unfold Protocol.process_attestation
      split_ifs <;> rfl

/-- Exact targeted action coverage advances the named proposal by one height. -/
theorem named_proposedBlock_height_eq_succ_of_actionCoverage
    (S : Setup V) {rho : Run V} (hfb : BelowOneThird S rho.honest)
    {r : Round} {s : Slot} {H : Height} {T : BlockId}
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B)
    (hmature : ProposalTimeoutMatureAt S rho s)
    (hcoverage : NamedTargetedHonestActionProposalCoverageAt
      S rho r B H T)
    (hPheight : (Protocol.derive_named S.E S.cfg B.parent).h = H)
    (hPtarget :
      (Protocol.derive_named S.E S.cfg B.parent).T_h.root = T) :
    (Protocol.derive_named S.E S.cfg B).h = H + 1 := by
  obtain ⟨parent, hparent, -⟩ := proposedBlockAt_parent S rho s hB
  cases B with
  | genesis => cases hparent
  | node parent' slot root votes support rows proposer =>
      have hparentEq : parent' = parent := Option.some.inj hparent
      subst parent
      let sigma := Protocol.derive_named S.E S.cfg parent'
      let block : NamedBlock V :=
        .node parent' slot root votes support rows proposer
      let folded := Protocol.fold_rows
        (Protocol.TimeoutBinding.targeted V) sigma block.erase rows
      have hslot : slot = s := by
        simpa only [block, NamedBlock.slot] using proposedBlockAt_slot S rho s hB
      have hquorum : S.E.electorate.IsQuorum folded.progress := by
        apply Protocol.isQuorum_of_subset
          (AlignedRoundLemmas.honestQuorum_of_belowOneThird hfb)
        intro v hv
        obtain ⟨hcovered, hpair⟩ := hcoverage v hv
        rcases hcovered with hparentCovered | hchild
        · have hsubset := named_progress_subset_foldl rows
            ({sigma with s := block.erase.slot})
          exact hsubset hparentCovered.2.1
        · rw [← (actionAttestationAt_shape S rho v r).1]
          apply named_mem_progress_foldl_of_matching rows
            ({sigma with s := block.erase.slot}) hchild
          rcases hpair with htarget | htimeout
          · simpa [htarget, NamedHeightPair.matchesEntry, sigma] using
              And.intro hPheight.symm hPtarget.symm
          · simpa [htimeout, NamedHeightPair.matchesEntry, sigma] using
              And.intro hPheight.symm hPtarget.symm
      have hmature' : folded.T_h.slot + S.cfg.timeoutDelay ≤ folded.s := by
        have hm := hmature block hB parent' rfl
        have hfields := NamedDerivationGeometry.fold_context_fields
          (Protocol.TimeoutBinding.targeted V) rows
          ({sigma with s := block.erase.slot})
        change sigma.T_h.slot + S.cfg.timeoutDelay ≤ s at hm
        change folded.T_h.slot + S.cfg.timeoutDelay ≤ folded.s
        rw [show folded.T_h = sigma.T_h by exact hfields.2.2.1]
        rw [show folded.s = block.erase.slot by
          exact named_foldl_s rows ({sigma with s := block.erase.slot})]
        simpa only [block, Proofs.NamedWire.erase_slot, hslot] using hm
      change (Protocol.process_height_events S.E S.cfg folded).h = H + 1
      rw [NjGap.advances_of_progress_quorum S.E S.cfg hmature' hquorum]
      have hfields := NamedDerivationGeometry.fold_context_fields
        (Protocol.TimeoutBinding.targeted V) rows
        ({sigma with s := block.erase.slot})
      rw [show folded.h = sigma.h by exact hfields.2.1]
      exact congrArg (· + 1) hPheight






private theorem roundActionFinalityHeight_lt_actionHMax_named
    (S : Setup V) {rho : Run V} (_adm : Admissible S rho)
    (v : V) (r : Round) {H : Height} {T : BlockId}
    (hpair : (actionAttestationAt S rho v r).finality_pair = some ⟨H, T⟩) :
    H < (actionStoreAt S rho v r).st.core.h_max := by
  let ast := actionStoreAt S rho v r
  have hJ : ast.st.core.J ∈ ast.st.core.T := by
    simpa only [ast, actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using
        Proofs.NamedStoreBridge.justifiedInTree_stateBeforeTime S rho (S.a r) v
  have hF : ast.st.core.F ∈ ast.st.core.T := by
    simpa only [ast, actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using
        Proofs.NamedStoreBridge.finalizedInTree_stateBeforeTime S rho (S.a r) v
  have hpair' :
      (Protocol.NamedActions.round_action_with
        (DecoupledConsensusModel.Protocol.frameContract ast.cache) S.E S.hc
        (S.node v) ast.st.core.toHealing ast.record).2.finality_pair =
          some ⟨H, T⟩ := by
    simpa only [ast, actionAttestationAt, actionStoreAt, actionReadAt,
      Protocol.NamedDuties.attest_with] using hpair
  obtain ⟨Hd, hHd, hHdHeight⟩ :=
    round_action_head_mem_frame ast.cache S.E S.hc (S.node v)
      ast.st.core ast.record hJ hF hpair'
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg ast.st := by
    apply Proofs.NamedConfirmationMembership.invariant_update
    exact Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ (S.a r)
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a r) v).1
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg ast.st := hinv.1.1
  have hHdImage := hHd
  rw [hcoh.1] at hHdImage
  obtain ⟨D, hD, hDerase⟩ := Finset.mem_image.mp hHdImage
  have hDHeight : (Protocol.derive_named S.E S.cfg D).h_j = H := by
    rw [← hcoh.2.2.2.2 D hD, hDerase]
    exact hHdHeight
  have hnoPre :=
    NamedJustificationBound.noHighJustifications_stateBeforeTime
      S rho (S.a r) v
  have hno : NamedNoHighJustifications S.E S.cfg ast.st := by
    simpa only [ast, actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hnoPre
  have hbelowPre :=
    NamedJustificationBound.justificationBelowMax_stateBeforeTime
      S rho (S.a r) v
  have hbelow : ast.st.core.h_j < ast.st.core.h_max := by
    simpa only [ast, actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hbelowPre
  exact (hDHeight ▸ hno D hD).trans_lt hbelow

private theorem recordLock_finalityEmission_before_named
    (S : Setup V) (rho : Run V) (v : V) :
    ∀ (n : Nat) {H : Height} {T : BlockId},
      (rho.stateBefore S n v).record.legacy.lock H = some T →
        ∃ (i : Nat), i < n ∧ ∃ (t : Time) (a : NamedAttestation V),
          rho.events[i]? = some (Event.tick v t) ∧
            Object.attest a ∈ (on_tick_emit S v
              (rho.stateBefore S i v) t).2 ∧
            a.finality_pair = some ⟨H, T⟩ := by
  intro n
  induction n with
  | zero =>
      intro H T hlock
      exact absurd hlock (by
        simp [Run.stateBefore, NamedRun.stateBefore, NamedWorld.init,
          NamedNode.initial, Protocol.NamedRecord.initial, Record.initial])
  | succ n ih =>
      intro H T hlock
      change (NamedRun.stateBefore S rho (n + 1) v).record.legacy.lock H =
        some T at hlock
      cases hpre : (rho.stateBefore S n v).record.legacy.lock H with
      | some X =>
          have hmono :
              (rho.stateBefore S (n + 1) v).record.legacy.lock H = some X :=
            stateBefore_lock_mono S rho v (n + 1) (Nat.le_succ n) hpre
          have hXT : X = T := by
            rw [hlock] at hmono
            exact (Option.some.inj hmono).symm
          subst X
          obtain ⟨i, hi, t, a, hevent, hemitted, hpair⟩ := ih hpre
          exact ⟨i, Nat.lt_succ_of_lt hi, t, a, hevent, hemitted, hpair⟩
      | none =>
          change (NamedRun.stateBefore S rho n v).record.legacy.lock H =
            none at hpre
          have hstep := congrFun (Proofs.NamedRuntime.stateBefore_succ S rho n) v
          cases hevent : rho.events[n]? with
          | none =>
              rw [hstep, hevent] at hlock
              simp only [Option.toList, List.foldl_nil] at hlock
              exact absurd hlock (by rw [hpre]; simp)
          | some e =>
              cases e with
              | tick u t =>
                  by_cases huv : u = v
                  · subst u
                    have hpost :
                        (on_tick_emit S v
                          (rho.stateBefore S n v) t).1.record.legacy.lock H =
                            some T := by
                      rw [← stateBefore_succ_record S rho hevent]
                      exact hlock
                    obtain ⟨a, hemitted, hpair⟩ :=
                      Protocol.on_tick_emit_lock_introduced
                        S v (rho.stateBefore S n v) t hpre hpost
                    exact ⟨n, Nat.lt_succ_self n, t, a, hevent,
                      hemitted, hpair⟩
                  · rw [hstep, hevent] at hlock
                    simp only [Option.toList, List.foldl_cons,
                      List.foldl_nil, NamedWorld.step,
                      Function.update_of_ne (Ne.symm huv)] at hlock
                    exact absurd hlock (by rw [hpre]; simp)
              | deliver u o t =>
                  by_cases huv : u = v
                  · subst u
                    rw [hstep, hevent] at hlock
                    simp only [Option.toList, List.foldl_cons,
                      List.foldl_nil, NamedWorld.step,
                      Function.update_self] at hlock
                    change (NamedNode.process S
                      (NamedRun.stateBefore S rho n v) o).Λ.legacy.lock H =
                        some T at hlock
                    rw [process_record] at hlock
                    exact absurd hlock (by rw [hpre]; simp)
                  · rw [hstep, hevent] at hlock
                    simp only [Option.toList, List.foldl_cons,
                      List.foldl_nil, NamedWorld.step,
                      Function.update_of_ne (Ne.symm huv)] at hlock
                    exact absurd hlock (by rw [hpre]; simp)

private theorem recordLockHeight_lt_actionHMax_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (v : V) (r : Round) {H : Height} {T : BlockId}
    (hlock : (rho.stateBeforeTime S (S.a r) v).record.legacy.lock H =
      some T) :
    H < (actionStoreAt S rho v r).st.core.h_max := by
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.a r)
  have hlockN : (rho.stateBefore S n v).record.legacy.lock H = some T := by
    rw [← congrFun hn v]
    exact hlock
  obtain ⟨i, hi, t, a, hevent, hemitted, hpair⟩ :=
    recordLock_finalityEmission_before_named S rho v n hlockN
  have hemit : rho.emits S v (Object.attest a) t :=
    ⟨i, hevent, hemitted⟩
  have hshape := Proofs.Optimistic.emits_attest_shape S hemit
  have haeq : a = actionAttestationAt S rho v a.round := by
    have hemit' : rho.emits S v (Object.attest a) (S.a a.round) := by
      rw [← hshape.2]
      exact hemit
    exact (NamedActionSources.action_run_emission S rho
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      v a.round a).mp hemit' |>.2.2
  have hlocal : H <
      (actionStoreAt S rho v a.round).st.core.h_max := by
    apply roundActionFinalityHeight_lt_actionHMax_named S adm v a.round
    rw [← haeq]
    exact hpair
  have hbefore := Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hevent
  change NamedRun.stateBefore S rho i v =
    NamedRun.stateBeforeTime S rho t v at hbefore
  have hlocalEq :
      (actionStoreAt S rho v a.round).st.core.h_max =
        (rho.stateBefore S i v).st.core.h_max := by
    change (NamedRun.stateBeforeTime S rho (S.a a.round) v).st.core.h_max =
      (NamedRun.stateBefore S rho i v).st.core.h_max
    rw [← hshape.2, ← hbefore]
  rw [hlocalEq] at hlocal
  have hmono := stateBefore_hMax_mono S rho v (Nat.le_of_lt hi)
  have hcurrentEq : (actionStoreAt S rho v r).st.core.h_max =
      (rho.stateBefore S n v).st.core.h_max := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using
        congrArg (fun x : NodeState V => x.st.core.h_max) (congrFun hn v)
  rw [hcurrentEq]
  exact hlocal.trans_le hmono

private theorem ownLockHeight_lt_actionHMax_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (v : V) (r : Round) {H : Height} {locked : BlockId}
    (hlock : own_lock
      (rho.stateBeforeTime S (S.a r) v).record.legacy H
      (actionAttestationAt S rho v r).finality_pair = some locked) :
    H < (actionStoreAt S rho v r).st.core.h_max := by
  cases hfp : (actionAttestationAt S rho v r).finality_pair with
  | none =>
      apply recordLockHeight_lt_actionHMax_named S adm v r
      simpa [own_lock, hfp] using hlock
  | some p =>
      rcases p with ⟨h, target⟩
      by_cases hh : h = H
      · subst h
        have ht : target = locked := by
          simpa [own_lock, hfp] using hlock
        subst target
        exact roundActionFinalityHeight_lt_actionHMax_named
          S adm v r hfp
      · apply recordLockHeight_lt_actionHMax_named S adm v r
        simpa [own_lock, hfp, hh] using hlock

private theorem actionBody_runBlock_coverage
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionStoreAt S rho v r).st.bodies) :
    RunBlock S rho D := by
  have hDpre : D ∈ (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hD
  obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted (S.a r)
  have hDi : D ∈ (rho.stateBefore S i v).st.bodies := by
    change D ∈ (NamedRun.stateBefore S rho i v).st.bodies
    rw [← hi]
    exact hDpre
  exact Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hDi)

/-- An honest named exact action emits the fixed target or timeout unless its
local raw frontier is already above the fixed height. -/
theorem actionAttestationAt_pair_or_hMaxRise
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (hr : 0 < r) (hhor : S.a r ≤ rho.horizon)
    {C : NamedBlock V} {H : Height} {T : BlockId}
    (hforms : NamedGradeFormsAt S rho r C.erase)
    (hCrun : RunBlock S rho C)
    (hCheight : (Protocol.derive_named S.E S.cfg C).h = H)
    (hCtarget : (Protocol.derive_named S.E S.cfg C).T_h.root = T)
    {v : V} (hv : v ∈ rho.honest)
    (hwindow : FinalityFilterRetainedAtRead S rho v (S.a r) C.erase) :
    ((actionAttestationAt S rho v r).height_pair = .vote H T false ∨
      (actionAttestationAt S rho v r).height_pair = .vote H T true) ∨
      H < (actionStoreAt S rho v r).st.core.h_max := by
  let ast := actionStoreAt S rho v r
  have hactive : C.erase ∈ PhaseGrades.filteredTree
      (actionReadAt S rho v r) :=
    namedGradeFormsAt_actionStore_of_window S hforms hv hwindow
  obtain ⟨Q, hsource⟩ := exists_actionFGSource_of_namedGradeFormsAt
    S adm.toNamedAdmissibleCore hr hhor hforms hv hactive
  have hsource' : actionFGSource S ast = some Q := by
    have hround : S.hc.round_of ast.st.core.toHealing.s = r := by
      simpa only [ast, actionStoreAt, actionReadAt] using
        Proofs.HealingLemmas.round_of_slotOf_a S r
    simpa only [PhaseGrades.nodeFGSource, actionFGSource, ast, hround] using
      hsource
  obtain ⟨DQ, hDQ, hDQerase, hDQderive, -⟩ :=
    NamedActionSources.action_witness S rho v r Q hsource'
  have hDQderive' : ast.st.core.σ Q =
      Protocol.derive_named S.E S.cfg DQ := by
    simpa only [ast, actionStoreAt] using hDQderive
  have hDQrun : RunBlock S rho DQ :=
    actionBody_runBlock_coverage S adm hv hDQ
  have hCQerase : Block.Preceq C.erase DQ.erase := by
    rw [hDQerase]
    exact namedGradeFormsAt_preceq_actionSource S
      adm.toNamedAdmissibleCore hr hhor hforms hv hactive hsource
  obtain ⟨A, hADQ, hAerasure⟩ :=
    Proofs.NamedAncestry.erased_ancestor_lift DQ hCQerase
  have hArun : RunBlock S rho A :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hDQrun hADQ
  have hAC : A = C :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      A C hArun hCrun A C (Or.inl (Proofs.NamedAncestry.named_self A))
        (Or.inr (Proofs.NamedAncestry.named_self C)) (by
          rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root C,
            hAerasure])
  have hCQ : NamedBlock.Preceq C DQ := by
    rw [← hAC]
    exact hADQ
  have hfloor : H ≤ (ast.st.core.σ Q).h := by
    rw [hDQderive', ← hCheight]
    exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hCQ
  have hcap : (ast.st.core.σ Q).h ≤ ast.st.core.h_max := by
    apply treeHeightsLeHMax_actionStore S adm v r Q
    have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg ast.st := by
      apply Proofs.NamedConfirmationMembership.invariant_update
      exact Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _
        (S.a r) (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a r) v).1
    rw [hinv.1.1.1, ← hDQerase]
    exact Finset.mem_image_of_mem NamedBlock.erase (by
      simpa only [ast, actionStoreAt] using hDQ)
  have hsourceCases :
      ((ast.st.core.σ Q).h = H ∧
        (ast.st.core.σ Q).T_h.root = T) ∨
        H < ast.st.core.h_max := by
    rcases eq_or_lt_of_le hfloor with heq | hlt
    · left
      have hsame : (Protocol.derive_named S.E S.cfg DQ).h =
          (Protocol.derive_named S.E S.cfg C).h := by
        calc
          _ = (ast.st.core.σ Q).h :=
            congrArg (fun X => X.h) hDQderive'.symm
          _ = H := heq.symm
          _ = _ := hCheight.symm
      have htargetEq := Proofs.NamedEntryHeight.entry_eq_on_plateau
        S.E S.cfg hCQ hsame.symm
      refine ⟨heq.symm, ?_⟩
      calc
        (ast.st.core.σ Q).T_h.root =
            (Protocol.derive_named S.E S.cfg DQ).T_h.root :=
          congrArg (fun X => X.T_h.root) hDQderive'
        _ = (Protocol.derive_named S.E S.cfg C).T_h.root :=
          congrArg (fun X => X.root) htargetEq.symm
        _ = T := hCtarget
    · exact Or.inr (hlt.trans_le hcap)
  rcases hsourceCases with ⟨hQheight, hQtarget⟩ | hrise
  · have hcases := round_action_height_pair_cases
      (NamedProfile.gradeContract ast.cache) S.E S.hc (S.node v)
      ast.st.core.toHealing ast.record
    rcases hcases with hnone | ⟨Q', hQ', hresult⟩
    · have hnone' : actionFGSource S ast = none := by
        simpa only [actionFGSource, ast] using hnone.1
      rw [hsource'] at hnone'
      contradiction
    · have hQeq : Q' = Q := by
        have hQ'' : actionFGSource S ast = some Q' := by
          simpa only [actionFGSource, ast] using hQ'
        rw [hsource'] at hQ''
        exact Option.some.inj hQ''.symm
      subst Q'
      rcases hresult with hoff | htarget | htimeout
      · right
        obtain ⟨locked, -, hown, -, -⟩ := hoff
        have hown' : own_lock ast.record.legacy H
            (actionAttestationAt S rho v r).finality_pair = some locked := by
          rw [← hQheight]
          change own_lock ast.record.legacy (ast.st.core.σ Q).h
            (actionAttestationAt S rho v r).finality_pair = some locked
          simpa only [actionAttestationAt, ast, actionStoreAt,
            Protocol.NamedDuties.attest_with] using hown
        apply ownLockHeight_lt_actionHMax_named S adm v r
        simpa only [ast, actionStoreAt, actionReadAt,
          NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
          NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
          NamedRun.stateBeforeTime] using hown'
      · left; left
        change (actionAttestationAt S rho v r).height_pair =
          .vote (ast.st.core.σ Q).h
            (ast.st.core.σ Q).T_h.root false at htarget
        rw [hQheight, hQtarget] at htarget
        exact htarget
      · left; right
        change (actionAttestationAt S rho v r).height_pair =
          .vote (ast.st.core.σ Q).h
            (ast.st.core.σ Q).T_h.root true at htimeout
        rw [hQheight, hQtarget] at htimeout
        exact htimeout
  · exact Or.inr hrise

private theorem namedTransition_eq_afterFin_of_height_eq
    (E : Env V) (cfg : HeightConfig)
    (st : ChainState V) (B : NamedBlock V)
    (hh : (Protocol.named_transition E cfg st B).h = st.h) :
    Protocol.named_transition E cfg st B =
      Protocol.afterFin E (Protocol.fold_rows
        (Protocol.TimeoutBinding.targeted V)
        st B.erase B.attestations) := by
  unfold Protocol.named_transition
    Protocol.transition_rows at hh ⊢
  rw [Protocol.process_height_events_eq] at hh ⊢
  split_ifs at hh ⊢ with ht hp
  · have hfold := NamedDerivationGeometry.fold_context_fields
      (Protocol.TimeoutBinding.targeted V) B.attestations
      ({st with s := B.erase.slot})
    rw [Protocol.advance_height_h, Protocol.afterFin_h,
      show (Protocol.fold_rows
        (Protocol.TimeoutBinding.targeted V)
        st B.erase B.attestations).h = st.h by exact hfold.2.1] at hh
    exact False.elim (Nat.succ_ne_self _ hh)
  · have hfold := NamedDerivationGeometry.fold_context_fields
      (Protocol.TimeoutBinding.targeted V) B.attestations
      ({st with s := B.erase.slot})
    rw [Protocol.advance_height_h, Protocol.afterFin_h,
      show (Protocol.fold_rows
        (Protocol.TimeoutBinding.targeted V)
        st B.erase B.attestations).h = st.h by exact hfold.2.1] at hh
    exact False.elim (Nat.succ_ne_self _ hh)
  · rfl

private theorem namedProgress_subset_node_of_same_height
    (E : Env V) (cfg : HeightConfig)
    (p : NamedBlock V) (s : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V))
    (rows : List (NamedAttestation V)) (proposer : V)
    (hh : (Protocol.derive_named E cfg
      (.node p s root votes support rows proposer)).h =
        (Protocol.derive_named E cfg p).h) :
    (Protocol.derive_named E cfg p).progress ⊆
      (Protocol.derive_named E cfg
        (.node p s root votes support rows proposer)).progress := by
  have hstay := namedTransition_eq_afterFin_of_height_eq E cfg
    (Protocol.derive_named E cfg p)
    (.node p s root votes support rows proposer) hh
  rw [Protocol.derive_named, hstay, Protocol.afterFin_progress]
  change (Protocol.derive_named E cfg p).progress ⊆
    (rows.foldl (Protocol.process_attestation_with
      (Protocol.TimeoutBinding.targeted V))
      {Protocol.derive_named E cfg p with s := s}).progress
  simpa only using named_progress_subset_foldl rows
    ({Protocol.derive_named E cfg p with s := s})

private theorem namedPair_mem_progress_node_of_same_height
    (E : Env V) (cfg : HeightConfig)
    (p : NamedBlock V) (s : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V))
    (rows : List (NamedAttestation V)) (proposer : V)
    {a : NamedAttestation V} (ha : a ∈ rows)
    (hpair : a.height_pair = .vote
          (Protocol.derive_named E cfg p).h
          (Protocol.derive_named E cfg p).T_h.root false ∨
        a.height_pair = .vote
          (Protocol.derive_named E cfg p).h
          (Protocol.derive_named E cfg p).T_h.root true)
    (hh : (Protocol.derive_named E cfg
      (.node p s root votes support rows proposer)).h =
        (Protocol.derive_named E cfg p).h) :
    a.val_index ∈ (Protocol.derive_named E cfg
      (.node p s root votes support rows proposer)).progress := by
  have hstay := namedTransition_eq_afterFin_of_height_eq E cfg
    (Protocol.derive_named E cfg p)
    (.node p s root votes support rows proposer) hh
  rw [Protocol.derive_named, hstay, Protocol.afterFin_progress]
  change a.val_index ∈
    (rows.foldl (Protocol.process_attestation_with
      (Protocol.TimeoutBinding.targeted V))
      {Protocol.derive_named E cfg p with s := s}).progress
  apply named_mem_progress_foldl_of_matching rows _ ha
  rcases hpair with htarget | htimeout
  · simpa [htarget, NamedHeightPair.matchesEntry]
  · simpa [htimeout, NamedHeightPair.matchesEntry]

omit [Fintype V] in
private theorem namedTarget_subset_foldl
    (rows : List (NamedAttestation V)) (sigma : ChainState V) :
    sigma.target_participation ⊆
      (rows.foldl (Protocol.process_attestation_with
        (Protocol.TimeoutBinding.targeted V))
        sigma).target_participation := by
  induction rows generalizing sigma with
  | nil => exact Finset.Subset.refl _
  | cons row rows ih =>
      rw [List.foldl_cons]
      apply Finset.Subset.trans _ (ih _)
      rw [(TargetedTimeoutBinding.process_height_fields sigma row).2]
      split_ifs
      · exact Finset.subset_insert _ _
      · exact Finset.Subset.refl _

omit [Fintype V] in
private theorem namedTarget_mem_foldl {a : NamedAttestation V} :
    ∀ (rows : List (NamedAttestation V)) (sigma : ChainState V),
      a ∈ rows →
      a.height_pair = .vote sigma.h sigma.T_h.root false →
      a.val_index ∈
        (rows.foldl (Protocol.process_attestation_with
          (Protocol.TimeoutBinding.targeted V))
          sigma).target_participation := by
  intro rows
  induction rows with
  | nil => intro sigma ha _; simp at ha
  | cons row rows ih =>
      intro sigma ha hpair
      rw [List.foldl_cons]
      rcases List.mem_cons.mp ha with rfl | htail
      · apply namedTarget_subset_foldl rows
        rw [(TargetedTimeoutBinding.process_height_fields sigma a).2]
        have htest :
            (a.height_pair.matchesEntry sigma.h sigma.T_h.root &&
              a.height_pair.properTarget) = true := by
          rw [hpair]
          simp [NamedHeightPair.matchesEntry,
            NamedHeightPair.properTarget]
        rw [if_pos htest]
        exact Finset.mem_insert_self _ _
      · apply ih _ htail
        have hfields := TimeoutBindingDefaults.process_context_fields
          (Protocol.TimeoutBinding.targeted V) sigma row
        rw [hfields.2.1, hfields.2.2.1]
        exact hpair

private theorem namedTarget_subset_node_of_same_height
    (E : Env V) (cfg : HeightConfig)
    (p : NamedBlock V) (s : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V))
    (rows : List (NamedAttestation V)) (proposer : V)
    (hh : (Protocol.derive_named E cfg
      (.node p s root votes support rows proposer)).h =
        (Protocol.derive_named E cfg p).h) :
    (Protocol.derive_named E cfg p).target_participation ⊆
      (Protocol.derive_named E cfg
        (.node p s root votes support rows proposer)).target_participation := by
  have hstay := namedTransition_eq_afterFin_of_height_eq E cfg
    (Protocol.derive_named E cfg p)
    (.node p s root votes support rows proposer) hh
  rw [Protocol.derive_named, hstay,
    Protocol.afterFin_target_participation]
  change (Protocol.derive_named E cfg p).target_participation ⊆
    (rows.foldl (Protocol.process_attestation_with
      (Protocol.TimeoutBinding.targeted V))
      {Protocol.derive_named E cfg p with s := s}).target_participation
  simpa only using namedTarget_subset_foldl rows
    ({Protocol.derive_named E cfg p with s := s})

private theorem namedTarget_mem_node_of_same_height
    (E : Env V) (cfg : HeightConfig)
    (p : NamedBlock V) (s : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V))
    (rows : List (NamedAttestation V)) (proposer : V)
    {a : NamedAttestation V} (ha : a ∈ rows)
    (hpair : a.height_pair = .vote
      (Protocol.derive_named E cfg p).h
      (Protocol.derive_named E cfg p).T_h.root false)
    (hh : (Protocol.derive_named E cfg
      (.node p s root votes support rows proposer)).h =
        (Protocol.derive_named E cfg p).h) :
    a.val_index ∈ (Protocol.derive_named E cfg
      (.node p s root votes support rows proposer)).target_participation := by
  have hstay := namedTransition_eq_afterFin_of_height_eq E cfg
    (Protocol.derive_named E cfg p)
    (.node p s root votes support rows proposer) hh
  rw [Protocol.derive_named, hstay,
    Protocol.afterFin_target_participation]
  change a.val_index ∈
    (rows.foldl (Protocol.process_attestation_with
      (Protocol.TimeoutBinding.targeted V))
      {Protocol.derive_named E cfg p with s := s}).target_participation
  apply namedTarget_mem_foldl rows _ ha
  simpa only using hpair

private theorem namedPair_mem_progress_of_suffix_same_height
    (E : Env V) (cfg : HeightConfig)
    {C P : NamedBlock V} {a : NamedAttestation V}
    (hCP : NamedBlock.Preceq C P)
    (haP : a ∈ Protocol.named_chain_attestations P)
    (haC : a ∉ Protocol.named_chain_attestations C)
    (hh : (Protocol.derive_named E cfg P).h =
      (Protocol.derive_named E cfg C).h)
    (hpair : a.height_pair = .vote
          (Protocol.derive_named E cfg C).h
          (Protocol.derive_named E cfg C).T_h.root false ∨
        a.height_pair = .vote
          (Protocol.derive_named E cfg C).h
          (Protocol.derive_named E cfg C).T_h.root true) :
    a.val_index ∈ (Protocol.derive_named E cfg P).progress := by
  induction P with
  | genesis =>
      simp [Protocol.named_chain_attestations] at haP
  | node p s root votes support rows proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hCP
      rcases hCP with rfl | hCp
      · exact False.elim (haC haP)
      · have hparentNode : NamedBlock.Preceq p
            (.node p s root votes support rows proposer) :=
          Proofs.NamedAncestry.named_extend s root votes support rows proposer
            (Proofs.NamedAncestry.named_self p)
        have hpHeight : (Protocol.derive_named E cfg p).h =
            (Protocol.derive_named E cfg C).h := by
          apply Nat.le_antisymm
          · exact (Proofs.NamedEntryHeight.derive_height_mono E cfg
              hparentNode).trans_eq hh
          · exact Proofs.NamedEntryHeight.derive_height_mono E cfg hCp
        have hnodeHeight : (Protocol.derive_named E cfg
            (.node p s root votes support rows proposer)).h =
              (Protocol.derive_named E cfg p).h :=
          hh.trans hpHeight.symm
        have htargetEq : (Protocol.derive_named E cfg p).T_h =
            (Protocol.derive_named E cfg C).T_h :=
          (Proofs.NamedEntryHeight.entry_eq_on_plateau
            E cfg hCp hpHeight.symm).symm
        have hpairParent : a.height_pair = .vote
              (Protocol.derive_named E cfg p).h
              (Protocol.derive_named E cfg p).T_h.root false ∨
            a.height_pair = .vote
              (Protocol.derive_named E cfg p).h
              (Protocol.derive_named E cfg p).T_h.root true := by
          simpa only [hpHeight, htargetEq] using hpair
        simp only [Protocol.named_chain_attestations,
          Finset.mem_union] at haP
        rcases haP with haParent | haOwn
        · exact namedProgress_subset_node_of_same_height
            E cfg p s root votes support rows proposer hnodeHeight
              (ih hCp haParent hpHeight)
        · exact namedPair_mem_progress_node_of_same_height
            E cfg p s root votes support rows proposer
              (List.mem_toFinset.mp haOwn) hpairParent hnodeHeight

private theorem namedTarget_mem_of_suffix_same_height
    (E : Env V) (cfg : HeightConfig)
    {C P : NamedBlock V} {a : NamedAttestation V}
    (hCP : NamedBlock.Preceq C P)
    (haP : a ∈ Protocol.named_chain_attestations P)
    (haC : a ∉ Protocol.named_chain_attestations C)
    (hh : (Protocol.derive_named E cfg P).h =
      (Protocol.derive_named E cfg C).h)
    (hpair : a.height_pair = .vote
      (Protocol.derive_named E cfg C).h
      (Protocol.derive_named E cfg C).T_h.root false) :
    a.val_index ∈
      (Protocol.derive_named E cfg P).target_participation := by
  induction P with
  | genesis =>
      simp [Protocol.named_chain_attestations] at haP
  | node p s root votes support rows proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hCP
      rcases hCP with rfl | hCp
      · exact False.elim (haC haP)
      · have hparentNode : NamedBlock.Preceq p
            (.node p s root votes support rows proposer) :=
          Proofs.NamedAncestry.named_extend s root votes support rows proposer
            (Proofs.NamedAncestry.named_self p)
        have hpHeight : (Protocol.derive_named E cfg p).h =
            (Protocol.derive_named E cfg C).h := by
          apply Nat.le_antisymm
          · exact (Proofs.NamedEntryHeight.derive_height_mono E cfg
              hparentNode).trans_eq hh
          · exact Proofs.NamedEntryHeight.derive_height_mono E cfg hCp
        have hnodeHeight : (Protocol.derive_named E cfg
            (.node p s root votes support rows proposer)).h =
              (Protocol.derive_named E cfg p).h :=
          hh.trans hpHeight.symm
        have htargetEq : (Protocol.derive_named E cfg p).T_h =
            (Protocol.derive_named E cfg C).T_h :=
          (Proofs.NamedEntryHeight.entry_eq_on_plateau
            E cfg hCp hpHeight.symm).symm
        have hpairParent : a.height_pair = .vote
            (Protocol.derive_named E cfg p).h
            (Protocol.derive_named E cfg p).T_h.root false := by
          simpa only [hpHeight, htargetEq] using hpair
        simp only [Protocol.named_chain_attestations,
          Finset.mem_union] at haP
        rcases haP with haParent | haOwn
        · exact namedTarget_subset_node_of_same_height
            E cfg p s root votes support rows proposer hnodeHeight
              (ih hCp haParent hpHeight)
        · exact namedTarget_mem_node_of_same_height
            E cfg p s root votes support rows proposer
              (List.mem_toFinset.mp haOwn) hpairParent hnodeHeight

omit [Fintype V] in
private theorem chainRows_iff_named_chain
    {B : NamedBlock V} {a : NamedAttestation V} :
    a ∈ Protocol.NamedProposalRows.chainRows B ↔
      a ∈ Protocol.named_chain_attestations B := by
  induction B with
  | genesis =>
      simp [Protocol.NamedProposalRows.chainRows,
        Protocol.named_chain_attestations]
  | node p s root votes support rows proposer ih =>
      simp only [Protocol.NamedProposalRows.chainRows,
        Protocol.named_chain_attestations, List.mem_append,
        Finset.mem_union, List.mem_toFinset, ih, or_comm]

omit [Fintype V] in
private theorem namedChain_row_ancestor
    {B : NamedBlock V} {a : NamedAttestation V}
    (ha : a ∈ Protocol.named_chain_attestations B) :
    ∃ A : NamedBlock V, NamedBlock.Preceq A B ∧ a ∈ A.attestations := by
  induction B with
  | genesis => simp [Protocol.named_chain_attestations] at ha
  | node p s root votes support rows proposer ih =>
      simp only [Protocol.named_chain_attestations,
        Finset.mem_union] at ha
      rcases ha with haParent | haOwn
      · obtain ⟨A, hA, hrow⟩ := ih haParent
        exact ⟨A, Proofs.NamedAncestry.named_extend
          s root votes support rows proposer hA, hrow⟩
      · exact ⟨.node p s root votes support rows proposer,
          Proofs.NamedAncestry.named_self _, List.mem_toFinset.mp haOwn⟩

omit [Fintype V] in
private theorem namedAncestor_body_mem
    {st : Protocol.NamedStore V} (hpc : NamedStore.NamedParentClosed st)
    {A B : NamedBlock V} (hB : B ∈ st.bodies)
    (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  induction B with
  | genesis =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq,
        decide_eq_true_eq] at hAB
      exact hAB ▸ hB
  | node parent s root votes support rows proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hparent
      · exact hB
      · exact ih (hpc.2 _ hB) hparent

private theorem emittedAttestation_not_mem_named_chain_before
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {i : V} {a : NamedAttestation V} {t : Time} {C : NamedBlock V}
    (hi : i ∈ rho.honest)
    (hemit : rho.emits S i (Object.attest a) t)
    (hC : C ∈ (rho.stateBeforeTime S t i).st.bodies) :
    a ∉ Protocol.named_chain_attestations C := by
  intro haC
  have haHon : a.val_index ∈ rho.honest := by
    rw [(Proofs.Optimistic.emits_attest_shape S hemit).1]
    exact hi
  obtain ⟨A, hAC, hrow⟩ := namedChain_row_ancestor haC
  obtain ⟨n, hn, hbound⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed t
  have hni : rho.stateBeforeTime S t i = rho.stateBefore S n i :=
    congrFun hn i
  have hCbefore : C ∈ (rho.stateBefore S n i).st.bodies := by
    rw [← hni]
    exact hC
  have hpc : NamedStore.NamedParentClosed (rho.stateBefore S n i).st :=
    (Proofs.NamedRuntime.stateBefore_invariants S rho n i).1.1.1.2.2.1
  have hAbefore := namedAncestor_body_mem hpc hCbefore hAC
  rcases Proofs.Bridges.processes_block_of_mem_T S rho i n A hAbefore with
    hgen | ⟨j, e, hj, hje, hproc⟩
  · subst A
    simpa [NamedBlock.attestations] using hrow
  · obtain ⟨hle, -⟩ :=
      Proofs.Bridges.carriedArePastEmissions_of_admissibleCore
        S adm.toNamedAdmissibleCore hproc hrow haHon
    have htime : S.a a.round < t := hle.trans_lt (hbound j e hj hje)
    have htEq : t = S.a a.round :=
      (Proofs.Optimistic.emits_attest_shape S hemit).2
    rw [← htEq] at htime
    exact lt_irrefl t htime

private theorem exactRow_mem_namedProcessed
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} {a : NamedAttestation V}
    (haHon : a.val_index ∈ rho.honest)
    (hemit : rho.emits S a.val_index (Object.attest a) (S.a a.round))
    (hprocessed : a.erase ∈
      (Protocol.proposerDutyStore S rho s).processed_attestations S.hc) :
    a ∈ Protocol.NamedProposalRows.processedRows S.hc
      (proposerReadAt S rho s).st := by
  let st := (proposerReadAt S rho s).st
  have hPool : NamedStore.PoolView st := by
    simpa only [st, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using
        (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
          (Protocol.proposal_time S.E s)
          (S.E.proposer s)).1.1.1.2.2.2.1
  have hmap := NamedProposalRows.processed_rows_erasure S.hc st hPool
  have hmemMap : a.erase ∈
      (Protocol.NamedProposalRows.processedRows S.hc st).map
        NamedAttestation.erase := by
    rw [hmap]
    simpa only [st, Protocol.proposerDutyStore, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using
        hprocessed
  obtain ⟨b, hb, hberase⟩ := List.mem_map.mp hmemMap
  have hbFlat := hb
  rw [Protocol.NamedProposalRows.processedRows] at hbFlat
  obtain ⟨k, -, hbk⟩ := List.mem_flatMap.mp hbFlat
  have hrounds : Proofs.NamedStoreBridge.SgRowRounds st := by
    simpa only [st, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using
        Proofs.NamedStoreBridge.sgRowRounds_stateBeforeTime S rho
          (Protocol.proposal_time S.E s) (S.E.proposer s)
  have hbr : b.round = k := hrounds k b hbk
  have hbOwn : b ∈ st.sg_rows b.round := by
    rw [hbr]
    exact hbk
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (Protocol.proposal_time S.E s)
  have hbN : b ∈
      (rho.stateBefore S n (S.E.proposer s)).st.sg_rows b.round := by
    rw [← congrFun hn (S.E.proposer s)]
    simpa only [st, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hbOwn
  have hbval : b.val_index = a.val_index :=
    congrArg CombinedAttestation.val_index hberase
  have hbHon : b.val_index ∈ rho.honest := by
    rw [hbval]
    exact haHon
  obtain ⟨_, _, _, _, _, hbEmit⟩ :=
    Proofs.Bridges.heldArePastEmissions_of_admissibleCore
      S adm.toNamedAdmissibleCore n (S.E.proposer s) hbN hbHon
  have hbEmit' : rho.emits S a.val_index
      (Object.attest b) (S.a b.round) := by
    simpa only [hbval] using hbEmit
  have hround : b.round = a.round :=
    congrArg CombinedAttestation.round hberase
  have hba : b = a := Proofs.Optimistic.emits_attest_unique S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
    hbEmit' hemit hround
  simpa only [st, hba] using hb

/-- Every exact named honest action row is present in the actual named proposal.
If the selected parent already carries the row, the row is live in the parent's
fixed-height state. Otherwise, F2 carries the exact row in the child. -/
theorem actionAttestationAt_coveredAtProposal
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {C : NamedBlock V} {H : Height} {T : BlockId}
    (hforms : NamedGradeFormsAt S rho r C.erase)
    (hCrun : RunBlock S rho C)
    (hCheight : (Protocol.derive_named S.E S.cfg C).h = H)
    (hCtarget : (Protocol.derive_named S.E S.cfg C).T_h.root = T)
    {s : Slot} {B : NamedBlock V}
    (hB : proposedBlockAt S rho s = some B)
    (hCP : NamedBlock.Preceq C B.parent)
    (hPheight :
      (Protocol.derive_named S.E S.cfg B.parent).h = H)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E s ≤ rho.horizon)
    (hpost : S.E.t_GST ≤ S.a r)
    (hdelay : S.a r + S.E.Δ ≤ Protocol.proposal_time S.E s)
    {v : V} (hv : v ∈ rho.honest)
    (hwindow :
      FinalityFilterRetainedAtRead S rho v (S.a r) C.erase)
    (hinWindow : Protocol.ProposalRows.inWindow S.hc
      (proposerReadAt S rho s).st.core r = true)
    (hpair : (actionAttestationAt S rho v r).height_pair =
        .vote H T false ∨
      (actionAttestationAt S rho v r).height_pair = .vote H T true) :
    ((actionAttestationAt S rho v r ∈
          Protocol.named_chain_attestations B.parent ∧
        v ∈ (Protocol.derive_named S.E S.cfg B.parent).progress ∧
        ((actionAttestationAt S rho v r).height_pair = .vote H T false →
          v ∈ (Protocol.derive_named S.E S.cfg
            B.parent).target_participation)) ∨
      actionAttestationAt S rho v r ∈ B.attestations) := by
  let a := actionAttestationAt S rho v r
  have hactionHor : S.a r ≤ rho.horizon :=
    (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
      (hdelay.trans hhor)
  have hemitV : rho.emits S v (Object.attest a) (S.a r) := by
    simpa only [a] using
      honest_emits_exact_actionAttestationAt S adm hv r hactionHor (by assumption)
  have haVal : a.val_index = v :=
    (Proofs.Optimistic.emits_attest_shape S hemitV).1
  have haRound : a.round = r :=
    (actionAttestationAt_shape S rho v r).2.1
  have hemit : rho.emits S a.val_index
      (Object.attest a) (S.a a.round) := by
    simpa only [haVal, haRound] using hemitV
  have hemitAtR : rho.emits S a.val_index
      (Object.attest a) (S.a r) := by
    simpa only [haVal] using hemitV
  have hactive : C.erase ∈ PhaseGrades.filteredTree
      (actionReadAt S rho v r) :=
    namedGradeFormsAt_actionStore_of_window S hforms hv hwindow
  have hCcore : C.erase ∈
      (actionStoreAt S rho v r).st.core.T :=
    Proofs.Records.get_filtered_block_tree_subset _ hactive
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (actionStoreAt S rho v r).st := by
    apply Proofs.NamedConfirmationMembership.invariant_update
    exact Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _
      (S.a r) (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a r) v).1
  have hcoh := hinv.1.1
  have hCimage := hCcore
  rw [hcoh.1] at hCimage
  obtain ⟨C', hC', hCerase⟩ := Finset.mem_image.mp hCimage
  have hC'run : RunBlock S rho C' :=
    actionBody_runBlock_coverage S adm hv hC'
  have hC'eq : C' = C :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      C' C hC'run hCrun C' C
        (Or.inl (Proofs.NamedAncestry.named_self C'))
        (Or.inr (Proofs.NamedAncestry.named_self C)) (by
          rw [← Proofs.NamedWire.erase_root C', ← Proofs.NamedWire.erase_root C,
            hCerase])
  have hCbody : C ∈ (actionStoreAt S rho v r).st.bodies := by
    rw [← hC'eq]
    exact hC'
  have hCpre : C ∈
      (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hCbody
  have hnotC := emittedAttestation_not_mem_named_chain_before
    S adm hv hemitV hCpre
  have hprocessed := honestAttestation_mem_processedAtProposal_after_gst
    S adm hprop hhor (by simpa only [haVal] using hv)
      hemitAtR hpost hdelay
  have haProcessed := exactRow_mem_namedProcessed
    S adm (by simpa only [haVal] using hv) hemit hprocessed
  have haSelected : a ∈
      Protocol.NamedProposalRows.select .poolAndCarried S.hc
        (proposerReadAt S rho s).st := by
    apply List.mem_append_left
    simp only [Protocol.NamedProposalRows.poolRows, List.mem_filter]
    exact ⟨haProcessed, by simpa only [haRound] using hinWindow⟩
  have hpay := Proofs.NamedActions.proposal_payload
    (NamedProfile.gradeContract (proposerReadAt S rho s).cache)
    .poolAndCarried S.E S.hc (S.node (S.E.proposer s))
    (proposerReadAt S rho s).st B hB
  by_cases hchain : a ∈ Protocol.NamedProposalRows.chainRows B.parent
  · left
    have hchain' := chainRows_iff_named_chain.mp hchain
    refine ⟨hchain', ?_, ?_⟩
    · rw [← haVal]
      apply namedPair_mem_progress_of_suffix_same_height
        S.E S.cfg hCP hchain' hnotC
      · rw [hPheight, hCheight]
      · simpa only [a, hCheight, hCtarget] using hpair
    · intro htarget
      rw [← haVal]
      apply namedTarget_mem_of_suffix_same_height
        S.E S.cfg hCP hchain' hnotC
      · rw [hPheight, hCheight]
      · simpa only [a, hCheight, hCtarget] using htarget
  · right
    rw [hpay.2.2.2.2.2.2.1]
    apply NamedProposalRows.mem_proposalRows_of_unique B.parent _ a haSelected hchain
    intro b hb hval hround
    exact honest_selected_row_unique S adm s haSelected hb
      (by simpa only [haVal] using hv) hval hround

/-- **The on-chain half of row coverage, without the proposer's row window.**

`actionAttestationAt_coveredAtProposal` asks for `NamedGradeFormsAt` at the
row's own round and for the row to fall inside the proposer's selection window.
Both are there to cover the case where the proposer includes the row FRESHLY.
When the row is already on the selected parent's chain neither is needed: the
reader only has to hold the named block the row names, and the two suffix
lemmas do the rest.

This is the shape the gate-off seed's `M - 1` promotion consumes. There the
row is carried across more rounds than `η_SG`, so `Protocol.ProposalRows.inWindow`
can never hold and a fresh inclusion is impossible; the row travels on the
chain instead. -/
theorem actionAttestationAt_coveredAtProposal_of_chainRows
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {C : NamedBlock V} {H : Height} {T : BlockId}
    (hCrun : RunBlock S rho C)
    (hCheight : (Protocol.derive_named S.E S.cfg C).h = H)
    (hCtarget : (Protocol.derive_named S.E S.cfg C).T_h.root = T)
    {B : NamedBlock V}
    (hCP : NamedBlock.Preceq C B.parent)
    (hPheight : (Protocol.derive_named S.E S.cfg B.parent).h = H)
    (hactionHor : S.a r ≤ rho.horizon)
    (hpost : S.E.t_GST ≤ S.a r)
    {v : V} (hv : v ∈ rho.honest)
    (hCcore : C.erase ∈ (actionStoreAt S rho v r).st.core.T)
    (hchain : actionAttestationAt S rho v r ∈
      Protocol.NamedProposalRows.chainRows B.parent)
    (hpair : (actionAttestationAt S rho v r).height_pair = .vote H T false ∨
      (actionAttestationAt S rho v r).height_pair = .vote H T true) :
    ((actionAttestationAt S rho v r ∈
          Protocol.named_chain_attestations B.parent ∧
        v ∈ (Protocol.derive_named S.E S.cfg B.parent).progress ∧
        ((actionAttestationAt S rho v r).height_pair = .vote H T false →
          v ∈ (Protocol.derive_named S.E S.cfg
            B.parent).target_participation)) ∨
      actionAttestationAt S rho v r ∈ B.attestations) := by
  let a := actionAttestationAt S rho v r
  have hemitV : rho.emits S v (Object.attest a) (S.a r) := by
    simpa only [a] using
      honest_emits_exact_actionAttestationAt S adm hv r hactionHor hpost
  have haVal : a.val_index = v :=
    (Proofs.Optimistic.emits_attest_shape S hemitV).1
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (actionStoreAt S rho v r).st := by
    apply Proofs.NamedConfirmationMembership.invariant_update
    exact Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _
      (S.a r) (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a r) v).1
  have hcoh := hinv.1.1
  have hCimage := hCcore
  rw [hcoh.1] at hCimage
  obtain ⟨C', hC', hCerase⟩ := Finset.mem_image.mp hCimage
  have hC'run : RunBlock S rho C' :=
    actionBody_runBlock_coverage S adm hv hC'
  have hC'eq : C' = C :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      C' C hC'run hCrun C' C
        (Or.inl (Proofs.NamedAncestry.named_self C'))
        (Or.inr (Proofs.NamedAncestry.named_self C)) (by
          rw [← Proofs.NamedWire.erase_root C', ← Proofs.NamedWire.erase_root C,
            hCerase])
  have hCbody : C ∈ (actionStoreAt S rho v r).st.bodies := by
    rw [← hC'eq]
    exact hC'
  have hCpre : C ∈
      (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hCbody
  have hnotC := emittedAttestation_not_mem_named_chain_before
    S adm hv hemitV hCpre
  left
  have hchain' := chainRows_iff_named_chain.mp hchain
  refine ⟨hchain', ?_, ?_⟩
  · rw [← haVal]
    apply namedPair_mem_progress_of_suffix_same_height
      S.E S.cfg hCP hchain' hnotC
    · rw [hPheight, hCheight]
    · simpa only [a, hCheight, hCtarget] using hpair
  · intro htarget
    rw [← haVal]
    apply namedTarget_mem_of_suffix_same_height
      S.E S.cfg hCP hchain' hnotC
    · rw [hPheight, hCheight]
    · simpa only [a, hCheight, hCtarget] using htarget

#print axioms named_proposedBlock_height_eq_succ_of_actionCoverage
#print axioms actionAttestationAt_pair_or_hMaxRise
#print axioms actionAttestationAt_coveredAtProposal
#print axioms actionAttestationAt_coveredAtProposal_of_chainRows






/-
/-- The exact action row reaches the processed list of a later honest proposal
after one full post-GST delay. -/
theorem actionAttestationAt_mem_processedAtProposal_after_gst
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {r: Round} {v: V} (hv: v ∈ rho.honest)
    {s: Slot} (hprop: S.E.proposer s ∈ rho.honest)
    (hhor: Protocol.proposal_time S.E s ≤ rho.horizon)
    (hpost: S.E.t_GST ≤ S.a r)
    (hdelay: S.a r + S.E.Δ ≤ Protocol.proposal_time S.E s):
    let duty:= Protocol.proposerDutyStore S rho s
    actionAttestationAt S rho v r ∈ duty.processed_attestations S.hc:= by
  let a:= actionAttestationAt S rho v r
  let p:= S.E.proposer s
  let tp:= Protocol.proposal_time S.E s
  have hactionHor: S.a r ≤ rho.horizon:= by
    exact (le_trans
      (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)) hdelay).trans hhor
  have hemit: rho.emits S v (Object.attest a) (S.a r):= by
    simpa only [a] using
      honest_emits_exact_actionAttestationAt S adm hv r hactionHor (by assumption)
  have hlt: S.a r < tp:= by
    exact lt_of_lt_of_le (Int.lt_add_of_pos_right _ S.E.Δ_pos)
      (by simpa only [tp] using hdelay)
  obtain ⟨i, hi, hselfPool⟩:=
    Protocol.attest_pooled_of_emission_exact S adm hv hemit
  have hselfProcessed: (Object.attest a).processed
      (rho.stateBefore S (i + 1) v).st = true:= by
    simpa only [Object.processed, decide_eq_true_eq] using hselfPool
  obtain ⟨j, hj, ta, hacc⟩:=
    Protocol.acceptsAt_attest_of_processed
      S rho v (i + 1) a hselfProcessed
  have haccProcess: rho.processes S v (Object.attest a) ta:=
    Protocol.processes_of_acceptsAt_attest S hacc
  have haVal: a.val_index = v:= (Proofs.Optimistic.emits_attest_shape S hemit).1
  have haHon: a.val_index ∈ rho.honest:= by rw [haVal]; exact hv
  obtain ⟨te, hte, hemite⟩:=
    adm.unforgeable v (Object.attest a) ta haccProcess
      a.val_index haHon rfl
  rw [haVal] at hemite
  have hteq: te = S.a r:= by
    obtain ⟨-, hteShape⟩:= Proofs.Optimistic.emits_attest_shape S hemite
    obtain ⟨-, htShape⟩:= Proofs.Optimistic.emits_attest_shape S hemit
    rw [hteShape, htShape]
  have htTa: S.a r ≤ ta:= by simpa only [hteq] using hte
  obtain ⟨-, e, he, -, heta⟩:= hacc.1
  have htaT: ta ≤ S.a r:= by
    have hji: j ≤ i:= Nat.lt_succ_iff.mp hj
    rcases lt_or_eq_of_le hji with hji | rfl
    · have hkey:= Proofs.Optimistic.key_le_of_index_lt S adm.toScheduleWellFormed
        hji he hi
      calc
        ta = e.time:= heta.symm
        _ ≤ (Event.tick v (S.a r)).time:= Proofs.Bridges.time_le_of_key_le hkey
        _ ≤ S.a r:= by simp [Event.time]
    · have heq: e = Event.tick v (S.a r):=
        Option.some.inj (he.symm.trans hi)
      calc
        ta = e.time:= heta.symm
        _ ≤ S.a r:= by rw [heq]; simp [Event.time]
  have hta: ta = S.a r:= le_antisymm htaT htTa
  have hpHon: p ∈ rho.honest:= by simpa only [p] using hprop
  have carryToProposal: ∀ {q: Nat} {ev: Event V},
      rho.events[q]? = some ev → ev.time < tp →
        a ∈ (rho.stateBefore S (q + 1) p).st.sg_pool a.round →
          a ∈ (rho.stateBeforeTime S tp p).st.sg_pool a.round:= by
    intro q ev hq hqt ha
    exact Protocol.attest_mem_stateBeforeTime_of_post
      S adm.toScheduleWellFormed hq hqt ha
  have haRead: a ∈ (rho.stateBeforeTime S tp p).st.sg_pool a.round:= by
    by_cases hsame: p = v
    · have hreadSelf:= Protocol.attest_mem_stateBeforeTime_of_post S
        adm.toScheduleWellFormed hi (by simpa only [tp] using hlt) hselfPool
      simpa only [hsame] using hreadSelf
    · by_cases halready: (Object.attest a).processed
          (rho.stateBefore S (j + 1) p).st = true
      · have ha: a ∈ (rho.stateBefore S (j + 1) p).st.sg_pool a.round:= by
          simpa only [Object.processed, decide_eq_true_eq] using halready
        exact carryToProposal he (by
          rw [heta, hta]
          simpa only [tp] using hlt) ha
      · have hunaccepted: (Object.attest a).processed
            (rho.stateBefore S (j + 1) p).st = false:=
          Bool.eq_false_of_not_eq_true halready
        have hrelayHorizon: ta + S.E.Δ ≤ rho.horizon:= by
          rw [hta]
          exact hdelay.trans hhor
        obtain ⟨td, htaTd, htd, hproc⟩:=
          Protocol.relay_attest_after_gst S adm hv hpHon
            (by simpa only [hta] using hpost) hacc hunaccepted hrelayHorizon
        rcases hproc with htargetEmit | ⟨d, hd⟩
        · have htargetVal:= (Proofs.Optimistic.emits_attest_shape S htargetEmit).1
          have hsourceVal:= (Proofs.Optimistic.emits_attest_shape S hemit).1
          exact absurd (htargetVal.symm.trans hsourceVal) hsame
        · have htShape:= (Proofs.Optimistic.emits_attest_shape S hemit).2
          have hlo: S.a a.round ≤ td:= by
            change S.hc.a S.E.Δ a.round ≤ td
            rw [← htShape, ← hta]
            exact htaTd
          have hhi: td < S.a a.round + S.E.Δ:= by
            change td < S.hc.a S.E.Δ a.round + S.E.Δ
            rw [← htShape, ← hta]
            exact htd
          have hpool:= Proofs.HealingLemmas.attest_pooled_of_delivery
            S adm hpHon hd haHon
              ⟨S.a r, by simpa only [haVal] using hemit⟩ hlo hhi
          exact carryToProposal hd
            (lt_of_lt_of_le htd (by
              rw [hta]
              simpa only [tp] using hdelay)) hpool
  let duty:= Protocol.proposerDutyStore S rho s
  have haDuty: a ∈ duty.sg_pool a.round:= by
    simpa only [duty, Protocol.proposerDutyStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime, tp, p] using haRead
  have hround: a.round ≤ S.hc.round_of duty.s:= by
    have hltAction: S.a a.round < Protocol.proposal_time S.E s:= by
      change S.hc.a S.E.Δ a.round < Protocol.proposal_time S.E s
      rw [← (Proofs.Optimistic.emits_attest_shape S hemit).2]
      simpa only [tp] using hlt
    have hr:= Protocol.action_round_le_of_lt_proposal S
      (r:= a.round) (s:= s) hltAction
    simpa only [duty, Protocol.proposerDutyStore,
      Proofs.Optimistic.tickStore, Proofs.Optimistic.slotOf_proposal_time] using hr
  simpa only [a] using
    (Protocol.mem_processed_attestations_of_pool S.hc duty haDuty hround)

/-- The exact action row is in the proposal's resolved input when the graded
prefix is still active at the proposal duty. -/
theorem actionAttestationAt_mem_resolvedAtProposal_after_gst
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {r: Round} {C: Block V} (hforms: GradeFormsAt S rho r C)
    {v: V} (hv: v ∈ rho.honest)
    {s: Slot} (hprop: S.E.proposer s ∈ rho.honest)
    (hhor: Protocol.proposal_time S.E s ≤ rho.horizon)
    (hpost: S.E.t_GST ≤ S.a r)
    (hdelay: S.a r + S.E.Δ ≤ Protocol.proposal_time S.E s)
    (hactive: C ∈ Protocol.get_filtered_block_tree
      (Protocol.proposerDutyStore S rho s).toHealing.toFG):
    let duty:= Protocol.proposerDutyStore S rho s
    actionAttestationAt S rho v r ∈ duty.resolved_attestations S.hc:= by
  let duty:= Protocol.proposerDutyStore S rho s
  unfold Protocol.Store.resolved_attestations
  simp only [List.mem_filter]
  refine ⟨actionAttestationAt_mem_processedAtProposal_after_gst
      S adm hv hprop hhor hpost hdelay, ?_⟩
  simpa only [duty] using
    (actionAttestationAt_resolvedAtProposal_of_gradeFormsAt
      S adm hforms hv hprop hhor hpost hdelay hactive)

/-- The exact action row is in the proposal's resolved input when its SG
carrier is already in the proposer's strict pre-proposal store. -/
theorem actionAttestationAt_mem_resolvedAtProposal_after_gst_of_memProposerStore
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {r: Round} {v: V} (hv: v ∈ rho.honest)
    {s: Slot} (hprop: S.E.proposer s ∈ rho.honest)
    (hhor: Protocol.proposal_time S.E s ≤ rho.horizon)
    (hpost: S.E.t_GST ≤ S.a r)
    (hdelay: S.a r + S.E.Δ ≤ Protocol.proposal_time S.E s)
    (hSGpre: actionSGBlockAt S rho v r ∈
      (rho.storeBeforeTime S (S.E.proposer s)
        (Protocol.proposal_time S.E s)).T):
    let duty:= Protocol.proposerDutyStore S rho s
    actionAttestationAt S rho v r ∈ duty.resolved_attestations S.hc:= by
  let duty:= Protocol.proposerDutyStore S rho s
  unfold Protocol.Store.resolved_attestations
  simp only [List.mem_filter]
  refine ⟨actionAttestationAt_mem_processedAtProposal_after_gst
      S adm hv hprop hhor hpost hdelay, ?_⟩
  simpa only [duty] using
    (actionAttestationAt_resolvedAtProposal_of_memProposerStore_core
      S adm hv hprop hSGpre)

/-- An active common-grade floor puts the exact action row in the proposal's
resolved input. If the floor is strictly below the later FG root, this theorem
keeps that alternative. -/
theorem actionAttestationAt_mem_resolvedAtProposal_after_gst_or_prec_root
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {r: Round} {C: Block V} (hforms: GradeFormsAt S rho r C)
    {v: V} (hv: v ∈ rho.honest)
    {s: Slot} (hprop: S.E.proposer s ∈ rho.honest)
    (hhor: Protocol.proposal_time S.E s ≤ rho.horizon)
    (hpost: S.E.t_GST ≤ S.a r)
    (hdelay: S.a r + S.E.Δ ≤ Protocol.proposal_time S.E s)
    (hactiveOr:
      C ∈ Protocol.get_filtered_block_tree
          (Protocol.proposerDutyStore S rho s).toHealing.toFG ∨
        Block.Prec C
          (Protocol.get_fg_root
            (rho.storeBeforeTime S (S.E.proposer s)
              (Protocol.proposal_time S.E s)).toHealing.toFG)):
    (let duty:= Protocol.proposerDutyStore S rho s
     actionAttestationAt S rho v r ∈ duty.resolved_attestations S.hc) ∨
      Block.Prec C
        (Protocol.get_fg_root
          (rho.storeBeforeTime S (S.E.proposer s)
            (Protocol.proposal_time S.E s)).toHealing.toFG):= by
  rcases
      actionAttestationAt_resolvedAtProposal_of_gradeFormsAt_or_prec_root
        S adm hforms hv hprop hhor hpost hdelay hactiveOr with
    hresolved | hprec
  · left
    let duty:= Protocol.proposerDutyStore S rho s
    unfold Protocol.Store.resolved_attestations
    simp only [List.mem_filter]
    refine ⟨actionAttestationAt_mem_processedAtProposal_after_gst
        S adm hv hprop hhor hpost hdelay, ?_⟩
    simpa only [duty] using hresolved
  · exact Or.inr hprec

private theorem proposedParent_mem_filtered
    (S: Setup V) {rho: Run V} (adm: Admissible S rho) (s: Slot):
    Protocol.proposedParent S rho s ∈
      Protocol.get_filtered_block_tree
        (Protocol.proposerDutyStore S rho s).toHealing.toFG:= by
  let p:= S.E.proposer s
  let t:= Protocol.proposal_time S.E s
  let pre:= rho.storeBeforeTime S p t
  let duty:= Protocol.proposerDutyStore S rho s
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node p) pre:= by
    simpa only [pre, p, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed t p)
  have hrootPre:= fgRoot_mem_filtered_depReachable
    S.E S.hc S.cfg (S.node p) hdep
  have hrootDuty: Protocol.get_fg_root duty.toHealing.toFG ∈
      Protocol.get_filtered_block_tree duty.toHealing.toFG:= by
    simpa only [duty, Protocol.proposerDutyStore,
      Proofs.Optimistic.tickStore, pre, t, p] using hrootPre
  let votes:= Protocol.proposer_view duty.toHealing.toFG.toSG.toGoldfishStore duty.s
  let support:= Protocol.proposer_support_view duty.toHealing.toFG.toSG.toGoldfishStore duty.s
  have hhead:= getHead_mem_filtered_of_fgRoot_mem
    S.E S.hc duty.toHealing votes.toFinset support.toFinset
      (duty.s - 1) hrootDuty
  simpa only [Protocol.proposedParent, duty, votes, support] using hhead

/-- A prefix of the exact proposal parent is either active or below the exact
finality-gadget root used by that proposal. -/
theorem prefix_mem_filtered_or_preceq_proposalFGRoot
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {s: Slot} {C P: Block V}
    (hparent: Protocol.proposedParent S rho s = P)
    (hCP: Block.Preceq C P):
    C ∈ Protocol.get_filtered_block_tree
        (Protocol.proposerDutyStore S rho s).toHealing.toFG ∨
      Block.Preceq C (Protocol.get_fg_root
        (Protocol.proposerDutyStore S rho s).toHealing.toFG):= by
  let p:= S.E.proposer s
  let t:= Protocol.proposal_time S.E s
  let pre:= rho.storeBeforeTime S p t
  let duty:= Protocol.proposerDutyStore S rho s
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node p) pre:= by
    simpa only [pre, p, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed t p)
  have hpcPre: ParentClosed pre:=
    parentClosed_depReachable S.E S.hc S.cfg (S.node p) pre hdep
  have hpcDuty: ParentClosed duty:= by
    apply parentClosed_of_T_eq (st:= pre)
    · simp only [duty, Protocol.proposerDutyStore,
        Proofs.Optimistic.tickStore, pre, t, p]
    · exact hpcPre
  have hPactive: P ∈ Protocol.get_filtered_block_tree duty.toHealing.toFG:= by
    rw [← hparent]
    simpa only [duty] using proposedParent_mem_filtered S adm s
  have hPmem: P ∈ duty.T:=
    Proofs.Records.get_filtered_block_tree_subset duty.toHealing.toFG hPactive
  have hCmem: C ∈ duty.T:=
    Proofs.Records.mem_of_preceq ((parentClosed_iff duty).mp hpcDuty).2 C P hPmem hCP
  have hreach:= Proofs.Bridges.reachableStore_of_depReachableStore
    S.E S.hc S.cfg (S.node p) hdep
  have hFJpre: Block.Preceq pre.F pre.J:=
    finalizedPrecedesJustifiedInvariant S.E S.hc S.cfg (S.node p) pre hreach
  have hFJ: Block.Preceq duty.F duty.J:= by
    simpa only [duty, Protocol.proposerDutyStore,
      Proofs.Optimistic.tickStore, pre, t, p] using hFJpre
  by_cases hrootC: Block.Preceq
      (Protocol.get_fg_root duty.toHealing.toFG) C
  · exact Or.inl (Proofs.Records.mem_filtered_of_preceq
      hFJ hPactive hCmem hCP hrootC)
  · right
    have hrootP: Block.Preceq
        (Protocol.get_fg_root duty.toHealing.toFG) P:=
      Proofs.Records.preceq_get_fg_root_of_mem_filtered hPactive
    have hcompat:= Block.compatible_of_preceq_common hCP hrootP
    simp only [Block.compatible, Bool.or_eq_true] at hcompat
    rcases hcompat with hCroot | hrootC'
    · exact hCroot
    · exact False.elim (hrootC hrootC')

private theorem emittedAttestation_not_mem_chain_of_prefix_held_before
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {i: V} {a: CombinedAttestation V} {t: Time} {C: Block V}
    (hi: i ∈ rho.honest)
    (hemit: rho.emits S i (Object.attest a) t)
    (hC: C ∈ (rho.stateBeforeTime S t i).st.T):
    a ∉ chain_attestations C:= by
  intro haC
  have haHon: a.val_index ∈ rho.honest:= by
    rw [(Proofs.Optimistic.emits_attest_shape S hemit).1]
    exact hi
  obtain ⟨t', ht', hemit'⟩:=
    Proofs.Bridges.carriedArePastEmissions_of_admissible
      S adm t i hC a haC haHon
  have htEq: t' = t:= by
    rw [(Proofs.Optimistic.emits_attest_shape S hemit').2,
      (Proofs.Optimistic.emits_attest_shape S hemit).2]
  exact (ne_of_lt ht') htEq

-/



/-- A later named opening proposal satisfies Rule A when its parent extends an
earlier named opening proposal at the same derived height. -/
theorem laterOpening_timeoutMature_of_sameHeight
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hdelay : TimeoutDelayBound S delayExtra)
    {entry proposal : Round}
    (hentry : 0 < entry)
    (hspace : entry + 2 + delayExtra ≤ proposal)
    {B P Q : NamedBlock V}
    (hB : proposedBlockAt S rho (S.hc.opening_slot entry) = some B)
    (hQ : proposedBlockAt S rho (S.hc.opening_slot proposal) = some Q)
    (hparent : NamedBlock.parent? Q = some P)
    (hpreceq : NamedBlock.Preceq B P)
    (hsameHeight : (Protocol.derive_named S.E S.cfg P).h =
      (Protocol.derive_named S.E S.cfg B).h) :
    ProposalTimeoutMatureAt S rho (S.hc.opening_slot proposal) := by
  intro Q' hQ' P' hP'
  have hQQ' : Q' = Q := Option.some.inj (hQ'.symm.trans hQ)
  subst Q'
  have hPP' : P' = P := Option.some.inj (hP'.symm.trans hparent)
  subst P'
  obtain ⟨parent, hparentQ, hparentErase⟩ :=
    proposedBlockAt_parent S rho (S.hc.opening_slot proposal) hQ
  have hparentEq : parent = P := Option.some.inj (hparentQ.symm.trans hparent)
  subst parent
  have hparentMem : proposedParent S rho (S.hc.opening_slot proposal) ∈
      (rho.storeBeforeTime S (S.E.proposer (S.hc.opening_slot proposal))
        (Protocol.proposal_time S.E (S.hc.opening_slot proposal))).T := by
    simpa only [proposerReadAt, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      Protocol.NamedStore.setClock, Run.storeBeforeTime] using
        proposedParent_mem S rho (S.hc.opening_slot proposal)
  have hBParent : Block.Preceq B.erase
      (proposedParent S rho (S.hc.opening_slot proposal)) := by
    rw [← hparentErase]
    exact Proofs.NamedWire.erase_preceq hpreceq
  have hBmem : B.erase ∈
      (rho.storeBeforeTime S (S.E.proposer (S.hc.opening_slot proposal))
        (Protocol.proposal_time S.E (S.hc.opening_slot proposal))).T :=
    Proofs.NamedSlotFreshness.ancestor_mem_storeBeforeTime
      S adm.toNamedAdmissibleCore hparentMem hBParent
  have htargetSlot :
      (Protocol.derive_named S.E S.cfg B).T_h.slot ≤ B.erase.slot := by
    exact Proofs.NamedSlotFreshness.preceq_slot_le_of_mem_storeBeforeTime
      S adm.toNamedAdmissibleCore _ hBmem _
        (Proofs.NamedEntryHeight.entry_geometry_ancestor S.E S.cfg B)
  have hentrySlot : B.erase.slot = S.hc.opening_slot entry := by
    rw [Proofs.NamedWire.erase_slot, proposedBlockAt_slot S rho _ hB]
  have hslot : (Protocol.derive_named S.E S.cfg P).T_h.slot ≤
      S.hc.opening_slot entry := by
    rw [← Proofs.NamedEntryHeight.entry_eq_on_plateau
      S.E S.cfg hpreceq hsameHeight.symm, ← hentrySlot]
    exact htargetSlot
  calc
    (Protocol.derive_named S.E S.cfg P).T_h.slot + S.cfg.timeoutDelay ≤
        S.hc.opening_slot entry + (2 + delayExtra) * S.hc.R :=
      Nat.add_le_add hslot (timeoutDelay_le_roundBound S hdelay)
    _ = S.hc.opening_slot (entry + (2 + delayExtra)) := by
      simp [Protocol.HealConfig.opening_slot, Nat.add_mul]
    _ ≤ S.hc.opening_slot proposal := by
      exact Nat.mul_le_mul_right S.hc.R (by
        simpa only [Nat.add_assoc] using hspace)

#print axioms laterOpening_timeoutMature_of_sameHeight

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
