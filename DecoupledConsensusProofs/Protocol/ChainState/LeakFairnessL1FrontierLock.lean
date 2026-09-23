module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.LeakFairnessL1
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.Schedule.ConfirmationHistoryProducer
public import DecoupledConsensusInternal.Execution.Run
public import DecoupledConsensusProofs.Execution.Concentration
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Protocol.ChainState.DerivationGeometry
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.Handlers.JustificationBound
public import DecoupledConsensusProofs.Protocol.Handlers.JustificationCarrier
public import DecoupledConsensusProofs.Protocol.ChainState.CheckpointHeights
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.BodyRetention
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordClean

@[expose] public section

/-! Frontier lock proof for CurrentProduction. The frontier bound
and internal same-height uniqueness predicate are explicit. Every store
invariant and same-reader lock witness is produced from the actual Core.
The root-to-source step uses only the G2 floor, not full source viability.
No Admissible/all-awake, BelowOneThird or standing lock alignment is used. -/
namespace DecoupledConsensusModel.Proofs.LeakFairnessL1FrontierLock
open DecoupledConsensusModel Internal Execution Execution.NamedActionReads
  Internal.LeakFairness
open Proofs.HealingSurface Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

private theorem w4_fg_root_preceq_current_source
    (S : Setup V) (rho : Run V) (v : V) (r : Round) (source : Block V)
    (hsource : currentProductionSource S rho v r = some source) :
    Block.Preceq
      (Protocol.get_fg_root
        (actionStoreAt S rho v r).st.core.toHealing.toFG) source := by
  let ast := actionStoreAt S rho v r
  change Block.Preceq
    (Protocol.get_fg_root ast.st.core.toHealing.toFG) source
  have hsource' : actionFGSource S ast = some source := by
    simpa only [currentProductionSource, ast] using hsource
  change Protocol.fg_source_with (NamedProfile.gradeContract ast.cache)
      S.E S.hc ast.st.core.toHealing (S.hc.round_of ast.st.core.s)
      (Protocol.grade2_block_with (NamedProfile.gradeContract ast.cache)
        S.E S.hc ast.st.core.toHealing (S.hc.round_of ast.st.core.s)) =
      some source at hsource'
  cases hQ : Protocol.grade2_block_with (NamedProfile.gradeContract ast.cache)
      S.E S.hc ast.st.core.toHealing (S.hc.round_of ast.st.core.s) with
  | none =>
      rw [Protocol.fg_source_with.eq_def, hQ] at hsource'
      exact False.elim (by cases hsource')
  | some Q =>
      have hQmem : Q ∈ Protocol.get_filtered_block_tree ast.st.core.toHealing.toFG := by
        have hQread := hQ
        change DecoupledConsensusModel.Protocol.grade2Block ast.st.core.toHealing
          (DecoupledConsensusModel.Protocol.readFrame ast.cache ast.st.core.toHealing
            (S.hc.round_of ast.st.core.s)) = some Q at hQread
        unfold DecoupledConsensusModel.Protocol.grade2Block at hQread
        split_ifs at hQread
        obtain ⟨root, _, hp⟩ := Option.bind_eq_some_iff.mp hQread
        exact NamedProposalParent.activePrefix_mem _ root Q hp
      have hrootQ : Block.Preceq
          (Protocol.get_fg_root ast.st.core.toHealing.toFG) Q :=
        Proofs.Records.preceq_get_fg_root_of_mem_filtered hQmem
      rw [Protocol.fg_source_with.eq_def, hQ] at hsource'
      cases hwalk : Protocol.deepest_clear (some Q)
          ast.st.core.toHealing.live_confirmed
          ((NamedProfile.gradeContract ast.cache).read S.E S.hc
            ast.st.core.toHealing (S.hc.round_of ast.st.core.s)).clear with
      | none =>
          simp only [hwalk] at hsource'
          have hsourceQ : Q = source := Option.some.inj hsource'
          exact hsourceQ ▸ hrootQ
      | some B =>
          simp only [hwalk] at hsource'
          have hQB : Block.Preceq Q B :=
            (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hwalk)).2.1
          have hsourceB : B = source := Option.some.inj hsource'
          simpa only [hsourceB] using Block.preceq_trans hrootQ hQB

private theorem w4_action_invariant (S : Setup V) (rho : Run V)
    (v : V) (r : Round) :
    Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (actionStoreAt S rho v r).st := by
  unfold actionStoreAt Proofs.HealingSurface.actionReadAt NamedActionReads.actionReadAt
    NamedActionReads.actionReadFrom
  apply Proofs.NamedConfirmationMembership.invariant_update
  apply Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ (S.a r)
  exact (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a r) v).1

theorem currentProduction_action_mem_in_run (S : Setup V) (rho : Run V)
    (sorted : rho.events.Pairwise (fun e f => NamedEvent.key e ≤ NamedEvent.key f))
    {v : V} (hv : v ∈ rho.honest) (r : Round)
    {C : NamedBlock V} (hC : C ∈ (actionStoreAt S rho v r).st.bodies) :
    RunBlock S rho C := by
  have hCpre : C ∈ (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    simpa only [actionStoreAt, Proofs.HealingSurface.actionReadAt,
      NamedActionReads.actionReadAt,
      NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, Protocol.NamedDuties.update_confirmation_with] using hC
  obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho sorted (S.a r)
  have hCn : C ∈ (NamedRun.stateBefore S rho n v).st.bodies := by
    rw [← congrFun hn v]
    exact hCpre
  exact Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv n hCn)

private theorem w4_currentProduction_source_body (S : Setup V) (rho : Run V)
    (v : V) (r : Round) (source : Block V)
    (hsource : currentProductionSource S rho v r = some source) :
    ∃ C : NamedBlock V, C ∈ (actionStoreAt S rho v r).st.bodies ∧ C.erase = source ∧
      (actionStoreAt S rho v r).st.core.σ source =
        Protocol.derive_named S.E S.cfg C := by
  obtain ⟨C, hC, hErase, hDerived, -⟩ :=
    NamedActionSources.action_witness S rho v r source hsource
  exact ⟨C, hC, hErase, hDerived⟩

/-- The actual source is processed; its sigma entry agrees with its derived
chain state. These facts are produced, not added to the lock theorem. -/
theorem currentProduction_source_processed (S : Setup V) (rho : Run V)
    (_core : LeakFairnessExecution S rho) (v : V) (r : Round) (source : Block V)
    (hsource : currentProductionSource S rho v r = some source) :
    ∃ C : NamedBlock V, C ∈ (actionStoreAt S rho v r).st.bodies ∧ C.erase = source ∧
      currentProductionSourceState S rho v r source =
        Protocol.derive_named S.E S.cfg C := by
  obtain ⟨C, hC, hErase, hDerived⟩ := w4_currentProduction_source_body
    S rho v r source hsource
  exact ⟨C, hC, hErase, hDerived⟩

private theorem w4_round_action_head_fields
    (S : Setup V) (rho : Run V) (v : V) (r : Round)
    {H : Height} {T : BlockId}
    (hpair : (actionAttestationAt S rho v r).finality_pair = some ⟨H, T⟩) :
    ∃ D ∈ (actionStoreAt S rho v r).st.core.T,
      ((actionStoreAt S rho v r).st.core.σ D).h_j = H ∧
      ((actionStoreAt S rho v r).st.core.σ D).J.root = T := by
  let ast := actionStoreAt S rho v r
  have hJ : ast.st.core.J ∈ ast.st.core.T := by
    simpa only [ast, actionStoreAt, Proofs.HealingSurface.actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using
        Proofs.NamedStoreBridge.justifiedInTree_stateBeforeTime S rho (S.a r) v
  have hF : ast.st.core.F ∈ ast.st.core.T := by
    simpa only [ast, actionStoreAt, Proofs.HealingSurface.actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using
        Proofs.NamedStoreBridge.finalizedInTree_stateBeforeTime S rho (S.a r) v
  have hpair' :
      (Protocol.NamedActions.round_action_with
        (DecoupledConsensusModel.Protocol.frameContract ast.cache) S.E S.hc
        (S.node v) ast.st.core.toHealing ast.record).2.finality_pair =
          some ⟨H, T⟩ := by
    simpa only [ast, actionAttestationAt, actionStoreAt,
      Proofs.HealingSurface.actionReadAt, Protocol.NamedDuties.attest_with] using hpair
  obtain ⟨D, hD, heq⟩ := round_action_finality_pair
    (DecoupledConsensusModel.Protocol.frameContract ast.cache) S.E S.hc (S.node v)
    ast.st.core.toHealing ast.record
  have heq' :
      (Protocol.NamedActions.round_action_with
        (DecoupledConsensusModel.Protocol.frameContract ast.cache) S.E S.hc
        (S.node v) ast.st.core.toHealing ast.record).2.finality_pair =
      Protocol.finality_pair ast.record.legacy
        (ast.st.core.σ D).h_j (ast.st.core.σ D).J.root
        (ast.st.core.σ D).h_F := by
    simpa only [Protocol.Store.toHealing] using heq
  have hp' : Protocol.finality_pair ast.record.legacy
      (ast.st.core.σ D).h_j (ast.st.core.σ D).J.root
      (ast.st.core.σ D).h_F = some ⟨H, T⟩ := by
    rw [← heq']
    exact hpair'
  have hheight : (ast.st.core.σ D).h_j = H := by
    exact finality_pair_height hp'
  have hroot : (ast.st.core.σ D).J.root = T := by
    simp only [Protocol.finality_pair] at hp'
    split at hp'
    · split at hp'
      · simp only [Option.some.injEq] at hp'
        exact congrArg FinalityPair.target hp'
      · simp at hp'
    · simp at hp'
  refine ⟨D, ?_, hheight, hroot⟩
  rw [hD]
  refine NamedProposalParent.runtime_get_head_mem ast.cache S.E S.hc
    ast.st.core.toHealing _ _ _ ?_
  change (if ast.st.core.h_max = ast.st.core.h_j + 1 then ast.st.core.J else
    ast.st.core.F) ∈ ast.st.core.T
  split_ifs <;> assumption

private theorem w4_currentProduction_finality_body_witness
    (S : Setup V) (rho : Run V) (v : V) (r : Round)
    {H : Height} {T : BlockId}
    (hpair : (actionAttestationAt S rho v r).finality_pair = some ⟨H, T⟩) :
    ∃ D : NamedBlock V, D ∈ (actionStoreAt S rho v r).st.bodies ∧
      (Protocol.derive_named S.E S.cfg D).h_j = H ∧
      (Protocol.derive_named S.E S.cfg D).J.root = T := by
  let ast := actionStoreAt S rho v r
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg ast.st := by
    simpa only [ast] using w4_action_invariant S rho v r
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg ast.st := hinv.1.1
  obtain ⟨D, hD, hDheight, hDroot⟩ :=
    w4_round_action_head_fields S rho v r hpair
  have hDimage : D ∈ ast.st.bodies.image NamedBlock.erase := by
    rw [← hcoh.1]
    exact hD
  obtain ⟨C, hC, hCe⟩ := Finset.mem_image.mp hDimage
  have hσ : ast.st.core.σ D = Protocol.derive_named S.E S.cfg C := by
    rw [← hCe]
    exact hcoh.2.2.2.2 C hC
  refine ⟨C, ?_, ?_, ?_⟩
  · exact hC
  · rw [hσ] at hDheight
    exact hDheight
  · rw [hσ] at hDroot
    exact hDroot

private theorem w4_recordLock_finalityEmission_before_named
    (S : Setup V) (rho : Run V) (v : V) :
    ∀ (n : Nat) {H : Height} {T : BlockId},
      (rho.stateBefore S n v).record.legacy.lock H = some T →
        ∃ (i : Nat), i < n ∧ ∃ (t : Time) (a : NamedAttestation V),
          rho.events[i]? = some (.tick v t) ∧
            Object.attest a ∈ (on_tick_emit S v
              (rho.stateBefore S i v) t).2 ∧
            a.finality_pair = some ⟨H, T⟩ := by
  intro n
  induction n with
  | zero =>
      intro H T hlock
      exact absurd hlock (by
        simp [Run.stateBefore, NamedRun.stateBefore, NamedWorld.init,
          NamedNode.initial, Protocol.NamedRecord.initial,
          Protocol.Record.initial])
  | succ n ih =>
      intro H T hlock
      change (NamedRun.stateBefore S rho (n + 1) v).record.legacy.lock H =
        some T at hlock
      cases hpre : (rho.stateBefore S n v).record.legacy.lock H with
      | some X =>
          have hmono :
              (rho.stateBefore S (n + 1) v).record.legacy.lock H = some X :=
            stateBefore_lock_mono S rho v (n + 1) (Nat.le_succ n) hpre
          have heq : X = T := by
            rw [hlock] at hmono
            exact (Option.some.inj hmono).symm
          subst X
          obtain ⟨i, hi, t, a, hevent, hemitted, hpair⟩ := ih hpre
          exact ⟨i, Nat.lt_succ_of_lt hi, t, a, hevent, hemitted, hpair⟩
      | none =>
          change (rho.stateBefore S n v).record.legacy.lock H = none at hpre
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
                    rw [NamedNode.process_record_eq] at hlock
                    exact absurd hlock (by rw [hpre]; simp)
                  · rw [hstep, hevent] at hlock
                    simp only [Option.toList, List.foldl_cons,
                      List.foldl_nil, NamedWorld.step,
                      Function.update_of_ne (Ne.symm huv)] at hlock
                    exact absurd hlock (by rw [hpre]; simp)

private theorem w4_currentProduction_record_lock_body
    (S : Setup V) (rho : Run V) (core : LeakFairnessExecution S rho)
    (v : V) (r : Round) {H : Height} {T : BlockId}
    (hrecord : (rho.stateBeforeTime S (S.a r) v).record.legacy.lock H = some T) :
    ∃ D : NamedBlock V, D ∈ (actionStoreAt S rho v r).st.bodies ∧
      (Protocol.derive_named S.E S.cfg D).h_j = H ∧
      (Protocol.derive_named S.E S.cfg D).J.root = T := by
  obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    core.sorted (S.a r)
  have hrecordN :
      (rho.stateBefore S n v).record.legacy.lock H = some T := by
    have hn_v := congrFun hn v
    change (NamedRun.stateBefore S rho n v).record.legacy.lock H = some T
    rw [← hn_v]
    exact hrecord
  obtain ⟨i, hi, t, a, hevent, hemitted, hpair⟩ :=
    w4_recordLock_finalityEmission_before_named S rho v n hrecordN
  have hshape := Proofs.Optimistic.emits_attest_shape S
    (show rho.emits S v (Object.attest a) t from ⟨i, hevent, hemitted⟩)
  have htime : t = S.a a.round := hshape.2
  have haeq : a = actionAttestationAt S rho v a.round := by
    have hemitAction : rho.emits S v (Object.attest a) (S.a a.round) := by
      rw [← htime]
      exact ⟨i, hevent, hemitted⟩
    exact (NamedActionSources.action_run_emission_of_sorted_nodup S rho
      core.sorted core.nodup v a.round a).mp
      hemitAction |>.2.2
  have hpair' :
      (actionAttestationAt S rho v a.round).finality_pair = some ⟨H, T⟩ := by
    rw [← haeq]
    exact hpair
  obtain ⟨D, hD, hDh, hDT⟩ :=
    w4_currentProduction_finality_body_witness S rho v a.round hpair'
  have hDi : D ∈ (rho.stateBefore S i v).st.bodies := by
    have hDpre : D ∈ (rho.stateBeforeTime S (S.a a.round) v).st.bodies := by
      simpa only [actionStoreAt, Proofs.HealingSurface.actionReadAt,
        NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
        NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
        NamedRun.stateBeforeTime] using hD
    have hbefore := Proofs.NamedRuntime.tick_prefix_eq_strict S rho
      core.sorted core.nodup hevent
    have hbefore' : NamedRun.stateBefore S rho i v =
        NamedRun.stateBeforeTime S rho (S.a a.round) v := by
      rw [← htime]
      exact hbefore
    change D ∈ (NamedRun.stateBefore S rho i v).st.bodies
    rw [hbefore']
    exact hDpre
  have hDn : D ∈ (rho.stateBefore S n v).st.bodies :=
    NamedBodyRetention.stateBefore_bodies_mono S rho v
      (Nat.le_of_lt hi) hDi
  refine ⟨D, ?_, hDh, hDT⟩
  have hDn' : D ∈ (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    have hn_v := congrFun hn v
    change D ∈ (NamedRun.stateBeforeTime S rho (S.a r) v).st.bodies
    rw [hn_v]
    exact hDn
  simpa only [actionStoreAt, Proofs.HealingSurface.actionReadAt,
    NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
    NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
    NamedRun.stateBeforeTime] using hDn'

private theorem w4_currentProduction_effective_lock_body
    (S : Setup V) (rho : Run V) (core : LeakFairnessExecution S rho)
    (v : V) (r : Round) (source : Block V) {T : BlockId}
    (hlock : currentProductionEffectiveLock S rho v r source = some T) :
    ∃ D : NamedBlock V, D ∈ (actionStoreAt S rho v r).st.bodies ∧
      (Protocol.derive_named S.E S.cfg D).h_j =
        (currentProductionSourceState S rho v r source).h ∧
      (Protocol.derive_named S.E S.cfg D).J.root = T := by
  let H := (currentProductionSourceState S rho v r source).h
  change Protocol.own_lock
      (currentProductionRecord S rho v r) H
      (actionAttestationAt S rho v r).finality_pair = some T at hlock
  cases hfp : (actionAttestationAt S rho v r).finality_pair with
  | none =>
      have hrecord :
          (rho.stateBeforeTime S (S.a r) v).record.legacy.lock H = some T := by
        simpa only [currentProductionRecord, Protocol.own_lock, hfp] using hlock
      exact w4_currentProduction_record_lock_body S rho core v r hrecord
  | some p =>
      rcases p with ⟨h, target⟩
      by_cases hh : h = H
      · subst h
        have ht : target = T := by
          have hlock' : some target = some T := by
            simpa only [currentProductionRecord, Protocol.own_lock, hfp,
              ↓reduceIte] using hlock
          exact Option.some.inj hlock'
        subst target
        exact w4_currentProduction_finality_body_witness S rho v r hfp
      · have hrecord :
            (rho.stateBeforeTime S (S.a r) v).record.legacy.lock H = some T := by
          simpa only [currentProductionRecord, Protocol.own_lock, hfp, hh] using hlock
        exact w4_currentProduction_record_lock_body S rho core v r hrecord

private def w4_NamedEnteringAt (E : Env V) (cfg : HeightConfig)
    (B : NamedBlock V) (H : Height) : Prop :=
  (Protocol.derive_named E cfg B).h = H ∧
    ∀ A : NamedBlock V, NamedBlock.Preceq A B → A ≠ B →
      (Protocol.derive_named E cfg A).h < H

private theorem w4_named_entering_genesis (E : Env V) (cfg : HeightConfig) :
    w4_NamedEnteringAt E cfg NamedBlock.genesis
      (Protocol.derive_named E cfg NamedBlock.genesis).h := by
  constructor
  · rfl
  · intro A hA hne
    have hEq : A = NamedBlock.genesis := by
      simpa only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] using hA
    exact False.elim (hne hEq)

private theorem w4_named_entering_node (E : Env V) (cfg : HeightConfig)
    (parent : NamedBlock V) (s : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V)) (rows : List (NamedAttestation V))
    (proposer : V)
    (hnew : (Protocol.derive_named E cfg
      (.node parent s root votes support rows proposer)).h =
        (Protocol.derive_named E cfg parent).h + 1) :
    w4_NamedEnteringAt E cfg
      (.node parent s root votes support rows proposer)
      (Protocol.derive_named E cfg
        (.node parent s root votes support rows proposer)).h := by
  constructor
  · rfl
  · intro A hA hne
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
      decide_eq_true_eq] at hA
    rcases hA with hEq | hParent
    · exact False.elim (hne hEq)
    · have hle := Proofs.NamedEntryHeight.derive_height_mono E cfg hParent
      rw [hnew]
      exact Nat.lt_succ_of_le hle

private theorem w4_entry_ancestor_same_height_entering
    (E : Env V) (cfg : HeightConfig) (B : NamedBlock V) :
    ∃ entry : NamedBlock V, NamedBlock.Preceq entry B ∧
      entry.erase = (Protocol.derive_named E cfg B).T_h ∧
      (Protocol.derive_named E cfg entry).h =
        (Protocol.derive_named E cfg B).h ∧
      w4_NamedEnteringAt E cfg entry
        (Protocol.derive_named E cfg B).h := by
  induction B with
  | genesis =>
      exact ⟨.genesis, Proofs.NamedAncestry.named_self _, rfl, rfl,
        w4_named_entering_genesis E cfg⟩
  | node parent s root votes support rows proposer ih =>
      let B := NamedBlock.node parent s root votes support rows proposer
      rcases Proofs.NamedEntryHeight.transition_height_entry_cases E cfg
          (Protocol.derive_named E cfg parent) B with hstay | hnew
      · obtain ⟨entry, hentry, herase, hheight, henter⟩ := ih
        refine ⟨entry, Proofs.NamedAncestry.named_extend s root votes support rows proposer hentry,
          ?_, ?_, ?_⟩
        · exact herase.trans hstay.2.symm
        · exact hheight.trans hstay.1.symm
        · change w4_NamedEnteringAt E cfg entry
            (Protocol.named_transition E cfg
              (Protocol.derive_named E cfg parent) B).h
          rw [hstay.1]
          exact henter
      · refine ⟨B, Proofs.NamedAncestry.named_self B, hnew.2.symm, rfl, ?_⟩
        exact w4_named_entering_node E cfg parent s root votes support rows proposer hnew.1

private theorem w4_fold_J (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (Protocol.fold_rows (Protocol.TimeoutBinding.targeted V)
      st geometry rows).J = st.J :=
  (NamedDerivationGeometry.fold_context_fields
    (Protocol.TimeoutBinding.targeted V) rows
    {st with s := geometry.slot}).2.2.2.1

private theorem w4_fold_h_j (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (Protocol.fold_rows (Protocol.TimeoutBinding.targeted V)
      st geometry rows).h_j = st.h_j :=
  (NamedDerivationGeometry.fold_context_fields
    (Protocol.TimeoutBinding.targeted V) rows
    {st with s := geometry.slot}).2.2.2.2.1

private theorem w4_fold_h (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (Protocol.fold_rows (Protocol.TimeoutBinding.targeted V)
      st geometry rows).h = st.h :=
  (NamedDerivationGeometry.fold_context_fields
    (Protocol.TimeoutBinding.targeted V) rows
    {st with s := geometry.slot}).2.1

private theorem w4_fold_T_h (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (Protocol.fold_rows (Protocol.TimeoutBinding.targeted V)
      st geometry rows).T_h = st.T_h :=
  (NamedDerivationGeometry.fold_context_fields
    (Protocol.TimeoutBinding.targeted V) rows
    {st with s := geometry.slot}).2.2.1

private theorem w4_justified_ancestor_with_entering
    (E : Env V) (cfg : HeightConfig) (B : NamedBlock V) :
    (Protocol.derive_named E cfg B).h_j = 0 ∨
      ∃ J : NamedBlock V, NamedBlock.Preceq J B ∧
        J.erase = (Protocol.derive_named E cfg B).J ∧
        (Protocol.derive_named E cfg J).h =
          (Protocol.derive_named E cfg B).h_j ∧
        w4_NamedEnteringAt E cfg J
          (Protocol.derive_named E cfg B).h_j := by
  induction B with
  | genesis => exact Or.inl rfl
  | node parent s root votes support rows proposer ih =>
      let B := NamedBlock.node parent s root votes support rows proposer
      let folded := Protocol.fold_rows
        (Protocol.TimeoutBinding.targeted V)
        (Protocol.derive_named E cfg parent) B.erase B.attestations
      have hstate : Protocol.derive_named E cfg B =
          Protocol.process_height_events E cfg folded := rfl
      rw [hstate, Protocol.process_height_events_eq]
      split_ifs with htarget hfinal
      · right
        obtain ⟨entry, hentry, herase, hheight, henter⟩ :=
          w4_entry_ancestor_same_height_entering E cfg parent
        refine ⟨entry, Proofs.NamedAncestry.named_extend s root votes support rows proposer hentry,
          ?_, ?_, ?_⟩
        · rw [Protocol.advance_height_J,
            Protocol.afterFin_T_h]
          exact herase.trans
            (w4_fold_T_h
              (Protocol.derive_named E cfg parent) B.erase B.attestations).symm
        · rw [Protocol.advance_height_h_j,
            Protocol.afterFin_h]
          exact hheight.trans
            (w4_fold_h
              (Protocol.derive_named E cfg parent) B.erase B.attestations).symm
        · simpa [folded, w4_NamedEnteringAt, Protocol.process_height_events_eq,
            htarget, Protocol.advance_height_h_j, Protocol.afterFin_h, w4_fold_h] using henter
      · rcases ih with hz | ⟨J, hJ, hJE, hJheight, hJenter⟩
        · left
          rw [Protocol.advance_height_h_j,
            Protocol.afterFin_h_j,
            w4_fold_h_j]
          exact hz
        · right
          refine ⟨J, Proofs.NamedAncestry.named_extend s root votes support rows proposer hJ,
            ?_, ?_, ?_⟩
          · rw [Protocol.advance_height_J,
              Protocol.afterFin_J,
              w4_fold_J]
            exact hJE
          · rw [Protocol.advance_height_h_j,
              Protocol.afterFin_h_j,
              w4_fold_h_j]
            exact hJheight
          · simpa [folded, w4_NamedEnteringAt, Protocol.advance_height_h_j,
              Protocol.afterFin_h_j, w4_fold_h_j] using hJenter
      · rcases ih with hz | ⟨J, hJ, hJE, hJheight, hJenter⟩
        · left
          rw [Protocol.afterFin_h_j,
            w4_fold_h_j]
          exact hz
        · right
          refine ⟨J, Proofs.NamedAncestry.named_extend s root votes support rows proposer hJ,
            ?_, ?_, ?_⟩
          · rw [Protocol.afterFin_J,
              w4_fold_J]
            exact hJE
          · rw [Protocol.afterFin_h_j,
              w4_fold_h_j]
            exact hJheight
          · simpa [folded, w4_NamedEnteringAt, Protocol.afterFin_h_j, w4_fold_h_j] using hJenter

private theorem w4_named_entering_unique
    (E : Env V) (cfg : HeightConfig) {A B C : NamedBlock V} {H : Height}
    (hA : w4_NamedEnteringAt E cfg A H)
    (hB : w4_NamedEnteringAt E cfg B H)
    (hAC : NamedBlock.Preceq A C) (hBC : NamedBlock.Preceq B C) : A = B := by
  have hlinear : NamedBlock.Preceq A B ∨ NamedBlock.Preceq B A := by
    induction C with
    | genesis =>
        have hAgen : A = NamedBlock.genesis := by
          simpa only [NamedBlock.Preceq, NamedBlock.preceq,
            decide_eq_true_eq] using hAC
        have hBgen : B = NamedBlock.genesis := by
          simpa only [NamedBlock.Preceq, NamedBlock.preceq,
            decide_eq_true_eq] using hBC
        subst A
        subst B
        exact Or.inl (Proofs.NamedAncestry.named_self _)
    | node p s root votes support rows proposer ih =>
        simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
          decide_eq_true_eq] at hAC hBC
        rcases hAC with hAe | hAp <;> rcases hBC with hBe | hBp
        · subst A
          subst B
          exact Or.inl (Proofs.NamedAncestry.named_self _)
        · subst A
          exact Or.inr (Proofs.NamedAncestry.named_extend s root votes support rows proposer hBp)
        · subst B
          exact Or.inl (Proofs.NamedAncestry.named_extend s root votes support rows proposer hAp)
        · exact ih hAp hBp
  rcases hlinear with hAB | hBA
  · by_contra hne
    have hlt := hB.2 A hAB hne
    exact (Nat.lt_irrefl H) (hA.1 ▸ hlt)
  · by_contra hne
    have hlt := hA.2 B hBA (Ne.symm hne)
    exact (Nat.lt_irrefl H) (hB.1 ▸ hlt)

/-- Actual lock provenance plus the explicit frontier forces the current
justification and source entry to coincide. No lock case is excluded. -/
theorem lock_on_source_at_frontier (S : Setup V) (rho : Run V)
    (core : LeakFairnessExecution S rho) {v : V} (hv : v ∈ rho.honest)
    (r : Round) (source : Block V)
    (hsource : currentProductionSource S rho v r = some source)
    (hfrontier : CurrentProductionSourceAtFrontier S rho v r source)
    (hunique : NoConflictingJustificationsAtHCurrentProduction S rho
      (currentProductionSourceState S rho v r source).h)
    {entry : BlockId} (hlock : currentProductionEffectiveLock S rho v r source = some entry) :
    entry = (currentProductionSourceState S rho v r source).T_h.root := by
  let ast := actionStoreAt S rho v r
  let st := ast.st
  let H := (currentProductionSourceState S rho v r source).h
  have hfront : st.core.h_max ≤ H + 1 := by
    simpa only [st, ast, H] using hfrontier
  have hnoPre := NamedJustificationBound.noHighJustifications_stateBeforeTime
    S rho (S.a r) v
  have hno : Internal.NamedNoHighJustifications S.E S.cfg st := by
    simpa only [st, ast, actionStoreAt, Proofs.HealingSurface.actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hnoPre
  have hbelowPre := NamedJustificationBound.justificationBelowMax_stateBeforeTime
    S rho (S.a r) v
  have hbelow : st.core.h_j < st.core.h_max := by
    simpa only [st, ast, actionStoreAt, Proofs.HealingSurface.actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hbelowPre
  obtain ⟨body, hbody, hbodyHeight, hbodyRoot⟩ :=
    w4_currentProduction_effective_lock_body S rho core v r source hlock
  have hlow : H ≤ st.core.h_j :=
    hbodyHeight.symm.le.trans (hno body (by simpa only [st, ast] using hbody))
  have hhigh : st.core.h_j < st.core.h_max := hbelow
  have hJHeight : st.core.h_j = H :=
    Nat.le_antisymm (Nat.lt_succ_iff.mp (hhigh.trans_le hfront)) hlow
  have hMax : st.core.h_max = st.core.h_j + 1 := by
    have hupper : st.core.h_max ≤ st.core.h_j + 1 :=
      hfront.trans_eq (congrArg (fun n : Nat => n + 1) hJHeight.symm)
    exact Nat.le_antisymm hupper (Nat.succ_le_of_lt hhigh)
  have hRoot : Protocol.get_fg_root st.core.toHealing.toFG = st.core.J := by
    exact if_pos hMax
  have hJsource : Block.Preceq st.core.J source := by
    have hfloor := w4_fg_root_preceq_current_source S rho v r source hsource
    have hfloor' : Block.Preceq
        (Protocol.get_fg_root st.core.toHealing.toFG) source := by
      simpa only [st, ast] using hfloor
    rw [hRoot] at hfloor'
    exact hfloor'
  obtain ⟨sourceBody, hsourceBody, hsourceErase, hsourceDerived⟩ :=
    currentProduction_source_processed S rho core v r source hsource
  have hSourceHeight :
      (Protocol.derive_named S.E S.cfg sourceBody).h = H := by
    have hheight := congrArg ChainState.h hsourceDerived
    simpa only [H] using hheight.symm
  have hHpos : 0 < H := by
    have hpos :=
      (Proofs.NamedStoreRoots.chainOrder_derive_named S.E S.cfg sourceBody).justified_below_height
    have hpos' : 0 < (Protocol.derive_named S.E S.cfg sourceBody).h :=
      lt_of_le_of_lt (Nat.zero_le _) hpos
    simpa only [hSourceHeight] using hpos'
  have hHne : H ≠ 0 := Nat.ne_of_gt hHpos
  obtain ⟨carrier, hcarrierPre, hcarrierJ, hcarrierHeight⟩ :=
    NamedJustificationCarrier.justification_carrier_stateBeforeTime S rho
      (S.a r) v
  have hcarrierA : carrier ∈ st.bodies := by
    simpa only [st, ast, actionStoreAt, Proofs.HealingSurface.actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hcarrierPre
  have hcarrierJ' :
      (Protocol.derive_named S.E S.cfg carrier).J = st.core.J := by
    simpa only [st, ast, actionStoreAt, Proofs.HealingSurface.actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hcarrierJ
  have hcarrierHeight' :
      (Protocol.derive_named S.E S.cfg carrier).h_j = st.core.h_j := by
    simpa only [st, ast, actionStoreAt, Proofs.HealingSurface.actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hcarrierHeight
  have hcarrierH :
      (Protocol.derive_named S.E S.cfg carrier).h_j = H :=
    hcarrierHeight'.trans hJHeight
  rcases w4_justified_ancestor_with_entering S.E S.cfg carrier with hz |
      ⟨Jentry, hJentryCarrier, hJentryErase, hJentryHeight, hJentryEntering⟩
  · exact False.elim (hHne (hcarrierH.symm.trans hz))
  have hJentryHeight' :
      (Protocol.derive_named S.E S.cfg Jentry).h = H := by
    exact hJentryHeight.trans hcarrierH
  have hJentryErase' : Jentry.erase = st.core.J := by
    exact hJentryErase.trans hcarrierJ'
  have hcarrierRun : RunBlock S rho carrier :=
    currentProduction_action_mem_in_run S rho
      core.sorted hv r hcarrierA
  have hJentryRun : RunBlock S rho Jentry :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hcarrierRun hJentryCarrier
  have hsourceRun : RunBlock S rho sourceBody :=
    currentProduction_action_mem_in_run S rho
      core.sorted hv r hsourceBody
  have hJsourceBody : Block.Preceq st.core.J sourceBody.erase := by
    rw [hsourceErase]
    exact hJsource
  obtain ⟨Jlift, hJlift, hJliftErase⟩ :=
    Proofs.NamedAncestry.erased_ancestor_lift sourceBody hJsourceBody
  have hJliftRun : RunBlock S rho Jlift :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hsourceRun hJlift
  have hJliftEq : Jlift = Jentry := by
    have hroot : Jlift.root = Jentry.root := by
      calc
        Jlift.root = Jlift.erase.root := (Proofs.NamedWire.erase_root Jlift).symm
        _ = st.core.J.root := congrArg Block.root hJliftErase
        _ = Jentry.erase.root := congrArg Block.root hJentryErase'.symm
        _ = Jentry.root := Proofs.NamedWire.erase_root Jentry
    exact NamedRootCollisionFree.root_injective core.rootCollisionFree Jlift Jentry
      hJliftRun hJentryRun Jlift Jentry
      (Or.inl (Proofs.NamedAncestry.named_self Jlift))
      (Or.inr (Proofs.NamedAncestry.named_self Jentry))
      hroot
  have hJentrySource : NamedBlock.Preceq Jentry sourceBody := by
    rw [← hJliftEq]
    exact hJlift
  have hJentryEntering' : w4_NamedEnteringAt S.E S.cfg Jentry H := by
    simpa only [w4_NamedEnteringAt, hJentryHeight', hcarrierH] using hJentryEntering
  obtain ⟨Eentry, hEentrySource, hEentryErase, hEentryHeight, hEentryEntering⟩ :=
    w4_entry_ancestor_same_height_entering S.E S.cfg sourceBody
  have hEentryHeight' :
      (Protocol.derive_named S.E S.cfg Eentry).h = H :=
    hEentryHeight.trans hSourceHeight
  have hEentryEntering' : w4_NamedEnteringAt S.E S.cfg Eentry H := by
    simpa only [w4_NamedEnteringAt, hEentryHeight', hSourceHeight] using hEentryEntering
  have hentryEq : Jentry = Eentry := w4_named_entering_unique S.E S.cfg
    hJentryEntering' hEentryEntering' hJentrySource hEentrySource
  have hEentryErase' : Eentry.erase =
      (currentProductionSourceState S rho v r source).T_h := by
    have hsourceTh := congrArg ChainState.T_h hsourceDerived
    exact hEentryErase.trans hsourceTh.symm
  have hJrootSource : st.core.J.root =
      (currentProductionSourceState S rho v r source).T_h.root := by
    calc
      st.core.J.root = Jentry.erase.root := congrArg Block.root hJentryErase'.symm
      _ = Jentry.root := Proofs.NamedWire.erase_root Jentry
      _ = Eentry.root := congrArg NamedBlock.root hentryEq
      _ = Eentry.erase.root := (Proofs.NamedWire.erase_root Eentry).symm
      _ = (currentProductionSourceState S rho v r source).T_h.root :=
        congrArg Block.root hEentryErase'
  have hbodyRun : RunBlock S rho body :=
    currentProduction_action_mem_in_run S rho
      core.sorted hv r
      (by simpa only [st, ast] using hbody)
  have hbodyCarrier := hunique body carrier hbodyRun hcarrierRun
    hbodyHeight hcarrierH
  have hcarrierRoot :
      (Protocol.derive_named S.E S.cfg carrier).J.root = st.core.J.root :=
    congrArg Block.root hcarrierJ'
  calc
    entry = (Protocol.derive_named S.E S.cfg body).J.root := hbodyRoot.symm
    _ = (Protocol.derive_named S.E S.cfg carrier).J.root := hbodyCarrier
    _ = st.core.J.root := hcarrierRoot
    _ = (currentProductionSourceState S rho v r source).T_h.root := hJrootSource

#print axioms currentProduction_action_mem_in_run
#print axioms currentProduction_source_processed
#print axioms lock_on_source_at_frontier
end DecoupledConsensusModel.Proofs.LeakFairnessL1FrontierLock

end
