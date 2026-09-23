module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.LeakFairnessL1FrontierLock
public import DecoupledConsensusProofs.Protocol.ChainState.TargetedTimeoutBinding
public import DecoupledConsensusProofs.Protocol.ChainState.DerivationGeometry
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusProofs.Protocol.ChainState.LeakLedger
public import DecoupledConsensusProofs.Protocol.ValidatorClient.Engine
public import DecoupledConsensusProofs.Protocol.ChainState.JustificationCertificates

@[expose] public section

/-! CurrentProduction L1 fairness assembly. The lock theorem and structural
protection are separate
dependencies. The public statement has only its accepted Core, SlashableBound,
honest/emitted-row, exact-source and frontier premises. No lock alignment or
row-contribution premise is inserted into that headline. -/
namespace DecoupledConsensusModel.Proofs.LeakFairnessL1
open DecoupledConsensusModel Internal Execution Internal.LeakFairness
open Proofs.HealingSurface


private theorem w4_named_height_pair_counts_of_lock_agreement
    (record : Protocol.Record) (H : Height) (entry : BlockId) (nu : Bool)
    (fp : Option FinalityPair)
    (haligned : ∀ locked : BlockId, Protocol.own_lock record H fp = some locked →
      locked = entry) :
    Protocol.NamedRecord.encodeHeight (some (H, entry, nu))
        (Protocol.height_pair record (some (H, entry, nu)) fp) =
      .vote H entry false ∨
        Protocol.NamedRecord.encodeHeight (some (H, entry, nu))
          (Protocol.height_pair record (some (H, entry, nu)) fp) =
            .vote H entry true := by
  by_cases htimeout : record.timeout H = true
  · exact Or.inr (by simp only [Protocol.height_pair, if_pos htimeout,
      Protocol.NamedRecord.encodeHeight])
  · cases hlock : Protocol.own_lock record H fp with
    | some locked =>
        have heq := haligned locked hlock
        exact Or.inl (by simp [Protocol.height_pair, htimeout, hlock, heq,
          Protocol.NamedRecord.encodeHeight])
    | none =>
        cases htarget : record.target H with
        | some recorded =>
            by_cases hsame : recorded = entry
            · exact Or.inl (by simp [Protocol.height_pair, htimeout, hlock,
                htarget, hsame, Protocol.NamedRecord.encodeHeight])
            · exact Or.inr (by simp [Protocol.height_pair, htimeout, hlock,
                htarget, hsame, Protocol.NamedRecord.encodeHeight])
        | none =>
            cases nu <;>
              simp [Protocol.height_pair, htimeout, hlock, htarget,
                Protocol.NamedRecord.encodeHeight]

variable {V : Type} [DecidableEq V] [Fintype V]

set_option maxHeartbeats 1000000 in
-- The exact default source equation normalizes repeated action and store projections.
/-- Exact projection of the existing round_action/create_attestation call,
including the actual row's own finality pair and pre-action record. -/
theorem currentProduction_height_pair_fields (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    (actionAttestationAt S rho v r).height_pair =
      Protocol.NamedRecord.encodeHeight
        ((currentProductionSource S rho v r).map (fun source =>
          ((currentProductionSourceState S rho v r source).h,
           (currentProductionSourceState S rho v r source).T_h.root,
           (currentProductionSourceState S rho v r source).nj)))
        (Protocol.height_pair (currentProductionRecord S rho v r)
        ((currentProductionSource S rho v r).map (fun source =>
          ((currentProductionSourceState S rho v r source).h,
           (currentProductionSourceState S rho v r source).T_h.root,
           (currentProductionSourceState S rho v r source).nj)))
        (actionAttestationAt S rho v r).finality_pair) := rfl

/-- The required contribution is derived from the proved-lock target, rather
than assumed as a fairness input. This covers timeout, recorded target,
new target, stored lock, and own-finality lock override branches. -/
theorem currentProduction_heightContribution (S : Setup V) (rho : Run V)
    (core : LeakFairnessExecution S rho) {v : V} (hv : v ∈ rho.honest)
    (r : Round) (source : Block V)
    (hsource : currentProductionSource S rho v r = some source)
    (hfrontier : CurrentProductionSourceAtFrontier S rho v r source)
    (hunique : NoConflictingJustificationsAtHCurrentProduction S rho
      (currentProductionSourceState S rho v r source).h) :
    CurrentProductionHeightContribution S rho v r source := by
  let state := currentProductionSourceState S rho v r source
  let record := currentProductionRecord S rho v r
  let row := actionAttestationAt S rho v r
  have haligned : ∀ locked : BlockId, Protocol.own_lock record state.h row.finality_pair =
      some locked → locked = state.T_h.root := by
    intro locked hlock
    exact LeakFairnessL1FrontierLock.lock_on_source_at_frontier
      S rho core hv r source hsource hfrontier hunique hlock
  have hpair := currentProduction_height_pair_fields S rho v r
  simp only [hsource, Option.map_some] at hpair
  change row.height_pair = .vote state.h state.T_h.root false ∨
    row.height_pair = .vote state.h state.T_h.root true
  rw [hpair]
  exact w4_named_height_pair_counts_of_lock_agreement record state.h state.T_h.root state.nj
    row.finality_pair haligned

omit [Fintype V] in
private theorem w4_named_progress_subset_foldl
    (rows : List (NamedAttestation V)) (sigma : Protocol.ChainState V) :
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
private theorem w4_named_mem_progress_foldl_of_matching
    {a : NamedAttestation V} :
    ∀ (rows : List (NamedAttestation V)) (sigma : Protocol.ChainState V),
      a ∈ rows → a.height_pair.matchesEntry sigma.h sigma.T_h.root = true →
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
      · apply w4_named_progress_subset_foldl
        rw [(TargetedTimeoutBinding.process_height_fields sigma a).1,
          if_pos hmatch]
        exact Finset.mem_insert_self _ _
      · apply ih _ htail
        have hfields := TimeoutBindingDefaults.process_context_fields
          (Protocol.TimeoutBinding.targeted V) sigma row
        rw [hfields.2.1, hfields.2.2.1]
        exact hmatch

private theorem w4_named_preheight_h (E : Env V) (cfg : Protocol.HeightConfig)
    (B : NamedBlock V) :
    (Internal.LeakLedger.namedPreHeightSnapshot E cfg B).h =
      (Protocol.derive_named E cfg B.parent).h := by
  cases B with
  | genesis => rfl
  | node parent slot root votes support rows proposer =>
      exact (NamedDerivationGeometry.fold_context_fields
        (Protocol.TimeoutBinding.targeted V) rows
        ({Protocol.derive_named E cfg parent with s :=
          (NamedBlock.node parent slot root votes support rows proposer).erase.slot})).2.1

private theorem w4_named_height_events_progress_of_same_height
    (E : Env V) (cfg : Protocol.HeightConfig) (pre : Protocol.ChainState V)
    (hh : (Protocol.process_height_events E cfg pre).h = pre.h) :
    (Protocol.process_height_events E cfg pre).progress = pre.progress := by
  rw [Protocol.process_height_events_eq]
  split_ifs with ht hp
  · have hbad := hh
    rw [Protocol.process_height_events_eq, if_pos ht, Protocol.advance_height_h,
      Protocol.afterFin_h] at hbad
    exact False.elim (Nat.succ_ne_self pre.h hbad)
  · have hbad := hh
    rw [Protocol.process_height_events_eq, if_neg ht, if_pos hp,
      Protocol.advance_height_h, Protocol.afterFin_h] at hbad
    exact False.elim (Nat.succ_ne_self pre.h hbad)
  · exact Protocol.afterFin_progress E

private theorem w4_named_pre_progress_to_derive
    (E : Env V) (cfg : Protocol.HeightConfig) (B : NamedBlock V)
    (hh : (Protocol.derive_named E cfg B).h =
      (Protocol.derive_named E cfg B.parent).h) :
    (Internal.LeakLedger.namedPreHeightSnapshot E cfg B).progress ⊆
      (Protocol.derive_named E cfg B).progress := by
  cases B with
  | genesis => exact Finset.Subset.refl _
  | node parent slot root votes support rows proposer =>
      let B : NamedBlock V := .node parent slot root votes support rows proposer
      let pre := Internal.LeakLedger.namedPreHeightSnapshot E cfg B
      have hstate : Protocol.derive_named E cfg B =
          Protocol.process_height_events E cfg pre := rfl
      have hSameSnapshot :
          (Protocol.process_height_events E cfg pre).h = pre.h := by
        rw [← hstate]
        exact hh.trans (w4_named_preheight_h E cfg B).symm
      rw [hstate,
        w4_named_height_events_progress_of_same_height E cfg pre hSameSnapshot]

private theorem w4_named_progress_subset_of_same_height
    (E : Env V) (cfg : Protocol.HeightConfig) {A C : NamedBlock V}
    (hAC : NamedBlock.Preceq A C)
    (hh : (Protocol.derive_named E cfg A).h =
      (Protocol.derive_named E cfg C).h) :
    (Protocol.derive_named E cfg A).progress ⊆
      (Protocol.derive_named E cfg C).progress := by
  induction C with
  | genesis =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAC
      subst A
      exact Finset.Subset.refl _
  | node parent slot root votes support rows proposer ih =>
      let C : NamedBlock V := .node parent slot root votes support rows proposer
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAC
      rcases hAC with rfl | hAparent
      · exact Finset.Subset.refl _
      · have hAparent_le := Proofs.NamedEntryHeight.derive_height_mono E cfg hAparent
        have hparentC_le := Proofs.NamedEntryHeight.derive_height_mono E cfg
          (Proofs.NamedAncestry.named_extend slot root votes support rows proposer
            (Proofs.NamedAncestry.named_self parent))
        have hparent : (Protocol.derive_named E cfg parent).h =
            (Protocol.derive_named E cfg C).h := by
          exact Nat.le_antisymm hparentC_le
            (hh ▸ hAparent_le)
        have hfold :
            (Protocol.derive_named E cfg parent).progress ⊆
              (Internal.LeakLedger.namedPreHeightSnapshot E cfg C).progress := by
          exact w4_named_progress_subset_foldl C.attestations
            ({Protocol.derive_named E cfg parent with s := C.erase.slot})
        exact (ih hAparent (hh.trans hparent.symm)).trans
          (hfold.trans (w4_named_pre_progress_to_derive E cfg C hparent.symm))

private theorem w4_named_of_erase_preceq_of_runBlocks
    (S : Setup V) (rho : Run V) (core : LeakFairnessExecution S rho)
    {A B : NamedBlock V}
    (hArun : RunBlock S rho A) (hBrun : RunBlock S rho B)
    (hpre : Block.Preceq A.erase B.erase) : NamedBlock.Preceq A B := by
  obtain ⟨A', hA'B, hA'e⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hpre
  have hA'run : RunBlock S rho A' :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hBrun hA'B
  have hroot : A'.root = A.root := by
    calc
      A'.root = A'.erase.root := (Proofs.NamedWire.erase_root A').symm
      _ = A.erase.root := congrArg Block.root hA'e
      _ = A.root := Proofs.NamedWire.erase_root A
  have hEq : A' = A :=
    NamedRootCollisionFree.root_injective core.rootCollisionFree A' A
      hA'run hArun A' A (Or.inl (Proofs.NamedAncestry.named_self A'))
      (Or.inr (Proofs.NamedAncestry.named_self A)) hroot
  rw [← hEq]
  exact hA'B

private theorem w4_named_l1_zero_of_pre_progress
    (E : Env V) (cfg : Protocol.HeightConfig) (C : NamedBlock V) (v : V)
    (hprogress : v ∈ (Internal.LeakLedger.namedPreHeightSnapshot E cfg C).progress) :
    (Internal.LeakLedger.namedBlockCharges E cfg C v).l1 = 0 := by
  simp only [Internal.LeakLedger.namedBlockCharges,
    Internal.LeakLedger.LayerCharges.scale, Internal.LeakLedger.charges]
  by_cases hsame :
      (Protocol.derive_named E cfg C).h =
        (Internal.LeakLedger.namedPreHeightSnapshot E cfg C).h
  · have hnot : v ∉
        Finset.univ \ (Internal.LeakLedger.namedPreHeightSnapshot E cfg C).progress := by
      intro hv
      exact (Finset.mem_sdiff.mp hv).2 hprogress
    simp [Internal.LeakLedger.layerOne, hsame, hnot]
  · simp [Internal.LeakLedger.layerOne, hsame]

private theorem w4_carried_contribution_sets_pre_progress
    (S : Setup V) (rho : Run V) (v : V) (r : Round) (source : Block V)
    (hcontribution : CurrentProductionHeightContribution S rho v r source)
    {B : NamedBlock V} (hcarried : CarriedAtSourceEntryCurrentProduction
      S rho v r source B) :
    v ∈ (Internal.LeakLedger.namedPreHeightSnapshot S.E S.cfg B).progress := by
  obtain ⟨_, _, hrow, hheight, hentry⟩ := hcarried
  cases B with
  | genesis =>
      exfalso
      simpa only [Internal.LeakLedger.namedPreHeightSnapshot,
        NamedBlock.attestations, List.not_mem_nil] using hrow
  | node parent slot root votes support rows proposer =>
      let B : NamedBlock V := .node parent slot root votes support rows proposer
      change v ∈
        (rows.foldl (Protocol.process_attestation_with
          (Protocol.TimeoutBinding.targeted V))
          ({Protocol.derive_named S.E S.cfg parent with s := B.erase.slot})).progress
      have hmatch : (actionAttestationAt S rho v r).height_pair.matchesEntry
          (Protocol.derive_named S.E S.cfg parent).h
          (Protocol.derive_named S.E S.cfg parent).T_h.root = true := by
        rcases hcontribution with htarget | htimeout
        · simp only [htarget, NamedHeightPair.matchesEntry, decide_eq_true_eq]
          exact ⟨hheight.symm, hentry.symm⟩
        · simp only [htimeout, NamedHeightPair.matchesEntry, decide_eq_true_eq]
          exact ⟨hheight.symm, hentry.symm⟩
      simpa only [(actionAttestationAt_shape S rho v r).1] using
        w4_named_mem_progress_foldl_of_matching rows
          ({Protocol.derive_named S.E S.cfg parent with s := B.erase.slot})
          hrow hmatch

private theorem w4_same_height_extension_l1_zero
    (S : Setup V) (rho : Run V) (core : LeakFairnessExecution S rho)
    (v : V) {B : NamedBlock V} (hB : B ≠ NamedBlock.genesis)
    (hprogress : v ∈ (Internal.LeakLedger.namedPreHeightSnapshot S.E S.cfg B).progress)
    (hBRun : RunBlock S rho B)
    {C : NamedBlock V} (hCrun : RunBlock S rho C)
    (hBC : Block.Preceq B.erase C.erase)
    (hheight : (Protocol.derive_named S.E S.cfg C.parent).h =
      (Protocol.derive_named S.E S.cfg B.parent).h) :
    (Internal.LeakLedger.namedBlockCharges S.E S.cfg C v).l1 = 0 := by
  cases C with
  | genesis =>
      simp [Internal.LeakLedger.namedBlockCharges,
        Internal.LeakLedger.LayerCharges.scale, Internal.LeakLedger.slotSpan,
        Internal.LeakLedger.charges, Internal.LeakLedger.layerOne,
        NamedBlock.erase, Block.slot, Block.parent]
  | node parent slot root votes support rows proposer =>
      let C : NamedBlock V := .node parent slot root votes support rows proposer
      simp only [NamedBlock.erase, Block.Preceq, Block.preceq,
        Bool.or_eq_true, decide_eq_true_eq] at hBC
      rcases hBC with hEq | hBparentRaw
      · have hBrun : RunBlock S rho B := hBRun
        have hroot : B.root = C.root := by
          have hEq' : B.erase = C.erase := by simpa only [C] using hEq
          calc
            B.root = B.erase.root := (Proofs.NamedWire.erase_root B).symm
            _ = C.erase.root := congrArg Block.root hEq'
            _ = C.root := Proofs.NamedWire.erase_root C
        have hEqNamed : B = C :=
          NamedRootCollisionFree.root_injective core.rootCollisionFree B C
            hBrun hCrun B C (Or.inl (Proofs.NamedAncestry.named_self B))
            (Or.inr (Proofs.NamedAncestry.named_self C)) hroot
        have hprogressC :
            v ∈ (Internal.LeakLedger.namedPreHeightSnapshot S.E S.cfg C).progress := by
          simpa only [hEqNamed] using hprogress
        simpa only [C] using
          w4_named_l1_zero_of_pre_progress S.E S.cfg C v hprogressC

      · have hBtoCparent : NamedBlock.Preceq B C.parent := by
          have hCparentRun : RunBlock S rho C.parent := by
            apply Proofs.NamedRuntime.blockInRun_of_ancestor S rho hCrun
            exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
              (Proofs.NamedAncestry.named_self parent)
          exact w4_named_of_erase_preceq_of_runBlocks S rho core
            hBRun hCparentRun hBparentRaw
        have hBparent_to_B : NamedBlock.Preceq B.parent B := by
          cases B with
          | genesis => exact False.elim (hB rfl)
          | node parentB slotB rootB votesB supportB rowsB proposerB =>
              simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
              exact Or.inr (Proofs.NamedAncestry.named_self _)
        have hBheight_le :
            (Protocol.derive_named S.E S.cfg B).h ≤
              (Protocol.derive_named S.E S.cfg C.parent).h :=
          Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hBtoCparent
        have hBparent_le :
            (Protocol.derive_named S.E S.cfg B.parent).h ≤
              (Protocol.derive_named S.E S.cfg B).h :=
          Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hBparent_to_B
        have hBheight :
            (Protocol.derive_named S.E S.cfg B).h =
              (Protocol.derive_named S.E S.cfg B.parent).h := by
          exact Nat.le_antisymm (hheight ▸ hBheight_le) hBparent_le
        have hBprogress : v ∈
            (Protocol.derive_named S.E S.cfg B).progress :=
          w4_named_pre_progress_to_derive S.E S.cfg B hBheight
            hprogress
        have hCparentProgress : v ∈
            (Protocol.derive_named S.E S.cfg C.parent).progress := by
          exact (w4_named_progress_subset_of_same_height S.E S.cfg hBtoCparent
            (hBheight.trans hheight.symm)) hBprogress
        have hCpreProgress : v ∈
            (Internal.LeakLedger.namedPreHeightSnapshot S.E S.cfg C).progress := by
          change v ∈
            (rows.foldl (Protocol.process_attestation_with
              (Protocol.TimeoutBinding.targeted V))
              ({Protocol.derive_named S.E S.cfg parent with s := C.erase.slot})).progress
          exact w4_named_progress_subset_foldl rows
            ({Protocol.derive_named S.E S.cfg parent with s := C.erase.slot})
            hCparentProgress
        exact w4_named_l1_zero_of_pre_progress S.E S.cfg C v hCpreProgress

private theorem w4_currentProductionL1Protection_of_contribution
    (S : Setup V) (rho : Run V) (core : LeakFairnessExecution S rho)
    (v : V) (r : Round) (source : Block V)
    (hcontribution : CurrentProductionHeightContribution S rho v r source) :
    CurrentProductionL1Protection S rho v r source := by
  intro B hcarried
  have hprogress := w4_carried_contribution_sets_pre_progress
    S rho v r source hcontribution hcarried
  obtain ⟨hBRun, _, hrow, hBheight, _⟩ := hcarried
  have hBne : B ≠ NamedBlock.genesis := by
    intro hgen
    subst B
    simp only [NamedBlock.attestations, List.not_mem_nil] at hrow
  refine ⟨hprogress, ?_⟩
  intro C hCrun hBC hCheight
  exact w4_same_height_extension_l1_zero S rho core v hBne hprogress hBRun hCrun
    hBC (hCheight.trans hBheight.symm)

private theorem w4_named_own_row_erase_mem (B : NamedBlock V) (a : NamedAttestation V)
    (ha : a ∈ B.attestations) :
    a.erase ∈ chain_attestations B.erase := by
  cases B with
  | genesis => simp [NamedBlock.attestations] at ha
  | node parent slot root votes support rows proposer =>
      apply Protocol.mem_chain_attestations_of_mem
      exact List.mem_map.mpr ⟨a, ha, rfl⟩

private theorem w4_named_on_chain_erase_mem {tip carrier : NamedBlock V}
    {a : NamedAttestation V} (hcarrier : NamedBlock.Preceq carrier tip)
    (ha : a ∈ carrier.attestations) :
    a.erase ∈ chain_attestations tip.erase :=
  Protocol.chain_attestations_mono (Proofs.NamedWire.erase_preceq hcarrier)
    (w4_named_own_row_erase_mem carrier a ha)

private theorem w4_no_conflicting_justifications_of_slashableBound
    (S : Setup V) (rho : Run V) (hsb : SlashableBound S rho) (H : Height) :
    NoConflictingJustificationsAtHCurrentProduction S rho H := by
  intro A B hA hB hAh hBh
  by_cases hzero : H = 0
  · have hAg := NamedJustificationCertificates.justified_zero_is_genesis S.E S.cfg A
      (hAh.trans hzero)
    have hBg := NamedJustificationCertificates.justified_zero_is_genesis S.E S.cfg B
      (hBh.trans hzero)
    rw [hAg, hBg]
  · obtain ⟨JA, hJA, hJAerase, QA, hQA, hWA⟩ :=
      NamedJustificationCertificates.justification_certificate S.E S.cfg A
        (by rw [hAh]; exact hzero)
    obtain ⟨JB, hJB, hJBerase, QB, hQB, hWB⟩ :=
      NamedJustificationCertificates.justification_certificate S.E S.cfg B
        (by rw [hBh]; exact hzero)
    have hJAroot :
        (Protocol.derive_named S.E S.cfg A).J.root = JA.root :=
      (congrArg Block.root hJAerase).symm.trans (Proofs.NamedWire.erase_root JA)
    have hJBroot :
        (Protocol.derive_named S.E S.cfg B).J.root = JB.root :=
      (congrArg Block.root hJBerase).symm.trans (Proofs.NamedWire.erase_root JB)
    have hroots : JA.root = JB.root := by
      by_contra hne
      apply hsb A B hA hB
      exact Proofs.Engine.justification_unique_per_height_slashable S.E
        (h := H) (T₁ := JA.root) (T₂ := JB.root) hne hQA hQB
        (by
          intro signer hsigner
          obtain ⟨carrier, a, hcarrier, ha, hav, hpair⟩ := hWA signer hsigner
          refine ⟨a.erase, w4_named_on_chain_erase_mem hcarrier ha, hav, ?_⟩
          change a.height_pair.erase = .target H JA.root
          have hp := congrArg NamedHeightPair.erase hpair
          simpa [NamedHeightPair.erase, hAh] using hp)
        (by
          intro signer hsigner
          obtain ⟨carrier, b, hcarrier, hb, hbv, hpair⟩ := hWB signer hsigner
          refine ⟨b.erase, w4_named_on_chain_erase_mem hcarrier hb, hbv, ?_⟩
          change b.height_pair.erase = .target H JB.root
          have hp := congrArg NamedHeightPair.erase hpair
          simpa [NamedHeightPair.erase, hBh] using hp)
    exact hJAroot.trans (hroots.trans hJBroot.symm)

private theorem w4_public_of_internal (S : Setup V)
    (hInternal : LeakFairnessL1CurrentProductionInternal S) :
    LeakFairnessL1CurrentProduction S := by
  intro rho v r source core hsb hv hsource hfrontier
  exact hInternal rho v r source core hv hsource hfrontier
    (w4_no_conflicting_justifications_of_slashableBound S rho hsb
      (currentProductionSourceState S rho v r source).h)

/-- Internal explicit-no-conflict form. Contribution and carried-chain
protection are both conclusions, with no added callback or lock premise. -/
theorem leakFairnessL1CurrentProductionInternal (S : Setup V) :
    LeakFairnessL1CurrentProductionInternal S := by
  intro rho v r source core hv hsource hfrontier hunique
  have hcontribution := currentProduction_heightContribution
    S rho core hv r source hsource hfrontier hunique
  exact ⟨hcontribution,
    w4_currentProductionL1Protection_of_contribution
      S rho core v r source hcontribution⟩

/-- Proposed public headline. SlashableBound supplies same-height root
uniqueness through the actual chain-certificate theorem. No standalone
no-conflict, lock, or row-contribution assumption is added. -/
theorem leakFairnessL1CurrentProduction (S : Setup V) : LeakFairnessL1CurrentProduction S :=
  w4_public_of_internal S (leakFairnessL1CurrentProductionInternal S)

#print axioms currentProduction_height_pair_fields
#print axioms currentProduction_heightContribution
#print axioms leakFairnessL1CurrentProductionInternal
#print axioms leakFairnessL1CurrentProduction
end DecoupledConsensusModel.Proofs.LeakFairnessL1

end
