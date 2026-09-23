module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.FGConfirmationHistory
public import DecoupledConsensusProofs.Protocol.ChainState.Main
public import DecoupledConsensusInternal.Execution.Assumptions
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge
public import DecoupledConsensusProofs.Protocol.Handlers.StoreRoots
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusProofs.Execution.BridgesTail
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityCertificates

@[expose] public section

/-!
# Exact honest sources of selected FG roots

The selected root is justified on a processed chain. In the finalized branch,
use the ancestor that justified the finalized target, not the store's current
justification. Its certificate supplies an earlier honest target action and
the exact confirmation witness. No compatibility of old targets is assumed.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem namedAncestorBodyMem {st : Protocol.NamedStore V}
    (hpc : NamedStore.NamedParentClosed st) {A B : NamedBlock V}
    (hB : B ∈ st.bodies) (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
      exact hAB ▸ hB
  | node parent slot root votes support rows proposer ih =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hparent
      · exact hB
      · exact ih (hpc.2 _ hB) hparent

private theorem actionStore_coherent_core
    (S : Setup V) {rho : Run V} (v : V) (r : Round) :
    Proofs.NamedStore.Coherent S.E S.cfg (actionStoreAt S rho v r).st := by
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (actionStoreAt S rho v r).st := by
    apply Proofs.NamedConfirmationMembership.invariant_update
    exact Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ (S.a r)
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a r) v).1
  exact hinv.1.1

private theorem actionBody_runBlock_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionStoreAt S rho v r).st.bodies) :
    RunBlock S rho D := by
  have hDpre : D ∈ (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    simpa only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
      NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hD
  obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedScheduleWellFormed.sorted (S.a r)
  have hDi : D ∈ (rho.stateBefore S i v).st.bodies := by
    change D ∈ (NamedRun.stateBefore S rho i v).st.bodies
    rw [← hi]
    exact hDpre
  exact Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hDi)

private theorem action_named_checkpoint_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionStoreAt S rho v r).st.bodies) :
    ∃ K : NamedBlock V,
      K ∈ (actionStoreAt S rho v r).st.bodies ∧
      K.erase = (Protocol.derive_named S.E S.cfg D).T_h ∧
      (Protocol.derive_named S.E S.cfg K).h =
        (Protocol.derive_named S.E S.cfg D).h ∧
      NamedBlock.Preceq K D ∧ RunBlock S rho K := by
  obtain ⟨K, hKD, hKentry, hKh⟩ :=
    Proofs.NamedEntryHeight.entry_ancestor_same_height S.E S.cfg D
  have hcoh := actionStore_coherent_core (rho := rho) S v r
  have hK : K ∈ (actionStoreAt S rho v r).st.bodies :=
    namedAncestorBodyMem hcoh.2.2.1 hD hKD
  exact ⟨K, hK, hKentry, hKh, hKD, actionBody_runBlock_core S adm hv hK⟩

theorem emittedAttestation_eq_actionAttestationAt_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {a : NamedAttestation V} {ta : Time}
    (hemit : NamedRun.emits S rho a.val_index (Object.attest a) ta) :
    a = actionAttestationAt S rho a.val_index a.round := by
  have htime : ta = S.a a.round := (Proofs.Optimistic.emits_attest_shape S hemit).2
  subst ta
  obtain ⟨i, hi, hduty⟩ := Proofs.Optimistic.emits_attest_duty S hemit
  rw [Proofs.NamedRuntime.tick_prefix_eq_strict S rho adm.sorted adm.nodup hi] at hduty
  simpa only [actionAttestationAt, actionReadAt,
    NamedActionReads.actionReadAt] using hduty.symm

private theorem honestEmittedHeightRow_exactFGSelectorWitness_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {a : NamedAttestation V} {ta : Time} {h : Height}
    (hemit : NamedRun.emits S rho a.val_index (Object.attest a) ta)
    (hh : a.height_pair.erase.height? = some h) :
    ∃ D : NamedBlock V, ∃ J : Block V,
      ta = S.a a.round ∧
        a = actionAttestationAt S rho a.val_index a.round ∧
        actionFGSource S (actionStoreAt S rho a.val_index a.round) =
          some D.erase ∧
        D ∈ (actionStoreAt S rho a.val_index a.round).st.bodies ∧
        ((actionStoreAt S rho a.val_index a.round).st.core.σ D.erase).h = h ∧
        (Protocol.derive_named S.E S.cfg D).h = h ∧
        J = (Protocol.derive_named S.E S.cfg D).T_h ∧
        (a.height_pair.erase = HeightPair.target h J.root ∨
          a.height_pair.erase = HeightPair.timeout h) := by
  have htime : ta = S.a a.round := (Proofs.Optimistic.emits_attest_shape S hemit).2
  have haEq := emittedAttestation_eq_actionAttestationAt_core S adm hemit
  rw [haEq] at hh
  generalize hp :
      (actionAttestationAt S rho a.val_index a.round).height_pair = q at hh
  cases q with
  | empty => cases hh
  | vote h' entry timeout =>
      have hh' : h' = h := by
        cases timeout <;>
          simpa [NamedHeightPair.erase, HeightPair.height?] using hh
      subst h'
      obtain ⟨Cfg, hCfg, hCfgHeight, hCfgRoot⟩ :=
        NamedActionSources.action_source S rho a.val_index a.round h entry timeout hp
      obtain ⟨D, hD, hDerase, hDderive, -⟩ :=
        NamedActionSources.action_witness S rho a.val_index a.round Cfg hCfg
      let J := (Protocol.derive_named S.E S.cfg D).T_h
      have hsource : actionFGSource S
          (actionStoreAt S rho a.val_index a.round) = some D.erase := by
        simpa only [actionStoreAt, hDerase] using hCfg
      have hheight :
          ((actionStoreAt S rho a.val_index a.round).st.core.σ D.erase).h = h := by
        simpa only [actionStoreAt, hDerase] using hCfgHeight
      have hnamedHeight :
          (Protocol.derive_named S.E S.cfg D).h = h := by
        simpa only [hDderive, actionStoreAt, hDerase] using hheight
      have hJroot : J.root = entry := by
        dsimp only [J]
        simpa only [hDderive] using hCfgRoot
      refine ⟨D, J, htime, haEq, hsource, hD, hheight,
        hnamedHeight, rfl, ?_⟩
      cases timeout with
      | false =>
          left
          rw [haEq, hp]
          simp [NamedHeightPair.erase, hJroot]
      | true =>
          right
          rw [haEq, hp]
          simp [NamedHeightPair.erase]

private theorem honestHeightRow_confirmationWitness_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {a : NamedAttestation V} {ta : Time} {h : Height}
    (haHon : a.val_index ∈ rho.honest)
    (hemit : NamedRun.emits S rho a.val_index (Object.attest a) ta)
    (hh : a.height_pair.erase.height? = some h) :
    ∃ D K : NamedBlock V,
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
        some (Protocol.derive_named S.E S.cfg K).T_h ∧
      D ∈ (actionStoreAt S rho a.val_index a.round).st.bodies ∧
      actionFGSource S (actionStoreAt S rho a.val_index a.round) = some D.erase ∧
      (Protocol.derive_named S.E S.cfg D).h = h ∧
      K ∈ (actionStoreAt S rho a.val_index a.round).st.bodies ∧
      K.erase = (Protocol.derive_named S.E S.cfg D).T_h ∧
      (Protocol.derive_named S.E S.cfg K).h = h ∧
      Block.Preceq K.erase D.erase ∧
      (a.height_pair.erase = HeightPair.target h K.erase.root ∨
        a.height_pair.erase = HeightPair.timeout h) := by
  obtain ⟨D, J, -, -, hsource, hD, -, hnamedHeight, hJ, hrow⟩ :=
    honestEmittedHeightRow_exactFGSelectorWitness_core S adm hemit hh
  obtain ⟨K, hK, hKentry, hKheight, hKpre, -⟩ :=
    action_named_checkpoint_core S adm haHon hD
  have hKheight' : (Protocol.derive_named S.E S.cfg K).h = h :=
    hKheight.trans hnamedHeight
  have hDderive :
      (actionStoreAt S rho a.val_index a.round).st.core.σ D.erase =
        Protocol.derive_named S.E S.cfg D :=
    (actionStore_coherent_core S a.val_index a.round).2.2.2.2 D hD
  have hfg' : fgConfirmationWitness S
      (actionStoreAt S rho a.val_index a.round) =
      some (Protocol.derive_named S.E S.cfg D).T_h := by
    unfold fgConfirmationWitness
    rw [hsource, Option.map_some, hDderive]
  have hKtarget : (Protocol.derive_named S.E S.cfg K).T_h = K.erase := by
    exact (Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hKpre hKheight).trans
      hKentry.symm
  have hfgK : fgConfirmationWitness S
      (actionStoreAt S rho a.val_index a.round) =
      some (Protocol.derive_named S.E S.cfg K).T_h := by
    rw [hfg']
    congr 1
    exact (hKtarget.trans hKentry).symm
  have hJroot : J.root = K.erase.root := by
    rw [hJ, ← hKentry]
  refine ⟨D, K, hfgK, hD, hsource, hnamedHeight, hK, hKentry,
    hKheight', Proofs.NamedWire.erase_preceq hKpre, ?_⟩
  simpa only [hJroot] using hrow


/-- The core frontier witness with the checkpoint's own entry identity kept. -/
theorem frontier_confirmationWitness_core_entry
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hmajority : HonestWeightMajority S rho.honest)
    {v : V} {time : Time}
    (hlarge : 1 < (rho.storeBeforeTime S v time).h_max) :
    ∃ (a : NamedAttestation V) (ta : Time) (D K : NamedBlock V),
      a.val_index ∈ rho.honest ∧
      NamedRun.emits S rho a.val_index (Object.attest a) ta ∧ ta < time ∧
      a.height_pair.erase.height? =
        some ((rho.storeBeforeTime S v time).core.h_max - 1) ∧
      fgConfirmationWitness S
          (actionStoreAt S rho a.val_index a.round) =
        some (Protocol.derive_named S.E S.cfg K).T_h ∧
      D ∈ (actionStoreAt S rho a.val_index a.round).st.bodies ∧
      K ∈ (actionStoreAt S rho a.val_index a.round).st.bodies ∧
      (Protocol.derive_named S.E S.cfg K).T_h = K.erase ∧
      RunBlock S rho K ∧
      (Protocol.derive_named S.E S.cfg K).h =
        (rho.storeBeforeTime S v time).core.h_max - 1 := by
  obtain ⟨W, hW, Q, X, a, ta, hmaxW, hQ, hXW, haW, haHon, hemit, hta,
      hheight⟩ := Protocol.frontierQuorumWitness_stateBeforeTime_core
    S adm hmajority hlarge
  obtain ⟨D, K, hfg, hD, -, hDheight, hK, hKentry, hKheight, hKpre, -⟩ :=
    honestHeightRow_confirmationWitness_core S adm haHon hemit hheight
  have hKrun := actionBody_runBlock_core S adm haHon hK
  have hDrun := actionBody_runBlock_core S adm haHon hD
  obtain ⟨K', hK'D, hK'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift D hKpre
  have hK'run : RunBlock S rho K' :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hDrun hK'D
  have hK'eq : K' = K := by
    apply adm.toNamedRootCollisionFree.root_injective K' K hK'run hKrun
      K' K (Or.inl (Proofs.NamedAncestry.named_self K'))
        (Or.inr (Proofs.NamedAncestry.named_self K))
    rw [← Proofs.NamedWire.erase_root K', ← Proofs.NamedWire.erase_root K, hK'erase]
  have hKpreNamed : NamedBlock.Preceq K D := by
    rw [← hK'eq]
    exact hK'D
  have hKtarget : (Protocol.derive_named S.E S.cfg K).T_h = K.erase :=
    (Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hKpreNamed
      (hKheight.trans hDheight.symm)).trans hKentry.symm
  exact ⟨a, ta, D, K, haHon, hemit, hta, hheight, hfg, hD, hK,
    hKtarget, hKrun, hKheight⟩

private theorem derive_named_F_node_cases
    (E : Env V) (cfg : Protocol.HeightConfig)
    (p : NamedBlock V) (s : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V))
    (rows : List (NamedAttestation V)) (proposer : V) :
    (Protocol.derive_named E cfg
        (.node p s root votes support rows proposer)).F =
        (Protocol.derive_named E cfg p).J ∨
      (Protocol.derive_named E cfg
        (.node p s root votes support rows proposer)).F =
        (Protocol.derive_named E cfg p).F := by
  let B : NamedBlock V := .node p s root votes support rows proposer
  have hfields := NamedDerivationGeometry.fold_context_fields
    (Protocol.TimeoutBinding.targeted V) B.attestations
    { (Protocol.derive_named E cfg p) with s := B.erase.slot }
  have hJfold :
      (Protocol.fold_rows (Protocol.TimeoutBinding.targeted V)
        (Protocol.derive_named E cfg p) B.erase B.attestations).J =
        (Protocol.derive_named E cfg p).J := by
    simpa only [Protocol.fold_rows] using hfields.2.2.2.1
  have hFfold :
      (Protocol.fold_rows (Protocol.TimeoutBinding.targeted V)
        (Protocol.derive_named E cfg p) B.erase B.attestations).F =
        (Protocol.derive_named E cfg p).F := by
    simpa only [Protocol.fold_rows] using hfields.2.2.2.2.2.1
  rw [BlockProcessingDefaults.derive_named_node]
  unfold Protocol.named_transition Protocol.transition_rows
  rw [Protocol.process_height_events_F, Protocol.afterFin_F]
  split_ifs
  · left
    exact hJfold
  · right
    exact hFfold

private theorem namedTrans {A B C : NamedBlock V}
    (hAB : NamedBlock.Preceq A B) (hBC : NamedBlock.Preceq B C) :
    NamedBlock.Preceq A C := by
  induction C with
  | genesis =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hBC
      subst B
      exact hAB
  | node parent slot root votes support rows proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hBC
      rcases hBC with rfl | hparent
      · exact hAB
      · exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
          (ih hparent)

private theorem named_finalized_justificationAncestor
    (E : Env V) (cfg : Protocol.HeightConfig) :
    ∀ C : NamedBlock V, ∃ D : NamedBlock V,
      NamedBlock.Preceq D C ∧
        (Protocol.derive_named E cfg D).J =
          (Protocol.derive_named E cfg C).F := by
  intro C
  induction C with
  | genesis =>
      exact ⟨.genesis, Proofs.NamedAncestry.named_self _, rfl⟩
  | node p s root votes support rows proposer ih =>
      rcases derive_named_F_node_cases E cfg p s root votes support rows proposer with
        h | h
      · exact ⟨p, Proofs.NamedAncestry.named_extend s root votes support rows proposer
          (Proofs.NamedAncestry.named_self p), h.symm⟩
      · obtain ⟨D, hDC, hDJ⟩ := ih
        exact ⟨D, namedTrans hDC
          (Proofs.NamedAncestry.named_extend s root votes support rows proposer
            (Proofs.NamedAncestry.named_self p)), hDJ.trans h.symm⟩

/-- Both FG-root branches have their own processed justification source. -/
theorem fgRoot_justificationSource_at_read
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho) (v : V) (time : Time) :
    ∃ D ∈ (rho.storeBeforeTime S v time).bodies,
      (Protocol.derive_named S.E S.cfg D).J =
        Protocol.get_fg_root (rho.storeBeforeTime S v time).toHealing.toFG := by
  let st := rho.storeBeforeTime S v time
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg st := by
    simpa only [st, Run.storeBeforeTime] using
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho time v).1.1.1
  have hpc : NamedStore.NamedParentClosed st := hcoh.2.2.1
  obtain ⟨J, hJ, hJheight⟩ := Proofs.Bridges.storeJustificationOnChain_stateBeforeTime
    S rho time v
  obtain ⟨F, hF, hFstate, hFheight⟩ := Proofs.Bridges.storeFinalizationOnChain_stateBeforeTime
    S rho time v
  change ∃ D ∈ st.bodies, (Protocol.derive_named S.E S.cfg D).J =
    Protocol.get_fg_root st.toHealing.toFG
  unfold Protocol.get_fg_root
  split_ifs
  · exact ⟨J, hJ, hJheight.1⟩
  · obtain ⟨D, hDF, hDJ⟩ := named_finalized_justificationAncestor
      S.E S.cfg F
    exact ⟨D, namedAncestorBodyMem hpc hF hDF, hDJ.trans hFstate⟩

/-- A processed non-genesis justification is the exact witness of an
earlier honest target action. The emission bound is strict at the read. -/
theorem processedJustification_confirmationWitness
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hmajority : HonestWeightMajority S rho.honest)
    {v : V} (hv : v ∈ rho.honest) {time : Time} {C : NamedBlock V}
    (hC : C ∈ (rho.storeBeforeTime S v time).bodies) :
    (Protocol.derive_named S.E S.cfg C).J = Block.genesis ∨
      ∃ (a : NamedAttestation V) (ta : Time),
        a.val_index ∈ rho.honest ∧
        NamedRun.emits S rho a.val_index (Object.attest a) ta ∧ ta < time ∧
        a.height_pair.erase = HeightPair.target
          (Protocol.derive_named S.E S.cfg C).h_j
          (Protocol.derive_named S.E S.cfg C).J.root ∧
        fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
          some (Protocol.derive_named S.E S.cfg C).J := by
  by_cases hz : (Protocol.derive_named S.E S.cfg C).h_j = 0
  · exact Or.inl (NamedJustificationCertificates.justified_zero_is_genesis
      S.E S.cfg C hz)
  obtain ⟨Jcert, hJcert, hJcertErase, Q, hQ, hwit⟩ :=
    NamedJustificationCertificates.justification_certificate S.E S.cfg C hz
  have hJcertRoot : Jcert.root =
      (Protocol.derive_named S.E S.cfg C).J.root := by
    simpa only [Proofs.NamedWire.erase_root] using congrArg Block.root hJcertErase
  obtain ⟨i, hiQ, hiHon⟩ :=
    Protocol.HonestWeightMajority.exists_honest_member_of_quorum hmajority hQ
  obtain ⟨carrier, a, hcarrier, ha, hai, hap⟩ := hwit i hiQ
  have haHon : a.val_index ∈ rho.honest := by
    rw [hai]
    exact hiHon
  have sch : ScheduleWellFormed S rho :=
    adm.toNamedScheduleWellFormed
  obtain ⟨n, hn, hbefore⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    sch.sorted time
  have hCpre : C ∈ (rho.stateBefore S n v).st.bodies := by
    change C ∈ (NamedRun.stateBefore S rho n v).st.bodies
    have hstate := congrFun hn v
    rw [← hstate]
    exact hC
  have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho n v).1.1.1
  have hcarrierBody : carrier ∈ (rho.stateBefore S n v).st.bodies :=
    namedAncestorBodyMem hcoh.2.2.1 hCpre hcarrier
  rcases Proofs.Bridges.processes_block_of_mem_T S rho v n carrier hcarrierBody with
    hgen | ⟨j, e, hj, hje, hproc⟩
  · simp only [hgen, NamedBlock.attestations, List.not_mem_nil] at ha
  · obtain ⟨hround, hemit⟩ := Proofs.Bridges.carriedArePastEmissions_of_processes
      S rho adm.toNamedUnforgeable hproc ha haHon
    have hta : S.a a.round < time :=
      lt_of_le_of_lt hround (hbefore j e hj hje)
    have hheight : a.height_pair.erase.height? =
        some (Protocol.derive_named S.E S.cfg C).h_j := by
      simpa [hap, hJcertRoot, NamedHeightPair.erase, HeightPair.height?]
    obtain ⟨D, K, hfg, hD, hsource, hDheight, hK, hKentry, hKheight,
        hKpre, hrow⟩ := honestHeightRow_confirmationWitness_core
      S adm haHon hemit hheight
    have hDpre : D ∈
        (rho.stateBeforeTime S (S.a a.round) a.val_index).st.bodies := by
      simpa only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
        NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hD
    have hKpreTime : K ∈
        (rho.stateBeforeTime S (S.a a.round) a.val_index).st.bodies := by
      simpa only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
        NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hK
    have hcohAction := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
      (S.a a.round) a.val_index).1.1.1
    obtain ⟨K', hK'D, hK'erase⟩ :=
      Proofs.NamedAncestry.erased_ancestor_lift D hKpre
    have hK'body : K' ∈
        (rho.stateBeforeTime S (S.a a.round) a.val_index).st.bodies :=
      namedAncestorBodyMem hcohAction.2.2.1 hDpre hK'D
    have hK'eq : K' = K := hcohAction.2.1 K' hK'body K hKpreTime hK'erase
    have hKpreNamed : NamedBlock.Preceq K D := by
      rw [← hK'eq]
      exact hK'D
    have hKtarget : (Protocol.derive_named S.E S.cfg K).T_h = K.erase := by
      have hKDheight : (Protocol.derive_named S.E S.cfg K).h =
          (Protocol.derive_named S.E S.cfg D).h :=
        hKheight.trans hDheight.symm
      exact (Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hKpreNamed hKDheight).trans
        hKentry.symm
    have hroot : K.erase.root =
        (Protocol.derive_named S.E S.cfg C).J.root := by
      rcases hrow with htarget | htimeout
      · have hpair : a.height_pair.erase = HeightPair.target
            (Protocol.derive_named S.E S.cfg C).h_j
            (Protocol.derive_named S.E S.cfg C).J.root := by
          simpa [hap, NamedHeightPair.erase]
        have hEq := htarget.symm.trans hpair
        have hEq' : True ∧ K.erase.root =
            (Protocol.derive_named S.E S.cfg C).J.root := by
          simpa only [HeightPair.target.injEq] using hEq
        exact hEq'.2
      · simp [hap, NamedHeightPair.erase] at htimeout
    have hKrun : RunBlock S rho K := by
      have hKpreTime : K ∈
          (rho.storeBeforeTime S a.val_index (S.a a.round)).bodies := by
        simpa only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
          NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
          NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hK
      obtain ⟨nK, hnK, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
        sch.sorted (S.a a.round)
      have hKprefix : K ∈ (rho.stateBefore S nK a.val_index).st.bodies := by
        change K ∈ (NamedRun.stateBefore S rho nK a.val_index).st.bodies
        have hstate := congrFun hnK a.val_index
        rw [← hstate]
        exact hKpreTime
      exact Proofs.NamedRuntime.blockInRun_of_direct S rho
        (Proofs.NamedRuntime.directBlock_of_prefix S rho haHon nK hKprefix)
    have hcohTime := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho time v).1.1.1
    have hCmemCore : C.erase ∈
        (rho.storeBeforeTime S v time).core.T := by
      change C.erase ∈
        (NamedRun.stateBeforeTime S rho time v).st.core.T
      rw [hcohTime.1]
      exact Finset.mem_image_of_mem NamedBlock.erase hC
    have hJmem : (Protocol.derive_named S.E S.cfg C).J ∈
        (rho.storeBeforeTime S v time).core.T := by
      apply NamedDerivationGeometry.core_ancestor_mem S.E S.cfg
        (rho.storeBeforeTime S v time) hcohTime hCmemCore
      exact (NamedDerivationGeometry.derive_named_anchors_preceq S.E S.cfg C).2
    obtain ⟨J, hJerase, hJrun⟩ :=
      Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
        sch hv time hJmem
    have hroots : K.root = J.root := by
      calc
        K.root = K.erase.root := (Proofs.NamedWire.erase_root K).symm
        _ = (Protocol.derive_named S.E S.cfg C).J.root := hroot
        _ = J.erase.root := by rw [hJerase]
        _ = J.root := Proofs.NamedWire.erase_root J
    have hEq : K = J :=
      adm.toNamedRootCollisionFree.root_injective K J
        hKrun hJrun K J (Or.inl (Proofs.NamedAncestry.named_self K))
        (Or.inr (Proofs.NamedAncestry.named_self J)) hroots
    have hW : (Protocol.derive_named S.E S.cfg K).T_h =
        (Protocol.derive_named S.E S.cfg C).J := by
      exact hKtarget.trans (hEq ▸ hJerase)
    exact Or.inr ⟨a, S.a a.round, haHon, hemit, hta, by
      simpa [hap, NamedHeightPair.erase], hW ▸ hfg⟩

/-- A selected FG root is genesis or an earlier honest action's exact
confirmation witness. This needs only an honest-weight majority. -/
theorem fgRoot_confirmationWitness_at_read
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hmajority : HonestWeightMajority S rho.honest)
    {v : V} (hv : v ∈ rho.honest) (time : Time) :
    let R := Protocol.get_fg_root (rho.storeBeforeTime S v time).toHealing.toFG
    R = Block.genesis ∨ ∃ (C : NamedBlock V),
      C ∈ (rho.storeBeforeTime S v time).bodies ∧
      (Protocol.derive_named S.E S.cfg C).J = R ∧
      ∃ (a : NamedAttestation V) (ta : Time),
      a.val_index ∈ rho.honest ∧
      NamedRun.emits S rho a.val_index (Object.attest a) ta ∧ ta < time ∧
      a.height_pair.erase = HeightPair.target
        (Protocol.derive_named S.E S.cfg C).h_j
        (Protocol.derive_named S.E S.cfg C).J.root ∧
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) = some R := by
  obtain ⟨C, hC, hJ⟩ := fgRoot_justificationSource_at_read S adm v time
  rcases processedJustification_confirmationWitness S adm hmajority hv hC with
      hgen | ⟨a, ta, haHon, hemit, hta, hpair, hwitness⟩
  · exact Or.inl (hJ.symm.trans hgen)
  · exact Or.inr ⟨C, hC, hJ, a, ta, haHon, hemit, hta, hpair, hJ ▸ hwitness⟩

/-- At an action, the selected root comes from a strictly earlier action
round. Thus its source can use the earlier-round safety induction. -/
theorem fgRoot_confirmationWitness_at_action
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hmajority : HonestWeightMajority S rho.honest)
    {v : V} (hv : v ∈ rho.honest) (r : Round) :
    let R := Protocol.get_fg_root (actionStoreAt S rho v r).toHealing.toFG
    R = Block.genesis ∨ ∃ (C : NamedBlock V),
      C ∈ (actionStoreAt S rho v r).st.bodies ∧
      (Protocol.derive_named S.E S.cfg C).J = R ∧
      ∃ a : NamedAttestation V,
      a.val_index ∈ rho.honest ∧
      NamedRun.emits S rho a.val_index (Object.attest a) (S.a a.round) ∧
        a.round < r ∧
      a.height_pair.erase = HeightPair.target
        (Protocol.derive_named S.E S.cfg C).h_j
        (Protocol.derive_named S.E S.cfg C).J.root ∧
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) = some R := by
  dsimp only
  rw [actionStoreAt_fgRoot_eq_storeBeforeTime]
  rcases fgRoot_confirmationWitness_at_read S adm hmajority hv (S.a r) with
      hgen | ⟨C, hC, hJ, a, ta, ha, hemit, ht, hpair, hT⟩
  · exact Or.inl hgen
  · have htime := (Proofs.Optimistic.emits_attest_shape S hemit).2
    have hlt : S.a a.round < S.a r := by simpa only [htime] using ht
    have hr : a.round < r := by
      by_contra hnot
      exact (not_lt_of_ge (Assembly.a_mono S (Nat.le_of_not_gt hnot))) hlt
    exact Or.inr ⟨C, hC, hJ, a, ha, by simpa only [htime] using hemit,
      hr, hpair, hT⟩

/-- Root compatibility follows from recent exact witnesses and a bootstrap
fact only for an old target that can explain this selected root. Old targets
on other branches of the tree are not constrained. -/
theorem fgRoot_compatible_of_bootstrap_and_recentActions_at_read
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hmajority : HonestWeightMajority S rho.honest)
    {v : V} (hv : v ∈ rho.honest) {time : Time} {cut : Round} {B : Block V}
    (hrecent : ∀ r, cut ≤ r → S.a r < time → ∀ w ∈ rho.honest, ∀ T,
      fgConfirmationWitness S (actionStoreAt S rho w r) = some T →
        Block.compatible B T = true)
    (hbootstrap : ∀ (C : NamedBlock V) (a : NamedAttestation V) (ta : Time),
      let R := Protocol.get_fg_root (rho.storeBeforeTime S v time).toHealing.toFG
      C ∈ (rho.storeBeforeTime S v time).bodies →
      (Protocol.derive_named S.E S.cfg C).J = R →
      a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (Object.attest a) ta →
      ta < time → a.round < cut →
      a.height_pair.erase = HeightPair.target
        (Protocol.derive_named S.E S.cfg C).h_j
        (Protocol.derive_named S.E S.cfg C).J.root →
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) = some R →
        Block.compatible B R = true) :
    Block.compatible
      (Protocol.get_fg_root (rho.storeBeforeTime S v time).toHealing.toFG) B = true := by
  rcases fgRoot_confirmationWitness_at_read S adm hmajority hv time with
      hgen | ⟨C, hC, hJ, a, ta, ha, hemit, ht, hpair, hT⟩
  · rw [hgen]
    simp [Block.compatible, Protocol.preceq_genesis]
  · suffices h : Block.compatible B
        (Protocol.get_fg_root (rho.storeBeforeTime S v time).toHealing.toFG) = true by
      simpa only [Block.compatible, Bool.or_comm] using h
    by_cases hboot : a.round < cut
    · exact hbootstrap C a ta hC hJ ha hemit ht hboot hpair hT
    · have htime := (Proofs.Optimistic.emits_attest_shape S hemit).2
      have hltime : S.a a.round < time := by
        simpa only [htime] using ht
      exact hrecent a.round (Nat.le_of_not_gt hboot) hltime
        a.val_index ha _ hT



end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms frontier_confirmationWitness_core_entry
#print axioms fgRoot_confirmationWitness_at_read
#print axioms fgRoot_confirmationWitness_at_action
#print axioms fgRoot_compatible_of_bootstrap_and_recentActions_at_read
end DecoupledConsensusModel.Proofs.HealingSurface

end
