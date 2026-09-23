module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.WeakGenesisGSTZeroActionSources
public import DecoupledConsensusProofs.Execution.HandoverPreparedV4
public import DecoupledConsensusProofs.Protocol.ChainState.FGRootWitness

@[expose] public section

/-!
# Prepared V4 protected vote slots

This leaf ports the W5 GST-zero protected-slot fold to the prepared V4 cut.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]


open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem postCut_namedAncestorBodyMem {st : Protocol.NamedStore V}
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

private theorem postCut_actionStore_coherent_core
    (S : Setup V) {rho : Run V} (v : V) (r : Round) :
    Proofs.NamedStore.Coherent S.E S.cfg (actionStoreAt S rho v r).st := by
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (actionStoreAt S rho v r).st := by
    apply Proofs.NamedConfirmationMembership.invariant_update
    exact Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ (S.a r)
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a r) v).1
  exact hinv.1.1

private theorem postCut_actionBody_runBlock_core
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

private theorem postCut_action_named_checkpoint_core
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
  have hcoh := postCut_actionStore_coherent_core (rho := rho) S v r
  have hK : K ∈ (actionStoreAt S rho v r).st.bodies :=
    postCut_namedAncestorBodyMem hcoh.2.2.1 hD hKD
  exact ⟨K, hK, hKentry, hKh, hKD, postCut_actionBody_runBlock_core S adm hv hK⟩

private theorem postCut_emittedAttestation_eq_actionAttestationAt_core
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

private theorem postCut_honestEmittedHeightRow_exactFGSelectorWitness_core
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
  have haEq := postCut_emittedAttestation_eq_actionAttestationAt_core S adm hemit
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

private theorem postCut_honestHeightRow_confirmationWitness_core
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
    postCut_honestEmittedHeightRow_exactFGSelectorWitness_core S adm hemit hh
  obtain ⟨K, hK, hKentry, hKheight, hKpre, -⟩ :=
    postCut_action_named_checkpoint_core S adm haHon hD
  have hKheight' : (Protocol.derive_named S.E S.cfg K).h = h :=
    hKheight.trans hnamedHeight
  have hDderive :
      (actionStoreAt S rho a.val_index a.round).st.core.σ D.erase =
        Protocol.derive_named S.E S.cfg D :=
    (postCut_actionStore_coherent_core S a.val_index a.round).2.2.2.2 D hD
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

private theorem postCut_namedPreceq_of_runBlock_erase_preceq
    {S : Setup V} {rho : Run V} (adm : AdmissibleCore S rho)
    {X B : NamedBlock V}
    (hXrun : RunBlock S rho X) (hBrun : RunBlock S rho B)
    (h : Block.Preceq X.erase B.erase) :
    NamedBlock.Preceq X B := by
  obtain ⟨A, hAB, hAerase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B h
  have hArun : RunBlock S rho A :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hBrun hAB
  have hrootEq : A.root = X.root := by
    rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root X, hAerase]
  have hAX : A = X :=
    adm.toNamedRootCollisionFree.root_injective
      A X hArun hXrun A X
      (Or.inl (Proofs.NamedAncestry.named_self A))
      (Or.inr (Proofs.NamedAncestry.named_self X)) hrootEq
  rw [← hAX]
  exact hAB

private theorem postCut_named_eq_of_runBlocks_erase_eq
    {S : Setup V} {rho : Run V} (adm : AdmissibleCore S rho)
    {A B : NamedBlock V} (hArun : RunBlock S rho A)
    (hBrun : RunBlock S rho B) (hAB : A.erase = B.erase) : A = B := by
  apply adm.toNamedRootCollisionFree.root_injective
    A B hArun hBrun A B
      (Or.inl (Proofs.NamedAncestry.named_self A))
      (Or.inr (Proofs.NamedAncestry.named_self B))
  rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root B, hAB]

private theorem postCut_noOldFrontierAtCutRunBlocks_of_finiteRows
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {fresh base : Round} {cap : Height} {start last : Slot}
    {P : NamedBlock V}
    (holdRows : WeakJoint.OldHeightRowsBounded S rho fresh cap)
    (hheight : cap ≤ (Protocol.derive_named S.E S.cfg P).h)
    (hfgAll : WeakJoint.FGWitnessesBelow S rho fresh base P.erase) :
    WeakJoint.NoOldFrontierAtCutRunBlocks S rho
      (base + S.hc.η_SG) start last P := by
  intro e he hlast C hCrun hPC w hw hhigh a ta K hKrun ha hemit ht hrow hold hT
  by_cases hpre : a.round < fresh
  · have hbound := holdRows a ta _ ha hemit hpre hrow
    have hfloor := hheight.trans
      (Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hPC)
    exact False.elim ((Nat.not_lt_of_ge (hbound.trans hfloor)) hhigh)
  · have hTP := hfgAll a ta _ (Protocol.derive_named S.E S.cfg K).T_h
      ha hemit hrow (Nat.le_of_not_gt hpre) hold hT
    obtain ⟨D, K₀, hT₀, hDmem, -, hDheight, hK₀mem, hK₀entry,
        hK₀height, hK₀D, -⟩ :=
      postCut_honestHeightRow_confirmationWitness_core S adm ha hemit hrow
    have hDrun : RunBlock S rho D := postCut_actionBody_runBlock_core S adm ha hDmem
    have hK₀run : RunBlock S rho K₀ := postCut_actionBody_runBlock_core S adm ha hK₀mem
    have hK₀Dnamed : NamedBlock.Preceq K₀ D :=
      postCut_namedPreceq_of_runBlock_erase_preceq adm hK₀run hDrun hK₀D
    have hK₀target : (derive_named S.E S.cfg K₀).T_h = K₀.erase :=
      (Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hK₀Dnamed
        (hK₀height.trans hDheight.symm)).trans hK₀entry.symm
    have htargets : (derive_named S.E S.cfg K).T_h =
        (derive_named S.E S.cfg K₀).T_h := by
      exact Option.some.inj (hT.symm.trans hT₀)
    obtain ⟨E, hEK, hEentry, hEheight⟩ :=
      Proofs.NamedEntryHeight.entry_ancestor_same_height S.E S.cfg K
    have hErun : RunBlock S rho E :=
      Proofs.NamedRuntime.blockInRun_of_ancestor S rho hKrun hEK
    have hEK₀erase : E.erase = K₀.erase := by
      calc
        E.erase = (derive_named S.E S.cfg K).T_h := hEentry
        _ = (derive_named S.E S.cfg K₀).T_h := htargets
        _ = K₀.erase := hK₀target
    have hEK₀ : E = K₀ :=
      postCut_named_eq_of_runBlocks_erase_eq adm hErun hK₀run hEK₀erase
    have hKheight : (derive_named S.E S.cfg K).h =
        (voteDutyStore S rho w e).h_max - 1 := by
      calc
        (derive_named S.E S.cfg K).h = (derive_named S.E S.cfg E).h := hEheight.symm
        _ = (derive_named S.E S.cfg K₀).h := congrArg
          (fun X => (derive_named S.E S.cfg X).h) hEK₀
        _ = (voteDutyStore S rho w e).h_max - 1 := hK₀height
    have hECerase : Block.Preceq E.erase C.erase := by
      rw [hEentry]
      exact Block.preceq_trans hTP (Proofs.NamedWire.erase_preceq hPC)
    have hEC : NamedBlock.Preceq E C :=
      postCut_namedPreceq_of_runBlock_erase_preceq adm hErun hCrun hECerase
    have hECheight := Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hEC
    have hrowLe : (voteDutyStore S rho w e).h_max - 1 ≤
        (derive_named S.E S.cfg C).h := by
      rw [← hKheight, ← hEheight]
      exact hECheight
    exact False.elim ((Nat.not_lt_of_ge hrowLe) hhigh)


private theorem postCut_protectedVoteSlots_of_historyCut_v2_w_runBlocks
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {lo cap : Time} (hdelivery : NamedHealthyWindowDelivery S rho lo cap)
    (hgstLo : S.E.t_GST ≤ lo)
    (hcapHor : cap ≤ rho.horizon)
    (hcom : HonestCommittees S rho.honest)
    (hmajority : HonestWeightMajority S rho.honest)
    {base cut : Round} {start last : Slot} {P : Block V} {Pn : NamedBlock V}
    (hPerase : Pn.erase = P)
    (hPrun : RunBlock S rho Pn)
    (hspan : base ≤ cut - S.hc.η_SG)
    (hsendLo : ∀ k, base ≤ k → lo ≤ S.a k)
    (hstartpos : 0 < start)
    (hsettled : S.hc.opening_slot cut ≤ start)
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E start)
    (hcap : Protocol.confirmation_time S.E last ≤ cap)
    (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hseed : ProtectedVoteSlot S rho start P)
    (hnoOldFrontier : WeakJoint.NoOldFrontierAtCutRunBlocks
      S rho cut start last Pn)
    (hsgBoot : ∀ r, base ≤ r → r < cut → ∀ w ∈ rho.honest,
      NamedRun.emits S rho w
        (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
      Block.Preceq (actionSGBlockAt S rho w r) P)
    (hconfBoot : ∀ q, S.hc.opening_slot cut ≤ q → q < start →
      ∀ w ∈ rho.honest, ∀ B,
      GenuineConfirmationWith
        (NamedProfile.gradeContract
          (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
        S.E S.hc (confStore S rho w q) q B →
      Block.Preceq B P)
    (hlegacyActionRoots : ∀ r, cut ≤ r →
      S.a r < Protocol.vote_time S.E (last + 1) → ∀ w ∈ rho.honest,
      ∀ (C : NamedBlock V) (a : NamedAttestation V),
      let R := Protocol.get_fg_root
        (actionStoreAt S rho w r).st.core.toHealing.toFG
      C ∈ (actionStoreAt S rho w r).st.bodies →
      (Protocol.derive_named S.E S.cfg C).J = R →
      a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (Object.attest a) (S.a a.round) →
      a.round < cut →
      a.height_pair.erase = HeightPair.target
        (Protocol.derive_named S.E S.cfg C).h_j
        (Protocol.derive_named S.E S.cfg C).J.root →
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
        some R →
      Block.Preceq R P)
    (hlegacyReadRoots : ∀ d, start < d → d ≤ last + 1 →
      ∀ w ∈ rho.honest,
      ∀ (C : NamedBlock V) (a : NamedAttestation V) (ta : Time),
      let R := Protocol.get_fg_root
        (voteDutyStore S rho w d).toHealing.toFG
      C ∈ (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).bodies →
      (Protocol.derive_named S.E S.cfg C).J = R →
      a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (Object.attest a) ta →
      ta < Protocol.vote_time S.E d →
      a.round < cut →
      a.height_pair.erase = HeightPair.target
        (Protocol.derive_named S.E S.cfg C).h_j
        (Protocol.derive_named S.E S.cfg C).J.root →
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
        some R →
      Block.Preceq R P)
    (hwindow : ∀ r, cut ≤ r → 0 < r →
      S.a r < Protocol.vote_time S.E (last + 1) →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hreadWindowV2 : ∀ d, start < d → d ≤ last + 1 →
      0 < S.hc.round_of d →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG (S.hc.round_of d))
    (hcapDomainV2 : ∀ r, cut ≤ r → 0 < r →
      S.a r < Protocol.vote_time S.E (last + 1) → ∀ p,
      DecoupledConsensusModel.Protocol.domain S.E S.hc r p ≤ cap) :
    ∀ d, start ≤ d → d ≤ last + 1 →
      ProtectedVoteSlot S rho d P ∧
      (∀ q, S.hc.opening_slot cut ≤ q → q < d →
        ∀ w ∈ rho.honest, ∀ B,
        GenuineConfirmationWith
          (NamedProfile.gradeContract
            (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
          S.E S.hc (confStore S rho w q) q B →
          ProtectedVoteSlot S rho d B) := by
  have hRpos : 0 < S.hc.R :=
    lt_of_lt_of_le (by decide : 0 < 2) S.hc.R_ge_two
  have hconfHor : ∀ k, k ≤ last →
      Protocol.confirmation_time S.E k ≤ rho.horizon := by
    intro k hk
    apply le_trans ?_ hhor
    rw [Protocol.confirmation_time_eq_support_cutoff_succ,
      Protocol.confirmation_time_eq_support_cutoff_succ]
    exact support_cutoff_mono S.E (Nat.add_le_add_right hk 1)
  have hconfCap : ∀ k, k ≤ last →
      Protocol.confirmation_time S.E k ≤ cap := by
    intro k hk
    apply le_trans ?_ hcap
    rw [Protocol.confirmation_time_eq_support_cutoff_succ,
      Protocol.confirmation_time_eq_support_cutoff_succ]
    exact support_cutoff_mono S.E (Nat.add_le_add_right hk 1)
  intro d hd
  induction d, hd using Nat.le_induction with
  | base =>
      intro hupper
      exact ⟨hseed, fun q hq hqd w hw B hB =>
        hseed.of_ancestor (hconfBoot q hq hqd w hw B hB)⟩
  | succ d hd ih =>
      intro hupper
      have hdlast : d ≤ last := Nat.le_of_succ_le_succ hupper
      have hprev := ih (hdlast.trans (Nat.le_succ last))
      have hdpos : 0 < d := hstartpos.trans_le hd
      have hnext : start < d + 1 := Nat.lt_succ_of_le hd
      have hpostD := hpost.trans (proposal_time_mono S.E hd)
      have hpostVote := hpostD.trans (proposal_time_lt_vote_time S.E d).le
      have hgap : cut ≤ S.hc.round_of (d + 1) := by
        change cut ≤ (d + 1) / S.hc.R
        exact (Nat.le_div_iff_mul_le hRpos).2
          (hsettled.trans (hd.trans (Nat.le_succ d)))
      have htimeMax := vote_time_mono_slots S.E (Nat.add_le_add_right hdlast 1)
      have htimeLift : ∀ {t : Time}, t < Protocol.vote_time S.E (d + 1) →
          t < Protocol.vote_time S.E (last + 1) :=
        fun ht => ht.trans_le htimeMax
      have hnonempty : 0 < ((S.E.committee d) ∩ rho.honest).card := by
        have hm := hcom d
        rcases Nat.eq_zero_or_pos ((S.E.committee d) ∩ rho.honest).card with hz | hp
        · rw [hz, Nat.mul_zero] at hm
          exact absurd hm (Nat.not_lt_zero _)
        · exact hp
      obtain ⟨x, hxmem⟩ := Finset.card_pos.mp hnonempty
      have hx : x ∈ rho.honest := (Finset.mem_inter.mp hxmem).2
      have hxCommittee : x ∈ S.E.committee d := (Finset.mem_inter.mp hxmem).1
      have hpreserve (B : Block V) (hPB : Block.Preceq P B)
          (hB : ProtectedVoteSlot S rho d B) :
          ProtectedVoteSlot S rho (d + 1) B := by
        let D := voterHeadAt S rho x d
        have hbootstrapD : ∀ r, base ≤ r → r < cut →
            S.a r < Protocol.vote_time S.E (d + 1) → ∀ w ∈ rho.honest,
            NamedRun.emits S rho w
              (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
            Block.Preceq (actionSGBlockAt S rho w r) D := by
          intro r hrlo hrhi ht w hw hemit
          exact Block.preceq_trans (hsgBoot r hrlo hrhi w hw hemit)
            (hprev.1.heads x hx)
        have hpriorD : ∀ q, S.hc.opening_slot cut ≤ q → q < d →
            ∀ w ∈ rho.honest, ∀ C,
            GenuineConfirmationWith
              (NamedProfile.gradeContract
                (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
              S.E S.hc (confStore S rho w q) q C →
            Block.Preceq C D := by
          intro q hq hqd w hw C hC
          exact (hprev.2 q hq hqd w hw C hC).heads x hx
        have hlegacyActionRootsD : ∀ r, cut ≤ r →
            S.a r < Protocol.vote_time S.E (d + 1) → ∀ w ∈ rho.honest,
            ∀ (C : NamedBlock V) (a : NamedAttestation V),
            let R := Protocol.get_fg_root
              (actionStoreAt S rho w r).st.core.toHealing.toFG
            C ∈ (actionStoreAt S rho w r).st.bodies →
            (Protocol.derive_named S.E S.cfg C).J = R →
            a.val_index ∈ rho.honest →
            NamedRun.emits S rho a.val_index (Object.attest a) (S.a a.round) →
            a.round < cut →
            a.height_pair.erase = HeightPair.target
              (Protocol.derive_named S.E S.cfg C).h_j
              (Protocol.derive_named S.E S.cfg C).J.root →
            fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
              some R →
            Block.Preceq R D := by
          intro r hr ht w hw C a
          dsimp only
          intro hC hJ ha hemit hold hpair hT
          exact Block.preceq_trans
            (hlegacyActionRoots r hr (htimeLift ht) w hw C a hC hJ ha hemit
              hold hpair hT)
            (hprev.1.heads x hx)
        have hrootCompat : ∀ w ∈ rho.honest, ∀ (C : NamedBlock V)
            (a : NamedAttestation V) (ta : Time),
            let R := Protocol.get_fg_root
              (rho.storeBeforeTime S w (Protocol.vote_time S.E (d + 1))).toHealing.toFG
            C ∈ (rho.storeBeforeTime S w
              (Protocol.vote_time S.E (d + 1))).bodies →
            (Protocol.derive_named S.E S.cfg C).J = R →
            a.val_index ∈ rho.honest →
            NamedRun.emits S rho a.val_index (Object.attest a) ta →
            ta < Protocol.vote_time S.E (d + 1) →
            a.round < cut →
            a.height_pair.erase = HeightPair.target
              (Protocol.derive_named S.E S.cfg C).h_j
              (Protocol.derive_named S.E S.cfg C).J.root →
            fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
              some R →
            Block.compatible B R = true := by
          intro w hw C a ta
          dsimp only
          intro hC hJ ha hemit hta hold hpair hT
          have hRP := hlegacyReadRoots (d + 1) hnext hupper w hw C a ta
            hC hJ ha hemit hta hold hpair hT
          have hRP' : Block.Preceq
              (Protocol.get_fg_root
                (rho.storeBeforeTime S w
                  (Protocol.vote_time S.E (d + 1))).toHealing.toFG) P := by
            simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
              Proofs.Optimistic.tickStore, Protocol.NamedStore.setClock] using hRP
          simp only [Block.compatible, Bool.or_eq_true]
          exact Or.inr (Block.preceq_trans hRP' hPB)
        have hsourcesD :=
          WeakJoint.actionSources_preceq_of_priorConfirmations_and_historyCut_w
            S adm hdelivery hgstLo hcapHor hmajority (base := base) (cut := cut)
            (s := d) (D := D) hspan hsendLo hbootstrapD hpriorD hlegacyActionRootsD
            (fun r hr hrpos ht => hwindow r hr hrpos (htimeLift ht))
            (fun r hr hrpos ht p => hcapDomainV2 r hr hrpos (htimeLift ht) p)
        have hfgB : ∀ r, cut ≤ r →
            S.a r < Protocol.vote_time S.E (d + 1) →
            ∀ z ∈ rho.honest, ∀ T,
            fgConfirmationWitness S (actionStoreAt S rho z r) = some T →
            Block.compatible B T = true := by
          intro r hr ht z hz T hT
          exact Block.compatible_of_preceq_common (hB.heads x hx)
            (((hsourcesD r ((hspan.trans (Nat.sub_le _ _)).trans hr) ht).2
              hr z hz).2 T hT)
        have hrootB : ∀ z ∈ rho.honest, Block.compatible
            (Protocol.get_fg_root
              (Internal.NamedRecoveryRead.voteDutyRead S rho z
                (d + 1)).st.core.toHealing.toFG) B = true := by
          intro z hz
          have hroot := WeakFG.fgRoot_compatible_of_bootstrap_and_recentActions_at_read
            S adm hmajority hz (time := Protocol.vote_time S.E (d + 1))
            (cut := cut) (B := B) hfgB (hrootCompat z hz)
          simpa only [Internal.NamedRecoveryRead.voteDutyRead,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom,
            Protocol.NamedStore.setClock] using hroot
        have hfrontierB : ∀ z ∈ rho.honest, ∀ {C : NamedBlock V}, C.erase = B →
            (Protocol.derive_named S.E S.cfg C).h <
              (Internal.NamedRecoveryRead.voteDutyRead S rho z
                (d + 1)).st.core.h_max - 1 →
            RunBlock S rho C →
            ∀ (a : NamedAttestation V) (ta : Time) (K : NamedBlock V),
              a.val_index ∈ rho.honest →
              NamedRun.emits S rho a.val_index (Object.attest a) ta →
              ta < Protocol.vote_time S.E (d + 1) →
              a.height_pair.erase.height? =
                some ((Proofs.Optimistic.voteDutyStore S rho z (d + 1)).h_max - 1) →
              fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
                some (Protocol.derive_named S.E S.cfg K).T_h →
              RunBlock S rho K →
              Block.compatible C.erase
                (Protocol.derive_named S.E S.cfg K).T_h = true := by
          intro z hz C hCB hCheight hCrun a ta K ha hemit hta hrow hselected hKrun
          by_cases haold : a.round < cut
          · have hPC : NamedBlock.Preceq Pn C :=
              postCut_namedPreceq_of_runBlock_erase_preceq
                adm hPrun hCrun (by
                  rw [hPerase]
                  simpa only [hCB] using hPB)
            have hnamed := hnoOldFrontier (d + 1) hnext hupper C hCrun hPC
              z hz hCheight a ta K hKrun ha hemit hta hrow haold hselected
            have htarget := Proofs.Optimistic.derive_named_T_h_preceq S.E S.cfg K
            have hcases : NamedBlock.Preceq C K ∨ NamedBlock.Preceq K C := by
              simpa only [NamedBlock.compatible, Bool.or_eq_true] using hnamed
            rcases hcases with hCK | hKC
            · exact Block.compatible_of_preceq_common
                (Proofs.NamedWire.erase_preceq hCK) htarget
            · simp only [Block.compatible, Bool.or_eq_true]
              exact Or.inr (Block.preceq_trans htarget
                (Proofs.NamedWire.erase_preceq hKC))
          · have harecent : cut ≤ a.round := Nat.le_of_not_gt haold
            have htime : S.a a.round < Protocol.vote_time S.E (d + 1) := by
              simpa only [(Proofs.Optimistic.emits_attest_shape S hemit).2] using hta
            simpa only [hCB] using
              hfgB a.round harecent htime a.val_index ha
                (Protocol.derive_named S.E S.cfg K).T_h hselected
        have hanchorB : ∀ z ∈ rho.honest,
            Block.compatible (voterAnchorAt S rho z (d + 1)) B = true := by
          intro z hz
          by_cases hrzero : S.hc.round_of (d + 1) = 0
          · rw [WeakGenesis.voterAnchorAt_eq_fgRoot_of_round_zero
              S adm z (d + 1) hrzero]
            exact hrootB z hz
          · have hrpos : 0 < S.hc.round_of (d + 1) :=
              Nat.pos_of_ne_zero hrzero
            have hBD : Block.Preceq B D := hB.heads x hx
            have hcarriersD : ∀ k, base ≤ k → k < S.hc.round_of (d + 1) →
                ∀ u ∈ rho.honest,
                NamedRun.emits S rho u
                  (Object.attest (actionAttestationAt S rho u k)) (S.a k) →
                Block.Preceq (actionSGBlockAt S rho u k) D := by
              intro k hk hklt u hu hemit
              exact (hsourcesD k hk (action_before_vote_of_round_lt S hklt)).1
                u hu hemit
            have hfgD : ∀ r, cut ≤ r →
                S.a r < Protocol.vote_time S.E (d + 1) →
                ∀ u ∈ rho.honest, ∀ T,
                fgConfirmationWitness S (actionStoreAt S rho u r) = some T →
                Block.compatible D T = true := by
              intro r hr ht u hu T hT
              simp only [Block.compatible, Bool.or_eq_true]
              exact Or.inr (((hsourcesD r
                ((hspan.trans (Nat.sub_le _ _)).trans hr) ht).2 hr u hu).2 T hT)
            have hrootCompatD : ∀ u ∈ rho.honest, ∀ (C : NamedBlock V)
                (a : NamedAttestation V) (ta : Time),
                let R := Protocol.get_fg_root
                  (rho.storeBeforeTime S u
                    (Protocol.vote_time S.E (d + 1))).toHealing.toFG
                C ∈ (rho.storeBeforeTime S u
                  (Protocol.vote_time S.E (d + 1))).bodies →
                (Protocol.derive_named S.E S.cfg C).J = R →
                a.val_index ∈ rho.honest →
                NamedRun.emits S rho a.val_index (Object.attest a) ta →
                ta < Protocol.vote_time S.E (d + 1) →
                a.round < cut →
                a.height_pair.erase = HeightPair.target
                  (Protocol.derive_named S.E S.cfg C).h_j
                  (Protocol.derive_named S.E S.cfg C).J.root →
                fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
                  some R →
                Block.compatible D R = true := by
              intro u hu C a ta
              dsimp only
              intro hC hJ ha hemit hta hold hpair hT
              have hRP := hlegacyReadRoots (d + 1) hnext hupper u hu C a ta
                hC hJ ha hemit hta hold hpair hT
              have hRP' : Block.Preceq
                  (Protocol.get_fg_root
                    (rho.storeBeforeTime S u
                      (Protocol.vote_time S.E (d + 1))).toHealing.toFG) P := by
                simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
                  Proofs.Optimistic.tickStore, Protocol.NamedStore.setClock] using hRP
              simp only [Block.compatible, Bool.or_eq_true]
              exact Or.inr (Block.preceq_trans hRP' (hprev.1.heads x hx))
            have hrootD : ∀ u ∈ rho.honest, Block.compatible
                (Protocol.get_fg_root
                  (Internal.NamedRecoveryRead.voteDutyRead S rho u
                    (d + 1)).st.core.toHealing.toFG) D = true := by
              intro u hu
              have hroot := WeakFG.fgRoot_compatible_of_bootstrap_and_recentActions_at_read
                S adm hmajority hu (time := Protocol.vote_time S.E (d + 1))
                (cut := cut) (B := D) hfgD (hrootCompatD u hu)
              simpa only [Internal.NamedRecoveryRead.voteDutyRead,
                NamedActionReads.confirmationReadAt,
                NamedActionReads.confirmationReadFrom,
                Protocol.NamedStore.setClock] using hroot
            have hvoteCap : Protocol.vote_time S.E (d + 1) ≤ cap := by
              apply le_trans ?_ (hconfCap d hdlast)
              rw [← vote_time_succ_add_delta_eq_confirmation_time S.E d]
              exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
            have hvoteHor : Protocol.vote_time S.E (d + 1) ≤ rho.horizon := by
              apply le_trans ?_ (hconfHor d hdlast)
              rw [← vote_time_succ_add_delta_eq_confirmation_time S.E d]
              exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
            have hwindowStart : base ≤ S.hc.round_of (d + 1) - S.hc.η_SG :=
              hspan.trans (Nat.sub_le_sub_right hgap _)
            have hcapEarly : DecoupledConsensusModel.Protocol.early S.E S.hc
                (S.hc.round_of (d + 1)) .g1 ≤ cap := by
              have hdomainCapG1 : DecoupledConsensusModel.Protocol.domain S.E S.hc
                  (S.hc.round_of (d + 1)) .g1 ≤ cap := by
                rw [NamedOutageClosure.domain_g1_eq_opening]
                exact ((proposal_time_mono S.E
                  (Nat.div_mul_le_self (d + 1) S.hc.R)).trans
                    (proposal_time_lt_vote_time S.E (d + 1)).le).trans hvoteCap
              exact (NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1
                S (S.hc.round_of (d + 1))).trans hdomainCapG1
            have hinterpreted := WeakJoint.interpretedInputs_at_voteDuty_w
              S adm hdelivery hgstLo (base := base) (r := S.hc.round_of (d + 1))
              (d := d + 1) (B := D) rfl hrpos hwindowStart (fun k hk _ => hsendLo k hk) hcarriersD hrootD
              hcapEarly hvoteHor
            have hwindowB : Internal.PhaseGrades.WindowMajorityAt S.E S.hc
                (Internal.NamedRecoveryRead.voteDutyRead S rho z
                  (d + 1)).st.core.toHealing.gradeView
                (Internal.NamedRecoveryRead.voteDutyRead S rho z (d + 1)).st.core.F
                rho.honest (S.hc.round_of (d + 1))
                (DecoupledConsensusModel.Protocol.late S.E S.hc
                  (S.hc.round_of (d + 1)) .g1) := by
              apply WeakSG.windowMajorityAt_of_awakeWindowMajority S
                (hreadWindowV2 (d + 1) hnext hupper hrpos)
              intro v hv
              obtain ⟨hvHon, k, hk, huk⟩ := WeakSG.mem_honestAwakeWindow_iff.mp hv
              obtain ⟨input, hinput, hround, hconfirmed, hfind⟩ :=
                hinterpreted z hz v hvHon k hk huk
              refine ⟨input, ?_⟩
              exact GradeCutoffMono.interpretedInputs_mono
                (Internal.NamedRecoveryRead.voteDutyRead S rho z
                  (d + 1)).st.core.toHealing.gradeView
                (Internal.NamedRecoveryRead.voteDutyRead S rho z (d + 1)).st.core.F
                S.hc.η_SG (S.hc.round_of (d + 1))
                (NamedOutageClosure.q10_early_le_late S
                  (S.hc.round_of (d + 1)) .g1) v hinput
            have hhistoryB : ∀ k ∈ Protocol.latest_window S.hc.η_SG
                (S.hc.round_of (d + 1)),
                HonestSGEmissionsCompatibleAtRound S rho k B := by
              intro k hk u hu hemit
              have hcarrierD := hcarriersD k
                (hwindowStart.trans (WeakSG.mem_latestWindow_lower_bound hk))
                (mem_latestWindow_lt hk) u hu hemit
              exact Block.compatible_of_preceq_common hcarrierD hBD
            have hbatchB := WeakJoint.batchCompatibleAt_of_historyCutEmissions
              S adm hz hhistoryB
            let read := Internal.NamedRecoveryRead.voteDutyRead S rho z (d + 1)
            have hslot : read.st.core.s = d + 1 :=
              Proofs.Optimistic.voteDutyRead_slot S rho z (d + 1)
            rcases voterAnchorAt_cases S rho z (d + 1) with hroot |
                ⟨raw, A, hframe, hactive, hA⟩
            · rw [hroot]
              exact hrootB z hz
            · have hframeRead :
                  (DecoupledConsensusModel.Protocol.readFrame read.cache read.st.core.toHealing
                    (S.hc.round_of (d + 1))).g1 = some (some raw) := by
                simpa only [read, hslot] using hframe
              have hgrade := WeakJoint.preparedVoteDutyG1FrameGrade_of_activePrefix
                S adm rfl hrpos hvoteHor z hz raw hframeRead A hactive
              have hanchor := WeakSG.getSgRoot_compatible_of_windowHistory_at_read
                S read (S.hc.round_of (d + 1)) B hbatchB hwindowB
                (fun raw' hframe' => by
                  have heq : raw' = raw := by
                    exact Option.some.inj (Option.some.inj
                      (hframe'.symm.trans hframeRead))
                  simpa only [heq] using hgrade)
                (hrootB z hz)
              simpa only [voterAnchorAt, Internal.PhaseGrades.nodeAnchor,
                Internal.PhaseGrades.nodeRead, Protocol.get_sg_root_with, read, hslot, hA]
                using hanchor
        have hstep := WeakGoldfish.goldfishCone_succ_of_runFrontierWitnesses
          S adm hcom hmajority hdpos hpostVote (hconfHor d hdlast) hB.cone hfrontierB hrootB hanchorB
        exact ⟨hstep.1, hstep.2⟩
      have hPnext := hpreserve P (Block.preceq_self P) hprev.1
      refine ⟨hPnext, ?_⟩
      intro q hq hqd w hw B hB
      by_cases hqd' : q < d
      · have hBold := hprev.2 q hq hqd' w hw B hB
        have hordered : Block.Preceq P B ∨ Block.Preceq B P := by
          simpa only [Block.compatible, Bool.or_eq_true] using
            Block.compatible_of_preceq_common (hprev.1.heads x hx)
              (hBold.heads x hx)
        rcases hordered with hPB | hBP
        · exact hpreserve B hPB hBold
        · exact hPnext.of_ancestor hBP
      · have hqe : q = d :=
          Nat.le_antisymm (Nat.le_of_lt_succ hqd) (Nat.le_of_not_gt hqd')
        subst q
        obtain ⟨y, hy, hBhead⟩ :=
          WeakGoldfish.genuineConfirmation_exists_honestVoteSupporter_after_gst
            S adm hcom (v := w) hw hdpos hpostVote (hconfHor d hdlast) hB
        obtain ⟨hyCommittee, hBhead⟩ := hBhead
        have hordered : Block.Preceq P B ∨ Block.Preceq B P := by
          simpa only [Block.compatible, Bool.or_eq_true] using
            Block.compatible_of_preceq_common (hprev.1.heads y hy) hBhead
        rcases hordered with hPB | hBP
        · let D := voterHeadAt S rho y d
          have hbootstrapD : ∀ r, base ≤ r → r < cut →
              S.a r < Protocol.vote_time S.E (d + 1) → ∀ z ∈ rho.honest,
              NamedRun.emits S rho z
                (Object.attest (actionAttestationAt S rho z r)) (S.a r) →
              Block.Preceq (actionSGBlockAt S rho z r) D := by
            intro r hrlo hrhi ht z hz hemit
            exact Block.preceq_trans (hsgBoot r hrlo hrhi z hz hemit)
              (hprev.1.heads y hy)
          have hpriorD : ∀ q, S.hc.opening_slot cut ≤ q → q < d →
              ∀ z ∈ rho.honest, ∀ C,
              GenuineConfirmationWith
                (NamedProfile.gradeContract
                  (Internal.NamedRecoveryRead.confirmationInputRead S rho z q).cache)
                S.E S.hc (confStore S rho z q) q C →
              Block.Preceq C D := by
            intro q hq hqd z hz C hC
            exact (hprev.2 q hq hqd z hz C hC).heads y hy
          have hlegacyActionRootsD : ∀ r, cut ≤ r →
              S.a r < Protocol.vote_time S.E (d + 1) → ∀ z ∈ rho.honest,
              ∀ (C : NamedBlock V) (a : NamedAttestation V),
              let R := Protocol.get_fg_root
                (actionStoreAt S rho z r).st.core.toHealing.toFG
              C ∈ (actionStoreAt S rho z r).st.bodies →
              (Protocol.derive_named S.E S.cfg C).J = R →
              a.val_index ∈ rho.honest →
              NamedRun.emits S rho a.val_index (Object.attest a) (S.a a.round) →
              a.round < cut →
              a.height_pair.erase = HeightPair.target
                (Protocol.derive_named S.E S.cfg C).h_j
                (Protocol.derive_named S.E S.cfg C).J.root →
              fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
                some R →
              Block.Preceq R D := by
            intro r hr ht z hz C a
            dsimp only
            intro hC hJ ha hemit hold hpair hT
            exact Block.preceq_trans
              (hlegacyActionRoots r hr (htimeLift ht) z hz C a hC hJ ha hemit
                hold hpair hT)
              (hprev.1.heads y hy)
          have hsources :=
            WeakJoint.actionSources_preceq_of_priorConfirmations_and_historyCut_w
              S adm hdelivery hgstLo hcapHor hmajority (base := base) (cut := cut)
              (s := d) (D := D) hspan hsendLo hbootstrapD hpriorD hlegacyActionRootsD
              (fun r hr hrpos ht => hwindow r hr hrpos (htimeLift ht))
              (fun r hr hrpos ht p => hcapDomainV2 r hr hrpos (htimeLift ht) p)
          have hfg : ∀ r, cut ≤ r →
              S.a r < Protocol.vote_time S.E (d + 1) →
              ∀ z ∈ rho.honest, ∀ T,
              fgConfirmationWitness S (actionStoreAt S rho z r) = some T →
              Block.compatible B T = true := by
            intro r hr ht z hz T hT
            exact Block.compatible_of_preceq_common hBhead
              (((hsources r ((hspan.trans (Nat.sub_le _ _)).trans hr) ht).2
                hr z hz).2 T hT)
          have hrootCompatB : ∀ z ∈ rho.honest, ∀ (C : NamedBlock V)
              (a : NamedAttestation V) (ta : Time),
              let R := Protocol.get_fg_root
                (rho.storeBeforeTime S z (Protocol.vote_time S.E (d + 1))).toHealing.toFG
              C ∈ (rho.storeBeforeTime S z
                (Protocol.vote_time S.E (d + 1))).bodies →
              (Protocol.derive_named S.E S.cfg C).J = R →
              a.val_index ∈ rho.honest →
              NamedRun.emits S rho a.val_index (Object.attest a) ta →
              ta < Protocol.vote_time S.E (d + 1) →
              a.round < cut →
              a.height_pair.erase = HeightPair.target
                (Protocol.derive_named S.E S.cfg C).h_j
                (Protocol.derive_named S.E S.cfg C).J.root →
              fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
                some R →
              Block.compatible B R = true := by
            intro z hz C a ta
            dsimp only
            intro hC hJ ha hemit hta hold hpair hT
            have hRP := hlegacyReadRoots (d + 1) hnext hupper z hz C a ta
              hC hJ ha hemit hta hold hpair hT
            have hRP' : Block.Preceq
                (Protocol.get_fg_root
                  (rho.storeBeforeTime S z
                    (Protocol.vote_time S.E (d + 1))).toHealing.toFG) P := by
              simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
                Proofs.Optimistic.tickStore, Protocol.NamedStore.setClock] using hRP
            simp only [Block.compatible, Bool.or_eq_true]
            exact Or.inr (Block.preceq_trans hRP' hPB)
          have hrootB : ∀ z ∈ rho.honest, Block.compatible
              (Protocol.get_fg_root
                (Internal.NamedRecoveryRead.voteDutyRead S rho z (d + 1)).st.core.toHealing.toFG)
              B = true := by
            intro z hz
            have hroot := WeakFG.fgRoot_compatible_of_bootstrap_and_recentActions_at_read
              S adm hmajority hz (time := Protocol.vote_time S.E (d + 1)) (cut := cut)
              (B := B) hfg (hrootCompatB z hz)
            simpa only [Internal.NamedRecoveryRead.voteDutyRead,
              NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
              Protocol.NamedStore.setClock] using hroot
          have hanchorB : ∀ z ∈ rho.honest,
              Block.compatible (voterAnchorAt S rho z (d + 1)) B = true := by
            intro z hz
            by_cases hrzero : S.hc.round_of (d + 1) = 0
            · rw [WeakGenesis.voterAnchorAt_eq_fgRoot_of_round_zero
                S adm z (d + 1) hrzero]
              exact hrootB z hz
            · have hrpos : 0 < S.hc.round_of (d + 1) :=
                Nat.pos_of_ne_zero hrzero
              have hcarriersD : ∀ k, base ≤ k → k < S.hc.round_of (d + 1) →
                  ∀ u ∈ rho.honest,
                  NamedRun.emits S rho u
                    (Object.attest (actionAttestationAt S rho u k)) (S.a k) →
                  Block.Preceq (actionSGBlockAt S rho u k) D := by
                intro k hk hklt u hu hemit
                exact (hsources k hk (action_before_vote_of_round_lt S hklt)).1
                  u hu hemit
              have hfgD : ∀ r, cut ≤ r →
                  S.a r < Protocol.vote_time S.E (d + 1) →
                  ∀ u ∈ rho.honest, ∀ T,
                  fgConfirmationWitness S (actionStoreAt S rho u r) = some T →
                  Block.compatible D T = true := by
                intro r hr ht u hu T hT
                simp only [Block.compatible, Bool.or_eq_true]
                exact Or.inr (((hsources r
                  ((hspan.trans (Nat.sub_le _ _)).trans hr) ht).2 hr u hu).2 T hT)
              have hrootCompatD : ∀ u ∈ rho.honest, ∀ (C : NamedBlock V)
                  (a : NamedAttestation V) (ta : Time),
                  let R := Protocol.get_fg_root
                    (rho.storeBeforeTime S u
                      (Protocol.vote_time S.E (d + 1))).toHealing.toFG
                  C ∈ (rho.storeBeforeTime S u
                    (Protocol.vote_time S.E (d + 1))).bodies →
                  (Protocol.derive_named S.E S.cfg C).J = R →
                  a.val_index ∈ rho.honest →
                  NamedRun.emits S rho a.val_index (Object.attest a) ta →
                  ta < Protocol.vote_time S.E (d + 1) →
                  a.round < cut →
                  a.height_pair.erase = HeightPair.target
                    (Protocol.derive_named S.E S.cfg C).h_j
                    (Protocol.derive_named S.E S.cfg C).J.root →
                  fgConfirmationWitness S
                    (actionStoreAt S rho a.val_index a.round) = some R →
                  Block.compatible D R = true := by
                intro u hu C a ta
                dsimp only
                intro hC hJ ha hemit hta hold hpair hT
                have hRP := hlegacyReadRoots (d + 1) hnext hupper u hu C a ta
                  hC hJ ha hemit hta hold hpair hT
                have hRP' : Block.Preceq
                    (Protocol.get_fg_root
                      (rho.storeBeforeTime S u
                        (Protocol.vote_time S.E (d + 1))).toHealing.toFG) P := by
                  simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
                    Proofs.Optimistic.tickStore, Protocol.NamedStore.setClock] using hRP
                simp only [Block.compatible, Bool.or_eq_true]
                exact Or.inr (Block.preceq_trans hRP' (hprev.1.heads y hy))
              have hrootD : ∀ u ∈ rho.honest, Block.compatible
                  (Protocol.get_fg_root
                    (Internal.NamedRecoveryRead.voteDutyRead S rho u
                      (d + 1)).st.core.toHealing.toFG) D = true := by
                intro u hu
                have hroot := WeakFG.fgRoot_compatible_of_bootstrap_and_recentActions_at_read
                  S adm hmajority hu (time := Protocol.vote_time S.E (d + 1))
                  (cut := cut) (B := D) hfgD (hrootCompatD u hu)
                simpa only [Internal.NamedRecoveryRead.voteDutyRead,
                  NamedActionReads.confirmationReadAt,
                  NamedActionReads.confirmationReadFrom,
                  Protocol.NamedStore.setClock] using hroot
              have hvoteCap : Protocol.vote_time S.E (d + 1) ≤ cap := by
                apply le_trans ?_ (hconfCap d hdlast)
                rw [← vote_time_succ_add_delta_eq_confirmation_time S.E d]
                exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
              have hvoteHor : Protocol.vote_time S.E (d + 1) ≤ rho.horizon := by
                apply le_trans ?_ (hconfHor d hdlast)
                rw [← vote_time_succ_add_delta_eq_confirmation_time S.E d]
                exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
              have hwindowStart : base ≤ S.hc.round_of (d + 1) - S.hc.η_SG :=
                hspan.trans (Nat.sub_le_sub_right hgap _)
              have hcapEarly : DecoupledConsensusModel.Protocol.early S.E S.hc
                  (S.hc.round_of (d + 1)) .g1 ≤ cap := by
                have hdomainCapG1 : DecoupledConsensusModel.Protocol.domain S.E S.hc
                    (S.hc.round_of (d + 1)) .g1 ≤ cap := by
                  rw [NamedOutageClosure.domain_g1_eq_opening]
                  exact ((proposal_time_mono S.E
                    (Nat.div_mul_le_self (d + 1) S.hc.R)).trans
                      (proposal_time_lt_vote_time S.E (d + 1)).le).trans hvoteCap
                exact (NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1
                  S (S.hc.round_of (d + 1))).trans hdomainCapG1
              have hinterpreted := WeakJoint.interpretedInputs_at_voteDuty_w
                S adm hdelivery hgstLo (base := base) (r := S.hc.round_of (d + 1))
                (d := d + 1) (B := D) rfl hrpos hwindowStart (fun k hk _ => hsendLo k hk) hcarriersD hrootD
                hcapEarly hvoteHor
              have hwindowB : Internal.PhaseGrades.WindowMajorityAt S.E S.hc
                  (Internal.NamedRecoveryRead.voteDutyRead S rho z
                    (d + 1)).st.core.toHealing.gradeView
                  (Internal.NamedRecoveryRead.voteDutyRead S rho z (d + 1)).st.core.F
                  rho.honest (S.hc.round_of (d + 1))
                  (DecoupledConsensusModel.Protocol.late S.E S.hc
                    (S.hc.round_of (d + 1)) .g1) := by
                apply WeakSG.windowMajorityAt_of_awakeWindowMajority S
                  (hreadWindowV2 (d + 1) hnext hupper hrpos)
                intro v hv
                obtain ⟨hvHon, k, hk, huk⟩ := WeakSG.mem_honestAwakeWindow_iff.mp hv
                obtain ⟨input, hinput, hround, hconfirmed, hfind⟩ :=
                  hinterpreted z hz v hvHon k hk huk
                refine ⟨input, ?_⟩
                exact GradeCutoffMono.interpretedInputs_mono
                  (Internal.NamedRecoveryRead.voteDutyRead S rho z
                    (d + 1)).st.core.toHealing.gradeView
                  (Internal.NamedRecoveryRead.voteDutyRead S rho z (d + 1)).st.core.F
                  S.hc.η_SG (S.hc.round_of (d + 1))
                  (NamedOutageClosure.q10_early_le_late S
                    (S.hc.round_of (d + 1)) .g1) v hinput
              have hhistoryB : ∀ k ∈ Protocol.latest_window S.hc.η_SG
                  (S.hc.round_of (d + 1)),
                  HonestSGEmissionsCompatibleAtRound S rho k B := by
                intro k hk u hu hemit
                have hcarrierD := hcarriersD k
                  (hwindowStart.trans (WeakSG.mem_latestWindow_lower_bound hk))
                  (mem_latestWindow_lt hk) u hu hemit
                exact Block.compatible_of_preceq_common hcarrierD hBhead
              have hbatchB := WeakJoint.batchCompatibleAt_of_historyCutEmissions
                S adm hz hhistoryB
              let read := Internal.NamedRecoveryRead.voteDutyRead S rho z (d + 1)
              have hslot : read.st.core.s = d + 1 :=
                Proofs.Optimistic.voteDutyRead_slot S rho z (d + 1)
              rcases voterAnchorAt_cases S rho z (d + 1) with hroot |
                  ⟨raw, A, hframe, hactive, hA⟩
              · rw [hroot]
                exact hrootB z hz
              · have hframeRead :
                    (DecoupledConsensusModel.Protocol.readFrame read.cache read.st.core.toHealing
                      (S.hc.round_of (d + 1))).g1 = some (some raw) := by
                  simpa only [read, hslot] using hframe
                have hgrade := WeakJoint.preparedVoteDutyG1FrameGrade_of_activePrefix
                  S adm rfl hrpos hvoteHor z hz raw hframeRead A hactive
                have hanchor := WeakSG.getSgRoot_compatible_of_windowHistory_at_read
                  S read (S.hc.round_of (d + 1)) B hbatchB hwindowB
                  (fun raw' hframe' => by
                    have heq : raw' = raw := by
                      exact Option.some.inj (Option.some.inj
                        (hframe'.symm.trans hframeRead))
                    simpa only [heq] using hgrade)
                  (hrootB z hz)
                simpa only [voterAnchorAt, Internal.PhaseGrades.nodeAnchor,
                  Internal.PhaseGrades.nodeRead, Protocol.get_sg_root_with,
                  read, hslot, hA] using hanchor
          have hfrontierB : ∀ z ∈ rho.honest, ∀ {C : NamedBlock V}, C.erase = B →
              (Protocol.derive_named S.E S.cfg C).h <
                (Internal.NamedRecoveryRead.voteDutyRead S rho z (d + 1)).st.core.h_max - 1 →
              RunBlock S rho C →
              ∀ (a : NamedAttestation V) (ta : Time) (K : NamedBlock V),
                a.val_index ∈ rho.honest →
                NamedRun.emits S rho a.val_index (Object.attest a) ta →
                ta < Protocol.vote_time S.E (d + 1) →
                a.height_pair.erase.height? =
                  some ((Proofs.Optimistic.voteDutyStore S rho z (d + 1)).h_max - 1) →
                fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
                  some (Protocol.derive_named S.E S.cfg K).T_h →
                RunBlock S rho K →
                Block.compatible C.erase
                  (Protocol.derive_named S.E S.cfg K).T_h = true := by
            intro z hz C hCB hCheight hCrun a ta K ha hemit hta hrow hselected hKrun
            by_cases haold : a.round < cut
            · have hPC : NamedBlock.Preceq Pn C :=
                  postCut_namedPreceq_of_runBlock_erase_preceq
                  adm hPrun hCrun (by
                    rw [hPerase]
                    simpa only [hCB] using hPB)
              have hnamed := hnoOldFrontier (d + 1) hnext hupper C hCrun hPC
                z hz hCheight a ta K hKrun ha hemit hta hrow haold hselected
              have htarget := Proofs.Optimistic.derive_named_T_h_preceq S.E S.cfg K
              have hcases : NamedBlock.Preceq C K ∨ NamedBlock.Preceq K C := by
                simpa only [NamedBlock.compatible, Bool.or_eq_true] using hnamed
              rcases hcases with hCK | hKC
              · exact Block.compatible_of_preceq_common
                  (Proofs.NamedWire.erase_preceq hCK) htarget
              · simp only [Block.compatible, Bool.or_eq_true]
                exact Or.inr (Block.preceq_trans htarget
                  (Proofs.NamedWire.erase_preceq hKC))
            · have harecent : cut ≤ a.round := Nat.le_of_not_gt haold
              have htime : S.a a.round < Protocol.vote_time S.E (d + 1) := by
                simpa only [(Proofs.Optimistic.emits_attest_shape S hemit).2] using hta
              simpa only [hCB] using
                hfg a.round harecent htime a.val_index ha
                  (Protocol.derive_named S.E S.cfg K).T_h hselected
          exact WeakGoldfish.protectedVoteSlot_succ_of_genuineConfirmationWith
            S adm hcom hmajority (v := w) hw hdpos hpostD
            (hconfHor d hdlast) hB hfrontierB hrootB hanchorB
        · exact hPnext.of_ancestor hBP






/-- The V4 cut supplies the seed, previous rows, and post-cut window inputs of the
read-horizon protected-slot fold. -/
theorem SettledBootstrapPreparedV4.protectedVoteSlots_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start last : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon) :
    ∀ d, start ≤ d → d ≤ last + 1 →
      ProtectedVoteSlot S rho d P.erase ∧
      (∀ q, S.hc.opening_slot (base + S.hc.η_SG) ≤ q → q < d →
        ∀ w ∈ rho.honest, ∀ B,
        GenuineConfirmationWith
          (NamedProfile.gradeContract
            (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
          S.E S.hc (confStore S rho w q) q B →
          ProtectedVoteSlot S rho d B) := by
  intro d hd hdupper
  by_cases hstartUpper : start ≤ last + 1
  · have hRpos : 0 < S.hc.R :=
      lt_of_lt_of_le (by decide : 0 < 2) S.hc.R_ge_two
    have hcutpos : 0 < base + S.hc.η_SG :=
      Nat.zero_lt_of_lt (Nat.add_lt_add_left S.hc.η_SG_ge_one base)
    have hstartpos : 0 < start :=
      (Nat.mul_pos hcutpos hRpos).trans_le hboot.settled
    have hmajority := honestWeightMajority_of_finiteWindowsFrom S hawake hcutpos
      hboot.settled hstartUpper hhor
    have hpostStart : S.E.t_GST ≤ Protocol.proposal_time S.E start := by
      have hbaseCut : base < base + S.hc.η_SG :=
        Nat.lt_of_succ_le (Nat.add_le_add_left S.hc.η_SG_ge_one base)
      have htime := Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt
        S hbaseCut
      exact hboot.basePost.trans
        ((Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
          (htime.trans (proposal_time_mono S.E hboot.settled)))
    have hvoteHor : Protocol.vote_time S.E (last + 1) ≤ rho.horizon := by
      apply le_trans ?_ hhor
      rw [← vote_time_succ_add_delta_eq_confirmation_time S.E last]
      exact Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)
    have hseed : ProtectedVoteSlot S rho start P.erase :=
      ⟨hboot.seedAll, hboot.seed.cone⟩
    have hnoOld := postCut_noOldFrontierAtCutRunBlocks_of_finiteRows
      S adm (start := start) (last := last)
        hboot.oldRows hboot.heightCap hboot.fgAll
    obtain ⟨hlegacyActionRoots, hlegacyReadRoots⟩ :=
      WeakJoint.legacyRootCallbacks_of_finiteBootstrap_complete
        S adm hboot.oldRows hfinality hboot.frontierSeed hboot.fgAll
    have hwindow : ∀ r, base + S.hc.η_SG ≤ r → 0 < r →
        S.a r < Protocol.vote_time S.E (last + 1) →
        AwakeWindowMajority S.E (fun v => (S.node v).awake)
          rho.honest S.hc.η_SG r := by
      intro r hr _ htime
      apply hawake r hr
      exact (Assembly.a_mono S (Nat.sub_le r 1)).trans
        (le_of_lt htime) |>.trans hvoteHor
    have hreadWindow : ∀ e, start < e → e ≤ last + 1 →
        0 < S.hc.round_of e →
        AwakeWindowMajority S.E (fun v => (S.node v).awake)
          rho.honest S.hc.η_SG (S.hc.round_of e) := by
      intro e hse helast her
      apply hawake (S.hc.round_of e)
      · change base + S.hc.η_SG ≤ e / S.hc.R
        exact (Nat.le_div_iff_mul_le hRpos).2
          (hboot.settled.trans (Nat.le_of_lt hse))
      · exact (windowSourceTime_le_vote S her).trans
          ((vote_time_mono_slots S.E helast).trans hvoteHor)
    have hcapDomain : ∀ r, base + S.hc.η_SG ≤ r → 0 < r →
        S.a r < Protocol.vote_time S.E (last + 1) → ∀ p,
        DecoupledConsensusModel.Protocol.domain S.E S.hc r p ≤ rho.horizon := by
      intro r _ _ htime p
      have hopen : S.hc.opening_slot r ≤ last + 1 := by
        by_contra hn
        have hslt : last + 1 < S.hc.opening_slot r := Nat.lt_of_not_ge hn
        have hconfMono : Protocol.confirmation_time S.E (last + 1) ≤
            Protocol.confirmation_time S.E (S.hc.opening_slot r) := by
          unfold Protocol.confirmation_time
          exact Int.add_le_add_right
            (proposal_time_mono S.E (Nat.le_of_lt hslt)) _
        have hvoteAction : Protocol.vote_time S.E (last + 1) < S.a r := by
          rw [← opening_confirmation_time_eq_action S]
          have hvoteConf : Protocol.vote_time S.E (last + 1) <
              Protocol.confirmation_time S.E (last + 1) := by
            unfold Protocol.vote_time Protocol.confirmation_time
            linarith [S.E.Δ_pos]
          exact hvoteConf.trans_le hconfMono
        exact (not_lt_of_ge hvoteAction.le) htime
      have hopenTime : DecoupledConsensusModel.Protocol.opening S.E S.hc r ≤
          Protocol.proposal_time S.E (last + 1) :=
        proposal_time_mono S.E hopen
      cases p with
      | g0 =>
          simpa only [DecoupledConsensusModel.Protocol.domain,
            DecoupledConsensusModel.Protocol.Phase.domainOffset, one_mul,
            DecoupledConsensusModel.Protocol.opening, Protocol.vote_time] using
            (vote_time_mono_slots S.E hopen).trans hvoteHor
      | g1 =>
          simpa only [DecoupledConsensusModel.Protocol.domain,
            DecoupledConsensusModel.Protocol.Phase.domainOffset, zero_mul, add_zero] using
            hopenTime.trans
              ((proposal_time_lt_vote_time S.E (last + 1)).le.trans hvoteHor)
      | g2 =>
          exact (NamedOutageClosure.domain_le_opening S r).trans
            (hopenTime.trans
              ((proposal_time_lt_vote_time S.E (last + 1)).le.trans hvoteHor))
    have hall := postCut_protectedVoteSlots_of_historyCut_v2_w_runBlocks
      S adm
      (NamedOutageClosure.healthyWindowDelivery_after_gst S rho adm)
      (le_refl _) (le_refl _) hcom hmajority (Pn := P) rfl hboot.runBlock
      (Nat.le_sub_of_add_le (Nat.le_refl _))
      (fun k hk => hboot.basePost.trans (Assembly.a_mono S hk))
      hstartpos hboot.settled hpostStart hhor hhor hseed hnoOld
      hboot.sgBoot hboot.confBoot hlegacyActionRoots hlegacyReadRoots
      hwindow hreadWindow hcapDomain
    exact hall d hd hdupper
  · exact False.elim (hstartUpper (hd.trans hdupper))

#print axioms SettledBootstrapPreparedV4.protectedVoteSlots_core

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
