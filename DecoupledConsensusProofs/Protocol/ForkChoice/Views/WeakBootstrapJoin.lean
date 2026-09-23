module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Store.WeakSGHistory
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGCompatibleHistory
public import DecoupledConsensusProofs.Protocol.Grades.RelativeOneChain
public import DecoupledConsensusProofs.Protocol.Grades.WeakBootstrapAction
public import DecoupledConsensusProofs.Objects.WeakFGRoot
public import DecoupledConsensusProofs.Protocol.Grades.SafetyCompatibilityJoin
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.WeakConfirmationSupport
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.WeakBootstrapGradePersistence
public import DecoupledConsensusProofs.Protocol.Schedule.WeakGoldfishCone
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.PreparedVoteDutyPackage

@[expose] public section


/-!
# Joint compatibility with an independent history cutoff

Earlier confirmations and the finite bootstrap protect the current action
sources. These sources supply compatibility for both cone preservation and
new confirmation adoption. No future safety result is an input.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakJoint

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]








/-- The prepared vote-duty read stores every named run block it holds at that
block's canonical derived height. This replaces earlier's
`derivedStateAgrees_depReachable` step by the  named store exports. -/
theorem storedHeight_of_runBlock_mem_voteDutyRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot} {X : NamedBlock V}
    (hXrun : RunBlock S rho X)
    (hXmem : X.erase ∈
      (Internal.NamedRecoveryRead.voteDutyRead S rho w s).st.core.T) :
    ((Internal.NamedRecoveryRead.voteDutyRead S rho w s).st.core.σ X.erase).h =
      (Protocol.derive_named S.E S.cfg X).h := by
  obtain ⟨X', hX', hX'erase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (Protocol.vote_time S.E s) w (by
        simpa only [Internal.NamedRecoveryRead.voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock] using hXmem)
  have hX'run : RunBlock S rho X' := by
    obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted
      (Protocol.vote_time S.E s)
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw
    change X' ∈ (NamedRun.stateBefore S rho i w).st.bodies
    rw [← hi]
    exact hX'
  have hX'eq : X' = X :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      X' X hX'run hXrun X' X (Or.inl (Proofs.NamedAncestry.named_self X'))
        (Or.inr (Proofs.NamedAncestry.named_self X)) (by
          rw [← Proofs.NamedWire.erase_root X', ← Proofs.NamedWire.erase_root X, hX'erase])
  have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime
    S rho (Protocol.vote_time S.E s) w X (by simpa only [hX'eq] using hX')
  simpa only [Internal.NamedRecoveryRead.voteDutyRead,
    NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom,
    Protocol.NamedStore.setClock] using congrArg (fun st => st.h) hview

#print axioms storedHeight_of_runBlock_mem_voteDutyRead

/-- The named prepared-read analogue of earlier's
`candidatePath_of_processedBandDescendant`. A processed descendant at the
reader's own height band makes the protected block, and every strict block
between the reader's anchor and it, a frozen vote candidate. The retired
reachability inputs of earlier's proof are replaced by the  named store
exports. -/
theorem namedCandidatePath_of_processedBandDescendant_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot} {C D : Block V}
    (hCD : Block.Preceq C D)
    (hDprocessed : D ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s)
    (hband : (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.h_max - 1 ≤
      ((Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.σ D).h)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) C) :
    C ∈ voterCandidateTreeAt S rho w (s + 1) ∧
      ∀ B : Block V,
        Block.Preceq (voterAnchorAt S rho w (s + 1)) B →
        B ≠ voterAnchorAt S rho w (s + 1) →
        Block.Preceq B C → B ≠ C →
        B ∈ voterCandidateTreeAt S rho w (s + 1) := by
  let read := Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)
  have hDread : D ∈ Protocol.voter_processed_block_tree S.E
      read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s := by
    simpa only [read, Internal.NamedRecoveryRead.voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using hDprocessed
  have hancestor : ∀ B : Block V, Block.Preceq B D →
      B ∈ Protocol.voter_processed_block_tree S.E
        read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s := by
    intro B hBD
    have hanc := WeakGoldfish.ancestorProcessed_of_voterProcessed
      S adm hw (s := s) (B := D) hDprocessed B hBD
    simpa only [read, Internal.NamedRecoveryRead.voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using hanc
  have hFroot : Block.Preceq read.st.core.F
      (Protocol.get_fg_root read.st.core.toHealing.toFG) :=
    Proofs.Records.preceq_get_fg_root_of_F
      (st := read.st.core.toHealing.toFG) (by
        simpa only [read, Internal.NamedRecoveryRead.voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock] using
            (Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
              S rho (Protocol.vote_time S.E (s + 1)) w))
  have hmem : ∀ B : Block V,
      Block.Preceq (Protocol.get_fg_root read.st.core.toHealing.toFG) B →
      Block.Preceq B C →
      B ∈ voterCandidateTreeAt S rho w (s + 1) := by
    intro B hrootB hBC
    change B ∈ Protocol.get_filtered_block_tree_from
      read.st.core.toHealing.toFG
      (Protocol.voter_processed_block_tree S.E
        read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
    simp only [Protocol.get_filtered_block_tree_from,
      Protocol.viable_tree, Protocol.finalized_descendants,
      Protocol.viable, Finset.mem_filter, decide_eq_true_eq]
    exact ⟨⟨⟨hancestor B (Block.preceq_trans hBC hCD),
      Block.preceq_trans hFroot hrootB⟩,
      D, hDread, Block.preceq_trans hBC hCD, hband⟩, hrootB⟩
  refine ⟨hmem C hroot (Block.preceq_self C), ?_⟩
  intro B hAB _ hBC _
  have hrootAnchor : Block.Preceq
      (Protocol.get_fg_root read.st.core.toHealing.toFG)
      (voterAnchorAt S rho w (s + 1)) :=
    NamedOutageClosure.fg_root_preceq_anchor S.E S.hc
      read.st.core.toHealing (S.hc.round_of read.st.core.s)
      (DecoupledConsensusModel.Protocol.readFrame read.cache read.st.core.toHealing
        (S.hc.round_of read.st.core.s)).g1
  exact hmem B (Block.preceq_trans hrootAnchor hAB) hBC

theorem namedCandidatePath_of_processedBandDescendant
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot} {C D : Block V}
    (hCD : Block.Preceq C D)
    (hDprocessed : D ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s)
    (hband : (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.h_max - 1 ≤
      ((Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.σ D).h)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) C) :
    C ∈ voterCandidateTreeAt S rho w (s + 1) ∧
      ∀ B : Block V,
        Block.Preceq (voterAnchorAt S rho w (s + 1)) B →
        B ≠ voterAnchorAt S rho w (s + 1) →
        Block.Preceq B C → B ≠ C →
        B ∈ voterCandidateTreeAt S rho w (s + 1) :=
  namedCandidatePath_of_processedBandDescendant_core
    S adm.toNamedAdmissibleCore hw hCD hDprocessed hband hroot

#print axioms namedCandidatePath_of_processedBandDescendant_core

#print axioms namedCandidatePath_of_processedBandDescendant






/- The delivery-parametric action induction is the prepared counterpart of
earlier's `goldfishCone_succ_of_priorConfirmationSafety_at_historyCut` route.
The carrier token is formed at each action round from the preceding rows and
The current action FG root. -/
theorem actionSources_preceq_of_priorConfirmations_and_historyCut_of_delivery
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {cap : Time} (hdelivery : NamedHealthyPrefixDelivery S rho cap)
    (hcapHor : cap ≤ rho.horizon)
    (hmajority : HonestWeightMajority S rho.honest)
    {base cut : Round} {s : Slot} {D : Block V}
    (hspan : base ≤ cut - S.hc.η_SG)
    (hbootstrap : ∀ r, base ≤ r → r < cut →
      S.a r < Protocol.vote_time S.E (s + 1) → ∀ w ∈ rho.honest,
      NamedRun.emits S rho w
        (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
      Block.Preceq (actionSGBlockAt S rho w r) D)
    (hprior : ∀ q, S.hc.opening_slot cut ≤ q → q < s →
      ∀ v ∈ rho.honest, ∀ C,
      GenuineConfirmationWith
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadAt S rho v
            (Protocol.confirmation_time S.E q)).cache)
        S.E S.hc (confStore S rho v q) q C →
      Block.Preceq C D)
    (hlegacyRoots : ∀ r, cut ≤ r →
      S.a r < Protocol.vote_time S.E (s + 1) → ∀ w ∈ rho.honest,
      ∀ (C : NamedBlock V) (a : NamedAttestation V),
      let R := Protocol.get_fg_root
        (actionStoreAt S rho w r).st.core.toHealing.toFG
      C ∈ (actionStoreAt S rho w r).st.bodies →
      (Protocol.derive_named S.E S.cfg C).J = R →
      a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index
        (Object.attest a) (S.a a.round) →
      a.round < cut →
      a.height_pair.erase = HeightPair.target
        (Protocol.derive_named S.E S.cfg C).h_j
        (Protocol.derive_named S.E S.cfg C).J.root →
      fgConfirmationWitness S
        (actionStoreAt S rho a.val_index a.round) = some R →
      Block.Preceq R D)
    (hawake : ∀ r, cut ≤ r → 0 < r →
      S.a r < Protocol.vote_time S.E (s + 1) →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hcapDomain : ∀ r, cut ≤ r → 0 < r →
      S.a r < Protocol.vote_time S.E (s + 1) → ∀ p,
      DecoupledConsensusModel.Protocol.domain S.E S.hc r p ≤ cap) :
    ∀ r, base ≤ r → S.a r < Protocol.vote_time S.E (s + 1) →
      (∀ w ∈ rho.honest,
        NamedRun.emits S rho w
          (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
          Block.Preceq (actionSGBlockAt S rho w r) D) ∧
      (cut ≤ r → ∀ w ∈ rho.honest,
        Block.Preceq
          (Protocol.get_fg_root
            (actionStoreAt S rho w r).st.core.toHealing.toFG) D ∧
        ∀ T, fgConfirmationWitness S
            (actionStoreAt S rho w r) = some T →
          Block.Preceq T D) := by
  have hbaseCut : base ≤ cut := hspan.trans (Nat.sub_le _ _)
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
      intro hbase haction
      by_cases hboot : r < cut
      · refine ⟨hbootstrap r hbase hboot haction, ?_⟩
        intro hcut
        exact False.elim (Nat.not_lt_of_ge hcut hboot)
      · have hcut : cut ≤ r := Nat.le_of_not_gt hboot
        have hsg : ∀ k, base ≤ k → k < r → ∀ v ∈ rho.honest,
            NamedRun.emits S rho v
              (Object.attest (actionAttestationAt S rho v k)) (S.a k) →
            Block.Preceq (actionSGBlockAt S rho v k) D := by
          intro k hk hkr
          exact (ih k hkr hk
            ((Assembly.a_mono S (Nat.le_of_lt hkr)).trans_lt haction)).1
        have hroots : ∀ w ∈ rho.honest,
            Block.Preceq
              (Protocol.get_fg_root
                (actionStoreAt S rho w r).st.core.toHealing.toFG) D := by
          intro w hw
          rcases WeakFG.fgRoot_confirmationWitness_at_action S adm hmajority hw r with
              hgen | ⟨C, hC, hJ, a, ha, hemit, har, hpair, hT⟩
          · rw [hgen]
            exact Protocol.preceq_genesis D
          · by_cases haold : a.round < cut
            · exact hlegacyRoots r hcut haction w hw C a hC hJ
                ha hemit haold hpair hT
            · have harecent : cut ≤ a.round := Nat.le_of_not_gt haold
              exact ((ih a.round har (hbaseCut.trans harecent)
                ((Assembly.a_mono S har.le).trans_lt haction)).2
                  harecent a.val_index ha).2 _ hT
        by_cases hrzero : r = 0
        · subst r
          constructor
          · intro w hw hemit
            rw [WeakGenesis.actionSGBlock_eq_genesis_zero S adm hmajority hw]
            exact Protocol.preceq_genesis D
          · intro _ w hw
            refine ⟨hroots w hw, ?_⟩
            intro T hT
            rw [WeakGenesis.fgConfirmationWitness_zero S adm w] at hT
            cases hT
        · have hrpos : 0 < r := Nat.pos_of_ne_zero hrzero
          have hwindowStart : base ≤ r - S.hc.η_SG :=
            hspan.trans (Nat.sub_le_sub_right hcut _)
          have hlive : ∀ w ∈ rho.honest,
              Block.Preceq (actionStoreAt S rho w r).live_confirmed D := by
            intro w hw
            rcases actionStoreAt_liveConfirmed_genuine_or_fgRoot S rho w r with
                ⟨C, hC, hEq⟩ | ⟨R, hR, hEq⟩
            · rw [← hEq]
              exact hprior (S.hc.opening_slot r)
                (Nat.mul_le_mul_right S.hc.R hcut)
                (Nat.lt_of_succ_le (openingNext_le_of_action_before_nextVote S haction))
                w hw C (by
                  simpa only [Setup.a, Protocol.a_eq_confirmation_time] using hC)
            · rw [← hEq, hR]
              have hroot := hroots w hw
              rw [actionStoreAt_fgRoot_eq_openingConfStore] at hroot
              exact hroot
          have hform : ActionGradeFormationAt S rho r :=
            actionGradeFormationAt_of_awakeWindowMajority S adm hrpos
              (hawake r hcut hrpos haction)
              (fun p hp => relativeGradeCarrierAt_of_awakeWindowMajority S adm hrpos
                (hawake r hcut hrpos haction)
                (relativeCarrierWindowAt_of_awakeWindowHistory_of_delivery
                  S adm hdelivery hcapHor hrpos hwindowStart
                  (hawake r hcut hrpos haction) hsg hroots p
                  (hcapDomain r hcut hrpos haction p)))
          constructor
          · intro w hw hemit
            rcases hform.action w hw hemit with
                hpre | heq | ⟨k, hk, v, hv, hem, hpre⟩
            · exact Block.preceq_trans hpre (hlive w hw)
            · exact heq ▸ hroots w hw
            · exact Block.preceq_trans hpre
                (hsg k (hwindowStart.trans (WeakSG.mem_latestWindow_lower_bound hk))
                  (mem_latestWindow_lt hk) v hv hem)

          · intro _ w hw
            refine ⟨hroots w hw, ?_⟩
            intro T hT
            rcases hform.witness w hw T hT with
                hpre | ⟨k, hk, v, hv, hem, hpre⟩
            · exact Block.preceq_trans hpre (hlive w hw)
            · exact Block.preceq_trans hpre
                (hsg k (hwindowStart.trans (WeakSG.mem_latestWindow_lower_bound hk))
                  (mem_latestWindow_lt hk) v hv hem)

#print axioms actionSources_preceq_of_priorConfirmations_and_historyCut_of_delivery
theorem actionSources_preceq_of_priorConfirmations_and_historyCut_w
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {lo cap : Time} (hdelivery : NamedHealthyWindowDelivery S rho lo cap)
    (hgstLo : S.E.t_GST ≤ lo)
    (hcapHor : cap ≤ rho.horizon)
    (hmajority : HonestWeightMajority S rho.honest)
    {base cut : Round} {s : Slot} {D : Block V}
    (hspan : base ≤ cut - S.hc.η_SG)
    (hsendLo : ∀ k, base ≤ k → lo ≤ S.a k)
    (hbootstrap : ∀ r, base ≤ r → r < cut →
      S.a r < Protocol.vote_time S.E (s + 1) → ∀ w ∈ rho.honest,
      NamedRun.emits S rho w
        (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
      Block.Preceq (actionSGBlockAt S rho w r) D)
    (hprior : ∀ q, S.hc.opening_slot cut ≤ q → q < s →
      ∀ v ∈ rho.honest, ∀ C,
      GenuineConfirmationWith
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadAt S rho v
            (Protocol.confirmation_time S.E q)).cache)
        S.E S.hc (confStore S rho v q) q C →
      Block.Preceq C D)
    (hlegacyRoots : ∀ r, cut ≤ r →
      S.a r < Protocol.vote_time S.E (s + 1) → ∀ w ∈ rho.honest,
      ∀ (C : NamedBlock V) (a : NamedAttestation V),
      let R := Protocol.get_fg_root
        (actionStoreAt S rho w r).st.core.toHealing.toFG
      C ∈ (actionStoreAt S rho w r).st.bodies →
      (Protocol.derive_named S.E S.cfg C).J = R →
      a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index
        (Object.attest a) (S.a a.round) →
      a.round < cut →
      a.height_pair.erase = HeightPair.target
        (Protocol.derive_named S.E S.cfg C).h_j
        (Protocol.derive_named S.E S.cfg C).J.root →
      fgConfirmationWitness S
        (actionStoreAt S rho a.val_index a.round) = some R →
      Block.Preceq R D)
    (hawake : ∀ r, cut ≤ r → 0 < r →
      S.a r < Protocol.vote_time S.E (s + 1) →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hcapDomain : ∀ r, cut ≤ r → 0 < r →
      S.a r < Protocol.vote_time S.E (s + 1) → ∀ p,
      DecoupledConsensusModel.Protocol.domain S.E S.hc r p ≤ cap) :
    ∀ r, base ≤ r → S.a r < Protocol.vote_time S.E (s + 1) →
      (∀ w ∈ rho.honest,
        NamedRun.emits S rho w
          (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
          Block.Preceq (actionSGBlockAt S rho w r) D) ∧
      (cut ≤ r → ∀ w ∈ rho.honest,
        Block.Preceq
          (Protocol.get_fg_root
            (actionStoreAt S rho w r).st.core.toHealing.toFG) D ∧
        ∀ T, fgConfirmationWitness S
            (actionStoreAt S rho w r) = some T →
          Block.Preceq T D) := by
  have hbaseCut : base ≤ cut := hspan.trans (Nat.sub_le _ _)
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
      intro hbase haction
      by_cases hboot : r < cut
      · refine ⟨hbootstrap r hbase hboot haction, ?_⟩
        intro hcut
        exact False.elim (Nat.not_lt_of_ge hcut hboot)
      · have hcut : cut ≤ r := Nat.le_of_not_gt hboot
        have hsg : ∀ k, base ≤ k → k < r → ∀ v ∈ rho.honest,
            NamedRun.emits S rho v
              (Object.attest (actionAttestationAt S rho v k)) (S.a k) →
            Block.Preceq (actionSGBlockAt S rho v k) D := by
          intro k hk hkr
          exact (ih k hkr hk
            ((Assembly.a_mono S (Nat.le_of_lt hkr)).trans_lt haction)).1
        have hroots : ∀ w ∈ rho.honest,
            Block.Preceq
              (Protocol.get_fg_root
                (actionStoreAt S rho w r).st.core.toHealing.toFG) D := by
          intro w hw
          rcases WeakFG.fgRoot_confirmationWitness_at_action S adm hmajority hw r with
              hgen | ⟨C, hC, hJ, a, ha, hemit, har, hpair, hT⟩
          · rw [hgen]
            exact Protocol.preceq_genesis D
          · by_cases haold : a.round < cut
            · exact hlegacyRoots r hcut haction w hw C a hC hJ
                ha hemit haold hpair hT
            · have harecent : cut ≤ a.round := Nat.le_of_not_gt haold
              exact ((ih a.round har (hbaseCut.trans harecent)
                ((Assembly.a_mono S har.le).trans_lt haction)).2
                  harecent a.val_index ha).2 _ hT
        by_cases hrzero : r = 0
        · subst r
          constructor
          · intro w hw hemit
            rw [WeakGenesis.actionSGBlock_eq_genesis_zero S adm hmajority hw]
            exact Protocol.preceq_genesis D
          · intro _ w hw
            refine ⟨hroots w hw, ?_⟩
            intro T hT
            rw [WeakGenesis.fgConfirmationWitness_zero S adm w] at hT
            cases hT
        · have hrpos : 0 < r := Nat.pos_of_ne_zero hrzero
          have hwindowStart : base ≤ r - S.hc.η_SG :=
            hspan.trans (Nat.sub_le_sub_right hcut _)
          have hlive : ∀ w ∈ rho.honest,
              Block.Preceq (actionStoreAt S rho w r).live_confirmed D := by
            intro w hw
            rcases actionStoreAt_liveConfirmed_genuine_or_fgRoot S rho w r with
                ⟨C, hC, hEq⟩ | ⟨R, hR, hEq⟩
            · rw [← hEq]
              exact hprior (S.hc.opening_slot r)
                (Nat.mul_le_mul_right S.hc.R hcut)
                (Nat.lt_of_succ_le (openingNext_le_of_action_before_nextVote S haction))
                w hw C (by
                  simpa only [Setup.a, Protocol.a_eq_confirmation_time] using hC)
            · rw [← hEq, hR]
              have hroot := hroots w hw
              rw [actionStoreAt_fgRoot_eq_openingConfStore] at hroot
              exact hroot
          have hform : ActionGradeFormationAt S rho r :=
            actionGradeFormationAt_of_awakeWindowMajority S adm hrpos
              (hawake r hcut hrpos haction)
              (fun p hp => relativeGradeCarrierAt_of_awakeWindowMajority S adm hrpos
                (hawake r hcut hrpos haction)
                (relativeCarrierWindowAt_of_awakeWindowHistory_w
                  S adm hdelivery hgstLo hcapHor hrpos hwindowStart
                  (fun k hk _ => hsendLo k hk)
                  (hawake r hcut hrpos haction) hsg hroots p
                  (hcapDomain r hcut hrpos haction p)))
          constructor
          · intro w hw hemit
            rcases hform.action w hw hemit with
                hpre | heq | ⟨k, hk, v, hv, hem, hpre⟩
            · exact Block.preceq_trans hpre (hlive w hw)
            · exact heq ▸ hroots w hw
            · exact Block.preceq_trans hpre
                (hsg k (hwindowStart.trans (WeakSG.mem_latestWindow_lower_bound hk))
                  (mem_latestWindow_lt hk) v hv hem)

          · intro _ w hw
            refine ⟨hroots w hw, ?_⟩
            intro T hT
            rcases hform.witness w hw T hT with
                hpre | ⟨k, hk, v, hv, hem, hpre⟩
            · exact Block.preceq_trans hpre (hlive w hw)
            · exact Block.preceq_trans hpre
                (hsg k (hwindowStart.trans (WeakSG.mem_latestWindow_lower_bound hk))
                  (mem_latestWindow_lt hk) v hv hem)


#print axioms actionSources_preceq_of_priorConfirmations_and_historyCut_w

/-/ The prepared-read twin of earlier's successor. Recent frontier rows come
    from the action induction; old rows remain the only frontier callback. -/


















end WeakJoint
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
