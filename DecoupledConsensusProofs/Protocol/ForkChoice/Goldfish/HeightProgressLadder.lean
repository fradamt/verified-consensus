module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.FixedHeightRootAdmission
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FixedHeightRootPreparedParent
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FixedRootGradePersistence
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradePersistence
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightProgressSeedRegime
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RawHeightActiveEliminator
public import DecoupledConsensusProofs.Execution.RecoveryGradeProcessedRead
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGProposalLifecycle
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RawExactHeightSeed
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.ChainState.CheckpointHeights
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Execution.Wire

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Height-progress ladder leaves

This module records local consequences of the fixed-root Claim-4 records. The
lifecycle proposal has height at the fixed frontier or one below it, a
thin-window common grade persists while the same fixed root and frontier remain
at every honest action read, and an exact-frontier attempt after rebasing onto
the first fixed target must increase the honest frontier.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}



private theorem namedParent_preceq_of_parent?
    {B P : NamedBlock V} (h : NamedBlock.parent? B = some P) :
    NamedBlock.Preceq P B := by
  cases B with
  | genesis => cases h
  | node parent slot root votes support rows proposer =>
      have hparent : parent = P := Option.some.inj h
      subst P
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
      exact Or.inr (Proofs.NamedAncestry.named_self parent)



/-- A persisted named grade gives the named ancestry used by Rule A at a later
lifecycle opening. The action-read activity is explicit under the frame
runtime. -/
theorem opening_timeoutMature_of_persistedGrade
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hdelay : TimeoutDelayBound S delayExtra)
    {entry proposal : Round} {B Q P : NamedBlock V}
    (hentry : 0 < entry)
    (hspace : entry + 2 + delayExtra ≤ proposal)
    (hentryBlock : proposedBlockAt S rho (S.hc.opening_slot entry) = some B)
    (hBRun : RunBlock S rho B)
    (hforms : NamedGradeFormsAt S rho (proposal - 1) B.erase)
    (hactive : B.erase ∈
      PhaseGrades.filteredTree (actionReadAt S rho
        (S.E.proposer (S.hc.opening_slot proposal)) (proposal - 1)))
    (hactionHor : S.a (proposal - 1) ≤ rho.horizon)
    (hpacket : NamedSGProposalLifecyclePacket S rho (proposal - 1)
      (S.hc.opening_slot proposal - 1) Q)
    (hparent : NamedBlock.parent? Q = some P)
    (hsameHeight : (Protocol.derive_named S.E S.cfg P).h =
      (Protocol.derive_named S.E S.cfg B).h) :
    ProposalTimeoutMatureAt S rho (S.hc.opening_slot proposal) := by
  have hentrySucc : entry + 1 ≤ entry + 2 + delayExtra := by
    exact (Nat.add_le_add_left (by decide : 1 ≤ 2) entry).trans
      (Nat.le_add_right (entry + 2) delayExtra)
  have hproposal : 0 < proposal :=
    (Nat.zero_lt_succ entry).trans_le (hentrySucc.trans hspace)
  have hproposalTwo : 2 ≤ proposal := by
    exact (Nat.le_add_left 2 entry).trans
      ((Nat.le_add_right (entry + 2) delayExtra).trans hspace)
  have hpred : proposal - 1 + 1 = proposal := Nat.sub_add_cancel hproposal
  have hproposalQ :
      proposedBlockAt S rho (S.hc.opening_slot proposal) = some Q := by
    simpa only [hpred] using hpacket.lifecycle.proposal
  let v := S.E.proposer (S.hc.opening_slot proposal)
  have hv : v ∈ rho.honest := by
    simpa only [v, hpred] using hpacket.lifecycle.proposerHonest
  have htarget : Block.Preceq
      (actionSGBlockAt S rho v (proposal - 1)) P.erase := by
    obtain ⟨P', hP', hP'erase⟩ :=
      proposedBlockAt_parent S rho (S.hc.opening_slot proposal)
        hproposalQ
    have hP'eq : P' = P := Option.some.inj (hP'.symm.trans hparent)
    subst P'
    rw [hP'erase]
    simpa only [hpred] using hpacket.actionTargetParent v hv
  have hBtarget : Block.Preceq B.erase P.erase :=
    Block.preceq_trans
      (preceq_actionSGBlockAt_of_namedGradeFormsAt
        (r := proposal - 1) S adm.toNamedAdmissibleCore
          (Nat.sub_pos_of_lt (Nat.lt_of_succ_le hproposalTwo))
          hactionHor hforms hv hactive)
      htarget
  obtain ⟨B', hB'P, hB'erase⟩ :=
    Proofs.NamedAncestry.erased_ancestor_lift P hBtarget
  have hPrun : RunBlock S rho P :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hpacket.lifecycle.runBlock
      (namedParent_preceq_of_parent? hparent)
  have hB'run : RunBlock S rho B' :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hPrun hB'P
  have hrootEq : B'.root = B.root := by
    rw [← Proofs.NamedWire.erase_root B', ← Proofs.NamedWire.erase_root B, hB'erase]
  have hB'eq : B' = B :=
    adm.toNamedRootCollisionFree.root_injective B' B hB'run hBRun B' B
      (Or.inl (Proofs.NamedAncestry.named_self B'))
      (Or.inr (Proofs.NamedAncestry.named_self B)) hrootEq
  exact laterOpening_timeoutMature_of_sameHeight
    S adm hdelay hentry hspace hentryBlock hproposalQ hparent
      (by simpa only [hB'eq] using hB'P) hsameHeight

#print axioms opening_timeoutMature_of_persistedGrade

/-- A named exact-frontier attempt rebased above the fixed justification target
must raise the public frontier. The two retention inputs are the named-runtime
form required by the active-opening eliminator. -/
theorem exactHeightAttempt_rise_of_rebased
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {u : V} {read0 : Time}
    (hroot : FixedHeightJustificationRootAtRead S rho M u read0)
    {q : Round} (hq : 0 < q) {B : NamedBlock V}
    (hcarrier : ProposerCarrierAt S rho q)
    (hformsPrev : NamedGradeFormsAt S rho (q - 1) B.erase)
    (hwindowPrev : ∀ w ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho w (S.a (q - 1)) B.erase)
    (hdomainWindow : ∀ w ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho w
        (DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2) B.erase)
    (hBRun : RunBlock S rho B)
    (hBheight : (Protocol.derive_named S.E S.cfg B).h = M)
    (hpostPrev : S.E.t_GST ≤ S.a (q - 1))
    (hmature : ProposalTimeoutMatureAt S rho (S.hc.opening_slot q))
    (hactiveAtAction : ∀ w ∈ rho.honest,
      B.erase ∈ Protocol.get_filtered_block_tree
        (healStoreAt S rho w q).toFG)
    (hJB : Block.Preceq (rho.storeBeforeTime S u read0).J B.erase)
    {endpoint : Time} (hactionEnd : S.a q ≤ endpoint)
    (hendHor : endpoint ≤ rho.horizon) :
    M < honestHMaxAt S rho endpoint := by
  rcases activeExactHeightOpening_fixedInterference_or_hMaxRise
      S adm hfb hq hcarrier hformsPrev hwindowPrev hdomainWindow hBRun
        hBheight hpostPrev hmature hactiveAtAction hactionEnd hendHor with
    hrise | hfixed
  · exact hrise
  · exact False.elim
      (hroot.fixedTarget.not_again_after_target_rebase adm
        hfixed.1.fixedTarget hJB)

#print axioms exactHeightAttempt_rise_of_rebased



/-- A fixed-root block that formed a named grade remains active at later action
reads while the exact root and frontier stay fixed. -/
private theorem fixedRootGrade_mem_filtered_action_of_noRise
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {M : Height} {u : V} {read0 : Time} {base q : Round}
    {B : NamedBlock V}
    (hseed : NamedGradeFormsAt S rho base B.erase)
    (hbase : base ≤ q)
    (hBRun : RunBlock S rho B)
    (hJB : Block.Preceq (rho.storeBeforeTime S u read0).J B.erase)
    (hBheight : M - 1 ≤ (Protocol.derive_named S.E S.cfg B).h)
    (hfixed : ∀ v ∈ rho.honest,
      Protocol.get_fg_root
          (rho.storeBeforeTime S v (S.a q)).toHealing.toFG =
        (rho.storeBeforeTime S u read0).J ∧
      (rho.storeBeforeTime S v (S.a q)).h_max = M) :
    ∀ v ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho v (S.a q) B.erase := by
  intro v hv
  have hprocessed : B.erase ∈
      (rho.storeBeforeTime S v (S.a q)).core.T :=
    namedGradeFormsAt_processedAtRead_of_action_le
      S adm hseed hv ((action_strictMono S).monotone hbase)
  exact fixedRootGrade_mem_filtered_of_exactRoot
    S adm hv hBRun hprocessed hJB hBheight
      (hfixed v hv).1 (hfixed v hv).2

/-- A common named grade persists through a bounded fixed-root no-rise window,
and the same named block is active at the final action read.

The relative runtime adds one proof-layer timing input: the original fixed-root
read precedes the base action. This lets the fixed-root relay theorem identify
the exact root at every next G2 domain read. -/
theorem gradeFormsAt_persist_of_fixedRoot_noRise
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {u : V} {read0 : Time}
    (hroot : FixedHeightJustificationRootAtRead S rho M u read0)
    {q1 q' : Round} {B : NamedBlock V}
    (hseed : NamedGradeFormsAt S rho (q1 + 1) B.erase)
    (hBRun : RunBlock S rho B)
    (hpostRoot : S.E.t_GST ≤ read0)
    (hreadBase : read0 ≤ S.a q1)
    (hwindow : q1 + 1 ≤ q')
    (hendpoint : S.a q' ≤ rho.horizon)
    (hcapEnd : honestHMaxAt S rho (S.a q') ≤ M)
    (hJB : Block.Preceq (rho.storeBeforeTime S u read0).J B.erase)
    (hBheight : M - 1 ≤ (Protocol.derive_named S.E S.cfg B).h)
    (hfixed : ∀ r', q1 + 1 ≤ r' → r' ≤ q' → ∀ v ∈ rho.honest,
      Protocol.get_fg_root
          (rho.storeBeforeTime S v (S.a r')).toHealing.toFG =
        (rho.storeBeforeTime S u read0).J ∧
      (rho.storeBeforeTime S v (S.a r')).h_max = M) :
    (∀ r', q1 + 1 ≤ r' → r' ≤ q' →
      NamedGradeFormsAt S rho r' B.erase) ∧
    ∀ v ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho v (S.a q') B.erase := by
  have hmajority : HonestWeightMajority S rho.honest :=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S := S) hfb
  have hactiveAction : ∀ r', q1 + 1 ≤ r' → r' ≤ q' →
      ∀ v ∈ rho.honest,
        FinalityFilterRetainedAtRead S rho v (S.a r') B.erase := by
    intro r' hbase hr'end
    exact fixedRootGrade_mem_filtered_action_of_noRise
      S adm hseed hbase hBRun hJB hBheight (hfixed r' hbase hr'end)
  have hforms : ∀ r', q1 + 1 ≤ r' → r' ≤ q' →
      NamedGradeFormsAt S rho r' B.erase := by
    intro r'
    induction r' using Nat.strong_induction_on with
    | h r' ih =>
        intro hbase hr'end
        rcases eq_or_lt_of_le hbase with hEq | hlt
        · subst r'
          exact hseed
        · cases r' with
          | zero => exact (Nat.not_lt_zero _ hlt).elim
          | succ r =>
              have hbasePrev : q1 + 1 ≤ r := Nat.le_of_lt_succ hlt
              have hrendPrev : r ≤ q' := (Nat.le_succ r).trans hr'end
              have hformsPrev : NamedGradeFormsAt S rho r B.erase :=
                ih r (Nat.lt_succ_self r) hbasePrev hrendPrev
              have hq1lt : q1 < r + 1 := by
                exact (Nat.lt_succ_self q1).trans_le hbase
              have hdelay : read0 + S.E.Δ ≤
                  DecoupledConsensusModel.Protocol.domain S.E S.hc (r + 1) .g2 := by
                exact (Int.add_le_add_right hreadBase S.E.Δ).trans
                  ((NamedOutageClosure.action_delta_le_early
                    S S.hc.R_ge_three hq1lt).trans
                    (NamedOutageClosure.early_le_domain S (r + 1)))
              have hdomainAction :
                  DecoupledConsensusModel.Protocol.domain S.E S.hc (r + 1) .g2 ≤
                    S.a (r + 1) :=
                FrameForward.domain_le_a S (r + 1) .g2
              have hactionEnd : S.a (r + 1) ≤ S.a q' :=
                (action_strictMono S).monotone hr'end
              have hdomainHor :
                  DecoupledConsensusModel.Protocol.domain S.E S.hc (r + 1) .g2 ≤
                    rho.horizon :=
                hdomainAction.trans (hactionEnd.trans hendpoint)
              have hdomainCap : honestHMaxAt S rho
                  (DecoupledConsensusModel.Protocol.domain S.E S.hc (r + 1) .g2) ≤ M :=
                (honestHMaxAt_mono S adm.toNamedScheduleWellFormed
                  (hdomainAction.trans hactionEnd)).trans hcapEnd
              have hactiveDomain : ∀ v ∈ rho.honest,
                  B.erase ∈ PhaseGrades.filteredTree
                    (relativeG2Read S rho (r + 1) v) := by
                intro v hv
                exact fixedRootGrade_mem_filteredTree_nextG2_of_noRise
                  S adm hfb hroot hformsPrev hBRun hJB hBheight hpostRoot
                    hdelay hdomainHor hdomainCap hv
              have hcover : ActionCarriersCover S rho r B.erase :=
                by
                  intro v hv
                  exact preceq_actionSGBlockAt_of_namedGradeFormsAt
                    S adm.toNamedAdmissibleCore
                      ((Nat.zero_lt_succ q1).trans_le hbasePrev)
                      (((action_strictMono S).monotone hrendPrev).trans
                        hendpoint)
                      hformsPrev hv (by
                        simpa only [FinalityFilterRetainedAtRead,
                          actionReadAt, Run.storeBeforeTime] using
                          hactiveAction r hbasePrev hrendPrev v hv)
              have hpostPrev : S.E.t_GST ≤ S.a r :=
                hpostRoot.trans
                  (hreadBase.trans ((action_strictMono S).monotone
                    (Nat.le_of_succ_le hbasePrev)))
              have hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon := by
                rw [gammaNeg1_eq_domain_g2_succ S r]
                exact hdomainHor
              have hactiveNext : ∀ v ∈ rho.honest,
                  B.erase ∈ Protocol.get_filtered_block_tree
                    (healStoreAt S rho v (r + 1)).toFG := by
                intro v hv
                simpa only [FinalityFilterRetainedAtRead, healStoreAt] using
                  hactiveAction (r + 1) (by
                    simpa only [Nat.succ_eq_add_one] using
                      Nat.le_of_lt hlt) hr'end v hv
              exact namedGradeFormsAt_succ_of_actionCarriersCover_and_next_active
                S adm hmajority hcover hpostPrev hcut hactiveNext hactiveDomain
  exact ⟨hforms, hactiveAction q' hwindow (Nat.le_refl q')⟩

#print axioms gradeFormsAt_persist_of_fixedRoot_noRise

/-- A fixed-root exact-height attempt after the persisted named grade must raise
the public frontier. -/
theorem exactHeightAttempt_rise_of_rebased_of_fixedRoot_noRise
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {u : V} {read0 : Time}
    (hroot : FixedHeightJustificationRootAtRead S rho M u read0)
    {q1 q : Round} {B : NamedBlock V}
    (hseed : NamedGradeFormsAt S rho (q1 + 1) B.erase)
    (hBRun : RunBlock S rho B)
    (hpostRoot : S.E.t_GST ≤ read0)
    (hreadBase : read0 ≤ S.a q1)
    (hspacing : q1 + 2 ≤ q)
    (hcarrier : ProposerCarrierAt S rho q)
    (hmature : ProposalTimeoutMatureAt S rho (S.hc.opening_slot q))
    (hBheight : (Protocol.derive_named S.E S.cfg B).h = M)
    (hJB : Block.Preceq (rho.storeBeforeTime S u read0).J B.erase)
    (hfixed : ∀ r', q1 + 1 ≤ r' → r' ≤ q → ∀ v ∈ rho.honest,
      Protocol.get_fg_root
          (rho.storeBeforeTime S v (S.a r')).toHealing.toFG =
        (rho.storeBeforeTime S u read0).J ∧
      (rho.storeBeforeTime S v (S.a r')).h_max = M)
    {endpoint : Time} (hactionEnd : S.a q ≤ endpoint)
    (hendHor : endpoint ≤ rho.horizon)
    (hcapEnd : honestHMaxAt S rho endpoint ≤ M) :
    M < honestHMaxAt S rho endpoint := by
  have hstep : q1 + 1 ≤ q1 + 2 :=
    Nat.add_le_add_left (by decide : 1 ≤ 2) q1
  have hbaseQ : q1 + 1 ≤ q := hstep.trans hspacing
  have hq : 0 < q := (Nat.zero_lt_succ q1).trans_le hbaseQ
  have hpred : q - 1 + 1 = q := Nat.sub_add_cancel hq
  have hbasePrev : q1 + 1 ≤ q - 1 :=
    Nat.le_sub_one_of_lt
      ((Nat.add_lt_add_left (by decide : 1 < 2) q1).trans_le hspacing)
  have hprevQ : q - 1 ≤ q := Nat.sub_le q 1
  have hprevAction : S.a (q - 1) ≤ S.a q :=
    (action_strictMono S).monotone hprevQ
  have hprevHor : S.a (q - 1) ≤ rho.horizon :=
    hprevAction.trans (hactionEnd.trans hendHor)
  have hprevCap : honestHMaxAt S rho (S.a (q - 1)) ≤ M :=
    (honestHMaxAt_mono S adm.toNamedScheduleWellFormed
      (hprevAction.trans hactionEnd)).trans hcapEnd
  have hthin : M - 1 ≤ (Protocol.derive_named S.E S.cfg B).h := by
    rw [hBheight]
    exact Nat.sub_le M 1
  obtain ⟨hforms, hwindowPrev⟩ := gradeFormsAt_persist_of_fixedRoot_noRise
    S adm hfb hroot hseed hBRun hpostRoot hreadBase hbasePrev hprevHor
      hprevCap hJB hthin (by
        intro r' hbase hr'end
        exact hfixed r' hbase (hr'end.trans hprevQ))
  have hformsPrev : NamedGradeFormsAt S rho (q - 1) B.erase :=
    hforms (q - 1) hbasePrev (Nat.le_refl _)
  have hpostPrev : S.E.t_GST ≤ S.a (q - 1) :=
    hpostRoot.trans
      (hreadBase.trans ((action_strictMono S).monotone
        ((Nat.le_succ q1).trans hbasePrev)))
  have hdomainAction : DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2 ≤ S.a q :=
    FrameForward.domain_le_a S q .g2
  have hdomainHor : DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2 ≤ rho.horizon :=
    hdomainAction.trans (hactionEnd.trans hendHor)
  have hdomainCap : honestHMaxAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2) ≤ M :=
    (honestHMaxAt_mono S adm.toNamedScheduleWellFormed
      (hdomainAction.trans hactionEnd)).trans hcapEnd
  have hdelay : read0 + S.E.Δ ≤
      DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2 := by
    exact (Int.add_le_add_right hreadBase S.E.Δ).trans
      ((NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
        ((Nat.lt_succ_self q1).trans_le hbaseQ)).trans
        (NamedOutageClosure.early_le_domain S q))
  have hdomainWindow : ∀ v ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho v
        (DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2) B.erase := by
    intro v hv
    have hmem := fixedRootGrade_mem_filteredTree_nextG2_of_noRise
      S adm hfb hroot hformsPrev hBRun hJB hthin hpostRoot
        (by simpa only [hpred] using hdelay)
        (by simpa only [hpred] using hdomainHor)
        (by simpa only [hpred] using hdomainCap) hv
    unfold FinalityFilterRetainedAtRead
    change B.erase ∈ Protocol.get_filtered_block_tree
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2) v).st.core.toHealing.toFG
    simpa only [hpred] using hmem
  have hactive : ∀ v ∈ rho.honest,
      B.erase ∈ Protocol.get_filtered_block_tree
        (healStoreAt S rho v q).toFG := by
    intro v hv
    have hretained := fixedRootGrade_mem_filtered_action_of_noRise
      S adm hseed hbaseQ hBRun hJB hthin
        (hfixed q hbaseQ (Nat.le_refl q)) v hv
    simpa only [FinalityFilterRetainedAtRead, healStoreAt] using hretained
  exact exactHeightAttempt_rise_of_rebased
    S adm hfb hroot hq hcarrier hformsPrev hwindowPrev hdomainWindow
      hBRun hBheight hpostPrev hmature hactive hJB hactionEnd hendHor

#print axioms exactHeightAttempt_rise_of_rebased_of_fixedRoot_noRise


/-
/-- The earlier fixed-root proposer-selection route, restated for named grades and
named derived heights. -/
theorem fixedRoot_opening_parent_preceq_of_gradeFormsAt
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {M: Height} {u: V} {read0: Time}
    (_hroot: FixedHeightJustificationRootAtRead S rho M u read0)
    {q: Round} (hq: 0 < q) {B: NamedBlock V}
    (hcarrier: ProposerCarrierAt S rho q)
    (hformsPrev: NamedGradeFormsAt S rho (q - 1) B.erase)
    (hwindowPrev: ∀ w ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho w (S.a (q - 1)) B.erase)
    (hdomainWindow: ∀ w ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho w
        (DecoupledConsensusModel.Protocol.domain S.E S.hc q.g2) B.erase)
    (hBRun: RunBlock S rho B)
    (hpostPrev: S.E.t_GST ≤ S.a (q - 1))
    (hcut: S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon)
    (hJB: Block.Preceq (rho.storeBeforeTime S u read0).J B.erase)
    (hBheight: (Protocol.derive_named S.E S.cfg B).h = M)
    (hfixedAction: ∀ w ∈ rho.honest,
      Protocol.get_fg_root
          (rho.storeBeforeTime S w (S.a q)).toHealing.toFG =
        (rho.storeBeforeTime S u read0).J ∧
        (rho.storeBeforeTime S w (S.a q)).h_max = M)
    (hrootDuty: Protocol.get_fg_root
      (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot q)).toHealing.toFG =
      (rho.storeBeforeTime S u read0).J)
    (hmaxDuty: (Protocol.proposerDutyStore S rho
      (S.hc.opening_slot q)).h_max = M):
    Block.Preceq B.erase
      (Protocol.proposedParent S rho (S.hc.opening_slot q)):= by
  have hprop: S.E.proposer (S.hc.opening_slot q) ∈ rho.honest:= hcarrier.1
  have hmajority: HonestWeightMajority S rho.honest:=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S:= S) hfb
  have hactiveAction: ∀ w ∈ rho.honest,
      B.erase ∈ Protocol.get_filtered_block_tree
        (healStoreAt S rho w q).toFG:= by
    intro w hw
    have hretained:= fixedRootGrade_mem_filtered_action_of_noRise
      S adm hformsPrev (Nat.sub_le q 1) hBRun hJB
        (by rw [hBheight]; exact Nat.sub_le M 1) (hfixedAction w hw)
    simpa only [FinalityFilterRetainedAtRead, healStoreAt] using hretained
  have hprocessed: B.erase ∈
      (rho.storeBeforeTime S (S.E.proposer (S.hc.opening_slot q))
        (Protocol.proposal_time S.E (S.hc.opening_slot q))).T:= by
    apply gradeFormsAt_processedAtRead_of_action_le S adm hformsPrev hprop
    have hround: q - 1 < q:= Nat.sub_lt hq (by decide)
    have hdelay:= action_add_delta_le_openingProposal_of_round_lt S hround
    exact le_trans (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)) hdelay
  have hrootPre: Protocol.get_fg_root
      (rho.storeBeforeTime S (S.E.proposer (S.hc.opening_slot q))
        (Protocol.proposal_time S.E
          (S.hc.opening_slot q))).core.toHealing.toFG =
      (rho.storeBeforeTime S u read0).J:= by
    simpa only [Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
      Protocol.Store.toHealing, Protocol.NamedStore.toHealing,
      Protocol.get_fg_root] using hrootDuty
  have hmaxPre: (rho.storeBeforeTime S
      (S.E.proposer (S.hc.opening_slot q))
      (Protocol.proposal_time S.E (S.hc.opening_slot q))).core.h_max = M:= by
    simpa only [Protocol.proposerDutyStore, Proofs.Optimistic.tickStore] using hmaxDuty
  have hactivePre: B.erase ∈ Protocol.get_filtered_block_tree
      (rho.storeBeforeTime S (S.E.proposer (S.hc.opening_slot q))
        (Protocol.proposal_time S.E
          (S.hc.opening_slot q))).core.toHealing.toFG:=
    fixedRootGrade_mem_filtered_of_exactRoot S adm hprop hBRun hprocessed hJB
      (by rw [hBheight]; exact Nat.sub_le M 1) hrootPre hmaxPre
  have hactiveDuty: B.erase ∈ Protocol.get_filtered_block_tree
      (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot q)).toHealing.toFG:= by
    simpa only [Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
      Protocol.Store.toHealing, Protocol.NamedStore.toHealing] using hactivePre
  have hG1:= proposerG1_of_gradeFormsAt_prev_and_active
    S adm hmajority hq hformsPrev hwindowPrev hdomainWindow hpostPrev hcut
      hactiveAction hprop hactiveDuty
  exact proposedParent_preceq_of_proposerG1 S hactiveDuty hG1

/-- The fixed-root named ancestry gives the configured Rule-A timeout at the
later opening. -/
theorem fixedRoot_timeoutMature_of_exactLifecycleGrade
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest) (hdelay: TimeoutDelayBound S delayExtra)
    {M: Height} {u: V} {read0: Time}
    (hroot: FixedHeightJustificationRootAtRead S rho M u read0)
    {entry q: Round} {B P Q: NamedBlock V}
    (hentry: 0 < entry) (hspace: entry + 2 + delayExtra ≤ q)
    (hentryBlock: proposedBlockAt S rho
      (S.hc.opening_slot entry) = some B)
    (hq: 0 < q) (hcarrier: ProposerCarrierAt S rho q)
    (hformsPrev: NamedGradeFormsAt S rho (q - 1) B.erase)
    (hwindowPrev: ∀ w ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho w (S.a (q - 1)) B.erase)
    (hdomainWindow: ∀ w ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho w
        (DecoupledConsensusModel.Protocol.domain S.E S.hc q.g2) B.erase)
    (hBRun: RunBlock S rho B)
    (hpostPrev: S.E.t_GST ≤ S.a (q - 1))
    (hcut: S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon)
    (hJB: Block.Preceq (rho.storeBeforeTime S u read0).J B.erase)
    (hBheight: (Protocol.derive_named S.E S.cfg B).h = M)
    (hfixedAction: ∀ w ∈ rho.honest,
      Protocol.get_fg_root
          (rho.storeBeforeTime S w (S.a q)).toHealing.toFG =
        (rho.storeBeforeTime S u read0).J ∧
        (rho.storeBeforeTime S w (S.a q)).h_max = M)
    (hrootDuty: Protocol.get_fg_root
      (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot q)).toHealing.toFG =
      (rho.storeBeforeTime S u read0).J)
    (hmaxDuty: (Protocol.proposerDutyStore S rho
      (S.hc.opening_slot q)).h_max = M)
    (hproposalBlock: proposedBlockAt S rho
      (S.hc.opening_slot q) = some Q)
    (hparent: NamedBlock.parent? Q = some P)
    (hsameHeight: (Protocol.derive_named S.E S.cfg P).h =
      (Protocol.derive_named S.E S.cfg B).h):
    ProposalTimeoutMatureAt S rho (S.hc.opening_slot q):= by
  have hBParent:= fixedRoot_opening_parent_preceq_of_gradeFormsAt
    S adm hfb hroot hq hcarrier hformsPrev hwindowPrev hdomainWindow hBRun
      hpostPrev hcut hJB hBheight hfixedAction hrootDuty hmaxDuty
  obtain ⟨P', hP'parent, hP'erase⟩:=
    proposedBlockAt_parent S rho (S.hc.opening_slot q) hproposalBlock
  have hP'eq: P' = P:= Option.some.inj (hP'parent.symm.trans hparent)
  subst P'
  have hBPErase: Block.Preceq B.erase P.erase:= by
    rw [hP'erase]
    exact hBParent
  obtain ⟨B', hB'P, hB'erase⟩:= Proofs.NamedAncestry.erased_ancestor_lift P hBPErase
  have hPRun: RunBlock S rho P:=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho
      (proposedBlockAt_blockInRun_of_admissible S adm q hproposalBlock)
      (namedParent_preceq_of_parent? hparent)
  have hB'Run: RunBlock S rho B':=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hPRun hB'P
  have hrootEq: B'.root = B.root:= by
    rw [← Proofs.NamedWire.erase_root B', ← Proofs.NamedWire.erase_root B, hB'erase]
  have hB'eq: B' = B:=
    adm.toNamedRootCollisionFree.root_injective B' B hB'Run hBRun B' B
      (Or.inl (Proofs.NamedAncestry.named_self B'))
      (Or.inr (Proofs.NamedAncestry.named_self B)) hrootEq
  exact laterOpening_timeoutMature_of_sameHeight
    S adm hdelay hentry hspace hentryBlock hproposalBlock hparent
      (by simpa only [hB'eq] using hB'P) hsameHeight

#print axioms fixedRoot_opening_parent_preceq_of_gradeFormsAt
#print axioms fixedRoot_timeoutMature_of_exactLifecycleGrade
-/

private theorem fixedRoot_namedGradeFormsAt_round_pos
    (S : Setup V) {rho : Run V} {q : Round} {P : Block V}
    (hforms : NamedGradeFormsAt S rho q P)
    (hnonempty : rho.honest.Nonempty) : 0 < q := by
  by_contra hq
  have hq0 : q = 0 := Nat.eq_zero_of_not_pos hq
  obtain ⟨v, hv⟩ := hnonempty
  have hgrade := (hforms v hv).2
  rw [hq0] at hgrade
  simp [Internal.PhaseGrades.storeGrade, Internal.PhaseGrades.phaseGrade,
    DecoupledConsensusModel.Protocol.gradeBool, DecoupledConsensusModel.Protocol.positive,
    DecoupledConsensusModel.Protocol.opposing, DecoupledConsensusModel.Protocol.readyView,
    DecoupledConsensusModel.Protocol.rawView, DecoupledConsensusModel.Protocol.interpretedInputs,
    DecoupledConsensusModel.Protocol.rawInputs, DecoupledConsensusModel.Protocol.Supports,
    DecoupledConsensusModel.Protocol.Opposes, DecoupledConsensusModel.Protocol.CleanFrom,
    Protocol.latest_window_zero, Electorate.weightOf] at hgrade

/-- A named grade lies below the fixed-root prepared proposal parent through
the preceding action carrier. -/
theorem fixedRoot_opening_parent_preceq_of_gradeFormsAt
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {u : V} {read0 : Time}
    (hroot : FixedHeightJustificationRootAtRead S rho M u read0)
    {q : Round} {A B : Block V} (hq : 0 < q)
    (hforms : NamedGradeFormsAt S rho (q - 1) B)
    (hactive : ∀ v ∈ rho.honest,
      B ∈ Internal.PhaseGrades.filteredTree
        (actionReadAt S rho v (q - 1)))
    (hlock : SGTargetOpeningConeRootLock S rho M (q - 1)
      (S.hc.opening_slot q - 1))
    (hpostRead : S.E.t_GST ≤ read0)
    (hproposalDelay : read0 + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hproposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hproposalCap : honestHMaxAt S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) ≤ M)
    (hpostCone : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot q - 1))
    (hpostPreviousAction : S.E.t_GST ≤ S.a (q - 1))
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hanchor : Protocol.fresh_anchor S.E S.hc
      (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot q)).toHealing q = some A) :
    Block.Preceq B (proposedParent S rho (S.hc.opening_slot q)) := by
  obtain ⟨v, hv⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
  have hqPrev : 0 < q - 1 := fixedRoot_namedGradeFormsAt_round_pos
    S hforms ⟨v, hv⟩
  have hactionHor : S.a (q - 1) ≤ rho.horizon := by
    have hprevLt : q - 1 < q := Nat.sub_lt hq (by decide)
    have hdelay := action_add_delta_le_openingProposal_of_round_lt S hprevLt
    exact (le_trans (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos))
      hdelay).trans hproposalHor
  have hBTarget : Block.Preceq B (actionSGBlockAt S rho v (q - 1)) :=
    preceq_actionSGBlockAt_of_namedGradeFormsAt
      S adm.toNamedAdmissibleCore hqPrev hactionHor hforms hv (hactive v hv)
  have htargetParent :=
    actionTarget_preceq_preparedOpeningParent_of_fixedRootLock
      S adm hcom hfb hroot hq hlock hpostRead hproposalDelay hproposalHor
      hproposalCap hpostCone hpostPreviousAction hprop hanchor v hv
  exact Block.preceq_trans hBTarget htargetParent




end HealingSurface
end Proofs
end DecoupledConsensusModel

end
