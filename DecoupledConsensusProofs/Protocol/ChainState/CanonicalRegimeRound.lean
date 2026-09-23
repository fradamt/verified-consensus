module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.CanonicalSuffixPostGSTCore
public import DecoupledConsensusInternal.RecoveryPrefix
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.AdoptionRun
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionHistory
public import DecoupledConsensusProofs.Protocol.ValidatorClient.FinalityPairCore
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Generic.SuffixHistory
public import DecoupledConsensusProofs.Protocol.Grades.ProposalLifecycleCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.ProposalCore
public import DecoupledConsensusProofs.Generic.PostGSTCarrierAdmissionCore
public import DecoupledConsensusProofs.Protocol.Schedule.GSTZeroHeadResolution
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryHandoffCore
public import DecoupledConsensusProofs.Protocol.ChainState.SlashableBoundBridge
public import DecoupledConsensusProofs.Execution.RecoveryActionInterval
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.EmissionShape
public import DecoupledConsensusProofs.Protocol.Schedule.ConfirmationHistoryProducer
public import DecoupledConsensusProofs.Protocol.Grades.GoldfishConePersistence
public import DecoupledConsensusProofs.Protocol.ChainState.RecurringFinality
public import DecoupledConsensusProofs.Protocol.Grades.LifecycleActionSource
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.RecoverySourceProgress
public import DecoupledConsensusProofs.Generic.CanonicalSuffix
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionConfirmationCore
public import DecoupledConsensusProofs.Protocol.ChainState.CarrierAlignment
public import DecoupledConsensusProofs.Protocol.ValidatorClient.SuccessorTargetRows

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Canonical-regime carrier rounds

This file packages the local data at one canonical carrier round. It keeps the
three possible height outcomes of the slot-`+1` proposal. A progress-only
height event is a valid third outcome and is not treated as a target event.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Prefix provenance for height sources emitted before the current carrier. -/
def CanonicalHeightSourceHistoryAt
    (S : Setup V) (rho : Run V) (q0 r : Round) (P0 : NamedBlock V) : Prop :=
  ∀ k, q0 ≤ k → k < r → ∀ v, v ∈ rho.honest → ∀ h,
    (actionAttestationAt S rho v k).height_pair.erase.height? = some h →
      ∃ Q : NamedBlock V,
        actionFGSource S (actionReadAt S rho v k) = some Q.erase ∧
        RunBlock S rho Q ∧ NamedBlock.Preceq Q P0 ∧
        (Protocol.derive_named S.E S.cfg Q).h = h

/-- Prefix provenance for target entries visible at the current action.

Restricted to heights ABOVE the boundary frontier. A row recorded before the
healing boundary need not have a canonical origin below `P0` at all — an honest
validator may have voted a target on a branch abandoned before GST — so the
moving chain can only supply rows whose emission is post-boundary, and the
height form of that condition is what every consumer already has in hand. -/
def CanonicalTargetHistoryAt
    (S : Setup V) (rho : Run V) (q0 r : Round) (P0 : NamedBlock V) : Prop :=
  ∀ v, v ∈ rho.honest → ∀ h X,
    honestHMaxAt S rho (S.a q0) < h →
    (rho.stateBeforeTime S (S.a r) v).Λ.target h = some X →
      ∃ Q : NamedBlock V,
        RunBlock S rho Q ∧ NamedBlock.Preceq Q P0 ∧
        (Protocol.derive_named S.E S.cfg Q).h = h ∧
        (Protocol.derive_named S.E S.cfg Q).T_h.root = X

/-- Prefix provenance for timeout entries visible at the current action,
restricted to heights above the boundary frontier for the same reason as
`CanonicalTargetHistoryAt`. -/
def CanonicalTimeoutHistoryAt
    (S : Setup V) (rho : Run V) (q0 r : Round) (P0 : NamedBlock V) : Prop :=
  ∀ v, v ∈ rho.honest → ∀ h,
    honestHMaxAt S rho (S.a q0) < h →
    (rho.stateBeforeTime S (S.a r) v).Λ.timeout h = true →
      ∃ Q : NamedBlock V,
        RunBlock S rho Q ∧ NamedBlock.Preceq Q P0 ∧
        (Protocol.derive_named S.E S.cfg Q).h = h ∧
        (Protocol.derive_named S.E S.cfg Q).nj = true

/-- One honest author's timely, resolved vote in a carrier grade view. -/
def CanonicalBatchVoteAt
    (S : Setup V) (rho : Run V) (r : Round)
    (gv : Protocol.GradeView V) (w : V) : Prop :=
  ∃ vote : Protocol.SGVote V,
    vote ∈ Protocol.sg_votes_by (Protocol.round_batch gv r) w ∧
      vote = actionSGVoteAt S rho w (r - 1) ∧
      vote.round + 1 = r ∧
      Block.find? gv.T (actionSGBlockAt S rho w (r - 1)).root =
        some (actionSGBlockAt S rho w (r - 1)) ∧
      occurrenceBefore
        (Protocol.sg_resolution_time gv.T gv.timestamp_block
          gv.timestamp_sg_vote vote) (S.hc.Γ_neg1 S.E.Δ r) = true

/-- The complete local record for one canonical carrier round. -/
structure CanonicalRegimeRoundAt
    (S : Setup V) (rho : Run V) (q0 r : Round) : Prop where
  openingProposal : ∃ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P
  carrier : ProposerCarrierAt S rho r
  afterBoundary : healingBoundaryTime S q0 <
    Protocol.proposal_time S.E (S.hc.opening_slot r)
  inHorizon : Protocol.confirmation_time S.E
    (S.hc.opening_slot r + 2) ≤ rho.horizon
  batchSole : ∀ v ∈ rho.honest, ∀ w ∈ rho.honest,
    (Protocol.sg_votes_by
      (Protocol.round_batch
        (actionStoreAt S rho v r).toHealing.gradeView r) w).card ≤ 1
  batchComplete : ∀ v ∈ rho.honest, ∀ w ∈ rho.honest,
    CanonicalBatchVoteAt S rho r
      (actionStoreAt S rho v r).toHealing.gradeView w
  batchHeads : ∀ v ∈ rho.honest, ∀ w ∈ rho.honest,
    ∀ u ∈ Protocol.sg_votes_by
      (Protocol.round_batch
        (actionStoreAt S rho v r).toHealing.gradeView r) w,
      ∀ P : NamedBlock V,
        proposedBlockAt S rho (S.hc.opening_slot r) = some P →
      Proofs.Optimistic.rootOnCan
        (actionStoreAt S rho v r).toHealing.gradeView.T
        P.erase u.confirmed = true
  openingLive : ∀ v ∈ rho.honest, ∀ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P →
    (actionStoreAt S rho v r).st.core.live_confirmed = P.erase
  openingSource : ∀ v ∈ rho.honest, ∀ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P →
    actionFGSource S (actionReadAt S rho v r) = some P.erase
  actionRootBelowOpening : ∀ v ∈ rho.honest, ∀ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P →
    Block.Preceq
      (Protocol.get_fg_root
        (actionStoreAt S rho v r).st.core.toHealing.toFG) P.erase
  actionAnchorBelowOpening : ∀ v ∈ rho.honest, ∀ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P →
    Block.Preceq
      (Proofs.Optimistic.healAnchor S.E S.hc
        (actionStoreAt S rho v r).st.core.toHealing) P.erase
  /-- The prepared action-read anchor is below the opening proposal. -/
  namedActionAnchorBelowOpening : ∀ v ∈ rho.honest, ∀ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P →
    Block.Preceq
      (PhaseGrades.nodeAnchor S (actionReadAt S rho v r) r) P.erase
  plusOneCandidate : ∀ v ∈ rho.honest, ∀ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P →
    P.erase ∈
      Protocol.get_filtered_block_tree
        (actionStoreAt S rho v r).st.core.toHealing.toFG
  plusOneCone : ∀ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P →
    Block.Preceq P.erase
      (proposedParent S rho (S.hc.opening_slot r + 1))
  plusTwoCone : ∀ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P →
    Block.Preceq P.erase
      (proposedParent S rho (S.hc.opening_slot r + 2))
  heightHistory : ∀ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P →
      CanonicalHeightSourceHistoryAt S rho q0 r P
  targetHistory : ∀ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P →
      CanonicalTargetHistoryAt S rho q0 r P
  timeoutHistory : ∀ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P →
      CanonicalTimeoutHistoryAt S rho q0 r P


/-- The carrier's batch fields are the existing `BatchAligned` record. -/
theorem CanonicalRegimeRoundAt.actionBatchAligned
    {S : Setup V} {rho : Run V} {q0 r : Round}
    (h : CanonicalRegimeRoundAt S rho q0 r) :
    ∀ v ∈ rho.honest, ∀ P : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r) = some P →
      Proofs.Optimistic.BatchAligned
        (actionStoreAt S rho v r).toHealing.gradeView
        rho.honest r P.erase := by
  intro v hv P hP
  exact
    { sole := h.batchSole v hv
      heads := by
        intro w hw u hu
        exact h.batchHeads v hv w hw u hu P hP }




private theorem honest_nonempty_of_honestWeightMajority
    (S : Setup V) {H : Finset V}
    (hmajority : HonestWeightMajority S H) : H.Nonempty := by
  by_contra hnone
  have hzero : S.E.electorate.weightOf H = 0 := by
    rw [Finset.not_nonempty_iff_eq_empty.mp hnone]
    simp [Electorate.weightOf]
  have hsum := S.E.electorate.weightOf_add_weightOf_sdiff H
  unfold HonestWeightMajority at hmajority
  omega

private theorem actionGradeView_eq_gradeViewAt
  (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    (actionStoreAt S rho v r).toHealing.gradeView =
      gradeViewAt S rho v r := by
  exact Protocol.actionStoreAt_gradeView_eq_storeBeforeTime S rho v r


/-- The complete batch gives direct support to each block below every honest
emitted head. Stated on the two batch fields alone, so a producer can use it
before the full carrier record exists. -/
theorem honestSupport_of_batchFields
    {S : Setup V} {rho : Run V} {r : Round}
    (hsole : ∀ v ∈ rho.honest, ∀ w ∈ rho.honest,
      (Protocol.sg_votes_by
        (Protocol.round_batch
          (actionStoreAt S rho v r).toHealing.gradeView r) w).card ≤ 1)
    (hcomplete : ∀ v ∈ rho.honest, ∀ w ∈ rho.honest,
      CanonicalBatchVoteAt S rho r
        (actionStoreAt S rho v r).toHealing.gradeView w)
    {C : Block V}
    (hbelow : ∀ w ∈ rho.honest,
      Block.Preceq C (actionSGBlockAt S rho w (r - 1))) :
    ∀ v ∈ rho.honest, ∀ w ∈ rho.honest,
      occurrenceBefore
          (Protocol.summary
            (actionStoreAt S rho v r).toHealing.gradeView r w).t_v
          (S.hc.Γ_neg1 S.E.Δ r) = true ∧
        Protocol.head_covers
          (actionStoreAt S rho v r).toHealing.gradeView.T C
          (Protocol.summary
            (actionStoreAt S rho v r).toHealing.gradeView r w).C_v = true ∧
        occurrenceAtLeast
          (Protocol.summary
            (actionStoreAt S rho v r).toHealing.gradeView r w).e_v
          (S.hc.Γ_2 S.E.Δ r) = true := by
  intro v hv w hw
  let gv := (actionStoreAt S rho v r).toHealing.gradeView
  let batch := Protocol.sg_votes_by (Protocol.round_batch gv r) w
  let tau := Protocol.sg_resolution_time gv.T gv.timestamp_block
    gv.timestamp_sg_vote
  let headed := batch.filter (fun x =>
    x.confirmed.isSome ∧ Protocol.sg_resolved gv.T x = true)
  obtain ⟨u, hu, hue, -, hfind, hut⟩ := hcomplete v hv w hw
  have huBatch : u ∈ batch := by simpa only [batch, gv] using hu
  have huResolved : Protocol.sg_resolved gv.T u = true := by
    rw [hue]
    simp only [actionSGVoteAt, Protocol.sg_resolved, gv, hfind,
      Option.isSome_some]
  have huHeaded : u ∈ headed := by
    refine Finset.mem_filter.mpr ⟨huBatch, ?_⟩
    exact ⟨by rw [hue]; simp [actionSGVoteAt], huResolved⟩
  have hcard : batch.card ≤ 1 := by
    simpa only [batch, gv] using hsole v hv w hw
  have hheadedCard : headed.card ≤ 1 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans hcard
  have hfirst : Protocol.batch_first? tau headed = some u :=
    Proofs.Optimistic.batch_first?_of_card_le_one huHeaded hheadedCard
  have hsummaryC : (Protocol.summary gv r w).C_v = u.confirmed := by
    change (Protocol.batch_first? tau headed).bind
      Protocol.SGVote.confirmed = u.confirmed
    rw [hfirst]
    rfl
  have hsummaryT : (Protocol.summary gv r w).t_v = tau u := by
    change (Protocol.batch_first? tau headed).elim none tau = tau u
    rw [hfirst]
    simp
  have hsummaryE : (Protocol.summary gv r w).e_v = none := by
    rw [Proofs.Optimistic.summary_e_v_eq]
    exact Proofs.Optimistic.equivocation_instant_eq_none hcard
  refine ⟨?_, ?_, ?_⟩
  · rw [hsummaryT]
    simpa only [tau, gv] using hut
  · rw [hsummaryC, hue]
    simp only [actionSGVoteAt, Protocol.head_covers, hfind]
    exact hbelow w hw
  · rw [hsummaryE]
    rfl


/-- The batch fields alone produce one block below `P0` with common grade-2
support. They do not show that this block remains in every filtered tree. -/
theorem CanonicalRegimeRoundAt.exists_commonG2Floor
    {S : Setup V} {rho : Run V} {q0 r : Round}
    (h : CanonicalRegimeRoundAt S rho q0 r)
    (hmajority : HonestWeightMajority S rho.honest) :
    ∃ P : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r) = some P ∧
        ∃ C, Block.Preceq C P.erase ∧
          ∀ v ∈ rho.honest,
            Protocol.G2 S.E (gradeViewAt S rho v r) S.hc r C = true := by
  obtain ⟨P, hP⟩ := h.openingProposal
  have hnonempty : rho.honest.Nonempty :=
    honest_nonempty_of_honestWeightMajority S hmajority
  obtain ⟨w0, hw0, hmin⟩ := Finset.exists_mem_eq_inf' hnonempty
    (fun w => (actionSGBlockAt S rho w (r - 1)).depth)
  let C := actionSGBlockAt S rho w0 (r - 1)
  have hheadPre : ∀ w ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho w (r - 1)) P.erase := by
    intro w hw
    obtain ⟨u, hu, hue, -, hfind, -⟩ := h.batchComplete w0 hw0 w hw
    have hhead := h.batchHeads w0 hw0 w hw u hu P hP
    rw [hue] at hhead
    simpa only [actionSGVoteAt, Proofs.Optimistic.rootOnCan, hfind] using hhead
  have hdepth : ∀ w ∈ rho.honest,
      C.depth ≤ (actionSGBlockAt S rho w (r - 1)).depth := by
    intro w hw
    change (actionSGBlockAt S rho w0 (r - 1)).depth ≤
      (actionSGBlockAt S rho w (r - 1)).depth
    rw [← hmin]
    exact Finset.inf'_le _ hw
  have hbelow : ∀ w ∈ rho.honest,
      Block.Preceq C (actionSGBlockAt S rho w (r - 1)) := by
    intro w hw
    exact AlignedRoundLemmas.preceq_of_compatible_of_depth_le
      (Block.compatible_of_preceq_common
        (hheadPre w0 hw0) (hheadPre w hw)) (hdepth w hw)
  refine ⟨P, hP, C, hheadPre w0 hw0, ?_⟩
  intro v hv
  have hsupport := honestSupport_of_batchFields
    h.batchSole h.batchComplete hbelow v hv
  rw [← actionGradeView_eq_gradeViewAt S rho v r]
  simp only [Protocol.G2, decide_eq_true_eq]
  unfold Protocol.direct_support
  refine le_trans (honestWeight_ge_m hmajority)
    (S.E.electorate.weightOf_mono ?_)
  intro w hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hsupport w hw⟩











/-- Sole plus complete pins every honest batch vote to that author's exact
round-`(r-1)` action vote, so head alignment on `P0` reduces to the exact SG
carrier being below `P0`. -/
theorem batchHeads_of_batchFields
    {S : Setup V} {rho : Run V} {r : Round} {Can : Block V}
    (hsole : ∀ v ∈ rho.honest, ∀ w ∈ rho.honest,
      (Protocol.sg_votes_by
        (Protocol.round_batch
          (actionStoreAt S rho v r).toHealing.gradeView r) w).card ≤ 1)
    (hcomplete : ∀ v ∈ rho.honest, ∀ w ∈ rho.honest,
      CanonicalBatchVoteAt S rho r
        (actionStoreAt S rho v r).toHealing.gradeView w)
    (hcarriers : ∀ w ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho w (r - 1)) Can) :
    ∀ v ∈ rho.honest, ∀ w ∈ rho.honest,
      ∀ u ∈ Protocol.sg_votes_by
        (Protocol.round_batch
          (actionStoreAt S rho v r).toHealing.gradeView r) w,
        Proofs.Optimistic.rootOnCan
          (actionStoreAt S rho v r).toHealing.gradeView.T
          Can u.confirmed = true := by
  intro v hv w hw u hu
  obtain ⟨vote, hvote, hvoteEq, -, hfind, -⟩ := hcomplete v hv w hw
  have hcard := hsole v hv w hw
  have huvote : u = vote :=
    Finset.card_le_one.mp hcard u hu vote hvote
  subst u
  rw [hvoteEq]
  simpa only [actionSGVoteAt, Proofs.Optimistic.rootOnCan, hfind] using
    hcarriers w hw

private theorem canonical_named_fold_nj (rows : List (NamedAttestation V))
    (st : Protocol.ChainState V) :
    (rows.foldl (Protocol.process_attestation_with
      (Protocol.TimeoutBinding.targeted V)) st).nj = st.nj := by
  induction rows generalizing st with
  | nil => rfl
  | cons row rows ih =>
      rw [List.foldl_cons, ih]
      exact NjGap.process_attestation_nj st _

private theorem canonical_named_fold_h (rows : List (NamedAttestation V))
    (st : Protocol.ChainState V) (geometry : Block V) :
    (rows.foldl (Protocol.process_attestation_with
      (Protocol.TimeoutBinding.targeted V))
      {st with s := geometry.slot}).h = st.h :=
  (NamedDerivationGeometry.fold_context_fields
    (Protocol.TimeoutBinding.targeted V) rows
    {st with s := geometry.slot}).2.1

private theorem canonical_named_nj_eq_node_of_same_height
    (E : Env V) (cfg : Protocol.HeightConfig)
    (parent : NamedBlock V) (s : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V))
    (rows : List (NamedAttestation V)) (proposer : V)
    (hh : (Protocol.derive_named E cfg
      (.node parent s root votes support rows proposer)).h =
        (Protocol.derive_named E cfg parent).h) :
    (Protocol.derive_named E cfg
      (.node parent s root votes support rows proposer)).nj =
        (Protocol.derive_named E cfg parent).nj := by
  have hderive : Protocol.derive_named E cfg
        (.node parent s root votes support rows proposer) =
      Protocol.named_transition E cfg
        (Protocol.derive_named E cfg parent)
          (.node parent s root votes support rows proposer) := by
    rw [BlockProcessingDefaults.derive_named_node]
  rw [hderive]
  unfold Protocol.named_transition Protocol.transition_rows
  rw [Protocol.process_height_events_eq]
  split_ifs with htarget hprogress
  · exfalso
    have hh' := hh
    change (Protocol.named_transition E cfg
      (Protocol.derive_named E cfg parent)
        (.node parent s root votes support rows proposer)).h =
      (Protocol.derive_named E cfg parent).h at hh'
    simp only [Protocol.named_transition,
      Protocol.transition_rows] at hh'
    rw [Protocol.process_height_events_eq, if_pos htarget,
      Protocol.advance_height_h, Protocol.afterFin_h] at hh'
    simp only [Protocol.fold_rows] at hh'
    rw [canonical_named_fold_h] at hh'
    exact (Nat.ne_of_lt (Nat.lt_succ_self _)) hh'.symm
  · exfalso
    have hh' := hh
    change (Protocol.named_transition E cfg
      (Protocol.derive_named E cfg parent)
        (.node parent s root votes support rows proposer)).h =
      (Protocol.derive_named E cfg parent).h at hh'
    simp only [Protocol.named_transition,
      Protocol.transition_rows] at hh'
    rw [Protocol.process_height_events_eq, if_neg htarget,
      if_pos hprogress, Protocol.advance_height_h, Protocol.afterFin_h] at hh'
    simp only [Protocol.fold_rows] at hh'
    rw [canonical_named_fold_h] at hh'
    exact (Nat.ne_of_lt (Nat.lt_succ_self _)) hh'.symm
  · rw [Protocol.afterFin_nj]
    simp only [Protocol.fold_rows]
    rw [canonical_named_fold_nj]

private theorem named_nj_eq_of_preceq_same_height
    (E : Env V) (cfg : Protocol.HeightConfig)
    {C P : NamedBlock V}
    (hCP : NamedBlock.Preceq C P)
    (hh : (Protocol.derive_named E cfg P).h =
      (Protocol.derive_named E cfg C).h) :
    (Protocol.derive_named E cfg P).nj =
      (Protocol.derive_named E cfg C).nj := by
  induction P with
  | genesis =>
      have hC : C = .genesis := by
        cases C with
        | genesis => rfl
        | node p s root votes support rows proposer =>
            simp [NamedBlock.Preceq, NamedBlock.preceq] at hCP
      subst C
      rfl
  | node p s root votes support rows proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq,
        Bool.or_eq_true, decide_eq_true_eq] at hCP
      rcases hCP with hEq | hCp
      · subst C
        rfl
      · have hpHeight : (Protocol.derive_named E cfg p).h =
            (Protocol.derive_named E cfg C).h := by
          apply Nat.le_antisymm
          · exact (Proofs.NamedEntryHeight.derive_height_mono E cfg
              (Proofs.NamedAncestry.named_extend s root votes support rows proposer
                (Proofs.NamedAncestry.named_self p))).trans_eq hh
          · exact Proofs.NamedEntryHeight.derive_height_mono E cfg hCp
        have hnodeHeight :
            (Protocol.derive_named E cfg
              (.node p s root votes support rows proposer)).h =
              (Protocol.derive_named E cfg p).h :=
          hh.trans hpHeight.symm
        exact (canonical_named_nj_eq_node_of_same_height E cfg
          p s root votes support rows proposer hnodeHeight).trans
          (ih hCp hpHeight)




/-- Canonical record histories at a justifiable endpoint preserve a reused
target and exclude a timeout at its height. No carrier, grade, or fresh-row
premise is needed. The endpoint need not be an opening proposal. -/
theorem successorTargetRecordAt_of_canonicalRecordHistory
    {S : Setup V} {rho : Run V} {q0 r : Round} {P0 : NamedBlock V}
    (htarget : CanonicalTargetHistoryAt S rho q0 r P0)
    (htimeout : CanonicalTimeoutHistoryAt S rho q0 r P0)
    (habove : honestHMaxAt S rho (S.a q0) <
      (Protocol.derive_named S.E S.cfg P0).h)
    (hnj : (Protocol.derive_named S.E S.cfg P0).nj = false) :
    ∀ v ∈ rho.honest,
      SuccessorTargetRecordAt (rho.stateBeforeTime S (S.a r) v).Λ
        (Protocol.derive_named S.E S.cfg P0).h
        (Protocol.derive_named S.E S.cfg P0).T_h.root := by
  intro v hv
  let H0 := (Protocol.derive_named S.E S.cfg P0).h
  let T0 := (Protocol.derive_named S.E S.cfg P0).T_h.root
  constructor
  · by_cases hnone :
      (rho.stateBeforeTime S (S.a r) v).Λ.legacy.target H0 = none
    · exact Or.inl hnone
    · obtain ⟨X, ht⟩ := Option.ne_none_iff_exists'.mp hnone
      right
      obtain ⟨Q, -, hQP0, hQheight, hQtarget⟩ :=
        htarget v hv H0 X habove ht
      have hsame := Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hQP0
        (by simpa only [H0] using hQheight.trans rfl)
      have hroot : X = T0 := by
        calc
          X = (Protocol.derive_named S.E S.cfg Q).T_h.root := hQtarget.symm
          _ = (Protocol.derive_named S.E S.cfg P0).T_h.root :=
            congrArg Block.root hsame
          _ = T0 := rfl
      rw [ht, hroot]
  · by_cases hfalse :
      (rho.stateBeforeTime S (S.a r) v).Λ.legacy.timeout H0 = false
    · exact hfalse
    · have htrue :
          (rho.stateBeforeTime S (S.a r) v).Λ.legacy.timeout H0 = true :=
        Bool.eq_true_of_not_eq_false hfalse
      obtain ⟨Q, -, hQP0, hQheight, hQnj⟩ :=
        htimeout v hv H0 habove htrue
      have hsame := named_nj_eq_of_preceq_same_height S.E S.cfg hQP0
        (by simpa only [H0] using (hQheight.trans rfl).symm)
      have hP0nj : (Protocol.derive_named S.E S.cfg P0).nj = true :=
        hsame.trans hQnj
      have : False := by
        rw [hnj] at hP0nj
        exact Bool.noConfusion hP0nj
      contradiction

/-- A justifiable opening makes every same-height target canonical and every
same-height timeout entry false. -/
theorem CanonicalRegimeRoundAt.successorTargetRecordAt
    {S : Setup V} {rho : Run V} {q0 r : Round}
    (h : CanonicalRegimeRoundAt S rho q0 r)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot r) = some P)
    (habove : honestHMaxAt S rho (S.a q0) <
      (Protocol.derive_named S.E S.cfg P).h)
    (hnj : (Protocol.derive_named S.E S.cfg P).nj = false) :
    ∀ v ∈ rho.honest,
      SuccessorTargetRecordAt (rho.stateBeforeTime S (S.a r) v).Λ
        (Protocol.derive_named S.E S.cfg P).h
        (Protocol.derive_named S.E S.cfg P).T_h.root := by
  exact successorTargetRecordAt_of_canonicalRecordHistory
    (h.targetHistory P hP) (h.timeoutHistory P hP) habove hnj


/-
/-- The round record supplies the exact action-history residual used by the
slot-`+1` action-head cone. -/
theorem CanonicalRegimeRoundAt.actionHistoryResidual
    {S: Setup V} {rho: Run V} {q0 r: Round}
    (h: CanonicalRegimeRoundAt S rho q0 r):
    CanonicalCarrierActionHistoryResidualAt S rho r:= by
  let P0:= proposedBlock S rho (S.hc.opening_slot r)
  let P1:= proposedBlock S rho (S.hc.opening_slot r + 1)
  have hP0P1: Block.Preceq P0 P1:=
    Block.preceq_trans h.plusOneCone
      (Protocol.proposedParent_preceq_proposedBlock S rho
        (S.hc.opening_slot r + 1))
  refine
    { actionRootCompatible:= ?_
      actionAnchorCompatible:= ?_
      actionCandidate:= ?_
      actionBatchAligned:= h.actionBatchAligned }
  · intro v hv
    exact Block.compatible_of_preceq_common
      (Block.preceq_trans (h.actionRootBelowOpening v hv) hP0P1)
      (Block.preceq_self P1)
  · intro v hv
    exact Block.compatible_of_preceq_common
      (Block.preceq_trans (h.actionAnchorBelowOpening v hv) hP0P1)
      (Block.preceq_self P1)
  · intro v hv _
    exact h.plusOneCandidate v hv

-/




/- /-- The quiet arm preserves the opening height and complete height target. -/
/-- The quiet arm preserves the opening height and complete height target. -/
theorem CarrierPlusOneOutcomeAt.quiet_state
    {S: Setup V} {rho: Run V} {r: Round} {P0: Block V}
    (hparent: Protocol.proposedParent S rho
      (S.hc.opening_slot r + 1) = P0)
    (hquiet: CarrierPlusOneNoHeightEventAt S rho r P0):
    (derived_state S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot r + 1))).h =
        (derived_state S.E S.cfg P0).h ∧
      (derived_state S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot r + 1))).T_h =
        (derived_state S.E S.cfg P0).T_h:= by
  exact plusOne_state_eq_of_parent_of_noHeightEvent S hparent hquiet
/-- In the target arm, slot `+1` justifies the previous target and advances once. -/
theorem CarrierPlusOneOutcomeAt.earlyTarget_state
    {S: Setup V} {rho: Run V} {r: Round} {P0: Block V}
    (hparent: Protocol.proposedParent S rho
      (S.hc.opening_slot r + 1) = P0)
    (htarget: Protocol.targetReady S.E
      (Protocol.afterFin S.E (carrierPlusOneFold S rho r P0)) = true):
    let P1:= proposedBlock S rho (S.hc.opening_slot r + 1)
    (derived_state S.E S.cfg P1).h = (derived_state S.E S.cfg P0).h + 1 ∧
      (derived_state S.E S.cfg P1).J = (derived_state S.E S.cfg P0).T_h ∧
      (derived_state S.E S.cfg P1).h_j = (derived_state S.E S.cfg P0).h ∧
      (derived_state S.E S.cfg P1).T_h = P1:= by
  dsimp only
  generalize hP1: proposedBlock S rho (S.hc.opening_slot r + 1) = P1
  cases P1 with
  | genesis =>
      have hp:= Protocol.proposedBlock_parent S rho
        (S.hc.opening_slot r + 1)
      rw [hP1] at hp
      simp only [Block.parent?] at hp
      cases hp
  | node p s root votes support ats i =>
      have hp:= Protocol.proposedBlock_parent S rho
        (S.hc.opening_slot r + 1)
      rw [hP1] at hp
      simp only [Block.parent?] at hp
      have hpeq: p = P0:= by
        rw [hparent] at hp
        exact Option.some.inj hp
      subst p
      simp only [carrierPlusOneFold, hP1] at htarget
      simp only [Protocol.derived_state_node, Protocol.process_height_events_eq,
        htarget, if_pos, Protocol.advance_height_h, Protocol.afterFin_h,
        Protocol.foldBlock_h, Protocol.advance_height_J,
        Protocol.afterFin_T_h, Protocol.foldBlock_T_h,
        Protocol.advance_height_h_j, Protocol.advance_height_T_h,
        Protocol.afterFin_L, Protocol.foldBlock_L, true_and]
/-- In the progress-only arm, slot `+1` advances once and preserves the
after-finality justification fields. -/
theorem CarrierPlusOneOutcomeAt.earlyProgress_state
    {S: Setup V} {rho: Run V} {r: Round} {P0: Block V}
    (hparent: Protocol.proposedParent S rho
      (S.hc.opening_slot r + 1) = P0)
    (htarget: Protocol.targetReady S.E
      (Protocol.afterFin S.E (carrierPlusOneFold S rho r P0)) = false)
    (hprogress: Protocol.progReady S.E S.cfg
      (Protocol.afterFin S.E (carrierPlusOneFold S rho r P0)) = true):
    let P1:= proposedBlock S rho (S.hc.opening_slot r + 1)
    let tau:= Protocol.afterFin S.E (carrierPlusOneFold S rho r P0)
    (derived_state S.E S.cfg P1).h = (derived_state S.E S.cfg P0).h + 1 ∧
      (derived_state S.E S.cfg P1).J = tau.J ∧
      (derived_state S.E S.cfg P1).h_j = tau.h_j ∧
      (derived_state S.E S.cfg P1).T_h = P1:= by
  dsimp only
  generalize hP1: proposedBlock S rho (S.hc.opening_slot r + 1) = P1
  cases P1 with
  | genesis =>
      have hp:= Protocol.proposedBlock_parent S rho
        (S.hc.opening_slot r + 1)
      rw [hP1] at hp
      simp only [Block.parent?] at hp
      cases hp
  | node p s root votes support ats i =>
      have hp:= Protocol.proposedBlock_parent S rho
        (S.hc.opening_slot r + 1)
      rw [hP1] at hp
      simp only [Block.parent?] at hp
      have hpeq: p = P0:= by
        rw [hparent] at hp
        exact Option.some.inj hp
      subst p
      simp only [carrierPlusOneFold, hP1] at htarget hprogress ⊢
      have htarget': Protocol.targetReady S.E
          (Protocol.afterFin S.E
            (Protocol.foldBlock (derived_state S.E S.cfg P0)
              (P0.node s root votes support ats i))) ≠ true:= by
        rw [htarget]
        simp
      rw [Protocol.derived_state_node, Protocol.process_height_events_eq,
        if_neg htarget', if_pos hprogress]
      simp only [Protocol.advance_height_h, Protocol.afterFin_h,
        Protocol.foldBlock_h, Protocol.advance_height_J,
        Protocol.advance_height_h_j, Protocol.advance_height_T_h,
        Protocol.afterFin_L, Protocol.foldBlock_L, true_and]
/-- A justifiable quiet carrier round assembles the existing regime residual.
The explicit quiet premise also checks the slot-`+1` state preservation used by
the later carrier kernel.
**Open (Rule B residual).** The canonical-round history proves the
successor target and timeout facts, but Rule B does not determine a stored lock
or the target of a same-height finality pair when both record entries are empty.
-/
theorem canonicalCarrierRegimeResidualAt_of_regimeRound
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hmajority: HonestWeightMajority S rho.honest)
    {q0 r: Round} (h: CanonicalRegimeRoundAt S rho q0 r)
    (hactivity: CanonicalGradeFloorActivityResidualAt S rho r)
    (habove: honestHMaxAt S rho (S.a q0) <
      (derived_state S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot r))).h)
    (hnj: (derived_state S.E S.cfg
      (proposedBlock S rho (S.hc.opening_slot r))).nj = false)
    (hlockAligned: ∀ v ∈ rho.honest,
      SuccessorTargetLockAlignmentAt
        (rho.stateBeforeTime S (S.a r) v).Λ
        (actionAttestationAt S rho v r).finality_pair
        (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r))).h
        (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r))).T_h.root)
    (hquiet: CarrierPlusOneNoHeightEventAt S rho r
      (proposedBlock S rho (S.hc.opening_slot r))):
    ∃ C, CanonicalCarrierRegimeResidualAt S rho r C:= by
  let P0:= proposedBlock S rho (S.hc.opening_slot r)
  have hparent: Protocol.proposedParent S rho
      (S.hc.opening_slot r + 1) = P0:= by
    apply proposedParent_eq_previousSlotBlock_of_preceq S adm
      (Protocol.proposedBlock_slot S rho (S.hc.opening_slot r))
    simpa only [P0] using h.plusOneCone
  have _hquietState:= plusOne_state_eq_of_parent_of_noHeightEvent
    S hparent hquiet
  obtain ⟨C, hgrade, hbelow⟩:= h.exists_gradeFloor hmajority hactivity
  refine ⟨C, canonicalCarrierRegimeResidualAt_of_fresh_records
    S adm hgrade ?_ ?_⟩
  · exact
      { gradeBelowOpening:= hbelow
        actionBatchAligned:= h.actionBatchAligned }
  · exact
      { successorRecord:= h.successorTargetRecordAt habove hnj
        lockAlignment:= hlockAligned }
/-- The assembled residual projects to the existing canonical carrier regime. -/
theorem exists_canonicalCarrierRegimeAt_of_regimeRound
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hmajority: HonestWeightMajority S rho.honest)
    {q0 r: Round} (h: CanonicalRegimeRoundAt S rho q0 r)
    (hactivity: CanonicalGradeFloorActivityResidualAt S rho r)
    (habove: honestHMaxAt S rho (S.a q0) <
      (derived_state S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot r))).h)
    (hnj: (derived_state S.E S.cfg
      (proposedBlock S rho (S.hc.opening_slot r))).nj = false)
    (hlockAligned: ∀ v ∈ rho.honest,
      SuccessorTargetLockAlignmentAt
        (rho.stateBeforeTime S (S.a r) v).Λ
        (actionAttestationAt S rho v r).finality_pair
        (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r))).h
        (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r))).T_h.root)
    (hquiet: CarrierPlusOneNoHeightEventAt S rho r
      (proposedBlock S rho (S.hc.opening_slot r))):
    ∃ C, CanonicalCarrierRegimeAt S rho r C:= by
  obtain ⟨C, hres⟩:= canonicalCarrierRegimeResidualAt_of_regimeRound
    S adm hmajority h hactivity habove hnj hlockAligned hquiet
  exact ⟨C, canonicalCarrierRegimeAt_of_residual S hres⟩
-/

#print axioms CanonicalRegimeRoundAt.actionBatchAligned
#print axioms CanonicalRegimeRoundAt.exists_commonG2Floor
#print axioms batchHeads_of_batchFields
#print axioms successorTargetRecordAt_of_canonicalRecordHistory
#print axioms CanonicalRegimeRoundAt.successorTargetRecordAt
#print axioms canonical_named_fold_nj
#print axioms canonical_named_fold_h
#print axioms canonical_named_nj_eq_node_of_same_height
#print axioms named_nj_eq_of_preceq_same_height




end HealingSurface
end Proofs
end DecoupledConsensusModel

end
