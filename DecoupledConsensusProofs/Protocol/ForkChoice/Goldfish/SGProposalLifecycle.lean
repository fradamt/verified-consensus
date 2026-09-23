module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryProposalConfirmation
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryProposalWindow
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.GoldfishCone
public import DecoupledConsensusProofs.Protocol.Grades.RelativeOneChain
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FinalityFilterRetention
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryCapturedSlotInterval
public import DecoupledConsensusProofs.Protocol.Schedule.PostHealingReuse
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FinalityFilterInterference
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ReaderLocalCone
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HonestMajorityCore
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionHistory
public import DecoupledConsensusProofs.Generic.SuffixHistory
public import DecoupledConsensusProofs.Protocol.Handlers.StoreFinality
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.ChainState.JustificationCertificates
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Protocol.Grades.ProposalParent
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordClean
public import DecoupledConsensusProofs.Generic.EvaluationStore
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Objects.EmittedHeightBound
public import DecoupledConsensusProofs.Execution.ReleasedCertificateHeightProgress
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecoveryTimeout
public import DecoupledConsensusProofs.Execution.RecoveryGradeProcessedRead
public import DecoupledConsensusProofs.Execution.StoreFinalityRun
public import DecoupledConsensusProofs.Execution.CertificateUniqueness
public import DecoupledConsensusProofs.Protocol.ChainState.ProgressQuorumCore
public import DecoupledConsensusProofs.Protocol.Handlers.Staleness
public import DecoupledConsensusModel.Protocol.ChainState
public import DecoupledConsensusProofs.Protocol.Handlers.BlockProcessingDefaults
public import DecoupledConsensusProofs.Protocol.ChainState.TargetedTimeoutBinding
public import DecoupledConsensusProofs.Protocol.ChainState.TimeoutBindingDefaults
public import DecoupledConsensusProofs.Protocol.ChainState.NjGap
public import DecoupledConsensusProofs.Protocol.ChainState.DerivationGeometry
public import DecoupledConsensusInternal.Execution.Run
public import DecoupledConsensusProofs.Protocol.ChainState.SlashableBoundBridge
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.Schedule.ConfirmationHistoryProducer
public import DecoupledConsensusProofs.Execution.Concentration
public import DecoupledConsensusProofs.Execution.Runtime
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusInternal.Definitions.NamedDerived
public import DecoupledConsensusProofs.Protocol.ChainState.NamedNjGap
public import DecoupledConsensusProofs.Protocol.Handlers.Bridges
public import DecoupledConsensusInternal.Healing
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsProducers
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsBridge
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityCertificates
public import DecoupledConsensusProofs.Protocol.Handlers.JustificationCarrier
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryCapturedNextActionExact
public import DecoupledConsensusProofs.Protocol.Handlers.Proposer
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalPivot
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalSnapshotBridge
public import DecoupledConsensusProofs.Execution.BodyRetention
public import DecoupledConsensusProofs.Protocol.Handlers.GoldfishVotePool
public import DecoupledConsensusProofs.Protocol.Grades.HealthyHeadReady
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusInternal.Definitions.NamedLifecycle
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGTargetCanonicality
public import DecoupledConsensusProofs.Objects.SGTargetCompatibility
public import DecoupledConsensusProofs.Objects.SGTargetG1Concentration
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RawExactHeightSeed
public import DecoupledConsensusProofs.Protocol.Schedule.PostHealingBoundaryCanonicality
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionConfirmationCore
public import DecoupledConsensusProofs.Protocol.Grades.VoteBelowSource

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# SG proposal lifecycle

This file restores Claim 4 over the named proposal and prepared-read
interfaces. The schedule and direct projection declarations are live. The
complete earlier source remains below for audit. Each dependent declaration
open items at the first missing named producer.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open Internal.NamedOutageEntry
open Internal.NamedRecoveryRead
open Protocol
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The interior slot preceding the selected opening is positive. -/
theorem NamedSGProposalLifecycleInputs.previousSlotPositive
    {S : Setup V} {rho : Run V} {r : Round} {s : Slot}
    {A : Block V} {P : NamedBlock V}
    (h : NamedSGProposalLifecycleInputs S rho r s A P) : 0 < s := by
  have hopen : 2 ≤ S.hc.opening_slot (r + 1) := by
    unfold Protocol.HealConfig.opening_slot
    calc
      2 ≤ 1 * S.hc.R := by simpa using S.hc.R_ge_two
      _ ≤ (r + 1) * S.hc.R :=
        Nat.mul_le_mul_right S.hc.R (Nat.succ_le_succ (Nat.zero_le r))
  rw [← h.openingSlot] at hopen
  exact Nat.le_of_succ_le_succ hopen

/-- The selected opening vote is in the action horizon. -/
theorem NamedSGProposalLifecycleInputs.openingVoteInHorizon
    {S : Setup V} {rho : Run V} {r : Round} {s : Slot}
    {A : Block V} {P : NamedBlock V}
    (h : NamedSGProposalLifecycleInputs S rho r s A P) :
    Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
  calc
    Protocol.vote_time S.E (s + 1) ≤
        Protocol.confirmation_time S.E (s + 1) :=
      Protocol.vote_time_le_confirmation_time S.E (s + 1)
    _ = S.a (r + 1) := by
      rw [h.openingSlot]
      exact (Protocol.a_eq_confirmation_time S.hc S.E (r + 1)).symm
    _ ≤ rho.horizon := h.actionInHorizon

/-- The selected opening proposal is in the action horizon. -/
theorem NamedSGProposalLifecycleInputs.openingProposalInHorizon
    {S : Setup V} {rho : Run V} {r : Round} {s : Slot}
    {A : Block V} {P : NamedBlock V}
    (h : NamedSGProposalLifecycleInputs S rho r s A P) :
    Protocol.proposal_time S.E (s + 1) ≤ rho.horizon := by
  calc
    Protocol.proposal_time S.E (s + 1) ≤
        Protocol.confirmation_time S.E (s + 1) :=
      Protocol.proposal_time_le_confirmation_time S.E (s + 1)
    _ = S.a (r + 1) := by
      rw [h.openingSlot]
      exact (Protocol.a_eq_confirmation_time S.hc S.E (r + 1)).symm
    _ ≤ rho.horizon := h.actionInHorizon

/-- The previous vote cone is post-GST. -/
theorem NamedSGProposalLifecycleInputs.previousVotePostGST
    {S : Setup V} {rho : Run V} {r : Round} {s : Slot}
    {A : Block V} {P : NamedBlock V}
    (h : NamedSGProposalLifecycleInputs S rho r s A P) :
    S.E.t_GST ≤ Protocol.vote_time S.E s :=
  h.postProposalSnapshot.trans
    (le_of_lt (Protocol.proposal_time_lt_vote_time S.E s))

/-- The opening vote is post-GST. -/
theorem NamedSGProposalLifecycleInputs.openingVotePostGST
    {S : Setup V} {rho : Run V} {r : Round} {s : Slot}
    {A : Block V} {P : NamedBlock V}
    (h : NamedSGProposalLifecycleInputs S rho r s A P) :
    S.E.t_GST ≤ Protocol.vote_time S.E (s + 1) :=
  h.previousVotePostGST.trans
    (Protocol.vote_time_mono_slots S.E (Nat.le_succ s))

/-- The prepared proposer read uses the anchor recorded by the input. -/
theorem NamedSGProposalLifecycleInputs.proposerHealAnchor_eq
    {S : Setup V} {rho : Run V} {r : Round} {s : Slot}
    {A : Block V} {P : NamedBlock V}
    (h : NamedSGProposalLifecycleInputs S rho r s A P) :
    nodeAnchor S (proposerReadAt S rho (s + 1)) (r + 1) = A :=
  h.proposalAnchor

/-- Claim 3 supplies the named cone of the opening proposer's anchor. -/
theorem NamedSGProposalLifecycleInputs.anchorCone
    {S : Setup V} {rho : Run V} {r : Round} {s : Slot}
    {A : Block V} {P : NamedBlock V}
    (h : NamedSGProposalLifecycleInputs S rho r s A P) :
    NamedHonestVotesCone S rho s (fun X => Block.Preceq A X) := by
  apply h.concentration.supported h.proposerHonest
  have htime : DecoupledConsensusModel.Protocol.domain S.E S.hc (r + 1) .g1 =
      Protocol.proposal_time S.E (s + 1) := by
    rw [h.openingSlot]
    simp [DecoupledConsensusModel.Protocol.domain, DecoupledConsensusModel.Protocol.opening,
      DecoupledConsensusModel.Protocol.Phase.domainOffset]
  rw [namedG1At, htime]
  simpa only [proposerReadAt, NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
    Protocol.NamedStore.setClock, storeGrade, phaseGrade,
    Protocol.HealingStore.gradeView] using h.proposalAnchorG1

/-- Direct projection of the live-G1 parent disposition. -/
theorem NamedSGProposalLifecycleInputs.liveG1_preceq_proposedParent
    {S : Setup V} {rho : Run V} (_adm : Admissible S rho)
    (_hcom : HonestCommittees S rho.honest)
    {r : Round} {s : Slot} {A B : Block V} {P : NamedBlock V}
    (h : NamedSGProposalLifecycleInputs S rho r s A P)
    {w : V} (hw : w ∈ rho.honest)
    (hG1 : namedG1At S rho w (r + 1) B) :
    Block.Preceq B (proposedParent S rho (s + 1)) :=
  h.liveG1Parent w hw B hG1

/-- Direct projection of the preceding action-target parent disposition. -/
theorem NamedSGProposalLifecycleInputs.actionTarget_preceq_proposedParent
    {S : Setup V} {rho : Run V} (_adm : Admissible S rho)
    (_hcom : HonestCommittees S rho.honest)
    {r : Round} {s : Slot} {A : Block V} {P : NamedBlock V}
    (h : NamedSGProposalLifecycleInputs S rho r s A P)
    {v : V} (hv : v ∈ rho.honest) :
    Block.Preceq (actionSGBlockAt S rho v r)
      (proposedParent S rho (s + 1)) :=
  h.actionTargetParent v hv

/-- The lifecycle confirmation-read field has the current named local shape. -/
theorem NamedSGProposalLifecycleInputs.recoveryConfirmationRead
    {S : Setup V} {rho : Run V} {r : Round} {s : Slot}
    {A : Block V} {P : NamedBlock V}
    (h : NamedSGProposalLifecycleInputs S rho r s A P)
    {v : V} (hv : v ∈ rho.honest) :
    RecoveryProposalConfirmationRead S rho (s + 1) v P := by
  exact
    { root := (h.confirmationRead v hv).root
      anchor := (h.confirmationRead v hv).anchor
      candidate := (h.confirmationRead v hv).candidate }

/-- Restricting the prepared voter candidate domain can only remove
candidates. -/
private theorem namedLifecycle_voterCandidateTree_subset_filtered
    (E : Env V) (st : Protocol.Store V) :
    Protocol.voter_filtered_block_tree E st st.s ⊆
      Protocol.get_filtered_block_tree st.toHealing.toFG := by
  intro B hB
  have hB' : B ∈ Proofs.Optimistic.voter_candidate_tree E st.toHealing := by
    simpa only [Proofs.Optimistic.voter_candidate_tree_eq_protocol_voter_filtered_block_tree]
      using hB
  simp only [Proofs.Optimistic.voter_candidate_tree,
    Protocol.get_filtered_block_tree,
    Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
    Protocol.finalized_descendants, Protocol.viable,
    Finset.mem_filter, decide_eq_true_eq] at hB' ⊢
  obtain ⟨⟨⟨hBprocessed, hFB⟩, W, hWprocessed, hBW, hheight⟩,
    hroot⟩ := hB'
  have hBT : B ∈ st.T := by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
      at hBprocessed
    exact hBprocessed.1
  have hWT : W ∈ st.T := by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
      at hWprocessed
    exact hWprocessed.1
  exact ⟨⟨⟨hBT, hFB⟩, W, hWT, hBW, hheight⟩, hroot⟩

/-- The preceding honest vote cone makes the prepared proposal-free target
walk pass its pivot. -/
theorem NamedSGOpeningFrozenVoteAt.pivot_preceq_proposalFreeHead_core
    {S : Setup V} {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {r : Round} {s : Slot} {A : Block V} {P : NamedBlock V}
    (h : NamedSGProposalLifecycleInputs S rho r s A P)
    {v : V} (hv : v ∈ rho.honest)
    (frozen : NamedSGOpeningFrozenVoteAt S rho s A v P) :
    Block.Preceq A
      (Protocol.ghost (voterAnchorAt S rho v (s + 1))
        (namedWalkTargetTree S rho (s + 1) v P)
        (namedWalkTargetScore S rho (s + 1) v)
        (namedWalkTargetEligible S rho (s + 1) v)) := by
  let read := voteDutyRead S rho v (s + 1)
  let st := read.st.core
  let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  have hcandidate : A ∈ voterCandidateTreeAt S rho v (s + 1) :=
    Finset.mem_of_mem_erase frozen.pivotCandidate
  have hfiltered : A ∈ Protocol.get_filtered_block_tree st.toHealing.toFG := by
    apply namedLifecycle_voterCandidateTree_subset_filtered S.E st
    simpa only [st, read, voterCandidateTreeAt] using hcandidate
  have hroot : Block.Preceq
      (Protocol.get_fg_root st.toHealing.toFG) A :=
    Proofs.Records.preceq_get_fg_root_of_mem_filtered hfiltered
  have hinputs : GoldfishConeVoteInputs S rho s A v :=
    { candidate := hcandidate
      root := by simpa only [st, read] using hroot
      anchor := frozen.pivotAnchorCompatible
      path := by
        intro D hAD hDne hDA _
        exact Finset.mem_of_mem_erase
          (frozen.pivotPath (Block.preceq_trans hAD hDA) D hAD hDne hDA) }
  have hconfHor : Protocol.confirmation_time S.E s ≤ rho.horizon := by
    have hmono : Protocol.confirmation_time S.E s ≤
        Protocol.confirmation_time S.E (s + 1) := by
      rw [Protocol.confirmation_time_eq_support_cutoff_succ,
        Protocol.confirmation_time_eq_support_cutoff_succ]
      exact Proofs.Optimistic.support_cutoff_mono S.E
        (Nat.add_le_add_right (Nat.le_succ s) 1)
    exact hmono.trans (by
        rw [show Protocol.confirmation_time S.E (s + 1) = S.a (r + 1) by
          rw [h.openingSlot]
          exact (Protocol.a_eq_confirmation_time S.hc S.E (r + 1)).symm]
        exact h.actionInHorizon)
  have hwalk := goldfishCone_pathEligible_core S adm hcom h.previousSlotPositive
    h.previousVotePostGST hconfHor h.anchorCone hv hinputs
  have hhead := Protocol.goldfish_fork_choice_captures_supporter_majority
    S.E st.σ st.h_max st.T
      (namedWalkTargetTree S rho (s + 1) v P) st.s votes support
      (st.s - 1) (Proofs.Optimistic.ConeSupport.sub hwalk.1) hwalk.2.1
      frozen.pivotAnchorCompatible frozen.pivotPath
  simpa only [Protocol.goldfish_fork_choice,
    namedWalkTargetScore, namedWalkTargetEligible, st, read, votes, support]
    using hhead

/-- The preceding honest vote cone makes the prepared proposal-free target
walk pass its pivot. -/
theorem NamedSGOpeningFrozenVoteAt.pivot_preceq_proposalFreeHead
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {r : Round} {s : Slot} {A : Block V} {P : NamedBlock V}
    (h : NamedSGProposalLifecycleInputs S rho r s A P)
    {v : V} (hv : v ∈ rho.honest)
    (frozen : NamedSGOpeningFrozenVoteAt S rho s A v P) :
    Block.Preceq A
      (Protocol.ghost (voterAnchorAt S rho v (s + 1))
        (namedWalkTargetTree S rho (s + 1) v P)
        (namedWalkTargetScore S rho (s + 1) v)
        (namedWalkTargetEligible S rho (s + 1) v)) :=
  NamedSGOpeningFrozenVoteAt.pivot_preceq_proposalFreeHead_core
    (S := S) (rho := rho) adm.toNamedAdmissibleCore hcom h hv frozen


private theorem lifecycle_resolved_blocks_eq_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {source reader : V} (hsource : source ∈ rho.honest)
    (hreader : reader ∈ rho.honest) {sourceTime readerTime : Time}
    {u : GoldfishVote V} {H K : Block V}
    (hH : Block.find?
      (rho.storeBeforeTime S source sourceTime).core.T u.head = some H)
    (hK : Block.find?
      (rho.storeBeforeTime S reader readerTime).core.T u.head = some K) :
    H = K := by
  obtain ⟨HN, hHNe, hHNrun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
      adm.toNamedScheduleWellFormed hsource sourceTime
      (Proofs.HealingLemmas.find?_mem hH)
  obtain ⟨KN, hKNe, hKNrun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
      adm.toNamedScheduleWellFormed hreader readerTime
      (Proofs.HealingLemmas.find?_mem hK)
  have hroot : HN.root = KN.root := by
    rw [← Proofs.NamedWire.erase_root HN, ← Proofs.NamedWire.erase_root KN, hHNe, hKNe]
    exact (Proofs.HealingLemmas.find?_root hH).trans
      (Proofs.HealingLemmas.find?_root hK).symm
  have heq := adm.toNamedRootCollisionFree.root_injective
    HN KN hHNrun hKNrun HN KN (Or.inl (Proofs.NamedAncestry.named_self HN))
      (Or.inr (Proofs.NamedAncestry.named_self KN)) hroot
  calc
    H = HN.erase := hHNe.symm
    _ = KN.erase := congrArg NamedBlock.erase heq
    _ = K := hKNe


private theorem lifecycle_index_lt_strictEventIndex_of_time_lt
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {t : Time} {i : Nat} {e : Event V}
    (hi : rho.events[i]? = some e) (ht : e.time < t) :
    i < strictEventIndex rho t := by
  have hfilt : rho.events.filter (fun x => decide (x.time < t)) =
      rho.events.take (strictEventIndex rho t) := by
    simpa only [strictEventIndex] using
      Proofs.Optimistic.filter_eq_take S sch _ (Proofs.Optimistic.downward_lt t)
  have hmem : e ∈ rho.events.filter (fun x => decide (x.time < t)) :=
    List.mem_filter.mpr ⟨List.mem_of_getElem? hi, by simpa using ht⟩
  rw [hfilt] at hmem
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hmem
  obtain ⟨hjlen, hjget⟩ := List.getElem?_eq_some_iff.mp hj
  have hjn : j < strictEventIndex rho t := by
    have hlen := hjlen
    rw [List.length_take] at hlen
    exact lt_of_lt_of_le hlen (Nat.min_le_left _ _)
  have hj' : rho.events[j]? = some e := by
    rw [← List.getElem?_take_of_lt hjn]
    exact hj
  obtain ⟨hjl, hje⟩ := List.getElem?_eq_some_iff.mp hj'
  obtain ⟨hil, hie⟩ := List.getElem?_eq_some_iff.mp hi
  have hji : j = i := by
    exact (List.Nodup.getElem_inj_iff
      (NamedScheduleWellFormed.nodup sch)).mp (hje.trans hie.symm)
  simpa only [← hji] using hjn

/-- A held named body whose retained stamp precedes a public cutoff was
already held at the strict cutoff read. -/
private theorem lifecycle_body_held_at_public_cut_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {reader : V} (hreader : reader ∈ rho.honest)
    {B : NamedBlock V} {cut read : Time}
    (hpublic : PublicTime S cut)
    (hB : B ∈ (NamedRun.stateBeforeTime S rho read reader).st.bodies)
    (hstamp : stampedBefore
      (NamedRun.stateBeforeTime S rho read reader).st.core.timestamp_block
      cut B.erase = true) :
    B ∈ (NamedRun.stateBeforeTime S rho cut reader).st.bodies := by
  let n := strictEventIndex rho read
  have heqRead := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedScheduleWellFormed read) reader
  have hBn : B ∈ (rho.stateBefore S n reader).st.bodies := by
    simpa only [n, heqRead] using hB
  have hstampN : stampedBefore
      (rho.stateBefore S n reader).st.core.timestamp_block cut B.erase = true := by
    simpa only [n, heqRead] using hstamp
  have hprocessed : Object.processed (rho.stateBefore S n reader).st
      (Object.block B) = true := by
    simpa only [Object.processed, NamedReceipt.processed,
      decide_eq_true_eq] using hBn
  rcases Protocol.acceptsAt_block_of_processed
      S rho reader n B hprocessed with hgen | hacc
  · subst B
    exact (Proofs.NamedRuntime.stateBeforeTime_invariants S rho cut reader).1.1.1.2.2.1.1
  · obtain ⟨i, hi, t, haccepts⟩ := hacc
    have ht : t < cut :=
      Protocol.HonestWeightMajority.acceptsAt_block_lt_of_stamp_before_core
        S adm hreader haccepts (Nat.succ_le_of_lt hi) hpublic hstampN
    obtain ⟨hhandle, -, hpost⟩ := haccepts
    obtain ⟨hindex, e, he, -, het⟩ := hhandle
    have hiCut : i < strictEventIndex rho cut := by
      apply lifecycle_index_lt_strictEventIndex_of_time_lt
        S adm.toNamedScheduleWellFormed he
      simpa only [← het] using ht
    have hBi : B ∈ (rho.stateBefore S (i + 1) reader).st.bodies := by
      simpa only [Object.processed, NamedReceipt.processed,
        decide_eq_true_eq] using hpost
    have hBCut := NamedBodyRetention.stateBefore_bodies_mono
      S rho reader (Nat.succ_le_of_lt hiCut) hBi
    change B ∈ ((Run.stateBeforeTime S rho cut) reader).st.bodies
    unfold Run.stateBeforeTime
    rw [stateBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedScheduleWellFormed cut]
    exact hBCut


/-- Candidate-local proposal and vote views give the same Goldfish score on
their common prepared candidate. -/
theorem NamedSGOpeningFrozenVoteAt.scoreEq_core
    {S : Setup V} {rho : Run V} (adm : AdmissibleCore S rho)
    {r : Round} {s : Slot} {A : Block V} {P : NamedBlock V}
    (h : NamedSGProposalLifecycleInputs S rho r s A P)
    {v : V} (hv : v ∈ rho.honest)
    (frozen : NamedSGOpeningFrozenVoteAt S rho s A v P) :
    ∀ C,
      C ∈ namedWalkSourceTree S rho (s + 1) →
      C ∈ namedWalkTargetTree S rho (s + 1) v P →
      namedWalkTargetScore S rho (s + 1) v C =
        namedWalkSourceScore S rho (s + 1) C := by
  intro C hCsource hCtarget
  let source := proposalDutyRead S rho (s + 1)
  let target := voteDutyRead S rho v (s + 1)
  let targetRaw := Protocol.voter_view S.E
    target.st.core.toHealing.toFG.toSG.toGoldfishStore target.st.core.s
  let targetSupport := Protocol.voter_support_view S.E
    target.st.core.toHealing.toFG.toSG.toGoldfishStore target.st.core.s
  have hsourceSlot : source.st.core.s = s + 1 := by
    simpa only [source, proposalDutyRead, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      Proofs.Optimistic.slotOf_proposal_time S.E (s + 1)
  have htargetSlot : target.st.core.s = s + 1 := by
    simpa only [target] using Proofs.Optimistic.voteDutyRead_slot S rho v (s + 1)
  have hPtargetCandidate : P.erase ∈ voterCandidateTreeAt S rho v (s + 1) :=
    frozen.proposalCandidate
  have hPtargetFiltered : P.erase ∈
      Protocol.get_filtered_block_tree target.st.core.toHealing.toFG := by
    apply namedLifecycle_voterCandidateTree_subset_filtered S.E target.st.core
    simpa only [target, voterCandidateTreeAt] using hPtargetCandidate
  have hPtargetT : P.erase ∈ target.st.core.T :=
    Proofs.Records.get_filtered_block_tree_subset _ hPtargetFiltered
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed
      (Protocol.vote_time S.E (s + 1))
  have hPprefix : P.erase ∈ (rho.stateBefore S n v).st.core.T := by
    simpa only [target, voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Run.storeBeforeTime, hn] using hPtargetT
  have hslots : ∀ u ∈ P.gf_votes, u.slot + 1 = P.slot := by
    intro u hu
    obtain ⟨np, hnp, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
      S adm.toNamedScheduleWellFormed
        (Protocol.proposal_time S.E (s + 1))
    have huFin : u ∈ source.st.core.pool (source.st.core.s - 1) := by
      change u ∈ (proposerReadAt S rho (s + 1)).st.core.pool
        ((proposerReadAt S rho (s + 1)).st.core.s - 1)
      rw [← Protocol.proposedBlock_raw_eq_proposer_pool
        S rho (s + 1) h.proposal]
      exact List.mem_toFinset.mpr hu
    have huFin' : u ∈ source.st.core.pool s := by
      simpa only [hsourceSlot, Nat.add_sub_cancel] using huFin
    have huPool : u ∈
        (rho.stateBefore S np (S.E.proposer (s + 1))).st.core.gf_votes s := by
      simpa only [source, proposalDutyRead, proposerReadAt,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock, Protocol.Store.pool,
        List.mem_toFinset, Run.storeBeforeTime, hnp] using huFin'
    have hus := (Protocol.poolStamps_stateBefore S
      adm.toNamedScheduleWellFormed
      (S.E.proposer (s + 1)) np).slot s u huPool
    calc
      u.slot + 1 = s + 1 := congrArg (· + 1) hus
      _ = P.slot := (proposedBlockAt_slot S rho (s + 1) h.proposal).symm
  have hrawSubset : P.gf_votes.toFinset ⊆ targetRaw := by
    intro u hu
    have hPslot : P.erase.slot = target.st.core.toHealing.s := by
      rw [Proofs.NamedWire.erase_slot,
        proposedBlockAt_slot S rho (s + 1) h.proposal]
      exact htargetSlot.symm
    have hsub := Protocol.carried_raw_subset_voter_view
      S.E target.st.core.toHealing.toFG.toSG.toGoldfishStore hPtargetT
      hPslot
      (by
        intro x hx
        have hx' : x ∈ P.gf_votes := by
          simpa only [Proofs.NamedWire.erase_goldfish_votes] using hx
        simpa only [Proofs.NamedWire.erase_slot] using hslots x hx')
    exact hsub (by simpa only [Proofs.NamedWire.erase_goldfish_votes] using hu)
  have hbridge : Protocol.CandidateScorePreservingViewExtension
      source.st.core.T target.st.core.T P.gf_votes.toFinset
      P.gf_support_votes.toFinset targetRaw targetSupport C := by
    refine
      { raw_subset := hrawSubset
        raw_extra_equiv := ?_
        forward := ?_
        backward := ?_ }
    · intro u hu hnot
      simpa only [Proofs.NamedWire.erase_goldfish_votes] using
        frozen.rawExtra u (by simpa only [targetRaw, htargetSlot] using hu)
          (by simpa only [Proofs.NamedWire.erase_goldfish_votes] using hnot)
    · intro u hu htargets
      obtain ⟨H, hfindSource, hCH⟩ := Protocol.targets_under_iff.mp htargets
      have hHsource : H ∈ source.st.core.T :=
        Proofs.HealingLemmas.find?_mem hfindSource
      have hHpre : H ∈ (rho.storeBeforeTime S (S.E.proposer (s + 1))
          (Protocol.proposal_time S.E (s + 1))).core.T := by
        simpa only [source, proposalDutyRead, proposerReadAt,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock] using hHsource
      obtain ⟨HN, hHNbody, hHNerase⟩ :=
        Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
          (Protocol.proposal_time S.E (s + 1))
          (S.E.proposer (s + 1)) hHpre
      have hFC : Block.Preceq target.st.core.F C := by
        have hCfull : C ∈ voterCandidateTreeAt S rho v (s + 1) :=
          Finset.mem_of_mem_erase hCtarget
        have hCfiltered := namedLifecycle_voterCandidateTree_subset_filtered
          S.E target.st.core hCfull
        simp only [Protocol.get_filtered_block_tree,
          Protocol.get_filtered_block_tree_from,
          Protocol.viable_tree, Protocol.finalized_descendants,
          Protocol.viable, Finset.mem_filter,
          decide_eq_true_eq] at hCfiltered
        obtain ⟨⟨⟨_, hFC⟩, _, _, _, _⟩, _⟩ := hCfiltered
        exact hFC
      have hFH : Block.Preceq target.st.core.F H :=
        Block.preceq_trans hFC hCH.2
      have hdeadline : max (Protocol.proposal_time S.E (s + 1)) S.E.t_GST +
          S.E.Δ ≤ Protocol.vote_time S.E (s + 1) := by
        rw [max_eq_left]
        · exact le_of_eq (by
            unfold Protocol.proposal_time Protocol.vote_time
            ring)
        · exact h.postProposalSnapshot.trans
            (Protocol.proposal_time_mono S.E (Nat.le_succ s))
      have hrelay := NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
        S rho adm (S.E.proposer (s + 1))
        h.proposerHonest v hv HN (Protocol.proposal_time S.E (s + 1))
        (Protocol.vote_time S.E (s + 1))
        (Protocol.vote_time S.E (s + 1)) hHNbody hdeadline le_rfl
        h.openingVoteInHorizon (by
          rw [hHNerase]
          simpa only [target, voteDutyRead,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom,
            Protocol.NamedStore.setClock] using hFH)
      have hfindTarget : Block.find? target.st.core.T u.head = some H := by
        have hfind := hrelay.2.2
        rw [hHNerase] at hfind
        have hroot : H.root = u.head := Proofs.HealingLemmas.find?_root hfindSource
        simpa only [target, voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock, hroot] using hfind
      have hresolved : Protocol.resolved target.st.core.T u = true := by
        unfold Protocol.resolved
        rw [hfindTarget]
        simp [hCH.1]
      have huList : u ∈ P.gf_support_votes := List.mem_toFinset.mp hu
      have huslot : u.slot + 1 = P.erase.slot := by
        rw [Proofs.NamedWire.erase_slot]
        exact hslots u (by
          rw [Protocol.proposedBlock_gf_support_votes
            S rho (s + 1) h.proposal] at huList
          have hraw := (List.mem_filter.mp huList).1
          rw [Protocol.proposedBlock_gf_votes
            S rho (s + 1) h.proposal]
          exact hraw)
      have huTarget : u ∈ targetSupport := by
        exact Protocol.mem_voter_support_view_of_carried S.E
          target.st.core.toHealing.toFG.toSG.toGoldfishStore hPtargetT
          (by rw [Proofs.NamedWire.erase_slot,
            proposedBlockAt_slot S rho (s + 1) h.proposal, htargetSlot])
          (by simpa only [Proofs.NamedWire.erase_goldfish_support] using huList)
          hresolved huslot
      exact Or.inl ⟨huTarget,
        Protocol.targets_under_iff.mpr ⟨H, hfindTarget, hCH.1, hCH.2⟩⟩
    · intro u hu htargets
      have huRaw : u ∈ targetRaw := by
        apply (Protocol.voter_support_view_subset S.E
          target.st.core.toHealing.toFG.toSG.toGoldfishStore target.st.core.s
          (by
            intro D hD x hx
            have hDprefix : D ∈ (rho.stateBefore S n v).st.core.T := by
              simpa only [target, voteDutyRead,
                NamedActionReads.confirmationReadAt,
                NamedActionReads.confirmationReadFrom,
                Protocol.NamedStore.setClock, Run.storeBeforeTime, hn] using hD
            exact Proofs.Optimistic.carried_support_subset_of_mem_T_core
              S adm v n hDprefix x hx)) hu
      change u ∈ Protocol.voter_support_view S.E
        target.st.core.toHealing.toFG.toSG.toGoldfishStore target.st.core.s at hu
      rw [Protocol.voter_support_view, Finset.mem_union] at hu
      rcases hu with hpool | hcarried
      · by_cases huSource : u ∈ P.gf_votes.toFinset
        · obtain ⟨K, hfindTarget, hCK⟩ :=
            Protocol.targets_under_iff.mp htargets
          have hKtarget : K ∈ target.st.core.T :=
            Proofs.HealingLemmas.find?_mem hfindTarget
          have hKpre : K ∈ (rho.storeBeforeTime S v
              (Protocol.vote_time S.E (s + 1))).core.T := by
            simpa only [target, voteDutyRead,
              NamedActionReads.confirmationReadAt,
              NamedActionReads.confirmationReadFrom,
              Protocol.NamedStore.setClock] using hKtarget
          obtain ⟨KN, hKNbody, hKNerase⟩ :=
            Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
              (Protocol.vote_time S.E (s + 1)) v hKpre
          have hstamp : stampedBefore
              (rho.storeBeforeTime S v
                (Protocol.vote_time S.E (s + 1))).core.timestamp_block
              (Protocol.view_freeze S.E s) KN.erase = true := by
            have hstampK : stampedBefore target.st.core.timestamp_block
                (Protocol.view_freeze S.E s) K = true := by
              have hvoteStamp := (Finset.mem_filter.mp hpool).2
              exact Protocol.HonestWeightMajority.stampedBefore_block_of_resolution
                hfindTarget (by
                  simpa only [target, htargetSlot, Nat.add_sub_cancel] using
                    hvoteStamp)
            simpa only [target, voteDutyRead,
              NamedActionReads.confirmationReadAt,
              NamedActionReads.confirmationReadFrom,
              Protocol.NamedStore.setClock, hKNerase] using hstampK
          have hKNfreeze := lifecycle_body_held_at_public_cut_core
            S adm hv (Protocol.publicTime_view_freeze S s) hKNbody hstamp
          have hFC : Block.Preceq source.st.core.F C := by
            simp only [namedWalkSourceTree,
              Protocol.get_filtered_block_tree,
              Protocol.get_filtered_block_tree_from,
              Protocol.viable_tree, Protocol.finalized_descendants,
              Protocol.viable, Finset.mem_filter,
              decide_eq_true_eq] at hCsource
            obtain ⟨⟨⟨_, hFC⟩, _, _, _, _⟩, _⟩ := hCsource
            exact hFC
          have hFK : Block.Preceq source.st.core.F K :=
            Block.preceq_trans hFC hCK.2
          have hdeadline : max (Protocol.view_freeze S.E s) S.E.t_GST +
              S.E.Δ ≤ Protocol.proposal_time S.E (s + 1) := by
            rw [max_eq_left]
            · exact le_of_eq
                (Protocol.view_freeze_add_delta_eq_proposal_time_succ S.E s)
            · exact h.postProposalSnapshot.trans
                (by
                  unfold Protocol.proposal_time Protocol.view_freeze
                  linarith [S.E.Δ_pos])
          have hrelay := NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
            S rho adm v hv (S.E.proposer (s + 1))
            h.proposerHonest KN (Protocol.view_freeze S.E s)
            (Protocol.proposal_time S.E (s + 1))
            (Protocol.proposal_time S.E (s + 1)) hKNfreeze hdeadline le_rfl
            h.openingProposalInHorizon (by
              rw [hKNerase]
              simpa only [source, proposalDutyRead, proposerReadAt,
                NamedActionReads.confirmationReadAt,
                NamedActionReads.confirmationReadFrom,
                Protocol.NamedStore.setClock] using hFK)
          have hfindSource : Block.find? source.st.core.T u.head = some K := by
            have hfind := hrelay.2.2
            rw [hKNerase] at hfind
            have hroot : K.root = u.head := Proofs.HealingLemmas.find?_root hfindTarget
            simpa only [source, proposalDutyRead, proposerReadAt,
              NamedActionReads.confirmationReadAt,
              NamedActionReads.confirmationReadFrom,
              Protocol.NamedStore.setClock, hroot] using hfind
          have huList : u ∈ P.gf_votes := List.mem_toFinset.mp huSource
          have huSupport : u ∈ P.gf_support_votes.toFinset := by
            rw [List.mem_toFinset,
              Protocol.proposedBlock_gf_support_votes
                S rho (s + 1) h.proposal]
            change u ∈ Protocol.proposer_support_view
              (proposerReadAt S rho (s + 1)).st.core.toHealing.toFG.toSG.toGoldfishStore
              (proposerReadAt S rho (s + 1)).st.core.toHealing.s
            rw [Protocol.proposer_support_view, List.mem_filter]
            refine ⟨?_, ?_⟩
            · rw [Protocol.proposedBlock_gf_votes
                S rho (s + 1) h.proposal] at huList
              simpa only [proposalInputAt, Protocol.proposal_input_with,
                Protocol.with_proposal_input] using huList
            · unfold Protocol.resolved
              have hfindSource' : Block.find?
                  (proposerReadAt S rho (s + 1)).st.core.toHealing.T
                  u.head = some K := by
                simpa only [source, proposalDutyRead,
                  Protocol.Store.toHealing] using hfindSource
              rw [hfindSource']
              simp [hCK.1]
          exact Or.inl ⟨huSupport,
            Protocol.targets_under_iff.mpr ⟨K, hfindSource, hCK.1, hCK.2⟩⟩
        · exact Or.inr (by
            simpa only [Proofs.NamedWire.erase_goldfish_votes] using
              frozen.rawExtra u
                (by simpa only [targetRaw, htargetSlot] using huRaw)
                (by simpa only [Proofs.NamedWire.erase_goldfish_votes] using huSource))
      · rw [Finset.mem_biUnion] at hcarried
        obtain ⟨D, hD, huD⟩ := hcarried
        rw [Finset.mem_filter] at hD huD
        have hDprefix : D ∈ (rho.stateBefore S n v).st.core.T := by
          simpa only [target, voteDutyRead,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom,
            Protocol.NamedStore.setClock, Run.storeBeforeTime, hn] using hD.1
        have hDeq : D = P.erase := unique_slot_block_in_store_core
          S adm (Nat.succ_pos s) h.proposerHonest
          hDprefix hPprefix (by simpa only [htargetSlot] using hD.2)
          (by rw [Proofs.NamedWire.erase_slot,
            proposedBlockAt_slot S rho (s + 1) h.proposal])
        subst D
        have huSource : u ∈ P.gf_support_votes.toFinset := by
          simpa only [Proofs.NamedWire.erase_goldfish_support] using huD.1
        obtain ⟨K, hfindTarget, hCK⟩ :=
          Protocol.targets_under_iff.mp htargets
        have hresolvedSource : Protocol.resolved source.st.core.T u = true := by
          have huList : u ∈ P.gf_support_votes :=
            List.mem_toFinset.mp huSource
          rw [Protocol.proposedBlock_gf_support_votes
            S rho (s + 1) h.proposal] at huList
          exact of_decide_eq_true (by
            simpa only [source, proposalDutyRead, Protocol.Store.toHealing]
              using (List.mem_filter.mp huList).2)
        obtain ⟨H, hfindSource⟩ : ∃ H, Block.find? source.st.core.T u.head = some H := by
          cases hfind : Block.find? source.st.core.T u.head with
          | none => simp [Protocol.resolved, hfind] at hresolvedSource
          | some H => exact ⟨H, rfl⟩
        have hHK : H = K := lifecycle_resolved_blocks_eq_core
          S adm h.proposerHonest hv
          (sourceTime := Protocol.proposal_time S.E (s + 1))
          (readerTime := Protocol.vote_time S.E (s + 1))
          (by simpa only [source, proposalDutyRead, proposerReadAt,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom,
            Protocol.NamedStore.setClock] using hfindSource)
          (by simpa only [target, voteDutyRead,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom,
            Protocol.NamedStore.setClock] using hfindTarget)
        have hHslot : H.slot ≤ u.slot := by
          simpa only [← hHK] using hCK.1
        have hHC : C.preceq H = true := by
          simpa only [← hHK] using hCK.2
        exact Or.inl ⟨huSource,
          Protocol.targets_under_iff.mpr ⟨H, hfindSource, hHslot, hHC⟩⟩
  have hscore := hbridge.goldfish_score_eq S.E (s + 1 - 1)
  have hsourceSlot' : (proposerReadAt S rho (s + 1)).st.core.s = s + 1 := by
    simpa only [source, proposalDutyRead] using hsourceSlot
  symm
  simpa only [namedWalkSourceScore, namedWalkTargetScore, source, target,
    targetRaw, targetSupport, hsourceSlot, hsourceSlot', htargetSlot,
    Nat.add_sub_cancel, Protocol.proposedBlock_gf_votes
      S rho (s + 1) h.proposal,
    Protocol.proposedBlock_gf_support_votes S rho (s + 1) h.proposal,
    proposalInputAt, Protocol.proposal_input_with,
    Protocol.with_proposal_input, id_eq, proposalDutyRead,
    Protocol.Store.toHealing]
    using hscore

/-- Candidate-local proposal and vote views give the same Goldfish score on
their common prepared candidate. -/
theorem NamedSGOpeningFrozenVoteAt.scoreEq
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {r : Round} {s : Slot} {A : Block V} {P : NamedBlock V}
    (h : NamedSGProposalLifecycleInputs S rho r s A P)
    {v : V} (hv : v ∈ rho.honest)
    (frozen : NamedSGOpeningFrozenVoteAt S rho s A v P) :
    ∀ C,
      C ∈ namedWalkSourceTree S rho (s + 1) →
      C ∈ namedWalkTargetTree S rho (s + 1) v P →
      namedWalkTargetScore S rho (s + 1) v C =
        namedWalkSourceScore S rho (s + 1) C :=
  NamedSGOpeningFrozenVoteAt.scoreEq_core
    (S := S) (rho := rho) adm.toNamedAdmissibleCore h hv frozen

set_option maxHeartbeats 1000000 in
/-- One honest opening voter transfers the prepared proposal walk. -/
theorem NamedSGOpeningFrozenVoteAt.voteStoreExtends_core
    {S : Setup V} {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {r : Round} {s : Slot} {A : Block V} {P : NamedBlock V}
    (h : NamedSGProposalLifecycleInputs S rho r s A P)
    {v : V} (hv : v ∈ rho.honest)
    (frozen : NamedSGOpeningFrozenVoteAt S rho s A v P) :
    Proofs.Optimistic.NamedVoteStoreExtends S rho v (s + 1)
      (namedWalkTargetTree S rho (s + 1) v P)
      (proposedParent S rho (s + 1)) P := by
  have htime : DecoupledConsensusModel.Protocol.domain S.E S.hc (r + 1) .g1 =
      Protocol.proposal_time S.E (s + 1) := by
    rw [h.openingSlot]
    simp [DecoupledConsensusModel.Protocol.domain, DecoupledConsensusModel.Protocol.opening,
      DecoupledConsensusModel.Protocol.Phase.domainOffset]
  have hG1 : namedG1At S rho (S.E.proposer (s + 1)) (r + 1) A := by
    rw [namedG1At, htime]
    simpa only [proposerReadAt, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, Protocol.NamedStore.setClock,
      storeGrade, phaseGrade, Protocol.HealingStore.gradeView] using
        h.proposalAnchorG1
  have hpivotParent : Block.Preceq A (proposedParent S rho (s + 1)) :=
    h.liveG1Parent (S.E.proposer (s + 1)) h.proposerHonest A hG1
  have hround : S.hc.round_of (proposerReadAt S rho (s + 1)).st.core.s =
      r + 1 := by
    simpa only [proposerReadAt, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.slotOf_proposal_time, h.openingSlot] using
        round_of_opening_slot_eq S.hc (r + 1)
  have hsourcePivot : Block.Preceq
      (Protocol.get_sg_root_with
        (NamedProfile.gradeContract (proposerReadAt S rho (s + 1)).cache)
        S.E S.hc (proposerReadAt S rho (s + 1)).st.core.toHealing
        (S.hc.round_of (proposerReadAt S rho (s + 1)).st.core.s)) A := by
    change Block.Preceq
      (nodeAnchor S (proposerReadAt S rho (s + 1))
        (S.hc.round_of (proposerReadAt S rho (s + 1)).st.core.s)) A
    rw [hround, h.proposalAnchor]
    exact Block.preceq_self A
  exact Protocol.namedProposalWalkTransferred_of_frozenCompatiblePivot_core
    S adm h.proposal h.proposerHonest hv frozen.proposalCandidate
      frozen.proposalAnchorCompatible hsourcePivot hpivotParent
      (frozen.pivot_preceq_proposalFreeHead_core adm hcom h hv)
      frozen.suffix (frozen.scoreEq_core adm h hv)

set_option maxHeartbeats 1000000 in
/-- One honest opening voter transfers the prepared proposal walk. -/
theorem NamedSGOpeningFrozenVoteAt.voteStoreExtends
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {r : Round} {s : Slot} {A : Block V} {P : NamedBlock V}
    (h : NamedSGProposalLifecycleInputs S rho r s A P)
    {v : V} (hv : v ∈ rho.honest)
    (frozen : NamedSGOpeningFrozenVoteAt S rho s A v P) :
    Proofs.Optimistic.NamedVoteStoreExtends S rho v (s + 1)
      (namedWalkTargetTree S rho (s + 1) v P)
      (proposedParent S rho (s + 1)) P :=
  NamedSGOpeningFrozenVoteAt.voteStoreExtends_core
    (S := S) (rho := rho) adm.toNamedAdmissibleCore hcom h hv frozen

/-- Every honest opening voter transfers the prepared proposal walk. -/
theorem NamedSGProposalLifecycleInputs.voteStoresExtend
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {r : Round} {s : Slot} {A : Block V} {P : NamedBlock V}
    (h : NamedSGProposalLifecycleInputs S rho r s A P) :
    Protocol.VoteStoresExtend S rho (s + 1) P := by
  intro v hv hcommittee
  exact ⟨namedWalkTargetTree S rho (s + 1) v P,
    proposedParent S rho (s + 1),
    (h.frozenVote v hv hcommittee).voteStoreExtends adm hcom h hv⟩

/-- The transferred prepared walks make every honest opening vote name the
bound proposal. -/
theorem NamedSGProposalLifecycleInputs.honestVotesName
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {r : Round} {s : Slot} {A : Block V} {P : NamedBlock V}
    (h : NamedSGProposalLifecycleInputs S rho r s A P) :
    NamedHonestVotesName S rho (s + 1) P.erase := by
  exact Protocol.honestVotesName_of_voteStoresExtend S adm
    (Nat.succ_pos s) h.openingVoteInHorizon (h.voteStoresExtend adm hcom)

/-- Each honest prepared confirmation read genuinely selects the bound
proposal and records it at the confirmation time. -/
theorem NamedSGProposalLifecycleInputs.genuineConfirmation
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {r : Round} {s : Slot} {A : Block V} {P : NamedBlock V}
    (h : NamedSGProposalLifecycleInputs S rho r s A P)
    {v : V} (hv : v ∈ rho.honest) :
    GenuineConfirmationAt S rho v (s + 1) ∧
      (rho.storeAt S v (Protocol.confirmation_time S.E (s + 1))).live_confirmed =
        P.erase := by
  let read := confirmationInputRead S rho v (s + 1)
  let contract := NamedProfile.gradeContract read.cache
  have hlocal := h.recoveryConfirmationRead hv
  have hrun : NamedRun.blockInRun S rho P :=
    proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
      (s + 1) (Nat.succ_pos s) h.proposerHonest
      h.openingProposalInHorizon h.proposal
  have hsupport : HonestSupport S.E read.st.core.T
      (confirmationVotes S.E read.st.core (s + 1)) (s + 1)
      rho.honest P.erase := by
    exact honestSupport_confVotes_after_gst_of_names S adm hcom
      (Nat.succ_pos s) h.openingVotePostGST
      (by
        rw [show Protocol.confirmation_time S.E (s + 1) = S.a (r + 1) by
          rw [h.openingSlot]
          exact (Protocol.a_eq_confirmation_time S.hc S.E (r + 1)).symm]
        exact h.actionInHorizon)
      hrun (h.honestVotesName adm hcom) hv hlocal.root hlocal.candidate
  have hvalid : Protocol.VoteSetValid S.E (s + 1)
      (confirmationLate S.E read.st.core (s + 1)) := by
    have hvalid' : Protocol.VoteSetValid S.E (s + 1)
        (confLate S.E (Proofs.Optimistic.confStore S rho v (s + 1)) (s + 1)) := by
      simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using
        voteSetValid_confLate_stateBeforeTime S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v
          (Protocol.confirmation_time S.E (s + 1)) (s + 1)
    simpa only [read, confirmationLate, confLate,
      Proofs.Optimistic.confStore_eq_confirmationInputRead] using hvalid'
  have hpath : ∀ C : Block V,
      Block.Preceq (namedConfirmationAnchor S read) C →
      C ≠ namedConfirmationAnchor S read →
      Block.Preceq C P.erase → C ∈ confTree read.st.core := by
    have hpath' := Protocol.confPath_of_candidate S
      (show P.erase ∈ confTree (Proofs.Optimistic.confStore S rho v (s + 1)) from by
        simpa only [read, Proofs.Optimistic.confStore_eq_confirmationInputRead] using
          hlocal.candidate)
    simpa only [read, Proofs.Optimistic.confStore_eq_confirmationInputRead] using hpath'
  have hanchor : Block.Preceq
      (confAnchorWith contract S.E S.hc
        (Proofs.Optimistic.confStore S rho v (s + 1))) P.erase := by
    simpa only [contract, read, namedConfirmationAnchor,
      Proofs.Optimistic.confStore_eq_confirmationInputRead] using hlocal.anchor
  obtain ⟨hwalk, helig⟩ := confWalkWith_eq_of_support contract S.E S.hc
    (Proofs.Optimistic.confStore S rho v (s + 1)) (s + 1) rho.honest P.erase
    (by simpa only [read, Proofs.Optimistic.confStore_eq_confirmationInputRead,
      confirmationVotes, confVotes] using hsupport)
    (by simpa only [confirmationLate, confLate] using hvalid)
    hanchor
    (by simpa only [contract, read, namedConfirmationAnchor,
      Proofs.Optimistic.confStore_eq_confirmationInputRead] using hpath)
  have hwrite : (Protocol.update_confirmation_with contract S.E S.hc
      (Proofs.Optimistic.confStore S rho v (s + 1)) (s + 1)).live_confirmed =
      P.erase := by
    rw [update_confirmation_with_live_confirmed, hwalk, if_pos helig]
  have hrecord := Proofs.Optimistic.live_confirmed_eq_update S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv (s + 1)
    (by
      rw [show Protocol.confirmation_time S.E (s + 1) = S.a (r + 1) by
        rw [h.openingSlot]
        exact (Protocol.a_eq_confirmation_time S.hc S.E (r + 1)).symm]
      exact h.actionInHorizon)
  have hrecordP :
      (rho.storeAt S v (Protocol.confirmation_time S.E (s + 1))).live_confirmed =
        P.erase := by
    rw [hrecord]
    simpa only [contract, read] using hwrite
  refine ⟨?_, hrecordP⟩
  unfold GenuineConfirmationAt
  refine ⟨?_, ?_⟩
  · rw [hrecordP]
    simpa only [namedConfirmationWalk, read, contract,
      Proofs.Optimistic.confStore_eq_confirmationInputRead] using hwalk.symm
  · change confEligible S.E (Proofs.Optimistic.confStore S rho v (s + 1))
      (s + 1) (confWalkWith contract S.E S.hc
        (Proofs.Optimistic.confStore S rho v (s + 1)) (s + 1)) = true
    rw [hwalk]
    exact helig

omit [Fintype V] in
private theorem namedLifecycle_parent_preceq (P : NamedBlock V) :
    Block.Preceq P.parent.erase P.erase := by
  cases P with
  | genesis => exact Block.preceq_self _
  | node parent slot root votes support rows proposer =>
      exact Proofs.NamedWire.erase_preceq
        (Proofs.NamedAncestry.named_extend slot root votes support rows proposer
          (Proofs.NamedAncestry.named_self parent))

private theorem namedLifecycle_proposedParent_preceq
    (S : Setup V) (rho : Run V) (s : Slot) {P : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P) :
    Block.Preceq (proposedParent S rho s) P.erase := by
  obtain ⟨parent, hparent, hparentErase⟩ := proposedBlockAt_parent S rho s hP
  have hparentEq : P.parent = parent := by
    cases P with
    | genesis => simp only [NamedBlock.parent?, reduceCtorEq] at hparent
    | node p slot root votes support rows proposer =>
        simpa only [NamedBlock.parent, NamedBlock.parent?, Option.some.injEq]
          using hparent
  rw [← hparentErase, ← hparentEq]
  exact namedLifecycle_parent_preceq P

/-- The genuine opening confirmation is the exact value read by each honest
Section 7 action. -/
theorem NamedSGProposalLifecycleInputs.liveConfirmedAtAction
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {r : Round} {s : Slot} {A : Block V} {P : NamedBlock V}
    (h : NamedSGProposalLifecycleInputs S rho r s A P) :
    ∀ v ∈ rho.honest,
      (actionReadAt S rho v (r + 1)).st.core.live_confirmed = P.erase := by
  have hpost : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot (r + 1)) := by
    rw [← h.openingSlot]
    exact h.openingVotePostGST
  have hresult := openingProposal_liveConfirmed_actionStore_after_gst_of_localReads
    S adm hcom (Nat.succ_pos r) hpost h.actionInHorizon
      (by simpa only [← h.openingSlot] using h.proposerHonest)
      (by simpa only [← h.openingSlot] using h.proposal)
      (by simpa only [← h.openingSlot] using h.voteStoresExtend adm hcom)
      (by
        intro v hv
        simpa only [← h.openingSlot] using h.recoveryConfirmationRead hv)
  simpa only [actionStoreAt] using hresult




/-- The G0-domain freeze is clear for the bound opening proposal.

The relative carrier input is the  grade-formation interface. It places
every frozen G0 root below an honest round-`r` action carrier. The lifecycle
parent field then places that carrier below the proposal. -/
theorem NamedSGProposalLifecycleInputs.g0ClearAtAction
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {r : Round} {s : Slot} {A : Block V} {P : NamedBlock V}
    (hwindow : RelativeCarrierWindowAt S rho r .g0)
    (hforming : GradeFormingMajority S rho (r + 1))
    (h : NamedSGProposalLifecycleInputs S rho r s A P) :
    ∀ v ∈ rho.honest,
      nodeClear S (actionReadAt S rho v (r + 1))
        (r + 1) P.erase = true := by
  have hparentP : Block.Preceq (proposedParent S rho (s + 1)) P.erase :=
    namedLifecycle_proposedParent_preceq S rho (s + 1) h.proposal
  intro v hv
  let n := actionReadAt S rho v (r + 1)
  have hframe := actionFrame_g0 S adm.toNamedAdmissibleCore hv
    (Nat.succ_pos r) h.actionInHorizon
  unfold nodeClear nodeRead
  change DecoupledConsensusModel.Protocol.clear
    (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing (r + 1))
      P.erase = true
  unfold DecoupledConsensusModel.Protocol.clear
  rw [show (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing
      (r + 1)).g0 = _ by simpa only [n] using hframe]
  cases hroot : storeRoot S.E S.hc
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g0) v).st (r + 1) .g0 with
  | none => rfl
  | some raw =>
      have hrawGrade : DecoupledConsensusModel.Protocol.gradeBool S.E
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) .g0) v).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (r + 1) .g0) v).st.core.F
          S.hc.η_SG (r + 1) (early S.E S.hc (r + 1) .g0)
          (late S.E S.hc (r + 1) .g0) raw = true := by
        exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hroot)).2
      obtain ⟨u, hu, hrawCarrier⟩ := relativeGrade_has_roundCarrier
        S adm.toNamedAdmissibleCore hwindow hforming hv hrawGrade
      have huHon : u ∈ rho.honest :=
        ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u r).mp hu).1
      have hrawP : Block.Preceq raw P.erase :=
        Block.preceq_trans hrawCarrier
          (Block.preceq_trans (h.actionTargetParent u huHon) hparentP)
      have hclipP : Block.Preceq
          (DecoupledConsensusModel.Protocol.clipGrade raw n.st.core.F) P.erase :=
        Block.preceq_trans
          (NamedOutageClosure.q10_clip_preceq raw n.st.core.F) hrawP
      change Block.compatible P.erase
        (DecoupledConsensusModel.Protocol.clipGrade raw n.st.core.F) = true
      simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr hclipP

/-- The action root, frozen-G0 clearance, and exact live confirmation make
every honest action carrier cover the bound proposal. -/
theorem NamedSGProposalLifecycleInputs.actionCarriersCover
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {r : Round} {s : Slot} {A : Block V} {P : NamedBlock V}
    (hwindow : RelativeCarrierWindowAt S rho r .g0)
    (hforming : GradeFormingMajority S rho (r + 1))
    (h : NamedSGProposalLifecycleInputs S rho r s A P) :
    ActionCarriersCover S rho (r + 1) P.erase := by
  have hclear := h.g0ClearAtAction adm hwindow hforming
  intro v hv
  have hlive : (actionStoreAt S rho v (r + 1)).st.core.live_confirmed =
      P.erase := h.liveConfirmedAtAction adm hcom v hv
  have heq : actionSGBlockAt S rho v (r + 1) = P.erase := by
    apply actionSGBlockAt_eq_liveConfirmed_of_batchAligned S
      (Can := P.erase) (D := P.erase)
      (A := nodeAnchor S (actionReadAt S rho v (r + 1)) (r + 1))
    · exact hlive
    · exact h.actionBatchAligned v hv
    · exact Block.preceq_self _
    · rfl
    · simpa only [nodeAnchor, nodeRead] using h.actionRootPreceq v hv
    · exact hclear v hv
  rw [heq]
  exact Block.preceq_self _






namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms NamedSGProposalLifecycleInputs.previousSlotPositive
#print axioms NamedSGProposalLifecycleInputs.openingVoteInHorizon
#print axioms NamedSGProposalLifecycleInputs.openingProposalInHorizon
#print axioms NamedSGProposalLifecycleInputs.previousVotePostGST
#print axioms NamedSGProposalLifecycleInputs.openingVotePostGST
#print axioms NamedSGProposalLifecycleInputs.proposerHealAnchor_eq
#print axioms NamedSGProposalLifecycleInputs.anchorCone
#print axioms NamedSGProposalLifecycleInputs.liveG1_preceq_proposedParent
#print axioms NamedSGProposalLifecycleInputs.actionTarget_preceq_proposedParent
#print axioms NamedSGProposalLifecycleInputs.recoveryConfirmationRead
#print axioms NamedSGOpeningFrozenVoteAt.pivot_preceq_proposalFreeHead
#print axioms NamedSGOpeningFrozenVoteAt.scoreEq
#print axioms NamedSGOpeningFrozenVoteAt.voteStoreExtends_core
#print axioms NamedSGOpeningFrozenVoteAt.voteStoreExtends
#print axioms NamedSGProposalLifecycleInputs.voteStoresExtend
#print axioms NamedSGProposalLifecycleInputs.honestVotesName
#print axioms NamedSGProposalLifecycleInputs.genuineConfirmation
#print axioms NamedSGProposalLifecycleInputs.liveConfirmedAtAction
#print axioms NamedSGProposalLifecycleInputs.g0ClearAtAction
#print axioms NamedSGProposalLifecycleInputs.actionCarriersCover
end DecoupledConsensusModel.Proofs.HealingSurface

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
