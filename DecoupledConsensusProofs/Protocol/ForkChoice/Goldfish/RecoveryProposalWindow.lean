module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.PostGSTCarrierAdmissionCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.ProposalCore
public import DecoupledConsensusProofs.Protocol.ChainState.NjGap
public import DecoupledConsensusProofs.Protocol.ChainState.ProgressQuorumCore
public import DecoupledConsensusProofs.Protocol.Handlers.Bridges
public import DecoupledConsensusInternal.Healing
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.RecoveryVoteCone
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
public import DecoupledConsensusProofs.Execution.FrontierWitnessRelay
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ReaderLocalCone
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HonestMajorityCore
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionHistory
public import DecoupledConsensusProofs.Generic.SuffixHistory
public import DecoupledConsensusProofs.Protocol.Handlers.StoreFinality
public import DecoupledConsensusProofs.Protocol.ChainState.JustificationCertificates
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Protocol.Grades.ProposalParent
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordClean
public import DecoupledConsensusProofs.Generic.EvaluationStore
public import DecoupledConsensusProofs.Objects.EmittedHeightBound
public import DecoupledConsensusProofs.Execution.RecoveryFilterSchedule
public import DecoupledConsensusProofs.Protocol.Schedule.PostHealingReuse
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradePersistence
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.RecoverySourceProgress
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.Actions
public import DecoupledConsensusProofs.Execution.RecoveryActionInterval
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionActivity
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsBridge
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsProducers
public import DecoupledConsensusProofs.Protocol.ChainState.NamedNjGap
public import DecoupledConsensusProofs.Protocol.ChainState.CheckpointHeights
public import DecoupledConsensusProofs.Execution.ProgressCanonicality
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Schedule.ConfirmationHistoryProducer
public import DecoupledConsensusInternal.Execution.Run
public import DecoupledConsensusProofs.Execution.Concentration
public import DecoupledConsensusProofs.Protocol.ChainState.DerivationGeometry
public import DecoupledConsensusProofs.Execution.RecoveryReadFGClassification
public import DecoupledConsensusProofs.Protocol.ChainState.SlashableBoundBridge
public import DecoupledConsensusProofs.Execution.RecoveryGradeProcessedRead
public import DecoupledConsensusProofs.Generic.RecoveryConcentration
public import DecoupledConsensusProofs.Protocol.ForkChoice.Head.PreparedProposalReadBridge
public import DecoupledConsensusProofs.Protocol.Grades.Q26
public import DecoupledConsensusProofs.Protocol.Handlers.FrameFloorBridge

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Recovery-height crossing at an arbitrary honest read -/







/-
/-- If a height-`H` recovery block is below the selected FG root at an honest
read, the reader's justification height has already crossed `H`.

This is the read-time form of
`recoveryHeight_lt_h_j_of_preceq_actionFGRoot`. It applies directly to an
opening proposal store. -/
theorem recoveryHeight_lt_h_j_of_preceq_fgRootAtRead
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {h_F0 H: Height} (hnf: NonfinalityRun S rho h_F0)
    (hrec: NjGap.RecoveryHeight S.cfg h_F0 H)
    {P: Block V} (hPheight: (derived_state S.E S.cfg P).h = H)
    {w: V} (hw: w ∈ rho.honest) {read: Time}
    (hhor: read ≤ rho.horizon)
    (hProot: Block.Preceq P
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w read).toHealing.toFG)):
    H < (rho.storeBeforeTime S w read).h_j:= by
  let st:= rho.storeBeforeTime S w read
  have hProot': Block.Preceq P
      (Protocol.get_fg_root st.toHealing.toFG):= by
    simpa only [st] using hProot
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node w) st:= by
    simpa only [st, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed read w)
  have hreach: ReachableStore S.E S.hc S.cfg (S.node w) st:=
    Proofs.Bridges.reachableStore_of_depReachableStore
      S.E S.hc S.cfg (S.node w) hdep
  have hFJ: Block.Preceq st.F st.J:=
    finalizedPrecedesJustifiedInvariant
      S.E S.hc S.cfg (S.node w) st hreach
  have hprov:= Proofs.Bridges.provenance_depReachable
    S.E S.hc S.cfg (S.node w) hdep
  have hHone: 1 < H:= by
    exact lt_of_le_of_lt (Nat.succ_le_succ (Nat.zero_le h_F0))
      (NjGap.lt_of_recoveryHeight hrec)
  have hHle: H ≤ st.h_j:= by
    by_cases hgate: st.h_max = st.h_j + 1
    · have hPJ: Block.Preceq P st.J:= by
        simpa only [Protocol.get_fg_root,
          Protocol.Store.toHealing, if_pos hgate] using hProot'
      obtain ⟨C, hCT, hCh, hCJ⟩:= hprov.2
      rcases Protocol.derived_justified_height S.E S.cfg C with hz | hh
      · have hJgen: st.J = Block.genesis:= by
          rw [← hCJ]
          exact AlignedRoundLemmas.derived_state_J_of_h_j_zero
            S.E S.cfg C hz
        have hPgen: P = Block.genesis:= by
          apply Block.preceq_antisymm
          · simpa only [hJgen] using hPJ
          · exact Protocol.preceq_genesis P
        subst P
        change (1: Height) = H at hPheight
        exact False.elim ((Nat.ne_of_gt hHone) hPheight.symm)
      · calc
          H = (derived_state S.E S.cfg P).h:= hPheight.symm
          _ ≤ (derived_state S.E S.cfg st.J).h:=
            Protocol.derived_h_mono S.E S.cfg hPJ
          _ = st.h_j:= by
            rw [← hCJ, ← hCh]
            exact hh
    · have hPF: Block.Preceq P st.F:= by
        simpa only [Protocol.get_fg_root,
          Protocol.Store.toHealing, if_neg hgate] using hProot'
      rcases StoreFinality.finalized_height_le_justification
          S.E S.cfg st hFJ hprov.2 with hFgen | hFheight
      · have hPgen: P = Block.genesis:= by
          apply Block.preceq_antisymm
          · simpa only [hFgen] using hPF
          · exact Protocol.preceq_genesis P
        subst P
        change (1: Height) = H at hPheight
        exact False.elim ((Nat.ne_of_gt hHone) hPheight.symm)
      · calc
          H = (derived_state S.E S.cfg P).h:= hPheight.symm
          _ ≤ (derived_state S.E S.cfg st.F).h:=
            Protocol.derived_h_mono S.E S.cfg hPF
          _ ≤ st.h_j:= hFheight
  have hpredHor: read - 1 ≤ rho.horizon:=
    (sub_le_self read (by norm_num: (0: Time) ≤ 1)).trans hhor
  have hneAt:= NjGap.store_h_j_ne_recovery_height
    S adm hnf hrec hw hpredHor
  have hne: st.h_j ≠ H:= by
    simpa only [st,
      storeBeforeTime_eq_storeAt_sub_one_recovery] using hneAt
  have hlt: H < st.h_j:= Nat.lt_of_le_of_ne hHle (Ne.symm hne)
  simpa only [st] using hlt
-/

/-! ## The preceding action grade inside an opening proposal store -/

/-- Every exact preceding action vote is present and stamped before
`Gamma[-1]` in the next opening proposal store. -/
theorem actionSGVote_mem_stamp_nextOpeningProposer
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round}
    (hpost : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hprop : S.E.proposer (S.hc.opening_slot (r + 1)) ∈ rho.honest)
    {v : V} (hv : v ∈ rho.honest) :
    let s := S.hc.opening_slot (r + 1)
    actionSGVoteAt S rho v r ∈
        (Protocol.proposerDutyStore S rho s).toHealing.sg_votes r ∧
    occurrenceBefore
        ((Protocol.proposerDutyStore S rho s).timestamp_sg_vote
          (actionSGVoteAt S rho v r))
        (S.hc.Γ_neg1 S.E.Δ (r + 1)) = true := by
  let s := S.hc.opening_slot (r + 1)
  let read := Protocol.proposal_time S.E s
  have hdeadline : S.a r + S.E.Δ ≤ rho.horizon :=
    (action_add_delta_le_next_Γ_neg1 S r).trans hcut
  obtain ⟨j, e, hj, heDelta, hrow⟩ :=
    actionAttestationAt_rows_before_delta S adm hv hprop r hpost hdeadline
  have haRound : (actionAttestationAt S rho v r).round = r :=
    (actionAttestationAt_shape S rho v r).2.1
  have ha' : actionAttestationAt S rho v r ∈
      (rho.stateBefore S (j + 1) (S.E.proposer s)).st.sg_rows
        (actionAttestationAt S rho v r).round := by
    rw [haRound]
    exact hrow
  have hu : actionSGVoteAt S rho v r ∈
      (rho.stateBefore S (j + 1) (S.E.proposer s)).st.toHealing.sg_votes r := by
    have hpool := NamedAdmission.pool_view_mem
      (rho.stateBefore S (j + 1) (S.E.proposer s)).st
      (Proofs.NamedRuntime.stateBefore_invariants S rho (j + 1)
        (S.E.proposer s)).1.1.1.2.2.2.1 _ ha'
    rw [haRound] at hpool
    have himg := Finset.mem_image_of_mem Protocol.sgVote hpool
    rw [sgVote_actionAttestationAt] at himg
    exact himg
  have heCut : e.time < S.hc.Γ_neg1 S.E.Δ (r + 1) :=
    lt_of_lt_of_le heDelta (action_add_delta_le_next_Γ_neg1 S r)
  have hut := GradeDeliveryRun.timestamp_sg_vote_before_of_mem_post_event
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hj ha' heCut
  have hcutRead : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ read := by
    rw [show read = S.hc.Γ_0 S.E.Δ (r + 1) by
      exact (Protocol.Γ_0_eq_proposal_time S.hc S.E (r + 1)).symm]
    exact le_of_lt (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0
      S.hc S.E.Δ_pos (r + 1))
  have hpostRead := GradeDeliveryRun.projected_vote_mem_stamp_at_read
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hj heCut hcutRead hu
      (by simpa only [sgVote_actionAttestationAt] using hut)
  simpa only [s, read, Protocol.proposerDutyStore,
    Proofs.Optimistic.tickStore] using hpostRead


/-- Every honest-validator slice of the next opening proposal's grade batch
has at most one projected vote. -/
theorem nextOpeningProposer_roundBatch_card_le_one
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {v : V} (hv : v ∈ rho.honest) :
    let s := S.hc.opening_slot (r + 1)
    (Protocol.sg_votes_by
      (Protocol.round_batch
        (Protocol.proposerDutyStore S rho s).toHealing.gradeView (r + 1))
      v).card ≤ 1 := by
  let s := S.hc.opening_slot (r + 1)
  have h := Protocol.roundBatch_card_le_one_stateBeforeTime
    S adm (t := Protocol.proposal_time S.E s) (w := S.E.proposer s)
      (r := r + 1)
      (v := v) hv
  simpa only [s, Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
    Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using h

/-! An exact preceding action carrier is present and stamped before the next
`Gamma[-1]` in the next opening proposal store, provided the common block is
active there. -/
theorem actionSGBlockAt_visible_nextOpeningProposer_of_cleanActionRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {Q : Block V} (hclean : CleanActionReadFor S rho r Q)
    (hprop : S.E.proposer (S.hc.opening_slot (r + 1)) ∈ rho.honest)
    {v : V} (hv : v ∈ rho.honest)
    (hactive : Q ∈ Protocol.get_filtered_block_tree
      (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot (r + 1))).toHealing.toFG) :
    let s := S.hc.opening_slot (r + 1)
    let C := actionSGBlockAt S rho v r
    C ∈ (Protocol.proposerDutyStore S rho s).T ∧
      stampedBefore
        (Protocol.proposerDutyStore S rho s).timestamp_block
        (S.hc.Γ_neg1 S.E.Δ (r + 1)) C = true := by
  let s := S.hc.opening_slot (r + 1)
  let C := actionSGBlockAt S rho v r
  let read := Protocol.proposal_time S.E s
  let duty := Protocol.proposerDutyStore S rho s
  have hQC : Block.Preceq Q C := by
    simpa only [C] using
      cleanActionRead_preceq_actionSGBlockAt S adm hclean hprop hv
  have hCsource : C ∈ (rho.storeBeforeTime S v (S.a r)).T := by
    simpa only [C] using actionSGBlockAt_mem_storeBeforeTime S rho v r
  have hcutRead : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ read := by
    rw [show read = S.hc.Γ_0 S.E.Δ (r + 1) by
      exact (Protocol.Γ_0_eq_proposal_time S.hc S.E (r + 1)).symm]
    exact le_of_lt (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0
      S.hc S.E.Δ_pos (r + 1))
  have hdeadlineRead : S.a r + S.E.Δ ≤ read :=
    (action_add_delta_le_next_Γ_neg1 S r).trans hcutRead
  have hactivePre : Q ∈ Protocol.get_filtered_block_tree
      (rho.storeBeforeTime S (S.E.proposer s) read).toHealing.toFG := by
    simpa only [duty, Protocol.proposerDutyStore,
      Proofs.Optimistic.tickStore, read] using hactive
  rcases block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTime
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v (S.a r) hCsource with
    hgen | ⟨D, i, t, hDerase, hacc, ht⟩
  · have hgenvis := Protocol.genesis_mem_and_stamp_storeBeforeTime
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.E.proposer s) read
        (S.hc.Γ_neg1 S.E.Δ (r + 1))
    simpa only [C, hgen, duty, Protocol.proposerDutyStore,
      Proofs.Optimistic.tickStore, read] using hgenvis
  · have hDpos : 0 < D.slot := by
      rw [← Proofs.NamedWire.erase_slot]
      exact Nat.zero_lt_of_lt (Protocol.parent_slot_lt_of_acceptsAt_block S hacc)
    have hCpos : 0 < C.slot := by
      rw [← hDerase, Proofs.NamedWire.erase_slot]
      exact hDpos
    have hFhist : Protocol.BlockFinalizedBelowAtDeliveriesBefore
        S rho (S.E.proposer s) D (S.a r + S.E.Δ) :=
      finalizedBelowAtDeliveriesBefore_of_filteredAtLaterRead
        S adm hdeadlineRead hactivePre (by rw [hDerase]; exact hQC)
    have hdeadlineHor : S.a r + S.E.Δ ≤ rho.horizon :=
      (action_add_delta_le_next_Γ_neg1 S r).trans
        hclean.cutoff_in_horizon
    have hadmitD := Protocol.block_admittedBefore_of_accepted_after_cutoff
      S adm hv hprop hDpos hacc ht hclean.post_gst rfl hdeadlineHor hFhist
    have hadmit : Protocol.AdmittedBefore S rho (S.E.proposer s) C
        (S.a r + S.E.Δ) := by
      simpa only [hDerase] using hadmitD
    have hvisible := Protocol.admittedBefore_mem_and_stamp_at
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hadmit hdeadlineRead
    refine ⟨?_, ?_⟩
    · simpa only [duty, Protocol.proposerDutyStore,
        Proofs.Optimistic.tickStore, read] using hvisible.1
    · have hstamp := occurrenceBefore_mono
        (action_add_delta_le_next_Γ_neg1 S r) hvisible.2
      simpa only [stampedBefore_eq_occurrenceBefore, duty,
        Protocol.proposerDutyStore, Proofs.Optimistic.tickStore, read] using hstamp

/-
/-- An exact preceding action carrier is present and stamped before
`Gamma[-1]` in the next opening proposal store, provided the common block is
active there. -/
theorem actionSGBlockAt_visible_nextOpeningProposer_of_cleanActionRead
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {r: Round} {Q: Block V} (hclean: CleanActionReadFor S rho r Q)
    (hprop: S.E.proposer (S.hc.opening_slot (r + 1)) ∈ rho.honest)
    {v: V} (hv: v ∈ rho.honest)
    (hactive: Q ∈ Protocol.get_filtered_block_tree
      (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot (r + 1))).toHealing.toFG):
    let s:= S.hc.opening_slot (r + 1)
    let C:= actionSGBlockAt S rho v r
    C ∈ (Protocol.proposerDutyStore S rho s).T ∧
      stampedBefore
        (Protocol.proposerDutyStore S rho s).timestamp_block
        (S.hc.Γ_neg1 S.E.Δ (r + 1)) C = true:= by
  let s:= S.hc.opening_slot (r + 1)
  let C:= actionSGBlockAt S rho v r
  let read:= Protocol.proposal_time S.E s
  let duty:= Protocol.proposerDutyStore S rho s
  have hQC: Block.Preceq Q C:= by
    simpa only [C] using
      cleanActionRead_preceq_actionSGBlockAt S adm hclean hprop hv
  have hCsource: C ∈ (rho.storeBeforeTime S v (S.a r)).T:= by
    simpa only [C] using actionSGBlockAt_mem_storeBeforeTime S adm v r
  have hcutRead: S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ read:= by
    rw [show read = S.hc.Γ_0 S.E.Δ (r + 1) by
      exact (Protocol.Γ_0_eq_proposal_time S.hc S.E (r + 1)).symm]
    exact le_of_lt (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0
      S.hc S.E.Δ_pos (r + 1))
  have hdeadlineRead: S.a r + S.E.Δ ≤ read:=
    (action_add_delta_le_next_Γ_neg1 S r).trans hcutRead
  have hactivePre: Q ∈ Protocol.get_filtered_block_tree
      (rho.storeBeforeTime S (S.E.proposer s) read).toHealing.toFG:= by
    simpa only [duty, Protocol.proposerDutyStore,
      Proofs.Optimistic.tickStore, read] using hactive
  rcases block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTime
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v (S.a r) hCsource with
    hgen | ⟨i, t, hacc, ht⟩
  · have hgenvis:= Protocol.genesis_mem_and_stamp_storeBeforeTime
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.E.proposer s) read
        (S.hc.Γ_neg1 S.E.Δ (r + 1))
    simpa only [C, hgen, duty, Protocol.proposerDutyStore,
      Proofs.Optimistic.tickStore, read] using hgenvis
  · have hCpos: 0 < C.slot:=
      Nat.zero_lt_of_lt (Protocol.parent_slot_lt_of_acceptsAt_block S hacc)
    have hFhist: Protocol.BlockFinalizedBelowAtDeliveriesBefore
        S rho (S.E.proposer s) C (S.a r + S.E.Δ):=
      finalizedBelowAtDeliveriesBefore_of_filteredAtLaterRead
        S adm hdeadlineRead hactivePre hQC
    have hdeadlineHor: S.a r + S.E.Δ ≤ rho.horizon:=
      (action_add_delta_le_next_Γ_neg1 S r).trans
        hclean.cutoff_in_horizon
    have hadmit: Protocol.AdmittedBefore S rho (S.E.proposer s) C
        (S.a r + S.E.Δ):=
      Protocol.block_admittedBefore_of_accepted_after_cutoff
        S adm hv hprop hCpos hacc ht hclean.post_gst rfl hdeadlineHor hFhist
    have hvisible:= Protocol.admittedBefore_mem_and_stamp_at
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hadmit hdeadlineRead
    refine ⟨?_, ?_⟩
    · simpa only [duty, Protocol.proposerDutyStore,
        Proofs.Optimistic.tickStore, read] using hvisible.1
    · have hstamp:= occurrenceBefore_mono
        (action_add_delta_le_next_Γ_neg1 S r) hvisible.2
      simpa only [stampedBefore_eq_occurrenceBefore, duty,
        Protocol.proposerDutyStore, Proofs.Optimistic.tickStore, read] using hstamp
-/

/-- The same carrier is the unique block behind its root in the next opening
proposal tree. -/
theorem actionSGBlockAt_find_nextOpeningProposer_of_cleanActionRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {Q : Block V} (hclean : CleanActionReadFor S rho r Q)
    (hprop : S.E.proposer (S.hc.opening_slot (r + 1)) ∈ rho.honest)
    {v : V} (hv : v ∈ rho.honest)
    (hactive : Q ∈ Protocol.get_filtered_block_tree
      (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot (r + 1))).toHealing.toFG) :
    let s := S.hc.opening_slot (r + 1)
    Block.find? (Protocol.proposerDutyStore S rho s).T
      (actionSGBlockAt S rho v r).root =
        some (actionSGBlockAt S rho v r) := by
  let s := S.hc.opening_slot (r + 1)
  let C := actionSGBlockAt S rho v r
  have hvisible :=
    actionSGBlockAt_visible_nextOpeningProposer_of_cleanActionRead
      S adm hclean hprop hv hactive
  apply Proofs.Optimistic.find?_eq_some_of_unique
  · simpa only [C, s] using hvisible.1
  · intro X hX hroot
    let read := Protocol.proposal_time S.E s
    have hXmem : X ∈ (rho.storeBeforeTime S (S.E.proposer s) read).T := by
      simpa only [Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
        Run.storeBeforeTime, s, read] using hX
    have hCmem : C ∈ (rho.storeBeforeTime S (S.E.proposer s) read).T := by
      simpa only [Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
        Run.storeBeforeTime, C, s, read] using hvisible.1
    obtain ⟨Xn, hXnErase, hXrun⟩ :=
      Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hprop read hXmem
    obtain ⟨Cn, hCnErase, hCrun⟩ :=
      Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hprop read hCmem
    have hrootN : Xn.root = Cn.root := by
      rw [← Proofs.NamedWire.erase_root Xn, ← Proofs.NamedWire.erase_root Cn,
        hXnErase, hCnErase, hroot]
    have hXC := adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      Xn Cn hXrun hCrun Xn Cn
      (Or.inl (Proofs.NamedAncestry.named_self Xn))
      (Or.inr (Proofs.NamedAncestry.named_self Cn)) hrootN
    calc
      X = Xn.erase := hXnErase.symm
      _ = Cn.erase := congrArg NamedBlock.erase hXC
      _ = C := hCnErase


/-- The clean preceding action batch forms an active G2 in the next opening
proposal store. -/
theorem G2_nextOpeningProposer_of_cleanActionRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hmajority : HonestWeightMajority S rho.honest)
    {r : Round} {Q : Block V} (hclean : CleanActionReadFor S rho r Q)
    (hprop : S.E.proposer (S.hc.opening_slot (r + 1)) ∈ rho.honest)
    (hactive : Q ∈ Protocol.get_filtered_block_tree
      (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot (r + 1))).toHealing.toFG) :
    let s := S.hc.opening_slot (r + 1)
    Protocol.G2 S.E
      (Protocol.proposerDutyStore S rho s).toHealing.gradeView
      S.hc (r + 1) Q = true := by
  let s := S.hc.opening_slot (r + 1)
  let duty := Protocol.proposerDutyStore S rho s
  let gv := duty.toHealing.gradeView
  have hsupport : ∀ v ∈ rho.honest,
      occurrenceBefore (Protocol.summary gv (r + 1) v).t_v
          (S.hc.Γ_neg1 S.E.Δ (r + 1)) = true ∧
        Protocol.head_covers gv.T Q
          (Protocol.summary gv (r + 1) v).C_v = true ∧
        occurrenceAtLeast (Protocol.summary gv (r + 1) v).e_v
          (S.hc.Γ_2 S.E.Δ (r + 1)) = true := by
    intro v hv
    let u := actionSGVoteAt S rho v r
    let C := actionSGBlockAt S rho v r
    let batch := Protocol.sg_votes_by
      (Protocol.round_batch gv (r + 1)) v
    let tau := Protocol.sg_resolution_time gv.T gv.timestamp_block
      gv.timestamp_sg_vote
    let headed := batch.filter (fun x =>
      x.confirmed.isSome ∧ Protocol.sg_resolved gv.T x = true)
    have huRead := actionSGVote_mem_stamp_nextOpeningProposer
      S adm hclean.post_gst hclean.cutoff_in_horizon hprop hv
    have huPool : u ∈ duty.toHealing.sg_votes r := by
      simpa only [u, duty, s] using huRead.1
    have huBatch : u ∈ batch := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · simpa only [batch, gv, Protocol.round_batch,
          if_neg (Nat.succ_ne_zero r), Nat.add_sub_cancel] using huPool
      · exact (actionSGVoteAt_shape S rho v r).1
    have hfind := actionSGBlockAt_find_nextOpeningProposer_of_cleanActionRead
      S adm hclean hprop hv hactive
    have hfindAct : Block.find? gv.T
        (actionSGBlockAt S rho v r).root =
          some (actionSGBlockAt S rho v r) := by
      simpa only [gv, duty, s] using hfind
    have huHeaded : u ∈ headed := by
      apply Finset.mem_filter.mpr
      refine ⟨huBatch, ?_⟩
      simp only [u, actionSGVoteAt, Option.isSome_some, true_and,
        Protocol.sg_resolved, hfindAct, Option.isSome_some]
    have hbatchCard : batch.card ≤ 1 := by
      simpa only [batch, gv, duty, s] using
        (nextOpeningProposer_roundBatch_card_le_one
          S adm (r := r) (v := v) hv)
    have hheadedCard : headed.card ≤ 1 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans hbatchCard
    have hfirst : Protocol.batch_first? tau headed = some u :=
      Proofs.Optimistic.batch_first?_of_card_le_one huHeaded hheadedCard
    have hsummaryC : (Protocol.summary gv (r + 1) v).C_v = u.confirmed := by
      change (Protocol.batch_first? tau headed).bind
        Protocol.SGVote.confirmed = u.confirmed
      rw [hfirst]
      rfl
    have hsummaryT : (Protocol.summary gv (r + 1) v).t_v = tau u := by
      change (Protocol.batch_first? tau headed).elim none tau = tau u
      rw [hfirst]
      simp
    have hblockVisible :=
      actionSGBlockAt_visible_nextOpeningProposer_of_cleanActionRead
        S adm hclean hprop hv hactive
    have hblockStamp : occurrenceBefore (gv.timestamp_block C)
        (S.hc.Γ_neg1 S.E.Δ (r + 1)) = true := by
      simpa only [gv, duty, s, stampedBefore_eq_occurrenceBefore, C] using
        hblockVisible.2
    have hvoteStamp : occurrenceBefore (gv.timestamp_sg_vote u)
        (S.hc.Γ_neg1 S.E.Δ (r + 1)) = true := by
      simpa only [gv, duty, s, u] using huRead.2
    have hres : occurrenceBefore (tau u)
        (S.hc.Γ_neg1 S.E.Δ (r + 1)) = true := by
      simp only [tau, u, actionSGVoteAt,
        Protocol.sg_resolution_time, hfindAct]
      exact occurrenceBefore_max hvoteStamp hblockStamp
    have hQC : Block.Preceq Q C := by
      simpa only [C] using
        cleanActionRead_preceq_actionSGBlockAt S adm hclean hprop hv
    have hcov : Protocol.head_covers gv.T Q u.confirmed = true := by
      simp only [u, actionSGVoteAt, Protocol.head_covers, hfindAct]
      exact hQC
    have heNone : (Protocol.summary gv (r + 1) v).e_v = none := by
      rw [Proofs.Optimistic.summary_e_v_eq]
      exact Proofs.Optimistic.equivocation_instant_eq_none hbatchCard
    refine ⟨?_, ?_, ?_⟩
    · rwa [hsummaryT]
    · rwa [hsummaryC]
    · rw [heNone]
      rfl
  simp only [Protocol.G2, decide_eq_true_eq]
  unfold Protocol.direct_support
  refine le_trans (honestWeight_ge_m hmajority)
    (S.E.electorate.weightOf_mono ?_)
  intro v hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hsupport v hv⟩



/-
/-- Proposal activity plus the persistent preceding action grade forces the
exact Section 7 opening proposal parent above the protected block. -/
theorem protected_preceq_nextOpeningProposedParent_of_cleanActionRead
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hmajority: HonestWeightMajority S rho.honest)
    {r: Round} {P: Block V} (hclean: CleanActionReadFor S rho r P)
    (hprop: S.E.proposer (S.hc.opening_slot (r + 1)) ∈ rho.honest)
    (hactive: P ∈ Protocol.get_filtered_block_tree
      (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot (r + 1))).toHealing.toFG):
    Block.Preceq P
      (Internal.proposedBlock S rho
        (S.hc.opening_slot (r + 1))).parent:= by
  let s:= S.hc.opening_slot (r + 1)
  let duty:= Protocol.proposerDutyStore S rho s
  have hdutyRound: S.hc.round_of duty.s = r + 1:= by
    simp only [duty, Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
      Proofs.Optimistic.slotOf_proposal_time, s,
      Protocol.HealConfig.round_of, Protocol.HealConfig.opening_slot]
    have hR: 0 < S.hc.R:= lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two
    simpa only [Nat.mul_comm] using Nat.mul_div_cancel_left (r + 1) hR
  have hG2:= G2_nextOpeningProposer_of_cleanActionRead
    S adm hmajority hclean hprop hactive
  have hhead:= activeG2_preceq_getHead S.E S.hc duty hdutyRound hactive
    (by simpa only [duty, s] using hG2)
    (Protocol.proposer_view duty.toHealing.toFG.toSG.toGoldfishStore duty.s).toFinset
    (Protocol.proposer_support_view duty.toHealing.toFG.toSG.toGoldfishStore duty.s).toFinset
    (duty.s - 1)
  rw [parent_eq_of_parent?
    (Protocol.proposedBlock_parent S rho s)]
  simpa only [Protocol.proposedParent, duty, s] using hhead
-/



private theorem cacheAtRound_align_self_opening_local
    (c : DecoupledConsensusModel.Protocol.Cache V) (r : Round) :
    DecoupledConsensusModel.Protocol.cacheAtRound (DecoupledConsensusModel.Protocol.alignRound c r) r =
      DecoupledConsensusModel.Protocol.cacheAtRound c r := by
  by_cases h1 : r = c.round
  · rw [show DecoupledConsensusModel.Protocol.alignRound c r = c by
      unfold DecoupledConsensusModel.Protocol.alignRound
      rw [if_pos h1]]
  · by_cases h2 : r = c.round + 1
    · rw [show DecoupledConsensusModel.Protocol.alignRound c r =
        ⟨r, c.next, DecoupledConsensusModel.Protocol.pendingFrame⟩ by
        unfold DecoupledConsensusModel.Protocol.alignRound
        rw [if_neg h1, if_pos h2]]
      subst h2
      simp [DecoupledConsensusModel.Protocol.cacheAtRound]
    · rw [show DecoupledConsensusModel.Protocol.alignRound c r =
        ⟨r, DecoupledConsensusModel.Protocol.pendingFrame, DecoupledConsensusModel.Protocol.pendingFrame⟩ by
        unfold DecoupledConsensusModel.Protocol.alignRound
        rw [if_neg h1, if_neg h2]]
      simp [DecoupledConsensusModel.Protocol.cacheAtRound, h1, h2]

private theorem clip_grade_compatible_opening_local (g F : Block V) :
    Block.compatible (DecoupledConsensusModel.Protocol.clipGrade g F) F = true := by
  induction g with
  | genesis => simp [DecoupledConsensusModel.Protocol.clipGrade,
      Block.compatible, Protocol.preceq_genesis]
  | node p s root gv gsv ats v ih =>
      simp only [DecoupledConsensusModel.Protocol.clipGrade]
      split
      · assumption
      · exact ih

private theorem clip_grade_keeps_opening_local (g F : Block V)
    (h : Block.compatible g F = true) :
    DecoupledConsensusModel.Protocol.clipGrade g F = g := by
  cases g with
  | genesis => rfl
  | node p s root gv gsv ats v =>
      simp only [DecoupledConsensusModel.Protocol.clipGrade, h, ↓reduceIte]

private theorem clip_grade_idempotent_opening_local (g F : Block V) :
    DecoupledConsensusModel.Protocol.clipGrade
        (DecoupledConsensusModel.Protocol.clipGrade g F) F =
      DecoupledConsensusModel.Protocol.clipGrade g F := by
  exact clip_grade_keeps_opening_local _ _
    (clip_grade_compatible_opening_local g F)

private theorem clip_result_idempotent_opening_local
    (F : Block V) (x : Option (Option (Block V))) :
    DecoupledConsensusModel.Protocol.clipResult F (DecoupledConsensusModel.Protocol.clipResult F x) =
      DecoupledConsensusModel.Protocol.clipResult F x := by
  cases x with
  | none => rfl
  | some y =>
      cases y with
      | none => rfl
      | some B =>
          simp only [DecoupledConsensusModel.Protocol.clipResult, Option.map_some]
          rw [clip_grade_idempotent_opening_local]

private theorem clip_frame_idempotent_opening_local
    (F : Block V) (f : DecoupledConsensusModel.Protocol.Frame V) :
    DecoupledConsensusModel.Protocol.clipFrame F (DecoupledConsensusModel.Protocol.clipFrame F f) =
      DecoupledConsensusModel.Protocol.clipFrame F f := by
  cases f
  simp only [DecoupledConsensusModel.Protocol.clipFrame]
  congr 1 <;> exact clip_result_idempotent_opening_local F _

private theorem q10_g1_of_g2_freeze_local
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (v : V) (hv : v ∈ rho.honest) (r : Round) (hr : 0 < r) {g2 : Block V}
    (hg2raw : freezeRoot S.E
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.F
      S.hc.η_SG r (early S.E S.hc r .g2) (late S.E S.hc r .g2) = some g2)
    (hFB : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) v).st.core.F g2) :
    ∃ g1 : Block V, freezeRoot S.E
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) v).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) v).st.core.F
        S.hc.η_SG r (early S.E S.hc r .g1) (late S.E S.hc r .g1) = some g1 ∧
      Block.Preceq g2 g1 := by
  have hmemfilter := Proofs.Engine.deepest?_mem hg2raw
  have hmem2 := (Finset.mem_filter.mp hmemfilter).1
  have hgrade2 := (Finset.mem_filter.mp hmemfilter).2
  have hgrade1 := NamedOutageClosure.q10_grade_cross S rho core v hv r hr g2
    hFB hgrade2
  have hmem1 := NamedOutageClosure.q10_tree_fwd S rho core v
    (NamedOutageClosure.q10_domain_g2_lt_domain_g1 S r).le hmem2
  exact NamedOutageClosure.q10_freeze_of_graded S.E
    (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) v).st.core.toHealing.gradeView
    (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) v).st.core.F
    S.hc.η_SG r (NamedOutageClosure.q10_early_le_late S r .g1) hmem1 hgrade1

private theorem frameG1_preceq_of_freezeRoot_prepared_opening
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (w : V) (hw : w ∈ rho.honest) (r : Round) (hr : 0 < r) (t : Time)
    (hround : S.hc.round_of (S.E.slotOf t) = r)
    (hopen : domain S.E S.hc r .g1 = t) {P raw : Block V}
    (hPtree : P ∈ Protocol.get_filtered_block_tree
      (NamedActionReads.confirmationReadAt S rho w t).st.core.toHealing.toFG)
    (hfreeze : freezeRoot S.E
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.F
      S.hc.η_SG r (early S.E S.hc r .g2) (late S.E S.hc r .g2) = some raw)
    (hPraw : Block.Preceq P raw) :
    ∃ root, (DecoupledConsensusModel.Protocol.readFrame
      (NamedActionReads.confirmationReadAt S rho w t).cache
      (NamedActionReads.confirmationReadAt S rho w t).st.core.toHealing r).g1 =
        some (some root) ∧ Block.Preceq P root := by
  let before := NamedRun.stateBeforeTime S rho t w
  let read := NamedActionReads.confirmationReadFrom S before t
  have hround' : S.hc.round_of (S.E.slotOf t) = r := hround
  have hnotg2 : t ≠ domain S.E S.hc r .g2 := by
    intro heq
    exact (ne_of_gt (NamedOutageClosure.q10_domain_g2_lt_domain_g1 S r))
      (hopen.trans heq)
  have hnotg0 : t ≠ domain S.E S.hc r .g0 := by
    intro heq
    have h10 : domain S.E S.hc r .g1 < domain S.E S.hc r .g0 := by
      unfold domain
      simp only [Phase.domainOffset, zero_mul, one_mul, add_zero]
      exact lt_add_of_pos_right _ S.E.Δ_pos
    exact (ne_of_gt h10) (hopen.trans heq).symm
  have hrawNone :
      DecoupledConsensusModel.Protocol.phaseResult
        (DecoupledConsensusModel.Protocol.cacheAtRound before.cache r) .g1 = none := by
    by_contra hnone
    obtain ⟨root, hroot⟩ := Option.ne_none_iff_exists'.mp hnone
    rcases NamedCacheProvenance.completed_phase_before_read S rho core.sorted
      core.nodup t w r .g1 root hroot with hzero | hdone
    · exact (Nat.ne_of_gt hr) hzero.1
    · obtain ⟨j, u, hj, hu, hdom, hvalue⟩ := hdone
      have hlt : t < t := by
        calc
          t = domain S.E S.hc r .g1 := hopen.symm
          _ = u := hdom.symm
          _ < t := hu
      exact (lt_irrefl t) hlt
  let aligned := DecoupledConsensusModel.Protocol.alignRound before.cache r
  have halign : DecoupledConsensusModel.Protocol.cacheAtRound aligned r =
      DecoupledConsensusModel.Protocol.cacheAtRound before.cache r := by
    exact cacheAtRound_align_self_opening_local before.cache r
  have halignedNone :
      DecoupledConsensusModel.Protocol.phaseResult
        (DecoupledConsensusModel.Protocol.cacheAtRound aligned r) .g1 = none := by
    rw [halign]
    exact hrawNone
  have hcomplete :
      DecoupledConsensusModel.Protocol.phaseResult
          (DecoupledConsensusModel.Protocol.completeFrame S.E S.hc before.st.core.toHealing
            r t (DecoupledConsensusModel.Protocol.cacheAtRound aligned r)) .g1 =
        some (PhaseGrades.storeRoot S.E S.hc
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc r .g1) w).st r .g1) := by
    have hG1 : (DecoupledConsensusModel.Protocol.cacheAtRound aligned r).g1 = none :=
      halignedNone
    cases hG2 : (DecoupledConsensusModel.Protocol.cacheAtRound aligned r).g2 <;>
      cases hG0 : (DecoupledConsensusModel.Protocol.cacheAtRound aligned r).g0 <;>
        simp [DecoupledConsensusModel.Protocol.completeFrame, DecoupledConsensusModel.Protocol.completeOne,
          DecoupledConsensusModel.Protocol.putPhase, DecoupledConsensusModel.Protocol.phaseResult, hG2,
          hG0, hG1, hnotg2, hnotg0, before, hopen,
          PhaseGrades.storeRoot, PhaseGrades.phaseRoot,
          Protocol.Store.toHealing]
  have hframe :
      (DecoupledConsensusModel.Protocol.readFrame read.cache read.st.core.toHealing r).g1 =
        some ((PhaseGrades.storeRoot S.E S.hc
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) w).st r .g1).map
          (fun X => DecoupledConsensusModel.Protocol.clipGrade X read.st.core.F)) := by
    dsimp only [read, NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache]
    have halignedRound : aligned.round = r := by
      dsimp only [aligned]
      unfold DecoupledConsensusModel.Protocol.alignRound
      split_ifs with h
      · exact h.symm
      · rfl
      · rfl
    have hcacheTick :
        DecoupledConsensusModel.Protocol.cacheAtRound
            (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc before.st.core.toHealing
              t before.cache) r =
          DecoupledConsensusModel.Protocol.clipFrame before.st.core.F
            (DecoupledConsensusModel.Protocol.completeFrame S.E S.hc
              before.st.core.toHealing r t aligned.current) := by
      unfold DecoupledConsensusModel.Protocol.onPhaseTick
      rw [hround']
      simp [aligned, DecoupledConsensusModel.Protocol.cacheAtRound, halignedRound,
        DecoupledConsensusModel.Protocol.clipCache, Protocol.Store.toHealing]
    change (DecoupledConsensusModel.Protocol.readFrame
      (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc before.st.core.toHealing
        t before.cache)
      before.st.core.toHealing r).g1 = _
    unfold DecoupledConsensusModel.Protocol.readFrame
    change (DecoupledConsensusModel.Protocol.clipFrame before.st.core.F
      (DecoupledConsensusModel.Protocol.cacheAtRound
        (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc before.st.core.toHealing
          t before.cache) r)).g1 = _
    rw [hcacheTick, clip_frame_idempotent_opening_local]
    have hcache : DecoupledConsensusModel.Protocol.cacheAtRound aligned r = aligned.current := by
      simp [DecoupledConsensusModel.Protocol.cacheAtRound, halignedRound]
    have hcomplete' := hcomplete
    rw [hcache] at hcomplete'
    have hcomplete'' :
        (DecoupledConsensusModel.Protocol.completeFrame S.E S.hc before.st.core.toHealing
          r t aligned.current).g1 =
        some (PhaseGrades.storeRoot S.E S.hc
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) w).st r .g1) := by
      simpa only [DecoupledConsensusModel.Protocol.phaseResult] using hcomplete'
    simp only [DecoupledConsensusModel.Protocol.clipFrame, DecoupledConsensusModel.Protocol.clipResult]
    rw [hcomplete'']
    rfl
  have hFP : Block.Preceq read.st.core.F P := by
    simpa only [read, before, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using NamedOutageClosure.q10_filtered_F hPtree
  have hFB : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) w).st.core.F raw := by
    rw [hopen]
    exact Block.preceq_trans hFP hPraw
  obtain ⟨raw1, hfreeze1, hPraw1⟩ := q10_g1_of_g2_freeze_local
    S rho core w hw r hr hfreeze hFB
  have hstore : PhaseGrades.storeRoot S.E S.hc
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) w).st r .g1 =
      some raw1 := by
    simpa only [PhaseGrades.storeRoot, PhaseGrades.phaseRoot] using hfreeze1
  have hPclip : Block.Preceq P
      (DecoupledConsensusModel.Protocol.clipGrade raw1 read.st.core.F) := by
    exact (NamedOutageClosure.q10_retained_prefix raw1 read.st.core.F P (by
      simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr hFP)).mpr (Block.preceq_trans hPraw hPraw1)
  refine ⟨DecoupledConsensusModel.Protocol.clipGrade raw1 read.st.core.F, ?_, hPclip⟩
  simpa only [read, before, hstore, Option.map_some] using hframe

/-- A persistent clean action grade bounds the prepared parent of the next
opening proposal. -/
theorem protected_preceq_nextOpeningProposedParent_of_cleanActionRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hmajority : HonestWeightMajority S rho.honest)
    {r : Round} {P : Block V} (hclean : CleanActionReadFor S rho r P)
    (hprop : S.E.proposer (S.hc.opening_slot (r + 1)) ∈ rho.honest)
    (hactive : P ∈ Protocol.get_filtered_block_tree
      (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot (r + 1))).toHealing.toFG)
    {B : NamedBlock V}
    (hB : proposedBlockAt S rho (S.hc.opening_slot (r + 1)) = some B) :
    Block.Preceq P B.erase.parent := by
  let s := S.hc.opening_slot (r + 1)
  let t := Protocol.proposal_time S.E s
  let w := S.E.proposer s
  let duty := Protocol.proposerDutyStore S rho s
  have hdutyRound : S.hc.round_of duty.s = r + 1 := by
    simp only [duty, Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
      Proofs.Optimistic.slotOf_proposal_time, s,
      Protocol.HealConfig.round_of, Protocol.HealConfig.opening_slot]
    have hR : 0 < S.hc.R := lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two
    simpa only [Nat.mul_comm] using Nat.mul_div_cancel_left (r + 1) hR
  have hforms : NamedGradeFormsAt S rho (r + 1) P :=
    namedGradeFormsAt_of_cleanActionRead S adm hmajority hclean
  have hactive' : P ∈ Protocol.get_filtered_block_tree
      (proposalDutyRead S rho s).st.core.toHealing.toFG := by
    simpa only [Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
      proposalDutyRead, proposerReadAt, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Run.storeBeforeTime, s, t] using hactive
  have hPmem : P ∈
      (relativeG2Read S rho (r + 1) w).st.core.toHealing.gradeView.T := by
    have hmem := mem_T_of_mem_filteredTree (hforms w hprop).1
    simpa only [relativeG2Read, filteredTree] using hmem
  have hPgrade : DecoupledConsensusModel.Protocol.gradeBool S.E
      (relativeG2Read S rho (r + 1) w).st.core.toHealing.gradeView
      (relativeG2Read S rho (r + 1) w).st.core.F S.hc.η_SG (r + 1)
      (early S.E S.hc (r + 1) .g2) (late S.E S.hc (r + 1) .g2) P = true := by
    simpa only [storeGrade, phaseGrade, relativeG2Read] using (hforms w hprop).2
  obtain ⟨raw, hfreeze, hPraw⟩ := NamedOutageClosure.q10_freeze_of_graded
    S.E (relativeG2Read S rho (r + 1) w).st.core.toHealing.gradeView
    (relativeG2Read S rho (r + 1) w).st.core.F S.hc.η_SG (r + 1)
    (NamedOutageClosure.q10_early_le_late S (r + 1) .g2) hPmem hPgrade
  have hround : S.hc.round_of (S.E.slotOf t) = r + 1 := by
    simp only [t, Proofs.Optimistic.slotOf_proposal_time, s,
      Protocol.HealConfig.round_of, Protocol.HealConfig.opening_slot]
    have hR : 0 < S.hc.R := lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two
    simpa only [Nat.mul_comm] using Nat.mul_div_cancel_left (r + 1) hR
  have hta : t ≤ S.a (r + 1) := by
    exact le_of_lt <| (Protocol.proposal_time_lt_vote_time S.E s).trans
      (by simpa only [s] using Protocol.opening_vote_time_lt_action S (r + 1))
  have hfloor := frameG1_preceq_of_freezeRoot_prepared_opening
    S rho adm.toNamedAdmissibleCore w hprop (r + 1) (Nat.succ_pos r) t
      hround (by simp [t, s, domain, opening, Phase.domainOffset]) hactive' hfreeze hPraw
  obtain ⟨root, hroot, hProot⟩ := hfloor
  have hcase :
      (∃ root, (DecoupledConsensusModel.Protocol.readFrame
        (proposalDutyRead S rho s).cache
        (proposalDutyRead S rho s).st.core.toHealing (r + 1)).g1 =
          some (some root) ∧ Block.Preceq P root) ∨
      Block.Preceq P
        (Protocol.get_fg_root
          (proposalDutyRead S rho s).st.core.toHealing.toFG) := by
    exact Or.inl ⟨root, by
      simpa only [proposalDutyRead, proposerReadAt, t, s,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using hroot,
      hProot⟩
  have hanchor : Block.Preceq P
      (nodeAnchor S (proposalDutyRead S rho s) (r + 1)) :=
    anchor_preceq_of_frame_floor S (proposalDutyRead S rho s) (r + 1) P
      hactive' hcase
  have hreadRound : S.hc.round_of
      (proposalDutyRead S rho s).st.core.s = r + 1 := by
    simpa only [duty, Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
      proposalDutyRead, proposerReadAt, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Run.storeBeforeTime, s, t] using hdutyRound
  have hparent : Block.Preceq P (proposedParent S rho s) := by
    have hproposalAnchor := proposalAnchor_preceq_proposedParent S rho s
    rw [hreadRound] at hproposalAnchor
    exact Block.preceq_trans hanchor hproposalAnchor
  rw [proposedBlockErased_parent S rho s hB]
  exact hparent

/-! ## Persistent-grade proposal activity -/

/-- The opening slot names its round. -/
theorem round_of_opening_slot_eq
    (hc : Protocol.HealConfig) (r : Round) :
    hc.round_of (hc.opening_slot r) = r := by
  simp only [Protocol.HealConfig.round_of, Protocol.HealConfig.opening_slot]
  have hR : 0 < hc.R := lt_of_lt_of_le Nat.zero_lt_two hc.R_ge_two
  simpa only [Nat.mul_comm] using Nat.mul_div_cancel_left r hR





#print axioms actionSGVote_mem_stamp_nextOpeningProposer
#print axioms nextOpeningProposer_roundBatch_card_le_one
#print axioms actionSGBlockAt_visible_nextOpeningProposer_of_cleanActionRead
#print axioms actionSGBlockAt_find_nextOpeningProposer_of_cleanActionRead
#print axioms G2_nextOpeningProposer_of_cleanActionRead



/-
/-- Persistent grades from `base` through the round before an opening proposal
give exact selected-source compatibility from the base action to that proposal
read. -/
theorem compatibleAttestationSourcesAfter_to_openingProposal_of_persistentGrades
    (S: Setup V) {rho: Run V} {base q: Round} {P: Block V}
    (hgrades: ∀ k: Round, base ≤ k → k < q →
      NamedGradeFormsAt S rho k P):
    CompatibleAttestationSourcesAfter S rho (S.a base)
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) P:= by
  apply compatibleAttestationSourcesAfter_of_gradeFormsAt S
  intro a ta _ hemit hbase hproposal
  have hshape:= Proofs.Optimistic.emits_attest_shape S hemit
  apply hgrades a.round
  · apply round_le_of_action_le_action S
    simpa only [hshape.2] using hbase
  · by_contra hnot
    have hqle: q ≤ a.round:= Nat.le_of_not_gt hnot
    have hproposalAction:
        Protocol.proposal_time S.E (S.hc.opening_slot q) < S.a q:=
      (Protocol.proposal_time_lt_vote_time S.E
        (S.hc.opening_slot q)).trans
        (Protocol.opening_vote_time_lt_action S q)
    have hactionMono: S.a q ≤ S.a a.round:= Assembly.a_mono S hqle
    have hbad:
        Protocol.proposal_time S.E (S.hc.opening_slot q) < ta:= by
      simpa only [hshape.2] using hproposalAction.trans_le hactionMono
    exact (not_lt_of_ge (le_of_lt hproposal)) hbad

/-- The same persistent-grade interval makes every emitted height target
compatible with the protected block. -/
theorem honestHeightTargetsCompatibleAfter_to_openingProposal_of_persistentGrades
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {base q: Round} {P: Block V}
    (hgrades: ∀ k: Round, base ≤ k → k < q →
      NamedGradeFormsAt S rho k P):
    HonestHeightTargetsCompatibleAfter S rho (S.a base)
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) P:= by
  refine ⟨?_⟩
  intro a ta haHon hemit hbase hproposal h target hpair X hXrun hXroot
  have hshape:= Proofs.Optimistic.emits_attest_shape S hemit
  have hkbase: base ≤ a.round:= by
    apply round_le_of_action_le_action S
    simpa only [hshape.2] using hbase
  have hkq: a.round < q:= by
    by_contra hnot
    have hqle: q ≤ a.round:= Nat.le_of_not_gt hnot
    have hproposalAction:
        Protocol.proposal_time S.E (S.hc.opening_slot q) < S.a q:=
      (Protocol.proposal_time_lt_vote_time S.E
        (S.hc.opening_slot q)).trans
        (Protocol.opening_vote_time_lt_action S q)
    have hactionMono: S.a q ≤ S.a a.round:= Assembly.a_mono S hqle
    have hbad:
        Protocol.proposal_time S.E (S.hc.opening_slot q) < ta:= by
      simpa only [hshape.2] using hproposalAction.trans_le hactionMono
    exact (not_lt_of_ge (le_of_lt hproposal)) hbad
  obtain ⟨i, hevent, ha⟩:= hemit
  exact emittedTarget_compatible_of_gradeFormsAt
    S adm haHon hevent ha hshape.2 (hgrades a.round hkbase hkq)
      hpair X hXrun hXroot
-/








#print axioms protected_preceq_nextOpeningProposedParent_of_cleanActionRead

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
