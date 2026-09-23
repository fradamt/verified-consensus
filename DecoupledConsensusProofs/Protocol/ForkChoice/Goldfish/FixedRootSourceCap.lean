module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ValidatorClient.HeightProgressFixedRoot
public import DecoupledConsensusProofs.Protocol.Grades.RelativeCarrierWindowFixedRoot
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FreshFGSourceCone
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGTargetCanonicalityFixedRoot
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedCeiling
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedCeilingStep

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Fresh FG sources under a fixed justification root

The common root orders each relayed carrier. The exact frontier retains it,
which supplies relative grade settlement without a gate-off premise.
-/

namespace DecoupledConsensusModel.Proofs.HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Protocol Proofs.HealingLemmas Proofs.Optimistic DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

private theorem fixedRootSource_namedTarget
    (S : Setup V) {rho : Run V} {H : Height} {w : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho H w read) :
    ∃ J : NamedBlock V,
      J.erase = (rho.storeBeforeTime S w read).J ∧
        RunBlock S rho J ∧
          (Protocol.derive_named S.E S.cfg J).h = H - 1 := by
  obtain ⟨D, -, hDrun, hjust⟩ := hfix.carrierExists
  have hhj : (Protocol.derive_named S.E S.cfg D).h_j = H - 1 :=
    hjust.2.trans (by simpa only using hfix.fixedTarget.justificationHeight)
  have hhjNe : (Protocol.derive_named S.E S.cfg D).h_j ≠ 0 := by
    rw [hhj]
    exact Nat.ne_of_gt hfix.targetHeightPositive
  obtain ⟨J, hJD, hJerase, hJheight⟩ :=
    (NamedCheckpointHeights.justified_ancestor_height S.E S.cfg D).resolve_left hhjNe
  refine ⟨J, hJerase.trans hjust.1, ?_, ?_⟩
  · exact Proofs.NamedRuntime.blockInRun_of_ancestor S rho hDrun hJD
  · rw [hJheight, hhj]

omit [Fintype V] in
private theorem fixedRootSource_parent_preceq_self (B : NamedBlock V) :
    NamedBlock.Preceq B.parent B := by
  cases B with
  | genesis => exact Proofs.NamedAncestry.named_self _
  | node parent slot root votes support rows proposer =>
      exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
        (Proofs.NamedAncestry.named_self parent)

omit [Fintype V] in
private theorem fixedRootSource_compatible_left
    {A K C : Block V} (hAK : Block.Preceq A K)
    (hKC : Block.compatible K C = true) : Block.compatible A C = true := by
  rcases (show Block.Preceq K C ∨ Block.Preceq C K by
    simpa only [Block.compatible, Bool.or_eq_true] using hKC) with hKC | hCK
  · simpa only [Block.compatible, Bool.or_eq_true] using
      Or.inl (Block.preceq_trans hAK hKC)
  · exact Block.compatible_of_preceq_common hAK hCK

private theorem fixedRootSource_commonActionCeiling
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) {H : Height} {q : Round}
    (hlock : SGTargetOpeningConeRootLock S rho H
      q (S.hc.opening_slot (q + 1) - 1)) :
    ∃ K : Block V,
      (∃ v0 ∈ rho.honest, K = actionSGBlockAt S rho v0 q) ∧
      (∀ v ∈ rho.honest,
        Block.Preceq (actionSGBlockAt S rho v q) K) ∧
      NamedHonestVotesCone S rho (S.hc.opening_slot (q + 1) - 1)
        (fun X => Block.Preceq K X) := by
  have hnonempty : rho.honest.Nonempty :=
    Protocol.honest_nonempty_of_honestCommittees hcom
  obtain ⟨v0, hv0, hv0sup⟩ := Finset.exists_mem_eq_sup' hnonempty
    (fun v => (actionSGBlockAt S rho v q).depth)
  let K := actionSGBlockAt S rho v0 q
  have hmax : ∀ v ∈ rho.honest,
      (actionSGBlockAt S rho v q).depth ≤ K.depth := by
    intro v hv
    rw [← hv0sup]
    exact Finset.le_sup' (fun v => (actionSGBlockAt S rho v q).depth) hv
  have hupper : ∀ v ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho v q) K := by
    intro v hv
    have hcompat := sgTargetCompatible_of_honestVotesCone S hcom
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      adm.toNamedAdmissibleCore.toNamedRootCollisionFree
      (hlock.canonical v hv) (hlock.canonical v0 hv0)
    simpa only [K] using
      AlignedRoundLemmas.preceq_of_compatible_of_depth_le hcompat (hmax v hv)
  exact ⟨K, ⟨v0, hv0, rfl⟩, hupper,
    by simpa only [K] using hlock.canonical v0 hv0⟩

private theorem fixedRootSource_runBlock_of_actionBody
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {B : NamedBlock V}
    (hB : B ∈ (actionReadAt S rho v r).st.bodies) :
    RunBlock S rho B := by
  have hBpre : B ∈ (rho.storeBeforeTime S v (S.a r)).bodies := by
    simpa only [actionReadAt, NamedActionReads.actionReadAt,
      NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hB
  obtain ⟨i, hi, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.a r)
  apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i := i)
  rw [← hi]
  exact hBpre

private theorem fixedRootSource_namedSource_witness
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {Q : Block V}
    (hsource : nodeFGSource S (actionReadAt S rho v r) r = some Q) :
    ∃ Cn : NamedBlock V,
      Cn ∈ (actionReadAt S rho v r).st.bodies ∧
      Cn.erase = Q ∧
      RunBlock S rho Cn ∧
      (actionReadAt S rho v r).st.core.toHealing.σ Q =
        Protocol.derive_named S.E S.cfg Cn := by
  have hround : S.hc.round_of
      (actionReadAt S rho v r).st.core.toHealing.s = r := by
    simpa only [actionStoreAt, Protocol.Store.toHealing] using
      actionStoreAt_round S rho v r
  have hsource' : actionFGSource S (actionReadAt S rho v r) = some Q := by
    have hsource0 := hsource
    simp only [PhaseGrades.nodeFGSource] at hsource0
    simpa only [actionFGSource, hround] using hsource0
  obtain ⟨Cn, hCnbody, hCnerase, hσ, -⟩ :=
    NamedActionSources.action_witness S rho v r Q hsource'
  have hCnrun := fixedRootSource_runBlock_of_actionBody S adm hv hCnbody
  exact ⟨Cn, hCnbody, hCnerase, hCnrun, hσ⟩

set_option maxHeartbeats 400000 in
private theorem fixedRootSource_proposalAnchor_preceq_of_previousCarriers
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest) {q : Round}
    (hpost : S.E.t_GST ≤ S.a q)
    (hcut : S.hc.Γ_neg1 S.E.Δ (q + 1) ≤ rho.horizon)
    (hproposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot (q + 1)) ≤ rho.horizon)
    {C : Block V}
    (hupper : ∀ v ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho v q) C)
    (hprop : S.E.proposer (S.hc.opening_slot (q + 1)) ∈ rho.honest)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (proposerReadAt S rho (S.hc.opening_slot (q + 1))).st.core.toHealing.toFG) C) :
    Block.Preceq
      (nodeAnchor S
        (Internal.NamedRecoveryRead.proposalDutyRead S rho
          (S.hc.opening_slot (q + 1))) (q + 1)) C := by
  let o := S.hc.opening_slot (q + 1)
  let w := S.E.proposer o
  have hw : w ∈ rho.honest := by simpa only [w] using hprop
  have hround : S.hc.round_of o = q + 1 :=
    round_of_opening_slot_eq_schedule S.hc (q + 1)
  have hopen : DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1 =
      Protocol.proposal_time S.E o := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    rfl
  have hdomainHor : DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1 ≤
      rho.horizon := by
    rw [hopen]
    exact hproposalHor
  have hroundTime : S.hc.round_of (S.E.slotOf
      (Protocol.proposal_time S.E o)) = q + 1 := by
    simpa only [Proofs.Optimistic.slotOf_proposal_time] using hround
  have hframeStore := preparedFrame_g1_eq_storeRoot_at_opening S rho
    adm.toNamedAdmissibleCore (S.E.proposer o) hprop (q + 1) (Nat.succ_pos q)
    (Protocol.proposal_time S.E o) hroundTime hopen hdomainHor
  have hroundSt : S.hc.round_of
      (Internal.NamedRecoveryRead.proposalDutyRead S rho o).st.core.s = q + 1 := by
    simpa only [Internal.NamedRecoveryRead.proposalDutyRead, proposerReadAt,
      NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, Proofs.Optimistic.slotOf_proposal_time] using hround
  change Block.Preceq
    (nodeAnchor S (Internal.NamedRecoveryRead.proposalDutyRead S rho o)
      (q + 1)) C
  rcases proposalAnchor_cases S rho o with hfg | hactive
  · rw [hroundSt] at hfg
    rw [hfg]
    exact hroot
  · obtain ⟨root, A, hframe, hactive, hanchor⟩ := hactive
    have hanchor' : nodeAnchor S
        (Internal.NamedRecoveryRead.proposalDutyRead S rho o) (q + 1) = A := by
      simpa only [hroundSt] using hanchor
    rw [hanchor']
    have hframe' := hframe
    rw [hroundSt] at hframe'
    have hframe'' :
        (DecoupledConsensusModel.Protocol.readFrame
          (proposerReadAt S rho o).cache
          (proposerReadAt S rho o).st.core.toHealing (q + 1)).g1 =
          some (some root) := by
      simpa only [Internal.NamedRecoveryRead.proposalDutyRead,
        proposerReadAt] using hframe'
    let read := PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1)
      (S.E.proposer o)
    have hframeRead :
        (DecoupledConsensusModel.Protocol.readFrame
          (proposerReadAt S rho o).cache
          (proposerReadAt S rho o).st.core.toHealing (q + 1)).g1 =
          some ((storeRoot S.E S.hc read.st (q + 1) .g1).map
            (fun X => DecoupledConsensusModel.Protocol.clipGrade X
              (proposerReadAt S rho o).st.core.F)) := by
      simpa only [read, Internal.NamedRecoveryRead.proposalDutyRead, proposerReadAt,
        NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock] using hframeStore
    cases hstore : storeRoot S.E S.hc read.st (q + 1) .g1 with
    | none =>
        simp only [hstore, Option.map_none] at hframeRead
        rw [hframe''] at hframeRead
        cases hframeRead
    | some raw =>
        have hrootEq : root = DecoupledConsensusModel.Protocol.clipGrade raw
            (proposerReadAt S rho o).st.core.F := by
          have hopt : some (some root) = some
              (some (DecoupledConsensusModel.Protocol.clipGrade raw
                (proposerReadAt S rho o).st.core.F)) :=
            hframe''.symm.trans (by
              simpa only [hstore, Option.map_some] using hframeRead)
          exact Option.some.inj (Option.some.inj hopt)
        have hLroot : Block.Preceq A root := by
          unfold DecoupledConsensusModel.Protocol.activePrefix at hactive
          exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).2
        have hLraw : Block.Preceq A raw := by
          rw [hrootEq] at hLroot
          exact Block.preceq_trans hLroot
            (NamedOutageClosure.q10_clip_preceq raw
              (proposerReadAt S rho o).st.core.F)
        have hrawData := Proofs.Engine.deepest?_mem hstore
        have hrawTree : raw ∈ read.st.core.T :=
          (Finset.mem_filter.mp hrawData).1
        have hLtree : A ∈ read.st.core.T := by
          have hpc := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1)
            (S.E.proposer o)
          exact Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
            A raw hrawTree hLraw
        have hrawGrade : PhaseGrades.phaseGrade S.E S.hc
            read.st.core.toHealing.gradeView read.st.core.F
            (q + 1) .g1 raw = true := (Finset.mem_filter.mp hrawData).2
        have hAGrade := confirmation_phaseGrade_mono S.E S.hc _ _ (q + 1) .g1
          hLraw hrawGrade
        have hFroot : Block.Preceq read.st.core.F
            (Protocol.get_fg_root
              (proposerReadAt S rho o).st.core.toHealing.toFG) := by
          have hFJ :=
            Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
              (Protocol.proposal_time S.E o) (S.E.proposer o)
          simpa only [read, PhaseGrades.readAt, proposerReadAt,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom, hopen,
            Protocol.NamedStore.setClock] using
            (Proofs.Records.preceq_get_fg_root_of_F
              (st := (NamedRun.stateBeforeTime S rho
                (Protocol.proposal_time S.E o) (S.E.proposer o)).st.core.toHealing.toFG)
              hFJ)
        have hFC : Block.Preceq read.st.core.F C :=
          Block.preceq_trans hFroot hroot
        have hlatest : q ∈ Protocol.latest_window S.hc.η_SG (q + 1) := by
          simpa only [Nat.add_sub_cancel] using
            Protocol.pred_mem_latest_window S.hc.η_SG (q + 1)
              S.hc.η_SG_ge_one (Nat.succ_pos q)
        have hactionDeadline : S.a q + S.E.Δ ≤
            DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1 :=
          (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
            (Nat.lt_succ_self q)).trans
            (NamedOutageClosure.q10_early_g2_le_early_g1 S (q + 1))
        have hactionHor : S.a q ≤ rho.horizon :=
          (le_add_of_nonneg_right S.E.Δ_pos.le).trans
            ((action_add_delta_le_next_Γ_neg1 S q).trans hcut)
        have hearlyHor : DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1 ≤
            rho.horizon :=
          (NamedOutageClosure.q10_early_g1_le_domain_g2 S (q + 1)).trans
            (by simpa only [gammaNeg1_eq_domain_g2_succ S q] using hcut)
        have hearlyDomain : DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1 ≤
            DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1 :=
          (NamedOutageClosure.q10_early_g1_le_domain_g2 S (q + 1)).trans
            (NamedOutageClosure.q10_domain_g2_lt_domain_g1 S (q + 1)).le
        have hinterpreted : ∀ v ∈ rho.honest,
            (DecoupledConsensusModel.Protocol.interpretedInputs
              read.st.core.toHealing.gradeView read.st.core.F S.hc.η_SG
              (q + 1) (DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1) v).Nonempty := by
          intro v hv
          obtain ⟨a, hemit, hproj⟩ :=
            honest_emits_actionAttestationAt S adm hv q hactionHor (by assumption)
          obtain ⟨i, hi, -, H, hH, hconfirmed⟩ :=
            Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
          have haval : a.val_index = v := by
            have h := congrArg Protocol.SGVote.val_index hproj
            simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
          have haround : a.round = q := by
            have h := congrArg Protocol.SGVote.round hproj
            simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
          have hHbody : H ∈ (NamedRun.stateBefore S rho i v).st.bodies := by
            change H ∈ (NamedRun.stateBefore S rho i v).st.bodies at hH
            exact hH
          have hHrun : RunBlock S rho H :=
            Proofs.Bridges.runBlock_of_stateBefore_mem S hv hHbody
          have hCmem : actionSGBlockAt S rho v q ∈
              (rho.storeBeforeTime S v (S.a q)).T :=
            actionSGBlockAt_mem_storeBeforeTime S rho v q
          obtain ⟨Cn, hCnerase, hCnrun⟩ :=
            Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
              adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv (S.a q) hCmem
          have hconfirmedCarrier : a.confirmed =
              some (actionSGBlockAt S rho v q).root := by
            have h := congrArg Protocol.SGVote.confirmed hproj
            simpa only [Protocol.sgVote, actionSGVoteAt,
              NamedAttestation.erase] using h
          have hrootEq : H.erase.root = Cn.erase.root := by
            rw [Proofs.NamedWire.erase_root, hCnerase]
            exact congrArg id (Option.some.inj
              (hconfirmed.symm.trans hconfirmedCarrier))
          have hHCeq : H.erase = Cn.erase :=
            Protocol.runBlock_eq_of_root_eq
              adm.toNamedRootCollisionFree hHrun hCnrun hrootEq
          have hHC : Block.Preceq H.erase C := by
            rw [hHCeq, hCnerase]
            exact hupper v hv
          have hmem :=
            action_vote_mem_interpretedInputs_after_gst_common_upper
              S adm.toNamedAdmissibleCore .g1 hlatest hv hw
              ⟨haval, haround, hemit⟩ ⟨i, hi, hH, hconfirmed⟩ hHC hFC
              (by simpa only [haround] using hpost)
              (by rw [haround, max_eq_left hpost]; exact hactionDeadline)
              hearlyDomain hearlyHor
          exact ⟨Protocol.sgVote a.erase, by simpa only [read] using hmem⟩
        have hrepresented : ∀ v ∈ rho.honest,
            Protocol.represented read.st.core.toHealing.sg_votes
              S.hc.η_SG v (q + 1) = true := by
          intro v hv
          obtain ⟨a, hemit, hproj⟩ :=
            honest_emits_actionAttestationAt S adm hv q hactionHor (by assumption)
          obtain ⟨i, hi, -, H, hH, hconfirmed⟩ :=
            Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
          have haval : a.val_index = v := by
            have h := congrArg Protocol.SGVote.val_index hproj
            simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
          have haround : a.round = q := by
            have h := congrArg Protocol.SGVote.round hproj
            simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
          have hHbody : H ∈ (NamedRun.stateBefore S rho i v).st.bodies := by
            change H ∈ (NamedRun.stateBefore S rho i v).st.bodies at hH
            exact hH
          have hHrun : RunBlock S rho H :=
            Proofs.Bridges.runBlock_of_stateBefore_mem S hv hHbody
          have hCmem : actionSGBlockAt S rho v q ∈
              (rho.storeBeforeTime S v (S.a q)).T :=
            actionSGBlockAt_mem_storeBeforeTime S rho v q
          obtain ⟨Cn, hCnerase, hCnrun⟩ :=
            Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
              adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv (S.a q) hCmem
          have hconfirmedCarrier : a.confirmed =
              some (actionSGBlockAt S rho v q).root := by
            have h := congrArg Protocol.SGVote.confirmed hproj
            simpa only [Protocol.sgVote, actionSGVoteAt,
              NamedAttestation.erase] using h
          have hrootEq : H.erase.root = Cn.erase.root := by
            rw [Proofs.NamedWire.erase_root, hCnerase]
            exact congrArg id (Option.some.inj
              (hconfirmed.symm.trans hconfirmedCarrier))
          have hHCeq : H.erase = Cn.erase :=
            Protocol.runBlock_eq_of_root_eq
              adm.toNamedRootCollisionFree hHrun hCnrun hrootEq
          have hHC : Block.Preceq H.erase C := by
            rw [hHCeq, hCnerase]
            exact hupper v hv
          have hmem :=
            action_vote_mem_interpretedInputs_after_gst_common_upper
              S adm.toNamedAdmissibleCore .g1 hlatest hv hw
              ⟨haval, haround, hemit⟩ ⟨i, hi, hH, hconfirmed⟩ hHC hFC
              (by simpa only [haround] using hpost)
              (by rw [haround, max_eq_left hpost]; exact hactionDeadline)
              hearlyDomain hearlyHor
          have hraw := (Finset.mem_filter.mp hmem).1
          obtain ⟨hpool, hfields⟩ := Finset.mem_filter.mp hraw
          obtain ⟨k, hk, huk⟩ := Finset.mem_biUnion.mp hpool
          exact Protocol.represented_of_vote_mem
            (List.mem_toFinset.mp hk) huk hfields.1
        have hwindow := windowMajorityAt_of_honestWeightMajority_of_represented
          S (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird
            (S := S) hfb) hrepresented hinterpreted
        have hgrade : DecoupledConsensusModel.Protocol.gradeBool S.E
            read.st.core.toHealing.gradeView read.st.core.F S.hc.η_SG (q + 1)
            (DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1)
            (DecoupledConsensusModel.Protocol.late S.E S.hc (q + 1) .g1) A = true := by
          simpa only [read, PhaseGrades.storeGrade, PhaseGrades.phaseGrade] using hAGrade
        obtain ⟨v, hv, u, hu, head, hconf, hfind, -, hAhead, -, hmax⟩ :=
          exists_honest_max_positive_supporter_of_relativeGrade
            S.E S.hc hwindow hgrade
        obtain ⟨a, hemit, hproj⟩ :=
          honest_emits_actionAttestationAt S adm hv q hactionHor (by assumption)
        obtain ⟨i, hi, -, H, hH, hconfirmed⟩ :=
          Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
        have haval : a.val_index = v := by
          have h := congrArg Protocol.SGVote.val_index hproj
          simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
        have haround : a.round = q := by
          have h := congrArg Protocol.SGVote.round hproj
          simpa only [Protocol.sgVote, actionSGVoteAt, NamedAttestation.erase] using h
        have hHbody : H ∈ (NamedRun.stateBefore S rho i v).st.bodies := by
          change H ∈ (NamedRun.stateBefore S rho i v).st.bodies at hH
          exact hH
        have hHrun : RunBlock S rho H :=
          Proofs.Bridges.runBlock_of_stateBefore_mem S hv hHbody
        have hCmem : actionSGBlockAt S rho v q ∈
            (rho.storeBeforeTime S v (S.a q)).T :=
          actionSGBlockAt_mem_storeBeforeTime S rho v q
        obtain ⟨Cn, hCnerase, hCnrun⟩ :=
          Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
            adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv (S.a q) hCmem
        have hconfirmedCarrier : a.confirmed =
            some (actionSGBlockAt S rho v q).root := by
          have h := congrArg Protocol.SGVote.confirmed hproj
          simpa only [Protocol.sgVote, actionSGVoteAt,
            NamedAttestation.erase] using h
        have hrootEq : H.erase.root = Cn.erase.root := by
          rw [Proofs.NamedWire.erase_root, hCnerase]
          exact congrArg id (Option.some.inj
            (hconfirmed.symm.trans hconfirmedCarrier))
        have hHCeq : H.erase = Cn.erase :=
          Protocol.runBlock_eq_of_root_eq
            adm.toNamedRootCollisionFree hHrun hCnrun hrootEq
        have hHC : Block.Preceq H.erase C := by
          rw [hHCeq, hCnerase]
          exact hupper v hv
        have hactionInput :=
          action_vote_mem_interpretedInputs_after_gst_common_upper
            S adm.toNamedAdmissibleCore .g1 hlatest hv hw
            ⟨haval, haround, hemit⟩ ⟨i, hi, hH, hconfirmed⟩ hHC hFC
            (by simpa only [haround] using hpost)
            (by rw [haround, max_eq_left hpost]; exact hactionDeadline)
            hearlyDomain hearlyHor
        have hqle : q ≤ u.round := by
          have := hmax (Protocol.sgVote a.erase) hactionInput
          simpa only [Protocol.sgVote, NamedAttestation.erase, haround] using this
        have huraw := (Finset.mem_filter.mp hu).1
        obtain ⟨b, hbval, hbround, hbproj, huwindow, -, hbemit⟩ :=
          NamedOutageClosure.rawInputs_trace S rho
            adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
            adm.toNamedAdmissibleCore.toNamedUnforgeable
            (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1)
            (DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g1) w
            S.hc.η_SG (q + 1) v hv (by simpa only [read] using huraw)
        have hule : u.round ≤ q := Nat.le_of_lt_succ
          (NamedOutageClosure.window_bounds huwindow).2
        have huroundEq : u.round = q := Nat.le_antisymm hule hqle
        have hbroundQ : b.round = q := hbround.trans huroundEq
        have hba : b = a := Proofs.Optimistic.emits_attest_unique S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hbemit hemit
          (hbroundQ.trans haround.symm)
        have huEq : u = Protocol.sgVote a.erase := by
          rw [← hbproj, hba]
        have hheadRoot : head.root = (actionSGBlockAt S rho v q).root := by
          have huconf := congrArg Protocol.SGVote.confirmed huEq
          simpa only [Protocol.sgVote, NamedAttestation.erase, hconf,
            hconfirmedCarrier, Option.some.injEq] using huconf
        have hheadMem : head ∈ read.st.core.T := Proofs.HealingLemmas.find?_mem hfind
        obtain ⟨Headn, hHeaderase, hHeadrun⟩ :=
          Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
            adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hw
            (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g1) (by
              simpa only [read] using hheadMem)
        have hheadCnRoot : Headn.erase.root = Cn.erase.root := by
          rw [hHeaderase, hCnerase]
          exact hheadRoot
        have hheadCarrier : head = actionSGBlockAt S rho v q := by
          rw [← hHeaderase, ← hCnerase]
          exact Protocol.runBlock_eq_of_root_eq
            adm.toNamedAdmissibleCore.toNamedRootCollisionFree
            hHeadrun hCnrun hheadCnRoot
        have hAC : Block.Preceq A C :=
          Block.preceq_trans (by simpa only [hheadCarrier] using hAhead)
            (hupper v hv)
        exact hAC

private theorem fixedRootSource_preceq_voterHeadAt_of_adoption
    (S : Setup V) {rho : Run V} {source : Protocol.Store V}
    {s : Slot} {B : Block V} {w : V}
    (heligible : Protocol.voters_count S.E (confLate S.E source s) s <
      2 * Protocol.goldfish_score S.E source.T
        (confVotes S.E source s) (confVotes S.E source s) s B)
    (hadopt : NamedNextVoteAdoption S rho source s B w) :
    Block.Preceq B (voterHeadAt S rho w (s + 1)) := by
  let read := Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)
  let st := read.st.core
  let tree := voterCandidateTreeAt S rho w (s + 1)
  let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  have hslot : st.s = s + 1 := by
    simpa only [st, read] using Proofs.Optimistic.voteDutyRead_slot S rho w (s + 1)
  have hprev : st.s - 1 = s := by rw [hslot]; simp
  change Block.Preceq B
    (Protocol.get_head_in_tree_with_layer
      (NamedProfile.gradeContract read.cache) S.E S.hc st.toHealing
      tree votes support (st.s - 1))
  rw [Proofs.Optimistic.get_head_in_tree_split_with, hprev]
  simpa only [Protocol.Store.toHealing, read, st] using
    (Protocol.goldfish_fork_choice_captures_of_confirmation
      S.E st.σ st.h_max source.T st.T tree st.s
      (confEarly S.E source s) (confLate S.E source s)
      (confVotes S.E source s) votes support s
      (confNumerator S.E source s) hadopt.transport heligible
      hadopt.support_subset hadopt.anchor hadopt.path)

private theorem fixedRootSource_ancestorConfirmation_eligible
    (E : Env V) (hc : Protocol.HealConfig)
    (source : Protocol.Store V) (s : Slot)
    {T C : Block V} {contract : Protocol.GradeContract V}
    (hTC : Block.Preceq T C)
    (hC : GenuineConfirmationWith contract E hc source s C) :
    Protocol.voters_count E (confLate E source s) s <
      2 * Protocol.goldfish_score E source.T
        (confVotes E source s) (confVotes E source s) s T := by
  have hN := confNumerator E source s
  have hsupport := supporters_mono E source.T
    (confVotes E source s) (confVotes E source s) s hTC
  have hcard := Finset.card_le_card hsupport
  have hCg : GenuineConfirmation (contract := contract) E hc source s C :=
    ⟨hC.selected, hC.genuine⟩
  have hCeligible := hCg.eligible
  rw [hN.score_eq_supporters] at hCeligible ⊢
  exact lt_of_lt_of_le hCeligible (Nat.mul_le_mul_left 2 hcard)

private theorem fixedRootSource_confirmation_time_mono
    (E : Env V) {a b : Slot} (hab : a ≤ b) :
    Protocol.confirmation_time E a ≤ Protocol.confirmation_time E b := by
  rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time E a,
    ← Protocol.vote_time_succ_add_delta_eq_confirmation_time E b]
  exact Int.add_le_add_right
    (Protocol.vote_time_mono_slots E (Nat.succ_le_succ hab)) _

private theorem fixedRootSource_voteDutyRead_fgRoot_eq_storeBeforeTime
    (S : Setup V) (rho : Run V) (v : V) (d : Slot) :
    Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho v d).st.core.toHealing.toFG =
      Protocol.get_fg_root
        (rho.storeBeforeTime S v (Protocol.vote_time S.E d)).toHealing.toFG := by
  rfl

private theorem fixedRootSource_voteDutyRead_hMax_eq_storeBeforeTime
    (S : Setup V) (rho : Run V) (v : V) (d : Slot) :
    (Internal.NamedRecoveryRead.voteDutyRead S rho v d).st.core.h_max =
      (rho.storeBeforeTime S v (Protocol.vote_time S.E d)).h_max := by
  rfl

private theorem fixedRootSource_round_lt_of_lower_nat
    {r q1 : Nat} (h : r + 3 ≤ q1) : r < q1 := by
  omega

private theorem fixedRootSource_round_bounds_nat
    {r q1 q' delay : Nat} (hlo : r + 3 ≤ q1)
    (_hpos : 0 < q1) (hlt : q1 < q')
    (hspace : q1 + 2 + delay ≤ q') :
    0 < q' ∧ 0 < q' - 1 ∧ q1 < q' - 1 ∧ q1 ≤ q' - 2 ∧
      q1 ≤ q' - 1 - 1 ∧ 0 < q' - 1 - 1 := by
  omega

/-- A common FG root and exact frontier settle every previous action carrier. -/
theorem previousActionCarriersQuietAt_of_fixedRoot
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {c : Round} (hc : 0 < c) {H : Height} {J : Block V}
    (hpost : S.E.t_GST ≤ S.a (c - 1))
    (hprev : ∀ u ∈ rho.honest,
      Protocol.get_fg_root
          (rho.storeBeforeTime S u (S.a (c - 1))).toHealing.toFG = J ∧
        (rho.storeBeforeTime S u (S.a (c - 1))).h_max = H)
    (hcurrent : ∀ w ∈ rho.honest,
      Protocol.get_fg_root
          (rho.storeBeforeTime S w (S.a c)).toHealing.toFG = J ∧
        (rho.storeBeforeTime S w (S.a c)).h_max = H)
    (hhor : S.a c ≤ rho.horizon) :
    PreviousActionCarriersQuietAt S rho c := by
  intro u hu w hw
  obtain ⟨W, hWbody, hcarrierW, hWh⟩ :=
    actionSGBlockAt_frontierWitness S adm (hprev u hu).2
  have hJcarrier : Block.Preceq J (actionSGBlockAt S rho u (c - 1)) := by
    have h := Proofs.Records.preceq_get_fg_root_of_mem_filtered
      (actionSGBlockAt_mem_filtered_actionStore S adm u (c - 1))
    rw [actionStoreAt_fgRoot_eq_storeBeforeTime, (hprev u hu).1] at h
    exact h
  have hJW : Block.Preceq J W.erase := Block.preceq_trans hJcarrier hcarrierW
  have hrootW : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w (S.a c)).toHealing.toFG) W.erase := by
    rw [(hcurrent w hw).1]
    exact hJW
  obtain ⟨hWtarget, -, -⟩ := actionConeWitness_visibleAtReader_after_gst
    S adm hu hw hWbody (Block.preceq_self W.erase) hWh hpost
      (Protocol.previous_action_add_delta_le_action S hc) hhor hrootW
  have hcap : (rho.storeBeforeTime S w (S.a c)).h_max ≤
      (Protocol.derive_named S.E S.cfg W).h + 1 := by
    rw [(hcurrent w hw).2]
    exact Nat.sub_le_iff_le_add.mp hWh
  have hquiet : FinalityFilterNoninterferenceAtRead S rho w (S.a c) W.erase :=
    Or.inr (mem_filtered_of_mem_tree_of_exactFGRoot_heightCap
      S rho w (S.a c) hWtarget rfl (hcurrent w hw).1 hJW hcap)
  exact hquiet.ancestor S adm hcarrierW

/-- Fixed-root relay and relative majority settle every named G1 ancestor. -/
theorem namedLiveG1SettledAt_of_fixedRoot
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest) {c : Round} (hc : 0 < c)
    {H : Height} {w : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho H w read)
    (hpostRead : S.E.t_GST ≤ read)
    (hpost : S.E.t_GST ≤ S.a (c - 1))
    (hprevDelay : read + S.E.Δ ≤ S.a (c - 1))
    (hprevHor : S.a (c - 1) ≤ rho.horizon)
    (hprevCap : honestHMaxAt S rho (S.a (c - 1)) ≤ H)
    (hactionDelay : read + S.E.Δ ≤ S.a c)
    (hactionHor : S.a c ≤ rho.horizon)
    (hactionCap : honestHMaxAt S rho (S.a c) ≤ H) :
    NamedLiveG1SettledAt S rho c := by
  have hsb := slashableBound_of_admissible_belowOneThird S adm hfb
  have hprev := fun (u : V) (hu : u ∈ rho.honest) =>
    fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
      S adm hsb hfix hu hpostRead hprevDelay hprevHor hprevCap
  have hcurrent := fun (u : V) (hu : u ∈ rho.honest) =>
    fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
      S adm hsb hfix hu hpostRead hactionDelay hactionHor hactionCap
  have hquiet := previousActionCarriersQuietAt_of_fixedRoot S adm hc hpost
    hprev hcurrent hactionHor
  have hwindow := relativeCarrierWindowAt_of_fixedRoot S adm hfb hc hfix
    hpostRead hpost hprevDelay hprevHor hprevCap hactionDelay hactionHor
      hactionCap ((FrameForward.domain_le_a S c .g1).trans hactionHor)
  have hmajority := gradeFormingMajority_of_admissible_belowOneThird S adm hfb hc
    ((FrameForward.domain_le_a S c .g2).trans hactionHor) (by assumption)
  exact namedLiveG1SettledAt_of_previousActionCarriersQuiet S adm hc
    hwindow hmajority hquiet

/-- The exact FG source is active at its action read. -/
theorem fixedRootSource_mem_filtered_actionStore
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (v : V) (r : Round) {C : Block V}
    (hsource : nodeFGSource S (actionReadAt S rho v r) r = some C) :
    C ∈ Protocol.get_filtered_block_tree
      (actionStoreAt S rho v r).toHealing.toFG := by
  cases hQ : nodeQ2 S (actionReadAt S rho v r) r with
  | none =>
      have hbad := hsource
      simp only [nodeFGSource, nodeQ2, nodeRead] at hbad hQ
      unfold Protocol.grade2_block_with at hbad
      rw [hQ] at hbad
      simp [Protocol.fg_source_with] at hbad
  | some Q =>
      have hQmem : Q ∈ Protocol.get_filtered_block_tree
          (actionStoreAt S rho v r).toHealing.toFG :=
        actionQ2_mem_filteredTree S rho v r hQ
      have hsource' := hsource
      rw [nodeFGSource, Protocol.fg_source_with.eq_def] at hsource'
      have hQ' : Protocol.grade2_block_with
          (NamedProfile.gradeContract (actionReadAt S rho v r).cache)
          S.E S.hc (actionReadAt S rho v r).st.core.toHealing r = some Q := hQ
      rw [hQ'] at hsource'
      cases hwalk : Protocol.deepest_clear (some Q)
          (actionReadAt S rho v r).st.core.toHealing.live_confirmed
          ((NamedProfile.gradeContract (actionReadAt S rho v r).cache).read
            S.E S.hc (actionReadAt S rho v r).st.core.toHealing r).clear with
      | none =>
          simp only [hwalk] at hsource'
          rw [← Option.some_inj.mp hsource']
          exact hQmem
      | some B =>
          simp only [hwalk] at hsource'
          have hCB : C = B := (Option.some_inj.mp hsource').symm
          subst B
          have hmemChain := Proofs.Engine.deepest?_mem hwalk
          obtain ⟨hchain, hQC, -⟩ := Finset.mem_filter.mp hmemChain
          have hCL : Block.Preceq C
              (actionStoreAt S rho v r).live_confirmed :=
            Proofs.Engine.mem_chain_of_preceq (List.mem_toFinset.mp hchain)
          have hQC' : Block.Preceq Q C := by simpa using hQC
          have hLmem := liveConfirmed_mem_filtered_actionStore S adm v r
          have hQmem' := hQmem
          have hLmem' := hLmem
          simp only [Protocol.get_filtered_block_tree,
            Protocol.get_filtered_block_tree_from,
            Protocol.viable_tree, Protocol.finalized_descendants,
            Protocol.viable, Finset.mem_filter, Protocol.Store.toHealing,
            decide_eq_true_eq] at hQmem' hLmem' ⊢
          obtain ⟨⟨⟨-, hFQ⟩, -⟩, hrootQ⟩ := hQmem'
          obtain ⟨⟨⟨hLT, -⟩, W, hWT, hLW, hWh⟩, -⟩ := hLmem'
          have hpc : ParentClosed (actionStoreAt S rho v r).st.core := by
            have hpcPre := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime
              S rho (S.a r) v
            have hT : (actionStoreAt S rho v r).st.core.T =
                (rho.storeBeforeTime S v (S.a r)).core.T := rfl
            simpa only [ParentClosed, Protocol.GoldfishStore.parent_closed, hT] using hpcPre
          refine ⟨⟨⟨?_, ?_⟩, W, hWT,
            Block.preceq_trans hCL hLW, hWh⟩, ?_⟩
          · exact Proofs.Records.mem_of_preceq hpc.2 C _ hLT hCL
          · exact Block.preceq_trans hFQ hQC'
          · exact Block.preceq_trans hrootQ hQC'

set_option maxHeartbeats 400000 in
/-- Every prepared honest seed voter anchor is compatible with the exact FG
source selected by any honest action in the round. -/
theorem preparedAnchor_compatible_freshFGSource_of_fixedRoot
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {c : Round} (hc : 1 ≤ c) {J : Block V}
    (hactionRoot : ∀ u ∈ rho.honest,
      Protocol.get_fg_root
        (rho.storeBeforeTime S u (S.a c)).toHealing.toFG = J)
    (hsettled : NamedLiveG1SettledAt S rho c)
    (hhorNext : S.a (c + 1) ≤ rho.horizon)
    (ready : GradeRoundReady S rho c)
    {w v : V} (hw : w ∈ rho.honest) (hv : v ∈ rho.honest) {d : Slot}
    (hd1 : S.hc.opening_slot c + 1 ≤ d)
    (hd2 : d ≤ seedRoundLastSlot S c)
    (hround : S.hc.round_of d = c)
    (hvoteRoot : Protocol.get_fg_root
      (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.toFG = J)
    {C : Block V}
    (hsource : nodeFGSource S (actionReadAt S rho v c) c = some C) :
    Block.compatible (voterAnchorAt S rho w d) C = true := by
  have hcPos : 0 < c := Nat.succ_le_iff.mp hc
  have haCSucc : S.a c ≤ S.a (c + 1) := Assembly.a_mono S (Nat.le_succ c)
  have hhorC : S.a c ≤ rho.horizon := haCSucc.trans hhorNext
  have hlo : S.hc.opening_slot c ≤ d := (Nat.le_succ _).trans hd1
  have hdNext : d ≤ S.hc.opening_slot (c + 1) :=
    hd2.trans (by unfold seedRoundLastSlot; exact Nat.sub_le _ _)
  have hvoteHi : Protocol.vote_time S.E d ≤ S.a (c + 1) := by
    refine (Protocol.vote_time_le_confirmation_time S.E d).trans ?_
    have hm : Protocol.confirmation_time S.E d ≤
        Protocol.confirmation_time S.E (S.hc.opening_slot (c + 1)) := by
      rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E d,
        ← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E
          (S.hc.opening_slot (c + 1))]
      exact Int.add_le_add_right
        (Protocol.vote_time_mono_slots S.E (Nat.succ_le_succ hdNext)) _
    exact hm.trans (by rw [Setup.a, Protocol.a_eq_confirmation_time])
  have hvoteHor := hvoteHi.trans hhorNext
  have hnext : Protocol.vote_time S.E d ≤ opening S.E S.hc (c + 1) := by
    have hlt : d < S.hc.opening_slot (c + 1) :=
      hd2.trans_lt (Nat.sub_lt (by
        unfold Protocol.HealConfig.opening_slot
        exact Nat.mul_pos (Nat.succ_pos c)
          (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)) Nat.one_pos)
    exact (le_of_lt (by
      simpa only [opening] using
        (show Protocol.vote_time S.E d <
          Protocol.proposal_time S.E (S.hc.opening_slot (c + 1)) from
          (by
            exact (by
              have h := Protocol.proposal_time_mono S.E (Nat.succ_le_of_lt hlt)
              exact (lt_of_lt_of_le
                (by
                  simp only [Protocol.vote_time, Protocol.proposal_time,
                    Env.t, slotStart]
                  push_cast
                  nlinarith [S.E.Δ_pos]) h))))))
  have hsb := slashableBound_of_admissible_belowOneThird S adm hfb
  have hJC : Block.Preceq J C := by
    have h := Proofs.Records.preceq_get_fg_root_of_mem_filtered
      (fixedRootSource_mem_filtered_actionStore S adm v c hsource)
    rw [actionStoreAt_fgRoot_eq_storeBeforeTime, hactionRoot v hv] at h
    exact h
  cases hQ : nodeQ2 S (actionReadAt S rho v c) c with
  | none =>
      have hbad := hsource
      simp only [nodeFGSource, nodeQ2, nodeRead] at hbad hQ
      unfold Protocol.grade2_block_with at hbad
      rw [hQ] at hbad
      simp [Protocol.fg_source_with] at hbad
  | some Q =>
      have hQG1 := namedG1At_of_nodeQ2 S adm hcPos hhorC v hv Q hQ
      have hQG2 := selectedQ2_storeGrade_at_g2Domain S adm hQ
      have hsource' := hsource
      rw [nodeFGSource, Protocol.fg_source_with.eq_def] at hsource'
      have hQ' : Protocol.grade2_block_with
          (NamedProfile.gradeContract (actionReadAt S rho v c).cache)
          S.E S.hc (actionReadAt S rho v c).st.core.toHealing c = some Q := hQ
      rw [hQ'] at hsource'
      cases hwalk : Protocol.deepest_clear (some Q)
          (actionReadAt S rho v c).st.core.toHealing.live_confirmed
          ((NamedProfile.gradeContract (actionReadAt S rho v c).cache).read
            S.E S.hc (actionReadAt S rho v c).st.core.toHealing c).clear with
      | none =>
          simp only [hwalk] at hsource'
          have hCQ : C = Q := (Option.some_inj.mp hsource').symm
          subst C
          rcases voterAnchorAt_cases S rho w d with hfgAnchor |
              ⟨root, A, hframeG1, hactive, hanchor⟩
          · rw [hfgAnchor]
            simp only [Block.compatible, Bool.or_eq_true]
            rw [hvoteRoot]
            exact Or.inl hJC
          ·
              obtain ⟨-, hAG1⟩ := fixedRoot_activeVoterAnchor_g1_data
                S adm hcPos hlo hround hnext hvoteHor hw (by
                  simpa only [Internal.NamedRecoveryRead.voteDutyRead,
                    NamedActionReads.confirmationReadAt,
                    NamedActionReads.confirmationReadFrom,
                    Protocol.NamedStore.setClock, Proofs.Optimistic.slotOf_vote_time,
                    hround] using hframeG1) hactive
              rw [hanchor]
              rcases hsettled v hv Q hQG1 w hw with hQroot | hQactive
              · rcases hsettled w hw A hAG1 w hw with hAroot | hAactive
                · exact Block.compatible_of_preceq_common hAroot hQroot
                · have hrootA := Proofs.Records.preceq_get_fg_root_of_mem_filtered hAactive
                  rw [← actionStoreAt_fgRoot_eq_storeBeforeTime] at hQroot
                  simpa only [Block.compatible, Bool.or_eq_true] using
                    Or.inr (Block.preceq_trans hQroot hrootA)
              · have hQG1w := storeGrade_g1_of_g2_and_targetActionActive
                  S adm hsb hcPos ready hv hw hQG2 (by
                    change Q ∈ Protocol.get_filtered_block_tree
                      (actionStoreAt S rho w c).toHealing.toFG
                    rw [actionStoreAt_filteredTree]
                    exact hQactive)
                exact relativeSeed_sameReaderG1_compatible S rho c w hAG1 hQG1w
      | some B =>
          simp only [hwalk] at hsource'
          have hCB : C = B := (Option.some_inj.mp hsource').symm
          subst B
          have hQC : Block.Preceq Q C := by
            exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hwalk)).2.1
          have hCclear : nodeClear S (actionReadAt S rho v c) c C = true := by
            exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hwalk)).2.2
          rcases voterAnchorAt_cases S rho w d with hfgAnchor |
              ⟨root, A, hframeG1, hactive, hanchor⟩
          · rw [hfgAnchor]
            simp only [Block.compatible, Bool.or_eq_true]
            rw [hvoteRoot]
            exact Or.inl hJC
          ·
              obtain ⟨-, hAG1⟩ := fixedRoot_activeVoterAnchor_g1_data
                S adm hcPos hlo hround hnext hvoteHor hw (by
                  simpa only [Internal.NamedRecoveryRead.voteDutyRead,
                    NamedActionReads.confirmationReadAt,
                    NamedActionReads.confirmationReadFrom,
                    Protocol.NamedStore.setClock, Proofs.Optimistic.slotOf_vote_time,
                    hround] using hframeG1) hactive
              rw [hanchor]
              rcases hsettled w hw A hAG1 v hv with hAroot | hAactive
              · have hrootQ : Block.Preceq
                    (Protocol.get_fg_root
                      (rho.storeBeforeTime S v (S.a c)).toHealing.toFG) Q := by
                  rw [← actionStoreAt_fgRoot_eq_storeBeforeTime]
                  exact Proofs.Records.preceq_get_fg_root_of_mem_filtered
                    (actionQ2_mem_filteredTree S rho v c hQ)
                exact (show Block.compatible A C = true by
                  simp only [Block.compatible, Bool.or_eq_true]
                  exact Or.inl (Block.preceq_trans hAroot
                    (Block.preceq_trans hrootQ hQC)))
              · have hAaction : A ∈ filteredTree (actionReadAt S rho v c) := by
                  change A ∈ Protocol.get_filtered_block_tree
                    (actionStoreAt S rho v c).toHealing.toFG
                  rw [actionStoreAt_filteredTree]
                  exact hAactive
                have hAG0 := storeGrade_g0_of_g1_and_targetActionActive
                  S adm hsb hcPos ready hw hv hAG1 hAaction
                exact relativeG0_compatible_clearSource S adm hcPos hhorC hv hAG0
                  (storeGrade_g0_mem_domainTree S rho hAG0) hAaction hCclear

set_option maxHeartbeats 400000 in
theorem fixedRoot_sourceHeight_le_nextOpeningParent
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {w : V} {read0 : Time}
    {r endpointRound q1 q' : Round} {B1 B2 : NamedBlock V}
    (hfix : FixedHeightJustificationRootAtRead S rho H w read0)
    (hpostRead : S.E.t_GST ≤ read0)
    (hreadAction : read0 ≤ S.a r)
    (hq1lo : r + 3 ≤ q1)
    (hreadAction2 : read0 ≤ S.a q1)
    (hq1pos : 0 < q1) (hq1q2 : q1 < q')
    (hq2End : q' ≤ endpointRound)
    (hcarrier1 : ProposerCarrierAt S rho q1)
    (hpostQ1 : S.E.t_GST ≤ S.a q1)
    (hendHor : S.a endpointRound ≤ rho.horizon)
    (hcapEnd : honestHMaxAt S rho (S.a endpointRound) ≤ H)
    (hplusTwoFacts : ∃ Bplus : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot q1 + 2) = some Bplus ∧
      RunBlock S rho Bplus ∧
      S.E.proposer (S.hc.opening_slot q1 + 2) ∈ rho.honest ∧
      Protocol.proposal_time S.E (S.hc.opening_slot q1 + 2) ≤ rho.horizon ∧
      Protocol.get_fg_root
          (rho.storeBeforeTime S
            (S.E.proposer (S.hc.opening_slot q1 + 2))
            (Protocol.proposal_time S.E
              (S.hc.opening_slot q1 + 2))).toHealing.toFG =
        (rho.storeBeforeTime S w read0).J ∧
      (rho.storeBeforeTime S
        (S.E.proposer (S.hc.opening_slot q1 + 2))
        (Protocol.proposal_time S.E
          (S.hc.opening_slot q1 + 2))).h_max = H)
    (hpacket1 : NamedSGProposalLifecyclePacket S rho (q1 - 1)
      (S.hc.opening_slot q1 - 1) B1)
    (hpacket2 : NamedSGProposalLifecyclePacket S rho (q' - 1)
      (S.hc.opening_slot q' - 1) B2)
    (hB1pred : (Protocol.derive_named S.E S.cfg B1).h = H - 1)
    (hlock1 : SGTargetOpeningConeRootLock S rho H (q1 - 1)
      (S.hc.opening_slot q1 - 1))
    (hlock2 : SGTargetOpeningConeRootLock S rho H (q' - 1)
      (S.hc.opening_slot q' - 1))
    (hfixedAt : ∀ {k : Round}, r + 1 ≤ k → k ≤ endpointRound →
      ∀ v ∈ rho.honest,
        Protocol.get_fg_root
            (rho.storeBeforeTime S v (S.a k)).toHealing.toFG =
          (rho.storeBeforeTime S w read0).J ∧
        (rho.storeBeforeTime S v (S.a k)).h_max = H)
    (hrootDuty2 : Protocol.get_fg_root
        (Protocol.proposerDutyStore S rho
          (S.hc.opening_slot q')).toHealing.toFG =
      (rho.storeBeforeTime S w read0).J)
    (hmaxDuty2 : (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot q')).h_max = H)
    (hformsB1Prev : NamedGradeFormsAt S rho (q' - 1) B1.erase)
    (hactionB1 : ∀ v ∈ rho.honest,
      B1.erase ∈ PhaseGrades.filteredTree
        (actionReadAt S rho v (q' - 1)))
    (hB1ParentRows : Block.Preceq B1.erase B2.parent.erase)
    (hmature2 : ProposalTimeoutMatureAt S rho
      (S.hc.opening_slot q'))
    (hq2Spacing : q1 + 2 + delayExtra ≤ q') :
    ∀ v ∈ rho.honest, ∀ Q : Block V,
      nodeFGSource S (actionReadAt S rho v (q' - 1)) (q' - 1) = some Q →
      ((actionReadAt S rho v (q' - 1)).st.core.toHealing.σ Q).h ≤
        (Protocol.derive_named S.E S.cfg B2.parent).h := by
  intro v hv Q hsource
  obtain ⟨hq'pos, hq'predPos, hq1c, hq1cPred, hq1cMinus,
      hcPredPos⟩ := fixedRootSource_round_bounds_nat hq1lo hq1pos hq1q2
    hq2Spacing
  have hcRound : 0 < q' - 1 := hq'predPos
  have hcPredLt : (q' - 1) - 1 < q' - 1 :=
    Nat.sub_lt hcRound Nat.one_pos
  have hcEnd : q' - 1 ≤ endpointRound :=
    (Nat.sub_le q' 1).trans hq2End
  have hcPredEnd : (q' - 1) - 1 ≤ endpointRound :=
    (Nat.sub_le (q' - 1) 1).trans hcEnd
  have hpostC : S.E.t_GST ≤ S.a (q' - 1) := by
    exact hpostQ1.trans (Assembly.a_mono S (Nat.le_of_lt hq1c))
  have hpostCPred : S.E.t_GST ≤ S.a ((q' - 1) - 1) := by
    exact hpostQ1.trans (Assembly.a_mono S hq1cMinus)
  have hhorC : S.a (q' - 1) ≤ rho.horizon := by
    exact (Assembly.a_mono S hcEnd).trans hendHor
  have hhorCPred : S.a ((q' - 1) - 1) ≤ rho.horizon := by
    exact (Assembly.a_mono S hcPredEnd).trans hendHor
  have hcapC : honestHMaxAt S rho (S.a (q' - 1)) ≤ H := by
    exact (honestHMaxAt_mono S adm.toNamedScheduleWellFormed
      (Assembly.a_mono S hcEnd)).trans hcapEnd
  have hcapCPred : honestHMaxAt S rho (S.a ((q' - 1) - 1)) ≤ H := by
    exact (honestHMaxAt_mono S adm.toNamedScheduleWellFormed
      (Assembly.a_mono S hcPredEnd)).trans hcapEnd
  have hreadDeltaQ1 : read0 + S.E.Δ ≤ S.a q1 := by
    calc
      read0 + S.E.Δ ≤ S.a r + S.E.Δ :=
        Int.add_le_add_right hreadAction S.E.Δ
      _ ≤ Protocol.proposal_time S.E (S.hc.opening_slot q1) :=
        action_add_delta_le_openingProposal_of_round_lt S
          (fixedRootSource_round_lt_of_lower_nat hq1lo)
      _ ≤ S.a q1 := by
        rw [Setup.a, Protocol.a_eq_confirmation_time]
        exact Protocol.proposal_time_le_confirmation_time S.E _
  have hreadDeltaC : read0 + S.E.Δ ≤ S.a (q' - 1) := by
    exact hreadDeltaQ1.trans (Assembly.a_mono S (Nat.le_of_lt hq1c))
  have hreadDeltaCPred : read0 + S.E.Δ ≤ S.a ((q' - 1) - 1) := by
    exact hreadDeltaQ1.trans (Assembly.a_mono S hq1cMinus)
  obtain ⟨Jn, hJnErase, hJnRun, hJnHeight⟩ :=
    fixedRootSource_namedTarget S hfix
  have hrootAction : ∀ z ∈ rho.honest,
      Protocol.get_fg_root
          (actionStoreAt S rho z (q' - 1)).toHealing.toFG = Jn.erase := by
    intro z hz
    rw [actionStoreAt_fgRoot_eq_storeBeforeTime]
    have hr1c : r + 1 ≤ q' - 1 :=
      (Nat.add_le_add_left (by decide : 1 ≤ 3) r).trans
        (hq1lo.trans (Nat.le_of_lt hq1c))
    exact (hfixedAt hr1c hcEnd z hz).1.trans hJnErase.symm
  have hsourceFiltered := fixedRootSource_mem_filtered_actionStore
    S adm v (q' - 1) hsource
  have hJC : Block.Preceq Jn.erase Q := by
    have h := Proofs.Records.preceq_get_fg_root_of_mem_filtered hsourceFiltered
    rw [actionStoreAt_fgRoot_eq_storeBeforeTime,
      (hfixedAt ((Nat.add_le_add_left (by decide : 1 ≤ 3) r).trans
        (hq1lo.trans (Nat.le_of_lt hq1c))) hcEnd v hv).1] at h
    rw [← hJnErase] at h
    exact h
  obtain ⟨Cn, hCbody, hCerase, hCrun, hσ⟩ :=
    fixedRootSource_namedSource_witness S adm hv hsource
  have hJCn : Block.Preceq Jn.erase Cn.erase := by
    rw [hCerase]
    exact hJC
  have hJnCn : NamedBlock.Preceq Jn Cn := by
    obtain ⟨J', hJ'Cn, hJ'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift Cn
      (by simpa only [hCerase] using hJC)
    have hJ'run := Proofs.NamedRuntime.blockInRun_of_ancestor S rho hCrun hJ'Cn
    have hrootEq : J'.root = Jn.root := by
      calc
        J'.root = J'.erase.root := (Proofs.NamedWire.erase_root J').symm
        _ = Jn.erase.root := congrArg Block.root hJ'erase
        _ = (rho.storeBeforeTime S w read0).J.root :=
          congrArg Block.root hJnErase
        _ = Jn.root :=
          (congrArg Block.root hJnErase).symm.trans
            (Proofs.NamedWire.erase_root Jn)
    have hJ'eq := adm.toNamedRootCollisionFree.root_injective J' Jn
      hJ'run hJnRun J' Jn (Or.inl (Proofs.NamedAncestry.named_self J'))
      (Or.inr (Proofs.NamedAncestry.named_self Jn)) hrootEq
    simpa only [hJ'eq] using hJ'Cn
  have hσheight :
      ((actionReadAt S rho v (q' - 1)).st.core.toHealing.σ Q).h =
        (Protocol.derive_named S.E S.cfg Cn).h := by
    exact congrArg (fun X : Protocol.ChainState V => X.h) hσ
  have hB1Lifecycle : NamedRawOpeningLifecycleAt S rho q1 B1 := by
    simpa only [Nat.sub_add_cancel hq1pos] using hpacket1.lifecycle
  have hB2Lifecycle : NamedRawOpeningLifecycleAt S rho q' B2 := by
    simpa only [Nat.sub_add_cancel hq'pos] using hpacket2.lifecycle
  have hB2ParentRun : RunBlock S rho B2.parent :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hB2Lifecycle.runBlock
      (fixedRootSource_parent_preceq_self B2)
  have hB1ParentNamed : NamedBlock.Preceq B1 B2.parent :=
    Protocol.namedPreceq_of_runBlock_erase_preceq adm
      hB1Lifecycle.runBlock hB2ParentRun hB1ParentRows
  have hparentLower : H - 1 ≤
      (Protocol.derive_named S.E S.cfg B2.parent).h := by
    rw [← hB1pred]
    exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hB1ParentNamed
  by_cases hsourceBand : H - 1 ≤
      (Protocol.derive_named S.E S.cfg Cn).h
  · have hsb : SlashableBound S rho :=
      slashableBound_of_admissible_belowOneThird S adm hfb
    have hready : GradeRoundReady S rho (q' - 1) :=
      gradeRoundReady_of_previousAction S hcRound hpostCPred hhorC
    have hactionRootPre : ∀ z ∈ rho.honest,
        Protocol.get_fg_root
            (rho.storeBeforeTime S z (S.a (q' - 1))).toHealing.toFG =
          Jn.erase := by
      intro z hz
      exact (hfixedAt (by
        exact (Nat.add_le_add_left (by decide : 1 ≤ 3) r).trans
          (hq1lo.trans (Nat.le_of_lt hq1c))) hcEnd z hz).1.trans
        hJnErase.symm
    have hsettled : NamedLiveG1SettledAt S rho (q' - 1) :=
      namedLiveG1SettledAt_of_fixedRoot S adm hfb hcRound hfix hpostRead
        hpostCPred hreadDeltaCPred hhorCPred hcapCPred hreadDeltaC hhorC hcapC
    have hlastLo : S.hc.opening_slot (q' - 1) + 1 ≤
        S.hc.opening_slot q' - 1 := by
      unfold Protocol.HealConfig.opening_slot
      have hR := S.hc.R_ge_two
      have hmul : (q' - 1) * S.hc.R + S.hc.R = q' * S.hc.R := by
        calc
          (q' - 1) * S.hc.R + S.hc.R = ((q' - 1) + 1) * S.hc.R := by
            rw [Nat.add_mul]
            simp only [Nat.one_mul, Nat.add_comm]
          _ = q' * S.hc.R := by rw [Nat.sub_add_cancel hq'pos]
      apply Nat.le_sub_of_add_le
      calc
        (q' - 1) * S.hc.R + 1 + 1 =
            (q' - 1) * S.hc.R + (1 + 1) := by rw [Nat.add_assoc]
        _ ≤ (q' - 1) * S.hc.R + S.hc.R :=
          Nat.add_le_add_left S.hc.R_ge_two _
        _ = q' * S.hc.R := hmul
    have hlastLt : S.hc.opening_slot q' - 1 <
        S.hc.opening_slot q' := by
      have hq'openPos : 0 < S.hc.opening_slot q' := by
        unfold Protocol.HealConfig.opening_slot
        exact Nat.mul_pos hq'pos
          (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
      exact Nat.sub_lt hq'openPos Nat.one_pos
    have hlastPos : 0 < S.hc.opening_slot q' - 1 := by
      have hopenPos : 0 < S.hc.opening_slot (q' - 1) := by
        unfold Protocol.HealConfig.opening_slot
        exact Nat.mul_pos hcRound
          (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
      exact lt_of_lt_of_le hopenPos
        ((Nat.le_succ _).trans hlastLo)
    have hhorQ' : S.a q' ≤ rho.horizon :=
      (Assembly.a_mono S hq2End).trans hendHor
    have hproposalHor : Protocol.proposal_time S.E
        (S.hc.opening_slot q') ≤ rho.horizon := by
      exact (by
        rw [Setup.a, Protocol.a_eq_confirmation_time] at hhorQ'
        exact (Protocol.proposal_time_le_confirmation_time S.E _).trans hhorQ')
    have hsourceVoteDelay : ∀ {d : Slot},
        S.hc.opening_slot (q' - 1) + 1 ≤ d →
        d ≤ S.hc.opening_slot q' - 1 →
        read0 + S.E.Δ ≤ Protocol.vote_time S.E d := by
      intro d hdlo hdhi
      have hq1ToC : S.a q1 + S.E.Δ ≤
          Protocol.proposal_time S.E (S.hc.opening_slot (q' - 1)) :=
        action_add_delta_le_openingProposal_of_round_lt S hq1c
      have hpropToFirst : Protocol.proposal_time S.E
          (S.hc.opening_slot (q' - 1)) ≤
          Protocol.vote_time S.E
            (S.hc.opening_slot (q' - 1) + 1) :=
        (Protocol.proposal_time_lt_vote_time S.E
          (S.hc.opening_slot (q' - 1))).le.trans
          (Protocol.vote_time_mono_slots S.E (Nat.le_succ _))
      calc
        read0 + S.E.Δ ≤ S.a q1 + S.E.Δ :=
          Int.add_le_add_right hreadAction2 S.E.Δ
        _ ≤ Protocol.proposal_time S.E
            (S.hc.opening_slot (q' - 1)) := hq1ToC
        _ ≤ Protocol.vote_time S.E
            (S.hc.opening_slot (q' - 1) + 1) := hpropToFirst
        _ ≤ Protocol.vote_time S.E d :=
          Protocol.vote_time_mono_slots S.E hdlo
    have hsourceVoteFacts : ∀ {d : Slot},
        S.hc.opening_slot (q' - 1) + 1 ≤ d →
        d ≤ S.hc.opening_slot q' - 1 →
        ∀ z ∈ rho.honest,
        Protocol.get_fg_root
            (Internal.NamedRecoveryRead.voteDutyRead S rho z d).st.core.toHealing.toFG =
          Jn.erase ∧
        (Internal.NamedRecoveryRead.voteDutyRead S rho z d).st.core.h_max = H := by
      intro d hdlo hdhi z hz
      have hvoteHor : Protocol.vote_time S.E d ≤ rho.horizon := by
        calc
          Protocol.vote_time S.E d ≤ Protocol.confirmation_time S.E d :=
            Protocol.vote_time_le_confirmation_time S.E d
          _ ≤ Protocol.confirmation_time S.E
              (S.hc.opening_slot q' - 1) :=
            fixedRootSource_confirmation_time_mono S.E
              hdhi
          _ ≤ Protocol.confirmation_time S.E
              (S.hc.opening_slot q') :=
            fixedRootSource_confirmation_time_mono S.E
              (Nat.le_of_lt hlastLt)
          _ = S.a q' := by
            rw [Setup.a, Protocol.a_eq_confirmation_time]
          _ ≤ S.a endpointRound := Assembly.a_mono S hq2End
          _ ≤ rho.horizon := hendHor
      have hvoteEnd : Protocol.vote_time S.E d ≤
          S.a endpointRound := by
        calc
          Protocol.vote_time S.E d ≤ Protocol.confirmation_time S.E d :=
            Protocol.vote_time_le_confirmation_time S.E d
          _ ≤ Protocol.confirmation_time S.E
              (S.hc.opening_slot q') :=
            (fixedRootSource_confirmation_time_mono S.E
              (hdhi.trans (Nat.le_of_lt hlastLt)))
          _ = S.a q' := by
            rw [Setup.a, Protocol.a_eq_confirmation_time]
          _ ≤ S.a endpointRound := Assembly.a_mono S hq2End
      have hvoteCap : honestHMaxAt S rho
          (Protocol.vote_time S.E d) ≤ H :=
        (honestHMaxAt_mono S adm.toNamedScheduleWellFormed hvoteEnd).trans
          hcapEnd
      have hfixed :=
        fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
          S adm hsb hfix hz hpostRead (hsourceVoteDelay hdlo hdhi) hvoteHor
            hvoteCap
      constructor
      · rw [fixedRootSource_voteDutyRead_fgRoot_eq_storeBeforeTime]
        exact hfixed.1.trans hJnErase.symm
      · rw [fixedRootSource_voteDutyRead_hMax_eq_storeBeforeTime]
        exact hfixed.2
    have hhorQ'c : S.a ((q' - 1) + 1) ≤ rho.horizon := by
      simpa only [Nat.sub_add_cancel hq'pos] using hhorQ'
    have hlastSeed : ∀ {d : Slot},
        d ≤ S.hc.opening_slot q' - 1 →
        d ≤ seedRoundLastSlot S (q' - 1) := by
      intro d hd
      simpa only [seedRoundLastSlot, Nat.sub_add_cancel hq'pos] using hd
    have hsourceAnchorCompat : ∀ {d : Slot},
        S.hc.opening_slot (q' - 1) + 1 ≤ d →
        d ≤ S.hc.opening_slot q' - 1 →
        ∀ z ∈ rho.honest,
        Block.compatible (voterAnchorAt S rho z d) Q = true := by
      intro d hdlo hdhi z hz
      exact preparedAnchor_compatible_freshFGSource_of_fixedRoot S adm hfb
        (c := q' - 1) (by exact Nat.succ_le_iff.mpr hcRound)
        hactionRootPre hsettled hhorQ'c hready hz hv
        hdlo (by exact hlastSeed hdhi)
        (seedEntryRoundOf S hdlo (hlastSeed hdhi))
        (hsourceVoteFacts hdlo hdhi z hz).1 hsource
    have hsourceVoteHor : ∀ {d : Slot},
        S.hc.opening_slot (q' - 1) + 1 ≤ d →
        d ≤ S.hc.opening_slot q' - 1 →
        Protocol.vote_time S.E d ≤ rho.horizon := by
      intro d hdlo hdhi
      calc
        Protocol.vote_time S.E d ≤ Protocol.confirmation_time S.E d :=
          Protocol.vote_time_le_confirmation_time S.E d
        _ ≤ Protocol.confirmation_time S.E
            (S.hc.opening_slot q') :=
          fixedRootSource_confirmation_time_mono S.E
            (hdhi.trans hlastLt.le)
        _ = S.a q' := by
          rw [Setup.a, Protocol.a_eq_confirmation_time]
        _ ≤ S.a endpointRound := Assembly.a_mono S hq2End
        _ ≤ rho.horizon := hendHor
    have hsourceConfHor : ∀ {d : Slot},
        S.hc.opening_slot (q' - 1) + 1 ≤ d →
        d ≤ S.hc.opening_slot q' - 1 →
        Protocol.confirmation_time S.E d ≤ rho.horizon := by
      intro d hdlo hdhi
      calc
        Protocol.confirmation_time S.E d ≤
            Protocol.confirmation_time S.E (S.hc.opening_slot q') :=
          fixedRootSource_confirmation_time_mono S.E
            (hdhi.trans hlastLt.le)
        _ = S.a q' := by
          rw [Setup.a, Protocol.a_eq_confirmation_time]
        _ ≤ S.a endpointRound := Assembly.a_mono S hq2End
        _ ≤ rho.horizon := hendHor
    have hpostSource : S.E.t_GST ≤
        Protocol.proposal_time S.E (S.hc.opening_slot (q' - 1)) := by
      exact hpostCPred.trans
        ((le_add_of_nonneg_right S.E.Δ_pos.le).trans
          (action_add_delta_le_openingProposal_of_round_lt S hcPredLt))
    have hsourceHor : Protocol.confirmation_time S.E
        (S.hc.opening_slot (q' - 1)) ≤ rho.horizon := by
      calc
        Protocol.confirmation_time S.E
            (S.hc.opening_slot (q' - 1)) = S.a (q' - 1) := by
              rw [Setup.a, Protocol.a_eq_confirmation_time]
        _ ≤ rho.horizon := hhorC
    have hsourceVoteHor' : ∀ {d : Slot},
        S.hc.opening_slot (q' - 1) + 1 ≤ d →
        d ≤ S.hc.opening_slot q' - 1 →
        Protocol.vote_time S.E d ≤ rho.horizon := hsourceVoteHor
    have hsourceConfHor' : ∀ {d : Slot},
        S.hc.opening_slot (q' - 1) + 1 ≤ d →
        d ≤ S.hc.opening_slot q' - 1 →
        Protocol.confirmation_time S.E d ≤ rho.horizon := hsourceConfHor
    have hloLast : S.hc.opening_slot (q' - 1) + 1 ≤
        S.hc.opening_slot q' - 1 := hlastLo
    have hpostLo : S.E.t_GST ≤ Protocol.vote_time S.E
        (S.hc.opening_slot (q' - 1) + 1) := by
      exact hpostSource.trans
        ((Protocol.proposal_time_lt_vote_time S.E
          (S.hc.opening_slot (q' - 1))).le.trans
          (Protocol.vote_time_mono_slots S.E (Nat.le_succ _)))
    have hsourceCone : NamedHonestVotesCone S rho
        (S.hc.opening_slot q' - 1) (fun X => Block.Preceq Q X) := by
      cases hQ2 : nodeQ2 S (actionReadAt S rho v (q' - 1)) (q' - 1) with
      | none =>
          have hbad := hsource
          simp only [nodeFGSource, nodeQ2, nodeRead] at hbad hQ2
          unfold Protocol.grade2_block_with at hbad
          rw [hQ2] at hbad
          simp [Protocol.fg_source_with] at hbad
      | some Q2 =>
          have hQ2' : Protocol.grade2_block_with
              (NamedProfile.gradeContract
                (actionReadAt S rho v (q' - 1)).cache)
              S.E S.hc
              (actionReadAt S rho v (q' - 1)).st.core.toHealing (q' - 1) =
              some Q2 := hQ2
          have hsource' := hsource
          rw [nodeFGSource, Protocol.fg_source_with.eq_def, hQ2'] at hsource'
          cases hwalk : Protocol.deepest_clear (some Q2)
              (actionReadAt S rho v (q' - 1)).st.core.toHealing.live_confirmed
              ((NamedProfile.gradeContract
                (actionReadAt S rho v (q' - 1)).cache).read
                S.E S.hc
                (actionReadAt S rho v (q' - 1)).st.core.toHealing
                (q' - 1)).clear with
          | none =>
              simp only [hwalk] at hsource'
              have hCQ : Q = Q2 := (Option.some_inj.mp hsource').symm
              have hQtarget : Block.Preceq Q2
                  (actionSGBlockAt S rho v (q' - 1)) :=
                preceq_actionSGBlockAt_of_actionQ2
                  S adm.toNamedAdmissibleCore hv hcRound hhorC hQ2
                    (Block.preceq_self Q2)
              intro x hx hcommittee
              obtain ⟨X, hTX, hXrun, hXemit⟩ :=
                hlock2.canonical v hv x hx hcommittee
              exact ⟨X, by rw [hCQ]; exact Block.preceq_trans hQtarget hTX,
                hXrun, hXemit⟩
          | some Cclear =>
              simp only [hwalk] at hsource'
              have hCQ : Q = Cclear := (Option.some_inj.mp hsource').symm
              have hCL : Block.Preceq Cclear
                  (actionReadAt S rho v (q' - 1)).st.core.live_confirmed :=
                Proofs.Engine.deepest_clear_preceq hwalk
              have hCeraseClear : Cn.erase = Cclear := hCerase.trans hCQ
              have hJCclear : Block.Preceq Jn.erase Cclear := by
                rw [← hCeraseClear]
                exact hJCn
              have hsourceAnchorCompatClear : ∀ {d : Slot},
                  S.hc.opening_slot (q' - 1) + 1 ≤ d →
                  d ≤ S.hc.opening_slot q' - 1 →
                  ∀ z ∈ rho.honest,
                  Block.compatible (voterAnchorAt S rho z d) Cclear = true := by
                intro d hdlo hdhi z hz
                simpa only [hCQ] using
                  hsourceAnchorCompat hdlo hdhi z hz
              rcases actionStoreAt_liveConfirmed_genuine_or_fgRoot
                  S rho v (q' - 1) with
                ⟨L, hgenuine, hLlive⟩ | ⟨R, hRroot, hRlive⟩
              · have hCLive : Block.Preceq Cclear L := by
                  rw [hLlive]
                  exact hCL
                have hfirstCone : NamedHonestVotesCone S rho
                    (S.hc.opening_slot (q' - 1) + 1)
                    (fun X => Block.Preceq Cclear X) := by
                  intro x hx hcommittee
                  have hrootL : Block.Preceq
                      (Protocol.get_fg_root
                        (Internal.NamedRecoveryRead.voteDutyRead S rho x
                          (S.hc.opening_slot (q' - 1) + 1)).st.core.toHealing.toFG) L := by
                    rw [(hsourceVoteFacts (d :=
                      S.hc.opening_slot (q' - 1) + 1) (le_refl _) hloLast x hx).1]
                    exact Block.preceq_trans hJCclear hCLive
                  have hLprocessed :=
                    Protocol.voterProcessedTarget_of_genuineConfirmation_after_gst
                      S adm hv hx hpostSource hsourceHor
                      (⟨hgenuine.selected, hgenuine.genuine⟩) hrootL
                  have hCprocessed :=
                    WeakGoldfish.ancestorProcessed_of_voterProcessed
                      S adm.toNamedAdmissibleCore hx hLprocessed Cclear hCLive
                  have hCprocessedNamed : Cn.erase ∈
                      Protocol.voter_processed_block_tree S.E
                        (Proofs.Optimistic.voteDutyStore S rho x
                          (S.hc.opening_slot (q' - 1) + 1)).toHealing.toFG.toSG.toGoldfishStore
                        (Proofs.Optimistic.voteDutyStore S rho x
                          (S.hc.opening_slot (q' - 1) + 1)).toHealing.s := by
                    rw [hCeraseClear]
                    exact hCprocessed
                  have hcapFirst :
                      (Internal.NamedRecoveryRead.voteDutyRead S rho x
                        (S.hc.opening_slot (q' - 1) + 1)).st.core.h_max ≤
                        (Protocol.derive_named S.E S.cfg Jn).h + 1 := by
                    rw [(hsourceVoteFacts (d :=
                      S.hc.opening_slot (q' - 1) + 1) (le_refl _) hloLast x hx).2,
                      hJnHeight]
                    exact Nat.le_of_eq (Nat.sub_add_cancel
                      (Nat.le_of_lt (Nat.sub_pos_iff_lt.mp
                        hfix.targetHeightPositive))).symm
                  obtain ⟨hcandidate, hpath⟩ := fixedRoot_targetCandidateAndPath
                    S adm hJnRun hCrun hJCn hx
                    (Nat.zero_lt_succ _)
                    (hsourceVoteFacts (d :=
                      S.hc.opening_slot (q' - 1) + 1) (le_refl _) hloLast x hx).1
                    hcapFirst hCprocessedNamed
                  have hcandidateClear : Cclear ∈
                      voterCandidateTreeAt S rho x
                        (S.hc.opening_slot (q' - 1) + 1) := by
                    simpa only [hCeraseClear] using hcandidate
                  have hpathClear : ∀ D : Block V,
                      Block.Preceq
                          (voterAnchorAt S rho x
                            (S.hc.opening_slot (q' - 1) + 1)) D →
                      D ≠ voterAnchorAt S rho x
                        (S.hc.opening_slot (q' - 1) + 1) →
                      Block.Preceq D Cclear → D ≠ Cclear →
                      D ∈ voterCandidateTreeAt S rho x
                        (S.hc.opening_slot (q' - 1) + 1) := by
                    simpa only [hCeraseClear] using hpath
                  have hanchorCompat := hsourceAnchorCompatClear
                    (d := S.hc.opening_slot (q' - 1) + 1)
                    (le_refl _) hloLast x hx
                  have hhead : Block.Preceq Cclear
                      (voterHeadAt S rho x
                        (S.hc.opening_slot (q' - 1) + 1)) := by
                    simp only [Block.compatible, Bool.or_eq_true] at hanchorCompat
                    rcases hanchorCompat with hanchorC | hCanchor
                    · have hanchor' : Block.Preceq
                          (Protocol.get_sg_root_with
                            (NamedProfile.gradeContract
                              (Internal.NamedRecoveryRead.voteDutyRead S rho x
                                (S.hc.opening_slot (q' - 1) + 1)).cache)
                            S.E S.hc
                            (Internal.NamedRecoveryRead.voteDutyRead S rho x
                          (S.hc.opening_slot (q' - 1) + 1)).st.core.toHealing
                            (S.hc.round_of
                              (Internal.NamedRecoveryRead.voteDutyRead S rho x
                                (S.hc.opening_slot (q' - 1) + 1)).st.core.s)) Cclear := by
                        simpa only [voterAnchorAt, PhaseGrades.nodeAnchor,
                          PhaseGrades.nodeRead] using hanchorC
                      have hanchor'' : Block.Preceq
                          (Protocol.get_sg_root_with
                            (NamedProfile.gradeContract
                              (NamedActionReads.confirmationReadFrom S
                                (Run.stateBeforeTime S rho
                                  (Protocol.vote_time S.E
                                    (S.hc.opening_slot (q' - 1) + 1)) x)
                                (Protocol.vote_time S.E
                                  (S.hc.opening_slot (q' - 1) + 1))).cache)
                            S.E S.hc
                            (NamedActionReads.confirmationReadFrom S
                              (Run.stateBeforeTime S rho
                                (Protocol.vote_time S.E
                                  (S.hc.opening_slot (q' - 1) + 1)) x)
                                (Protocol.vote_time S.E
                                  (S.hc.opening_slot (q' - 1) + 1))).st.core.toHealing
                            (S.hc.round_of
                              (NamedActionReads.confirmationReadFrom S
                                (Run.stateBeforeTime S rho
                                  (Protocol.vote_time S.E
                                    (S.hc.opening_slot (q' - 1) + 1)) x)
                                (Protocol.vote_time S.E
                          (S.hc.opening_slot (q' - 1) + 1))).st.core.s)) Cclear := by
                        simpa only [Internal.NamedRecoveryRead.voteDutyRead,
                          NamedActionReads.confirmationReadAt] using hanchor'
                      have hadopt := nextVoteAdoption_of_frozenCandidateAtRead
                        (s := S.hc.opening_slot (q' - 1)) (D := Cclear)
                        S adm hv hpostSource hsourceHor hx hcandidateClear hanchor''
                      exact fixedRootSource_preceq_voterHeadAt_of_adoption S
                        (fixedRootSource_ancestorConfirmation_eligible S.E S.hc
                          (Proofs.Optimistic.confStore S rho v
                            (S.hc.opening_slot (q' - 1)))
                          (S.hc.opening_slot (q' - 1)) hCLive hgenuine) hadopt
                    · exact Block.preceq_trans hCanchor
                        (voterAnchorAt_preceq_voterHeadAt S rho x
                          (S.hc.opening_slot (q' - 1) + 1))
                  obtain ⟨X, hXhead, hXrun, hXemit⟩ := named_voter_head_emits
                    S adm hx (Nat.succ_pos (S.hc.opening_slot (q' - 1)))
                    hcommittee
                    (hsourceVoteHor' (d :=
                      S.hc.opening_slot (q' - 1) + 1) (le_refl _) hloLast)
                  exact ⟨X, by rw [hXhead]; exact hhead, hXrun, hXemit⟩
                have hconeAt : ∀ k : Slot,
                    S.hc.opening_slot (q' - 1) + 1 ≤ k →
                    k ≤ S.hc.opening_slot q' - 1 →
                    NamedHonestVotesCone S rho k
                      (fun X => Block.Preceq Cclear X) := by
                  intro k hklo
                  induction k, hklo using Nat.le_induction with
                  | base =>
                      intro _
                      exact hfirstCone
                  | succ k hk ih =>
                      intro hsuccLast
                      have hkLast : k ≤ S.hc.opening_slot q' - 1 :=
                        (Nat.le_succ k).trans hsuccLast
                      have hprev := ih hkLast
                      have hkPos : 0 < k :=
                        (Nat.zero_lt_succ (S.hc.opening_slot (q' - 1))).trans_le hk
                      have hdlo : S.hc.opening_slot (q' - 1) + 1 ≤ k + 1 :=
                        hk.trans (Nat.le_succ k)
                      have hdhi : k + 1 ≤ S.hc.opening_slot q' - 1 := hsuccLast
                      intro x hx hcommittee
                      have hrootL : Block.Preceq
                          (Protocol.get_fg_root
                            (Internal.NamedRecoveryRead.voteDutyRead S rho x
                              (k + 1)).st.core.toHealing.toFG) L := by
                        rw [(hsourceVoteFacts hdlo hdhi x hx).1]
                        exact Block.preceq_trans hJCclear hCLive
                      have hLprocessed :=
                        voterProcessedTarget_of_genuineConfirmation_at_laterVoteDuty_after_gst
                          (source := S.hc.opening_slot (q' - 1)) (k := k) (B := L)
                          S adm hv hx hk hpostSource
                          (hsourceVoteHor' hdlo hdhi)
                          (⟨hgenuine.selected, hgenuine.genuine⟩) hrootL
                      have hCprocessed :=
                        WeakGoldfish.ancestorProcessed_of_voterProcessed
                          S adm.toNamedAdmissibleCore hx hLprocessed Cclear hCLive
                      have hCprocessedNamed : Cn.erase ∈
                          Protocol.voter_processed_block_tree S.E
                            (Proofs.Optimistic.voteDutyStore S rho x (k + 1)).toHealing.toFG.toSG.toGoldfishStore
                            (Proofs.Optimistic.voteDutyStore S rho x (k + 1)).toHealing.s := by
                        rw [hCeraseClear]
                        exact hCprocessed
                      have hcapDuty :
                          (Internal.NamedRecoveryRead.voteDutyRead S rho x
                            (k + 1)).st.core.h_max ≤
                            (Protocol.derive_named S.E S.cfg Jn).h + 1 := by
                        rw [(hsourceVoteFacts hdlo hdhi x hx).2, hJnHeight]
                        exact Nat.le_of_eq (Nat.sub_add_cancel
                          (Nat.le_of_lt (Nat.sub_pos_iff_lt.mp
                            hfix.targetHeightPositive))).symm
                      obtain ⟨hcandidate, hpath⟩ := fixedRoot_targetCandidateAndPath
                        S adm hJnRun hCrun hJCn hx (Nat.zero_lt_succ _)
                        (hsourceVoteFacts hdlo hdhi x hx).1 hcapDuty hCprocessedNamed
                      have hcandidateClear : Cclear ∈
                          voterCandidateTreeAt S rho x (k + 1) := by
                        simpa only [hCeraseClear] using hcandidate
                      have hpathClear : ∀ D : Block V,
                          Block.Preceq
                              (voterAnchorAt S rho x (k + 1)) D →
                          D ≠ voterAnchorAt S rho x (k + 1) →
                          Block.Preceq D Cclear → D ≠ Cclear →
                          D ∈ voterCandidateTreeAt S rho x (k + 1) := by
                        simpa only [hCeraseClear] using hpath
                      have hrootDutyClear : Block.Preceq
                          (Protocol.get_fg_root
                            (Internal.NamedRecoveryRead.voteDutyRead S rho x
                              (k + 1)).st.core.toHealing.toFG) Cclear := by
                        rw [(hsourceVoteFacts hdlo hdhi x hx).1]
                        exact hJCclear
                      have hanchorCompat := hsourceAnchorCompatClear hdlo hdhi x hx
                      have hinputs : GoldfishConeVoteInputs' S rho k Cclear x :=
                        { rootSide := Or.inl
                            ⟨hrootDutyClear, hcandidateClear, hpathClear⟩
                          anchor := hanchorCompat }
                      have hpostK : S.E.t_GST ≤ Protocol.vote_time S.E k :=
                        hpostLo.trans (Protocol.vote_time_mono_slots S.E hk)
                      have hhead := goldfishCone_step' S adm hcom hkPos hpostK
                        (hsourceConfHor' hk hkLast) hprev hx hinputs
                      obtain ⟨X, hXhead, hXrun, hXemit⟩ := named_voter_head_emits
                        S adm hx (Nat.succ_pos k) hcommittee
                        (hsourceVoteHor' hdlo hdhi)
                      exact ⟨X, by rw [hXhead]; exact hhead, hXrun, hXemit⟩
                simpa only [hCQ] using
                  hconeAt (S.hc.opening_slot q' - 1) hloLast le_rfl
              · have hCLroot : Block.Preceq Cclear R := by
                  rw [hRlive]
                  exact hCL
                have hconfRoot : Protocol.get_fg_root
                    (Proofs.Optimistic.confStore S rho v
                      (S.hc.opening_slot (q' - 1))).toHealing.toFG =
                    Jn.erase := by
                  rw [← actionStoreAt_fgRoot_eq_openingConfStore,
                    actionStoreAt_fgRoot_eq_storeBeforeTime]
                  exact hactionRootPre v hv
                have hRJ : R = Jn.erase := by
                  rw [hRroot, hconfRoot]
                have hCeq : Cclear = Jn.erase :=
                  Block.preceq_antisymm
                    (by simpa only [hRJ] using hCLroot) hJCclear
                intro x hx hcommittee
                obtain ⟨X, hXhead, hXrun, hXemit⟩ := named_voter_head_emits
                  S adm hx hlastPos
                  hcommittee
                  (hsourceVoteHor' (d := S.hc.opening_slot q' - 1)
                    (by exact hloLast) le_rfl)
                have hrootAnchor : Block.Preceq
                    (Protocol.get_fg_root
                      (Internal.NamedRecoveryRead.voteDutyRead S rho x
                        (S.hc.opening_slot q' - 1)).st.core.toHealing.toFG)
                    (voterAnchorAt S rho x (S.hc.opening_slot q' - 1)) :=
                  NamedOutageClosure.fg_root_preceq_anchor S.E S.hc
                    (Internal.NamedRecoveryRead.voteDutyRead S rho x
                      (S.hc.opening_slot q' - 1)).st.core.toHealing
                    (S.hc.round_of
                      (Internal.NamedRecoveryRead.voteDutyRead S rho x
                        (S.hc.opening_slot q' - 1)).st.core.s)
                    (DecoupledConsensusModel.Protocol.readFrame
                      (Internal.NamedRecoveryRead.voteDutyRead S rho x
                        (S.hc.opening_slot q' - 1)).cache
                      (Internal.NamedRecoveryRead.voteDutyRead S rho x
                        (S.hc.opening_slot q' - 1)).st.core.toHealing
                      (S.hc.round_of
                        (Internal.NamedRecoveryRead.voteDutyRead S rho x
                          (S.hc.opening_slot q' - 1)).st.core.s)).g1
                have hJanchor : Block.Preceq Jn.erase
                    (voterAnchorAt S rho x (S.hc.opening_slot q' - 1)) := by
                  rw [← (hsourceVoteFacts (d := S.hc.opening_slot q' - 1)
                    hloLast le_rfl x hx).1]
                  exact hrootAnchor
                have hJhead : Block.Preceq Jn.erase
                    (voterHeadAt S rho x (S.hc.opening_slot q' - 1)) :=
                  Block.preceq_trans hJanchor
                    (voterAnchorAt_preceq_voterHeadAt S rho x
                      (S.hc.opening_slot q' - 1))
                exact ⟨X, by rw [hXhead, hCQ, hCeq]; exact hJhead,
                  hXrun, hXemit⟩
    have hsourceBodyAction : Cn ∈
        (actionStoreAt S rho v (q' - 1)).st.bodies := by
      exact hCbody
    have hsourceDelayProposal : S.a (q' - 1) + S.E.Δ ≤
        Protocol.proposal_time S.E (S.hc.opening_slot q') :=
      action_add_delta_le_openingProposal_of_round_lt S
        (Nat.sub_lt hq'pos Nat.one_pos)
    have hrootPre : Protocol.get_fg_root
        (rho.storeBeforeTime S (S.E.proposer (S.hc.opening_slot q'))
          (Protocol.proposal_time S.E (S.hc.opening_slot q'))).toHealing.toFG =
        Jn.erase := by
      have hrootDuty : Protocol.get_fg_root
          (Protocol.proposerDutyStore S rho
            (S.hc.opening_slot q')).toHealing.toFG = Jn.erase :=
        hrootDuty2.trans hJnErase.symm
      have hrootTick : Protocol.get_fg_root
          (Proofs.Optimistic.tickStore S
            (rho.storeBeforeTime S (S.E.proposer (S.hc.opening_slot q'))
              (Protocol.proposal_time S.E
                (S.hc.opening_slot q'))).core
            (Protocol.proposal_time S.E (S.hc.opening_slot q'))).toHealing.toFG =
          Jn.erase := by
        simpa only [Protocol.proposerDutyStore] using hrootDuty
      simpa only [Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hrootTick
    have hrootProposalJ : Block.Preceq
        (Protocol.get_fg_root
          (proposerReadAt S rho (S.hc.opening_slot q')).st.core.toHealing.toFG)
        Jn.erase := by
      have hrootNamedEq : Protocol.get_fg_root
          (proposerReadAt S rho (S.hc.opening_slot q')).st.core.toHealing.toFG =
          Protocol.get_fg_root
            (rho.storeBeforeTime S (S.E.proposer (S.hc.opening_slot q'))
              (Protocol.proposal_time S.E
                (S.hc.opening_slot q'))).toHealing.toFG := by
        unfold proposerReadAt NamedActionReads.confirmationReadAt
        unfold Protocol.get_fg_root
        rfl
      rw [hrootNamedEq.trans hrootPre]
      exact Block.preceq_self _
    have hrootProposalPre : Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S (S.E.proposer (S.hc.opening_slot q'))
            (Protocol.proposal_time S.E
              (S.hc.opening_slot q'))).toHealing.toFG) Jn.erase :=
      by
        rw [hrootPre]
        exact Block.preceq_self _
    have hvisible := actionConeWitness_visibleAtReader_after_gst
      S adm hv hB2Lifecycle.proposerHonest hsourceBodyAction hJCn
        hsourceBand hpostC hsourceDelayProposal hproposalHor hrootProposalPre
    have hmaxProposal :
        (rho.storeBeforeTime S (S.E.proposer (S.hc.opening_slot q'))
          (Protocol.proposal_time S.E (S.hc.opening_slot q'))).h_max = H := by
      simpa only [Protocol.proposerDutyStore, Proofs.Optimistic.tickStore] using
        hmaxDuty2
    have hcapProposal :
        (rho.storeBeforeTime S (S.E.proposer (S.hc.opening_slot q'))
          (Protocol.proposal_time S.E (S.hc.opening_slot q'))).h_max ≤
          (Protocol.derive_named S.E S.cfg Cn).h + 1 := by
      rw [hmaxProposal]
      exact Nat.sub_le_iff_le_add.mp hsourceBand
    have hactiveSource : Cn.erase ∈
        Protocol.get_filtered_block_tree
          (rho.storeBeforeTime S (S.E.proposer (S.hc.opening_slot q'))
            (Protocol.proposal_time S.E
              (S.hc.opening_slot q'))).toHealing.toFG :=
      mem_filtered_of_mem_tree_of_exactFGRoot_heightCap S rho
        (S.E.proposer (S.hc.opening_slot q'))
        (Protocol.proposal_time S.E (S.hc.opening_slot q')) hvisible.1
        rfl hrootPre hvisible.2.1 hcapProposal
    have hactiveQ : Q ∈
        Protocol.get_filtered_block_tree
          (Protocol.proposerDutyStore S rho
            (S.hc.opening_slot q')).toHealing.toFG := by
      simpa only [Protocol.proposerDutyStore, proposerReadAt,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.tickStore, hCerase] using hactiveSource
    obtain ⟨K, ⟨v0, hv0, hKeq⟩, hupperK, hKcone⟩ :=
      fixedRootSource_commonActionCeiling S adm hcom (H := H) (q := q' - 1)
        (by simpa only [Nat.sub_add_cancel hq'pos] using hlock2)
    have hKcone' : NamedHonestVotesCone S rho
        (S.hc.opening_slot q' - 1) (fun X => Block.Preceq K X) := by
      simpa only [Nat.sub_add_cancel hq'pos] using hKcone
    have hJK : Block.Preceq Jn.erase K := by
      have h := Proofs.Records.preceq_get_fg_root_of_mem_filtered
        (actionSGBlockAt_mem_filtered_actionStore S adm v0 (q' - 1))
      rw [actionStoreAt_fgRoot_eq_storeBeforeTime, hactionRootPre v0 hv0,
        ← hKeq] at h
      exact h
    have hKC : Block.compatible K Q = true :=
      sgTargetCompatible_of_honestVotesCone S hcom
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
        adm.toNamedAdmissibleCore.toNamedRootCollisionFree hKcone' hsourceCone
    have hcut : S.hc.Γ_neg1 S.E.Δ ((q' - 1) + 1) ≤ rho.horizon :=
      (next_Γ_neg1_lt_action S (q' - 1)).le.trans hhorQ'c
    have hopenQ'pos : 0 < S.hc.opening_slot q' :=
      lt_of_le_of_lt (Nat.zero_le _) hlastLt
    have hlastSucc : S.hc.opening_slot q' - 1 + 1 =
        S.hc.opening_slot q' := Nat.sub_add_cancel hopenQ'pos
    have hrootProposalK : Block.Preceq
        (Protocol.get_fg_root
          (proposerReadAt S rho (S.hc.opening_slot q')).st.core.toHealing.toFG)
        K := Block.preceq_trans hrootProposalJ hJK
    have hproposalHor' : Protocol.proposal_time S.E
        (S.hc.opening_slot (q' - 1 + 1)) ≤ rho.horizon := by
      simpa only [Nat.sub_add_cancel hq'pos] using hproposalHor
    have hproposerHonest' : S.E.proposer
        (S.hc.opening_slot (q' - 1 + 1)) ∈ rho.honest := by
      simpa only [Nat.sub_add_cancel hq'pos] using
        hB2Lifecycle.proposerHonest
    have hrootProposalK' : Block.Preceq
        (Protocol.get_fg_root
          (proposerReadAt S rho
            (S.hc.opening_slot (q' - 1 + 1))).st.core.toHealing.toFG) K := by
      simpa only [Nat.sub_add_cancel hq'pos] using hrootProposalK
    have hanchorK := fixedRootSource_proposalAnchor_preceq_of_previousCarriers
      S adm hfb hpostC hcut hproposalHor' hupperK
        hproposerHonest' hrootProposalK'
    have hanchorCompat := fixedRootSource_compatible_left hanchorK hKC
    have hroundProposal : S.hc.round_of
        (Internal.NamedRecoveryRead.proposalDutyRead S rho
          (S.hc.opening_slot q')).st.core.s = q' := by
      simpa only [Internal.NamedRecoveryRead.proposalDutyRead, proposerReadAt,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.slotOf_proposal_time] using
        round_of_opening_slot_eq_schedule S.hc q'
    have hanchorCompat' : Block.compatible
        (nodeAnchor S (Internal.NamedRecoveryRead.proposalDutyRead S rho
          (S.hc.opening_slot q'))
          (S.hc.round_of
            (Internal.NamedRecoveryRead.proposalDutyRead S rho
              (S.hc.opening_slot q')).st.core.s)) Q = true := by
      rw [hroundProposal]
      simpa only [Nat.sub_add_cancel hq'pos] using hanchorCompat
    have hpostLast : S.E.t_GST ≤ Protocol.vote_time S.E
        (S.hc.opening_slot q' - 1) := by
      exact hpostSource.trans
        ((Protocol.proposal_time_lt_vote_time S.E
          (S.hc.opening_slot (q' - 1))).le.trans
          (Protocol.vote_time_mono_slots S.E
            ((Nat.le_succ _).trans hloLast)))
    have hsupportHor : Protocol.support_cutoff S.E
        (S.hc.opening_slot q' - 1) ≤ rho.horizon := by
      calc
        Protocol.support_cutoff S.E (S.hc.opening_slot q' - 1) ≤
            Protocol.confirmation_time S.E (S.hc.opening_slot q' - 1) :=
          Protocol.support_cutoff_le_confirmation_time S.E _
        _ ≤ Protocol.confirmation_time S.E (S.hc.opening_slot q') :=
          fixedRootSource_confirmation_time_mono S.E hlastLt.le
        _ = S.a q' := by
          rw [Setup.a, Protocol.a_eq_confirmation_time]
        _ ≤ rho.horizon := hhorQ'
    have hparentCaptureRaw : Block.Preceq Q
        (proposedParent S rho (S.hc.opening_slot q' - 1 + 1)) :=
      coneTarget_preceq_nextProposedParent_named S adm hcom hlastPos
        hpostLast hsupportHor
          (by simpa only [hlastSucc] using hB2Lifecycle.proposerHonest)
          hsourceCone
          (by simpa only [hlastSucc] using hactiveQ)
          (by simpa only [hlastSucc] using hanchorCompat')
    have hparentCapture : Block.Preceq Q
        (proposedParent S rho (S.hc.opening_slot q')) := by
      simpa only [hlastSucc] using hparentCaptureRaw
    obtain ⟨P2, hP2parent, hP2erase⟩ :=
      proposedBlockAt_parent S rho (S.hc.opening_slot q') hB2Lifecycle.proposal
    have hparentEq : B2.parent = P2 := by
      cases B2 with
      | genesis => cases hP2parent
      | node p slot root votes support rows proposer =>
          exact Option.some.inj hP2parent
    have hsourceParent : Block.Preceq Q B2.parent.erase := by
      rw [hparentEq, hP2erase]
      exact hparentCapture
    have hsourceParentNamed : Block.Preceq Cn.erase B2.parent.erase := by
      rw [hCerase]
      exact hsourceParent
    have hCnParent : NamedBlock.Preceq Cn B2.parent :=
      Protocol.namedPreceq_of_runBlock_erase_preceq adm hCrun
        hB2ParentRun hsourceParentNamed
    calc
      ((actionReadAt S rho v (q' - 1)).st.core.toHealing.σ Q).h =
          (Protocol.derive_named S.E S.cfg Cn).h := hσheight
      _ ≤ (Protocol.derive_named S.E S.cfg B2.parent).h :=
        Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hCnParent
  · have hsourceHeightLt :
        (Protocol.derive_named S.E S.cfg Cn).h < H - 1 :=
      Nat.lt_of_not_ge hsourceBand
    calc
      ((actionReadAt S rho v (q' - 1)).st.core.toHealing.σ Q).h =
          (Protocol.derive_named S.E S.cfg Cn).h := hσheight
      _ ≤ (Protocol.derive_named S.E S.cfg B2.parent).h :=
        (Nat.le_of_lt hsourceHeightLt).trans hparentLower

#print axioms fixedRoot_sourceHeight_le_nextOpeningParent


end DecoupledConsensusModel.Proofs.HealingSurface

end
