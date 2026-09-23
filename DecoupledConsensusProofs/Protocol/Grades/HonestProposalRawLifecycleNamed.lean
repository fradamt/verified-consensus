module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalAdoptionNamedClosed
public import DecoupledConsensusProofs.Execution.ProposalConfirmationPreparedLiveNamed

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Raw opening lifecycle at an arbitrary healed named carrier -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.NamedRecoveryRead
open Internal.PhaseGrades Protocol Proofs.Optimistic Proofs.HealingLemmas DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

/-- The opening confirmation at an arbitrary post-deadline honest carrier is
the carrier's named proposal. -/
theorem honestProposal_liveConfirmed_at_action_after_SG_healing_named_of_openingProposer
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {m : Round} {P : NamedBlock V}
    (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m)
    (hopening : S.E.proposer (S.hc.opening_slot m) ∈ rho.honest)
    (hP : proposedBlockAt S rho (S.hc.opening_slot m) = some P)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot m) ≤ rho.horizon) :
    ∀ v ∈ rho.honest,
      (actionReadAt S rho v m).st.core.live_confirmed = P.erase := by
  classical
  let D := fgSafetyProgressDeadline S rho rGST gap delayExtra
  let start := S.hc.opening_slot m
  have hmPos : 2 ≤ m := (Nat.le_add_left 2 D).trans (by
    simpa only [D] using hm)
  have hstartPos : 0 < start := by
    unfold start Protocol.HealConfig.opening_slot
    exact Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_two hmPos)
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hprop : S.E.proposer start ∈ rho.honest := by
    simpa only [start] using hopening
  have hvoteHor : Protocol.vote_time S.E start ≤ rho.horizon :=
    (vote_time_le_confirmation_time S.E start).trans hhor
  have hvoteDelta : Protocol.vote_time S.E start + S.E.Δ ≤ rho.horizon := by
    rw [vote_time_add_delta]
    exact (support_cutoff_le_confirmation_time S.E start).trans hhor
  have hdeadlineSlot : S.hc.opening_slot D + 1 ≤ start := by
    have hstep : S.hc.opening_slot D + 1 <
        S.hc.opening_slot (D + 1) := by
      simpa only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
        using Nat.add_lt_add_left (Nat.lt_of_succ_le S.hc.R_ge_two)
          (D * S.hc.R)
    have hround : D + 1 ≤ m :=
      (Nat.le_succ (D + 1)).trans (by
        simpa only [D, Nat.add_assoc] using hm)
    exact hstep.le.trans (by
      simpa only [start, Protocol.HealConfig.opening_slot] using
        Nat.mul_le_mul_right S.hc.R hround)
  have hdeadlineProposal : S.a D ≤ Protocol.proposal_time S.E start := by
    have hround : S.hc.opening_slot D + 2 ≤ start := by
      have hstep : S.hc.opening_slot D + 2 ≤
          S.hc.opening_slot (D + 1) := by
        simp only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
        exact Nat.add_le_add_left S.hc.R_ge_two (D * S.hc.R)
      have hDm : D + 1 ≤ m :=
        (Nat.le_succ (D + 1)).trans (by
          simpa only [D, Nat.add_assoc] using hm)
      exact hstep.trans (by
        simpa only [start, Protocol.HealConfig.opening_slot] using
          Nat.mul_le_mul_right S.hc.R hDm)
    exact (action_lt_proposal_time_two_after S D).le.trans
      (proposal_time_mono S.E hround)
  have hdeadlineRead : S.a D ≤ Protocol.confirmation_time S.E start :=
    hdeadlineProposal.trans (proposal_time_le_confirmation_time S.E start)
  have hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E start := by
    have hGSTdead : rGST ≤ D := by
      unfold D fgSafetyProgressDeadline
      exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
    exact hpost.trans (((action_strictMono S).monotone hGSTdead).trans
      (hdeadlineProposal.trans (proposal_time_lt_vote_time S.E start).le))
  have hheads : ∀ w ∈ rho.honest, voterHeadAt S rho w start = P.erase :=
    honestProposal_voterHeadAt_eq_after_SG_healing_named_of_openingProposer
      S adm hcom hbelow hrec hdelay hpost
        (by simpa only [D] using hm) (by simpa only [start] using hvoteHor)
        hopening (by simpa only [start] using hP)
  have hcone : NamedHonestVotesCone S rho start
      (fun X => Block.Preceq P.erase X) :=
    honestProposal_openingVoteCone_after_SG_healing_named_of_openingProposer
      S adm hcom (by simpa only [D] using hm) hopening
        (by simpa only [start] using hvoteHor) (by simpa only [start] using hP)
        (by simpa only [start] using hheads)
  have hread := honestProposal_confirmationReadFacts_after_SG_healing_named_of_openingProposer
    S adm hcom hbelow hrec hdelay hpost (by simpa only [D] using hm)
      (by simpa only [start] using hhor) hopening
      (by simpa only [start] using hP)
  have hPrun : RunBlock S rho P :=
    proposedBlock_runBlock S adm hstartPos hprop
      ((proposal_time_le_confirmation_time S.E start).trans hhor) hP
  have hnames : NamedHonestVotesName S rho start P.erase := by
    intro w hw hwc
    obtain ⟨X, hXhead, -, hXemit⟩ := WeakGoldfish.voterHead_runBlock_and_emits
      S adm.toNamedAdmissibleCore hw hstartPos hwc hvoteHor
    have hX : X.erase = P.erase := hXhead.trans (hheads w hw)
    simpa only [hX] using hXemit
  intro v hv
  obtain ⟨hanchor, hcandidate⟩ := hread v hv
  have hroot : Block.Preceq
      (Protocol.get_fg_root
        (confirmationInputRead S rho v start).st.core.toHealing.toFG) P.erase := by
    have hrootHead := fgRoot_preceq_previousHead_through_confirmation_after_GST
      S adm hcom hbelow hrec hdelay hpost hdeadlineRead hhor
        hdeadlineSlot (le_refl _) hvoteDelta hv hv
    have hrootHead' : Block.Preceq
        (Protocol.get_fg_root
          (confirmationInputRead S rho v start).st.core.toHealing.toFG)
        (voterHeadAt S rho v start) := by
      simpa only [confirmationInputRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Protocol.voteDutyHead] using hrootHead
    simpa only [hheads v hv] using hrootHead'
  have hgenuine := genuineConfirmationAndPreceq_of_postHealingCone
    S adm hcom hstartPos hpostVote hhor hv hcone hroot hanchor hcandidate
  have hsupport := honestSupport_confVotes_after_gst_of_names
    S adm hcom hstartPos hpostVote hhor hPrun hnames hv hroot hcandidate
  have hvalid : Protocol.VoteSetValid S.E start
      (confLate S.E (confStore S rho v start) start) := by
    simpa only [confStore, tickStore] using
      voteSetValid_confLate_stateBeforeTime S adm.toNamedScheduleWellFormed v
        (Protocol.confirmation_time S.E start) start
  have hpath : ∀ C : Block V,
      Block.Preceq
          (confAnchorWith
            (NamedProfile.gradeContract
              (confirmationInputRead S rho v start).cache)
            S.E S.hc (confStore S rho v start)) C →
      C ≠ confAnchorWith
          (NamedProfile.gradeContract
            (confirmationInputRead S rho v start).cache)
          S.E S.hc (confStore S rho v start) →
      Block.Preceq C P.erase → C ∈ confTree (confStore S rho v start) := by
    have hpath' := confPath_of_candidate S
      (show P.erase ∈ confTree (confStore S rho v start) from by
        simpa only [confStore_eq_confirmationInputRead] using hcandidate)
    simpa only [confAnchorWith, namedConfirmationAnchor,
      confStore_eq_confirmationInputRead] using hpath'
  have hanchor' : Block.Preceq
      (confAnchorWith
        (NamedProfile.gradeContract
          (confirmationInputRead S rho v start).cache)
        S.E S.hc (confStore S rho v start)) P.erase := by
    simpa only [confAnchorWith, namedConfirmationAnchor,
      confStore_eq_confirmationInputRead] using hanchor
  obtain ⟨hwalk, -⟩ := confWalkWith_eq_of_support
    (NamedProfile.gradeContract (confirmationInputRead S rho v start).cache)
    S.E S.hc (confStore S rho v start) start rho.honest P.erase
      (by simpa only [confStore_eq_confirmationInputRead, confVotes,
        confirmationVotes] using hsupport) hvalid hanchor' hpath
  have helig : confEligible S.E (confStore S rho v start) start P.erase = true := by
    rw [← hwalk]
    exact hgenuine.1.genuine
  change (actionStoreAt S rho v m).st.core.live_confirmed = P.erase
  rw [actionStoreAt_eq_update_confirmation_confStore]
  change (Protocol.update_confirmation_with
    (NamedProfile.gradeContract (confirmationInputRead S rho v start).cache)
    S.E S.hc (confStore S rho v start) start).live_confirmed = P.erase
  rw [update_confirmation_with_live_confirmed, hwalk, if_pos helig]

#print axioms honestProposal_liveConfirmed_at_action_after_SG_healing_named_of_openingProposer


set_option maxHeartbeats 400000 in
private theorem lifecyclePreviousActionCarrierInput_of_commonUpper
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} (hq : 0 < q) {p : Phase} {t : Time}
    {C : Block V} (hpost : S.E.t_GST ≤ S.a (q - 1))
    (hsourceHor : S.a (q - 1) ≤ rho.horizon)
    (hcut : early S.E S.hc q p ≤ rho.horizon)
    (horder : early S.E S.hc q p ≤ t)
    {v u : V} (hv : v ∈ rho.honest) (hu : u ∈ rho.honest)
    (hcarrier : Block.Preceq (actionSGBlockAt S rho u (q - 1)) C)
    (hF : Block.Preceq
      (NamedRun.stateBeforeTime S rho t v).st.core.F C) :
    Protocol.sgVote (actionAttestationAt S rho u (q - 1)).erase ∈
      DecoupledConsensusModel.Protocol.interpretedInputs
        (NamedRun.stateBeforeTime S rho t v).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho t v).st.core.F
        S.hc.η_SG q (early S.E S.hc q p) u ∧
      (Protocol.sgVote (actionAttestationAt S rho u (q - 1)).erase).round = q - 1 ∧
      (Protocol.sgVote (actionAttestationAt S rho u (q - 1)).erase).confirmed =
        some (actionSGBlockAt S rho u (q - 1)).root ∧
      Block.find? (NamedRun.stateBeforeTime S rho t v).st.core.T
        (actionSGBlockAt S rho u (q - 1)).root =
          some (actionSGBlockAt S rho u (q - 1)) := by
  have hqr : q - 1 < q := Nat.sub_lt hq (by decide)
  have hk : q - 1 ∈ Protocol.latest_window S.hc.η_SG q :=
    NamedOutageClosure.mem_latest_window
      (Nat.sub_le_sub_left S.hc.η_SG_ge_one q) hqr
  have hdeadline : max (S.a (q - 1)) S.E.t_GST + S.E.Δ ≤
      early S.E S.hc q p := by
    rw [max_eq_left hpost]
    apply (NamedOutageClosure.action_delta_le_early
      S S.hc.R_ge_three hqr).trans
    cases p <;> simp only [early, Phase.earlyOffset] <;>
      linarith [S.E.Δ_pos]
  let a := actionAttestationAt S rho u (q - 1)
  have hshape : a.val_index = u ∧ a.round = q - 1 ∧
      a.confirmed = some (actionSGBlockAt S rho u (q - 1)).root := by
    simpa only [a] using actionAttestationAt_shape S rho u (q - 1)
  have hemit : NamedRun.emits S rho u (Object.attest a) (S.a (q - 1)) := by
    simpa only [a] using
      honest_emits_exact_actionAttestationAt S adm hu (q - 1) hsourceHor (by assumption)
  obtain ⟨i, hi, _, hhead⟩ := Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
  dsimp at hhead
  obtain ⟨H, hH, hconfirmed⟩ := hhead
  have hbodySource : H ∈
      (NamedRun.stateBeforeTime S rho (S.a (q - 1)) u).st.bodies := by
    have hi' : rho.events[i]? = some (.tick u (S.a (q - 1))) := by
      simpa only [hshape.2.1] using hi
    have hstate := NamedActionSources.action_read_index S rho
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed i u (q - 1) hi'
    change H ∈ (NamedRun.stateBefore S rho i u).st.bodies at hH
    rw [← hstate]
    exact hH
  have hcarrierMem : actionSGBlockAt S rho u (q - 1) ∈
      (NamedRun.stateBeforeTime S rho (S.a (q - 1)) u).st.core.T :=
    actionSGBlockAt_mem_storeBeforeTime S rho u (q - 1)
  obtain ⟨D, hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (S.a (q - 1)) u hcarrierMem
  obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted (S.a (q - 1))
  have hDprefix : D ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact hDbody
  have hHprefix : H ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact hbodySource
  have hDrun : RunBlock S rho D :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hu (i := n) hDprefix
  have hHrun : RunBlock S rho H :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hu (i := n) hHprefix
  have hroot : D.root = H.root := by
    rw [← Proofs.NamedWire.erase_root D, hDerase]
    exact Option.some.inj (hshape.2.2.symm.trans hconfirmed)
  have hDH : D = H :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective D H
      hDrun hHrun D H (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self H)) hroot
  have hHErase : H.erase = actionSGBlockAt S rho u (q - 1) := by
    rw [← hDH, hDerase]
  have hHC : Block.Preceq H.erase C := by
    rw [hHErase]
    exact hcarrier
  have hinput := action_vote_mem_interpretedInputs_after_gst_common_upper
      S adm.toNamedAdmissibleCore p hk hu hv
      ⟨hshape.1, hshape.2.1, hemit⟩ ⟨i, hi, hH, hconfirmed⟩
      hHC hF (by simpa only [hshape.2.1] using hpost)
      (by simpa only [hshape.2.1] using hdeadline) horder hcut
  have hconfirmedInput : (Protocol.sgVote a.erase).confirmed =
      some (actionSGBlockAt S rho u (q - 1)).root := by
    rw [NamedOutageClosure.sgVote_confirmed, hshape.2.2]
  have hfind : Block.find? (NamedRun.stateBeforeTime S rho t v).st.core.T
      (actionSGBlockAt S rho u (q - 1)).root =
        some (actionSGBlockAt S rho u (q - 1)) := by
    have hbodyReady := (Finset.mem_filter.mp hinput).2
    simp only [DecoupledConsensusModel.Protocol.bodyReady, hconfirmedInput] at hbodyReady
    change (match Block.find?
        (NamedRun.stateBeforeTime S rho t v).st.core.T
        (actionSGBlockAt S rho u (q - 1)).root with
      | none => false
      | some H => stampedBefore
          (NamedRun.stateBeforeTime S rho t v).st.core.timestamp_block
          (early S.E S.hc q p) H &&
        Block.compatible H
          (NamedRun.stateBeforeTime S rho t v).st.core.F) = true at hbodyReady
    cases hx : Block.find? (NamedRun.stateBeforeTime S rho t v).st.core.T
        (actionSGBlockAt S rho u (q - 1)).root with
    | none => simp [hx] at hbodyReady
    | some X =>
        have hXmem := Proofs.HealingLemmas.find?_mem hx
        obtain ⟨Xn, hXerase, hXrun⟩ :=
          Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
            adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv t hXmem
        have hXHroot : Xn.root = H.root := by
          rw [← Proofs.NamedWire.erase_root Xn, hXerase,
            Proofs.HealingLemmas.find?_root hx, ← hHErase, Proofs.NamedWire.erase_root H]
        have hXH :=
          adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective Xn H
            hXrun hHrun Xn H (Or.inl (Proofs.NamedAncestry.named_self Xn))
            (Or.inr (Proofs.NamedAncestry.named_self H)) hXHroot
        congr 1
        exact hXerase.symm.trans ((congrArg NamedBlock.erase hXH).trans hHErase)
  refine ⟨by simpa only [a] using hinput, ?_,
    by simpa only [a] using hconfirmedInput, hfind⟩
  simpa only [NamedOutageClosure.sgVote_round] using hshape.2.1

set_option maxHeartbeats 400000 in
private theorem lifecycleRelativeCarrierWindowAt_of_commonEndpoint
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} (hq : 0 < q) {p : Phase} {C : Block V}
    (hpost : S.E.t_GST ≤ S.a (q - 1))
    (hsourceHor : S.a (q - 1) ≤ rho.horizon)
    (hhor : domain S.E S.hc q p ≤ rho.horizon)
    (hcarrier : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u (q - 1)) C)
    (hroot : ∀ v ∈ rho.honest,
      Block.Preceq
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc q p) v).st.core.F C) :
    RelativeCarrierWindowAt S rho (q - 1) p := by
  intro v hv u hu
  change ∃ y ∈ DecoupledConsensusModel.Protocol.interpretedInputs
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (q - 1 + 1) p) v).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (q - 1 + 1) p) v).st.core.F
      S.hc.η_SG (q - 1 + 1) (early S.E S.hc (q - 1 + 1) p) u,
    y.round = q - 1 ∧
      y.confirmed = some (actionSGBlockAt S rho u (q - 1)).root ∧
      Block.find? (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (q - 1 + 1) p) v).st.core.T
        (actionSGBlockAt S rho u (q - 1)).root =
          some (actionSGBlockAt S rho u (q - 1))
  have huHon := ((Proofs.NamedOutageInputs.honestRoundVoters_iff
    S rho u (q - 1)).mp hu).1
  have hpred : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hq)
  have hearlyDomain : early S.E S.hc q p ≤ domain S.E S.hc q p := by
    cases p <;> simp only [early, domain, Phase.earlyOffset,
      Phase.domainOffset] <;> linarith [S.E.Δ_pos]
  have hres := lifecyclePreviousActionCarrierInput_of_commonUpper
    S adm hq hpost hsourceHor (hearlyDomain.trans hhor) hearlyDomain hv huHon
      (hcarrier u huHon) (hroot v hv)
  refine ⟨Protocol.sgVote (actionAttestationAt S rho u (q - 1)).erase, ?_⟩
  simpa only [hpred] using hres

set_option maxHeartbeats 400000 in
private theorem lifecycleActionBatchAlignedAt_of_commonEndpoint
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} (hq : 0 < q) {C : Block V}
    (hpost : S.E.t_GST ≤ S.a (q - 1))
    (hprevHor : S.a (q - 1) ≤ rho.horizon)
    (hactionHor : S.a q ≤ rho.horizon)
    (hcarrier : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u (q - 1)) C)
    (hroot : ∀ v ∈ rho.honest,
      Block.Preceq (actionReadAt S rho v q).st.core.F C) :
    ∀ v ∈ rho.honest,
      let n := actionReadAt S rho v q
      BatchAlignedAt S.hc n.st.core.toHealing.gradeView n.st.core.F
        rho.honest q (allPhasesCutoff S.E S.hc q) C := by
  have horder : early S.E S.hc q .g0 ≤ S.a q := by
    have hearlyDomain : early S.E S.hc q .g0 ≤ domain S.E S.hc q .g0 := by
      simp only [early, domain, Phase.earlyOffset, Phase.domainOffset]
      linarith [S.E.Δ_pos]
    exact hearlyDomain.trans (FrameForward.domain_le_a S q .g0)
  have hcut : early S.E S.hc q .g0 ≤ rho.horizon := horder.trans hactionHor
  have hlatest := nextActionBatchAligned_preceq_of_carriersPreceq_at_latest
    S adm hactionHor hcarrier
  intro v hv n w hw u hu hmax head hconfirmed hfind
  have hlatestV := hlatest v hv
  dsimp only at hlatestV
  apply hlatestV w hw
  · have hinput := lifecyclePreviousActionCarrierInput_of_commonUpper
      S adm hq hpost hprevHor hcut horder hv hw
        (hcarrier w hw) (hroot v hv)
    simpa only [allPhasesCutoff, early, late, Phase.earlyOffset,
      Phase.lateOffset] using hinput.1
  · exact hu
  · exact hmax
  · exact hconfirmed
  · exact hfind

set_option maxHeartbeats 400000 in
private theorem lifecycleNodeClear_live_of_commonEndpoint
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {q : Round} (hq : 0 < q) {C : Block V}
    (hactionHor : S.a q ≤ rho.horizon)
    (hgradeHor : domain S.E S.hc q .g2 ≤ rho.horizon)
    (hpost : S.E.t_GST ≤ S.a (q - 1))
    (hwindow : RelativeCarrierWindowAt S rho (q - 1) .g0)
    (hcarrier : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u (q - 1)) C)
    {D : Block V} (hCD : Block.Preceq C D) :
    ∀ v ∈ rho.honest,
      nodeClear S (actionReadAt S rho v q) q D = true := by
  have hpred : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hq)
  have hforming : Internal.NamedOutageEntry.GradeFormingMajority S rho (q - 1 + 1) := by
    rw [hpred]
    exact gradeFormingMajority_of_admissible_belowOneThird
      S adm hfb hq hgradeHor hpost
  intro v hv
  have hframe := actionFrame_g0 S adm.toNamedAdmissibleCore hv
    hq hactionHor
  unfold nodeClear nodeRead
  change DecoupledConsensusModel.Protocol.clear
    (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho v q).cache
      (actionReadAt S rho v q).st.core.toHealing q) D = true
  unfold DecoupledConsensusModel.Protocol.clear
  rw [hframe]
  cases hroot : storeRoot S.E S.hc
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g0) v).st q .g0 with
  | none => rfl
  | some raw =>
      have hrawGrade : DecoupledConsensusModel.Protocol.gradeBool S.E
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc q .g0) v).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc q .g0) v).st.core.F
          S.hc.η_SG q (early S.E S.hc q .g0)
          (late S.E S.hc q .g0) raw = true :=
        (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hroot)).2
      have hrawGrade' : DecoupledConsensusModel.Protocol.gradeBool S.E
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (q - 1 + 1) .g0) v).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (q - 1 + 1) .g0) v).st.core.F
          S.hc.η_SG (q - 1 + 1) (early S.E S.hc (q - 1 + 1) .g0)
          (late S.E S.hc (q - 1 + 1) .g0) raw = true := by
        rw [hpred]
        exact hrawGrade
      obtain ⟨u, hu, hrawCarrier⟩ := relativeGrade_has_roundCarrier
        S adm.toNamedAdmissibleCore hwindow hforming hv hrawGrade'
      have huHon := ((Proofs.NamedOutageInputs.honestRoundVoters_iff
        S rho u (q - 1)).mp hu).1
      have hrawD : Block.Preceq raw D :=
        Block.preceq_trans hrawCarrier
          (Block.preceq_trans (hcarrier u huHon) hCD)
      have hclipD : Block.Preceq
          (DecoupledConsensusModel.Protocol.clipGrade raw
            (actionReadAt S rho v q).st.core.F) D :=
        Block.preceq_trans
          (NamedOutageClosure.q10_clip_preceq raw
            (actionReadAt S rho v q).st.core.F) hrawD
      change Block.compatible D
        (DecoupledConsensusModel.Protocol.clipGrade raw
          (actionReadAt S rho v q).st.core.F) = true
      simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr hclipD

/-- Every honest action carrier covers the arbitrary post-deadline honest
carrier proposal. -/
theorem honestProposal_actionSelectors_after_SG_healing_named_of_openingProposer
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {m : Round} {P : NamedBlock V}
    (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m)
    (hopening : S.E.proposer (S.hc.opening_slot m) ∈ rho.honest)
    (hP : proposedBlockAt S rho (S.hc.opening_slot m) = some P)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot m) ≤ rho.horizon) :
    ∀ v ∈ rho.honest,
      actionSGBlockAt S rho v m = P.erase ∧
      Block.Preceq (nodeAnchor S (actionReadAt S rho v m) m) P.erase ∧
      nodeClear S (actionReadAt S rho v m) m P.erase = true := by
  classical
  let D := fgSafetyProgressDeadline S rho rGST gap delayExtra
  let start := S.hc.opening_slot m
  have hmPos : 2 ≤ m := (Nat.le_add_left 2 D).trans (by
    simpa only [D] using hm)
  have hmOne : 1 ≤ m := (by decide : 1 ≤ 2).trans hmPos
  have hmPositive : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hmOne
  have hpred : m - 1 + 1 = m := Nat.sub_add_cancel hmOne
  have hcEq : m - 2 + 1 = m - 1 := by
    have hmPredOne : 1 ≤ m - 1 := Nat.le_sub_of_add_le hmPos
    simpa only [Nat.sub_sub, Nat.add_comm, Nat.reduceAdd] using
      Nat.sub_add_cancel hmPredOne
  have hcDeadline : D ≤ m - 2 := Nat.le_sub_of_add_le (by
    simpa only [D] using hm)
  have hactionHor : S.a m ≤ rho.horizon := by
    simpa only [start, opening_confirmation_time_eq_action] using hhor
  have hprevHor : S.a (m - 1) ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.sub_le m 1)).trans hactionHor
  have hpostPrev : S.E.t_GST ≤ S.a (m - 1) := by
    have hGSTdead : rGST ≤ D := by
      unfold D fgSafetyProgressDeadline
      exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
    exact hpost.trans ((action_strictMono S).monotone
      (hGSTdead.trans (hcDeadline.trans (Nat.sub_le (m - 1) 1))))
  have hvoteHor : Protocol.vote_time S.E start ≤ rho.horizon :=
    (vote_time_le_confirmation_time S.E start).trans hhor
  have hvoteDelta : Protocol.vote_time S.E start + S.E.Δ ≤ rho.horizon := by
    rw [vote_time_add_delta]
    exact (support_cutoff_le_confirmation_time S.E start).trans hhor
  have hdeadlineSlot : S.hc.opening_slot D + 1 ≤ start := by
    have hstep : S.hc.opening_slot D + 1 <
        S.hc.opening_slot (D + 1) := by
      simpa only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
        using Nat.add_lt_add_left (Nat.lt_of_succ_le S.hc.R_ge_two)
          (D * S.hc.R)
    have hround : D + 1 ≤ m :=
      (Nat.le_succ (D + 1)).trans (by
        simpa only [D, Nat.add_assoc] using hm)
    exact hstep.le.trans (by
      simpa only [start, Protocol.HealConfig.opening_slot] using
        Nat.mul_le_mul_right S.hc.R hround)
  have hdeadlineProposal : S.a D ≤ Protocol.proposal_time S.E start := by
    have hround : S.hc.opening_slot D + 2 ≤ start := by
      have hstep : S.hc.opening_slot D + 2 ≤
          S.hc.opening_slot (D + 1) := by
        simp only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
        exact Nat.add_le_add_left S.hc.R_ge_two (D * S.hc.R)
      have hDm : D + 1 ≤ m :=
        (Nat.le_succ (D + 1)).trans (by
          simpa only [D, Nat.add_assoc] using hm)
      exact hstep.trans (by
        simpa only [start, Protocol.HealConfig.opening_slot] using
          Nat.mul_le_mul_right S.hc.R hDm)
    exact (action_lt_proposal_time_two_after S D).le.trans
      (proposal_time_mono S.E hround)
  have hdeadlineRead : S.a D ≤ Protocol.confirmation_time S.E start :=
    hdeadlineProposal.trans (proposal_time_le_confirmation_time S.E start)
  have hheads : ∀ w ∈ rho.honest, voterHeadAt S rho w start = P.erase :=
    honestProposal_voterHeadAt_eq_after_SG_healing_named_of_openingProposer
      S adm hcom hbelow hrec hdelay hpost
        (by simpa only [D] using hm) (by simpa only [start] using hvoteHor)
        hopening (by simpa only [start] using hP)
  have hinterior : S.hc.opening_slot (m - 1) + 1 ≤ start := by
    have hstep : S.hc.opening_slot (m - 1) + 1 <
        S.hc.opening_slot (m - 1 + 1) := by
      simpa only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
        using Nat.add_lt_add_left (Nat.lt_of_succ_le S.hc.R_ge_two)
          ((m - 1) * S.hc.R)
    simpa only [hpred, start] using hstep.le
  have hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u (m - 1)) P.erase := by
    intro u hu
    have h := actionSGBlock_preceq_voterHeadAt_after_GST
      S adm hcom hbelow hrec hdelay hpost hcDeadline
        (by simpa only [hcEq] using hinterior) hvoteDelta hu hu
    rw [hheads u hu] at h
    simpa only [hcEq] using h
  have hdomainG0Hor : domain S.E S.hc m .g0 ≤ rho.horizon :=
    (FrameForward.domain_le_a S m .g0).trans hactionHor
  have hdomainG2Hor : domain S.E S.hc m .g2 ≤ rho.horizon :=
    (FrameForward.domain_le_a S m .g2).trans hactionHor
  have hdeadlineG0 : S.a D ≤ domain S.E S.hc m .g0 := by
    apply hdeadlineProposal.trans
    simp only [domain, opening, Phase.domainOffset, one_mul]
    exact le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)
  have hrootG0 : ∀ v ∈ rho.honest,
      Block.Preceq
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc m .g0) v).st.core.F
        P.erase := by
    intro v hv
    have hfg := fgRoot_preceq_previousHead_through_confirmation_after_GST
      S adm hcom hbelow hrec hdelay hpost hdeadlineG0 hdomainG0Hor
        hdeadlineSlot
        ((FrameForward.domain_le_a S m .g0).trans (by
          simpa only [start, opening_confirmation_time_eq_action] using
            (le_refl (S.a m))))
        hvoteDelta hv hv
    have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
      S rho (domain S.E S.hc m .g0) v
    exact Block.preceq_trans
      (Proofs.Records.preceq_get_fg_root_of_F (st :=
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc m .g0) v).st.core.toHealing.toFG)
        hFJ)
      (by simpa only [Protocol.voteDutyHead, hheads v hv] using hfg)
  have hrootAction : ∀ v ∈ rho.honest,
      Block.Preceq
        (Protocol.get_fg_root
          (actionReadAt S rho v m).st.core.toHealing.toFG) P.erase := by
    intro v hv
    have hconf := fgRoot_preceq_previousHead_through_confirmation_after_GST
      S adm hcom hbelow hrec hdelay hpost hdeadlineRead hhor
        hdeadlineSlot (le_refl _) hvoteDelta hv hv
    have hrootEq : Protocol.get_fg_root
        (actionReadAt S rho v m).st.core.toHealing.toFG =
        Protocol.get_fg_root
          (confirmationInputRead S rho v start).st.core.toHealing.toFG := by
      calc
        Protocol.get_fg_root
            (actionReadAt S rho v m).st.core.toHealing.toFG =
            Protocol.get_fg_root
              (confStore S rho v start).toHealing.toFG := by
                simpa only [actionStoreAt, start] using
                  actionStoreAt_fgRoot_eq_openingConfStore S rho v m
        _ = Protocol.get_fg_root
            (confirmationInputRead S rho v start).st.core.toHealing.toFG := by
              rw [confStore_eq_confirmationInputRead]
    rw [hrootEq]
    simpa only [confirmationInputRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Protocol.voteDutyHead, hheads v hv] using hconf
  have hrootActionF : ∀ v ∈ rho.honest,
      Block.Preceq (actionReadAt S rho v m).st.core.F P.erase := by
    intro v hv
    exact Block.preceq_trans
      (StoreFinality.finalized_preceq_fgRoot
        (Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
          S rho (S.a m) v))
      (hrootAction v hv)
  have hwindow : RelativeCarrierWindowAt S rho (m - 1) .g0 :=
    lifecycleRelativeCarrierWindowAt_of_commonEndpoint S adm hmPositive
      hpostPrev hprevHor hdomainG0Hor hupper hrootG0
  have hbatch := lifecycleActionBatchAlignedAt_of_commonEndpoint
    S adm hmPositive hpostPrev hprevHor hactionHor hupper hrootActionF
  have hclear := lifecycleNodeClear_live_of_commonEndpoint
    S adm hbelow hmPositive hactionHor hdomainG2Hor hpostPrev hwindow hupper
      (Block.preceq_self P.erase)
  have hanchor : ∀ v ∈ rho.honest,
      Block.Preceq (nodeAnchor S (actionReadAt S rho v m) m) P.erase := by
    intro v hv
    have hread := honestProposal_confirmationReadFacts_after_SG_healing_named_of_openingProposer
      S adm hcom hbelow hrec hdelay hpost (by simpa only [D] using hm)
        (by simpa only [start] using hhor) hopening
        (by simpa only [start] using hP) v hv
    have hroundConf : S.hc.round_of
        (confirmationInputRead S rho v start).st.core.s = m := by
      simpa only [start, confirmationInputRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        opening_confirmation_time_eq_action, Protocol.NamedStore.setClock] using
        Proofs.HealingLemmas.round_of_slotOf_a S m
    have hconfAnchor : namedConfirmationAnchor S
        (confirmationInputRead S rho v start) =
        nodeAnchor S (confirmationInputRead S rho v start) m := by
      simpa only [namedConfirmationAnchor, nodeAnchor, nodeRead,
        Protocol.get_sg_root_with, hroundConf]
    have hnode : nodeAnchor S (actionReadAt S rho v m) m =
        nodeAnchor S (confirmationInputRead S rho v start) m := by
      rfl
    rw [hnode, ← hconfAnchor]
    exact hread.1
  intro v hv
  have hlive := honestProposal_liveConfirmed_at_action_after_SG_healing_named_of_openingProposer
    S adm hcom hbelow hrec hdelay hpost hm hopening hP hhor v hv
  have heq : actionSGBlockAt S rho v m = P.erase := by
    apply actionSGBlockAt_eq_liveConfirmed_of_batchAligned S
      (Can := P.erase) (D := P.erase)
      (A := nodeAnchor S (actionReadAt S rho v m) m)
    · exact hlive
    · exact hbatch v hv
    · exact Block.preceq_self _
    · rfl
    · exact hanchor v hv
    · exact hclear v hv
  exact ⟨heq, hanchor v hv, hclear v hv⟩


#print axioms honestProposal_actionSelectors_after_SG_healing_named_of_openingProposer

/-- The carrier form of the action-cover export, for the existing consumers. -/
theorem honestProposal_actionCover_after_SG_healing_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {m : Round} {P : NamedBlock V}
    (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m)
    (hcarrier : ProposerCarrierAt S rho m)
    (hP : proposedBlockAt S rho (S.hc.opening_slot m) = some P)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot m) ≤ rho.horizon) :
    ActionCarriersCover S rho m P.erase := by
  intro v hv
  rw [(honestProposal_actionSelectors_after_SG_healing_named_of_openingProposer
    S adm hcom hbelow hrec hdelay hpost hm hcarrier.1 hP hhor v hv).1]
  exact Block.preceq_self _

#print axioms honestProposal_actionCover_after_SG_healing_named



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
