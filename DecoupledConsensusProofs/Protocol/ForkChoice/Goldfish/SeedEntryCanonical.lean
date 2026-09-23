module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.SeedFinalizedCanonical
public import DecoupledConsensusProofs.Protocol.Schedule.SeedBoundaryConeLead
public import DecoupledConsensusProofs.Protocol.Grades.SeedHeightProgress
public import DecoupledConsensusProofs.Execution.SeedCommonRootComplement
public import DecoupledConsensusProofs.Protocol.Schedule.SeedCanonicalAnchor
public import DecoupledConsensusProofs.Protocol.Grades.RelativeSeedK3
public import DecoupledConsensusProofs.Protocol.Grades.Q31_actionSGBlock_tiers
public import DecoupledConsensusProofs.Protocol.Grades.SeedActionQ2
public import DecoupledConsensusProofs.Protocol.Grades.SeedRelativeGrade
public import DecoupledConsensusProofs.Protocol.Grades.RelativeCarrierWindowGateOff

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# The seed entry on canonicity (no common root)

The helpers of `SeedBoundaryConeLeadRun` that used the common-root window are
restated here on canonicity (`finalizedRoot_preceq_of_band`): the relay of a
grade-1 block's band witness needs only that the receiver's FG root is below
the witness, which every band run block satisfies at a gate-off read.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

/-- The previous action is two relay delays before the round's opening
proposal (`R ≥ 2`). -/
private theorem prevAction_add_two_delta_le_openingProposal'
    (S : Setup V) {c : Round} (hc : 1 ≤ c) :
    S.a (c - 1) + 2 * S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot c) := by
  have hcR : S.hc.opening_slot c = S.hc.opening_slot (c - 1) + S.hc.R := by
    unfold Protocol.HealConfig.opening_slot
    calc c * S.hc.R = (c - 1 + 1) * S.hc.R := by rw [Nat.sub_add_cancel hc]
      _ = (c - 1) * S.hc.R + S.hc.R := Nat.succ_mul _ _
  have hΔ : (0 : Time) ≤ S.E.Δ := le_of_lt S.E.Δ_pos
  have hR : (2 : Time) ≤ (S.hc.R : Time) := by exact_mod_cast S.hc.R_ge_two
  have h4 : (0 : Time) ≤ 4 * S.E.Δ := Int.mul_nonneg (by decide) hΔ
  have hmul : 4 * S.E.Δ * 2 ≤ 4 * S.E.Δ * (S.hc.R : Time) :=
    Int.mul_le_mul_of_nonneg_left hR h4
  rw [Setup.a]
  unfold Protocol.HealConfig.a Protocol.proposal_time Env.t slotStart
  rw [hcR]
  push_cast
  rw [mul_add]
  have hre : 4 * S.E.Δ * (S.hc.opening_slot (c - 1) : Time) + 6 * S.E.Δ + 2 * S.E.Δ =
      4 * S.E.Δ * (S.hc.opening_slot (c - 1) : Time) + 4 * S.E.Δ * 2 := by ring
  rw [hre]
  exact Int.add_le_add_left hmul _

/-- The support cutoff of the previous slot is two relay delays before the
slot's proposal. -/
private theorem supportCutoff_pred_add_two_delta' (E : Env V) {d : Slot} (hd : 0 < d) :
    Protocol.support_cutoff E (d - 1) + 2 * E.Δ = Protocol.proposal_time E d := by
  unfold Protocol.support_cutoff Protocol.proposal_time Env.t slotStart
  have hcast : ((d : Nat) : Time) = ((d - 1 : Nat) : Time) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel hd).symm
  rw [hcast]
  ring

/-- The band witness of an honest round action's SG carrier, as a named run
block. Local twin of `SeedAssemblyRun.actionCarrierFrontierWitness`, whose
producer is `private` there, so the route is repeated here rather than
re-derived. -/
private theorem actionCarrierFrontierWitness'
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {M : Height}
    (hfrontier : (rho.storeBeforeTime S v (S.a r)).h_max = M) :
    ∃ W : NamedBlock V,
      W.erase ∈ (rho.storeBeforeTime S v (S.a r)).core.T ∧
        Block.Preceq (actionSGBlockAt S rho v r) W.erase ∧
        RunBlock S rho W ∧
          M - 1 ≤ (Protocol.derive_named S.E S.cfg W).h := by
  have hfiltered := actionSGBlockAt_mem_filtered_actionStore S adm v r
  simp only [Protocol.get_filtered_block_tree,
    Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq,
    Protocol.Store.toHealing] at hfiltered
  obtain ⟨⟨⟨-, -⟩, W, hWT, hcarrierW, hheight⟩, -⟩ := hfiltered
  have hmax : (actionStoreAt S rho v r).st.core.h_max = M := by
    rw [actionStoreAt_eq_update_confirmation_confStore]
    simp only [Protocol.update_confirmation_with]
    simpa only [Run.storeBeforeTime] using hfrontier
  rw [hmax] at hheight
  have hWTpre : W ∈ (rho.storeBeforeTime S v (S.a r)).core.T := by
    have hWT' := hWT
    rw [actionStoreAt_eq_update_confirmation_confStore] at hWT'
    simpa only [Protocol.update_confirmation_with] using hWT'
  obtain ⟨D, hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho (S.a r) v hWTpre
  have hDrun : RunBlock S rho D := by
    obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.a r)
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i := n)
    rw [← hn]
    exact hDbody
  have hsig : (actionStoreAt S rho v r).st.core.σ D.erase =
      Protocol.derive_named S.E S.cfg D := by
    rw [actionStoreAt_eq_update_confirmation_confStore]
    simpa only [Protocol.update_confirmation_with, hDerase] using
      (Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho (S.a r) v D hDbody)
  refine ⟨D, ?_, ?_, hDrun, ?_⟩
  · rw [hDerase]
    exact hWTpre
  · simpa only [hDerase] using hcarrierW
  · rw [← congrArg (fun cs => cs.h) hsig]
    simpa only [hDerase] using hheight


/-- **The band witness of a grade-1 block, relayed (canonicity form).** As
`g1_bandWitness_relayed`, but the receiver's FG root is below the witness by
canonicity instead of by a common-root premise: the witness is a band run
block and the receiver's gate is off at the duty read.

design note: the witness is a named run block, its band height is read with
`derive_named`, and the admission of the witness at the receiver goes through
`finalizedBelowAtDeliveriesBefore_of_finalizedPreceqAtLaterRead` (the named
delivery producer of `SeedCanonicalAnchorRun`) instead of the retired
`finalized_preceq_at_delivery_of_voteDutyRoot_preceq`. -/
theorem g1_bandWitness_relayed'
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {c : Round} (hc : 1 ≤ c)
    (hpost : S.E.t_GST ≤ S.a (c - 1))
    (hhor : S.a c ≤ rho.horizon)
    (hprevFrontier : ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (c - 1))).h_max = M)
    {B : Block V}
    (hcarrier : ∃ u ∈ rho.honest, Block.Preceq B (actionSGBlockAt S rho u (c - 1)))
    {w : V} (hw : w ∈ rho.honest) {d : Slot}
    (hd : S.hc.opening_slot c ≤ d)
    (hvoteHor : Protocol.vote_time S.E d ≤ rho.horizon)
    (hgateDuty : (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).h_j + 2 ≤ M) :
    ∃ W : NamedBlock V, RunBlock S rho W ∧ Block.Preceq B W.erase ∧
      M - 1 ≤ (Protocol.derive_named S.E S.cfg W).h ∧
      (W.erase = Block.genesis ∨
        AdmittedBefore S rho w W.erase (Protocol.view_freeze S.E (d - 1))) := by
  have hpredSucc : c - 1 + 1 = c := Nat.sub_add_cancel hc
  have hoPos : 0 < S.hc.opening_slot c := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos hc (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hdPos : 0 < d := lt_of_lt_of_le hoPos hd
  have hdSucc : d - 1 + 1 = d := Nat.sub_add_cancel hdPos
  obtain ⟨u, hu, hBu⟩ := hcarrier
  obtain ⟨W, hWpre, hcarrierW, hWrun, hWh⟩ :=
    actionCarrierFrontierWitness' S adm hu (r := c - 1) (hprevFrontier u hu)
  have hBW : Block.Preceq B W.erase := Block.preceq_trans hBu hcarrierW
  refine ⟨W, hWrun, hBW, hWh, ?_⟩
  have hfreezeLe : Protocol.view_freeze S.E (d - 1) ≤ Protocol.vote_time S.E d := by
    have h := Protocol.view_freeze_lt_vote_time_succ S.E (d - 1)
    rw [hdSucc] at h
    exact le_of_lt h
  have hprevLeCut : S.a (c - 1) ≤ Protocol.support_cutoff S.E (d - 1) := by
    have h1 := prevAction_add_two_delta_le_openingProposal' S hc
    have h2 := supportCutoff_pred_add_two_delta' S.E hdPos
    have h3 : Protocol.proposal_time S.E (S.hc.opening_slot c) ≤
        Protocol.proposal_time S.E d := Protocol.proposal_time_mono S.E hd
    have h4 : S.a (c - 1) + 2 * S.E.Δ ≤
        Protocol.support_cutoff S.E (d - 1) + 2 * S.E.Δ := by
      rw [h2]
      exact h1.trans h3
    exact le_of_add_le_add_right h4
  have hcutIn : S.E.t_GST ≤ Protocol.support_cutoff S.E (d - 1) := hpost.trans hprevLeCut
  -- the receiver's finalized root at the duty read is below the band witness
  have hFW : Block.Preceq
      (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).core.F W.erase :=
    finalizedRoot_preceq_of_band S adm hfb hw hgateDuty hWrun hWh
  rcases block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTime S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed u (S.a (c - 1))
      (by simpa only [Run.storeBeforeTime] using hWpre) with hgen | ⟨D, i, t, hDerase, hacc, ht⟩
  · exact Or.inl hgen
  · right
    have htIn : t < Protocol.support_cutoff S.E (d - 1) := lt_of_lt_of_le ht hprevLeCut
    have hDpos : 0 < D.slot := by
      rw [← Proofs.NamedWire.erase_slot]
      exact Nat.zero_lt_of_lt (Protocol.parent_slot_lt_of_acceptsAt_block S hacc)
    have hfreezeHor : Protocol.view_freeze S.E (d - 1) ≤ rho.horizon :=
      hfreezeLe.trans hvoteHor
    rw [← hDerase]
    apply Protocol.block_admittedBefore_of_accepted_after_cutoff
      S adm hu hw hDpos hacc htIn hcutIn
        (Protocol.support_cutoff_add_delta_eq_view_freeze S.E (d - 1))
        hfreezeHor
    exact finalizedBelowAtDeliveriesBefore_of_finalizedPreceqAtLaterRead S adm
      hfreezeLe (Block.preceq_self _) (by rw [hDerase]; exact hFW)

/-! ## Persistence with a comparable root

`VoteDutyFrameAt` asked for the FG root below the cone block at every duty.
With finalized roots moving, the root is only comparable with the cone block:
either below it (the walk passes the block as before) or above it (the vote
head is above its own root, hence above the block). -/

/-- The prepared-read twin of `Protocol.votePath_of_candidate`: the strict
walk from the prepared vote anchor to a frozen candidate stays in the frozen
candidate tree. The producer in `SeedBoundaryConeLeadRun` is `private`, so the
proof is repeated here verbatim rather than re-derived. -/
private theorem votePathAt_of_candidate'
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot} {C : Block V}
    (hC : C ∈ voterCandidateTreeAt S rho w (s + 1)) :
    ∀ D : Block V,
      Block.Preceq (voterAnchorAt S rho w (s + 1)) D →
      D ≠ voterAnchorAt S rho w (s + 1) → Block.Preceq D C → D ≠ C →
      D ∈ voterCandidateTreeAt S rho w (s + 1) := by
  let duty := voteDutyStore S rho w (s + 1)
  have hCraw : C ∈ voter_candidate_tree S.E duty.toHealing := by
    simpa only [voterCandidateTreeAt, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, duty, voteDutyStore] using hC
  have hCfull : C ∈ Protocol.get_filtered_block_tree duty.toHealing.toFG :=
    frozenVoterCandidateTree_subset_filtered S.E duty.toHealing hCraw
  have hCT : C ∈ duty.T :=
    Proofs.Records.get_filtered_block_tree_subset duty.toHealing.toFG hCfull
  have hpc : ParentClosed duty := by
    simpa only [duty, voteDutyStore, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using
      Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
        (Protocol.vote_time S.E (s + 1)) w
  have hFJ : Block.Preceq duty.F duty.J := by
    simpa only [duty, voteDutyStore, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using
      Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
        (Protocol.vote_time S.E (s + 1)) w
  have hrootAnchor : Block.Preceq
      (Protocol.get_fg_root duty.toHealing.toFG)
      (voterAnchorAt S rho w (s + 1)) := by
    simpa only [duty, voteDutyStore, voterAnchorAt, Internal.PhaseGrades.nodeAnchor,
      Internal.PhaseGrades.nodeRead,
      Internal.NamedRecoveryRead.voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      fg_root_preceq_get_sg_root_with_frame
        (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).cache S.E S.hc
        duty.toHealing (S.hc.round_of duty.toHealing.s)
  intro D hAD _hDne hDC _hDneC
  have hDT : D ∈ duty.T :=
    Proofs.Records.mem_of_preceq ((parentClosed_iff duty).mp hpc).2 D C hCT hDC
  have hCprocessed : C ∈ Protocol.voter_processed_block_tree S.E
      duty.toHealing.toFG.toSG.toGoldfishStore duty.toHealing.s := by
    have hCdata := hCraw
    simp only [voter_candidate_tree, Protocol.get_filtered_block_tree_from,
      Protocol.viable_tree, Protocol.finalized_descendants,
      Finset.mem_filter] at hCdata
    exact hCdata.1.1.1
  have hDfull : D ∈ Protocol.get_filtered_block_tree duty.toHealing.toFG := by
    apply Proofs.Records.mem_filtered_of_preceq (st := duty.toHealing.toFG)
      hFJ hCfull hDT hDC
    exact Block.preceq_trans hrootAnchor hAD
  have hDprocessed : D ∈ Protocol.voter_processed_block_tree S.E
      duty.toHealing.toFG.toSG.toGoldfishStore duty.toHealing.s := by
    have hDprocessed' := WeakGoldfish.ancestorProcessed_of_voterProcessed
      (S := S) (rho := rho) (w := w) (s := s) (B := C)
      (adm := adm.toNamedAdmissibleCore) hw hCprocessed D hDC
    simpa only [duty] using hDprocessed'
  have hCdata := hCraw
  have hDdata := hDfull
  simp only [voter_candidate_tree, Protocol.get_filtered_block_tree,
    Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq] at hCdata hDdata
  obtain ⟨W, hWprocessed, hCW, hheight⟩ := hCdata.1.2
  have hDcandidate' : D ∈ voter_candidate_tree S.E duty.toHealing := by
    simp only [voter_candidate_tree, Protocol.get_filtered_block_tree_from,
      Protocol.viable_tree, Protocol.finalized_descendants,
      Protocol.viable, Finset.mem_filter, decide_eq_true_eq]
    exact ⟨⟨⟨hDprocessed, hDdata.1.1.2⟩, W, hWprocessed,
      Block.preceq_trans hDC hCW, hheight⟩, hDdata.2⟩
  simpa only [voterCandidateTreeAt, Internal.NamedRecoveryRead.voteDutyRead,
    NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
    Protocol.NamedStore.setClock, duty, voteDutyStore] using hDcandidate'

/-- The vote-duty frame with a comparable root. -/
def VoteDutyFrameAt' (S : Setup V) (rho : Run V) (M : Height) (d : Slot)
    (C : Block V) : Prop :=
  ∀ w ∈ rho.honest,
    (voteDutyStore S rho w d).h_max = M ∧
    (voteDutyStore S rho w d).h_j + 2 ≤ M ∧
    (Block.Preceq (Protocol.get_fg_root (voteDutyStore S rho w d).toHealing.toFG) C ∨
      Block.Preceq C (Protocol.get_fg_root (voteDutyStore S rho w d).toHealing.toFG))


/-- One-slot persistence of a cone with a thin head, comparable-root form.

design note (statement change, ledger row). As `SeedBoundaryConeLeadRun`'s
`coneAndThin_succ`: the cone is the named cone, the anchor premise is the
prepared vote anchor `voterAnchorAt`, and the band premise carries the named
head witness that `headThin_of_band` consumes. The comparable root goes into
`GoldfishConeVoteInputs'` and the step is `goldfishCone_step'`. earlier text,
byte-exact:

    theorem coneAndThin_succ'
        (S: Setup V) {rho: Run V} (adm: Admissible S rho)
        (hcom: HonestCommittees S rho.honest)
        (hfb: BelowOneThird S rho.honest)
        {M: Height} {s: Slot} {C: Block V} (hs: 0 < s)
        (hpost: S.E.t_GST ≤ Protocol.vote_time S.E s)
        (hhor: Protocol.confirmation_time S.E s ≤ rho.horizon)
        (hvotes: HonestVotesCone S rho s (fun X => Block.Preceq C X))
        (hthin: ThinHonestHeadAt S rho M s C)
        (hframe: VoteDutyFrameAt' S rho M (s + 1) C)
        (hanchor: ∀ w ∈ rho.honest,
          Block.compatible
            (healAnchor S.E S.hc (voteDutyStore S rho w (s + 1)).toHealing) C
              = true)
        (hband: ∀ w ∈ rho.honest,
          (voteDutyStore S rho w (s + 1)).h_max - 1 ≤
            (derived_state S.E S.cfg (voteDutyHead S rho w (s + 1))).h):
        HonestVotesCone S rho (s + 1) (fun X => Block.Preceq C X) ∧
          ThinHonestHeadAt S rho M (s + 1) C -/
theorem coneAndThin_succ'
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {s : Slot} {C : Block V} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hvotes : NamedHonestVotesCone S rho s (fun X => Block.Preceq C X))
    (hthin : ThinHonestHeadAt S rho M s C)
    (hframe : VoteDutyFrameAt' S rho M (s + 1) C)
    (hanchor : ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w (s + 1)) C = true)
    (hband : ∀ w ∈ rho.honest, ∃ Hn : NamedBlock V,
      Hn.erase = voterHeadAt S rho w (s + 1) ∧ RunBlock S rho Hn ∧
        (voteDutyStore S rho w (s + 1)).h_max - 1 ≤
          (Protocol.derive_named S.E S.cfg Hn).h) :
    NamedHonestVotesCone S rho (s + 1) (fun X => Block.Preceq C X) ∧
      ThinHonestHeadAt S rho M (s + 1) C := by
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
    apply le_trans (le_of_lt ?_) hhor
    rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E s]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  have hinputs : ∀ w ∈ rho.honest, GoldfishConeVoteInputs' S rho s C w := by
    intro w hw
    obtain ⟨hfrontier, hgate, hroot⟩ := hframe w hw
    refine { rootSide := ?_, anchor := hanchor w hw }
    rcases hroot with hrootC | hCroot
    · left
      have hfacts :=
        seedRelayVoteFacts S adm hsb hpost hhor hvotes hthin hw hfrontier hgate hrootC
      have hcandidate : C ∈ voterCandidateTreeAt S rho w (s + 1) := by
        simpa only [voterCandidateTreeAt, Internal.NamedRecoveryRead.voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
          voteDutyStore] using hfacts.1
      exact ⟨hrootC, hcandidate, votePathAt_of_candidate' S adm hw hcandidate⟩
    · exact Or.inr hCroot
  have hhead : ∀ w ∈ rho.honest, Block.Preceq C (voterHeadAt S rho w (s + 1)) :=
    fun w hw => goldfishCone_step' S adm hcom hs hpost hhor hvotes hw (hinputs w hw)
  have hcone : NamedHonestVotesCone S rho (s + 1) (fun X => Block.Preceq C X) := by
    intro w hw hwCommittee
    obtain ⟨H, hHerase, hHrun⟩ := seedVoteDutyHead_runBlock S adm hw (s + 1)
    refine ⟨H, ?_, hHrun, ?_⟩
    · rw [hHerase]
      exact hhead w hw
    · simpa only [hHerase, voteDutyHead] using
        seedVoteDutyHead_emits S adm hw (Nat.succ_pos s) hwCommittee hvoteHor
  refine ⟨hcone, ?_⟩
  have hpositive : 0 < ((S.E.committee (s + 1)) ∩ rho.honest).card := by
    have hc := hcom (s + 1)
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpositive
  have hwCommittee : w ∈ S.E.committee (s + 1) := (Finset.mem_inter.mp hw).1
  have hwHonest : w ∈ rho.honest := (Finset.mem_inter.mp hw).2
  obtain ⟨H, hHerase, hHrun, hHband⟩ := hband w hwHonest
  have hHemit : NamedRun.emits S rho w
      (.gfVote ⟨w, s + 1, H.erase.root⟩) (Protocol.vote_time S.E (s + 1)) := by
    simpa only [hHerase, voteDutyHead] using
      seedVoteDutyHead_emits S adm hwHonest (Nat.succ_pos s) hwCommittee hvoteHor
  refine ⟨H, ⟨w, hwHonest, hwCommittee, hHrun, hHemit⟩, ?_, ?_⟩
  · rw [hHerase]
    exact hhead w hwHonest
  · have hM := (hframe w hwHonest).1
    rw [hM] at hHband
    exact hHband

/-- Confirmation times are monotone in the slot. -/
private theorem confirmation_time_mono_slots'' (E : Env V) {a b : Slot}
    (hab : a ≤ b) :
    Protocol.confirmation_time E a ≤ Protocol.confirmation_time E b := by
  rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time E a,
    ← Protocol.vote_time_succ_add_delta_eq_confirmation_time E b]
  exact Int.add_le_add_right
    (Protocol.vote_time_mono_slots E (Nat.succ_le_succ hab)) _

/-- Iterated persistence, comparable-root form. -/
theorem coneAndThin_through'
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {s0 s1 : Slot} {C : Block V} (hs0 : 0 < s0)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s0)
    (hhor : Protocol.confirmation_time S.E s1 ≤ rho.horizon)
    (hbase : NamedHonestVotesCone S rho s0 (fun X => Block.Preceq C X) ∧
      ThinHonestHeadAt S rho M s0 C)
    (hframe : ∀ d : Slot, s0 < d → d ≤ s1 → VoteDutyFrameAt' S rho M d C)
    (hanchor : ∀ d : Slot, s0 < d → d ≤ s1 → ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w d) C = true)
    (hband : ∀ d : Slot, s0 < d → d ≤ s1 → ∀ w ∈ rho.honest,
      ∃ Hn : NamedBlock V, Hn.erase = voterHeadAt S rho w d ∧ RunBlock S rho Hn ∧
        (voteDutyStore S rho w d).h_max - 1 ≤
          (Protocol.derive_named S.E S.cfg Hn).h) :
    ∀ k : Slot, s0 ≤ k → k ≤ s1 →
      NamedHonestVotesCone S rho k (fun X => Block.Preceq C X) ∧
        ThinHonestHeadAt S rho M k C := by
  intro k hk0 hk1
  induction k, hk0 using Nat.le_induction with
  | base => exact hbase
  | succ k hk ih =>
    have hkle : k ≤ s1 := (Nat.le_succ k).trans hk1
    have hprev := ih hkle
    have hkpos : 0 < k := lt_of_lt_of_le hs0 hk
    have hpostK : S.E.t_GST ≤ Protocol.vote_time S.E k :=
      hpost.trans (Protocol.vote_time_mono_slots S.E hk)
    have hhorK : Protocol.confirmation_time S.E k ≤ rho.horizon :=
      (confirmation_time_mono_slots'' S.E hkle).trans hhor
    exact coneAndThin_succ' S adm hcom hfb hkpos hpostK hhorK hprev.1 hprev.2
      (hframe (k + 1) (Nat.lt_succ_of_le hk) hk1)
      (hanchor (k + 1) (Nat.lt_succ_of_le hk) hk1)
      (hband (k + 1) (Nat.lt_succ_of_le hk) hk1)

/-- Slot facts of one round: the slot after the opening is at or before the
round's last slot, which is before the next opening. -/
private theorem roundSlots_nat {o R : Nat} (hR : 2 ≤ R) :
    o + 1 ≤ o + R - 1 ∧ o + R - 1 < o + R ∧ 0 < o + R := by
  omega

private theorem openingSucc_le_boundary' (S : Setup V) (c : Round) :
    S.hc.opening_slot c + 1 ≤ S.hc.opening_slot (c + 1) - 1 := by
  have h : S.hc.opening_slot (c + 1) = S.hc.opening_slot c + S.hc.R := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.succ_mul c S.hc.R
  rw [h]
  exact (roundSlots_nat S.hc.R_ge_two).1


private theorem boundary_lt_openingSucc' (S : Setup V) (c : Round) :
    S.hc.opening_slot (c + 1) - 1 < S.hc.opening_slot (c + 1) := by
  have h : S.hc.opening_slot (c + 1) = S.hc.opening_slot c + S.hc.R := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.succ_mul c S.hc.R
  rw [h]
  exact (roundSlots_nat S.hc.R_ge_two).2.1

/-- The boundary cone and thin head of round `c`, comparable-root form. -/
theorem boundaryConeAndThin_of_baseCone'
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {c : Round} {D : Block V}
    (hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E (S.hc.opening_slot c + 1))
    (hhorNext : S.a (c + 1) ≤ rho.horizon)
    (hbase : NamedHonestVotesCone S rho (S.hc.opening_slot c + 1)
        (fun X => Block.Preceq D X) ∧
      ThinHonestHeadAt S rho M (S.hc.opening_slot c + 1) D)
    (hframe : ∀ d : Slot, S.hc.opening_slot c + 1 < d →
      d ≤ S.hc.opening_slot (c + 1) - 1 → VoteDutyFrameAt' S rho M d D)
    (hanchor : ∀ d : Slot, S.hc.opening_slot c + 1 < d →
      d ≤ S.hc.opening_slot (c + 1) - 1 → ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w d) D = true)
    (hband : ∀ d : Slot, S.hc.opening_slot c + 1 < d →
      d ≤ S.hc.opening_slot (c + 1) - 1 → ∀ w ∈ rho.honest,
      ∃ Hn : NamedBlock V, Hn.erase = voterHeadAt S rho w d ∧ RunBlock S rho Hn ∧
        (voteDutyStore S rho w d).h_max - 1 ≤
          (Protocol.derive_named S.E S.cfg Hn).h) :
    NamedHonestVotesCone S rho (S.hc.opening_slot (c + 1) - 1)
        (fun X => Block.Preceq D X) ∧
      ThinHonestHeadAt S rho M (S.hc.opening_slot (c + 1) - 1) D := by
  have hb := openingSucc_le_boundary' S c
  have hboundaryConf : Protocol.confirmation_time S.E
      (S.hc.opening_slot (c + 1) - 1) ≤ rho.horizon := by
    refine (confirmation_time_mono_slots'' S.E
      (le_of_lt (boundary_lt_openingSucc' S c))).trans ?_
    simpa only [Setup.a, Protocol.a_eq_confirmation_time] using hhorNext
  exact coneAndThin_through' S adm hcom hfb
    (Nat.succ_pos _) hpostVote hboundaryConf hbase hframe hanchor hband
    (S.hc.opening_slot (c + 1) - 1) hb le_rfl

/-- The round ceiling at `c + 1` from the base cone at the slot after round
`c`'s opening, comparable-root form. -/
theorem roundCeiling_succ_of_baseCone'
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {c : Round} {D W : NamedBlock V}
    (hpostAction : S.E.t_GST ≤ S.a c)
    (hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E (S.hc.opening_slot c + 1))
    (hhorNext : S.a (c + 1) ≤ rho.horizon)
    (hDrun : RunBlock S rho D) (hWrun : RunBlock S rho W)
    (hDW : Block.Preceq D.erase W.erase)
    (hWthin : M - 1 ≤ (Protocol.derive_named S.E S.cfg W).h)
    (hcarriers : ∀ v ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho v c) D.erase)
    (hbase : NamedHonestVotesCone S rho (S.hc.opening_slot c + 1)
        (fun X => Block.Preceq D.erase X) ∧
      ThinHonestHeadAt S rho M (S.hc.opening_slot c + 1) D.erase)
    (hframe : ∀ d : Slot, S.hc.opening_slot c + 1 < d →
      d ≤ S.hc.opening_slot (c + 1) - 1 → VoteDutyFrameAt' S rho M d D.erase)
    (hanchor : ∀ d : Slot, S.hc.opening_slot c + 1 < d →
      d ≤ S.hc.opening_slot (c + 1) - 1 → ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w d) D.erase = true)
    (hband : ∀ d : Slot, S.hc.opening_slot c + 1 < d →
      d ≤ S.hc.opening_slot (c + 1) - 1 → ∀ w ∈ rho.honest,
      ∃ Hn : NamedBlock V, Hn.erase = voterHeadAt S rho w d ∧ RunBlock S rho Hn ∧
        (voteDutyStore S rho w d).h_max - 1 ≤
          (Protocol.derive_named S.E S.cfg Hn).h)
    (hheadThin : ∀ X : NamedBlock V,
      NamedHonestHead S rho (S.hc.opening_slot (c + 1) - 1) X →
        M - 1 ≤ (Protocol.derive_named S.E S.cfg X).h)
    (hreg : RoundCeilingNextRegimeAt S rho M c) :
    ∃ B : NamedBlock V,
      RoundCeilingAt S rho M (c + 1) B ∧ Block.Preceq D.erase B.erase := by
  have hb := openingSucc_le_boundary' S c
  have hboundaryConf : Protocol.confirmation_time S.E
      (S.hc.opening_slot (c + 1) - 1) ≤ rho.horizon := by
    refine (confirmation_time_mono_slots'' S.E
      (le_of_lt (boundary_lt_openingSucc' S c))).trans ?_
    simpa only [Setup.a, Protocol.a_eq_confirmation_time] using hhorNext
  have hthrough := boundaryConeAndThin_of_baseCone' S adm hcom hfb hpostVote hhorNext
    hbase hframe hanchor hband
  have hpostBoundaryVote : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot (c + 1) - 1) :=
    hpostVote.trans (Protocol.vote_time_mono_slots S.E hb)
  exact roundCeiling_base_of_carrierFrontier S adm hcom hfb hpostAction
    hpostBoundaryVote hboundaryConf hDrun hWrun hDW hWthin hcarriers
    hthrough.1 hheadThin hreg

/-- The vote of the slot after the opening is at or before the round's action. -/
private theorem openingSuccVote_le_action' (S : Setup V) (q : Round) :
    Protocol.vote_time S.E (S.hc.opening_slot q + 1) ≤ S.a q := by
  have h := Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E
    (S.hc.opening_slot q)
  rw [Setup.a, Protocol.a_eq_confirmation_time, ← h]
  exact le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)

/-! ## Claim 1 at the second slot from a grade-2 block, without a common root
The honest voter `w` reads its own FG root at the duty. The root is finalized
and the grade-2 block `Q` has a band witness `W` above it, so the root is an
ancestor of `W` too (canonicity); hence root and `Q` are comparable. Above
`Q` the vote head is above the root, hence above `Q`. Below `Q` the previous
fresh-anchor argument runs unchanged, with the action-read root below the
duty-read root by monotonicity. -/


/-- A relayed band witness is in the receiver's tree and stamped before the
freeze. Local twin of `SeedBoundaryConeLeadRun.relayedWitness_mem_and_stamp`,
still blocked there; the two producers it composes are both available. -/
private theorem relayedWitness_mem'
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} {W : Block V} {freeze read : Time} (hle : freeze ≤ read)
    (h : W = Block.genesis ∨ AdmittedBefore S rho w W freeze) :
    W ∈ (rho.storeBeforeTime S w read).T ∧
      stampedBefore (rho.storeBeforeTime S w read).timestamp_block freeze W = true := by
  rcases h with hgen | hadmit
  · simpa only [hgen] using
      (Protocol.genesis_mem_and_stamp_storeBeforeTime S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed w read freeze)
  · exact Protocol.admittedBefore_mem_and_stamp_at S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hadmit hle

/-- A slot's vote instant is before the next slot's proposal. Local twin of
`SeedCanonicalAnchorRun.k5_voteTime_lt_nextProposal`, which is `private`. -/
private theorem voteTime_lt_nextProposal' (E : Env V) (s : Slot) :
    Protocol.vote_time E s < Protocol.proposal_time E (s + 1) := by
  simp only [Protocol.vote_time, Protocol.proposal_time, Env.t, slotStart]
  push_cast
  nlinarith [E.Δ_pos]

/-- The `.g1` and `.g2` grade domains of a round are at or before its `.g0`
domain, so `GradeRoundReady`'s horizon clause covers all three. -/
private theorem domain_g1_le_g0 (S : Setup V) (r : Round) :
    DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1 ≤ DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0 := by
  unfold DecoupledConsensusModel.Protocol.domain DecoupledConsensusModel.Protocol.Phase.domainOffset
  have h := S.E.Δ_pos
  linarith

private theorem domain_g2_le_g0 (S : Setup V) (r : Round) :
    DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2 ≤ DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0 := by
  unfold DecoupledConsensusModel.Protocol.domain DecoupledConsensusModel.Protocol.Phase.domainOffset
  have h := S.E.Δ_pos
  linarith

theorem secondSlotCone_of_grade2'
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {c : Round} (hc : 1 ≤ c)
    (hpost : S.E.t_GST ≤ S.a (c - 1))
    (hhor : S.a c ≤ rho.horizon)
    (hframe : GateOffFrameAt S rho M (c - 1) c)
    (hready : GradeRoundReady S rho c)
    {v : V} (hv : v ∈ rho.honest) {Q : Block V}
    (hQ : Internal.PhaseGrades.nodeQ2 S (actionReadAt S rho v c) c = some Q) :
    NamedHonestVotesCone S rho (S.hc.opening_slot c + 1) (fun X => Block.Preceq Q X) := by
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hpredLe : S.a (c - 1) ≤ S.a c := Assembly.a_mono S (Nat.sub_le c 1)
  have hpredLt : c - 1 < c := Nat.sub_lt hc Nat.one_pos
  have hvote1Action : Protocol.vote_time S.E (S.hc.opening_slot c + 1) ≤ S.a c :=
    openingSuccVote_le_action' S c
  have hpredVote1 : S.a (c - 1) ≤ Protocol.vote_time S.E (S.hc.opening_slot c + 1) := by
    have h1 := action_add_delta_le_openingProposal_of_round_lt S hpredLt
    have h2 : S.a (c - 1) ≤ Protocol.proposal_time S.E (S.hc.opening_slot c) :=
      (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h1
    exact h2.trans ((le_of_lt (Protocol.proposal_time_lt_vote_time S.E _)).trans
      (Protocol.vote_time_mono_slots S.E (Nat.le_succ _)))
  have hvote1Hor : Protocol.vote_time S.E (S.hc.opening_slot c + 1) ≤ rho.horizon :=
    hvote1Action.trans hhor
  have hΓ0Vote1 : S.hc.Γ_0 S.E.Δ c ≤ Protocol.vote_time S.E (S.hc.opening_slot c + 1) := by
    rw [Protocol.Γ_0_eq_proposal_time]
    exact (Protocol.proposal_time_mono S.E (Nat.le_succ _)).trans
      (le_of_lt (Protocol.proposal_time_lt_vote_time S.E _))
  have hfreezeVote : Protocol.view_freeze S.E (S.hc.opening_slot c) ≤
      Protocol.vote_time S.E (S.hc.opening_slot c + 1) :=
    le_of_lt (Protocol.view_freeze_lt_vote_time_succ S.E _)
  have hframeC : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a c)).h_j + 2 ≤ M ∧
        (rho.storeBeforeTime S w (S.a c)).h_max = M :=
    fun w hw => hframe (S.a c) hpredLe le_rfl w hw
  have hframeV1 : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (Protocol.vote_time S.E (S.hc.opening_slot c + 1))).h_j + 2 ≤ M ∧
        (rho.storeBeforeTime S w (Protocol.vote_time S.E (S.hc.opening_slot c + 1))).h_max = M :=
    fun w hw => hframe _ hpredVote1 hvote1Action w hw
  have hprevFrontier : ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (c - 1))).h_max = M :=
    fun u hu => (hframe (S.a (c - 1)) le_rfl hpredLe u hu).2
  have hcPos : 0 < c := Nat.succ_le_iff.mp hc
  have hG1v : namedG1At S rho v c Q :=
    namedG1At_of_nodeQ2 S adm hcPos hhor v hv Q hQ
  have hwindow : RelativeCarrierWindowAt S rho (c - 1) DecoupledConsensusModel.Protocol.Phase.g1 :=
    relativeCarrierWindowAt_of_gateOff S adm hfb hcPos hpost hprevFrontier
      (fun x hx => (hframeC x hx).2) (fun x hx => (hframeC x hx).1)
      ((domain_g1_le_g0 S c).trans hready.2)
  have hmajority : Internal.NamedOutageEntry.GradeFormingMajority S rho c :=
    gradeFormingMajority_of_admissible_belowOneThird S adm hfb hcPos
      ((domain_g2_le_g0 S c).trans hready.2) (by assumption)
  have hcarrier := namedG1At_preceq_honestPreviousActionCarrier S
    adm.toNamedAdmissibleCore hc hwindow hmajority hv hG1v
  have hround1 : S.hc.round_of (S.hc.opening_slot c + 1) = c :=
    seedEntryRoundOf S le_rfl (openingSucc_le_boundary' S c)
  have hnextOpening : Protocol.vote_time S.E (S.hc.opening_slot c + 1) ≤
      DecoupledConsensusModel.Protocol.opening S.E S.hc (c + 1) := by
    have hlt : S.hc.opening_slot c + 1 < S.hc.opening_slot (c + 1) := by
      have h : S.hc.opening_slot (c + 1) = S.hc.opening_slot c + S.hc.R := by
        unfold Protocol.HealConfig.opening_slot
        exact Nat.succ_mul c S.hc.R
      have h1R : 1 < S.hc.R := lt_of_lt_of_le Nat.one_lt_two S.hc.R_ge_two
      rw [h]
      exact Nat.add_lt_add_left h1R _
    have hstep : Protocol.proposal_time S.E (S.hc.opening_slot c + 1 + 1) ≤
        Protocol.proposal_time S.E (S.hc.opening_slot (c + 1)) :=
      Protocol.proposal_time_mono S.E (Nat.succ_le_of_lt hlt)
    have hopen : DecoupledConsensusModel.Protocol.opening S.E S.hc (c + 1) =
        Protocol.proposal_time S.E (S.hc.opening_slot (c + 1)) := rfl
    rw [hopen]
    exact (le_of_lt (voteTime_lt_nextProposal' S.E (S.hc.opening_slot c + 1))).trans hstep
  intro w hw hwCommittee
  have hM : 1 ≤ M := by
    have h2 : 2 ≤ M := (Nat.le_add_left 2 _).trans (hframeC w hw).1
    exact le_trans (by decide) h2
  obtain ⟨W, hWrun, hQW, hWh, hrelay⟩ := g1_bandWitness_relayed' S adm hfb hc hpost hhor
    hprevFrontier hcarrier hw (Nat.le_succ _) hvote1Hor (hframeV1 w hw).1
  simp only [Nat.succ_sub_one] at hrelay
  -- the duty-read root is finalized, hence below the band witness `W`
  have hrootV1 : Protocol.get_fg_root
      (rho.storeBeforeTime S w (Protocol.vote_time S.E (S.hc.opening_slot c + 1))).toHealing.toFG
        = (rho.storeBeforeTime S w (Protocol.vote_time S.E (S.hc.opening_slot c + 1))).core.F :=
    fgRoot_eq_F_of_frame (hframeV1 w hw).1 (hframeV1 w hw).2
  have hFW : Block.Preceq
      (rho.storeBeforeTime S w
        (Protocol.vote_time S.E (S.hc.opening_slot c + 1))).core.F W.erase :=
    finalizedRoot_preceq_of_band S adm hfb hw (hframeV1 w hw).1 hWrun hWh
  obtain ⟨H, hHerase, hHrun⟩ :=
    seedVoteDutyHead_runBlock S adm hw (S.hc.opening_slot c + 1)
  have hemit : NamedRun.emits S rho w
      (.gfVote ⟨w, S.hc.opening_slot c + 1, H.erase.root⟩)
      (Protocol.vote_time S.E (S.hc.opening_slot c + 1)) := by
    simpa only [hHerase, voteDutyHead] using
      seedVoteDutyHead_emits S adm hw (Nat.succ_pos _) hwCommittee hvote1Hor
  refine ⟨H, ?_, hHrun, hemit⟩
  rw [hHerase]
  rcases Block.preceq_linear hFW hQW with hFQ | hQF
  · -- root below `Q`: the relative selection reaches the duty head
    have hWduty := (relayedWitness_mem' S adm hfreezeVote hrelay).1
    have hactiveDuty : Q ∈ Protocol.get_filtered_block_tree
        (rho.storeBeforeTime S w
          (Protocol.vote_time S.E (S.hc.opening_slot c + 1))).toHealing.toFG :=
      frontierAncestor_filtered_of_gateOff S adm hsb hw hvote1Hor hWduty rfl hWrun hQW hWh hM
        (hframeV1 w hw).2 (hframeV1 w hw).1 (by rw [hrootV1]; exact hFQ)
    have hactiveRead : Q ∈ Internal.PhaseGrades.filteredTree
        (Internal.NamedRecoveryRead.voteDutyRead S rho w (S.hc.opening_slot c + 1)) := by
      simpa only [Internal.PhaseGrades.filteredTree,
        Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock] using hactiveDuty
    exact preceq_voterHeadAt_of_nodeQ2_activeAtDutyRead S adm hsb hcPos
      (Nat.le_succ _) hround1 hnextOpening hvote1Hor hready.1 hready.2 hv hw hQ
      hactiveRead
  · -- `Q` below the root: the head is above its own root
    have hQroot : Block.Preceq Q (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w
          (S.hc.opening_slot c + 1)).st.core.toHealing.toFG) := by
      change Block.Preceq Q (Protocol.get_fg_root
        (rho.storeBeforeTime S w
          (Protocol.vote_time S.E (S.hc.opening_slot c + 1))).toHealing.toFG)
      rw [hrootV1]
      exact hQF
    exact Block.preceq_trans hQroot
      (fgRoot_preceq_voterHeadAt S rho w (S.hc.opening_slot c + 1))

/-! ## The boundary adoption from the frame alone
The three facts that the common root supplies are now stated as one
per-round discharge record: Claim 1 at the second slot, anchor–carrier
compatibility at every later duty, and the band reach of every duty head.
Each is derived from canonicity elsewhere; here the boundary cone, the
ceiling and the adoption follow from the record and the gate-off frame. -/

/-- A round's action is at or before the vote of the second slot after its
opening. -/
private theorem action_le_openingSuccSuccVote' (S : Setup V) (q : Round) :
    S.a q ≤ Protocol.vote_time S.E (S.hc.opening_slot q + 2) := by
  rw [Setup.a, Protocol.a_eq_confirmation_time]
  simp only [Protocol.confirmation_time, Protocol.vote_time, Env.t, slotStart]
  have hΔ : (0 : Time) ≤ S.E.Δ := le_of_lt S.E.Δ_pos
  have hcast : ((S.hc.opening_slot q + 2 : Nat) : Time) =
      (S.hc.opening_slot q : Time) + 2 := by push_cast; ring
  rw [hcast]
  have hexpand : 4 * S.E.Δ * ((S.hc.opening_slot q : Time) + 2) + S.E.Δ =
      4 * S.E.Δ * (S.hc.opening_slot q : Time) + 9 * S.E.Δ := by ring
  rw [hexpand]
  have h69 : (6 : Time) * S.E.Δ ≤ 9 * S.E.Δ := by
    have := Int.mul_le_mul_of_nonneg_right (show (6 : Time) ≤ 9 by decide) hΔ
    simpa using this
  exact Int.add_le_add_left h69 _

private theorem coverWindow_nat' {c : Nat} (hc : 1 ≤ c) :
    c - 1 ≤ c ∧ c ≤ c + 1 ∧ c ≤ c + 2 ∧ c + 1 ≤ c + 2 ∧ c - 1 ≤ c + 2 ∧
      c - 1 < c ∧ c - 1 + 1 = c ∧ c - 1 + 2 ≤ c + 1 ∧ 0 < c := by
  omega

private theorem coverSlots_nat' {o o' d : Nat} (ho' : o + 2 ≤ o')
    (hlo : o + 1 < d) (hhi : d ≤ o' - 1) :
    o + 2 ≤ d ∧ o + 1 ≤ d ∧ d ≤ o' - 1 ∧ 0 < o' - 1 ∧ o' - 1 ≤ o' ∧
      0 < o + 1 ∧ o + 1 ≤ o' - 1 := by
  omega

/-- The per-round facts that replace the common root. -/
structure SeedRoundDischargeAt (S : Setup V) (rho : Run V) (M : Height)
    (c : Round) : Prop where
  /-- Claim 1 at the second slot: every honest vote of slot `opening_slot c + 1`
  is above every honest round-`c` action SG block. -/
  claim1 : ∀ v ∈ rho.honest,
    NamedHonestVotesCone S rho (S.hc.opening_slot c + 1)
      (fun X => Block.Preceq (actionSGBlockAt S rho v c) X)
  /-- At every later duty of the round, every honest vote anchor is compatible
  with every honest round-`c` action SG block. -/
  anchorCompat : ∀ d : Slot, S.hc.opening_slot c + 1 < d →
    d ≤ S.hc.opening_slot (c + 1) - 1 → ∀ w ∈ rho.honest, ∀ v ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w d)
        (actionSGBlockAt S rho v c) = true
  /-- Every honest vote-duty head of the round is a named run block that
  reaches the band. -/
  headBand : ∀ d : Slot, S.hc.opening_slot c ≤ d →
    d ≤ S.hc.opening_slot (c + 1) - 1 → ∀ w ∈ rho.honest,
      ∃ Hn : NamedBlock V, Hn.erase = voterHeadAt S rho w d ∧ RunBlock S rho Hn ∧
        M - 1 ≤ (Protocol.derive_named S.E S.cfg Hn).h

/-- A finalized root at a gate-off read is comparable with any block that has
a band witness. -/
theorem fgRoot_comparable_of_bandWitness
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {w : V} (hw : w ∈ rho.honest) {t : Time} {M : Height}
    (hgate : (rho.storeBeforeTime S w t).h_j + 2 ≤ M)
    (hmax : (rho.storeBeforeTime S w t).h_max = M)
    {D : Block V} {W : NamedBlock V} (hWrun : RunBlock S rho W)
    (hDW : Block.Preceq D W.erase)
    (hWh : M - 1 ≤ (Protocol.derive_named S.E S.cfg W).h) :
    Block.Preceq (Protocol.get_fg_root (rho.storeBeforeTime S w t).toHealing.toFG) D ∨
      Block.Preceq D (Protocol.get_fg_root (rho.storeBeforeTime S w t).toHealing.toFG) := by
  rw [fgRoot_eq_F_of_frame hgate hmax]
  exact Block.preceq_linear (finalizedRoot_preceq_of_band S adm hfb hw hgate hWrun hWh) hDW

/-- **The boundary cone of round `c` and the round ceiling at `c + 1`, from
the gate-off frame and the round's discharge record.** -/
theorem seedBoundaryAdoption_of_discharge
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {c : Round} (hc : 1 ≤ c)
    (hpost : S.E.t_GST ≤ S.a (c - 1))
    (hhor : S.a (c + 2) ≤ rho.horizon)
    (hframe : GateOffFrameAt S rho M (c - 1) (c + 2))
    (hdis : SeedRoundDischargeAt S rho M c) :
    SeedBoundaryAdoptionAt S rho M c ∧
      ∃ B : NamedBlock V, RoundCeilingAt S rho M (c + 1) B := by
  obtain ⟨hpredLe, hcSucc, hcSucc2, hsucc12, hpred2, hpredLt, hpredSucc,
    hpred2Succ, hcPos⟩ := coverWindow_nat' hc
  let o := S.hc.opening_slot c
  let o' := S.hc.opening_slot (c + 1)
  have hoo' : o + 2 ≤ o' := by
    change S.hc.opening_slot c + 2 ≤ S.hc.opening_slot (c + 1)
    unfold Protocol.HealConfig.opening_slot
    have hR : 2 ≤ S.hc.R := S.hc.R_ge_two
    rw [Nat.succ_mul]
    exact Nat.add_le_add_left hR _
  -- time facts
  have haPredC : S.a (c - 1) ≤ S.a c := Assembly.a_mono S hpredLe
  have haCSucc : S.a c ≤ S.a (c + 1) := Assembly.a_mono S hcSucc
  have haCSucc2 : S.a c ≤ S.a (c + 2) := Assembly.a_mono S hcSucc2
  have haSucc12 : S.a (c + 1) ≤ S.a (c + 2) := Assembly.a_mono S hsucc12
  have hpostC : S.E.t_GST ≤ S.a c := hpost.trans haPredC
  have hhorC : S.a c ≤ rho.horizon := haCSucc2.trans hhor
  have hhorC1 : S.a (c + 1) ≤ rho.horizon := haSucc12.trans hhor
  have hpredVote : S.a (c - 1) ≤ Protocol.vote_time S.E (o + 1) := by
    have h1 := action_add_delta_le_openingProposal_of_round_lt S hpredLt
    have h2 : S.a (c - 1) ≤ Protocol.proposal_time S.E o :=
      (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h1
    exact h2.trans ((le_of_lt (Protocol.proposal_time_lt_vote_time S.E o)).trans
      (Protocol.vote_time_mono_slots S.E (Nat.le_succ o)))
  have hvoteSuccAction : Protocol.vote_time S.E (o + 1) ≤ S.a c :=
    openingSuccVote_le_action' S c
  have hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E (o + 1) :=
    hpost.trans hpredVote
  have hvoteSuccHor : Protocol.vote_time S.E (o + 1) ≤ rho.horizon :=
    hvoteSuccAction.trans hhorC
  have hframeC : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a c)).h_j + 2 ≤ M ∧
        (rho.storeBeforeTime S w (S.a c)).h_max = M :=
    fun w hw => hframe (S.a c) haPredC haCSucc2 w hw
  have hfrontierC : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a c)).h_max = M :=
    fun w hw => (hframeC w hw).2
  have hvoteLeNext : ∀ d : Slot, d ≤ o' - 1 →
      Protocol.vote_time S.E d ≤ S.a (c + 1) := by
    intro d hhi
    have h1 : Protocol.vote_time S.E d ≤ Protocol.vote_time S.E (o' - 1) :=
      Protocol.vote_time_mono_slots S.E hhi
    have h2 : Protocol.vote_time S.E (o' - 1) ≤
        Protocol.confirmation_time S.E (o' - 1) :=
      Protocol.vote_time_le_confirmation_time S.E _
    have h3 : Protocol.confirmation_time S.E (o' - 1) ≤
        Protocol.confirmation_time S.E o' :=
      confirmation_time_mono_slots'' S.E (Nat.sub_le o' 1)
    have h4 : Protocol.confirmation_time S.E o' = S.a (c + 1) := by
      rw [Setup.a, Protocol.a_eq_confirmation_time]
    exact h1.trans (h2.trans (h3.trans (le_of_eq h4)))
  -- the band reach of every duty head, in the store-frontier shape
  have hbandAt : ∀ d : Slot, o ≤ d → d ≤ o' - 1 → ∀ w ∈ rho.honest,
      ∃ Hn : NamedBlock V, Hn.erase = voterHeadAt S rho w d ∧ RunBlock S rho Hn ∧
        (voteDutyStore S rho w d).h_max - 1 ≤
          (Protocol.derive_named S.E S.cfg Hn).h := by
    intro d hlo hhi w hw
    have hvoteLo : S.a (c - 1) ≤ Protocol.vote_time S.E d := by
      have h1 := action_add_delta_le_openingProposal_of_round_lt S hpredLt
      exact (((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h1).trans
        (le_of_lt (Protocol.proposal_time_lt_vote_time S.E o))).trans
        (Protocol.vote_time_mono_slots S.E hlo)
    have hfrontD : (voteDutyStore S rho w d).h_max = M := by
      simpa only [voteDutyStore, voteStore, tickStore] using
        (hframe _ hvoteLo ((hvoteLeNext d hhi).trans haSucc12) w hw).2
    obtain ⟨Hn, hHe, hHr, hHb⟩ := hdis.headBand d hlo hhi w hw
    exact ⟨Hn, hHe, hHr, by rw [hfrontD]; exact hHb⟩
  -- one chain, the deepest carrier and its witness
  have hchain : HonestActionCarriersOneChainAt S rho c :=
    honestActionCarriersOneChainAt_of_secondSlotCone S adm hcom hdis.claim1
  obtain ⟨D, hD⟩ :=
    exists_deepestActionCarrierCeiling S adm hcom hfrontierC hchain
  obtain ⟨vD, hvD, hDeq, W, -, hDW, hWrun, hWthin⟩ := hD.sourceAndWitness
  obtain ⟨Dn, hDnErase, hDrun⟩ := hD.run
  have hcarriers : ∀ v ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho v c) D := hD.previousCarriers
  -- the base cone at `o + 1`
  have hcone : NamedHonestVotesCone S rho (o + 1) (fun X => Block.Preceq D X) := by
    rw [← hDeq]
    exact hdis.claim1 vD hvD
  have hthin : ThinHonestHeadAt S rho M (o + 1) D := by
    have hpositive : 0 < ((S.E.committee (o + 1)) ∩ rho.honest).card := by
      have hc := hcom (o + 1)
      omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hpositive
    have hwCommittee : w ∈ S.E.committee (o + 1) := (Finset.mem_inter.mp hw).1
    have hwHonest : w ∈ rho.honest := (Finset.mem_inter.mp hw).2
    obtain ⟨X, hDX, hXrun, hXemit⟩ := hcone w hwHonest hwCommittee
    have hhead : NamedHonestHead S rho (o + 1) X :=
      ⟨w, hwHonest, hwCommittee, hXrun, hXemit⟩
    refine ⟨X, hhead, hDX, ?_⟩
    refine headThin_of_band S adm (Nat.succ_pos o) hvoteSuccHor ?_
      (fun u hu => hbandAt (o + 1) (Nat.le_succ o) (openingSucc_le_boundary' S c) u hu)
      X hhead
    intro u hu
    have := (hframe (Protocol.vote_time S.E (o + 1)) hpredVote
      (hvoteSuccAction.trans haCSucc2) u hu).2
    simpa only [voteDutyStore, voteStore, tickStore] using this
  -- the per-duty binders inside round `c`
  have hduty : ∀ d : Slot, o + 1 < d → d ≤ o' - 1 →
      S.a c ≤ Protocol.vote_time S.E d ∧
        Protocol.vote_time S.E d ≤ S.a (c + 1) := by
    intro d hlo hhi
    obtain ⟨hd2, -, -, -, -, -, -⟩ := coverSlots_nat' hoo' hlo hhi
    exact ⟨(action_le_openingSuccSuccVote' S c).trans
      (Protocol.vote_time_mono_slots S.E hd2), hvoteLeNext d hhi⟩
  have hframeDuty : ∀ d : Slot, o + 1 < d → d ≤ o' - 1 →
      VoteDutyFrameAt' S rho M d D := by
    intro d hlo hhi w hw
    obtain ⟨hlo', hhi'⟩ := hduty d hlo hhi
    have h := hframe _ (haPredC.trans hlo') (hhi'.trans haSucc12) w hw
    have hcmp := fgRoot_comparable_of_bandWitness S adm hfb hw h.1 h.2 hWrun hDW hWthin
    refine ⟨?_, ?_, ?_⟩
    · simpa only [voteDutyStore, voteStore, tickStore] using h.2
    · simpa only [voteDutyStore, voteStore, tickStore] using h.1
    · simpa only [voteDutyStore, voteStore, tickStore] using hcmp
  have hanchorDuty : ∀ d : Slot, o + 1 < d → d ≤ o' - 1 → ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w d) D = true := by
    intro d hlo hhi w hw
    rw [← hDeq]
    exact hdis.anchorCompat d hlo hhi w hw vD hvD
  have hbandDuty : ∀ d : Slot, o + 1 < d → d ≤ o' - 1 → ∀ w ∈ rho.honest,
      ∃ Hn : NamedBlock V, Hn.erase = voterHeadAt S rho w d ∧ RunBlock S rho Hn ∧
        (voteDutyStore S rho w d).h_max - 1 ≤
          (Protocol.derive_named S.E S.cfg Hn).h :=
    fun d hlo hhi w hw => hbandAt d ((Nat.le_succ o).trans (le_of_lt hlo)) hhi w hw
  have hheadThin : ∀ X : NamedBlock V, NamedHonestHead S rho (o' - 1) X →
      M - 1 ≤ (Protocol.derive_named S.E S.cfg X).h := by
    have hb := openingSucc_le_boundary' S c
    have hboundaryVote : Protocol.vote_time S.E (o' - 1) ≤ S.a (c + 1) :=
      hvoteLeNext (o' - 1) le_rfl
    refine headThin_of_band S adm (Nat.lt_of_lt_of_le (Nat.succ_pos o) hb)
      (hboundaryVote.trans hhorC1) ?_
      (fun u hu => hbandAt (o' - 1) ((Nat.le_succ o).trans (openingSucc_le_boundary' S c))
        le_rfl u hu)
    intro u hu
    have := (hframe (Protocol.vote_time S.E (o' - 1))
      (hpredVote.trans (Protocol.vote_time_mono_slots S.E hb))
      (hboundaryVote.trans haSucc12) u hu).2
    simpa only [voteDutyStore, voteStore, tickStore] using this
  have hreg : RoundCeilingNextRegimeAt S rho M c :=
    regime_of_gateOffFrame S adm hfb hpostC hhor
      (fun read hlo hhi w hw => hframe read (haPredC.trans hlo) hhi w hw)
  obtain ⟨B, hB, -⟩ := roundCeiling_succ_of_baseCone' S adm hcom hfb hpostC hpostVote
    hhorC1 hDrun hWrun (by rw [hDnErase]; exact hDW)
    hWthin (by rw [hDnErase]; exact hcarriers)
    (by rw [hDnErase]; exact ⟨hcone, hthin⟩)
    (by rw [hDnErase]; exact hframeDuty)
    (by rw [hDnErase]; exact hanchorDuty)
    hbandDuty hheadThin hreg
  have hboundary := boundaryConeAndThin_of_baseCone' S adm hcom hfb hpostVote hhorC1
    ⟨hcone, hthin⟩ hframeDuty hanchorDuty hbandDuty
  have hseedAdoption : SeedBoundaryAdoptionAt S rho M c :=
    { headThin := hheadThin
      entry := ⟨Dn, hDrun, ⟨W, hWrun, by rw [hDnErase]; exact hDW, hWthin⟩,
        by rw [hDnErase]; exact hcarriers, ?entryBelow⟩ }
  · exact ⟨hseedAdoption, B, hB⟩
  case entryBelow =>
    intro X hX
    obtain ⟨x, hxHonest, hxCommittee, hXrun, hXemit⟩ := hX
    rw [hDnErase]
    exact honestHead_preceq_of_cone S adm hboundary.1 X.erase
      ⟨x, hxHonest, hxCommittee, ⟨X, rfl, hXrun⟩, hXemit⟩

/-- One named transition never lowers the height: it either keeps it or raises
it by one (`transition_height_entry_cases`). -/
private theorem named_transition_h_ge (E : Env V)
    (cfg : Protocol.HeightConfig) (st : Protocol.ChainState V)
    (B : NamedBlock V) :
    st.h ≤ (Protocol.named_transition E cfg st B).h := by
  rcases Proofs.NamedEntryHeight.transition_height_entry_cases E cfg st B with
    ⟨h, -⟩ | ⟨h, -⟩
  · exact le_of_eq h.symm
  · rw [h]
    exact Nat.le_succ _

/-- The named derivation's height never falls along the named parent. -/
private theorem derive_named_h_parent_le (S : Setup V) (P : NamedBlock V) :
    (Protocol.derive_named S.E S.cfg P.parent).h ≤
      (Protocol.derive_named S.E S.cfg P).h := by
  cases P with
  | genesis => exact le_rfl
  | node p s root votes support rows proposer =>
    have hne : (NamedBlock.node p s root votes support rows proposer) ≠ .genesis := by
      nofun
    rw [Proofs.BlockProcessingDefaults.derive_named_of_not_genesis S.E S.cfg _ hne]
    exact named_transition_h_ge S.E S.cfg _ _

/-- **The opening adoption at a carrier round `c + 1`** from round `c`'s
discharge record. -/
theorem gateOffOpeningAdoption_succ_of_discharge
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {c : Round} (hc : 1 ≤ c)
    (hpost : S.E.t_GST ≤ S.a (c - 1))
    (hhor : S.a (c + 2) ≤ rho.horizon)
    (hframe : GateOffFrameAt S rho M (c - 1) (c + 2))
    (hdis : SeedRoundDischargeAt S rho M c)
    (hcarrier : ProposerCarrierAt S rho (c + 1)) :
    ∃ P : NamedBlock V, NamedGateOffOpeningWindowAt S rho M (c + 1) P ∧
      GateOffOpeningAdoption S rho (c + 1) := by
  obtain ⟨-, B, hB⟩ := seedBoundaryAdoption_of_discharge S adm hcom hfb hc hpost hhor
    hframe hdis
  have hpred2Succ : c - 1 + 2 ≤ c + 1 := (coverWindow_nat' hc).2.2.2.2.2.2.2.1
  obtain ⟨P, hP⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot (c + 1))
  have hwindowNamed := gateOffOpeningWindow_of_window S adm hfb (base := c - 1) hpost
    hpred2Succ hhor hcarrier.1 hP (fun read hlo hhi w hw => hframe read hlo hhi w hw)
  have hpredLe : S.a (c - 1) ≤ S.a c := Assembly.a_mono S (Nat.sub_le c 1)
  have hcLe2 : S.a c ≤ S.a (c + 2) :=
    Assembly.a_mono S ((Nat.le_succ c).trans (Nat.le_succ (c + 1)))
  have hprevFrontier : ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (c + 1 - 1))).h_max = M := by
    intro u hu
    exact (hframe (S.a c) hpredLe hcLe2 u hu).2
  have hcutLo : S.a (c + 1) ≤ S.hc.Γ_neg1 S.E.Δ (c + 1 + 1) :=
    (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
      (action_add_delta_le_next_Γ_neg1 S (c + 1))
  have hcutHi : S.hc.Γ_neg1 S.E.Δ (c + 1 + 1) ≤ S.a (c + 2) :=
    le_of_lt (next_Γ_neg1_lt_action S (c + 1))
  have hcutFrame : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.hc.Γ_neg1 S.E.Δ (c + 1 + 1))).h_max = M ∧
        (rho.storeBeforeTime S w (S.hc.Γ_neg1 S.E.Δ (c + 1 + 1))).h_j + 2 ≤ M := by
    intro w hw
    have h := hframe _
      ((hpredLe.trans (Assembly.a_mono S (Nat.le_succ c))).trans hcutLo) hcutHi w hw
    exact ⟨h.2, h.1⟩
  exact ⟨P, hwindowNamed,
    gateOff_openingLifecycle_of_roundCeiling S adm hcom hfb hcarrier hB hwindowNamed
      hprevFrontier
      (seedOpeningProposal_nextActiveDomain S adm hfb hcarrier hwindowNamed
        hcutFrame)⟩

/-- The band cover at a carrier round `c + 1` from round `c`'s discharge
record. -/
theorem seedBandCarrierCover_succ_of_discharge
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {c : Round} (hc : 1 ≤ c)
    (hpost : S.E.t_GST ≤ S.a (c - 1))
    (hhor : S.a (c + 2) ≤ rho.horizon)
    (hframe : GateOffFrameAt S rho M (c - 1) (c + 2))
    (hdis : SeedRoundDischargeAt S rho M c)
    (hcarrier : ProposerCarrierAt S rho (c + 1)) :
    SeedBandCarrierCoverAt S rho M (c + 1) := by
  obtain ⟨P, hwindow, hadoption⟩ := gateOffOpeningAdoption_succ_of_discharge S adm hcom
    hfb hc hpost hhor hframe hdis hcarrier
  exact seedBandCarrierCover_of_adoption_window S hwindow.proposal
    (hwindow.parentHeight.trans (derive_named_h_parent_le S P)) hadoption

/-! ## The height-progress seed from the per-round discharge -/


/-- The per-round discharge record holds at every round at least three actions
into a gate-off window that has three more actions inside the horizon.:
the round offset is ` + 2 ≤ c` rather than ` ≤ c - 1`, so that the round's
open follows from the seed's own post-GST base round; the adoption route
already enters at `base + 3 ≤ q`, so both call sites have the slack. -/
def SeedDischargeFrom (S : Setup V) (rho : Run V) (r0 : Round) : Prop :=
  ∀ (M : Height) (base c : Round), r0 ≤ base → 1 ≤ c → base + 3 ≤ c →
    S.E.t_GST ≤ S.a (c - 1) → S.a (c + 2) ≤ rho.horizon →
    GateOffFrameAt S rho M (base + 1) (c + 2) → SeedRoundDischargeAt S rho M c

private theorem entry_nat' {base q : Nat} (hq : base + 4 ≤ q) :
    1 ≤ q ∧ 1 ≤ q - 1 ∧ base + 1 ≤ q - 1 ∧ base + 1 ≤ q - 1 - 1 ∧ base ≤ q - 1 ∧
      base ≤ q - 1 - 1 ∧ q - 1 + 1 = q ∧ q - 1 + 2 ≤ q + 2 ∧
      base + 3 ≤ q ∧ base + 3 ≤ q - 1 := by
  omega


/-! ## The three tiers of an honest round action's SG target

`get_sg_vote` returns the deepest clear block between the anchor and the live
confirmation, else the selected grade-2 block, else the anchor itself
(`get_sg_root`: the fresh anchor when one exists in the filtered tree, else the
FG root). The first two tiers and the root case of the third are covered by
canonicity; the anchor case of the third tier needs no grade-2 block in the
raw tree, which never happens post-GST. -/


/-- **The tiers of an honest round action's SG target** (row Q31). The
selector is `get_sg_vote_with` over the prepared cache, so the tiers are stated
over the action read's own frame: the deepest clear block between the anchor
and the live confirmation, else the selected candidate `nodeQ2`, else (with no
candidate but a raw grade-2 block in the frame) the FG root, else the anchor.
Proved by the row `Q31_actionSGBlock_tiers`. -/
theorem actionSGBlockAt_tiers (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    letI n := actionReadAt S rho v r
    letI A := Internal.PhaseGrades.nodeAnchor S n r
    (Block.Preceq A (actionSGBlockAt S rho v r) ∧
      Block.Preceq (actionSGBlockAt S rho v r) n.st.core.live_confirmed ∧
      Internal.PhaseGrades.nodeClear S n r (actionSGBlockAt S rho v r) = true) ∨
    (∃ Q, Internal.PhaseGrades.nodeQ2 S n r = some Q ∧
      actionSGBlockAt S rho v r = Q) ∨
    (Internal.PhaseGrades.nodeQ2 S n r = none ∧ Internal.PhaseGrades.nodeRawG2 S n r ∧
      actionSGBlockAt S rho v r =
        Protocol.get_fg_root n.st.core.toHealing.toFG) ∨
    (Internal.PhaseGrades.nodeQ2 S n r = none ∧
      ¬ Internal.PhaseGrades.nodeRawG2 S n r ∧ actionSGBlockAt S rho v r = A) :=
  Proofs.HealingLemmas.Rows.q31_actionsgblock_tiers S rho v r

#print axioms actionSGBlockAt_tiers

/-- **The tiers with the anchor fallback excluded.** A raw grade-2 root in the
action read's frame kills the fourth arm, leaving the three the safety strand
consumes: the clear walk, the selected candidate, or the read's FG root. -/
theorem actionSGBlockAt_tiers_of_rawG2 (S : Setup V) (rho : Run V) (v : V) (r : Round)
    (hraw : Internal.PhaseGrades.nodeRawG2 S (actionReadAt S rho v r) r) :
    letI n := actionReadAt S rho v r
    letI A := Internal.PhaseGrades.nodeAnchor S n r
    (Block.Preceq A (actionSGBlockAt S rho v r) ∧
      Block.Preceq (actionSGBlockAt S rho v r) n.st.core.live_confirmed ∧
      Internal.PhaseGrades.nodeClear S n r (actionSGBlockAt S rho v r) = true) ∨
    (∃ Q, Internal.PhaseGrades.nodeQ2 S n r = some Q ∧
      actionSGBlockAt S rho v r = Q) ∨
    actionSGBlockAt S rho v r =
      Protocol.get_fg_root n.st.core.toHealing.toFG := by
  rcases actionSGBlockAt_tiers S rho v r with h | h | ⟨-, -, h⟩ | ⟨-, hno, -⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact absurd hraw hno

#print axioms actionSGBlockAt_tiers_of_rawG2


/-! ## Claim 1 at the second slot, tier by tier, from the band reach -/

/-- A target below an honest finalized root read at the round action is below
every honest vote head of the slot after the opening, provided those heads
reach the band. -/
theorem secondSlotCone_of_rootBelow'
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {c : Round}
    (hhor : S.a c ≤ rho.horizon)
    (hframe : GateOffFrameAt S rho M (c - 1) c)
    (hband : ∀ w ∈ rho.honest, ∃ Hn : NamedBlock V,
      Hn.erase = voterHeadAt S rho w (S.hc.opening_slot c + 1) ∧ RunBlock S rho Hn ∧
        M - 1 ≤ (Protocol.derive_named S.E S.cfg Hn).h)
    {v : V} (hv : v ∈ rho.honest) {T : Block V}
    (hT : Block.Preceq T (rho.storeBeforeTime S v (S.a c)).core.F) :
    NamedHonestVotesCone S rho (S.hc.opening_slot c + 1) (fun X => Block.Preceq T X) := by
  have hpredLe : S.a (c - 1) ≤ S.a c := Assembly.a_mono S (Nat.sub_le c 1)
  have hvote1Hor : Protocol.vote_time S.E (S.hc.opening_slot c + 1) ≤ rho.horizon :=
    (openingSuccVote_le_action' S c).trans hhor
  intro w hw hwCommittee
  obtain ⟨H, hHerase, hHrun, hHband⟩ := hband w hw
  refine ⟨H, ?_, hHrun, ?_⟩
  · exact Block.preceq_trans hT
      (finalizedRoot_preceq_of_band S adm hfb hv
        (hframe (S.a c) hpredLe le_rfl v hv).1 hHrun hHband)
  · simpa only [hHerase, voteDutyHead] using
      seedVoteDutyHead_emits S adm hw (Nat.succ_pos _) hwCommittee hvote1Hor

/-- **Tier 3, root case (K4).** A target equal to the action store's FG root
is below every honest vote head of the slot after the opening. -/
theorem secondSlotCone_of_rootTarget'
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {c : Round}
    (hhor : S.a c ≤ rho.horizon)
    (hframe : GateOffFrameAt S rho M (c - 1) c)
    (hband : ∀ w ∈ rho.honest, ∃ Hn : NamedBlock V,
      Hn.erase = voterHeadAt S rho w (S.hc.opening_slot c + 1) ∧ RunBlock S rho Hn ∧
        M - 1 ≤ (Protocol.derive_named S.E S.cfg Hn).h)
    {v : V} (hv : v ∈ rho.honest)
    (hT : actionSGBlockAt S rho v c =
      Protocol.get_fg_root (actionStoreAt S rho v c).toHealing.toFG) :
    NamedHonestVotesCone S rho (S.hc.opening_slot c + 1)
      (fun X => Block.Preceq (actionSGBlockAt S rho v c) X) := by
  have hpredLe : S.a (c - 1) ≤ S.a c := Assembly.a_mono S (Nat.sub_le c 1)
  have hfr := hframe (S.a c) hpredLe le_rfl v hv
  refine secondSlotCone_of_rootBelow' S adm hfb hhor hframe hband hv ?_
  rw [hT, actionStoreAt_fgRoot_eq_storeBeforeTime, fgRoot_eq_F_of_frame hfr.1 hfr.2]
  exact Block.preceq_self _

/-- **Tier 1 (clear target).** A target clear below the action store's live
confirmation is below every honest vote head of the slot after the opening:
a genuine confirmation has an honest same-slot supporter at the band, and the
compatible anchors carry the cone one slot; a root confirmation puts the
target below the finalized root. -/
theorem secondSlotCone_of_clear'
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {c : Round} (hc : 1 ≤ c)
    (hpost : S.E.t_GST ≤ S.a (c - 1))
    (hhor : S.a (c + 1) ≤ rho.horizon)
    (hframe : GateOffFrameAt S rho M (c - 1) (c + 1))
    (hbandO : ∀ u ∈ rho.honest, ∃ Hn : NamedBlock V,
      Hn.erase = voterHeadAt S rho u (S.hc.opening_slot c) ∧ RunBlock S rho Hn ∧
        M - 1 ≤ (Protocol.derive_named S.E S.cfg Hn).h)
    (hband1 : ∀ w ∈ rho.honest, ∃ Hn : NamedBlock V,
      Hn.erase = voterHeadAt S rho w (S.hc.opening_slot c + 1) ∧ RunBlock S rho Hn ∧
        M - 1 ≤ (Protocol.derive_named S.E S.cfg Hn).h)
    {v : V} (hv : v ∈ rho.honest)
    (hanchor : ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w (S.hc.opening_slot c + 1))
        (actionSGBlockAt S rho v c) = true)
    (hclear : Block.Preceq (actionSGBlockAt S rho v c)
      (actionStoreAt S rho v c).live_confirmed) :
    NamedHonestVotesCone S rho (S.hc.opening_slot c + 1)
      (fun X => Block.Preceq (actionSGBlockAt S rho v c) X) := by
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hoPos : 0 < S.hc.opening_slot c := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos hc (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hoo' : S.hc.opening_slot c + 2 ≤ S.hc.opening_slot (c + 1) := by
    unfold Protocol.HealConfig.opening_slot
    have hR : 2 ≤ S.hc.R := S.hc.R_ge_two
    rw [Nat.succ_mul]
    exact Nat.add_le_add_left hR _
  have hSc : S.a c = Protocol.confirmation_time S.E (S.hc.opening_slot c) := by
    rw [Setup.a, Protocol.a_eq_confirmation_time]
  have hpredLe : S.a (c - 1) ≤ S.a c := Assembly.a_mono S (Nat.sub_le c 1)
  have hpredLt : c - 1 < c := Nat.sub_lt hc Nat.one_pos
  have haCSucc : S.a c ≤ S.a (c + 1) := Assembly.a_mono S (Nat.le_succ c)
  have hhorC : S.a c ≤ rho.horizon := haCSucc.trans hhor
  have hframeC : GateOffFrameAt S rho M (c - 1) c :=
    fun read hlo hhi w hw => hframe read hlo (hhi.trans haCSucc) w hw
  have hpostProp : S.E.t_GST ≤ Protocol.proposal_time S.E (S.hc.opening_slot c) := by
    have h1 := action_add_delta_le_openingProposal_of_round_lt S hpredLt
    exact hpost.trans ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h1)
  have hpredProp : S.a (c - 1) ≤ Protocol.proposal_time S.E (S.hc.opening_slot c) := by
    have h1 := action_add_delta_le_openingProposal_of_round_lt S hpredLt
    exact (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h1
  have hvoteO_le : Protocol.vote_time S.E (S.hc.opening_slot c) ≤ S.a c := by
    rw [hSc]
    exact Protocol.vote_time_le_confirmation_time S.E _
  have hpredVoteO : S.a (c - 1) ≤ Protocol.vote_time S.E (S.hc.opening_slot c) :=
    hpredProp.trans (le_of_lt (Protocol.proposal_time_lt_vote_time S.E _))
  have hvoteOHor : Protocol.vote_time S.E (S.hc.opening_slot c) ≤ rho.horizon :=
    hvoteO_le.trans hhorC
  have hpostVoteO : S.E.t_GST ≤ Protocol.vote_time S.E (S.hc.opening_slot c) :=
    hpost.trans hpredVoteO
  have hcutO_le : Protocol.support_cutoff S.E (S.hc.opening_slot c) ≤ S.a c := by
    rw [hSc]
    exact Protocol.support_cutoff_le_confirmation_time S.E _
  have hpredCutO : S.a (c - 1) ≤ Protocol.support_cutoff S.E (S.hc.opening_slot c) :=
    hpredProp.trans (by
      unfold Protocol.support_cutoff Protocol.proposal_time
      exact le_add_of_nonneg_right (Int.mul_nonneg (by decide) (le_of_lt S.E.Δ_pos)))
  have hvote1Action : Protocol.vote_time S.E (S.hc.opening_slot c + 1) ≤ S.a c :=
    openingSuccVote_le_action' S c
  have hpredVote1 : S.a (c - 1) ≤ Protocol.vote_time S.E (S.hc.opening_slot c + 1) :=
    hpredVoteO.trans (Protocol.vote_time_mono_slots S.E (Nat.le_succ _))
  have hconf1 : Protocol.confirmation_time S.E (S.hc.opening_slot c + 1) ≤ S.a (c + 1) := by
    rw [Setup.a, Protocol.a_eq_confirmation_time]
    exact confirmation_time_mono_slots'' S.E ((Nat.le_succ _).trans hoo')
  have hconfOHor : Protocol.confirmation_time S.E (S.hc.opening_slot c) ≤ rho.horizon := by
    rw [← hSc]
    exact hhorC
  have hframeV1 : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (Protocol.vote_time S.E (S.hc.opening_slot c + 1))).h_j + 2 ≤ M ∧
        (rho.storeBeforeTime S w (Protocol.vote_time S.E (S.hc.opening_slot c + 1))).h_max = M :=
    fun w hw => hframe _ hpredVote1 (hvote1Action.trans haCSucc) w hw
  have hdutyFrontierO : ∀ w ∈ rho.honest,
      (voteDutyStore S rho w (S.hc.opening_slot c)).h_max = M := by
    intro w hw
    have h := (hframe _ hpredVoteO (hvoteO_le.trans haCSucc) w hw).2
    simpa only [voteDutyStore, voteStore, tickStore] using h
  rcases actionStoreAt_liveConfirmed_genuine_or_fgRoot S rho v c with
    ⟨C, hgen, hCeq⟩ | ⟨R, hReq, hRlive⟩
  · rw [← hCeq] at hclear
    have hTrun : ∃ Tn : NamedBlock V,
        Tn.erase = actionSGBlockAt S rho v c ∧ RunBlock S rho Tn := by
      have hmem := actionSGBlockAt_mem_storeBeforeTime S rho v c
      exact Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv (S.a c)
        (by simpa only [Run.storeBeforeTime] using hmem)
    -- an honest slot-`o` supporter of the confirmation, at the band
    obtain ⟨x, hx, hxCommittee, hCx⟩ :=
      genuineConfirmation_exists_honestVoteSupporter_ceiling S adm hcom hv hoPos
        hpostVoteO hconfOHor hgen
    obtain ⟨Hx, hHxErase, hHxRun, hHxBand⟩ := hbandO x hx
    have hsupp : ∃ u ∈ rho.honest, ∃ Hn : NamedBlock V,
        Hn.erase = voterHeadAt S rho u (S.hc.opening_slot c) ∧ RunBlock S rho Hn ∧
          Block.Preceq C Hn.erase ∧
          M - 1 ≤ (Protocol.derive_named S.E S.cfg Hn).h :=
      ⟨x, hx, Hx, hHxErase, hHxRun, by rw [hHxErase]; exact hCx, hHxBand⟩
    have hframe1 : ∀ w ∈ rho.honest,
        (voteDutyStore S rho w (S.hc.opening_slot c + 1)).h_max = M ∧
        (voteDutyStore S rho w (S.hc.opening_slot c + 1)).h_j + 2 ≤ M ∧
        (Block.Preceq (Protocol.get_fg_root
            (voteDutyStore S rho w (S.hc.opening_slot c + 1)).toHealing.toFG)
            (actionSGBlockAt S rho v c) ∨
          Block.Preceq (actionSGBlockAt S rho v c) (Protocol.get_fg_root
            (voteDutyStore S rho w (S.hc.opening_slot c + 1)).toHealing.toFG)) := by
      intro w hw
      have hcmp := fgRoot_comparable_of_bandWitness S adm hfb hw (hframeV1 w hw).1
        (hframeV1 w hw).2 hHxRun
        (Block.preceq_trans hclear (by rw [hHxErase]; exact hCx)) hHxBand
      refine ⟨?_, ?_, ?_⟩
      · simpa only [voteDutyStore, voteStore, tickStore] using (hframeV1 w hw).2
      · simpa only [voteDutyStore, voteStore, tickStore] using (hframeV1 w hw).1
      · simpa only [voteDutyStore, voteStore, tickStore] using hcmp
    exact baseCone_succ_of_genuineSupporter_rootComparable S adm hcom hfb hv
      hpostProp (hconf1.trans hhor) hgen hclear hTrun hframe1 hsupp hanchor
  · -- the live confirmation is the root: the target is below the finalized root
    rw [← hRlive] at hclear
    have hfr := hframe (S.a c) hpredLe haCSucc v hv
    refine secondSlotCone_of_rootBelow' S adm hfb hhorC hframeC hband1 hv ?_
    have hR' : R = (rho.storeBeforeTime S v (S.a c)).core.F := by
      have h := fgRoot_eq_F_of_frame hfr.1 hfr.2
      rw [hReq, hSc]
      rw [hSc] at h
      simpa only [confStore, tickStore] using h
    rw [← hR']
    exact hclear

/-! ## The round discharge from its parts

The band reach of every duty head (K5) and the anchor-carrier compatibility at
every later duty (K3) are taken as premises in the shapes the canonicity module
produces; the first slot's Claim 1 is assembled tier by tier. -/


/-- **Claim 1 at the second slot of round `c`, tier by tier.** Extracted from
`seedRoundDischarge_of_parts` because the window induction needs it one round
before the full record: the anchor-carrier input is consumed here at the single
slot `opening_slot c + 1`, and only by the clear tier. -/
theorem seedClaim1_of_parts
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {c : Round} (hc : 1 ≤ c)
    (hpost : S.E.t_GST ≤ S.a (c - 1))
    (hhor : S.a (c + 1) ≤ rho.horizon)
    (hframe : GateOffFrameAt S rho M (c - 1) (c + 1))
    (hready : GradeRoundReady S rho c)
    (hband : ∀ d : Slot, S.hc.opening_slot c ≤ d →
      d ≤ S.hc.opening_slot (c + 1) - 1 → ∀ w ∈ rho.honest,
      ∃ Hn : NamedBlock V, Hn.erase = voterHeadAt S rho w d ∧ RunBlock S rho Hn ∧
        M - 1 ≤ (Protocol.derive_named S.E S.cfg Hn).h)
    (hanchor1 : ∀ w ∈ rho.honest, ∀ v ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w (S.hc.opening_slot c + 1))
        (actionSGBlockAt S rho v c) = true)
    (hg2 : ∀ v ∈ rho.honest, Internal.PhaseGrades.nodeRawG2 S (actionReadAt S rho v c) c) :
    ∀ v ∈ rho.honest,
      NamedHonestVotesCone S rho (S.hc.opening_slot c + 1)
        (fun X => Block.Preceq (actionSGBlockAt S rho v c) X) := by
  have hb := openingSucc_le_boundary' S c
  have haCSucc : S.a c ≤ S.a (c + 1) := Assembly.a_mono S (Nat.le_succ c)
  have hhorC : S.a c ≤ rho.horizon := haCSucc.trans hhor
  have hframeC : GateOffFrameAt S rho M (c - 1) c :=
    fun read hlo hhi w hw => hframe read hlo (hhi.trans haCSucc) w hw
  have hbandO : ∀ u ∈ rho.honest, ∃ Hn : NamedBlock V,
      Hn.erase = voterHeadAt S rho u (S.hc.opening_slot c) ∧ RunBlock S rho Hn ∧
        M - 1 ≤ (Protocol.derive_named S.E S.cfg Hn).h :=
    fun u hu => hband _ le_rfl ((Nat.le_succ _).trans hb) u hu
  have hband1 : ∀ w ∈ rho.honest, ∃ Hn : NamedBlock V,
      Hn.erase = voterHeadAt S rho w (S.hc.opening_slot c + 1) ∧ RunBlock S rho Hn ∧
        M - 1 ≤ (Protocol.derive_named S.E S.cfg Hn).h :=
    fun w hw => hband _ (Nat.le_succ _) hb w hw
  intro v hv
  rcases actionSGBlockAt_tiers S rho v c with
    ⟨-, hclear, -⟩ | ⟨Q, hQ, hTQ⟩ | ⟨-, -, hTeq⟩ | ⟨-, hnoRaw, -⟩
  · exact secondSlotCone_of_clear' S adm hcom hfb hc hpost hhor hframe hbandO hband1
      hv (fun w hw => hanchor1 w hw v hv) hclear
  · rw [hTQ]
    exact secondSlotCone_of_grade2' S adm hfb hc hpost hhorC hframeC hready hv hQ
  · exact secondSlotCone_of_rootTarget' S adm hfb hhorC hframeC hband1 hv hTeq
  · exact absurd (hg2 v hv) hnoRaw

/-- **The round discharge from its parts.** -/
theorem seedRoundDischarge_of_parts
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {c : Round} (hc : 1 ≤ c)
    (hpost : S.E.t_GST ≤ S.a (c - 1))
    (hhor : S.a (c + 1) ≤ rho.horizon)
    (hframe : GateOffFrameAt S rho M (c - 1) (c + 1))
    (hready : GradeRoundReady S rho c)
    (hband : ∀ d : Slot, S.hc.opening_slot c ≤ d →
      d ≤ S.hc.opening_slot (c + 1) - 1 → ∀ w ∈ rho.honest,
      ∃ Hn : NamedBlock V, Hn.erase = voterHeadAt S rho w d ∧ RunBlock S rho Hn ∧
        M - 1 ≤ (Protocol.derive_named S.E S.cfg Hn).h)
    (hanchor : ∀ d : Slot, S.hc.opening_slot c + 1 ≤ d →
      d ≤ S.hc.opening_slot (c + 1) - 1 → ∀ w ∈ rho.honest, ∀ v ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w d) (actionSGBlockAt S rho v c) = true)
    (hg2 : ∀ v ∈ rho.honest, Internal.PhaseGrades.nodeRawG2 S (actionReadAt S rho v c) c) :
    SeedRoundDischargeAt S rho M c := by
  have hb := openingSucc_le_boundary' S c
  have haCSucc : S.a c ≤ S.a (c + 1) := Assembly.a_mono S (Nat.le_succ c)
  have hhorC : S.a c ≤ rho.horizon := haCSucc.trans hhor
  have hframeC : GateOffFrameAt S rho M (c - 1) c :=
    fun read hlo hhi w hw => hframe read hlo (hhi.trans haCSucc) w hw
  have hbandO : ∀ u ∈ rho.honest, ∃ Hn : NamedBlock V,
      Hn.erase = voterHeadAt S rho u (S.hc.opening_slot c) ∧ RunBlock S rho Hn ∧
        M - 1 ≤ (Protocol.derive_named S.E S.cfg Hn).h :=
    fun u hu => hband _ le_rfl ((Nat.le_succ _).trans hb) u hu
  have hband1 : ∀ w ∈ rho.honest, ∃ Hn : NamedBlock V,
      Hn.erase = voterHeadAt S rho w (S.hc.opening_slot c + 1) ∧ RunBlock S rho Hn ∧
        M - 1 ≤ (Protocol.derive_named S.E S.cfg Hn).h :=
    fun w hw => hband _ (Nat.le_succ _) hb w hw
  refine { claim1 := ?_, anchorCompat := ?_, headBand := ?_ }
  · exact seedClaim1_of_parts S adm hcom hfb hc hpost hhor hframe hready hband
      (fun w hw v hv => hanchor _ le_rfl hb w hw v hv) hg2
  · intro d hlo hhi w hw v hv
    exact hanchor d (le_of_lt hlo) hhi w hw v hv
  · exact hband

/-! ## The discharge over the window, from the canonicity parts -/

/-- Band reach of every honest vote-duty head, at every round of a window
(K5's shape). -/
def SeedBandReachFrom (S : Setup V) (rho : Run V) (r0 : Round) : Prop :=
  ∀ (M : Height) (c : Round), 1 ≤ c → r0 + 2 ≤ c →
    S.E.t_GST ≤ S.a (c - 1) → S.a (c + 1) ≤ rho.horizon →
    GateOffFrameAt S rho M (c - 1) (c + 1) →
    ∀ d : Slot, S.hc.opening_slot c ≤ d → d ≤ S.hc.opening_slot (c + 1) - 1 →
      ∀ w ∈ rho.honest, ∃ Hn : NamedBlock V,
        Hn.erase = voterHeadAt S rho w d ∧ RunBlock S rho Hn ∧
          M - 1 ≤ (Protocol.derive_named S.E S.cfg Hn).h

/-- Anchor-carrier compatibility at every duty from the second slot, or the
raw-anchor configuration (K3's shape). -/
def SeedAnchorCompatFrom (S : Setup V) (rho : Run V) (r0 : Round) : Prop :=
  ∀ (M : Height) (c : Round), 1 ≤ c → r0 + 2 ≤ c →
    S.E.t_GST ≤ S.a (c - 1) → S.a (c + 1) ≤ rho.horizon →
    GateOffFrameAt S rho M (c - 1) (c + 1) →
    ∀ d : Slot, S.hc.opening_slot c + 1 ≤ d → d ≤ S.hc.opening_slot (c + 1) - 1 →
      ∀ w ∈ rho.honest, ∀ v ∈ rho.honest,
        Block.compatible (voterAnchorAt S rho w d)
            (actionSGBlockAt S rho v c) = true ∨
          ¬ Internal.PhaseGrades.nodeRawG2 S (actionReadAt S rho v c) c

/-- A grade-2 block in every honest raw tree at every round action of a window
(K2's grade-2 shape). -/
def SeedRawG2From (S : Setup V) (rho : Run V) (r0 : Round) : Prop :=
  ∀ (M : Height) (c : Round), 1 ≤ c → r0 + 2 ≤ c →
    S.E.t_GST ≤ S.a (c - 1) → S.a (c + 1) ≤ rho.horizon →
    GateOffFrameAt S rho M (c - 1) (c + 1) →
    ∀ v ∈ rho.honest, Internal.PhaseGrades.nodeRawG2 S (actionReadAt S rho v c) c

/-- The window discharge from the canonicity parts. -/
theorem seedDischargeFrom_of_parts
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {r0 : Round}
    (hpost0 : S.E.t_GST ≤ S.a r0)
    (hK5 : SeedBandReachFrom S rho r0)
    (hK3 : SeedAnchorCompatFrom S rho r0)
    (hK2 : SeedRawG2From S rho r0) :
    SeedDischargeFrom S rho r0 := by
  intro M base c hbase hc hbaseC hpost hhor2 hframe2
  have hbase2C : base + 2 ≤ c :=
    (Nat.add_le_add_left (by decide : 2 ≤ 3) base).trans hbaseC
  have hbase1Pred : base + 1 ≤ c - 1 := by
    apply Nat.le_sub_of_add_le
    simpa only [Nat.add_assoc] using hbase2C
  have hr02C : r0 + 2 ≤ c :=
    (Nat.add_le_add_right hbase 2).trans hbase2C
  have hcSucc : c + 1 ≤ c + 2 := Nat.le_succ _
  have hhor : S.a (c + 1) ≤ rho.horizon := (Assembly.a_mono S hcSucc).trans hhor2
  have hframe : GateOffFrameAt S rho M (c - 1) (c + 1) :=
    fun read hlo hhi w hw => hframe2 read
      ((Assembly.a_mono S hbase1Pred).trans hlo)
      (hhi.trans (Assembly.a_mono S hcSucc)) w hw
  have hhorC : S.a c ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_succ c)).trans hhor
  have hready : GradeRoundReady S rho c :=
    gradeRoundReady_of_gst_le_a S hpost0 hr02C hhorC
  have hg2 := hK2 M c hc hr02C hpost hhor hframe
  refine seedRoundDischarge_of_parts S adm hcom hfb hc hpost hhor hframe hready
    (hK5 M c hc hr02C hpost hhor hframe) ?_ hg2
  intro d hlo hhi w hw v hv
  rcases hK3 M c hc hr02C hpost hhor hframe d hlo hhi w hw v hv with h | hnoRaw
  · exact h
  · exact absurd (hg2 v hv) hnoRaw

/-- **The gate-off height-progress seed from the per-round discharge.** -/
theorem heightProgressSeedFrom_of_discharge
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    (hdelayBound : TimeoutDelayBound S delayExtra)
    {r0 gap : Round}
    (hrec : MultiProposerRecurrence S rho gap)
    (hpost : S.E.t_GST ≤ S.a r0)
    (hpred : SeedPredPromotionInputs S rho delayExtra)
    (hdis : SeedDischargeFrom S rho r0) :
    HeightProgressSeedFrom (delayExtra := delayExtra) S rho r0 gap := by
  refine heightProgressSeedFrom_of_carrierAdoption S adm hcom hfb hrec hpost
    ?_ (seedPredCloser_of_timeoutDelay S adm hcom hfb hdelayBound hpred hrec)
  intro M base q hbase hq hpostBase hhor hframeSeed hcarrier
  have hframe : GateOffFrameAt S rho M (base + 1) (q + 2) :=
    fun read hlo hhi w hw => hframeSeed read hlo hhi w hw
  obtain ⟨hq1, hq11, hbq1, hbq11, hbq1', hbq11', hq1succ, hq12, hbq2, hbq21⟩ :=
    entry_nat' hq
  constructor
  · have hpost' : S.E.t_GST ≤ S.a (q - 1) :=
      hpostBase.trans (Assembly.a_mono S hbq1')
    have hframe' : GateOffFrameAt S rho M (q - 1) (q + 2) :=
      fun read hlo hhi w hw => hframe read ((Assembly.a_mono S hbq1).trans hlo) hhi w hw
    exact (seedBoundaryAdoption_of_discharge S adm hcom hfb hq1 hpost' hhor hframe'
      (hdis M base q hbase hq1 hbq2
        hpost' hhor hframe)).1
  · have hpost' : S.E.t_GST ≤ S.a (q - 1 - 1) :=
      hpostBase.trans (Assembly.a_mono S hbq11')
    have hhor' : S.a (q - 1 + 2) ≤ rho.horizon :=
      (Assembly.a_mono S hq12).trans hhor
    have hframe' : GateOffFrameAt S rho M (q - 1 - 1) (q - 1 + 2) :=
      fun read hlo hhi w hw => hframe read ((Assembly.a_mono S hbq11).trans hlo)
        (hhi.trans (Assembly.a_mono S hq12)) w hw
    have hframeDis : GateOffFrameAt S rho M (base + 1) (q - 1 + 2) :=
      fun read hlo hhi w hw => hframe read hlo
        (hhi.trans (Assembly.a_mono S hq12)) w hw
    have hcarrier' : ProposerCarrierAt S rho (q - 1 + 1) := by
      rw [hq1succ]
      exact hcarrier
    have h := seedBandCarrierCover_succ_of_discharge S adm hcom hfb hq11 hpost' hhor'
      hframe' (hdis M base (q - 1) hbase hq11 hbq21 hpost' hhor' hframeDis)
      hcarrier'
    rw [hq1succ] at h
    exact h




/-! ## The canonicity parts, from `SeedCanonicalAnchorRun` -/

/-- K5 over a window: band reach of every honest vote-duty head. -/
theorem seedBandReachFrom_of_canonicity (S : Setup V) {rho : Run V}
    (adm : Admissible S rho) (hfb : BelowOneThird S rho.honest) (r0 : Round) :
    SeedBandReachFrom S rho r0 := by
  intro M c hc _ hpost hhor hframe d hlo hhi w hw
  exact voteDutyHead_band_at_duty S adm hfb hc hframe hpost hhor hw hlo hhi
    (seedEntryRoundOf' S hlo hhi)

/-- K2 (relative raw-grade-2 form) at the action read, over a window. -/
theorem seedRawG2From_of_canonicity (S : Setup V) {rho : Run V}
    (adm : Admissible S rho) (hfb : BelowOneThird S rho.honest) (r0 : Round) :
    SeedRawG2From S rho r0 := by
  intro M c hc _ hpost hhor hframe v hv
  have haCSucc : S.a c ≤ S.a (c + 1) := Assembly.a_mono S (Nat.le_succ c)
  have hpredLe : S.a (c - 1) ≤ S.a c := Assembly.a_mono S (Nat.sub_le c 1)
  exact nodeRawG2_of_gateOffFrame S adm hfb (Nat.succ_le_iff.mp hc)
    (haCSucc.trans hhor) hpost
    (fun u hu => (hframe (S.a (c - 1)) le_rfl (hpredLe.trans haCSucc) u hu).2)
    (fun w hw => (hframe (S.a c) hpredLe haCSucc w hw).2)
    (fun w hw => (hframe (S.a c) hpredLe haCSucc w hw).1) v hv

















/-- Pointwise K3 over a window, with open from its post-GST base. -/
theorem seedAnchorCompatFrom_of_canonicity (S : Setup V) {rho : Run V}
    (adm : Admissible S rho) (_hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    (r0 : Round) (hpost0 : S.E.t_GST ≤ S.a r0) :
    SeedAnchorCompatFrom S rho r0 := by
  intro M c hc hr0 hpost hhor hframe d hlo hhi w hw v hv
  have hready : GradeRoundReady S rho c :=
    gradeRoundReady_of_gst_le_a S hpost0 hr0
      ((Assembly.a_mono S (Nat.le_succ c)).trans hhor)
  exact Or.inl (preparedAnchor_compatible_carrier_of_gateOff_relative
    S adm hfb hc hframe hpost hhor hready hw hv hlo hhi
      (seedEntryRoundOf' S ((Nat.le_succ _).trans hlo) hhi))

/-- **The window discharge from canonicity.** -/
theorem seedDischargeFrom_of_canonicity (S : Setup V) {rho : Run V}
    (adm : Admissible S rho) (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest) {r0 : Round}
    (hpost0 : S.E.t_GST ≤ S.a r0) :
    SeedDischargeFrom S rho r0 :=
  seedDischargeFrom_of_parts S adm hcom hfb hpost0
    (seedBandReachFrom_of_canonicity S adm hfb r0)
    (seedAnchorCompatFrom_of_canonicity S adm hcom hfb r0 hpost0)
    (seedRawG2From_of_canonicity S adm hfb r0)

/-- **The gate-off height-progress seed from canonicity.** The seed rests on
the gate-off frame and the timeout delay bound. -/
theorem heightProgressSeedFrom_of_canonicity
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    (hdelayBound : TimeoutDelayBound S delayExtra)
    {r0 gap : Round}
    (hrec : MultiProposerRecurrence S rho gap)
    (hpost : S.E.t_GST ≤ S.a r0)
    (hpred : SeedPredPromotionInputs S rho delayExtra) :
    HeightProgressSeedFrom (delayExtra := delayExtra) S rho r0 gap :=
  heightProgressSeedFrom_of_discharge S adm hcom hfb hdelayBound hrec hpost
    hpred
    (seedDischargeFrom_of_canonicity S adm hcom hfb hpost)



























#print axioms g1_bandWitness_relayed'
#print axioms coneAndThin_succ'
#print axioms coneAndThin_through'
#print axioms boundaryConeAndThin_of_baseCone'
#print axioms roundCeiling_succ_of_baseCone'
#print axioms secondSlotCone_of_grade2'
#print axioms fgRoot_comparable_of_bandWitness
#print axioms seedBoundaryAdoption_of_discharge
#print axioms gateOffOpeningAdoption_succ_of_discharge
#print axioms seedBandCarrierCover_succ_of_discharge
#print axioms secondSlotCone_of_rootBelow'
#print axioms secondSlotCone_of_rootTarget'
#print axioms secondSlotCone_of_clear'

/-- **The per-round discharge from canonicity.** -/
theorem seedRoundDischarge_of_canonicity
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {c : Round} (hc : 1 ≤ c)
    (hpost : S.E.t_GST ≤ S.a (c - 1))
    (hhor : S.a (c + 1) ≤ rho.horizon)
    (hframe : GateOffFrameAt S rho M (c - 1) (c + 1))
    (hready : GradeRoundReady S rho c) :
    SeedRoundDischargeAt S rho M c := by
  have haCSucc : S.a c ≤ S.a (c + 1) := Assembly.a_mono S (Nat.le_succ c)
  have hpredLe : S.a (c - 1) ≤ S.a c := Assembly.a_mono S (Nat.sub_le c 1)
  have hg2 : ∀ v ∈ rho.honest,
      Internal.PhaseGrades.nodeRawG2 S (actionReadAt S rho v c) c :=
    nodeRawG2_of_gateOffFrame S adm hfb (Nat.succ_le_iff.mp hc)
      (haCSucc.trans hhor) hpost
      (fun u hu => (hframe (S.a (c - 1)) le_rfl (hpredLe.trans haCSucc) u hu).2)
      (fun w hw => (hframe (S.a c) hpredLe haCSucc w hw).2)
      (fun w hw => (hframe (S.a c) hpredLe haCSucc w hw).1)
  refine seedRoundDischarge_of_parts S adm hcom hfb hc hpost hhor hframe hready
    (fun d hlo hhi w hw => voteDutyHead_band_at_duty S adm hfb hc hframe hpost hhor hw
      hlo hhi (seedEntryRoundOf' S hlo hhi))
    ?_ hg2
  intro d hlo hhi w hw v hv
  exact preparedAnchor_compatible_carrier_of_gateOff_relative
    S adm hfb hc hframe hpost hhor hready hw hv hlo hhi
      (seedEntryRoundOf' S ((Nat.le_succ _).trans hlo) hhi)

#print axioms seedRoundDischarge_of_canonicity
#print axioms seedRoundDischarge_of_parts
#print axioms seedDischargeFrom_of_parts
#print axioms heightProgressSeedFrom_of_discharge
#print axioms seedBandReachFrom_of_canonicity
#print axioms seedRawG2From_of_canonicity
#print axioms seedAnchorCompatFrom_of_canonicity
#print axioms seedDischargeFrom_of_canonicity
#print axioms heightProgressSeedFrom_of_canonicity


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
