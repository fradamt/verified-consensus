module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.FixedHeightRootClaimOne
public import DecoupledConsensusProofs.Generic.FixedHeightRootAdmission
public import DecoupledConsensusProofs.Objects.SGTargetG1Concentration
public import DecoupledConsensusProofs.Protocol.Grades.FixedHeightRootOpeningParentComplete
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FixedHeightRootOpeningConfirmationRead
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.FixedHeightRootOpeningFrozenVote
public import DecoupledConsensusProofs.Protocol.Schedule.FixedHeightRootOpeningNextActive
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FinalityFilterRetention
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RawProposerSelection
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryStableProposalCapture
public import DecoupledConsensusProofs.Protocol.ForkChoice.Head.HeightProgressClosureactionRootPreceq
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightProgressClosurescoreEq
public import DecoupledConsensusProofs.Protocol.Grades.HeightProgressClosureg0ClearAtAction
public import DecoupledConsensusProofs.Protocol.Grades.RelativeCarrierWindowFixedRoot
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FixedHeightRootRelativeAnchor
public import DecoupledConsensusProofs.Protocol.Grades.HeightProgressClosureBatchAlignedSite
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryProposalCapInputs

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Fixed-height root Claim-4 lifecycle closure

A Claim-1 opening lock is extended through the concrete proposer, parent,
confirmation, frozen-vote, and next-action producers. The endpoint rise is
kept public; the no-rise branch constructs one complete lifecycle records.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

open Internal.NamedRecoveryRead in
/-- The round-`q` opening proposal is filtered at every honest voter's opening
vote-duty read, under exact fixed-root retention with no frontier rise. -/
private theorem openingProposal_mem_filteredTree_voteRead_of_fixedRoot
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {w : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho H w read)
    {q : Round} {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot q) = some P)
    (hq : 0 < q)
    (hpostRead : S.E.t_GST ≤ read)
    (hvoteDelay : read + S.E.Δ ≤
      Protocol.vote_time S.E (S.hc.opening_slot q))
    (hconfirmationDelay : read + S.E.Δ ≤
      Protocol.confirmation_time S.E (S.hc.opening_slot q))
    (hconfirmationHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hconfirmationCap : honestHMaxAt S rho
      (Protocol.confirmation_time S.E (S.hc.opening_slot q)) ≤ H)
    (hpostProposal : S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hJparent : Block.Preceq (rho.storeBeforeTime S w read).J
      (proposedParent S rho (S.hc.opening_slot q)))
    (hJP : Block.Preceq (rho.storeBeforeTime S w read).J P.erase) :
    ∀ v ∈ rho.honest, ∀ C : Block V,
      Block.Preceq (rho.storeBeforeTime S w read).J C →
      Block.Preceq C P.erase →
        C ∈ Protocol.get_filtered_block_tree
            (voteDutyRead S rho v
              (S.hc.opening_slot q)).st.core.toHealing.toFG ∧
          C ∈ voterCandidateTreeAt S rho v (S.hc.opening_slot q) := by
  have hopenPos : 0 < S.hc.opening_slot q :=
    Nat.mul_pos hq (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hopen : (S.hc.opening_slot q - 1) + 1 = S.hc.opening_slot q :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hopenPos))
  have hproposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon :=
    (Protocol.proposal_time_le_confirmation_time S.E
      (S.hc.opening_slot q)).trans hconfirmationHor
  have hvoteHor : Protocol.vote_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon :=
    (Protocol.vote_time_le_confirmation_time S.E
      (S.hc.opening_slot q)).trans hconfirmationHor
  have hvoteCap : honestHMaxAt S rho
      (Protocol.vote_time S.E (S.hc.opening_slot q)) ≤ H :=
    (honestHMaxAt_mono S adm.toNamedScheduleWellFormed
      (Protocol.vote_time_le_confirmation_time S.E
        (S.hc.opening_slot q))).trans hconfirmationCap
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hPrun : RunBlock S rho P :=
    proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
      (S.hc.opening_slot q) hopenPos hprop hproposalHor hP
  obtain ⟨Jn, hJnErase, hJnRun, hJnHeight⟩ :=
    fixedRoot_namedTarget_of_fixedRoot S hfix
  obtain ⟨Jp, hJpP, hJpErase⟩ := Proofs.NamedAncestry.erased_ancestor_lift P hJP
  have hJpRun := Proofs.NamedRuntime.blockInRun_of_ancestor S rho hPrun hJpP
  have hJpEq : Jp = Jn := by
    apply adm.toNamedRootCollisionFree.root_injective
      Jp Jn hJpRun hJnRun Jp Jn
      (Or.inl (Proofs.NamedAncestry.named_self Jp))
      (Or.inr (Proofs.NamedAncestry.named_self Jn))
    rw [← Proofs.NamedWire.erase_root Jp, ← Proofs.NamedWire.erase_root Jn,
      hJpErase, hJnErase]
  have hPheight : H - 1 ≤ (Protocol.derive_named S.E S.cfg P).h := by
    rw [← hJnHeight, ← hJpEq]
    exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hJpP
  have hadmit :=
    openingProposalAdmittedBeforeVote_of_fixedJustificationRootNoRise
      S adm hfb hfix hP hq hpostRead hconfirmationDelay hconfirmationHor
        hconfirmationCap hpostProposal hprop (Block.preceq_self _) hJparent
  intro v hv
  let target := voteDutyRead S rho v (S.hc.opening_slot q)
  have hrootMax :=
    fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
      S adm hsb hfix hv hpostRead hvoteDelay hvoteHor hvoteCap
  have hPtree : P.erase ∈ target.st.core.T := by
    have hmem := (admittedBefore_mem_and_stamp_at S
      adm.toNamedScheduleWellFormed (hadmit v hv) (le_refl _)).1
    simpa only [target, voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hmem
  have hroot : Protocol.get_fg_root target.st.core.toHealing.toFG =
      (rho.storeBeforeTime S w read).J := by
    simpa only [target, voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hrootMax.1
  have hmax : target.st.core.h_max = H := by
    simpa only [target, voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hrootMax.2
  have hraw := fixedRootGrade_mem_filtered_of_exactRoot S adm hv hPrun
    (by simpa only [target, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hPtree)
    hJP hPheight
    (by simpa only [target, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hroot)
    (by simpa only [target, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hmax)
  have hPfiltered : P.erase ∈ Protocol.get_filtered_block_tree
      target.st.core.toHealing.toFG := by
    simpa only [target, voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hraw
  have hslot : target.st.core.s = S.hc.opening_slot q := by
    simpa only [target] using
      Proofs.Optimistic.voteDutyRead_slot S rho v (S.hc.opening_slot q)
  have hPprocessed : P.erase ∈ Protocol.voter_processed_block_tree S.E
      target.st.core.toHealing.toFG.toSG.toGoldfishStore target.st.core.s := by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    refine ⟨hPtree, Or.inr ⟨P.erase, ⟨hPtree, ?_⟩, Block.preceq_self _⟩⟩
    rw [Proofs.NamedWire.erase_slot,
      proposedBlockAt_slot S rho (S.hc.opening_slot q) hP]
    exact hslot.symm
  have hmaxP : target.st.core.h_max ≤
      (Protocol.derive_named S.E S.cfg P).h + 1 := by
    rw [hmax]
    have hHone : 1 ≤ H :=
      Nat.le_of_lt (Nat.sub_pos_iff_lt.mp hfix.targetHeightPositive)
    calc
      H = H - 1 + 1 := (Nat.sub_add_cancel hHone).symm
      _ ≤ (Protocol.derive_named S.E S.cfg P).h + 1 :=
        Nat.add_le_add_right hPheight 1
  have hPprocessedStore : P.erase ∈ Protocol.voter_processed_block_tree S.E
      (Internal.NamedRecoveryRead.voteDutyStore S rho v
        ((S.hc.opening_slot q - 1) + 1)).toHealing.toFG.toSG.toGoldfishStore
      (Internal.NamedRecoveryRead.voteDutyStore S rho v
        ((S.hc.opening_slot q - 1) + 1)).toHealing.s := by
    simpa only [target, voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      hopen] using hPprocessed
  have hPfilteredStore : P.erase ∈ Protocol.get_filtered_block_tree
      (Internal.NamedRecoveryRead.voteDutyStore S rho v
        ((S.hc.opening_slot q - 1) + 1)).toHealing.toFG := by
    simpa only [target, voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      hopen] using hPfiltered
  have hmaxPStore : (Internal.NamedRecoveryRead.voteDutyStore S rho v
      ((S.hc.opening_slot q - 1) + 1)).h_max ≤
        (Protocol.derive_named S.E S.cfg P).h + 1 := by
    simpa only [target, voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      hopen] using hmaxP
  have hrootStore : Protocol.get_fg_root
      (Internal.NamedRecoveryRead.voteDutyStore S rho v
        ((S.hc.opening_slot q - 1) + 1)).toHealing.toFG =
      (rho.storeBeforeTime S w read).J := by
    simpa only [target, voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      hopen] using hroot
  have hFJ : Block.Preceq
      (Internal.NamedRecoveryRead.voteDutyStore S rho v ((S.hc.opening_slot q - 1) + 1)).F
      (Internal.NamedRecoveryRead.voteDutyStore S rho v ((S.hc.opening_slot q - 1) + 1)).J := by
    simpa only [Internal.NamedRecoveryRead.voteDutyStore, hopen] using
      (Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        S rho (Protocol.vote_time S.E (S.hc.opening_slot q)) v)
  have hpc : ParentClosed
      (Internal.NamedRecoveryRead.voteDutyStore S rho v ((S.hc.opening_slot q - 1) + 1)) := by
    simpa only [Internal.NamedRecoveryRead.voteDutyStore, hopen] using
      (Proofs.NamedStoreBridge.parentClosed_stateBeforeTime
        S rho (Protocol.vote_time S.E (S.hc.opening_slot q)) v)
  have hPT : P.erase ∈
      (Internal.NamedRecoveryRead.voteDutyStore S rho v ((S.hc.opening_slot q - 1) + 1)).T :=
    Proofs.Records.get_filtered_block_tree_subset _ hPfilteredStore
  intro C hJC hCP
  have hrootC : Block.Preceq
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyStore S rho v
          ((S.hc.opening_slot q - 1) + 1)).toHealing.toFG) C := by
    rw [hrootStore]
    exact hJC
  have hCT : C ∈
      (Internal.NamedRecoveryRead.voteDutyStore S rho v ((S.hc.opening_slot q - 1) + 1)).T :=
    Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2 C P.erase hPT hCP
  have hCfiltered := Proofs.Records.mem_filtered_of_preceq
    (st := (Internal.NamedRecoveryRead.voteDutyStore S rho v
      ((S.hc.opening_slot q - 1) + 1)).toHealing.toFG)
    (by simpa only [Block.Preceq, Protocol.Store.toHealing] using hFJ)
    hPfilteredStore hCT hCP hrootC
  have hcand := namedAncestorCandidate_of_processedDescendant_and_hMax
    S adm hv hPprocessedStore hPrun hCP hCfiltered hmaxPStore
  have hcand' : C ∈ voterCandidateTreeAt S rho v
      ((S.hc.opening_slot q - 1) + 1) := by
    simpa only [voterCandidateTreeAt,
      Proofs.Optimistic.voter_candidate_tree_eq_protocol_voter_filtered_block_tree]
      using hcand
  rw [hopen] at hcand' hCfiltered
  exact ⟨hCfiltered, hcand'⟩

set_option maxHeartbeats 400000 in

/-- A bounded recurrent honest proposer window either reaches a higher honest
frontier at its endpoint, or supplies a concrete opening proposal lifecycle.

This is the round-local closure of the producer above: the eight hoisted `∀ q`
pins are discharged at the single round the proof reaches, and the anchor is
the relative frame anchor of the proposer's own read. What remains is the
proposal pivot suffix, the action batch alignment, the relative-anchor layer,
and the fixed-root relative carrier window. -/
theorem fixedHeightJustificationRoot_boundedProposalLifecycle_closed
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {w : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho H w read)
    {r gap : Round}
    (hpost : S.E.t_GST ≤ read)
    (hreadAction : read ≤ S.a r)
    (hrecurrence : MultiProposerRecurrence S rho gap)
    (hendHor : S.a (r + 4 + gap) ≤ rho.horizon) :
    H < honestHMaxAt S rho (S.a (r + 4 + gap)) ∨
      ∃ q, r + 3 ≤ q ∧ q ≤ r + 3 + gap ∧
        ProposerCarrierAt S rho q ∧
          NamedGradeFormsAt S rho (q - 1) (rho.storeBeforeTime S w read).J ∧
            SGTargetOpeningConeRootLock S rho H (q - 1)
              (S.hc.opening_slot q - 1) ∧
              ∃ P : NamedBlock V,
                proposedBlockAt S rho (S.hc.opening_slot q) = some P ∧
                NamedSGProposalLifecyclePacket S rho (q - 1)
                  (S.hc.opening_slot q - 1) P := by
  by_cases hrise : H < honestHMaxAt S rho (S.a (r + 4 + gap))
  · exact Or.inl hrise
  · have hcapEnd : honestHMaxAt S rho (S.a (r + 4 + gap)) ≤ H :=
      Nat.le_of_not_gt hrise
    rcases
        fixedHeightJustificationRoot_boundedOpeningConeRootLock_of_proposerRecurrence_of_faultBound
          S adm hcom hfb hfix hpost hreadAction hrecurrence hendHor with
      hcontrary | ⟨q, hqlo, hqhi, hcarrier, hforms, hlock⟩
    · exact False.elim (hrise hcontrary)
    · right
      obtain ⟨P, hP⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot q)
      refine ⟨q, hqlo, hqhi, hcarrier, hforms, hlock, P, hP, ?_⟩
      let J := (rho.storeBeforeTime S w read).J
      let p := S.E.proposer (S.hc.opening_slot q)
      let proposalRead := Protocol.proposal_time S.E (S.hc.opening_slot q)
      let pre := rho.storeBeforeTime S p proposalRead
      let duty := Protocol.proposerDutyStore S rho (S.hc.opening_slot q)
      have hqlo' : r + 1 + 2 ≤ q := by
        simpa only [Nat.add_assoc] using hqlo
      have hqTwo : 2 ≤ q :=
        (Nat.le_add_left 2 (r + 1)).trans hqlo'
      have hqOne : 1 ≤ q :=
        (by decide : 1 ≤ 2).trans hqTwo
      have hqPos : 0 < q :=
        (by decide : 0 < 2).trans_le hqTwo
      have hqActionLower : r + 1 ≤ q - 2 :=
        Nat.le_sub_of_add_le hqlo'
      have hqActionSucc : q - 2 ≤ q - 1 :=
        Nat.sub_le_sub_left (by decide : 1 ≤ 2) q
      have hqReadyLower : r + 1 ≤ q - 1 :=
        hqActionLower.trans hqActionSucc
      have hqPred : q - 2 + 1 = q - 1 := by
        have hqEq : q - 2 + 2 = q := Nat.sub_add_cancel hqTwo
        rw [← hqEq]
        simp
      have hqPredAdd : q - 1 + 1 = q :=
        Nat.sub_add_cancel hqOne
      have hbaseEnd : r + 3 ≤ r + 4 :=
        Nat.add_le_add_left (Nat.le_succ 3) r
      have hqEnd : q ≤ r + 4 + gap :=
        hqhi.trans (Nat.add_le_add_right hbaseEnd gap)
      have hqNextEnd : q + 1 ≤ r + 4 + gap := by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          Nat.add_le_add_right hqhi 1
      have hqAtEnd : S.a q ≤ S.a (r + 4 + gap) :=
        Assembly.a_mono S hqEnd
      have hqNextAtEnd : S.a (q + 1) ≤ S.a (r + 4 + gap) :=
        Assembly.a_mono S hqNextEnd
      have hactionQHor : S.a q ≤ rho.horizon :=
        hqAtEnd.trans hendHor
      have hactionQCap : honestHMaxAt S rho (S.a q) ≤ H :=
        (honestHMaxAt_mono S adm.toNamedScheduleWellFormed hqAtEnd).trans hcapEnd
      have hactionNextHor : S.a (q + 1) ≤ rho.horizon :=
        hqNextAtEnd.trans hendHor
      have hrPrevLe : r ≤ q - 1 :=
        (Nat.le_succ r).trans hqReadyLower
      have hpostPreviousAction : S.E.t_GST ≤ S.a (q - 1) :=
        hpost.trans (hreadAction.trans (Assembly.a_mono S hrPrevLe))
      have hdelayAction : read + S.E.Δ ≤ S.a (q - 2) := by
        calc
          read + S.E.Δ ≤ S.a r + S.E.Δ :=
            Int.add_le_add_right hreadAction S.E.Δ
          _ ≤ S.hc.Γ_neg1 S.E.Δ (r + 1) :=
            action_add_delta_le_next_Γ_neg1 S r
          _ ≤ S.a (r + 1) :=
            le_of_lt (next_Γ_neg1_lt_action S r)
          _ ≤ S.a (q - 2) := Assembly.a_mono S hqActionLower
      have hrq : r < q :=
        (Nat.lt_succ_self r).trans_le
          (hqActionLower.trans (Nat.sub_le q 2))
      have hrPrev : r < q - 1 :=
        (Nat.lt_succ_self r).trans_le hqReadyLower
      have hproposalDelay : read + S.E.Δ ≤
          Protocol.proposal_time S.E (S.hc.opening_slot q) :=
        (Int.add_le_add_right hreadAction S.E.Δ).trans
          (Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt S hrq)
      have hproposalDelayPrev : read + S.E.Δ ≤
          Protocol.proposal_time S.E (S.hc.opening_slot (q - 1)) :=
        (Int.add_le_add_right hreadAction S.E.Δ).trans
          (Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt S hrPrev)
      have hproposalLeAction : Protocol.proposal_time S.E
          (S.hc.opening_slot q) ≤ S.a q := by
        calc
          Protocol.proposal_time S.E (S.hc.opening_slot q) =
              S.hc.Γ_0 S.E.Δ q :=
            (Protocol.Γ_0_eq_proposal_time S.hc S.E q).symm
          _ ≤ S.hc.Γ_1 S.E.Δ q :=
            le_of_lt (Proofs.HealingLemmas.Γ_0_lt_Γ_1 S.hc S.E.Δ_pos q)
          _ ≤ S.hc.Γ_2 S.E.Δ q :=
            le_of_lt (Proofs.HealingLemmas.Γ_1_lt_Γ_2 S.hc S.E.Δ_pos q)
          _ ≤ S.a q := Γ_2_le_a S.hc S.E.Δ_pos q
      have hproposalHor : Protocol.proposal_time S.E
          (S.hc.opening_slot q) ≤ rho.horizon :=
        hproposalLeAction.trans hactionQHor
      have hproposalCap : honestHMaxAt S rho
          (Protocol.proposal_time S.E (S.hc.opening_slot q)) ≤ H :=
        (honestHMaxAt_mono S adm.toNamedScheduleWellFormed
          hproposalLeAction).trans hactionQCap
      have hconfirmationDelay : read + S.E.Δ ≤
          Protocol.confirmation_time S.E (S.hc.opening_slot q) :=
        hproposalDelay.trans
          (Protocol.proposal_time_le_confirmation_time S.E
            (S.hc.opening_slot q))
      have hconfirmationHor : Protocol.confirmation_time S.E
          (S.hc.opening_slot q) ≤ rho.horizon := by
        rw [opening_confirmation_time_eq_action S q]
        exact hactionQHor
      have hconfirmationCap : honestHMaxAt S rho
          (Protocol.confirmation_time S.E (S.hc.opening_slot q)) ≤ H := by
        simpa only [opening_confirmation_time_eq_action S q] using hactionQCap
      have hvoteDelay : read + S.E.Δ ≤
          Protocol.vote_time S.E (S.hc.opening_slot q) :=
        hproposalDelay.trans
          (le_of_lt (Protocol.proposal_time_lt_vote_time S.E
            (S.hc.opening_slot q)))
      have hvoteHor : Protocol.vote_time S.E
          (S.hc.opening_slot q) ≤ rho.horizon :=
        (Protocol.vote_time_le_confirmation_time S.E
          (S.hc.opening_slot q)).trans hconfirmationHor
      obtain ⟨hslo, hshi, hsucc⟩ :=
        lastInteriorSlot_before_opening S.hc hqPos
      have hspos : 0 < S.hc.opening_slot q - 1 :=
        lt_of_lt_of_le (Nat.zero_lt_succ _) hslo
      have hslotPrev : S.hc.opening_slot (q - 2) + 2 ≤
          S.hc.opening_slot (q - 1) := by
        calc
          S.hc.opening_slot (q - 2) + 2 ≤
              S.hc.opening_slot (q - 2) + S.hc.R :=
            Nat.add_le_add_left S.hc.R_ge_two _
          _ = S.hc.opening_slot ((q - 2) + 1) :=
            (opening_slot_succ_eq S.hc (q - 2)).symm
          _ = S.hc.opening_slot (q - 1) :=
            congrArg S.hc.opening_slot hqPred
      have hvoteDelayPrev : read + S.E.Δ ≤
          Protocol.vote_time S.E (S.hc.opening_slot q - 1) := by
        have hprevOpeningLe : S.hc.opening_slot (q - 1) ≤
            S.hc.opening_slot q - 1 :=
          (Nat.le_succ _).trans hslo
        have hslot : S.hc.opening_slot (q - 2) + 2 ≤
            S.hc.opening_slot q - 1 :=
          hslotPrev.trans hprevOpeningLe
        exact hdelayAction.trans
          ((le_of_lt (Protocol.action_lt_vote_time_two_after S (q - 2))).trans
            (Protocol.vote_time_mono_slots S.E hslot))
      have hreadDelay : read ≤ read + S.E.Δ :=
        le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)
      have hpostSource : S.E.t_GST ≤
          Protocol.proposal_time S.E (S.hc.opening_slot q - 1) := by
        have hsourceSlot : S.hc.opening_slot (q - 1) ≤
            S.hc.opening_slot q - 1 :=
          (Nat.le_succ _).trans hslo
        have hproposalDelaySource : read + S.E.Δ ≤
            Protocol.proposal_time S.E (S.hc.opening_slot q - 1) :=
          hproposalDelayPrev.trans (proposal_time_mono S.E hsourceSlot)
        exact hpost.trans (hreadDelay.trans hproposalDelaySource)
      have hsourceLeOpening : S.hc.opening_slot q - 1 ≤
          S.hc.opening_slot q :=
        Nat.sub_le _ _
      have hpostOpeningProposal : S.E.t_GST ≤
          Protocol.proposal_time S.E (S.hc.opening_slot q) :=
        hpostSource.trans
          (proposal_time_mono S.E hsourceLeOpening)
      have hpostCone : S.E.t_GST ≤
          Protocol.vote_time S.E (S.hc.opening_slot q - 1) :=
        hpost.trans (hreadDelay.trans hvoteDelayPrev)
      have hpreviousSupportHor : Protocol.support_cutoff S.E
          (S.hc.opening_slot q - 1) ≤ rho.horizon :=
        (Protocol.support_cutoff_le_proposal_time_succ S.E
          (S.hc.opening_slot q - 1)).trans
          (by rw [hsucc]; exact hproposalHor)
      have hcutQ : S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon := by
        calc
          S.hc.Γ_neg1 S.E.Δ q ≤ S.hc.Γ_0 S.E.Δ q :=
            le_of_lt (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos q)
          _ = Protocol.proposal_time S.E (S.hc.opening_slot q) :=
            Protocol.Γ_0_eq_proposal_time S.hc S.E q
          _ ≤ rho.horizon := hproposalHor
      have hcutPrev : S.hc.Γ_neg1 S.E.Δ ((q - 1) + 1) ≤ rho.horizon := by
        simpa only [hqPredAdd] using hcutQ
      have hcutNext : S.hc.Γ_neg1 S.E.Δ ((q - 1) + 1 + 1) ≤ rho.horizon := by
        have hcutQNext : S.hc.Γ_neg1 S.E.Δ (q + 1) ≤ rho.horizon :=
          (le_of_lt (next_Γ_neg1_lt_action S q)).trans hactionNextHor
        simpa only [hqPredAdd] using hcutQNext
      have hsb : SlashableBound S rho :=
        slashableBound_of_admissible_belowOneThird S adm hfb
      have hformsJ : NamedGradeFormsAt S rho (q - 1) J := by
        simpa only [J] using hforms
      have hprop : p ∈ rho.honest := by
        simpa only [p] using hcarrier.1
      obtain ⟨hrootPre, _hmaxPre⟩ :=
        fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
          S adm hsb hfix hprop hpost hproposalDelay hproposalHor hproposalCap
      have hrootPreJ : Protocol.get_fg_root pre.toHealing.toFG = J := by
        simpa only [pre, p, proposalRead, J] using hrootPre
      have hactiveAtProposalPre : J ∈ Protocol.get_filtered_block_tree
          pre.toHealing.toFG := by
        rw [← hrootPreJ]
        simpa only [pre, Protocol.NamedStore.toHealing] using
          named_fgRoot_mem_filtered_stateBeforeTime S rho proposalRead p
      have hactiveAtProposal : J ∈ Protocol.get_filtered_block_tree
          duty.toHealing.toFG := by
        simpa only [duty, Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
          pre, p, proposalRead] using hactiveAtProposalPre
      have hactionDelayQ : read + S.E.Δ ≤ S.a q :=
        hproposalDelay.trans hproposalLeAction
      have hactiveAtAction : ∀ v ∈ rho.honest,
          J ∈ Protocol.get_filtered_block_tree
            (healStoreAt S rho v q).toFG := by
        intro v hv
        obtain ⟨hroot, _hmax⟩ :=
          fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
            S adm hsb hfix hv hpost hactionDelayQ hactionQHor hactionQCap
        have hrootJ : Protocol.get_fg_root
            (rho.storeBeforeTime S v (S.a q)).toHealing.toFG = J := by
          simpa only [J] using hroot
        change J ∈ Protocol.get_filtered_block_tree
          (rho.storeBeforeTime S v (S.a q)).toHealing.toFG
        rw [← hrootJ]
        simpa only [Protocol.NamedStore.toHealing] using
          named_fgRoot_mem_filtered_stateBeforeTime S rho (S.a q) v
      have hprevActionLe : S.a (q - 1) ≤ S.a q :=
        Assembly.a_mono S (Nat.sub_le q 1)
      have hprevActionHor : S.a (q - 1) ≤ rho.horizon :=
        hprevActionLe.trans hactionQHor
      have hprevActionCap : honestHMaxAt S rho (S.a (q - 1)) ≤ H :=
        (honestHMaxAt_mono S adm.toNamedScheduleWellFormed
          hprevActionLe).trans hactionQCap
      have hprevActionDelay : read + S.E.Δ ≤ S.a (q - 1) :=
        hdelayAction.trans (Assembly.a_mono S hqActionSucc)
      have hwindowPrev : ∀ v ∈ rho.honest,
          FinalityFilterRetainedAtRead S rho v (S.a (q - 1)) J := by
        intro v hv
        obtain ⟨hroot, _hmax⟩ :=
          fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
            S adm hsb hfix hv hpost hprevActionDelay hprevActionHor hprevActionCap
        unfold FinalityFilterRetainedAtRead
        rw [← show Protocol.get_fg_root
          (rho.storeBeforeTime S v (S.a (q - 1))).toHealing.toFG = J by
            simpa only [J] using hroot]
        simpa only [Run.storeBeforeTime] using
          named_fgRoot_mem_filtered_stateBeforeTime S rho (S.a (q - 1)) v
      have hdomainAction : DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2 ≤ S.a q :=
        FrameForward.domain_le_a S q .g2
      have hdomainHor : DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2 ≤ rho.horizon :=
        hdomainAction.trans hactionQHor
      have hdomainCap : honestHMaxAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2) ≤ H :=
        (honestHMaxAt_mono S adm.toNamedScheduleWellFormed
          hdomainAction).trans hactionQCap
      have hdomainDelay : read + S.E.Δ ≤
          DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2 :=
        hdelayAction.trans
          (NamedOutageClosure.action_le_domain S S.hc.R_ge_three
            (Nat.sub_lt hqPos (by decide : 0 < 2)))
      have hdomainWindow : ∀ v ∈ rho.honest,
          FinalityFilterRetainedAtRead S rho v
            (DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2) J := by
        intro v hv
        obtain ⟨hroot, _hmax⟩ :=
          fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
            S adm hsb hfix hv hpost hdomainDelay hdomainHor hdomainCap
        unfold FinalityFilterRetainedAtRead
        rw [← show Protocol.get_fg_root
          (rho.storeBeforeTime S v
            (DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2)).toHealing.toFG = J by
              simpa only [J] using hroot]
        simpa only [Run.storeBeforeTime] using
          named_fgRoot_mem_filtered_stateBeforeTime S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2) v
      have hmajority : HonestWeightMajority S rho.honest :=
        AlignedRoundLemmas.honestWeightMajority_of_belowOneThird
          (S := S) hfb
      have hJG1Named : namedG1At S rho p q J := by
        exact namedG1At_fixedRootTarget_of_retainedPreviousGrade
          S adm hfb hfix hqTwo hformsJ hwindowPrev hdomainWindow hpost
            hpostPreviousAction hcutQ hactionQHor hactiveAtAction hprop
            hproposalDelay hproposalHor hproposalCap
      obtain ⟨hAG1Raw, hJARaw, hAfilteredRaw⟩ :=
        relativeAnchor_of_fixedRootLock S adm hfb hfix hqTwo hformsJ
          hwindowPrev hdomainWindow hpost hpostPreviousAction hcutQ
            hactionQHor hactiveAtAction hprop hproposalDelay hproposalHor
              hproposalCap
      obtain ⟨A, hAdef⟩ :
          ∃ A : Block V,
            nodeAnchor S (proposerReadAt S rho (S.hc.opening_slot q)) q = A :=
        ⟨_, rfl⟩
      rw [hAdef] at hAG1Raw hJARaw hAfilteredRaw
      have hAG1Named : namedG1At S rho p q A := hAG1Raw
      have hJA : Block.Preceq J A := hJARaw
      have hAfiltered : A ∈ Protocol.get_filtered_block_tree
          (proposerReadAt S rho
            (S.hc.opening_slot q)).st.core.toHealing.toFG := hAfilteredRaw
      have hJAOld : Block.Preceq (rho.storeBeforeTime S w read).J A := hJA
      have hconcentration : NamedG1Concentration S rho (q - 1)
          (S.hc.opening_slot q - 1) :=
        namedG1Concentration_of_fixedRootLock S adm hcom hfb hfix hqTwo
          hforms hwindowPrev hlock hpost hproposalDelay hproposalHor
            hproposalCap hpostPreviousAction
      have hparents : FixedHeightRootOpeningParentRun S rho q :=
        fixedHeightJustificationRootOpeningParentRun_of_fixedRootLock_relative
          S adm hcom hfb hfix hqTwo hforms hwindowPrev hdomainWindow
            hactiveAtAction hlock hpost hproposalDelay hproposalHor
              hproposalCap hpostCone hpostPreviousAction hprop hAdef
                hAG1Named hAfiltered hJAOld
      have hbatch : ∀ v ∈ rho.honest,
          let n := actionReadAt S rho v q
          Internal.PhaseGrades.BatchAlignedAt S.hc
            n.st.core.toHealing.gradeView n.st.core.F rho.honest q
            (allPhasesCutoff S.E S.hc q) P.erase :=
        actionBatchAlignedAt_of_fixedRoot S adm hfb hqPos hfix hpost
          hpostPreviousAction hprevActionDelay hprevActionHor hprevActionCap
            hactionDelayQ hactionQHor hactionQCap hP hparents
      have hJparent : Block.Preceq J
          (proposedParent S rho (S.hc.opening_slot q)) :=
        hparents.liveG1Parent p hprop J hJG1Named
      have hparentB : Block.Preceq
          (proposedParent S rho (S.hc.opening_slot q))
          P.erase := by
        obtain ⟨Parent, hParent, hParentErase⟩ :=
          proposedBlockAt_parent S rho (S.hc.opening_slot q) hP
        have hParentP : NamedBlock.Preceq Parent P := by
          cases P with
          | genesis => cases hParent
          | node parent slot root votes support rows proposer =>
              simp only [NamedBlock.parent?, Option.some.injEq] at hParent
              subst Parent
              simp only [NamedBlock.Preceq, NamedBlock.preceq,
                Bool.or_eq_true]
              exact Or.inr (Proofs.NamedAncestry.named_self parent)
        rw [← hParentErase]
        exact Proofs.NamedWire.erase_preceq hParentP
      have hJB : Block.Preceq (rho.storeBeforeTime S w read).J
          P.erase :=
        Block.preceq_trans (by simpa only [J] using Block.preceq_self J)
          (Block.preceq_trans hJparent hparentB)
      have hconfirmation : ∀ v ∈ rho.honest,
          NamedSGOpeningConfirmationRead S rho (S.hc.opening_slot q) v P :=
        sgOpeningConfirmationReads_of_fixedJustificationRootNoRise
          S adm hfb hfix hP hqPos hpost hconfirmationDelay hconfirmationHor
            hconfirmationCap hpostOpeningProposal hpostPreviousAction hcarrier.1
              (by simpa only [J] using Block.preceq_self J) hJparent hparents
      have hopenPosQ : 0 < S.hc.opening_slot q :=
        Nat.mul_pos hqPos
          (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
      have hvoteData : ∀ v ∈ rho.honest, ∀ C : Block V,
          Block.Preceq (rho.storeBeforeTime S w read).J C →
          Block.Preceq C P.erase →
            C ∈ Protocol.get_filtered_block_tree
                (Internal.NamedRecoveryRead.voteDutyRead S rho v
                  (S.hc.opening_slot q)).st.core.toHealing.toFG ∧
              C ∈ voterCandidateTreeAt S rho v (S.hc.opening_slot q) :=
        openingProposal_mem_filteredTree_voteRead_of_fixedRoot S adm hfb hfix
          hP hqPos hpost hvoteDelay hconfirmationDelay hconfirmationHor
            hconfirmationCap hpostOpeningProposal hprop hJparent hJB
      have hrawExtra : ∀ v ∈ rho.honest, ∀ u,
          u ∈ Protocol.voter_view S.E
            (Internal.NamedRecoveryRead.voteDutyRead S rho v
              (S.hc.opening_slot q)).st.core.toHealing.toFG.toSG.toGoldfishStore
            (S.hc.opening_slot q) →
          u ∉ P.erase.gf_votes.toFinset →
          Protocol.equivocates P.erase.gf_votes.toFinset u.val_index = true := by
        intro v hv
        exact voter_raw_extra_equivocates_proposal_afterGST S adm hopenPosQ
          hpostSource hprop hv hproposalHor hP
            (hvoteData v hv P.erase hJB (Block.preceq_self _)).1
      /- `hpivotTransfer` above closes what is the
         `_of_pivotTransfer` pin, via
         `namedProposalPivotSuffixTransfer_of_frozenProposalNoRise`
         (SGOpeningFrozenSuffixRun, 596446d3). All six fields of its input
         record are built here: `sourceAnchor` is definitional once the
         proposer read's round is rewritten, `pivotTarget` and
         `proposalCandidate` come from `hvoteData`, the two compatibility
         fields from `hanchorCompat`, and `sameHMax` from the no-rise
         `h_max = H` at both prepared reads.
         Its candidate-score bridge is proved inside that module
         (`namedProposalCandidateScoreBridge_afterGST`, 14412be5), so nothing
         is carried here: the theorem stands on its public premises. -/
      have hAparentPre : Block.Preceq A
          (proposedParent S rho (S.hc.opening_slot q)) :=
        hparents.liveG1Parent p hprop A hAG1Named
      have hAP : Block.Preceq A P.erase :=
        Block.preceq_trans hAparentPre hparentB
      have hupperP : ∀ u ∈ rho.honest,
          Block.Preceq (actionSGBlockAt S rho u (q - 1)) P.erase := by
        intro u hu
        exact Block.preceq_trans (hparents.actionTargetParent u hu) hparentB
      have hvoteCap : honestHMaxAt S rho
          (Protocol.vote_time S.E (S.hc.opening_slot q)) ≤ H :=
        (honestHMaxAt_mono S adm.toNamedScheduleWellFormed
          (Protocol.vote_time_le_confirmation_time S.E
            (S.hc.opening_slot q))).trans hconfirmationCap
      have hroundVote : S.hc.round_of ((S.hc.opening_slot q - 1) + 1)
          = (q - 1) + 1 := by
        rw [hsucc, hqPredAdd]
        exact round_of_opening_slot_eq S.hc q
      have hanchorCompat : ∀ v ∈ rho.honest,
          Block.compatible
              (voterAnchorAt S rho v (S.hc.opening_slot q)) A = true ∧
            Block.compatible
              (voterAnchorAt S rho v (S.hc.opening_slot q)) P.erase = true := by
        intro v hv
        have hrootJ :=
          (fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
            S adm hsb hfix hv hpost hvoteDelay hvoteHor hvoteCap).1
        have hrootP : Block.Preceq
            (Protocol.get_fg_root
              (Internal.NamedRecoveryRead.voteDutyStore S rho v
                ((S.hc.opening_slot q - 1) + 1)).toHealing.toFG) P.erase := by
          have hbase : Block.Preceq
              (Protocol.get_fg_root
                (rho.storeBeforeTime S v
                  (Protocol.vote_time S.E
                    (S.hc.opening_slot q))).toHealing.toFG) P.erase := by
            rw [hrootJ]
            exact hJB
          simpa only [Internal.NamedRecoveryRead.voteDutyStore,
            Internal.NamedRecoveryRead.voteDutyRead,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom,
            Protocol.NamedStore.setClock, hsucc] using hbase
        have hanchorP := voterAnchorAt_preceq_of_previousCarriers S adm hfb
          hroundVote hpostPreviousAction
          (by simpa only [hqPredAdd] using hcutQ)
          (by rw [hsucc]; exact hvoteHor) hupperP hv hrootP
        rw [hsucc] at hanchorP
        exact ⟨Block.compatible_of_preceq_common hanchorP hAP,
          Block.compatible_of_preceq_common hanchorP (Block.preceq_self P.erase)⟩
      have hroundProposalPre :
          S.hc.round_of (proposerReadAt S rho (S.hc.opening_slot q)).st.core.s
            = q := by
        simpa only [proposerReadAt, NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
          Proofs.Optimistic.slotOf_proposal_time] using
            round_of_opening_slot_eq S.hc q
      have hsourceAnchorPre : Block.Preceq
          (Internal.PhaseGrades.nodeAnchor S
            (proposerReadAt S rho (S.hc.opening_slot q))
            (S.hc.round_of
              (proposerReadAt S rho (S.hc.opening_slot q)).st.core.s)) A := by
        rw [hroundProposalPre, hAdef]
        exact Block.preceq_self _
      have hmaxProposer :
          (proposerReadAt S rho (S.hc.opening_slot q)).st.core.h_max = H := by
        simpa only [proposerReadAt, NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock, p] using
          (fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
            S adm hsb hfix hprop hpost hproposalDelay hproposalHor
              hproposalCap).2
      have hpivotTransfer : ∀ v ∈ rho.honest,
          NamedProposalPivotSuffixTransfer S rho
            (S.hc.opening_slot q) A v P := by
        intro v hv
        have hmaxVoter :
            (Internal.NamedRecoveryRead.voteDutyRead S rho v
              (S.hc.opening_slot q)).st.core.h_max = H := by
          simpa only [Internal.NamedRecoveryRead.voteDutyRead,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom,
            Protocol.NamedStore.setClock] using
            (fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
              S adm hsb hfix hv hpost hvoteDelay hvoteHor hvoteCap).2
        exact namedProposalPivotSuffixTransfer_of_frozenProposalNoRise
          S adm hopenPosQ hpostSource hprop hv hvoteHor hP
          { sourceAnchor := hsourceAnchorPre
            pivotTarget := (hvoteData v hv A hJAOld hAP).1
            proposalCandidate :=
              (hvoteData v hv P.erase hJB (Block.preceq_self _)).2
            pivotAnchorCompatible := (hanchorCompat v hv).1
            proposalAnchorCompatible := (hanchorCompat v hv).2
            sameHMax := by rw [hmaxProposer, hmaxVoter] }
      have hfrozen : ∀ v ∈ rho.honest,
          v ∈ S.E.committee (S.hc.opening_slot q) →
            NamedSGOpeningFrozenVoteAt S rho
              (S.hc.opening_slot q - 1) A v P :=
        openingFrozenVotes_of_fixedJustificationRootLock_relative
          S adm hcom hfb hfix hP hqTwo hforms hwindowPrev hdomainWindow
            hactiveAtAction hlock hpost hproposalDelay hvoteDelay
              hconfirmationDelay hconfirmationHor hconfirmationCap hpostSource
                hpostCone hpostPreviousAction hprop hAdef hAG1Named hAfiltered
                  hJAOld hpivotTransfer hrawExtra
      obtain hnextRise | hnextActive :=
        fixedHeightJustificationRoot_namedOpeningProposal_nextActive_or_hMaxRise
          S adm hfb hfix hpost hreadAction hqlo hqhi hcarrier hP hJB hendHor
      · exact False.elim (hrise hnextRise)
      · 
        have hinputs : NamedSGProposalLifecycleInputs S rho (q - 1)
            (S.hc.opening_slot q - 1) A P :=
          { openingSlot := by
              simpa only [hqPredAdd] using hsucc
            proposal := by simpa only [hsucc] using hP
            postPreviousAction := hpostPreviousAction
            postProposalSnapshot := hpostSource
            previousSupportInHorizon := hpreviousSupportHor
            actionInHorizon := by
              simpa only [hqPredAdd] using hactionQHor
            nextCutoffInHorizon := by
              simpa only [hqPredAdd] using
                (FrameForward.domain_le_a S (q + 1) .g2).trans
                  hactionNextHor
            canonical := hlock.canonical
            concentration := hconcentration
            proposerHonest := by
              simpa only [hqPredAdd, hsucc] using hcarrier.1
            proposalAnchor := by
              simpa only [hqPredAdd, hsucc] using hAdef
            proposalAnchorG1 := by
              have hgrade : Internal.PhaseGrades.storeGrade S.E S.hc
                  (readAt S rho
                    (DecoupledConsensusModel.Protocol.domain S.E S.hc q .g1) p).st q .g1 A =
                  true := hAG1Named
              rw [NamedOutageClosure.domain_g1_eq_opening] at hgrade
              have hA : Internal.PhaseGrades.storeGrade S.E S.hc
                  (proposerReadAt S rho (S.hc.opening_slot q)).st q .g1 A =
                  true := by
                simpa only [p, proposerReadAt] using hgrade
              simpa only [hqPredAdd, hsucc] using hA
            actionTargetParent := by
              intro v hv
              simpa only [hqPredAdd, hsucc] using
                hparents.actionTargetParent v hv
            liveG1Parent := by
              intro v hv B hG1
              have hparent : Block.Preceq B
                  (proposedParent S rho (S.hc.opening_slot q)) := by
                apply hparents.liveG1Parent v hv B
                simpa only [hqPredAdd] using hG1
              rw [← hsucc] at hparent
              exact hparent
            frozenVote := by
              simpa only [hsucc] using hfrozen
            confirmationRead := by
              intro v hv
              simpa only [hsucc] using hconfirmation v hv
            actionBatchAligned := by
              intro v hv
              simpa only [hqPredAdd, hsucc] using hbatch v hv
            actionRootPreceq := by
              intro v hv
              simpa only [hqPredAdd] using
                actionRootPreceq_of_namedConfirmationRead S
                  (hconfirmation v hv)
            nextActive := by
              intro v hv
              simpa only [hqPredAdd, hsucc] using hnextActive.2 v hv }
        have hroundProposal :
            S.hc.round_of (proposerReadAt S rho (S.hc.opening_slot q)).st.core.s = q := by
          simpa only [proposerReadAt, NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
            Proofs.Optimistic.slotOf_proposal_time] using
              round_of_opening_slot_eq S.hc q
        have hsourceAnchorNamed : Block.Preceq
            (Protocol.get_sg_root_with
              (NamedProfile.gradeContract
                (proposerReadAt S rho (S.hc.opening_slot q)).cache)
              S.E S.hc
              (proposerReadAt S rho (S.hc.opening_slot q)).st.core.toHealing
              (S.hc.round_of
                (proposerReadAt S rho (S.hc.opening_slot q)).st.core.s)) A := by
          change Block.Preceq
            (nodeAnchor S (proposerReadAt S rho (S.hc.opening_slot q))
              (S.hc.round_of
                (proposerReadAt S rho (S.hc.opening_slot q)).st.core.s)) A
          rw [hroundProposal, hAdef]
          exact Block.preceq_self _
        have hconeA : NamedHonestVotesCone S rho
            (S.hc.opening_slot q - 1) (fun X => Block.Preceq A X) := by
          have hAG1AtRound : namedG1At S rho p ((q - 1) + 1) A := by
            simpa only [hqPredAdd] using hAG1Named
          exact hconcentration.supported hprop hAG1AtRound
        have hAparent : Block.Preceq A
            (proposedParent S rho (S.hc.opening_slot q)) :=
          hparents.liveG1Parent p hprop A hAG1Named
        have hconfPrevHor : Protocol.confirmation_time S.E
            (S.hc.opening_slot q - 1) ≤ rho.horizon := by
          rw [Protocol.confirmation_time_eq_support_cutoff_succ, hsucc]
          exact (Protocol.support_cutoff_le_confirmation_time S.E
            (S.hc.opening_slot q)).trans hconfirmationHor
        have hstores : Protocol.VoteStoresExtend S rho
            (S.hc.opening_slot q) P := by
          have hPsucc : proposedBlockAt S rho
              ((S.hc.opening_slot q - 1) + 1) = some P := by
            rw [hsucc]
            exact hP
          have hscoreSucc : ∀ v ∈ rho.honest, ∀ C,
              C ∈ namedWalkSourceTree S rho
                ((S.hc.opening_slot q - 1) + 1) →
              C ∈ namedWalkTargetTree S rho
                ((S.hc.opening_slot q - 1) + 1) v P →
              namedWalkTargetScore S rho
                  ((S.hc.opening_slot q - 1) + 1) v C =
                namedWalkSourceScore S rho
                  ((S.hc.opening_slot q - 1) + 1) C := by
            intro v hv C hCsource hCtarget
            exact namedWalkScore_target_eq_source_of_proposalCandidate
              (S := S) (rho := rho) adm (s := S.hc.opening_slot q - 1)
              (P := P) hPsucc hpostSource
              (by rw [hsucc]; exact hprop)
              (by rw [hsucc]; exact hvoteHor)
              (by rw [hsucc]; exact hproposalHor)
              hv (by
                rw [hsucc]
                exact (hvoteData v hv P.erase hJB (Block.preceq_self _)).2)
              (by rw [hsucc]; exact hrawExtra v hv)
              C hCsource hCtarget
          have hsourceAnchorSucc : Block.Preceq
              (Protocol.get_sg_root_with
                (NamedProfile.gradeContract
                  (proposerReadAt S rho
                    ((S.hc.opening_slot q - 1) + 1)).cache)
                S.E S.hc
                (proposerReadAt S rho
                  ((S.hc.opening_slot q - 1) + 1)).st.core.toHealing
                (S.hc.round_of
                  (proposerReadAt S rho
                    ((S.hc.opening_slot q - 1) + 1)).st.core.s)) A := by
            rw [hsucc]
            exact hsourceAnchorNamed
          have hAparentSucc : Block.Preceq A
              (proposedParent S rho
                ((S.hc.opening_slot q - 1) + 1)) := by
            rw [hsucc]
            exact hAparent
          have hfrozenSucc : ∀ v ∈ rho.honest,
              v ∈ S.E.committee ((S.hc.opening_slot q - 1) + 1) →
              NamedSGOpeningFrozenVoteAt S rho
                (S.hc.opening_slot q - 1) A v P := by
            intro v hv hcommittee
            apply hfrozen v hv
            rw [← hsucc]
            exact hcommittee
          have hstoresPre :=
            fixedHeightJustificationRoot_namedOpeningVoteStoresExtend
              S adm hcom hspos hpostCone hconfPrevHor hPsucc
                (by rw [hsucc]; exact hprop) hconeA hsourceAnchorSucc
                hAparentSucc hfrozenSucc hscoreSucc
          rw [hsucc] at hstoresPre
          exact hstoresPre
        have hopenPos : 0 < S.hc.opening_slot q :=
          Nat.mul_pos hqPos
            (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
        have hnames : NamedHonestVotesName S rho
            (S.hc.opening_slot q) P.erase :=
          namedHonestVotesName_of_namedVoteStoresExtend
            S adm hopenPos hvoteHor hstores
        have hdomainG0Hor : DecoupledConsensusModel.Protocol.domain S.E S.hc q .g0 ≤
            rho.horizon :=
          (FrameForward.domain_le_a S q .g0).trans hactionQHor
        have hwindow : RelativeCarrierWindowAt S rho (q - 1) .g0 :=
          relativeCarrierWindowAt_of_fixedRoot S adm hfb hqPos hfix hpost
            hpostPreviousAction hprevActionDelay hprevActionHor hprevActionCap
              hactionDelayQ hactionQHor hactionQCap hdomainG0Hor
        have hg0 : ∀ v ∈ rho.honest,
            nodeClear S (actionReadAt S rho v q) q P.erase = true :=
          g0ClearAtAction_of_relativeCarrierWindow_of_openingParentRun S adm
            hfb hqPos hactionQHor (hdomainAction.trans hactionQHor)
            hpostPreviousAction hwindow
              hparents hP
        have hcover : ActionCarriersCover S rho q P.erase := by
          intro v hv
          have hlive : (actionReadAt S rho v q).st.core.live_confirmed =
              P.erase := by
            simpa only [hqPredAdd] using hinputs.liveConfirmedAtAction adm hcom v hv
          have heq : actionSGBlockAt S rho v q = P.erase := by
            apply actionSGBlockAt_eq_liveConfirmed_of_batchAligned S
              (Can := P.erase) (D := P.erase)
              (A := nodeAnchor S (actionReadAt S rho v q) q)
            · exact hlive
            · exact hbatch v hv
            · exact Block.preceq_self _
            · rfl
            · simpa only [nodeAnchor, nodeRead] using
                actionRootPreceq_of_namedConfirmationRead S
                  (hconfirmation v hv)
            · exact hg0 v hv
          rw [heq]
          exact Block.preceq_self _
        have hnextGrade : NamedGradeFormsAt S rho (q + 1) P.erase :=
          namedGradeFormsAt_succ_of_actionCarriersCover_and_next_active
            S adm hmajority hcover
              (hpostPreviousAction.trans
                (Assembly.a_mono S (Nat.sub_le q 1)))
              (by simpa only [hqPredAdd] using hcutNext)
              hnextActive.1 hnextActive.2
        have hrun : NamedRun.blockInRun S rho P :=
          proposedBlockAt_blockInRun_of_admissible
            S adm.toNamedAdmissibleCore (S.hc.opening_slot q) hopenPos
              hcarrier.1 hproposalHor hP
        have hlifecycle : NamedRawOpeningLifecycleAt S rho q P :=
          { roundPositive := hqPos
            proposal := hP
            proposerHonest := hcarrier.1
            proposalInHorizon := hproposalHor
            runBlock := hrun
            liveConfirmed := by
              intro v hv
              simpa only [hqPredAdd] using
                hinputs.liveConfirmedAtAction adm hcom v hv
            actionCover := hcover
            gradeNext := hnextGrade }
        have hpacket : NamedSGProposalLifecyclePacket S rho (q - 1)
            (S.hc.opening_slot q - 1) P :=
          { openingSlot := by simpa only [hqPredAdd] using hsucc
            proposal := by simpa only [hqPredAdd] using hP
            actionTargetParent := by
              intro v hv
              simpa only [hqPredAdd] using hparents.actionTargetParent v hv
            liveG1Parent := by
              intro v hv X hG1
              simpa only [hqPredAdd] using
                hparents.liveG1Parent v hv X (by
                  simpa only [hqPredAdd] using hG1)
            honestVotes := by simpa only [hqPredAdd] using hnames
            genuineConfirmation := by
              intro v hv
              simpa only [hqPredAdd, hsucc] using
                hinputs.genuineConfirmation adm hcom hv
            g0ClearAtAction := by
              simpa only [hqPredAdd] using hg0
            lifecycle := by simpa only [hqPredAdd] using hlifecycle }
        simpa only [hsucc] using hpacket


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
