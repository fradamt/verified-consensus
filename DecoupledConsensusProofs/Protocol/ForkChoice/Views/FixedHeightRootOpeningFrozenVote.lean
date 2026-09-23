module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FixedHeightRootOpeningConfirmationRead
public import DecoupledConsensusProofs.Protocol.Grades.FixedHeightRootOpeningParentComplete
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGOpeningFrozenSuffix
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FixedRootGradePersistence
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedCeilingStep
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedViability

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Fixed-height opening frozen votes

The fixed root supplies the common one-step frontier at the opening proposer
and each honest opening vote. The preceding action ceiling controls selected
fresh anchors; the callback-free support-alignment path controls the relative
fallback. These local facts construct the frozen proposal comparison for each
honest committee voter.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.NamedRecoveryRead
open Proofs.Optimistic
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]



theorem openingFrozenVotes_of_fixedJustificationRootParentData
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {w : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho H w read)
    {q : Round} {A : Block V} {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot q) = some P)
    (hq : 0 < q)
    (hpostRead : S.E.t_GST ≤ read)
    (hproposalDelay : read + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hvoteDelay : read + S.E.Δ ≤
      Protocol.vote_time S.E (S.hc.opening_slot q))
    (hconfirmationDelay : read + S.E.Δ ≤
      Protocol.confirmation_time S.E (S.hc.opening_slot q))
    (hconfirmationHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hconfirmationCap : honestHMaxAt S rho
      (Protocol.confirmation_time S.E (S.hc.opening_slot q)) ≤ H)
    (hpostSource : S.E.t_GST ≤ Protocol.proposal_time S.E
      (S.hc.opening_slot q - 1))
    (hpostPreviousAction : S.E.t_GST ≤ S.a (q - 1))
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    (hJA : Block.Preceq (rho.storeBeforeTime S w read).J A)
    (hAparent : Block.Preceq A
      (proposedParent S rho (S.hc.opening_slot q)))
    (hparents : FixedHeightRootOpeningParentRun S rho q)
    (_of_pivotTransfer : ∀ v ∈ rho.honest,
      NamedProposalPivotSuffixTransfer S rho (S.hc.opening_slot q) A v P)
    (_of_frozenSuffix : ∀ v ∈ rho.honest, ∀ u,
      u ∈ Protocol.voter_view S.E
        (voteDutyRead S rho v (S.hc.opening_slot q)).st.core.toHealing.toFG.toSG.toGoldfishStore
        (S.hc.opening_slot q) →
      u ∉ P.erase.gf_votes.toFinset →
      Protocol.equivocates P.erase.gf_votes.toFinset u.val_index = true) :
    ∀ v ∈ rho.honest, v ∈ S.E.committee (S.hc.opening_slot q) →
      NamedSGOpeningFrozenVoteAt S rho (S.hc.opening_slot q - 1) A v P := by
  let o := S.hc.opening_slot q
  let s := o - 1
  let J := (rho.storeBeforeTime S w read).J
  have hqOne : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hq)
  have hopenPos : 0 < o := by
    exact Nat.mul_pos hq
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hopenOne : 1 ≤ o := Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hopenPos)
  have hopen : s + 1 = o := Nat.sub_add_cancel hopenOne
  have hproposalHor : Protocol.proposal_time S.E o ≤ rho.horizon :=
    (Protocol.proposal_time_le_confirmation_time S.E o).trans hconfirmationHor
  have hvoteHor : Protocol.vote_time S.E o ≤ rho.horizon :=
    (Protocol.vote_time_le_confirmation_time S.E o).trans hconfirmationHor
  have hvoteCap : honestHMaxAt S rho (Protocol.vote_time S.E o) ≤ H :=
    (honestHMaxAt_mono S adm.toNamedScheduleWellFormed
      (Protocol.vote_time_le_confirmation_time S.E o)).trans hconfirmationCap
  have hpostProposal : S.E.t_GST ≤ Protocol.proposal_time S.E o :=
    (hpostRead.trans (Int.le_add_of_nonneg_right S.E.Δ_pos.le)).trans
      hproposalDelay
  have hAparent' : Block.Preceq A (proposedParent S rho o) := by
    simpa only [o] using hAparent
  have hparentP : Block.Preceq (proposedParent S rho o) P.erase := by
    obtain ⟨parent, hp, he⟩ := proposedBlockAt_parent S rho o hP
    have hparentNamed : NamedBlock.Preceq parent P := by
      cases P with
      | genesis => cases hp
      | node parent' slot root votes support rows proposer =>
          simp only [NamedBlock.parent?, Option.some.injEq] at hp
          subst parent
          simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
          exact Or.inr (Proofs.NamedAncestry.named_self parent')
    rw [← he]
    exact Proofs.NamedWire.erase_preceq hparentNamed
  have hAP : Block.Preceq A P.erase := Block.preceq_trans hAparent' hparentP
  have hJP : Block.Preceq J P.erase := Block.preceq_trans hJA hAP
  have hPrun : RunBlock S rho P :=
    proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
      o hopenPos hprop hproposalHor hP
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
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hcut : S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon := by
    exact (le_of_lt (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos q)).trans
      (by simpa only [Protocol.Γ_0_eq_proposal_time] using hproposalHor)
  have hadmit := openingProposalAdmittedBeforeVote_of_fixedJustificationRootNoRise
    S adm hfb hfix hP hq hpostRead hconfirmationDelay hconfirmationHor
      hconfirmationCap hpostProposal hprop hJA hAparent'
  intro v hv _hcommittee
  let target := voteDutyRead S rho v o
  let targetStore := Internal.NamedRecoveryRead.voteDutyStore S rho v o
  have hrootMax :=
    fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
      S adm hsb hfix hv hpostRead (by simpa only [o] using hvoteDelay)
        (by simpa only [o] using hvoteHor)
        (by simpa only [o] using hvoteCap)
  have hroot : Protocol.get_fg_root target.st.core.toHealing.toFG = J := by
    simpa only [target, voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      J, o] using hrootMax.1
  have hmax : target.st.core.h_max = H := by
    simpa only [target, voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      o] using hrootMax.2
  have hPtree : P.erase ∈ target.st.core.T := by
    have hmem := (admittedBefore_mem_and_stamp_at S
      adm.toNamedScheduleWellFormed (hadmit v hv) (le_refl _)).1
    simpa only [target, voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      o] using hmem
  have hPprocessed : P.erase ∈ Protocol.voter_processed_block_tree S.E
      target.st.core.toHealing.toFG.toSG.toGoldfishStore target.st.core.s := by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    refine ⟨hPtree, Or.inr ⟨P.erase, ⟨hPtree, ?_⟩, Block.preceq_self _⟩⟩
    rw [Proofs.NamedWire.erase_slot, proposedBlockAt_slot S rho o hP]
    have hslot : target.st.core.s = o := by
      simpa only [target] using Proofs.Optimistic.voteDutyRead_slot S rho v o
    exact hslot.symm
  have hPfiltered : P.erase ∈
      Protocol.get_filtered_block_tree target.st.core.toHealing.toFG := by
    have hraw := fixedRootGrade_mem_filtered_of_exactRoot S adm hv hPrun
      (by simpa only [target, voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
        using hPtree)
      hJP hPheight (by simpa only [target, voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
        using hroot)
      (by simpa only [target, voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
        using hmax)
    simpa only [target, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
      using hraw
  have hmaxP : target.st.core.h_max ≤
      (Protocol.derive_named S.E S.cfg P).h + 1 := by
    rw [hmax]
    have hHone : 1 ≤ H := Nat.le_of_lt
      (Nat.sub_pos_iff_lt.mp hfix.targetHeightPositive)
    calc
      H = H - 1 + 1 := (Nat.sub_add_cancel hHone).symm
      _ ≤ (Protocol.derive_named S.E S.cfg P).h + 1 :=
        Nat.add_le_add_right hPheight 1
  have hPprocessedStore : P.erase ∈ Protocol.voter_processed_block_tree S.E
      (Internal.NamedRecoveryRead.voteDutyStore S rho v (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (Internal.NamedRecoveryRead.voteDutyStore S rho v (s + 1)).toHealing.s := by
    simpa only [target, voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      hopen] using hPprocessed
  have hPfilteredStore : P.erase ∈ Protocol.get_filtered_block_tree
      (Internal.NamedRecoveryRead.voteDutyStore S rho v (s + 1)).toHealing.toFG := by
    simpa only [target, voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      hopen] using hPfiltered
  have hmaxPStore : (Internal.NamedRecoveryRead.voteDutyStore S rho v (s + 1)).h_max ≤
      (Protocol.derive_named S.E S.cfg P).h + 1 := by
    simpa only [target, voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      hopen] using hmaxP
  have hFJ : Block.Preceq
      (Internal.NamedRecoveryRead.voteDutyStore S rho v (s + 1)).F
      (Internal.NamedRecoveryRead.voteDutyStore S rho v (s + 1)).J := by
    simpa only [Internal.NamedRecoveryRead.voteDutyStore, hopen] using
      (Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        S rho (Protocol.vote_time S.E o) v)
  have hpc : ParentClosed
      (Internal.NamedRecoveryRead.voteDutyStore S rho v (s + 1)) := by
    simpa only [Internal.NamedRecoveryRead.voteDutyStore, hopen] using
      (Proofs.NamedStoreBridge.parentClosed_stateBeforeTime
        S rho (Protocol.vote_time S.E o) v)
  have hPT : P.erase ∈
      (Internal.NamedRecoveryRead.voteDutyStore S rho v (s + 1)).T :=
    Proofs.Records.get_filtered_block_tree_subset _ hPfilteredStore
  have hcandidate_of_preceq : ∀ {C : Block V}, Block.Preceq C P.erase →
      Block.Preceq
        (Protocol.get_fg_root
          (Internal.NamedRecoveryRead.voteDutyStore S rho v (s + 1)).toHealing.toFG) C →
      C ∈ voterCandidateTreeAt S rho v (s + 1) := by
    intro C hCP hrootC
    have hCT : C ∈
        (Internal.NamedRecoveryRead.voteDutyStore S rho v (s + 1)).T :=
      Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2 C P.erase hPT hCP
    have hCfiltered := Proofs.Records.mem_filtered_of_preceq
      (st := (Internal.NamedRecoveryRead.voteDutyStore
        S rho v (s + 1)).toHealing.toFG)
      (by simpa only [Block.Preceq, Protocol.Store.toHealing] using hFJ)
      hPfilteredStore hCT hCP hrootC
    have hc := namedAncestorCandidate_of_processedDescendant_and_hMax
      S adm hv (s := s) hPprocessedStore hPrun hCP
      hCfiltered hmaxPStore
    simpa only [voterCandidateTreeAt,
      Proofs.Optimistic.voter_candidate_tree_eq_protocol_voter_filtered_block_tree]
      using hc
  have hrootPStore : Block.Preceq
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyStore S rho v (s + 1)).toHealing.toFG)
      P.erase := by
    have hrootPCurrent : Block.Preceq
        (Protocol.get_fg_root target.st.core.toHealing.toFG) P.erase := by
      rw [hroot]
      exact hJP
    simpa only [targetStore, target, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      hopen] using hrootPCurrent
  have hPcandidate : P.erase ∈ voterCandidateTreeAt S rho v (s + 1) :=
    hcandidate_of_preceq (Block.preceq_self P.erase) hrootPStore
  have hrootA : Block.Preceq
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyStore S rho v (s + 1)).toHealing.toFG) A :=
    by
      have hrootACurrent : Block.Preceq
          (Protocol.get_fg_root target.st.core.toHealing.toFG) A := by
        rw [hroot]
        exact hJA
      simpa only [targetStore, target, voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        hopen] using hrootACurrent
  have hAcandidate : A ∈ voterCandidateTreeAt S rho v (s + 1) :=
    hcandidate_of_preceq hAP hrootA
  have hAne : A ≠ P.erase := by
    intro heq
    have hPparent : Block.Preceq P.erase (proposedParent S rho o) := by
      simpa only [← heq] using hAparent'
    have heqParent := Block.preceq_antisymm hPparent hparentP
    obtain ⟨parent, hp, he⟩ := proposedBlockAt_parent S rho o hP
    have hrawParent : P.erase.parent? = some parent.erase := by
      simpa only [Proofs.NamedWire.erase_parent_optional, hp, Option.map_some]
    rw [he, heqParent] at hrawParent
    have hdepth := Protocol.depth_of_parent? hrawParent
    omega
  have hpivotCandidate : A ∈
      (voterCandidateTreeAt S rho v (s + 1)).erase P.erase :=
    Finset.mem_erase.mpr ⟨hAne, hAcandidate⟩
  have hupperP : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u (q - 1)) P.erase := by
    intro u hu
    exact Block.preceq_trans (hparents.actionTargetParent u hu) hparentP
  have hrootP : Block.Preceq
      (Protocol.get_fg_root target.st.core.toHealing.toFG) P.erase := by
    rw [hroot]
    exact hJP
  have hround : S.hc.round_of (s + 1) = (q - 1) + 1 := by
    rw [Nat.sub_add_cancel hqOne, hopen]
    exact round_of_opening_slot_eq S.hc q
  have hanchorP := voterAnchorAt_preceq_of_previousCarriers S adm hfb hround
    hpostPreviousAction (by simpa only [Nat.sub_add_cancel hqOne] using hcut)
      (by simpa only [hopen] using hvoteHor) hupperP hv
      (by simpa only [targetStore, target, voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        hopen] using hrootP)
  refine
    { proposalCandidate := hPcandidate
      pivotCandidate := hpivotCandidate
      pivotAnchorCompatible :=
        Block.compatible_of_preceq_common hanchorP hAP
      proposalAnchorCompatible :=
        Block.compatible_of_preceq_common hanchorP (Block.preceq_self P.erase)
      pivotPath := ?_
      suffix := by rw [hopen]; exact _of_pivotTransfer v hv
      rawExtra := by rw [hopen]; exact _of_frozenSuffix v hv }
  intro _hanchorA C hanchorC hCne hCA
  by_cases hCAeq : C = A
  · subst C
    exact Finset.mem_erase.mpr ⟨hAne, hAcandidate⟩
  · exact Finset.mem_erase.mpr
      ⟨fun hCP => hAne (Block.preceq_antisymm hAP (by simpa only [hCP] using hCA)),
        hcandidate_of_preceq (Block.preceq_trans hCA hAP)
          (by
            let read := voteDutyRead S rho v (s + 1)
            have hrootAnchor := NamedOutageClosure.fg_root_preceq_anchor
              S.E S.hc read.st.core.toHealing (S.hc.round_of read.st.core.s)
              (DecoupledConsensusModel.Protocol.readFrame read.cache read.st.core.toHealing
                (S.hc.round_of read.st.core.s)).g1
            exact Block.preceq_trans
              (by simpa only [read, voterAnchorAt,
                Internal.PhaseGrades.nodeAnchor, Internal.PhaseGrades.nodeRead,
                NamedProfile.gradeContract, DecoupledConsensusModel.Protocol.frameContract,
                DecoupledConsensusModel.Protocol.frameGradeRead] using hrootAnchor)
              hanchorC)⟩

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
