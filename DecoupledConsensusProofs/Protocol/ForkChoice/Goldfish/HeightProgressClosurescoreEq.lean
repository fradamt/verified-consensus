module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGProposalLifecycle

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Height-progress closure: the opening score-equality pin

The lifecycle producer
`fixedHeightJustificationRoot_boundedProposalLifecycle_of_proposerRecurrence_of_faultBound`
(FixedHeightRootClaimFourOuterRun.lean:36-106) carries a pinned premise
`_of_scoreEq`: at the opening slot of every round, the proposer's prepared
walk source view and each honest voter's prepared target view give the same
Goldfish score on every common candidate.

`NamedSGOpeningFrozenVoteAt.scoreEq` (SGProposalLifecycleRun.lean:364) already
proves that equality, but only from a full `NamedSGProposalLifecycleInputs`
package plus a `NamedSGOpeningFrozenVoteAt` witness. Inspection of that proof
shows it consumes exactly five facts from the package (the proposal witness,
The previous-slot GST bound, the honest slot proposer, and the two horizon
bounds) and exactly two from the frozen-vote witness (the proposal is a
candidate in the voter's prepared tree, and every raw vote outside the
proposal snapshot equivocates).

`namedWalkScore_target_eq_source_of_proposalCandidate` below is that same
route over those seven facts alone, with no lifecycle package, no pivot block
`A`, and no committee membership for the voter. `heightProgress_pin_scoreEq_of_openingData`
then closes the pinned premise verbatim from a per-round bundle of those facts.

The bare pin is NOT provable from the public premises: it quantifies over
every round `q`, and `proposedBlockAt S rho s = some P` is the block the
*named proposal duty computes on the slot proposer's prepared read*
(ProposalSources.lean:41), which is defined whether or not that proposer is
honest. Both halves of the score equality are honest-relay statements between
the proposer's read and the voter's read, so a Byzantine (or `q = 0`) opening
proposer defeats them. The residual is recorded in the branches report.
-/

/-! ## Local copies of the private lifecycle helpers

`SGProposalLifecycleRun` keeps these four `private`, so the route above cannot
reach them by name. They are copied verbatim under a proof branch prefix; the
originals stay untouched and keep their consumers. -/



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



private theorem pinScoreEq_voterCandidateTree_subset_filtered
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


private theorem pinScoreEq_resolved_blocks_eq
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
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
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hsource sourceTime
      (Proofs.HealingLemmas.find?_mem hH)
  obtain ⟨KN, hKNe, hKNrun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hreader readerTime
      (Proofs.HealingLemmas.find?_mem hK)
  have hroot : HN.root = KN.root := by
    rw [← Proofs.NamedWire.erase_root HN, ← Proofs.NamedWire.erase_root KN, hHNe, hKNe]
    exact (Proofs.HealingLemmas.find?_root hH).trans
      (Proofs.HealingLemmas.find?_root hK).symm
  have heq := adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
    HN KN hHNrun hKNrun HN KN (Or.inl (Proofs.NamedAncestry.named_self HN))
      (Or.inr (Proofs.NamedAncestry.named_self KN)) hroot
  calc
    H = HN.erase := hHNe.symm
    _ = KN.erase := congrArg NamedBlock.erase heq
    _ = K := hKNe


private theorem pinScoreEq_index_lt_strictEventIndex_of_time_lt
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


private theorem pinScoreEq_body_held_at_public_cut
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
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
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed read) reader
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
      Protocol.HonestWeightMajority.acceptsAt_block_lt_of_stamp_before
        S adm hreader haccepts (Nat.succ_le_of_lt hi) hpublic hstampN
    obtain ⟨hhandle, -, hpost⟩ := haccepts
    obtain ⟨hindex, e, he, -, het⟩ := hhandle
    have hiCut : i < strictEventIndex rho cut := by
      apply pinScoreEq_index_lt_strictEventIndex_of_time_lt
        S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed he
      simpa only [← het] using ht
    have hBi : B ∈ (rho.stateBefore S (i + 1) reader).st.bodies := by
      simpa only [Object.processed, NamedReceipt.processed,
        decide_eq_true_eq] using hpost
    have hBCut := NamedBodyRetention.stateBefore_bodies_mono
      S rho reader (Nat.succ_le_of_lt hiCut) hBi
    change B ∈ ((Run.stateBeforeTime S rho cut) reader).st.bodies
    unfold Run.stateBeforeTime
    rw [stateBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed cut]
    exact hBCut


/-- The candidate-local score equality of `NamedSGOpeningFrozenVoteAt.scoreEq`,
over the facts that proof actually uses: no lifecycle package, no pivot, and
no committee membership for the honest voter. -/
theorem namedWalkScore_target_eq_source_of_proposalCandidate
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {s : Slot} {P : NamedBlock V}
    (hproposal : proposedBlockAt S rho (s + 1) = some P)
    (hpostProposalSnapshot : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hproposerHonest : S.E.proposer (s + 1) ∈ rho.honest)
    (hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    (hproposalHor : Protocol.proposal_time S.E (s + 1) ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest)
    (hproposalCandidate : P.erase ∈ voterCandidateTreeAt S rho v (s + 1))
    (hrawExtra : ∀ u,
      u ∈ Protocol.voter_view S.E
        (voteDutyRead S rho v (s + 1)).st.core.toHealing.toFG.toSG.toGoldfishStore (s + 1) →
      u ∉ P.erase.gf_votes.toFinset →
      Protocol.equivocates P.erase.gf_votes.toFinset u.val_index = true) :
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
    hproposalCandidate
  have hPtargetFiltered : P.erase ∈
      Protocol.get_filtered_block_tree target.st.core.toHealing.toFG := by
    apply pinScoreEq_voterCandidateTree_subset_filtered S.E target.st.core
    simpa only [target, voterCandidateTreeAt] using hPtargetCandidate
  have hPtargetT : P.erase ∈ target.st.core.T :=
    Proofs.Records.get_filtered_block_tree_subset _ hPtargetFiltered
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (Protocol.vote_time S.E (s + 1))
  have hPprefix : P.erase ∈ (rho.stateBefore S n v).st.core.T := by
    simpa only [target, voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Run.storeBeforeTime, hn] using hPtargetT
  have hslots : ∀ u ∈ P.gf_votes, u.slot + 1 = P.slot := by
    intro u hu
    obtain ⟨np, hnp, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
        (Protocol.proposal_time S.E (s + 1))
    have huFin : u ∈ source.st.core.pool (source.st.core.s - 1) := by
      change u ∈ (proposerReadAt S rho (s + 1)).st.core.pool
        ((proposerReadAt S rho (s + 1)).st.core.s - 1)
      rw [← Protocol.proposedBlock_raw_eq_proposer_pool
        S rho (s + 1) hproposal]
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
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (S.E.proposer (s + 1)) np).slot s u huPool
    calc
      u.slot + 1 = s + 1 := congrArg (· + 1) hus
      _ = P.slot := (proposedBlockAt_slot S rho (s + 1) hproposal).symm
  have hrawSubset : P.gf_votes.toFinset ⊆ targetRaw := by
    intro u hu
    have hPslot : P.erase.slot = target.st.core.toHealing.s := by
      rw [Proofs.NamedWire.erase_slot,
        proposedBlockAt_slot S rho (s + 1) hproposal]
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
        hrawExtra u (by simpa only [targetRaw, htargetSlot] using hu)
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
        have hCfiltered := pinScoreEq_voterCandidateTree_subset_filtered
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
        · exact hpostProposalSnapshot.trans
            (Protocol.proposal_time_mono S.E (Nat.le_succ s))
      have hrelay := NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
        S rho adm.toNamedAdmissibleCore (S.E.proposer (s + 1))
        hproposerHonest v hv HN (Protocol.proposal_time S.E (s + 1))
        (Protocol.vote_time S.E (s + 1))
        (Protocol.vote_time S.E (s + 1)) hHNbody hdeadline le_rfl
        hvoteHor (by
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
            S rho (s + 1) hproposal] at huList
          have hraw := (List.mem_filter.mp huList).1
          rw [Protocol.proposedBlock_gf_votes
            S rho (s + 1) hproposal]
          exact hraw)
      have huTarget : u ∈ targetSupport := by
        exact Protocol.mem_voter_support_view_of_carried S.E
          target.st.core.toHealing.toFG.toSG.toGoldfishStore hPtargetT
          (by rw [Proofs.NamedWire.erase_slot,
            proposedBlockAt_slot S rho (s + 1) hproposal, htargetSlot])
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
            exact Proofs.Optimistic.carried_support_subset_of_mem_T
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
          have hKNfreeze := pinScoreEq_body_held_at_public_cut
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
            · exact hpostProposalSnapshot.trans
                (by
                  unfold Protocol.proposal_time Protocol.view_freeze
                  linarith [S.E.Δ_pos])
          have hrelay := NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
            S rho adm.toNamedAdmissibleCore v hv (S.E.proposer (s + 1))
            hproposerHonest KN (Protocol.view_freeze S.E s)
            (Protocol.proposal_time S.E (s + 1))
            (Protocol.proposal_time S.E (s + 1)) hKNfreeze hdeadline le_rfl
            hproposalHor (by
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
                S rho (s + 1) hproposal]
            change u ∈ Protocol.proposer_support_view
              (proposerReadAt S rho (s + 1)).st.core.toHealing.toFG.toSG.toGoldfishStore
              (proposerReadAt S rho (s + 1)).st.core.toHealing.s
            rw [Protocol.proposer_support_view, List.mem_filter]
            refine ⟨?_, ?_⟩
            · rw [Protocol.proposedBlock_gf_votes
                S rho (s + 1) hproposal] at huList
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
              hrawExtra u
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
        have hDeq : D = P.erase := unique_slot_block_in_store
          S adm (Nat.succ_pos s) hproposerHonest
          hDprefix hPprefix (by simpa only [htargetSlot] using hD.2)
          (by rw [Proofs.NamedWire.erase_slot,
            proposedBlockAt_slot S rho (s + 1) hproposal])
        subst D
        have huSource : u ∈ P.gf_support_votes.toFinset := by
          simpa only [Proofs.NamedWire.erase_goldfish_support] using huD.1
        obtain ⟨K, hfindTarget, hCK⟩ :=
          Protocol.targets_under_iff.mp htargets
        have hresolvedSource : Protocol.resolved source.st.core.T u = true := by
          have huList : u ∈ P.gf_support_votes :=
            List.mem_toFinset.mp huSource
          rw [Protocol.proposedBlock_gf_support_votes
            S rho (s + 1) hproposal] at huList
          exact of_decide_eq_true (by
            simpa only [source, proposalDutyRead, Protocol.Store.toHealing]
              using (List.mem_filter.mp huList).2)
        obtain ⟨H, hfindSource⟩ : ∃ H, Block.find? source.st.core.T u.head = some H := by
          cases hfind : Block.find? source.st.core.T u.head with
          | none => simp [Protocol.resolved, hfind] at hresolvedSource
          | some H => exact ⟨H, rfl⟩
        have hHK : H = K := pinScoreEq_resolved_blocks_eq
          S adm hproposerHonest hv
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
      S rho (s + 1) hproposal,
    Protocol.proposedBlock_gf_support_votes S rho (s + 1) hproposal,
    proposalInputAt, Protocol.proposal_input_with,
    Protocol.with_proposal_input, id_eq, proposalDutyRead,
    Protocol.Store.toHealing]
    using hscore


#print axioms namedWalkScore_target_eq_source_of_proposalCandidate



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
