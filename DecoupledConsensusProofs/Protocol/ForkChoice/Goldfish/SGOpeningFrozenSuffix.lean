module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGProposalLifecycle
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryProposalCapInputs
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.OpeningActiveCarrier

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Post-GST frozen proposal suffix transfer

The voter walk uses `voter_processed_block_tree`, not the full processed tree.
This makes target-only suffix reflection local and finite. A target candidate
outside the current proposal chain, together with its viability witness, must
have been stamped before the view freeze. Both blocks therefore reach the
honest proposer before its proposal read. Candidates on the proposal chain are
already ancestors of the exact proposal parent.

The transfer below uses equality of the source and target height frontiers. It
uses no recovery cap and no target-majority callback.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Restricting the voter processed domain only removes candidates from the
full filtered tree. -/
theorem frozenVoterCandidateTree_subset_filtered
    (E : Env V) (st : Protocol.HealingStore V) :
    Proofs.Optimistic.voter_candidate_tree E st ⊆
      Protocol.get_filtered_block_tree st.toFG := by
  intro B hB
  simp only [Proofs.Optimistic.voter_candidate_tree,
    Protocol.get_filtered_block_tree,
    Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq] at hB ⊢
  obtain ⟨⟨⟨hBprocessed, hFB⟩, W, hWprocessed, hBW, hheight⟩,
    hroot⟩ := hB
  have hBT : B ∈ st.T := by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
      at hBprocessed
    exact hBprocessed.1
  have hWT : W ∈ st.T := by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
      at hWprocessed
    exact hWprocessed.1
  exact ⟨⟨⟨hBT, hFB⟩, W, hWT, hBW, hheight⟩, hroot⟩



/-- Two run blocks with the same erasure are the same named block. -/
private theorem frozenSuffix_runBlock_unique
    {S : Setup V} {rho : Run V} (adm : AdmissibleCore S rho)
    {A B : NamedBlock V} (hA : RunBlock S rho A) (hB : RunBlock S rho B)
    (herase : A.erase = B.erase) : A = B :=
  adm.toNamedRootCollisionFree.root_injective
    A B hA hB A B (Or.inl (Proofs.NamedAncestry.named_self A))
      (Or.inr (Proofs.NamedAncestry.named_self B))
      (by rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root B, herase])

/-- Named replacement for the cross-store use of `DerivedStateAgrees`: a block
held at two honest prefix states has the same chain state at both. -/
private theorem frozenSuffix_sigma_eq
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {p w : V} (hp : p ∈ rho.honest) (hw : w ∈ rho.honest) (tp tw : Time)
    {C : Block V}
    (hCp : C ∈ (rho.storeBeforeTime S p tp).core.T)
    (hCw : C ∈ (rho.storeBeforeTime S w tw).core.T) :
    (rho.storeBeforeTime S p tp).core.σ C =
      (rho.storeBeforeTime S w tw).core.σ C := by
  have hsch := adm.toNamedScheduleWellFormed
  obtain ⟨np, hnp, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S hsch tp
  obtain ⟨nw, hnw, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S hsch tw
  obtain ⟨Dp, hDpmem, hDpe⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho tp p hCp
  obtain ⟨Dw, hDwmem, hDwe⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho tw w hCw
  have hRp : RunBlock S rho Dp :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hp (by simpa only [hnp] using hDpmem)
  have hRw : RunBlock S rho Dw :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hw (by simpa only [hnw] using hDwmem)
  have heq : Dp = Dw :=
    frozenSuffix_runBlock_unique adm hRp hRw (hDpe.trans hDwe.symm)
  calc (rho.storeBeforeTime S p tp).core.σ C
      = Protocol.derive_named S.E S.cfg Dp := by
        rw [← hDpe]
        exact Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho tp p Dp hDpmem
    _ = Protocol.derive_named S.E S.cfg Dw := by rw [heq]
    _ = (rho.storeBeforeTime S w tw).core.σ C := by
        rw [← hDwe]
        exact (Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho tw w Dw
          hDwmem).symm

/-- The proposal duty store of an honest proposer and the vote duty store of an
honest voter agree on the chain state of any block both hold. -/
private theorem frozenSuffix_sigma_source_target
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} (hprop : S.E.proposer s ∈ rho.honest)
    {v : V} (hv : v ∈ rho.honest) {C : Block V}
    (hCsource : C ∈ (Protocol.proposerDutyStore S rho s).T)
    (hCtarget : C ∈ (Proofs.Optimistic.voteDutyStore S rho v s).T) :
    (Protocol.proposerDutyStore S rho s).σ C =
      (Proofs.Optimistic.voteDutyStore S rho v s).σ C :=
  frozenSuffix_sigma_eq S adm hprop hv (Protocol.proposal_time S.E s)
    (Protocol.vote_time S.E s) hCsource hCtarget

/-- The proposal parent is a source-walk candidate at the exact proposal read.
Named twin of `proposedParent_mem_proposalWalkSourceTree`; the fact is already
live as `selectedOpeningProposedParent_mem_filtered`, and
`namedWalkSourceTree` is that tree. -/
private theorem proposedParent_mem_namedWalkSourceTree
    (S : Setup V) (rho : Run V) (s : Slot) :
    proposedParent S rho s ∈ namedWalkSourceTree S rho s :=
  selectedOpeningProposedParent_mem_filtered (rho := rho) S s

/-- A target full-tree candidate below the frozen proposal, with all root and
finality guards, is in the frozen voter tree. -/
private theorem voterCandidate_on_proposalSegment
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} {v : V} {D : Block V} {P : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P)
    (hproposal : P.erase ∈ voterCandidateTreeAt S rho v s)
    (hDP : Block.Preceq D P.erase)
    (hFD : Block.Preceq (Proofs.Optimistic.voteDutyStore S rho v s).F D)
    (hrootD : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.toFG) D) :
    D ∈ voterCandidateTreeAt S rho v s := by
  let target := Proofs.Optimistic.voteDutyStore S rho v s
  have htree : voterCandidateTreeAt S rho v s =
      Proofs.Optimistic.voter_candidate_tree S.E target.toHealing := rfl
  rw [htree] at hproposal ⊢
  have hdata := hproposal
  simp only [Proofs.Optimistic.voter_candidate_tree,
    Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq] at hdata ⊢
  obtain ⟨⟨⟨hPprocessed, _hFP⟩, W, hWprocessed, hPW, hheight⟩,
    _hrootP⟩ := hdata
  have hPT : P.erase ∈ target.T := by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
      at hPprocessed
    exact hPprocessed.1
  have hpc : ParentClosed target :=
    Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
      (Protocol.vote_time S.E s) v
  have hDT : D ∈ target.T :=
    Proofs.Records.mem_of_preceq ((parentClosed_iff target).mp hpc).2
      D P.erase hPT hDP
  have hslot : P.erase.slot = target.toHealing.s := by
    rw [Proofs.NamedWire.erase_slot, proposedBlockAt_slot S rho s hP]
    simpa only [target, Proofs.Optimistic.toHealing_slot] using
      (Proofs.Optimistic.voteDutyStore_slot S rho v s).symm
  have hDprocessed : D ∈ Protocol.voter_processed_block_tree S.E
      target.toHealing.toFG.toSG.toGoldfishStore target.toHealing.s := by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    refine ⟨hDT, Or.inr ?_⟩
    exact ⟨P.erase, ⟨hPT, hslot⟩, hDP⟩
  exact ⟨⟨⟨hDprocessed, hFD⟩, W, hWprocessed,
      Block.preceq_trans hDP hPW, hheight⟩, hrootD⟩

/-- Named bodies are closed under named ancestry (local twin of the private
`FrontierWitnessRelayRun.named_ancestor_body_mem`). -/
private theorem frozenSuffix_ancestor_body_mem
    {st : Protocol.NamedStore V} (hpc : NamedStore.NamedParentClosed st)
    {A B : NamedBlock V} (hB : B ∈ st.bodies)
    (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
      exact hAB ▸ hB
  | node parent slot root votes support rows proposer ih =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hparent
      · exact hB
      · exact ih (hpc.2 _ hB) hparent

/-- Named replacement for `Protocol.derived_h_mono` composed with the retired
`DerivedStateAgrees`: one honest prefix store's chain-state height is monotone
along its own tree. -/
private theorem frozenSuffix_sigma_height_mono
    (S : Setup V) (rho : Run V) (w : V) (t : Time)
    {A B : Block V}
    (hA : A ∈ (rho.storeBeforeTime S w t).core.T)
    (hB : B ∈ (rho.storeBeforeTime S w t).core.T)
    (hAB : Block.Preceq A B) :
    ((rho.storeBeforeTime S w t).core.σ A).h ≤
      ((rho.storeBeforeTime S w t).core.σ B).h := by
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg (rho.storeBeforeTime S w t) :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t w).1.1.1
  obtain ⟨An, hAn, hAerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho t w hA
  obtain ⟨Bn, hBn, hBerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho t w hB
  have hABn : Block.Preceq An.erase Bn.erase := by
    rw [hAerase, hBerase]; exact hAB
  obtain ⟨An', hAn'B, hAn'e⟩ := Proofs.NamedAncestry.erased_ancestor_lift Bn hABn
  have hAn'mem : An' ∈ (rho.storeBeforeTime S w t).bodies :=
    frozenSuffix_ancestor_body_mem hcoh.2.2.1 hBn hAn'B
  have hEq : An' = An := hcoh.2.1 An' hAn'mem An hAn hAn'e
  calc ((rho.storeBeforeTime S w t).core.σ A).h
      = (Protocol.derive_named S.E S.cfg An).h := by
        rw [← hAerase]
        exact congrArg (fun x => x.h)
          (Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho t w An hAn)
    _ = (Protocol.derive_named S.E S.cfg An').h := by rw [hEq]
    _ ≤ (Protocol.derive_named S.E S.cfg Bn).h :=
        Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hAn'B
    _ = ((rho.storeBeforeTime S w t).core.σ B).h := by
        rw [← hBerase]
        exact (congrArg (fun x => x.h)
          (Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho t w Bn hBn)).symm

/-- The prepared read's contract anchor is active whenever its FG root is
(local twin of the private `VoteDutyHeadBandRun` frame lemma, restated on
`nodeAnchor` so that no import has to be added here). -/
private theorem frozenSuffix_nodeAnchor_mem_filtered
    (S : Setup V) (n : NamedNodeState V) (r : Round)
    (hroot : Protocol.get_fg_root n.st.core.toHealing.toFG ∈
      Protocol.get_filtered_block_tree n.st.core.toHealing.toFG) :
    Internal.PhaseGrades.nodeAnchor S n r ∈
      Protocol.get_filtered_block_tree n.st.core.toHealing.toFG := by
  change DecoupledConsensusModel.Protocol.anchor S.E S.hc n.st.core.toHealing r
    (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g1 ∈
      Protocol.get_filtered_block_tree n.st.core.toHealing.toFG
  cases hframe :
      (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g1 with
  | none => exact hroot
  | some opt =>
      cases opt with
      | none => exact hroot
      | some root =>
          cases hactive : DecoupledConsensusModel.Protocol.activePrefix
              (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG)
              root with
          | none =>
              simpa only [DecoupledConsensusModel.Protocol.anchor, hactive,
                Option.getD_none] using hroot
          | some B =>
              simpa only [DecoupledConsensusModel.Protocol.anchor, hactive,
                Option.getD_some] using
                NamedProposalParent.activePrefix_mem _ root B hactive


/-- The proposer's FG root precedes its own prepared contract anchor. -/
private theorem frozenSuffix_fgRoot_preceq_proposerAnchor
    (S : Setup V) (rho : Run V) (s : Slot) :
    Block.Preceq
      (Protocol.get_fg_root
        (Protocol.proposerDutyStore S rho s).toHealing.toFG)
      (Internal.PhaseGrades.nodeAnchor S (proposerReadAt S rho s)
        (S.hc.round_of (proposerReadAt S rho s).st.core.s)) := by
  have hroot : Protocol.get_fg_root
      (proposerReadAt S rho s).st.core.toHealing.toFG ∈
      Protocol.get_filtered_block_tree
        (proposerReadAt S rho s).st.core.toHealing.toFG := by
    simpa only [proposerReadAt, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using
      named_fgRoot_mem_filtered_stateBeforeTime S rho
        (Protocol.proposal_time S.E s) (S.E.proposer s)
  exact Proofs.Records.preceq_get_fg_root_of_mem_filtered
    (frozenSuffix_nodeAnchor_mem_filtered S (proposerReadAt S rho s)
      (S.hc.round_of (proposerReadAt S rho s).st.core.s) hroot)

/-- Every prefix of a source-walk candidate that is above the proposer's FG
root is itself a source-walk candidate. Root-order twin of
`Protocol.proposalPath_of_candidate`, which is stated over the absolute
`healAnchor`: the graded proposer anchor is a different block, so the ordering
premise is taken at the FG root, which both anchors sit above. -/
private theorem frozenSuffix_path_of_candidate
    (S : Setup V) (rho : Run V) {s : Slot} {B C : Block V}
    (hB : B ∈ namedWalkSourceTree S rho s)
    (hrootC : Block.Preceq
      (Protocol.get_fg_root
        (Protocol.proposerDutyStore S rho s).toHealing.toFG) C)
    (hCB : Block.Preceq C B) :
    C ∈ namedWalkSourceTree S rho s := by
  have hpc : ParentClosed (Protocol.proposerDutyStore S rho s) :=
    Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
      (Protocol.proposal_time S.E s) (S.E.proposer s)
  have hFJ : Block.Preceq (Protocol.proposerDutyStore S rho s).F
      (Protocol.proposerDutyStore S rho s).J :=
    Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
      (Protocol.proposal_time S.E s) (S.E.proposer s)
  have hBT : B ∈ (Protocol.proposerDutyStore S rho s).T :=
    Proofs.Records.get_filtered_block_tree_subset
      (Protocol.proposerDutyStore S rho s).toHealing.toFG hB
  have hCT : C ∈ (Protocol.proposerDutyStore S rho s).T :=
    Proofs.Records.mem_of_preceq
      ((parentClosed_iff (Protocol.proposerDutyStore S rho s)).mp hpc).2
      C B hBT hCB
  exact Proofs.Records.mem_filtered_of_preceq
    (st := (Protocol.proposerDutyStore S rho s).toHealing.toFG) hFJ hB hCT
      hCB hrootC

/-- A target full-tree candidate below the frozen proposal supplies all root and
finality guards needed to restrict that segment to the frozen voter tree. -/
private theorem voterCandidate_above_fullPivot
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} {v : V} {A D : Block V} {P : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P)
    (hproposal : P.erase ∈ voterCandidateTreeAt S rho v s)
    (hA : A ∈ Protocol.get_filtered_block_tree
      (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.toFG)
    (hAD : Block.Preceq A D)
    (hDP : Block.Preceq D P.erase) :
    D ∈ voterCandidateTreeAt S rho v s := by
  let target := Proofs.Optimistic.voteDutyStore S rho v s
  have hFJ : Block.Preceq target.F target.J :=
    Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
      (Protocol.vote_time S.E s) v
  have hrootA : Block.Preceq
      (Protocol.get_fg_root target.toHealing.toFG) A :=
    Proofs.Records.preceq_get_fg_root_of_mem_filtered hA
  have hFA : Block.Preceq target.F A :=
    Block.preceq_trans
      (Proofs.Records.preceq_get_fg_root_of_F (st := target.toHealing.toFG) hFJ)
      hrootA
  exact voterCandidate_on_proposalSegment S adm hP hproposal hDP
    (Block.preceq_trans hFA hAD) (Block.preceq_trans hrootA hAD)

/-- A frozen processed block outside the exact current proposal chain must be
in the pre-freeze arm of `voter_processed_block_tree`. -/
private theorem stampedBefore_of_voterProcessed_not_proposalAncestor
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} (hs : 0 < s)
    (hprop : S.E.proposer s ∈ rho.honest)
    {v : V} {Z : Block V} {P : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P)
    (hproposal : P.erase ∈ voterCandidateTreeAt S rho v s)
    (hZprocessed : Z ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.s)
    (hnot : ¬ Block.Preceq Z P.erase) :
    stampedBefore
      (Proofs.Optimistic.voteDutyStore S rho v s).timestamp_block
      (Protocol.view_freeze S.E (s - 1)) Z = true := by
  let target := Proofs.Optimistic.voteDutyStore S rho v s
  have hdata := hZprocessed
  simp only [Protocol.voter_processed_block_tree, Finset.mem_filter] at hdata
  rcases hdata.2 with hstamp | hcurrent
  · simpa only [target, Proofs.Optimistic.toHealing_slot,
      Proofs.Optimistic.voteDutyStore_slot] using hstamp
  · obtain ⟨Q, hQ, hZQ⟩ := hcurrent
    have hproposalFull : P.erase ∈
        Protocol.get_filtered_block_tree target.toHealing.toFG :=
      frozenVoterCandidateTree_subset_filtered S.E target.toHealing hproposal
    have hproposalT : P.erase ∈ target.T :=
      Proofs.Records.get_filtered_block_tree_subset target.toHealing.toFG hproposalFull
    obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedScheduleWellFormed
      (Protocol.vote_time S.E s)
    have hQprefix : Q ∈ (rho.stateBefore S n v).st.core.T := by
      simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn] using hQ.1
    have hproposalPrefix : P.erase ∈ (rho.stateBefore S n v).st.core.T := by
      simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn] using hproposalT
    have hPslot : P.erase.slot = s := by
      rw [Proofs.NamedWire.erase_slot]; exact proposedBlockAt_slot S rho s hP
    have hQeq : Q = P.erase :=
      unique_slot_block_in_store_core S adm hs hprop hQprefix hproposalPrefix
        (by simpa only [target, Proofs.Optimistic.toHealing_slot,
          Proofs.Optimistic.voteDutyStore_slot] using hQ.2) hPslot
    exact False.elim (hnot (by simpa only [hQeq] using hZQ))

/-- A block above the proposer's FG root closes the honest proposer's
finalized-delivery guard at every prefix before the proposal read. -/
private theorem sourceAnchor_finalizedBelowAtDeliveries
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} {Z : NamedBlock V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Protocol.proposerDutyStore S rho s).toHealing.toFG) Z.erase) :
    Protocol.BlockFinalizedBelowAtDeliveriesBefore S rho (S.E.proposer s) Z
      (Protocol.proposal_time S.E s) := by
  have hsch := adm.toNamedScheduleWellFormed
  have hFJ : Block.Preceq (Protocol.proposerDutyStore S rho s).F
      (Protocol.proposerDutyStore S rho s).J :=
    Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
      (Protocol.proposal_time S.E s) (S.E.proposer s)
  have hFZ : Block.Preceq (Protocol.proposerDutyStore S rho s).F Z.erase :=
    Block.preceq_trans (StoreFinality.finalized_preceq_fgRoot hFJ) hroot
  let N := (rho.events.filter (fun e => decide
    (e.time < Protocol.proposal_time S.E s))).length
  have hstore : rho.storeBeforeTime S (S.E.proposer s)
      (Protocol.proposal_time S.E s) =
      (rho.stateBefore S N (S.E.proposer s)).st :=
    congrArg NamedNodeState.st
      (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S hsch
        (Protocol.proposal_time S.E s)) (S.E.proposer s))
  have hFZN : Block.Preceq
      (rho.stateBefore S N (S.E.proposer s)).st.core.F Z.erase := by
    simpa only [Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
      hstore] using hFZ
  intro i hi
  have hiN : i ≤ N := hi
  exact Block.preceq_trans
    (Protocol.stateBefore_F_mono S rho (S.E.proposer s)
      hiN) hFZN

/-- A pre-freeze frozen block above the proposer's FG root is present in the
exact honest proposer snapshot. -/
private theorem stampedVoterBlock_mem_proposerDuty_afterGST
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E (s - 1))
    (hprop : S.E.proposer s ∈ rho.honest)
    {v : V} (hv : v ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E s ≤ rho.horizon)
    {Z : NamedBlock V}
    (hZbody : Z ∈ (rho.storeBeforeTime S v (Protocol.vote_time S.E s)).bodies)
    (hstamp : stampedBefore
      (Proofs.Optimistic.voteDutyStore S rho v s).timestamp_block
      (Protocol.view_freeze S.E (s - 1)) Z.erase = true)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Protocol.proposerDutyStore S rho s).toHealing.toFG) Z.erase) :
    Z.erase ∈ (Protocol.proposerDutyStore S rho s).T := by
  have hsch := adm.toNamedScheduleWellFormed
  by_cases hgen : Z = NamedBlock.genesis
  · subst hgen
    have hvisible := Protocol.genesis_mem_and_stamp_storeBeforeTime S
      hsch (S.E.proposer s) (Protocol.proposal_time S.E s)
        (Protocol.proposal_time S.E s)
    simpa only [Protocol.proposerDutyStore, Proofs.Optimistic.tickStore] using
      hvisible.1
  · obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S hsch
      (Protocol.vote_time S.E s)
    have hZn : Z ∈ (rho.stateBefore S n v).st.bodies := by
      simpa only [Run.storeBeforeTime, hn] using hZbody
    have hstampn : stampedBefore
        (rho.stateBefore S n v).st.core.timestamp_block
        (Protocol.view_freeze S.E (s - 1)) Z.erase = true := by
      simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn] using hstamp
    have hprocessed : Object.processed (rho.stateBefore S n v).st
        (NamedObject.block Z) = true := by
      simpa only [Object.processed, NamedReceipt.processed,
        decide_eq_true_eq] using hZn
    rcases Protocol.acceptsAt_block_of_processed S rho v n Z hprocessed with
      hgen' | ⟨i, hi, t, hacc⟩
    · exact False.elim (hgen hgen')
    · have ht : t < Protocol.view_freeze S.E (s - 1) :=
        Protocol.HonestWeightMajority.acceptsAt_block_lt_of_stamp_before_core
          S adm hv hacc (Nat.succ_le_of_lt hi)
            (Protocol.publicTime_view_freeze S (s - 1)) hstampn
      have hpostFreeze : S.E.t_GST ≤ Protocol.view_freeze S.E (s - 1) := by
        apply hpost.trans
        calc
          Protocol.proposal_time S.E (s - 1) ≤
              Protocol.proposal_time S.E (s - 1) + 3 * S.E.Δ :=
            Int.le_add_of_nonneg_right
              (Int.mul_nonneg (by norm_num) (le_of_lt S.E.Δ_pos))
          _ = Protocol.view_freeze S.E (s - 1) := by
            unfold Protocol.proposal_time Protocol.view_freeze
            ring
      have hpred : s - 1 + 1 = s := Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hs))
      have hhop : Protocol.view_freeze S.E (s - 1) + S.E.Δ =
          Protocol.proposal_time S.E s := by
        rw [← hpred]
        exact Protocol.view_freeze_add_delta_eq_proposal_time_succ S.E (s - 1)
      have hZpos : 0 < Z.slot := by
        rw [← Proofs.NamedWire.erase_slot]
        exact Nat.zero_lt_of_lt
          (Protocol.parent_slot_lt_of_acceptsAt_block S hacc)
      have hadmit : Protocol.AdmittedBefore S rho (S.E.proposer s) Z.erase
          (Protocol.proposal_time S.E s) :=
        Protocol.block_admittedBefore_of_accepted_after_cutoff_core
          S adm hv hprop hZpos hacc ht hpostFreeze hhop hhor
            (sourceAnchor_finalizedBelowAtDeliveries S adm hroot)
      have hvisible := Protocol.admittedBefore_mem_and_stamp_at S
        hsch hadmit (le_refl _)
      simpa only [Protocol.proposerDutyStore, Proofs.Optimistic.tickStore] using
        hvisible.1

/-- The erased proposal's parent pointer is the selected parent. -/
private theorem proposedBlockErased_parent_optional
    (S : Setup V) (rho : Run V) (s : Slot) {P : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P) :
    P.erase.parent? = some (proposedParent S rho s) := by
  obtain ⟨p, hp, hpe⟩ := proposedBlockAt_parent S rho s hP
  rw [Proofs.NamedWire.erase_parent_optional, hp, Option.map_some, hpe]

/-- The selected parent precedes the bound named proposal. -/
private theorem proposedParent_preceq_proposedBlockAt
    (S : Setup V) (rho : Run V) (s : Slot) {P : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P) :
    Block.Preceq (proposedParent S rho s) P.erase :=
  Protocol.preceq_of_parent? (proposedBlockErased_parent_optional S rho s hP)

/-- Current frozen semantics produce source candidate membership for every
eligible target child above the fixed pivot, independently of its score arm. -/
private theorem targetChild_mem_sourceTree_of_frozenProposal
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E (s - 1))
    (hprop : S.E.proposer s ∈ rho.honest)
    {v : V} (hv : v ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E s ≤ rho.horizon)
    {pivot X C : Block V} {P : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P)
    (hsourceRoot : Block.Preceq
      (Protocol.get_fg_root
        (Protocol.proposerDutyStore S rho s).toHealing.toFG) pivot)
    (hproposal : P.erase ∈ voterCandidateTreeAt S rho v s)
    (hviability :
      (Protocol.proposerDutyStore S rho s).h_max - 1 ≤
          (Proofs.Optimistic.voteDutyStore S rho v s).h_max - 1 ∨
        (Protocol.proposerDutyStore S rho s).h_max - 1 ≤
          ((Protocol.proposerDutyStore S rho s).σ pivot).h)
    (hpivotX : Block.Preceq pivot X)
    (hCtarget : C ∈ namedWalkTargetTree S rho s v P)
    (hparent : C.parent? = some X) :
    C ∈ namedWalkSourceTree S rho s := by
  let source := Protocol.proposerDutyStore S rho s
  let target := Proofs.Optimistic.voteDutyStore S rho v s
  have htargetErase : C ∈
      (Proofs.Optimistic.voter_candidate_tree S.E target.toHealing).erase P.erase :=
    hCtarget
  have hCne : C ≠ P.erase := (Finset.mem_erase.mp htargetErase).1
  have hCfrozen : C ∈ Proofs.Optimistic.voter_candidate_tree S.E target.toHealing :=
    (Finset.mem_erase.mp htargetErase).2
  have hXC : Block.Preceq X C := Protocol.preceq_of_parent? hparent
  have hrootC : Block.Preceq
      (Protocol.get_fg_root source.toHealing.toFG) C :=
    Block.preceq_trans hsourceRoot (Block.preceq_trans hpivotX hXC)
  by_cases hCP : Block.Preceq C P.erase
  · have hCH : Block.Preceq C (proposedParent S rho s) :=
      Proofs.Optimistic.preceq_parent_of_ne
        (proposedBlockErased_parent_optional S rho s hP) hCP hCne
    have hHcandidate := proposedParent_mem_namedWalkSourceTree S rho s
    exact frozenSuffix_path_of_candidate S rho hHcandidate hrootC hCH
  · have hdata := hCfrozen
    simp only [Proofs.Optimistic.voter_candidate_tree,
      Protocol.get_filtered_block_tree_from,
      Protocol.viable_tree, Protocol.finalized_descendants,
      Protocol.viable, Finset.mem_filter, decide_eq_true_eq] at hdata
    obtain ⟨⟨⟨hCprocessed, _hFC⟩, W, hWprocessed, hCW, hheightTarget⟩,
      _hrootC⟩ := hdata
    have hWT : W ∈ target.T := by
      simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
        at hWprocessed
      exact hWprocessed.1
    have hCT : C ∈ target.T := by
      simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
        at hCprocessed
      exact hCprocessed.1
    have hWnot : ¬ Block.Preceq W P.erase := by
      intro hWP
      exact hCP (Block.preceq_trans hCW hWP)
    have hCstamp := stampedBefore_of_voterProcessed_not_proposalAncestor
      S adm hs hprop hP hproposal hCprocessed hCP
    have hWstamp := stampedBefore_of_voterProcessed_not_proposalAncestor
      S adm hs hprop hP hproposal hWprocessed hWnot
    obtain ⟨Cn, hCnbody, hCnerase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
        (Protocol.vote_time S.E s) v hCT
    obtain ⟨Wn, hWnbody, hWnerase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
        (Protocol.vote_time S.E s) v hWT
    have hrootW : Block.Preceq
        (Protocol.get_fg_root source.toHealing.toFG) W :=
      Block.preceq_trans hrootC hCW
    have hCTsource : C ∈ source.T := by
      have hmem := stampedVoterBlock_mem_proposerDuty_afterGST
        S adm hs hpost hprop hv hhor hCnbody
          (by rw [hCnerase]; exact hCstamp)
          (by rw [hCnerase]; exact hrootC)
      rwa [hCnerase] at hmem
    have hWTsource : W ∈ source.T := by
      have hmem := stampedVoterBlock_mem_proposerDuty_afterGST
        S adm hs hpost hprop hv hhor hWnbody
          (by rw [hWnerase]; exact hWstamp)
          (by rw [hWnerase]; exact hrootW)
      rwa [hWnerase] at hmem
    have hFJ : Block.Preceq source.F source.J :=
      Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
        (Protocol.proposal_time S.E s) (S.E.proposer s)
    have hFC : Block.Preceq source.F C :=
      Block.preceq_trans
        (Proofs.Records.preceq_get_fg_root_of_F (st := source.toHealing.toFG) hFJ)
        hrootC
    change C ∈ Protocol.get_filtered_block_tree source.toHealing.toFG
    simp only [Protocol.get_filtered_block_tree,
      Protocol.get_filtered_block_tree_from,
      Protocol.viable_tree, Protocol.finalized_descendants,
      Protocol.viable, Finset.mem_filter, decide_eq_true_eq]
    rcases hviability with hthreshold | hpivotFloor
    · have hheight : source.h_max - 1 ≤ (source.σ W).h := by
        calc
          source.h_max - 1 ≤ target.h_max - 1 := hthreshold
          _ ≤ (target.σ W).h := hheightTarget
          _ = (source.σ W).h := by
            rw [frozenSuffix_sigma_source_target S adm hprop hv hWTsource hWT]
      exact ⟨⟨⟨hCTsource, hFC⟩, W, hWTsource, hCW, hheight⟩, hrootC⟩
    · have hpivotC : Block.Preceq pivot C :=
        Block.preceq_trans hpivotX hXC
      have hpcSource : ParentClosed source :=
        Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
          (Protocol.proposal_time S.E s) (S.E.proposer s)
      have hpivotSource : pivot ∈ source.T :=
        Proofs.Records.mem_of_preceq ((parentClosed_iff source).mp hpcSource).2
          pivot C hCTsource hpivotC
      have hheight : source.h_max - 1 ≤ (source.σ C).h := by
        calc
          source.h_max - 1 ≤ (source.σ pivot).h := hpivotFloor
          _ ≤ (source.σ C).h :=
            frozenSuffix_sigma_height_mono S rho (S.E.proposer s)
              (Protocol.proposal_time S.E s) hpivotSource hCTsource hpivotC
      exact ⟨⟨⟨hCTsource, hFC⟩, C, hCTsource,
        Block.preceq_self C, hheight⟩, hrootC⟩




/-- Candidate and anchor inputs shared by fixed and moving-frontier suffix
comparisons, in the prepared-read shapes. The five fields are exactly the
first five of `NamedSGOpeningFrozenVoteAt`: the proposer's graded contract
anchor, the voter's filtered tree, the voter's frozen candidate tree, and the
two compatibility facts at the voter's prepared contract anchor `voterAnchorAt`
(design note; never the absolute `healAnchor`). -/
structure NamedFrozenProposalSuffixCoreInputs
    (S : Setup V) (rho : Run V) (s : Slot)
    (pivot : Block V) (v : V) (P : NamedBlock V) : Prop where
  sourceAnchor : Block.Preceq
    (Internal.PhaseGrades.nodeAnchor S (proposerReadAt S rho s)
      (S.hc.round_of (proposerReadAt S rho s).st.core.s)) pivot
  pivotTarget : pivot ∈ Protocol.get_filtered_block_tree
    (Internal.NamedRecoveryRead.voteDutyRead S rho v s).st.core.toHealing.toFG
  proposalCandidate : P.erase ∈ voterCandidateTreeAt S rho v s
  pivotAnchorCompatible : Block.compatible (voterAnchorAt S rho v s) pivot = true
  proposalAnchorCompatible :
    Block.compatible (voterAnchorAt S rho v s) P.erase = true

/-- Exact local inputs for the frozen suffix comparison under a no-rise
window: the five core fields plus the common frontier. -/
structure NamedFrozenProposalSuffixInputs
    (S : Setup V) (rho : Run V) (s : Slot)
    (pivot : Block V) (v : V) (P : NamedBlock V) : Prop
    extends NamedFrozenProposalSuffixCoreInputs S rho s pivot v P where
  sameHMax : (proposerReadAt S rho s).st.core.h_max =
    (Internal.NamedRecoveryRead.voteDutyRead S rho v s).st.core.h_max

/-- Frozen proposal inputs for a moving frontier. The pivot is inside the
viability band of both prepared reads. These two concrete height facts replace
the fixed-window frontier equality; each is read at the store that uses it,
because `derive_named` and `derived_state` differ on the timeout arm. -/
structure NamedFrozenProposalSuffixBandInputs
    (S : Setup V) (rho : Run V) (s : Slot)
    (pivot : Block V) (v : V) (P : NamedBlock V) : Prop
    extends NamedFrozenProposalSuffixCoreInputs S rho s pivot v P where
  sourceBand : (proposerReadAt S rho s).st.core.h_max - 1 ≤
    ((proposerReadAt S rho s).st.core.σ pivot).h
  targetBand :
    (Internal.NamedRecoveryRead.voteDutyRead S rho v s).st.core.h_max - 1 ≤
      ((Internal.NamedRecoveryRead.voteDutyRead S rho v s).st.core.σ pivot).h

/-- PRE-BUILDING pin: the named twin of
`candidateScorePreservingViewExtension_proposedBlock_afterGST_of_candidates`
(earlier `Availability/ProposalSnapshotBridgeRun`, live in the selection tree only in
the compatibility `WeakProposalResolvedSnapshotRun` vocabulary, which still reads the
retired total `proposedBlock`). It is the one fact the frozen suffix transfer
still takes as a hypothesis: for a candidate held by both the honest proposer
and the honest voter, the proposal's carried raw and support votes score that
candidate exactly as the voter's own merged view does. -/
def NamedProposalCandidateScoreBridge
    (S : Setup V) (rho : Run V) (s : Slot) (v : V) (P : NamedBlock V) : Prop :=
  ∀ C : Block V,
    C ∈ namedWalkSourceTree S rho s →
    C ∈ Protocol.get_filtered_block_tree
      (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.toFG →
    Protocol.CandidateScorePreservingViewExtension
      (Protocol.proposerDutyStore S rho s).T
      (Proofs.Optimistic.voteDutyStore S rho v s).T
      P.erase.gf_votes.toFinset
      P.erase.gf_support_votes.toFinset
      (Protocol.voter_view S.E
        (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.toFG.toSG.toGoldfishStore s)
      (Protocol.voter_support_view S.E
        (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.toFG.toSG.toGoldfishStore s) C

/-- Common proof of the frozen suffix transfer. The frontier relation is
either exact equality or two concrete pivot-band bounds. -/
private theorem namedProposalPivotSuffixTransfer_of_core_of_scoreBridge
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E (s - 1))
    (hprop : S.E.proposer s ∈ rho.honest)
    {v : V} (hv : v ∈ rho.honest)
    (hvoteHor : Protocol.vote_time S.E s ≤ rho.horizon)
    {pivot : Block V} {P : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P)
    (h : NamedFrozenProposalSuffixCoreInputs S rho s pivot v P)
    (hbridge : NamedProposalCandidateScoreBridge S rho s v P)
    (hfrontier :
      (Protocol.proposerDutyStore S rho s).h_max =
          (Proofs.Optimistic.voteDutyStore S rho v s).h_max ∨
        ((Protocol.proposerDutyStore S rho s).h_max - 1 ≤
            ((Protocol.proposerDutyStore S rho s).σ pivot).h ∧
          (Proofs.Optimistic.voteDutyStore S rho v s).h_max - 1 ≤
            ((Proofs.Optimistic.voteDutyStore S rho v s).σ pivot).h)) :
    NamedProposalPivotSuffixTransfer S rho s pivot v P := by
  let source := Protocol.proposerDutyStore S rho s
  let target := Proofs.Optimistic.voteDutyStore S rho v s
  have hproposalFull : P.erase ∈
      Protocol.get_filtered_block_tree target.toHealing.toFG :=
    frozenVoterCandidateTree_subset_filtered S.E target.toHealing
      h.proposalCandidate
  have hproposalT : P.erase ∈ target.T :=
    Proofs.Records.get_filtered_block_tree_subset target.toHealing.toFG hproposalFull
  have hproposalHor : Protocol.proposal_time S.E s ≤ rho.horizon :=
    le_trans (le_of_lt (Protocol.proposal_time_lt_vote_time S.E s))
      hvoteHor
  have hsourcePc : ParentClosed source :=
    Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
      (Protocol.proposal_time S.E s) (S.E.proposer s)
  have htargetPc : ParentClosed target :=
    Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
      (Protocol.vote_time S.E s) v
  have hsourceSlot : source.s = s := by
    simp only [source, Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
      Proofs.Optimistic.slotOf_proposal_time]
  have htargetSlot : target.s = s := by
    simp only [target, Proofs.Optimistic.voteDutyStore_slot]
  have hraw : P.erase.gf_votes.toFinset =
      (Protocol.proposer_view source.toHealing.toFG.toSG.toGoldfishStore source.s).toFinset := by
    rw [Proofs.NamedWire.erase_goldfish_votes,
      Protocol.proposedBlock_gf_votes S rho s hP]
    rfl
  have hsupport : P.erase.gf_support_votes.toFinset =
      (Protocol.proposer_support_view source.toHealing.toFG.toSG.toGoldfishStore
        source.s).toFinset := by
    rw [Proofs.NamedWire.erase_goldfish_support,
      Protocol.proposedBlock_gf_support_votes S rho s hP]
    rfl
  refine { persist := ?_, reflect := ?_ }
  · intro X C hpivotX _hXparent _hXne hstep hCparent
    have hchild := Protocol.ghost_step_child hstep
    have hparent : C.parent? = some X := hchild.2.1
    have hXC : Block.Preceq X C := Protocol.preceq_of_parent? hparent
    have hCP : Block.Preceq C P.erase :=
      Block.preceq_trans hCparent
        (proposedParent_preceq_proposedBlockAt S rho s hP)
    have hCtargetFrozen := voterCandidate_above_fullPivot S adm hP
      h.proposalCandidate h.pivotTarget (Block.preceq_trans hpivotX hXC) hCP
    have hCne : C ≠ P.erase := by
      intro heq
      have hproposalParent : Block.Preceq P.erase (proposedParent S rho s) := by
        simpa only [← heq] using hCparent
      have hparentProposal : Block.Preceq (proposedParent S rho s) P.erase :=
        proposedParent_preceq_proposedBlockAt S rho s hP
      have heq' := Block.preceq_antisymm hproposalParent hparentProposal
      have hpar := proposedBlockErased_parent_optional S rho s hP
      rw [heq'] at hpar
      have hdepth := Protocol.depth_of_parent? hpar
      omega
    have hCtarget : C ∈ namedWalkTargetTree S rho s v P :=
      Finset.mem_erase.mpr ⟨hCne, hCtargetFrozen⟩
    have hCsource : C ∈ namedWalkSourceTree S rho s := hchild.1
    have hCfullTarget : C ∈ Protocol.get_filtered_block_tree
        target.toHealing.toFG :=
      frozenVoterCandidateTree_subset_filtered S.E target.toHealing
        hCtargetFrozen
    have hsourceT : C ∈ source.T :=
      Proofs.Records.get_filtered_block_tree_subset source.toHealing.toFG hCsource
    have htargetT : C ∈ target.T :=
      Proofs.Records.get_filtered_block_tree_subset target.toHealing.toFG hCfullTarget
    have hsourceParentT : C.parent ∈ source.T :=
      Proofs.Records.mem_of_preceq ((parentClosed_iff source).mp hsourcePc).2
        C.parent C hsourceT (preceq_parent C)
    have htargetParentT : C.parent ∈ target.T :=
      Proofs.Records.mem_of_preceq ((parentClosed_iff target).mp htargetPc).2
        C.parent C htargetT (preceq_parent C)
    have hnotCurrent : C.slot ≠ source.s := by
      rw [hsourceSlot]
      exact Nat.ne_of_lt
        (Proofs.NamedSlotFreshness.block_slot_lt_of_mem_before_proposal
          S adm hs hsourceT)
    have heligibleSource : namedWalkSourceEligible S rho s C = true := hchild.2.2
    have hsourceElig : Protocol.goldfish_eligible S.E source.σ source.h_max
        source.T source.s
        (Protocol.proposer_view source.toHealing.toFG.toSG.toGoldfishStore source.s).toFinset
        (Protocol.proposer_support_view source.toHealing.toFG.toSG.toGoldfishStore
          source.s).toFinset (source.s - 1) C = true := heligibleSource
    have heligSource :=
      (Proofs.Optimistic.goldfish_eligible_iff S.E source.σ source.h_max
        source.T source.s
        (Protocol.proposer_view source.toHealing.toFG.toSG.toGoldfishStore source.s).toFinset
        (Protocol.proposer_support_view source.toHealing.toFG.toSG.toGoldfishStore
          source.s).toFinset (source.s - 1) C).mp hsourceElig
    refine ⟨hCtarget, ?_⟩
    have hgoal : namedWalkTargetEligible S rho s v C =
        Protocol.goldfish_eligible S.E target.σ target.h_max target.T
          target.s (Protocol.voter_view S.E target.toHealing.toFG.toSG.toGoldfishStore target.s)
          (Protocol.voter_support_view S.E target.toHealing.toFG.toSG.toGoldfishStore target.s)
          (target.s - 1) C := rfl
    rw [hgoal, Proofs.Optimistic.goldfish_eligible_iff]
    rcases heligSource with hlow | hmajority | hcurrent
    · rcases hfrontier with hmaxEq | hband
      · exact Or.inl (by
          calc
            (target.σ C.parent).h = (source.σ C.parent).h := by
              rw [frozenSuffix_sigma_source_target S adm hprop hv
                hsourceParentT htargetParentT]
            _ < source.h_max - 1 := hlow
            _ = target.h_max - 1 := by rw [hmaxEq])
      · have hpivotParent : Block.Preceq pivot C.parent := by
          rw [parent_eq_of_parent? hparent]
          exact hpivotX
        have hpivotSource : pivot ∈ source.T :=
          Proofs.Records.mem_of_preceq ((parentClosed_iff source).mp hsourcePc).2
            pivot C.parent hsourceParentT hpivotParent
        have hfloor : source.h_max - 1 ≤ (source.σ C.parent).h :=
          le_trans hband.1
            (frozenSuffix_sigma_height_mono S rho (S.E.proposer s)
              (Protocol.proposal_time S.E s) hpivotSource hsourceParentT
                hpivotParent)
        exact False.elim ((not_lt_of_ge hfloor) hlow)
    · right
      left
      have hext := hbridge C hCsource hCfullTarget
      have hcount := hext.voters_count_eq S.E (s - 1)
      have hscore := hext.goldfish_score_eq S.E (s - 1)
      rw [← hraw, ← hsupport] at hmajority
      rw [hsourceSlot] at hmajority
      rw [htargetSlot, ← hcount, ← hscore]
      exact hmajority
    · exact False.elim (hnotCurrent hcurrent)
  · intro X C hpivotX _hXparent hCtarget hparent heligible
    have hCsource := targetChild_mem_sourceTree_of_frozenProposal
      S adm hs hpost hprop hv hproposalHor hP
        (Block.preceq_trans (frozenSuffix_fgRoot_preceq_proposerAnchor S rho s)
          h.sourceAnchor)
        h.proposalCandidate (by
          rcases hfrontier with hmaxEq | hband
          · exact Or.inl (by rw [hmaxEq])
          · exact Or.inr hband.1)
          hpivotX hCtarget hparent
    have htargetErase : C ∈
        (Proofs.Optimistic.voter_candidate_tree S.E target.toHealing).erase P.erase :=
      hCtarget
    have hCne : C ≠ P.erase := (Finset.mem_erase.mp htargetErase).1
    have hCfrozen := (Finset.mem_erase.mp htargetErase).2
    have hCfullTarget : C ∈ Protocol.get_filtered_block_tree
        target.toHealing.toFG :=
      frozenVoterCandidateTree_subset_filtered S.E target.toHealing hCfrozen
    have hsourceFull : C ∈ Protocol.get_filtered_block_tree
        source.toHealing.toFG := hCsource
    have hsourceT : C ∈ source.T :=
      Proofs.Records.get_filtered_block_tree_subset source.toHealing.toFG hsourceFull
    have htargetT : C ∈ target.T :=
      Proofs.Records.get_filtered_block_tree_subset target.toHealing.toFG hCfullTarget
    have hsourceParentT : C.parent ∈ source.T :=
      Proofs.Records.mem_of_preceq ((parentClosed_iff source).mp hsourcePc).2
        C.parent C hsourceT (preceq_parent C)
    have htargetParentT : C.parent ∈ target.T :=
      Proofs.Records.mem_of_preceq ((parentClosed_iff target).mp htargetPc).2
        C.parent C htargetT (preceq_parent C)
    have hnotCurrent : C.slot ≠ target.s := by
      intro hcur
      obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
        adm.toNamedScheduleWellFormed
        (Protocol.vote_time S.E s)
      have hCprefix : C ∈ (rho.stateBefore S n v).st.core.T := by
        simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn] using htargetT
      have hPprefix : P.erase ∈ (rho.stateBefore S n v).st.core.T := by
        simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn] using hproposalT
      have hPslot : P.erase.slot = s := by
        rw [Proofs.NamedWire.erase_slot]
        exact proposedBlockAt_slot S rho s hP
      have hEq := unique_slot_block_in_store_core S adm hs hprop hCprefix hPprefix
        (by simpa only [htargetSlot] using hcur) hPslot
      exact hCne hEq
    have htargetElig : Protocol.goldfish_eligible S.E target.σ target.h_max
        target.T target.s
        (Protocol.voter_view S.E target.toHealing.toFG.toSG.toGoldfishStore target.s)
        (Protocol.voter_support_view S.E target.toHealing.toFG.toSG.toGoldfishStore target.s)
        (target.s - 1) C = true := heligible
    have heligTarget :=
      (Proofs.Optimistic.goldfish_eligible_iff S.E target.σ target.h_max target.T
        target.s (Protocol.voter_view S.E target.toHealing.toFG.toSG.toGoldfishStore target.s)
        (Protocol.voter_support_view S.E target.toHealing.toFG.toSG.toGoldfishStore target.s)
        (target.s - 1) C).mp htargetElig
    refine ⟨hCsource, ?_⟩
    have hgoal : namedWalkSourceEligible S rho s C =
        Protocol.goldfish_eligible S.E source.σ source.h_max source.T
          source.s
          (Protocol.proposer_view source.toHealing.toFG.toSG.toGoldfishStore source.s).toFinset
          (Protocol.proposer_support_view source.toHealing.toFG.toSG.toGoldfishStore
            source.s).toFinset (source.s - 1) C := rfl
    rw [hgoal, Proofs.Optimistic.goldfish_eligible_iff]
    rcases heligTarget with hlow | hmajority | hcurrent
    · rcases hfrontier with hmaxEq | hband
      · exact Or.inl (by
          calc
            (source.σ C.parent).h = (target.σ C.parent).h := by
              rw [frozenSuffix_sigma_source_target S adm hprop hv
                hsourceParentT htargetParentT]
            _ < target.h_max - 1 := hlow
            _ = source.h_max - 1 := by rw [hmaxEq])
      · have hpivotParent : Block.Preceq pivot C.parent := by
          rw [parent_eq_of_parent? hparent]
          exact hpivotX
        have hpivotTarget : pivot ∈ target.T :=
          Proofs.Records.mem_of_preceq ((parentClosed_iff target).mp htargetPc).2
            pivot C.parent htargetParentT hpivotParent
        have hfloor : target.h_max - 1 ≤ (target.σ C.parent).h :=
          le_trans hband.2
            (frozenSuffix_sigma_height_mono S rho v
              (Protocol.vote_time S.E s) hpivotTarget htargetParentT
                hpivotParent)
        exact False.elim ((not_lt_of_ge hfloor) hlow)
    · right
      left
      have hext := hbridge C hCsource hCfullTarget
      have hcount := hext.voters_count_eq S.E (s - 1)
      have hscore := hext.goldfish_score_eq S.E (s - 1)
      rw [htargetSlot] at hmajority
      rw [← hraw, ← hsupport, hsourceSlot, hcount, hscore]
      exact hmajority
    · exact False.elim (hnotCurrent hcurrent)



/-! ## The candidate score bridge

`NamedProposalCandidateScoreBridge` is discharged here, so the pivot transfer
carries no residual. This is the named twin of
`candidateScorePreservingViewExtension_proposedBlock_afterGST_of_candidates`
(`WeakProposalResolvedSnapshotRun`, still written over the retired total
`proposedBlock`): the proposal is the bound named witness `P`, its carried raw
and support votes are `P.erase.gf_votes`/`P.erase.gf_support_votes`, and the
voter reads its prepared vote-duty read.

The retired module's route survives, with three changes forced by the named
runtime. Acceptance and processing are stated at the *named body* behind a
stored block, so each visibility step first names the resolved target. Block
identity across two honest stores comes from run-block root injectivity rather
than from the erased store. And the proposal's carried votes are known to sit
at slot `s - 1` from the proposer view's own validity
(`proposerDutyStore_proposer_view_valid`), which replaces the retired
`carried_votes_wf_of_mem_T`. -/

/-- Two run blocks with the same root are the same named block. -/
private theorem frozenSuffix_runBlock_unique_of_root
    {S : Setup V} {rho : Run V} (adm : AdmissibleCore S rho)
    {A B : NamedBlock V} (hA : RunBlock S rho A) (hB : RunBlock S rho B)
    (hroot : A.root = B.root) : A = B :=
  adm.toNamedRootCollisionFree.root_injective
    A B hA hB A B (Or.inl (Proofs.NamedAncestry.named_self A))
      (Or.inr (Proofs.NamedAncestry.named_self B)) hroot

/-- One resolved block identity transports into any honest store that already
holds that exact block. -/
private theorem frozenSuffix_find_of_find_and_mem
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) (t : Time)
    {source : Protocol.Store V} {u : GoldfishVote V} {H : Block V}
    (hfind : Block.find? source.T u.head = some H)
    (hHmem : H ∈ (rho.storeBeforeTime S w t).core.T) :
    Block.find? (rho.storeBeforeTime S w t).core.T u.head = some H := by
  have hsch := adm.toNamedScheduleWellFormed
  have hHroot : H.root = u.head := Proofs.HealingLemmas.find?_root hfind
  rw [← hHroot]
  refine Proofs.Optimistic.find?_eq_some_of_unique hHmem ?_
  intro Y hY hrootEq
  obtain ⟨Yn, hYe, hYrun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S hsch hw t hY
  obtain ⟨Hn, hHe, hHrun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S hsch hw t hHmem
  have hr : Yn.root = Hn.root := by
    rw [← Proofs.NamedWire.erase_root Yn, ← Proofs.NamedWire.erase_root Hn, hYe, hHe]
    exact hrootEq
  have heq : Yn = Hn := frozenSuffix_runBlock_unique_of_root adm hYrun hHrun hr
  rw [← hYe, ← hHe, heq]

/-- Two honest duty stores cannot resolve one root to different run blocks. -/
private theorem frozenSuffix_resolved_blocks_eq
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} (hprop : S.E.proposer s ∈ rho.honest)
    {v : V} (hv : v ∈ rho.honest) {u : GoldfishVote V} {H K : Block V}
    (hH : Block.find? (Protocol.proposerDutyStore S rho s).T u.head = some H)
    (hK : Block.find? (Proofs.Optimistic.voteDutyStore S rho v s).T u.head = some K) :
    H = K := by
  have hsch := adm.toNamedScheduleWellFormed
  obtain ⟨Hn, hHe, hHrun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S hsch hprop
      (Protocol.proposal_time S.E s) (Proofs.HealingLemmas.find?_mem hH)
  obtain ⟨Kn, hKe, hKrun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S hsch hv
      (Protocol.vote_time S.E s) (Proofs.HealingLemmas.find?_mem hK)
  have hroot : Hn.root = Kn.root := by
    rw [← Proofs.NamedWire.erase_root Hn, ← Proofs.NamedWire.erase_root Kn, hHe, hKe]
    exact (Proofs.HealingLemmas.find?_root hH).trans (Proofs.HealingLemmas.find?_root hK).symm
  have heq : Hn = Kn := frozenSuffix_runBlock_unique_of_root adm hHrun hKrun hroot
  rw [← hHe, ← hKe, heq]

/-- The support view of a vote duty read is inside its own raw view. -/
private theorem frozenSuffix_voterSupport_subset_voterView
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho) (v : V) (s : Slot) :
    Protocol.voter_support_view S.E
        (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.toFG.toSG.toGoldfishStore s ⊆
      Protocol.voter_view S.E
        (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.toFG.toSG.toGoldfishStore s := by
  have hsch := adm.toNamedScheduleWellFormed
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S hsch
    (Protocol.vote_time S.E s)
  refine Protocol.voter_support_view_subset S.E _ s ?_
  intro B hB
  refine Proofs.Optimistic.carried_support_subset_of_mem_T_core S adm v n ?_
  simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
    Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn] using hB

/-- A filtered-tree candidate is above its store's finalized block. -/
private theorem frozenSuffix_F_preceq_of_mem_filtered
    (st : Protocol.Store V) {C : Block V}
    (hC : C ∈ Protocol.get_filtered_block_tree st.toHealing.toFG) :
    Block.Preceq st.F C := by
  simp only [Protocol.get_filtered_block_tree,
    Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
    Protocol.finalized_descendants, Protocol.viable,
    Finset.mem_filter, decide_eq_true_eq, Protocol.Store.toHealing] at hC
  exact hC.1.1.2

/-- The delivery guard from a candidate below the named block. -/
private theorem frozenSuffix_finalizedBelowAtDeliveries_of_preceq
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} {t : Time} {C : Block V} {H : NamedBlock V}
    (hFC : Block.Preceq (rho.storeBeforeTime S w t).core.F C)
    (hCH : Block.Preceq C H.erase) :
    Protocol.BlockFinalizedBelowAtDeliveriesBefore S rho w H t := by
  have hsch := adm.toNamedScheduleWellFormed
  let N := (rho.events.filter (fun e => decide (e.time < t))).length
  have hstore : rho.storeBeforeTime S w t = (rho.stateBefore S N w).st :=
    congrArg NamedNodeState.st
      (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S hsch t) w)
  have hFCN : Block.Preceq (rho.stateBefore S N w).st.core.F C := by
    simpa only [hstore] using hFC
  intro i hi
  have hiN : i ≤ N := hi
  exact Block.preceq_trans
    (Protocol.stateBefore_F_mono S rho w hiN)
    (Block.preceq_trans hFCN hCH)

/-- A target the honest proposer resolved is visible, and stamped, at every
honest voter of the same slot. -/
private theorem frozenSuffix_proposalTarget_visibleAtVote
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E (s - 1))
    (hprop : S.E.proposer s ∈ rho.honest)
    {v : V} (hv : v ∈ rho.honest)
    (hhor : Protocol.vote_time S.E s ≤ rho.horizon)
    {C : Block V}
    (hC : C ∈ Protocol.get_filtered_block_tree
      (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.toFG)
    {u : GoldfishVote V} {H : Block V}
    (hfind : Block.find? (Protocol.proposerDutyStore S rho s).T u.head
      = some H)
    (hCH : Block.Preceq C H) :
    Block.find? (Proofs.Optimistic.voteDutyStore S rho v s).T u.head = some H ∧
      stampedBefore (Proofs.Optimistic.voteDutyStore S rho v s).timestamp_block
        (Protocol.vote_time S.E s) H = true := by
  have hsch := adm.toNamedScheduleWellFormed
  have hHsource : H ∈ (Protocol.proposerDutyStore S rho s).T :=
    Proofs.HealingLemmas.find?_mem hfind
  obtain ⟨Hn, hHnbody, hHne⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (Protocol.proposal_time S.E s) (S.E.proposer s) hHsource
  obtain ⟨n, hn, hbefore⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S hsch
    (Protocol.proposal_time S.E s)
  have hHn : Hn ∈ (rho.stateBefore S n (S.E.proposer s)).st.bodies := by
    simpa only [Run.storeBeforeTime, hn] using hHnbody
  have hprocessed : Object.processed
      (rho.stateBefore S n (S.E.proposer s)).st (NamedObject.block Hn) = true := by
    simpa only [Object.processed, NamedReceipt.processed,
      decide_eq_true_eq] using hHn
  rcases Protocol.acceptsAt_block_of_processed S rho (S.E.proposer s) n Hn
      hprocessed with hgen | ⟨i, hi, t, hacc⟩
  · have hHgen : H = Block.genesis := by rw [← hHne, hgen]; rfl
    have hvisible := Protocol.genesis_mem_and_stamp_storeBeforeTime S hsch v
      (Protocol.vote_time S.E s) (Protocol.vote_time S.E s)
    refine ⟨?_, ?_⟩
    · exact frozenSuffix_find_of_find_and_mem S adm hv
        (Protocol.vote_time S.E s) hfind (by rw [hHgen]; exact hvisible.1)
    · rw [hHgen]; exact hvisible.2
  · obtain ⟨-, e, he, -, het⟩ := hacc.1
    have ht : t < Protocol.proposal_time S.E s := by
      rw [← het]
      exact hbefore i e hi he
    have hpostS : S.E.t_GST ≤ Protocol.proposal_time S.E s :=
      hpost.trans (Protocol.proposal_time_mono S.E (Nat.sub_le s 1))
    have hhop : Protocol.proposal_time S.E s + S.E.Δ =
        Protocol.vote_time S.E s := by
      unfold Protocol.proposal_time Protocol.vote_time
      ring
    have hFC : Block.Preceq (Proofs.Optimistic.voteDutyStore S rho v s).F C :=
      frozenSuffix_F_preceq_of_mem_filtered _ hC
    have hFhist := frozenSuffix_finalizedBelowAtDeliveries_of_preceq S adm
      (w := v) (t := Protocol.vote_time S.E s) hFC (by rw [hHne]; exact hCH)
    have hHpos : 0 < Hn.slot := by
      rw [← Proofs.NamedWire.erase_slot]
      exact Nat.zero_lt_of_lt
        (Protocol.parent_slot_lt_of_acceptsAt_block S hacc)
    have hadmit : Protocol.AdmittedBefore S rho v Hn.erase
        (Protocol.vote_time S.E s) :=
      Protocol.block_admittedBefore_of_accepted_after_cutoff_core
        S adm hprop hv hHpos hacc ht hpostS hhop hhor hFhist
    have hvisible := Protocol.admittedBefore_mem_and_stamp_at S hsch hadmit
      (le_refl _)
    rw [hHne] at hvisible
    exact ⟨frozenSuffix_find_of_find_and_mem S adm hv
      (Protocol.vote_time S.E s) hfind hvisible.1, hvisible.2⟩

/-- A pre-freeze target an honest voter resolved is visible at the honest
proposer of the same slot. -/
private theorem frozenSuffix_voterTarget_visibleAtProposal
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E (s - 1))
    (hprop : S.E.proposer s ∈ rho.honest)
    {v : V} (hv : v ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E s ≤ rho.horizon)
    {C : Block V}
    (hC : C ∈ Protocol.get_filtered_block_tree
      (Protocol.proposerDutyStore S rho s).toHealing.toFG)
    {u : GoldfishVote V} {H : Block V}
    (hfind : Block.find? (Proofs.Optimistic.voteDutyStore S rho v s).T u.head = some H)
    (hHstamp : stampedBefore
      (Proofs.Optimistic.voteDutyStore S rho v s).timestamp_block
      (Protocol.view_freeze S.E (s - 1)) H = true)
    (hCH : Block.Preceq C H) :
    Block.find? (Protocol.proposerDutyStore S rho s).T u.head = some H := by
  have hsch := adm.toNamedScheduleWellFormed
  have hpred : s - 1 + 1 = s := Nat.sub_add_cancel
    (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hs))
  have hHtarget : H ∈ (Proofs.Optimistic.voteDutyStore S rho v s).T :=
    Proofs.HealingLemmas.find?_mem hfind
  obtain ⟨Hn, hHnbody, hHne⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (Protocol.vote_time S.E s) v hHtarget
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S hsch
    (Protocol.vote_time S.E s)
  have hHn : Hn ∈ (rho.stateBefore S n v).st.bodies := by
    simpa only [Run.storeBeforeTime, hn] using hHnbody
  have hstampn : stampedBefore (rho.stateBefore S n v).st.core.timestamp_block
      (Protocol.view_freeze S.E (s - 1)) Hn.erase = true := by
    rw [hHne]
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn] using hHstamp
  have hprocessed : Object.processed (rho.stateBefore S n v).st
      (NamedObject.block Hn) = true := by
    simpa only [Object.processed, NamedReceipt.processed,
      decide_eq_true_eq] using hHn
  rcases Protocol.acceptsAt_block_of_processed S rho v n Hn hprocessed with
    hgen | ⟨i, hi, t, hacc⟩
  · have hHgen : H = Block.genesis := by rw [← hHne, hgen]; rfl
    have hvisible := Protocol.genesis_mem_and_stamp_storeBeforeTime S hsch
      (S.E.proposer s) (Protocol.proposal_time S.E s)
        (Protocol.proposal_time S.E s)
    exact frozenSuffix_find_of_find_and_mem S adm hprop
      (Protocol.proposal_time S.E s) hfind (by rw [hHgen]; exact hvisible.1)
  · have ht : t < Protocol.view_freeze S.E (s - 1) :=
      Protocol.HonestWeightMajority.acceptsAt_block_lt_of_stamp_before_core
        S adm hv hacc (Nat.succ_le_of_lt hi)
          (Protocol.publicTime_view_freeze S (s - 1)) hstampn
    have hpostFreeze : S.E.t_GST ≤ Protocol.view_freeze S.E (s - 1) := by
      apply hpost.trans
      calc
        Protocol.proposal_time S.E (s - 1) ≤
            Protocol.proposal_time S.E (s - 1) + 3 * S.E.Δ :=
          Int.le_add_of_nonneg_right
            (Int.mul_nonneg (by norm_num) (le_of_lt S.E.Δ_pos))
        _ = Protocol.view_freeze S.E (s - 1) := by
          unfold Protocol.proposal_time Protocol.view_freeze
          ring
    have hhop : Protocol.view_freeze S.E (s - 1) + S.E.Δ =
        Protocol.proposal_time S.E s := by
      rw [← hpred]
      exact Protocol.view_freeze_add_delta_eq_proposal_time_succ S.E (s - 1)
    have hFC : Block.Preceq (Protocol.proposerDutyStore S rho s).F C :=
      frozenSuffix_F_preceq_of_mem_filtered _ hC
    have hFhist := frozenSuffix_finalizedBelowAtDeliveries_of_preceq S adm
      (w := S.E.proposer s) (t := Protocol.proposal_time S.E s) hFC
        (by rw [hHne]; exact hCH)
    have hHpos : 0 < Hn.slot := by
      rw [← Proofs.NamedWire.erase_slot]
      exact Nat.zero_lt_of_lt
        (Protocol.parent_slot_lt_of_acceptsAt_block S hacc)
    have hadmit : Protocol.AdmittedBefore S rho (S.E.proposer s) Hn.erase
        (Protocol.proposal_time S.E s) :=
      Protocol.block_admittedBefore_of_accepted_after_cutoff_core
        S adm hv hprop hHpos hacc ht hpostFreeze hhop hhor hFhist
    have hvisible := Protocol.admittedBefore_mem_and_stamp_at S hsch hadmit
      (le_refl _)
    rw [hHne] at hvisible
    exact frozenSuffix_find_of_find_and_mem S adm hprop
      (Protocol.proposal_time S.E s) hfind hvisible.1

/-- **The candidate score bridge**: the honest proposal's carried raw and
support votes score every common candidate exactly as the honest voter's own
merged view does. -/
theorem namedProposalCandidateScoreBridge_afterGST_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E (s - 1))
    (hprop : S.E.proposer s ∈ rho.honest)
    {v : V} (hv : v ∈ rho.honest)
    (hhor : Protocol.vote_time S.E s ≤ rho.horizon)
    {P : NamedBlock V} (hP : proposedBlockAt S rho s = some P)
    (hproposal : P.erase ∈ Protocol.get_filtered_block_tree
      (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.toFG) :
    NamedProposalCandidateScoreBridge S rho s v P := by
  have hsch := adm.toNamedScheduleWellFormed
  have hproposalHor : Protocol.proposal_time S.E s ≤ rho.horizon :=
    le_trans (le_of_lt (Protocol.proposal_time_lt_vote_time S.E s)) hhor
  have hrawExtra := voter_raw_extra_equivocates_proposal_afterGST_core
    S adm hs hpost hprop hv hproposalHor hP hproposal
  have hBvote : P.erase ∈ (Proofs.Optimistic.voteDutyStore S rho v s).T :=
    Proofs.Records.get_filtered_block_tree_subset _ hproposal
  have hPslot : P.erase.slot = s := by
    rw [Proofs.NamedWire.erase_slot]
    exact proposedBlockAt_slot S rho s hP
  have hsourceSlot : (Protocol.proposerDutyStore S rho s).s = s := by
    simp only [Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
      Proofs.Optimistic.slotOf_proposal_time]
  have hraw : P.erase.gf_votes.toFinset =
      (Protocol.proposer_view
        (Protocol.proposerDutyStore S rho s).toHealing.toFG.toSG.toGoldfishStore
        (Protocol.proposerDutyStore S rho s).s).toFinset := by
    rw [Proofs.NamedWire.erase_goldfish_votes,
      Protocol.proposedBlock_gf_votes S rho s hP]
    rfl
  have hsupport : P.erase.gf_support_votes.toFinset =
      (Protocol.proposer_support_view
        (Protocol.proposerDutyStore S rho s).toHealing.toFG.toSG.toGoldfishStore
        (Protocol.proposerDutyStore S rho s).s).toFinset := by
    rw [Proofs.NamedWire.erase_goldfish_support,
      Protocol.proposedBlock_gf_support_votes S rho s hP]
    rfl
  have hvalid := Protocol.proposerDutyStore_proposer_view_valid_core S adm s
  have hslots : ∀ u ∈ P.erase.gf_votes, u.slot + 1 = P.erase.slot := by
    intro u hu
    have hmem : u ∈ (Protocol.proposer_view
        (Protocol.proposerDutyStore S rho s).toHealing.toFG.toSG.toGoldfishStore
        (Protocol.proposerDutyStore S rho s).s).toFinset := by
      rw [← hraw]
      exact List.mem_toFinset.mpr hu
    have hslot := (hvalid u hmem).1
    rw [hsourceSlot] at hslot
    rw [hPslot, hslot]
    exact Nat.succ_pred_eq_of_pos hs
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S hsch
    (Protocol.vote_time S.E s)
  have hBprefix : P.erase ∈ (rho.stateBefore S n v).st.core.T := by
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn] using hBvote
  intro C hCsource hCtarget
  refine
    { raw_subset := Protocol.carried_raw_subset_voter_view S.E
        (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.toFG.toSG.toGoldfishStore hBvote hPslot
          hslots
      raw_extra_equiv := hrawExtra
      forward := ?_
      backward := ?_ }
  · intro u hu htarget
    obtain ⟨H, hfindSource, hCH⟩ := Protocol.targets_under_iff.mp htarget
    have hvis := frozenSuffix_proposalTarget_visibleAtVote
      S adm hpost hprop hv hhor hCtarget hfindSource hCH.2
    have hresolved : Protocol.resolved
        (Proofs.Optimistic.voteDutyStore S rho v s).T u = true := by
      unfold Protocol.resolved
      rw [hvis.1]
      simp [hCH.1]
    have huslot : u.slot + 1 = P.erase.slot :=
      hslots u (Proofs.Optimistic.carried_support_subset_of_mem_T_core S adm v n hBprefix u
        (List.mem_toFinset.mp hu))
    exact Or.inl ⟨Protocol.mem_voter_support_view_of_carried S.E
      (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.toFG.toSG.toGoldfishStore hBvote hPslot
      (List.mem_toFinset.mp hu) hresolved huslot,
      Protocol.targets_under_iff.mpr ⟨H, hvis.1, hCH.1, hCH.2⟩⟩
  · intro u hu htarget
    have huRaw : u ∈ Protocol.voter_view S.E
        (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.toFG.toSG.toGoldfishStore s :=
      frozenSuffix_voterSupport_subset_voterView S adm v s hu
    rw [Protocol.voter_support_view, Finset.mem_union] at hu
    rcases hu with hpool | hcarried
    · by_cases huSource : u ∈ P.erase.gf_votes.toFinset
      · obtain ⟨K, hfindTarget, hCK⟩ := Protocol.targets_under_iff.mp htarget
        have huResolved : stampedBefore
            (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.toFG.toSG.toGoldfishStore.tau
            (Protocol.view_freeze S.E (s - 1)) u = true := by
          rw [beforeCutoff, Finset.mem_filter] at hpool
          exact hpool.2
        have hKstamp : stampedBefore
            (Proofs.Optimistic.voteDutyStore S rho v s).timestamp_block
            (Protocol.view_freeze S.E (s - 1)) K = true :=
          Protocol.HonestWeightMajority.stampedBefore_block_of_resolution
            hfindTarget huResolved
        have hfindSource := frozenSuffix_voterTarget_visibleAtProposal
          S adm hs hpost hprop hv hproposalHor hCsource hfindTarget hKstamp hCK.2
        have huSourceList : u ∈ (Protocol.proposer_view
            (Protocol.proposerDutyStore S rho s).toHealing.toFG.toSG.toGoldfishStore
            (Protocol.proposerDutyStore S rho s).s) := by
          have hmem : u ∈ (Protocol.proposer_view
              (Protocol.proposerDutyStore S rho s).toHealing.toFG.toSG.toGoldfishStore
              (Protocol.proposerDutyStore S rho s).s).toFinset := by
            rw [← hraw]
            exact huSource
          exact List.mem_toFinset.mp hmem
        have huSupport : u ∈ P.erase.gf_support_votes.toFinset := by
          rw [hsupport, List.mem_toFinset, Protocol.proposer_support_view,
            List.mem_filter]
          refine ⟨huSourceList, ?_⟩
          unfold Protocol.resolved
          simp only [Protocol.Store.toHealing, hfindSource]
          simp [hCK.1]
        exact Or.inl ⟨huSupport,
          Protocol.targets_under_iff.mpr ⟨K, hfindSource, hCK.1, hCK.2⟩⟩
      · exact Or.inr (hrawExtra u huRaw huSource)
    · rw [Finset.mem_biUnion] at hcarried
      obtain ⟨B, hB, huB⟩ := hcarried
      rw [Finset.mem_filter] at hB huB
      have hBprefix' : B ∈ (rho.stateBefore S n v).st.core.T := by
        simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn] using hB.1
      have hBeq : B = P.erase :=
        unique_slot_block_in_store_core S adm hs hprop
          hBprefix' hBprefix hB.2 hPslot
      subst hBeq
      have huSource : u ∈ P.erase.gf_support_votes.toFinset := huB.1
      obtain ⟨K, hfindTarget, hCK⟩ := Protocol.targets_under_iff.mp htarget
      have hmem : u ∈ (Protocol.proposer_support_view
          (Protocol.proposerDutyStore S rho s).toHealing.toFG.toSG.toGoldfishStore
          (Protocol.proposerDutyStore S rho s).s).toFinset := by
        rw [← hsupport]
        exact huSource
      rw [List.mem_toFinset, Protocol.proposer_support_view,
        List.mem_filter] at hmem
      have huResolvedSource : Protocol.resolved
          (Protocol.proposerDutyStore S rho s).T u = true := by
        exact of_decide_eq_true (by
          simpa only [Protocol.Store.toHealing] using hmem.2)
      obtain ⟨H, hfindSource⟩ : ∃ H, Block.find?
          (Protocol.proposerDutyStore S rho s).T u.head = some H := by
        cases hfind : Block.find? (Protocol.proposerDutyStore S rho s).T u.head with
        | none => simp [Protocol.resolved, hfind] at huResolvedSource
        | some H => exact ⟨H, rfl⟩
      have hHK : H = K :=
        frozenSuffix_resolved_blocks_eq S adm hprop hv hfindSource hfindTarget
      have hHslot : H.slot ≤ u.slot := by
        simpa only [← hHK] using hCK.1
      have hHC : C.preceq H = true := by
        simpa only [← hHK] using hCK.2
      exact Or.inl ⟨huSource,
        Protocol.targets_under_iff.mpr ⟨H, hfindSource, hHslot, hHC⟩⟩

theorem namedProposalCandidateScoreBridge_afterGST
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E (s - 1))
    (hprop : S.E.proposer s ∈ rho.honest)
    {v : V} (hv : v ∈ rho.honest)
    (hhor : Protocol.vote_time S.E s ≤ rho.horizon)
    {P : NamedBlock V} (hP : proposedBlockAt S rho s = some P)
    (hproposal : P.erase ∈ Protocol.get_filtered_block_tree
      (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.toFG) :
    NamedProposalCandidateScoreBridge S rho s v P :=
  namedProposalCandidateScoreBridge_afterGST_core
    S adm.toNamedAdmissibleCore hs hpost hprop hv hhor hP hproposal

#print axioms namedProposalCandidateScoreBridge_afterGST_core

/-- The current frozen processed-tree semantics and a fixed-height window imply
both directions of the proposal suffix transfer.

This is the named producer of the opening lifecycle's `_of_pivotTransfer`
premise: its conclusion is exactly
`NamedProposalPivotSuffixTransfer S rho s pivot v P`, the `suffix` field of
`NamedSGOpeningFrozenVoteAt`. -/
theorem namedProposalPivotSuffixTransfer_of_frozenProposalNoRise
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E (s - 1))
    (hprop : S.E.proposer s ∈ rho.honest)
    {v : V} (hv : v ∈ rho.honest)
    (hvoteHor : Protocol.vote_time S.E s ≤ rho.horizon)
    {pivot : Block V} {P : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P)
    (h : NamedFrozenProposalSuffixInputs S rho s pivot v P) :
    NamedProposalPivotSuffixTransfer S rho s pivot v P :=
  namedProposalPivotSuffixTransfer_of_core_of_scoreBridge
    S adm.toNamedAdmissibleCore hs hpost hprop hv hvoteHor hP
      h.toNamedFrozenProposalSuffixCoreInputs
        (namedProposalCandidateScoreBridge_afterGST S adm hs hpost hprop hv
          hvoteHor hP (frozenVoterCandidateTree_subset_filtered S.E _
            h.proposalCandidate))
        (Or.inl h.sameHMax)

/-- The same suffix transfer remains valid during a one-step frontier change
when the common pivot stays in both stores' viability bands. -/
theorem namedProposalPivotSuffixTransfer_of_riseLeOne_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E (s - 1))
    (hprop : S.E.proposer s ∈ rho.honest)
    {v : V} (hv : v ∈ rho.honest)
    (hvoteHor : Protocol.vote_time S.E s ≤ rho.horizon)
    {pivot : Block V} {P : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P)
    (h : NamedFrozenProposalSuffixBandInputs S rho s pivot v P) :
    NamedProposalPivotSuffixTransfer S rho s pivot v P :=
  namedProposalPivotSuffixTransfer_of_core_of_scoreBridge
    S adm hs hpost hprop hv hvoteHor hP
      h.toNamedFrozenProposalSuffixCoreInputs
        (namedProposalCandidateScoreBridge_afterGST_core S adm hs hpost hprop hv
          hvoteHor hP (frozenVoterCandidateTree_subset_filtered S.E _
            h.proposalCandidate))
        (Or.inr ⟨h.sourceBand, h.targetBand⟩)

theorem namedProposalPivotSuffixTransfer_of_riseLeOne
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E (s - 1))
    (hprop : S.E.proposer s ∈ rho.honest)
    {v : V} (hv : v ∈ rho.honest)
    (hvoteHor : Protocol.vote_time S.E s ≤ rho.horizon)
    {pivot : Block V} {P : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P)
    (h : NamedFrozenProposalSuffixBandInputs S rho s pivot v P) :
    NamedProposalPivotSuffixTransfer S rho s pivot v P :=
  namedProposalPivotSuffixTransfer_of_riseLeOne_core
    S adm.toNamedAdmissibleCore hs hpost hprop hv hvoteHor hP h

#print axioms namedProposalPivotSuffixTransfer_of_riseLeOne_core


/-
/-- The proposal parent is a source-walk candidate at the exact proposal read. -/
private theorem proposedParent_mem_proposalWalkSourceTree
    (S: Setup V) {rho: Run V} (adm: Admissible S rho) (s: Slot):
    proposedParent S rho s ∈ proposalWalkSourceTree S rho s:= by
  let p:= S.E.proposer s
  let t:= Protocol.proposal_time S.E s
  let pre:= rho.storeBeforeTime S p t
  let duty:= proposerDutyStore S rho s
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node p) pre:= by
    simpa only [pre, p, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed t p)
  have hrootPre:= fgRoot_mem_filtered_depReachable
    S.E S.hc S.cfg (S.node p) hdep
  have hrootDuty: Protocol.get_fg_root duty.toHealing.toFG ∈
      Protocol.get_filtered_block_tree duty.toHealing.toFG:= by
    simpa only [duty, proposerDutyStore, Proofs.Optimistic.tickStore,
      pre, t, p] using hrootPre
  let votes:= Protocol.proposer_view duty.toHealing.toFG.toSG.toGoldfishStore duty.s
  let support:= Protocol.proposer_support_view duty.toHealing.toFG.toSG.toGoldfishStore duty.s
  have hhead:= getHead_mem_filtered_of_fgRoot_mem
    S.E S.hc duty.toHealing votes.toFinset support.toFinset
      (duty.s - 1) hrootDuty
  simpa only [proposalWalkSourceTree, proposedParent, duty, votes, support]
    using hhead

/-- Reuse the frozen proposal's processed viability witness for an ancestor on
its proposal segment. -/
private theorem voterCandidate_on_proposalSegment
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {s: Slot} {v: V} {D: Block V}
    (hproposal: proposedBlock S rho s ∈
      Proofs.Optimistic.voter_candidate_tree S.E
        (Proofs.Optimistic.voteDutyStore S rho v s).toHealing)
    (hDP: Block.Preceq D (proposedBlock S rho s))
    (hFD: Block.Preceq (Proofs.Optimistic.voteDutyStore S rho v s).F D)
    (hrootD: Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.toFG) D):
    D ∈ Proofs.Optimistic.voter_candidate_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho v s).toHealing:= by
  let target:= Proofs.Optimistic.voteDutyStore S rho v s
  let pre:= rho.storeBeforeTime S v (Protocol.vote_time S.E s)
  have hdata:= hproposal
  simp only [Proofs.Optimistic.voter_candidate_tree,
    Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq] at hdata ⊢
  obtain ⟨⟨⟨hPprocessed, _hFP⟩, W, hWprocessed, hPW, hheight⟩,
    _hrootP⟩:= hdata
  have hPT: proposedBlock S rho s ∈ target.T:= by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
      at hPprocessed
    exact hPprocessed.1
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node v) pre:= by
    simpa only [pre, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed (Protocol.vote_time S.E s) v)
  have hpcPre: ParentClosed pre:=
    parentClosed_depReachable S.E S.hc S.cfg (S.node v) pre hdep
  have hpc: ParentClosed target:= by
    simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, pre] using hpcPre
  have hDT: D ∈ target.T:=
    Proofs.Records.mem_of_preceq ((parentClosed_iff target).mp hpc).2
      D (proposedBlock S rho s) hPT hDP
  have hDprocessed: D ∈ Protocol.voter_processed_block_tree S.E
      target.toHealing.toFG.toSG.toGoldfishStore target.toHealing.s:= by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    refine ⟨hDT, Or.inr ?_⟩
    refine ⟨proposedBlock S rho s, ⟨hPT, ?_⟩, hDP⟩
    simpa only [target, Proofs.Optimistic.toHealing_slot,
      Proofs.Optimistic.voteDutyStore_slot] using proposedBlock_slot S rho s
  exact ⟨⟨⟨hDprocessed, by simpa only [target] using hFD⟩,
      W, hWprocessed, Block.preceq_trans hDP hPW, hheight⟩,
    by simpa only [target] using hrootD⟩

/-- A target full-tree candidate below the frozen proposal supplies all root and
finality guards needed to restrict that segment to the frozen voter tree. -/
private theorem voterCandidate_above_fullPivot
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {s: Slot} {v: V} {A D: Block V}
    (hproposal: proposedBlock S rho s ∈
      Proofs.Optimistic.voter_candidate_tree S.E
        (Proofs.Optimistic.voteDutyStore S rho v s).toHealing)
    (hA: A ∈ Protocol.get_filtered_block_tree
      (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.toFG)
    (hAD: Block.Preceq A D)
    (hDP: Block.Preceq D (proposedBlock S rho s)):
    D ∈ Proofs.Optimistic.voter_candidate_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho v s).toHealing:= by
  let target:= Proofs.Optimistic.voteDutyStore S rho v s
  let pre:= rho.storeBeforeTime S v (Protocol.vote_time S.E s)
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node v) pre:= by
    simpa only [pre, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed (Protocol.vote_time S.E s) v)
  have hFJPre: Block.Preceq pre.F pre.J:=
    finalizedPrecedesJustifiedInvariant S.E S.hc S.cfg (S.node v) pre
      (Proofs.Bridges.reachableStore_of_depReachableStore
        S.E S.hc S.cfg (S.node v) hdep)
  have hFJ: Block.Preceq target.F target.J:= by
    simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, pre] using hFJPre
  have hrootA: Block.Preceq
      (Protocol.get_fg_root target.toHealing.toFG) A:=
    Proofs.Records.preceq_get_fg_root_of_mem_filtered hA
  have hFA: Block.Preceq target.F A:=
    Block.preceq_trans
      (Proofs.Records.preceq_get_fg_root_of_F (st:= target.toHealing.toFG) hFJ)
      hrootA
  exact voterCandidate_on_proposalSegment S adm hproposal hDP
    (Block.preceq_trans hFA hAD) (Block.preceq_trans hrootA hAD)

/-- A frozen processed block outside the exact current proposal chain must be
in the pre-freeze arm of `voter_processed_block_tree`. -/
private theorem stampedBefore_of_voterProcessed_not_proposalAncestor
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {s: Slot} (hs: 0 < s)
    (hprop: S.E.proposer s ∈ rho.honest)
    {v: V} {Z: Block V}
    (hproposal: proposedBlock S rho s ∈
      Proofs.Optimistic.voter_candidate_tree S.E
        (Proofs.Optimistic.voteDutyStore S rho v s).toHealing)
    (hZprocessed: Z ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.s)
    (hnot: ¬ Block.Preceq Z (proposedBlock S rho s)):
    stampedBefore
      (Proofs.Optimistic.voteDutyStore S rho v s).timestamp_block
      (Protocol.view_freeze S.E (s - 1)) Z = true:= by
  let target:= Proofs.Optimistic.voteDutyStore S rho v s
  have hdata:= hZprocessed
  simp only [Protocol.voter_processed_block_tree, Finset.mem_filter] at hdata
  rcases hdata.2 with hstamp | hcurrent
  · simpa only [target, Proofs.Optimistic.toHealing_slot,
      Proofs.Optimistic.voteDutyStore_slot] using hstamp
  · obtain ⟨P, hP, hZP⟩:= hcurrent
    have hproposalFull: proposedBlock S rho s ∈
        Protocol.get_filtered_block_tree target.toHealing.toFG:=
      frozenVoterCandidateTree_subset_filtered S.E target.toHealing
        (by simpa only [target] using hproposal)
    have hproposalT: proposedBlock S rho s ∈ target.T:=
      Proofs.Records.get_filtered_block_tree_subset target.toHealing.toFG hproposalFull
    obtain ⟨n, hn, -⟩:= Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toScheduleWellFormed (Protocol.vote_time S.E s)
    have hPprefix: P ∈ (rho.stateBefore S n v).st.T:= by
      simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn] using hP.1
    have hproposalPrefix: proposedBlock S rho s ∈
        (rho.stateBefore S n v).st.T:= by
      simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn] using hproposalT
    have hPeq: P = proposedBlock S rho s:=
      unique_slot_block_in_store S adm hs hprop hPprefix hproposalPrefix
        (by simpa only [target, Proofs.Optimistic.toHealing_slot,
          Proofs.Optimistic.voteDutyStore_slot] using hP.2)
        (proposedBlock_slot S rho s)
    exact False.elim (hnot (by simpa only [hPeq] using hZP))

/-- A source-anchor descendant closes the honest proposer's finalized-delivery
guard at every prefix before the proposal read. -/
private theorem sourceAnchor_finalizedBelowAtDeliveries
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {s: Slot} {Z: Block V}
    (hanchor: Block.Preceq
      (Proofs.Optimistic.healAnchor S.E S.hc
        (proposerDutyStore S rho s).toHealing) Z):
    BlockFinalizedBelowAtDeliveriesBefore S rho (S.E.proposer s) Z
      (Protocol.proposal_time S.E s):= by
  let source:= proposerDutyStore S rho s
  let pre:= rho.storeBeforeTime S (S.E.proposer s)
    (Protocol.proposal_time S.E s)
  have hdep: DepReachableStore S.E S.hc S.cfg
      (S.node (S.E.proposer s)) pre:= by
    simpa only [pre, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed (Protocol.proposal_time S.E s)
          (S.E.proposer s))
  have hFJPre: Block.Preceq pre.F pre.J:=
    finalizedPrecedesJustifiedInvariant S.E S.hc S.cfg
      (S.node (S.E.proposer s)) pre
      (Proofs.Bridges.reachableStore_of_depReachableStore
        S.E S.hc S.cfg (S.node (S.E.proposer s)) hdep)
  have hFJ: Block.Preceq source.F source.J:= by
    simpa only [source, proposerDutyStore, Proofs.Optimistic.tickStore, pre] using hFJPre
  have hFZ: Block.Preceq source.F Z:=
    Block.preceq_trans (StoreFinality.finalized_preceq_fgRoot hFJ)
      (Block.preceq_trans
        (StoreFinality.get_fg_root_preceq_get_sg_root S.E S.hc source)
        (by simpa only [source] using hanchor))
  let N:= (rho.events.filter (fun e => decide
    (e.time < Protocol.proposal_time S.E s))).length
  have hFZN: Block.Preceq
      (rho.stateBefore S N (S.E.proposer s)).st.F Z:= by
    simpa only [source, proposerDutyStore, Proofs.Optimistic.tickStore,
      Run.storeBeforeTime,
      Proofs.Optimistic.stateBeforeTime_eq_take S adm.toScheduleWellFormed,
      N] using hFZ
  intro i t hi _ hlt
  have hiN: i < N:= by
    by_contra hnot
    have hge: N ≤ i:= Nat.le_of_not_gt hnot
    have htime:= Proofs.Optimistic.le_time_of_index_ge
      S adm.toScheduleWellFormed hge hi
    exact (not_le_of_gt hlt) htime
  exact Block.preceq_trans
    (stateBefore_F_mono S rho (S.E.proposer s) (Nat.le_of_lt hiN)) hFZN

/-- A pre-freeze frozen block above the source anchor is present in the exact
honest proposer snapshot. -/
private theorem stampedVoterBlock_mem_proposerDuty_afterGST
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {s: Slot} (hs: 0 < s)
    (hpost: S.E.t_GST ≤ Protocol.proposal_time S.E (s - 1))
    (hprop: S.E.proposer s ∈ rho.honest)
    {v: V} (hv: v ∈ rho.honest)
    (hhor: Protocol.proposal_time S.E s ≤ rho.horizon)
    {Z: Block V}
    (hZT: Z ∈ (Proofs.Optimistic.voteDutyStore S rho v s).T)
    (hstamp: stampedBefore
      (Proofs.Optimistic.voteDutyStore S rho v s).timestamp_block
      (Protocol.view_freeze S.E (s - 1)) Z = true)
    (hanchor: Block.Preceq
      (Proofs.Optimistic.healAnchor S.E S.hc
        (proposerDutyStore S rho s).toHealing) Z):
    Z ∈ (proposerDutyStore S rho s).T:= by
  by_cases hgen: Z = Block.genesis
  · subst Z
    have hvisible:= genesis_mem_and_stamp_storeBeforeTime S
      adm.toScheduleWellFormed (S.E.proposer s)
        (Protocol.proposal_time S.E s) (Protocol.proposal_time S.E s)
    simpa only [proposerDutyStore, Proofs.Optimistic.tickStore] using hvisible.1
  · obtain ⟨n, hn, -⟩:= Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toScheduleWellFormed (Protocol.vote_time S.E s)
    have hZn: Z ∈ (rho.stateBefore S n v).st.T:= by
      simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn] using hZT
    have hstampn: stampedBefore (rho.stateBefore S n v).st.timestamp_block
        (Protocol.view_freeze S.E (s - 1)) Z = true:= by
      simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn] using hstamp
    have hprocessed: (Object.block Z).processed
        (rho.stateBefore S n v).st = true:= by
      simpa only [Object.processed, decide_eq_true_eq] using hZn
    rcases acceptsAt_block_of_processed S rho v n Z hprocessed with
      hgen' | ⟨i, hi, t, hacc⟩
    · exact False.elim (hgen hgen')
    · have ht: t < Protocol.view_freeze S.E (s - 1):=
        HonestWeightMajority.acceptsAt_block_lt_of_stamp_before
          S adm hv hacc (Nat.succ_le_of_lt hi)
            (publicTime_view_freeze S (s - 1)) hstampn
      have hpostFreeze: S.E.t_GST ≤ Protocol.view_freeze S.E (s - 1):= by
        apply hpost.trans
        calc
          Protocol.proposal_time S.E (s - 1) ≤
              Protocol.proposal_time S.E (s - 1) + 3 * S.E.Δ:=
            Int.le_add_of_nonneg_right
              (Int.mul_nonneg (by norm_num) (le_of_lt S.E.Δ_pos))
          _ = Protocol.view_freeze S.E (s - 1):= by
            unfold Protocol.proposal_time Protocol.view_freeze
            ring
      have hpred: s - 1 + 1 = s:= Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hs))
      have hhop: Protocol.view_freeze S.E (s - 1) + S.E.Δ =
          Protocol.proposal_time S.E s:= by
        rw [← hpred]
        unfold Protocol.view_freeze Protocol.proposal_time Env.t slotStart
        push_cast
        ring
      have hZpos: 0 < Z.slot:=
        Nat.zero_lt_of_lt (parent_slot_lt_of_acceptsAt_block S hacc)
      have hadmit: AdmittedBefore S rho (S.E.proposer s) Z
          (Protocol.proposal_time S.E s):=
        block_admittedBefore_of_accepted_after_cutoff
          S adm hv hprop hZpos hacc ht hpostFreeze hhop hhor
            (sourceAnchor_finalizedBelowAtDeliveries S adm hanchor)
      have hvisible:= admittedBefore_mem_and_stamp_at S
        adm.toScheduleWellFormed hadmit (le_refl _)
      simpa only [proposerDutyStore, Proofs.Optimistic.tickStore] using hvisible.1

/-- Current frozen semantics produce source candidate membership for every
eligible target child above the fixed pivot, independently of its score arm. -/
private theorem targetChild_mem_sourceTree_of_frozenProposal
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {s: Slot} (hs: 0 < s)
    (hpost: S.E.t_GST ≤ Protocol.proposal_time S.E (s - 1))
    (hprop: S.E.proposer s ∈ rho.honest)
    {v: V} (hv: v ∈ rho.honest)
    (hhor: Protocol.proposal_time S.E s ≤ rho.horizon)
    {pivot X C: Block V}
    (hsourceAnchor: Block.Preceq
      (Proofs.Optimistic.healAnchor S.E S.hc
        (proposerDutyStore S rho s).toHealing) pivot)
    (hproposal: proposedBlock S rho s ∈
      Proofs.Optimistic.voter_candidate_tree S.E
        (Proofs.Optimistic.voteDutyStore S rho v s).toHealing)
    (hviability:
      (proposerDutyStore S rho s).h_max - 1 ≤
          (Proofs.Optimistic.voteDutyStore S rho v s).h_max - 1 ∨
        (proposerDutyStore S rho s).h_max - 1 ≤
          (derived_state S.E S.cfg pivot).h)
    (hpivotX: Block.Preceq pivot X)
    (hCtarget: C ∈ proposalWalkTargetTree S rho s v)
    (hparent: C.parent? = some X):
    C ∈ proposalWalkSourceTree S rho s:= by
  let source:= proposerDutyStore S rho s
  let target:= Proofs.Optimistic.voteDutyStore S rho v s
  have htargetErase: C ∈
      (Proofs.Optimistic.voter_candidate_tree S.E target.toHealing).erase
        (proposedBlock S rho s):= by
    simpa only [proposalWalkTargetTree, target] using hCtarget
  have hCne: C ≠ proposedBlock S rho s:=
    (Finset.mem_erase.mp htargetErase).1
  have hCfrozen: C ∈ Proofs.Optimistic.voter_candidate_tree S.E target.toHealing:=
    (Finset.mem_erase.mp htargetErase).2
  have hXC: Block.Preceq X C:= preceq_of_parent? hparent
  have hanchorC: Block.Preceq
      (Proofs.Optimistic.healAnchor S.E S.hc source.toHealing) C:=
    Block.preceq_trans (by simpa only [source] using hsourceAnchor)
      (Block.preceq_trans hpivotX hXC)
  by_cases hCP: Block.Preceq C (proposedBlock S rho s)
  · have hCH: Block.Preceq C (proposedParent S rho s):=
      Proofs.Optimistic.preceq_parent_of_ne (proposedBlock_parent S rho s) hCP hCne
    have hHcandidate:= proposedParent_mem_proposalWalkSourceTree S adm s
    have hanchorNe: C ≠ Proofs.Optimistic.healAnchor S.E S.hc source.toHealing:= by
      intro heq
      have hCX: Block.Preceq C X:= by
        rw [heq]
        exact Block.preceq_trans (by simpa only [source] using hsourceAnchor)
          hpivotX
      have hdepthLe:= Block.preceq_depth_le hCX
      have hdepthChild:= depth_of_parent? hparent
      omega
    simpa only [proposalWalkSourceTree, source] using
      (proposalPath_of_candidate S adm hHcandidate C hanchorC hanchorNe hCH)
  · have hdata:= hCfrozen
    simp only [Proofs.Optimistic.voter_candidate_tree,
      Protocol.get_filtered_block_tree_from,
      Protocol.viable_tree, Protocol.finalized_descendants,
      Protocol.viable, Finset.mem_filter, decide_eq_true_eq] at hdata
    obtain ⟨⟨⟨hCprocessed, _hFC⟩, W, hWprocessed, hCW, hheightTarget⟩,
      _hrootC⟩:= hdata
    have hWT: W ∈ target.T:= by
      simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
        at hWprocessed
      exact hWprocessed.1
    have hCT: C ∈ target.T:= by
      simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
        at hCprocessed
      exact hCprocessed.1
    have hWnot: ¬ Block.Preceq W (proposedBlock S rho s):= by
      intro hWP
      exact hCP (Block.preceq_trans hCW hWP)
    have hCstamp:= stampedBefore_of_voterProcessed_not_proposalAncestor
      S adm hs hprop (by simpa only [target] using hproposal)
        hCprocessed hCP
    have hWstamp:= stampedBefore_of_voterProcessed_not_proposalAncestor
      S adm hs hprop (by simpa only [target] using hproposal)
        hWprocessed hWnot
    have hCTsource: C ∈ source.T:=
      stampedVoterBlock_mem_proposerDuty_afterGST
        S adm hs hpost hprop hv hhor hCT
          (by simpa only [target] using hCstamp) hanchorC
    have hanchorW: Block.Preceq
        (Proofs.Optimistic.healAnchor S.E S.hc source.toHealing) W:=
      Block.preceq_trans hanchorC hCW
    have hWTsource: W ∈ source.T:=
      stampedVoterBlock_mem_proposerDuty_afterGST
        S adm hs hpost hprop hv hhor hWT
          (by simpa only [target] using hWstamp) hanchorW
    let sourcePre:= rho.storeBeforeTime S (S.E.proposer s)
      (Protocol.proposal_time S.E s)
    let targetPre:= rho.storeBeforeTime S v (Protocol.vote_time S.E s)
    have hsourceDep: DepReachableStore S.E S.hc S.cfg
        (S.node (S.E.proposer s)) sourcePre:= by
      simpa only [sourcePre, Run.storeBeforeTime] using
        (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
          adm.toDeliveryWellFormed (Protocol.proposal_time S.E s)
            (S.E.proposer s))
    have htargetDep: DepReachableStore S.E S.hc S.cfg
        (S.node v) targetPre:= by
      simpa only [targetPre, Run.storeBeforeTime] using
        (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
          adm.toDeliveryWellFormed (Protocol.vote_time S.E s) v)
    have hsourceAgreePre:= derivedStateAgrees_depReachable
      S.E S.hc S.cfg (S.node (S.E.proposer s)) sourcePre hsourceDep
    have htargetAgreePre:= derivedStateAgrees_depReachable
      S.E S.hc S.cfg (S.node v) targetPre htargetDep
    have hsourceAgree: DerivedStateAgrees S.E S.cfg source:= by
      intro Z hZT
      simpa only [source, proposerDutyStore, Proofs.Optimistic.tickStore, sourcePre]
        using hsourceAgreePre Z hZT
    have htargetAgree: DerivedStateAgrees S.E S.cfg target:= by
      intro Z hZT
      simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, targetPre] using htargetAgreePre Z hZT
    have hsourceReach:= Proofs.Bridges.reachableStore_of_depReachableStore
      S.E S.hc S.cfg (S.node (S.E.proposer s)) hsourceDep
    have hFJPre: Block.Preceq sourcePre.F sourcePre.J:=
      finalizedPrecedesJustifiedInvariant S.E S.hc S.cfg
        (S.node (S.E.proposer s)) sourcePre hsourceReach
    have hFJ: Block.Preceq source.F source.J:= by
      simpa only [source, proposerDutyStore, Proofs.Optimistic.tickStore, sourcePre]
        using hFJPre
    have hrootAnchor: Block.Preceq
        (Protocol.get_fg_root source.toHealing.toFG)
        (Proofs.Optimistic.healAnchor S.E S.hc source.toHealing):=
      StoreFinality.get_fg_root_preceq_get_sg_root S.E S.hc source
    have hrootC: Block.Preceq
        (Protocol.get_fg_root source.toHealing.toFG) C:=
      Block.preceq_trans hrootAnchor hanchorC
    have hFC: Block.Preceq source.F C:=
      Block.preceq_trans
        (Proofs.Records.preceq_get_fg_root_of_F (st:= source.toHealing.toFG) hFJ)
        hrootC
    change C ∈ Protocol.get_filtered_block_tree source.toHealing.toFG
    simp only [Protocol.get_filtered_block_tree,
      Protocol.get_filtered_block_tree_from,
      Protocol.viable_tree, Protocol.finalized_descendants,
      Protocol.viable, Finset.mem_filter, decide_eq_true_eq]
    rcases hviability with hthreshold | hpivotFloor
    · have hheight: source.h_max - 1 ≤ (source.σ W).h:= by
        calc
          source.h_max - 1 ≤ target.h_max - 1:= by
            simpa only [source, target] using hthreshold
          _ ≤ (target.σ W).h:= hheightTarget
          _ = (derived_state S.E S.cfg W).h:= by
            rw [htargetAgree W hWT]
          _ = (source.σ W).h:= by
            rw [hsourceAgree W hWTsource]
      exact ⟨⟨⟨hCTsource, hFC⟩, W, hWTsource, hCW, hheight⟩, hrootC⟩
    · have hpivotC: Block.Preceq pivot C:=
        Block.preceq_trans hpivotX hXC
      have hheight: source.h_max - 1 ≤ (source.σ C).h:= by
        calc
          source.h_max - 1 ≤ (derived_state S.E S.cfg pivot).h:= by
            simpa only [source] using hpivotFloor
          _ ≤ (derived_state S.E S.cfg C).h:=
            Protocol.derived_h_mono S.E S.cfg hpivotC
          _ = (source.σ C).h:= by rw [hsourceAgree C hCTsource]
      exact ⟨⟨⟨hCTsource, hFC⟩, C, hCTsource,
        Block.preceq_self C, hheight⟩, hrootC⟩

/-- A common exact-height block pins the honest proposal and vote duty
frontiers to the same public no-progress cap. -/
theorem proposerDutyStore_hMax_eq_voteDutyStore_of_commonExactHeightCap
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (s: Slot) (hprop: S.E.proposer s ∈ rho.honest)
    {v: V} (hv: v ∈ rho.honest) {B: Block V} {K: Height}
    (hBsource: B ∈ (proposerDutyStore S rho s).T)
    (hBtarget: B ∈ (Proofs.Optimistic.voteDutyStore S rho v s).T)
    (hBheight: (derived_state S.E S.cfg B).h = K)
    (hcap: honestHMaxAt S rho (Protocol.vote_time S.E s) ≤ K):
    (proposerDutyStore S rho s).h_max =
      (Proofs.Optimistic.voteDutyStore S rho v s).h_max:= by
  let source:= proposerDutyStore S rho s
  let target:= Proofs.Optimistic.voteDutyStore S rho v s
  let sourcePre:= rho.storeBeforeTime S (S.E.proposer s)
    (Protocol.proposal_time S.E s)
  let targetPre:= rho.storeBeforeTime S v (Protocol.vote_time S.E s)
  have hsourceDep: DepReachableStore S.E S.hc S.cfg
      (S.node (S.E.proposer s)) sourcePre:= by
    simpa only [sourcePre, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed (Protocol.proposal_time S.E s)
          (S.E.proposer s))
  have htargetDep: DepReachableStore S.E S.hc S.cfg
      (S.node v) targetPre:= by
    simpa only [targetPre, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed (Protocol.vote_time S.E s) v)
  have hsourceAgree: DerivedStateAgrees S.E S.cfg sourcePre:=
    derivedStateAgrees_depReachable
      S.E S.hc S.cfg (S.node (S.E.proposer s)) sourcePre hsourceDep
  have htargetAgree: DerivedStateAgrees S.E S.cfg targetPre:=
    derivedStateAgrees_depReachable
      S.E S.hc S.cfg (S.node v) targetPre htargetDep
  have hsourceTree: TreeHeightsLeHMax sourcePre:=
    treeHeightsLeHMax_depReachable
      S.E S.hc S.cfg (S.node (S.E.proposer s)) hsourceDep
  have htargetTree: TreeHeightsLeHMax targetPre:=
    treeHeightsLeHMax_depReachable
      S.E S.hc S.cfg (S.node v) htargetDep
  have hBsourcePre: B ∈ sourcePre.T:= by
    simpa only [source, proposerDutyStore, Proofs.Optimistic.tickStore, sourcePre]
      using hBsource
  have hBtargetPre: B ∈ targetPre.T:= by
    simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, targetPre] using hBtarget
  have hsourceLowerPre: K ≤ sourcePre.h_max:= by
    rw [← hBheight, ← hsourceAgree B hBsourcePre]
    exact hsourceTree B hBsourcePre
  have htargetLowerPre: K ≤ targetPre.h_max:= by
    rw [← hBheight, ← htargetAgree B hBtargetPre]
    exact htargetTree B hBtargetPre
  have hproposalVote:
      honestHMaxAt S rho (Protocol.proposal_time S.E s) ≤
        honestHMaxAt S rho (Protocol.vote_time S.E s):=
    honestHMaxAt_mono S adm.toScheduleWellFormed
      (le_of_lt (Protocol.proposal_time_lt_vote_time S.E s))
  have hsourceUpperPre: sourcePre.h_max ≤ K:= by
    simpa only [sourcePre] using
      (storeBeforeTime_hMax_le_storeAt S adm.toScheduleWellFormed
        (S.E.proposer s) (Protocol.proposal_time S.E s)).trans
          ((localHMax_le_honestHMaxAt S rho
            (Protocol.proposal_time S.E s) hprop).trans
              (hproposalVote.trans hcap))
  have htargetUpperPre: targetPre.h_max ≤ K:= by
    simpa only [targetPre] using
      (storeBeforeTime_hMax_le_storeAt S adm.toScheduleWellFormed
        v (Protocol.vote_time S.E s)).trans
          ((localHMax_le_honestHMaxAt S rho
            (Protocol.vote_time S.E s) hv).trans hcap)
  have hsourceLower: K ≤ source.h_max:= by
    simpa only [source, proposerDutyStore, Proofs.Optimistic.tickStore, sourcePre]
      using hsourceLowerPre
  have hsourceUpper: source.h_max ≤ K:= by
    simpa only [source, proposerDutyStore, Proofs.Optimistic.tickStore, sourcePre]
      using hsourceUpperPre
  have htargetLower: K ≤ target.h_max:= by
    simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, targetPre] using htargetLowerPre
  have htargetUpper: target.h_max ≤ K:= by
    simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, targetPre] using htargetUpperPre
  change source.h_max = target.h_max
  exact (Nat.le_antisymm hsourceUpper hsourceLower).trans
    (Nat.le_antisymm htargetUpper htargetLower).symm

/-- Candidate and anchor inputs shared by fixed and moving-frontier suffix
comparisons. -/
structure FrozenProposalSuffixCoreInputs
    (S: Setup V) (rho: Run V) (s: Slot)
    (pivot: Block V) (v: V): Prop where
  sourceAnchor: Block.Preceq
    (Proofs.Optimistic.healAnchor S.E S.hc
      (proposerDutyStore S rho s).toHealing) pivot
  pivotTarget: pivot ∈ Protocol.get_filtered_block_tree
    (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.toFG
  proposalCandidate: proposedBlock S rho s ∈
    Proofs.Optimistic.voter_candidate_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho v s).toHealing
  pivotAnchorCompatible: Block.compatible
    (Proofs.Optimistic.healAnchor S.E S.hc
      (Proofs.Optimistic.voteDutyStore S rho v s).toHealing) pivot = true
  proposalAnchorCompatible: Block.compatible
    (Proofs.Optimistic.healAnchor S.E S.hc
      (Proofs.Optimistic.voteDutyStore S rho v s).toHealing)
    (proposedBlock S rho s) = true

/-- Exact local inputs for the frozen suffix comparison under a no-rise window. -/
structure FrozenProposalSuffixInputs
    (S: Setup V) (rho: Run V) (s: Slot)
    (pivot: Block V) (v: V): Prop
    extends FrozenProposalSuffixCoreInputs S rho s pivot v where
  sameHMax: (proposerDutyStore S rho s).h_max =
    (Proofs.Optimistic.voteDutyStore S rho v s).h_max

/-- Frozen proposal inputs for a moving frontier. The pivot is inside the
viability band of both duty stores. These two concrete height facts replace
the fixed-window frontier equality. -/
structure FrozenProposalSuffixBandInputs
    (S: Setup V) (rho: Run V) (s: Slot)
    (pivot: Block V) (v: V): Prop
    extends FrozenProposalSuffixCoreInputs S rho s pivot v where
  sourceBand: (proposerDutyStore S rho s).h_max - 1 ≤
    (derived_state S.E S.cfg pivot).h
  targetBand: (Proofs.Optimistic.voteDutyStore S rho v s).h_max - 1 ≤
    (derived_state S.E S.cfg pivot).h

/-- Recovery-cap reflection supplies every frozen suffix input once the common
exact-height pivot pins both duty-store frontiers. -/
theorem frozenProposalSuffixInputs_of_capReflection
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {s: Slot} {pivot: Block V} {floor: Height}
    (hsource: RecoveryProposalCapSourceInputs S rho s pivot floor)
    {v: V} (hv: v ∈ rho.honest)
    (hreflection:
      RecoveryProposalCapReflectionInputs S rho s pivot floor v)
    (hsourceAnchor: Block.Preceq
      (Proofs.Optimistic.healAnchor S.E S.hc
        (proposerDutyStore S rho s).toHealing) pivot)
    (hpivotProposal: Block.Preceq pivot (proposedBlock S rho s))
    (hpivotHeight: (derived_state S.E S.cfg pivot).h = floor)
    (hcap: honestHMaxAt S rho (Protocol.vote_time S.E s) ≤ floor):
    FrozenProposalSuffixInputs S rho s pivot v:= by
  let target:= Proofs.Optimistic.voteDutyStore S rho v s
  let targetPre:=
    rho.storeBeforeTime S v (Protocol.vote_time S.E s)
  have hproposalFiltered: proposedBlock S rho s ∈
      Protocol.get_filtered_block_tree target.toHealing.toFG:=
    frozenVoterCandidateTree_subset_filtered S.E target.toHealing
      (by simpa only [target] using hreflection.candidate)
  have hrootPivot: Block.Preceq
      (Protocol.get_fg_root target.toHealing.toFG) pivot:=
    Block.preceq_trans
      (StoreFinality.get_fg_root_preceq_get_sg_root S.E S.hc target)
      (by simpa only [target] using hreflection.targetAnchor)
  have htargetDep: DepReachableStore S.E S.hc S.cfg
      (S.node v) targetPre:= by
    simpa only [targetPre, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed (Protocol.vote_time S.E s) v)
  have htargetFJPre: Block.Preceq targetPre.F targetPre.J:=
    finalizedPrecedesJustifiedInvariant S.E S.hc S.cfg
      (S.node v) targetPre
      (Proofs.Bridges.reachableStore_of_depReachableStore
        S.E S.hc S.cfg (S.node v) htargetDep)
  have htargetFJ: Block.Preceq target.F target.J:= by
    simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, targetPre] using htargetFJPre
  have hpivotTarget: pivot ∈
      Protocol.get_filtered_block_tree target.toHealing.toFG:=
    Proofs.Records.mem_filtered_of_preceq
      (st:= target.toHealing.toFG)
      (by simpa only [Protocol.Store.toHealing] using htargetFJ)
      hproposalFiltered
      (by simpa only [target] using hreflection.pivotProcessed)
      hpivotProposal hrootPivot
  refine
    { sourceAnchor:= hsourceAnchor
      pivotTarget:= by simpa only [target] using hpivotTarget
      proposalCandidate:= hreflection.candidate
      pivotAnchorCompatible:=
        Block.compatible_of_preceq_common hreflection.targetAnchor
          (Block.preceq_self pivot)
      proposalAnchorCompatible:=
        Block.compatible_of_preceq_common
          (Block.preceq_trans hreflection.targetAnchor hpivotProposal)
          (Block.preceq_self (proposedBlock S rho s))
      sameHMax:= ?_ }
  exact proposerDutyStore_hMax_eq_voteDutyStore_of_commonExactHeightCap
    S adm s hsource.proposer hv hsource.pivotProcessed
      hreflection.pivotProcessed hpivotHeight hcap

/-- Raw processed membership and a common exact-height pivot reconstruct the
frozen voter candidate directly, without a recovery-cap reflection record.

Target pivot membership is not a premise: parent closure derives it from the
processed proposal and `pivot ⪯ proposedBlock`. -/
theorem frozenProposalSuffixInputs_of_commonExactHeightCap
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {s: Slot} (hprop: S.E.proposer s ∈ rho.honest)
    {v: V} (hv: v ∈ rho.honest)
    {pivot: Block V} {floor: Height}
    (hpivotSource: pivot ∈ (proposerDutyStore S rho s).T)
    (hproposalTarget: proposedBlock S rho s ∈
      (Proofs.Optimistic.voteDutyStore S rho v s).T)
    (hpivotHeight: (derived_state S.E S.cfg pivot).h = floor)
    (hcap: honestHMaxAt S rho (Protocol.vote_time S.E s) ≤ floor)
    (hsourceAnchor: Block.Preceq
      (Proofs.Optimistic.healAnchor S.E S.hc
        (proposerDutyStore S rho s).toHealing) pivot)
    (hrootPivot: Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.toFG) pivot)
    (hpivotProposal: Block.Preceq pivot (proposedBlock S rho s))
    (hpivotAnchorCompatible: Block.compatible
      (Proofs.Optimistic.healAnchor S.E S.hc
        (Proofs.Optimistic.voteDutyStore S rho v s).toHealing) pivot = true)
    (hproposalAnchorCompatible: Block.compatible
      (Proofs.Optimistic.healAnchor S.E S.hc
        (Proofs.Optimistic.voteDutyStore S rho v s).toHealing)
      (proposedBlock S rho s) = true):
    FrozenProposalSuffixInputs S rho s pivot v:= by
  let target:= Proofs.Optimistic.voteDutyStore S rho v s
  let targetPre:=
    rho.storeBeforeTime S v (Protocol.vote_time S.E s)
  have htargetDep: DepReachableStore S.E S.hc S.cfg
      (S.node v) targetPre:= by
    simpa only [targetPre, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed (Protocol.vote_time S.E s) v)
  have htargetReach:=
    Proofs.Bridges.reachableStore_of_depReachableStore
      S.E S.hc S.cfg (S.node v) htargetDep
  have htargetParentClosed: ParentClosed targetPre:=
    parentClosed_depReachable S.E S.hc S.cfg (S.node v) targetPre htargetDep
  have htargetAgree: DerivedStateAgrees S.E S.cfg targetPre:=
    derivedStateAgrees_depReachable
      S.E S.hc S.cfg (S.node v) targetPre htargetDep
  have htargetTree: TreeHeightsLeHMax targetPre:=
    treeHeightsLeHMax_depReachable
      S.E S.hc S.cfg (S.node v) htargetDep
  have htargetFJPre: Block.Preceq targetPre.F targetPre.J:=
    finalizedPrecedesJustifiedInvariant
      S.E S.hc S.cfg (S.node v) targetPre htargetReach
  have hproposalTargetPre: proposedBlock S rho s ∈ targetPre.T:= by
    simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, targetPre] using hproposalTarget
  have hpivotTargetPre: pivot ∈ targetPre.T:=
    Proofs.Records.mem_of_preceq ((parentClosed_iff targetPre).mp
      htargetParentClosed).2 pivot (proposedBlock S rho s)
        hproposalTargetPre hpivotProposal
  have hpivotTarget: pivot ∈ target.T:= by
    simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, targetPre] using hpivotTargetPre
  have htargetLower: floor ≤ targetPre.h_max:= by
    rw [← hpivotHeight, ← htargetAgree pivot hpivotTargetPre]
    exact htargetTree pivot hpivotTargetPre
  have htargetUpper: targetPre.h_max ≤ floor:= by
    simpa only [targetPre] using
      (storeBeforeTime_hMax_le_storeAt S adm.toScheduleWellFormed
        v (Protocol.vote_time S.E s)).trans
          ((localHMax_le_honestHMaxAt S rho
            (Protocol.vote_time S.E s) hv).trans hcap)
  have htargetMaxPre: targetPre.h_max = floor:=
    Nat.le_antisymm htargetUpper htargetLower
  have htargetMax: target.h_max = floor:= by
    simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, targetPre] using htargetMaxPre
  have hproposalAgree:
      (target.σ (proposedBlock S rho s)).h =
        (derived_state S.E S.cfg (proposedBlock S rho s)).h:= by
    have hagree:= congrArg (fun st => st.h)
      (htargetAgree (proposedBlock S rho s) hproposalTargetPre)
    simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, targetPre] using hagree
  have hproposalHeight: floor ≤
      (target.σ (proposedBlock S rho s)).h:= by
    calc
      floor = (derived_state S.E S.cfg pivot).h:= hpivotHeight.symm
      _ ≤ (derived_state S.E S.cfg (proposedBlock S rho s)).h:=
        Protocol.derived_h_mono S.E S.cfg hpivotProposal
      _ = (target.σ (proposedBlock S rho s)).h:= hproposalAgree.symm
  have htargetSlot: target.toHealing.s = s:= by
    simpa only [target, Proofs.Optimistic.toHealing_slot] using
      Proofs.Optimistic.voteDutyStore_slot S rho v s
  have hproposalProcessed: proposedBlock S rho s ∈
      Protocol.voter_processed_block_tree S.E
        target.toHealing.toFG.toSG.toGoldfishStore target.toHealing.s:= by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    refine ⟨?_, Or.inr ?_⟩
    · simpa only [target, Protocol.Store.toHealing] using hproposalTarget
    · refine ⟨proposedBlock S rho s, ?_, Block.preceq_self _⟩
      exact ⟨by simpa only [target, Protocol.Store.toHealing] using
          hproposalTarget,
        by simp only [proposedBlock_slot, htargetSlot]⟩
  have hrootProposal: Block.Preceq
      (Protocol.get_fg_root target.toHealing.toFG)
      (proposedBlock S rho s):=
    Block.preceq_trans (by simpa only [target] using hrootPivot)
      hpivotProposal
  have htargetFJ: Block.Preceq target.F target.J:= by
    simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, targetPre] using htargetFJPre
  have hfinalizedProposal:
      Block.Preceq target.F (proposedBlock S rho s):=
    Block.preceq_trans
      (Proofs.Records.preceq_get_fg_root_of_F
        (st:= target.toHealing.toFG)
        (by simpa only [Protocol.Store.toHealing] using htargetFJ))
      hrootProposal
  have hproposalFrontier: target.h_max - 1 ≤
      (target.σ (proposedBlock S rho s)).h:= by
    rw [htargetMax]
    exact (Nat.sub_le floor 1).trans hproposalHeight
  have hproposalCandidate: proposedBlock S rho s ∈
      Proofs.Optimistic.voter_candidate_tree S.E target.toHealing:= by
    simp only [Proofs.Optimistic.voter_candidate_tree,
      Protocol.get_filtered_block_tree_from,
      Protocol.viable_tree, Protocol.finalized_descendants,
      Protocol.viable, Finset.mem_filter, decide_eq_true_eq,
      Protocol.Store.toHealing]
    exact ⟨⟨⟨hproposalProcessed, hfinalizedProposal⟩,
      proposedBlock S rho s, hproposalProcessed, Block.preceq_self _,
      hproposalFrontier⟩, hrootProposal⟩
  have hproposalFiltered: proposedBlock S rho s ∈
      Protocol.get_filtered_block_tree target.toHealing.toFG:=
    frozenVoterCandidateTree_subset_filtered S.E target.toHealing
      hproposalCandidate
  have hpivotFiltered: pivot ∈
      Protocol.get_filtered_block_tree target.toHealing.toFG:=
    Proofs.Records.mem_filtered_of_preceq
      (st:= target.toHealing.toFG)
      (by simpa only [Protocol.Store.toHealing] using htargetFJ)
      hproposalFiltered hpivotTarget hpivotProposal
      (by simpa only [target] using hrootPivot)
  exact
    { sourceAnchor:= hsourceAnchor
      pivotTarget:= by simpa only [target] using hpivotFiltered
      proposalCandidate:= by simpa only [target] using hproposalCandidate
      pivotAnchorCompatible:= hpivotAnchorCompatible
      proposalAnchorCompatible:= hproposalAnchorCompatible
      sameHMax:=
        proposerDutyStore_hMax_eq_voteDutyStore_of_commonExactHeightCap
          S adm s hprop hv hpivotSource
            (by simpa only [target] using hpivotTarget)
            hpivotHeight hcap }

/-- Common proof of the frozen suffix transfer. The frontier relation is
either exact equality or two concrete pivot-band bounds. -/
private theorem proposalPivotSuffixTransfer_of_frozenProposalCore
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {s: Slot} (hs: 0 < s)
    (hpost: S.E.t_GST ≤ Protocol.proposal_time S.E (s - 1))
    (hprop: S.E.proposer s ∈ rho.honest)
    {v: V} (hv: v ∈ rho.honest)
    (hvoteHor: Protocol.vote_time S.E s ≤ rho.horizon)
    {pivot: Block V}
    (h: FrozenProposalSuffixCoreInputs S rho s pivot v)
    (hfrontier:
      (proposerDutyStore S rho s).h_max =
          (Proofs.Optimistic.voteDutyStore S rho v s).h_max ∨
        ((proposerDutyStore S rho s).h_max - 1 ≤
            (derived_state S.E S.cfg pivot).h ∧
          (Proofs.Optimistic.voteDutyStore S rho v s).h_max - 1 ≤
            (derived_state S.E S.cfg pivot).h)):
    ProposalPivotSuffixTransfer S rho s pivot v:= by
  let source:= proposerDutyStore S rho s
  let target:= Proofs.Optimistic.voteDutyStore S rho v s
  have hproposalFull: proposedBlock S rho s ∈
      Protocol.get_filtered_block_tree target.toHealing.toFG:=
    frozenVoterCandidateTree_subset_filtered S.E target.toHealing
      (by simpa only [target] using h.proposalCandidate)
  have hproposalT: proposedBlock S rho s ∈ target.T:=
    Proofs.Records.get_filtered_block_tree_subset target.toHealing.toFG hproposalFull
  have hproposalHor: Protocol.proposal_time S.E s ≤ rho.horizon:=
    le_trans (le_of_lt (Protocol.proposal_time_lt_vote_time S.E s))
      hvoteHor
  have hrawExtra:= voter_raw_extra_equivocates_proposal_afterGST
    S adm hs hpost hprop hv hproposalHor
      (by simpa only [target] using hproposalFull)
  refine { persist:= ?_, reflect:= ?_ }
  · intro X C hpivotX _hXparent _hXne hstep hCparent
    have hchild:= ghost_step_child hstep
    have hparent: C.parent? = some X:= hchild.2.1
    have hXC: Block.Preceq X C:= preceq_of_parent? hparent
    have hCP: Block.Preceq C (proposedBlock S rho s):=
      Block.preceq_trans hCparent
        (proposedParent_preceq_proposedBlock S rho s)
    have hCtargetFrozen:= voterCandidate_above_fullPivot S adm
      (by simpa only [target] using h.proposalCandidate)
      (by simpa only [target] using h.pivotTarget)
      (Block.preceq_trans hpivotX hXC) hCP
    have hCne: C ≠ proposedBlock S rho s:= by
      intro heq
      have hproposalParent: Block.Preceq (proposedBlock S rho s)
          (proposedParent S rho s):= by simpa only [← heq] using hCparent
      have hparentProposal: Block.Preceq (proposedParent S rho s)
          (proposedBlock S rho s):=
        proposedParent_preceq_proposedBlock S rho s
      have heq':= Block.preceq_antisymm hproposalParent hparentProposal
      have hpar:= proposedBlock_parent S rho s
      rw [heq'] at hpar
      have hdepth:= depth_of_parent? hpar
      omega
    have hCtarget: C ∈ proposalWalkTargetTree S rho s v:= by
      simp only [proposalWalkTargetTree]
      exact Finset.mem_erase.mpr ⟨hCne, hCtargetFrozen⟩
    have hCsource: C ∈ proposalWalkSourceTree S rho s:= hchild.1
    have hCfullTarget: C ∈ Protocol.get_filtered_block_tree
        target.toHealing.toFG:=
      frozenVoterCandidateTree_subset_filtered S.E target.toHealing hCtargetFrozen
    have hsourceT: C ∈ source.T:=
      Proofs.Records.get_filtered_block_tree_subset source.toHealing.toFG
        (by simpa only [proposalWalkSourceTree, source] using hCsource)
    have htargetT: C ∈ target.T:=
      Proofs.Records.get_filtered_block_tree_subset target.toHealing.toFG hCfullTarget
    let sourcePre:= rho.storeBeforeTime S (S.E.proposer s)
      (Protocol.proposal_time S.E s)
    let targetPre:= rho.storeBeforeTime S v (Protocol.vote_time S.E s)
    have hsourceDep: DepReachableStore S.E S.hc S.cfg
        (S.node (S.E.proposer s)) sourcePre:= by
      simpa only [sourcePre, Run.storeBeforeTime] using
        (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
          adm.toDeliveryWellFormed (Protocol.proposal_time S.E s)
            (S.E.proposer s))
    have htargetDep: DepReachableStore S.E S.hc S.cfg
        (S.node v) targetPre:= by
      simpa only [targetPre, Run.storeBeforeTime] using
        (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
          adm.toDeliveryWellFormed (Protocol.vote_time S.E s) v)
    have hsourceAgreePre:= derivedStateAgrees_depReachable
      S.E S.hc S.cfg (S.node (S.E.proposer s)) sourcePre hsourceDep
    have htargetAgreePre:= derivedStateAgrees_depReachable
      S.E S.hc S.cfg (S.node v) targetPre htargetDep
    have hsourceAgree: DerivedStateAgrees S.E S.cfg source:= by
      intro Z hZT
      simpa only [source, proposerDutyStore, Proofs.Optimistic.tickStore, sourcePre]
        using hsourceAgreePre Z hZT
    have htargetAgree: DerivedStateAgrees S.E S.cfg target:= by
      intro Z hZT
      simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, targetPre] using htargetAgreePre Z hZT
    have hsourcePcPre: ParentClosed sourcePre:=
      parentClosed_depReachable S.E S.hc S.cfg
        (S.node (S.E.proposer s)) sourcePre hsourceDep
    have htargetPcPre: ParentClosed targetPre:=
      parentClosed_depReachable S.E S.hc S.cfg (S.node v) targetPre htargetDep
    have hsourcePc: ParentClosed source:= by
      simpa only [source, proposerDutyStore, Proofs.Optimistic.tickStore, sourcePre]
        using hsourcePcPre
    have htargetPc: ParentClosed target:= by
      simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, targetPre] using htargetPcPre
    have hsourceParentT: C.parent ∈ source.T:=
      Proofs.Records.mem_of_preceq ((parentClosed_iff source).mp hsourcePc).2
        C.parent C hsourceT (preceq_parent C)
    have htargetParentT: C.parent ∈ target.T:=
      Proofs.Records.mem_of_preceq ((parentClosed_iff target).mp htargetPc).2
        C.parent C htargetT (preceq_parent C)
    have hsourceSlot: source.s = s:= by
      simp only [source, proposerDutyStore, Proofs.Optimistic.tickStore,
        Proofs.Optimistic.slotOf_proposal_time]
    have htargetSlot: target.s = s:= by
      simp only [target, Proofs.Optimistic.voteDutyStore_slot]
    have hnotCurrent: C.slot ≠ source.s:= by
      rw [hsourceSlot]
      exact Nat.ne_of_lt (block_slot_lt_of_mem_before_proposal S adm hs (by
        simpa only [source, proposerDutyStore, Proofs.Optimistic.tickStore] using
          hsourceT))
    have heligSource:
        (source.σ C.parent).h < source.h_max - 1 ∨
        Protocol.voters_count S.E
            (Protocol.proposer_view source.toHealing.toFG.toSG.toGoldfishStore source.s).toFinset
            (source.s - 1) <
          2 * Protocol.goldfish_score S.E source.T
            (Protocol.proposer_view source.toHealing.toFG.toSG.toGoldfishStore source.s).toFinset
            (Protocol.proposer_support_view source.toHealing.toFG.toSG.toGoldfishStore source.s).toFinset
            (source.s - 1) C ∨
        C.slot = source.s:= by
      have heligibleSource:= hchild.2.2
      change Protocol.goldfish_eligible S.E source.σ source.h_max
        source.T source.s
        (Protocol.proposer_view source.toHealing.toFG.toSG.toGoldfishStore source.s).toFinset
        (Protocol.proposer_support_view source.toHealing.toFG.toSG.toGoldfishStore source.s).toFinset
        (source.s - 1) C = true at heligibleSource
      exact (Proofs.Optimistic.goldfish_eligible_iff S.E source.σ source.h_max
        source.T source.s
        (Protocol.proposer_view source.toHealing.toFG.toSG.toGoldfishStore source.s).toFinset
        (Protocol.proposer_support_view source.toHealing.toFG.toSG.toGoldfishStore source.s).toFinset
        (source.s - 1) C).mp heligibleSource
    refine ⟨hCtarget, ?_⟩
    rw [proposalWalkTargetEligible, Proofs.Optimistic.goldfish_eligible_iff]
    rcases heligSource with hlow | hmajority | hcurrent
    · rcases hfrontier with hmaxEq | hband
      · exact Or.inl (by
          calc
            (target.σ C.parent).h =
                (derived_state S.E S.cfg C.parent).h:= by
              rw [htargetAgree C.parent htargetParentT]
            _ = (source.σ C.parent).h:= by
              rw [hsourceAgree C.parent hsourceParentT]
            _ < source.h_max - 1:= hlow
            _ = target.h_max - 1:= by rw [hmaxEq])
      · have hpivotParent: Block.Preceq pivot C.parent:= by
          rw [parent_eq_of_parent? hparent]
          exact hpivotX
        have hfloor: source.h_max - 1 ≤ (source.σ C.parent).h:= by
          calc
            source.h_max - 1 ≤ (derived_state S.E S.cfg pivot).h:= by
              simpa only [source] using hband.1
            _ ≤ (derived_state S.E S.cfg C.parent).h:=
              Protocol.derived_h_mono S.E S.cfg hpivotParent
            _ = (source.σ C.parent).h:= by
              rw [hsourceAgree C.parent hsourceParentT]
        exact False.elim ((not_lt_of_ge hfloor) hlow)
    · right
      left
      have hbridge:=
        candidateScorePreservingViewExtension_proposedBlock_afterGST_of_candidates
          S adm hs hpost hprop hv hvoteHor
            (by simpa only [target] using hproposalFull) hrawExtra
            (by simpa only [proposalWalkSourceTree, source] using hCsource)
            hCfullTarget
      have hcount:= hbridge.voters_count_eq S.E (s - 1)
      have hscore:= hbridge.goldfish_score_eq S.E (s - 1)
      rw [hsourceSlot] at hmajority
      rw [htargetSlot]
      dsimp only [source] at hmajority
      rw [← Protocol.proposedBlock_gf_votes S rho s,
        ← Protocol.proposedBlock_gf_support_votes S rho s] at hmajority
      change Protocol.voters_count S.E
          (Protocol.voter_view S.E target.toHealing.toFG.toSG.toGoldfishStore s) (s - 1) <
        2 * Protocol.goldfish_score S.E target.T
          (Protocol.voter_view S.E target.toHealing.toFG.toSG.toGoldfishStore s)
          (Protocol.voter_support_view S.E target.toHealing.toFG.toSG.toGoldfishStore s)
          (s - 1) C
      rw [← hcount, ← hscore]
      exact hmajority
    · exact False.elim (hnotCurrent hcurrent)
  · intro X C hpivotX _hXparent hCtarget hparent heligible
    have hCsource:= targetChild_mem_sourceTree_of_frozenProposal
      S adm hs hpost hprop hv hproposalHor h.sourceAnchor
        h.proposalCandidate (by
          rcases hfrontier with hmaxEq | hband
          · exact Or.inl (by rw [hmaxEq])
          · exact Or.inr hband.1)
          hpivotX hCtarget hparent
    have htargetErase: C ∈
        (Proofs.Optimistic.voter_candidate_tree S.E target.toHealing).erase
          (proposedBlock S rho s):= by
      simpa only [proposalWalkTargetTree, target] using hCtarget
    have hCne: C ≠ proposedBlock S rho s:=
      (Finset.mem_erase.mp htargetErase).1
    have hCfrozen:= (Finset.mem_erase.mp htargetErase).2
    have hCfull: C ∈ Protocol.get_filtered_block_tree
        target.toHealing.toFG:=
      frozenVoterCandidateTree_subset_filtered S.E target.toHealing hCfrozen
    have hsourceFull: C ∈ Protocol.get_filtered_block_tree
        source.toHealing.toFG:= by
      simpa only [proposalWalkSourceTree, source] using hCsource
    have hsourceT: C ∈ source.T:=
      Proofs.Records.get_filtered_block_tree_subset source.toHealing.toFG hsourceFull
    have htargetT: C ∈ target.T:=
      Proofs.Records.get_filtered_block_tree_subset target.toHealing.toFG hCfull
    let sourcePre:= rho.storeBeforeTime S (S.E.proposer s)
      (Protocol.proposal_time S.E s)
    let targetPre:= rho.storeBeforeTime S v (Protocol.vote_time S.E s)
    have hsourceDep: DepReachableStore S.E S.hc S.cfg
        (S.node (S.E.proposer s)) sourcePre:= by
      simpa only [sourcePre, Run.storeBeforeTime] using
        (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
          adm.toDeliveryWellFormed (Protocol.proposal_time S.E s)
            (S.E.proposer s))
    have htargetDep: DepReachableStore S.E S.hc S.cfg
        (S.node v) targetPre:= by
      simpa only [targetPre, Run.storeBeforeTime] using
        (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
          adm.toDeliveryWellFormed (Protocol.vote_time S.E s) v)
    have hsourceAgreePre:= derivedStateAgrees_depReachable
      S.E S.hc S.cfg (S.node (S.E.proposer s)) sourcePre hsourceDep
    have htargetAgreePre:= derivedStateAgrees_depReachable
      S.E S.hc S.cfg (S.node v) targetPre htargetDep
    have hsourceAgree: DerivedStateAgrees S.E S.cfg source:= by
      intro Z hZT
      simpa only [source, proposerDutyStore, Proofs.Optimistic.tickStore, sourcePre]
        using hsourceAgreePre Z hZT
    have htargetAgree: DerivedStateAgrees S.E S.cfg target:= by
      intro Z hZT
      simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, targetPre] using htargetAgreePre Z hZT
    have hsourcePcPre: ParentClosed sourcePre:=
      parentClosed_depReachable S.E S.hc S.cfg
        (S.node (S.E.proposer s)) sourcePre hsourceDep
    have htargetPcPre: ParentClosed targetPre:=
      parentClosed_depReachable S.E S.hc S.cfg (S.node v) targetPre htargetDep
    have hsourcePc: ParentClosed source:= by
      simpa only [source, proposerDutyStore, Proofs.Optimistic.tickStore, sourcePre]
        using hsourcePcPre
    have htargetPc: ParentClosed target:= by
      simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, targetPre] using htargetPcPre
    have hsourceParentT: C.parent ∈ source.T:=
      Proofs.Records.mem_of_preceq ((parentClosed_iff source).mp hsourcePc).2
        C.parent C hsourceT (preceq_parent C)
    have htargetParentT: C.parent ∈ target.T:=
      Proofs.Records.mem_of_preceq ((parentClosed_iff target).mp htargetPc).2
        C.parent C htargetT (preceq_parent C)
    have hsourceSlot: source.s = s:= by
      simp only [source, proposerDutyStore, Proofs.Optimistic.tickStore,
        Proofs.Optimistic.slotOf_proposal_time]
    have htargetSlot: target.s = s:= by
      simp only [target, Proofs.Optimistic.voteDutyStore_slot]
    have hnotCurrent: C.slot ≠ target.s:= by
      intro hcur
      obtain ⟨n, hn, -⟩:= Proofs.Bridges.stateBeforeTime_eq_stateBefore S
        adm.toScheduleWellFormed (Protocol.vote_time S.E s)
      have hCprefix: C ∈ (rho.stateBefore S n v).st.T:= by
        simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn] using htargetT
      have hPprefix: proposedBlock S rho s ∈
          (rho.stateBefore S n v).st.T:= by
        simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn] using hproposalT
      have hEq:= unique_slot_block_in_store S adm hs hprop
        hCprefix hPprefix (by simpa only [htargetSlot] using hcur)
          (proposedBlock_slot S rho s)
      exact hCne hEq
    have heligTarget:
        (target.σ C.parent).h < target.h_max - 1 ∨
        Protocol.voters_count S.E
            (Protocol.voter_view S.E target.toHealing.toFG.toSG.toGoldfishStore target.s)
            (target.s - 1) <
          2 * Protocol.goldfish_score S.E target.T
            (Protocol.voter_view S.E target.toHealing.toFG.toSG.toGoldfishStore target.s)
            (Protocol.voter_support_view S.E target.toHealing.toFG.toSG.toGoldfishStore target.s)
            (target.s - 1) C ∨
        C.slot = target.s:= by
      change Protocol.goldfish_eligible S.E target.σ target.h_max
        target.T target.s
        (Protocol.voter_view S.E target.toHealing.toFG.toSG.toGoldfishStore target.s)
        (Protocol.voter_support_view S.E target.toHealing.toFG.toSG.toGoldfishStore target.s)
        (target.s - 1) C = true at heligible
      exact (Proofs.Optimistic.goldfish_eligible_iff S.E target.σ target.h_max
        target.T target.s
        (Protocol.voter_view S.E target.toHealing.toFG.toSG.toGoldfishStore target.s)
        (Protocol.voter_support_view S.E target.toHealing.toFG.toSG.toGoldfishStore target.s)
        (target.s - 1) C).mp heligible
    refine ⟨hCsource, ?_⟩
    rw [proposalWalkSourceEligible, Proofs.Optimistic.goldfish_eligible_iff]
    rcases heligTarget with hlow | hmajority | hcurrent
    · rcases hfrontier with hmaxEq | hband
      · exact Or.inl (by
          calc
            (source.σ C.parent).h =
                (derived_state S.E S.cfg C.parent).h:= by
              rw [hsourceAgree C.parent hsourceParentT]
            _ = (target.σ C.parent).h:= by
              rw [htargetAgree C.parent htargetParentT]
            _ < target.h_max - 1:= hlow
            _ = source.h_max - 1:= by rw [hmaxEq])
      · have hpivotParent: Block.Preceq pivot C.parent:= by
          rw [parent_eq_of_parent? hparent]
          exact hpivotX
        have hfloor: target.h_max - 1 ≤ (target.σ C.parent).h:= by
          calc
            target.h_max - 1 ≤ (derived_state S.E S.cfg pivot).h:= by
              simpa only [target] using hband.2
            _ ≤ (derived_state S.E S.cfg C.parent).h:=
              Protocol.derived_h_mono S.E S.cfg hpivotParent
            _ = (target.σ C.parent).h:= by
              rw [htargetAgree C.parent htargetParentT]
        exact False.elim ((not_lt_of_ge hfloor) hlow)
    · right
      left
      have hbridge:=
        candidateScorePreservingViewExtension_proposedBlock_afterGST_of_candidates
          S adm hs hpost hprop hv hvoteHor
            (by simpa only [target] using hproposalFull) hrawExtra
            hsourceFull hCfull
      have hcount:= hbridge.voters_count_eq S.E (s - 1)
      have hscore:= hbridge.goldfish_score_eq S.E (s - 1)
      rw [htargetSlot] at hmajority
      rw [hsourceSlot]
      change Protocol.voters_count S.E
          (Protocol.voter_view S.E target.toHealing.toFG.toSG.toGoldfishStore s) (s - 1) <
        2 * Protocol.goldfish_score S.E target.T
          (Protocol.voter_view S.E target.toHealing.toFG.toSG.toGoldfishStore s)
          (Protocol.voter_support_view S.E target.toHealing.toFG.toSG.toGoldfishStore s)
          (s - 1) C at hmajority
      rw [← Protocol.proposedBlock_gf_votes S rho s,
        ← Protocol.proposedBlock_gf_support_votes S rho s]
      rw [hcount, hscore]
      exact hmajority
    · exact False.elim (hnotCurrent hcurrent)

/-- The current frozen processed-tree semantics and a fixed-height window imply
both directions of the proposal suffix transfer. -/
theorem proposalPivotSuffixTransfer_of_frozenProposalNoRise
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {s: Slot} (hs: 0 < s)
    (hpost: S.E.t_GST ≤ Protocol.proposal_time S.E (s - 1))
    (hprop: S.E.proposer s ∈ rho.honest)
    {v: V} (hv: v ∈ rho.honest)
    (hvoteHor: Protocol.vote_time S.E s ≤ rho.horizon)
    {pivot: Block V}
    (h: FrozenProposalSuffixInputs S rho s pivot v):
    ProposalPivotSuffixTransfer S rho s pivot v:= by
  exact proposalPivotSuffixTransfer_of_frozenProposalCore
    S adm hs hpost hprop hv hvoteHor h.toFrozenProposalSuffixCoreInputs
      (Or.inl h.sameHMax)

/-- The same suffix transfer remains valid during a one-step frontier change
when the common pivot stays in both stores' viability bands. In the low-height
arms, every parent above the pivot is already at the relevant frontier, so the
low-height disjunct is impossible; the majority arms use the frozen snapshot
bridge exactly as in the fixed-frontier proof. -/
theorem proposalPivotSuffixTransfer_of_riseLeOne
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {s: Slot} (hs: 0 < s)
    (hpost: S.E.t_GST ≤ Protocol.proposal_time S.E (s - 1))
    (hprop: S.E.proposer s ∈ rho.honest)
    {v: V} (hv: v ∈ rho.honest)
    (hvoteHor: Protocol.vote_time S.E s ≤ rho.horizon)
    {pivot: Block V}
    (h: FrozenProposalSuffixBandInputs S rho s pivot v):
    ProposalPivotSuffixTransfer S rho s pivot v:= by
  exact proposalPivotSuffixTransfer_of_frozenProposalCore
    S adm hs hpost hprop hv hvoteHor
      h.toFrozenProposalSuffixCoreInputs
      (Or.inr ⟨h.sourceBand, h.targetBand⟩)

/-- A pivot in both live frontier bands transfers the complete proposal walk.
Candidate scores come from the honest proposal snapshot bridge.

Open: `htargetPasses` is the remaining prefix fact. The slot fold must
derive it from the previous honest vote cone before it uses this theorem. -/
theorem proposalWalkTransferred_of_riseLeOne_of_targetPasses
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {s: Slot} (hs: 0 < s)
    (hpost: S.E.t_GST ≤ Protocol.proposal_time S.E (s - 1))
    (hprop: S.E.proposer s ∈ rho.honest)
    {v: V} (hv: v ∈ rho.honest)
    (hvoteHor: Protocol.vote_time S.E s ≤ rho.horizon)
    {pivot: Block V}
    (hpivotParent: Block.Preceq pivot (proposedParent S rho s))
    (htargetPasses: Block.Preceq pivot
      (Protocol.ghost
        (Proofs.Optimistic.healAnchor S.E S.hc
          (Proofs.Optimistic.voteDutyStore S rho v s).toHealing)
        (proposalWalkTargetTree S rho s v)
        (proposalWalkTargetScore S rho s v)
        (proposalWalkTargetEligible S rho s v)))
    (h: FrozenProposalSuffixBandInputs S rho s pivot v):
    ProposalWalkTransferred S rho s
      (proposedBlock S rho s) (proposedParent S rho s) v:= by
  let target:= Proofs.Optimistic.voteDutyStore S rho v s
  have hproposalFull: proposedBlock S rho s ∈
      Protocol.get_filtered_block_tree target.toHealing.toFG:=
    frozenVoterCandidateTree_subset_filtered S.E target.toHealing
      (by simpa only [target] using h.proposalCandidate)
  have hproposalHor: Protocol.proposal_time S.E s ≤ rho.horizon:=
    (le_of_lt (Protocol.proposal_time_lt_vote_time S.E s)).trans hvoteHor
  have hrawExtra:= voter_raw_extra_equivocates_proposal_afterGST
    S adm hs hpost hprop hv hproposalHor
      (by simpa only [target] using hproposalFull)
  have hscore: ∀ C,
      C ∈ proposalWalkSourceTree S rho s →
      C ∈ proposalWalkTargetTree S rho s v →
      proposalWalkTargetScore S rho s v C =
        proposalWalkSourceScore S rho s C:= by
    intro C hCsource hCtarget
    have hCtargetFrozen: C ∈ Proofs.Optimistic.voter_candidate_tree S.E
        target.toHealing:= by
      simpa only [proposalWalkTargetTree, target] using
        Finset.mem_of_mem_erase hCtarget
    have hCtargetFull: C ∈
        Protocol.get_filtered_block_tree target.toHealing.toFG:=
      frozenVoterCandidateTree_subset_filtered S.E target.toHealing
        hCtargetFrozen
    have hbridge:=
      candidateScorePreservingViewExtension_proposedBlock_afterGST_of_candidates
        S adm hs hpost hprop hv hvoteHor
          (by simpa only [target] using hproposalFull) hrawExtra
          (by simpa only [proposalWalkSourceTree] using hCsource)
          (by simpa only [target] using hCtargetFull)
    have hscoreEq:= hbridge.goldfish_score_eq S.E (s - 1)
    have hsourceSlot: (proposerDutyStore S rho s).s = s:= by
      simp only [proposerDutyStore, Proofs.Optimistic.tickStore,
        Proofs.Optimistic.slotOf_proposal_time]
    have htargetSlot: target.s = s:= by
      simpa only [target] using Proofs.Optimistic.voteDutyStore_slot S rho v s
    symm
    simpa only [proposalWalkSourceScore, proposalWalkTargetScore,
      Protocol.proposedBlock_gf_votes,
      Protocol.proposedBlock_gf_support_votes,
      hsourceSlot, htargetSlot, target] using hscoreEq
  exact proposalWalkTransferred_of_frozenCompatiblePivot
    S adm hprop hv h.proposalCandidate h.proposalAnchorCompatible
      h.sourceAnchor hpivotParent htargetPasses
      (proposalPivotSuffixTransfer_of_riseLeOne
        S adm hs hpost hprop hv hvoteHor h) hscore

/-- Assemble the complete Claim-4 frozen-vote record from run-local candidate,
anchor, and fixed-frontier facts. -/
theorem sgOpeningFrozenVoteAt_of_frozenProposalNoRise
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {s: Slot}
    (hpost: S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hprop: S.E.proposer (s + 1) ∈ rho.honest)
    {v: V} (hv: v ∈ rho.honest)
    (hvoteHor: Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    {A: Block V}
    (hAparent: Block.Preceq A (proposedParent S rho (s + 1)))
    (h: FrozenProposalSuffixInputs S rho (s + 1) A v):
    SGOpeningFrozenVoteAt S rho s A v:= by
  let target:= Proofs.Optimistic.voteDutyStore S rho v (s + 1)
  have hAP: Block.Preceq A (proposedBlock S rho (s + 1)):=
    Block.preceq_trans hAparent
      (proposedParent_preceq_proposedBlock S rho (s + 1))
  have hAfrozen:= voterCandidate_above_fullPivot S adm
    (by simpa only [target] using h.proposalCandidate)
    (by simpa only [target] using h.pivotTarget)
    (Block.preceq_self A) hAP
  have hAne: A ≠ proposedBlock S rho (s + 1):= by
    intro heq
    have hPH: Block.Preceq (proposedBlock S rho (s + 1))
        (proposedParent S rho (s + 1)):= by simpa only [← heq] using hAparent
    have hHP:= proposedParent_preceq_proposedBlock
      (S:= S) (rho:= rho) (s:= s + 1)
    have heq':= Block.preceq_antisymm hPH hHP
    have hpar:= proposedBlock_parent S rho (s + 1)
    rw [heq'] at hpar
    have hdepth:= depth_of_parent? hpar
    omega
  have hpivotCandidate: A ∈ proposalWalkTargetTree S rho (s + 1) v:= by
    simp only [proposalWalkTargetTree]
    exact Finset.mem_erase.mpr ⟨hAne, hAfrozen⟩
  have hpivotPath:
      Block.Preceq
          (Proofs.Optimistic.healAnchor S.E S.hc target.toHealing) A →
        ∀ C: Block V,
          Block.Preceq
            (Proofs.Optimistic.healAnchor S.E S.hc target.toHealing) C →
          C ≠ Proofs.Optimistic.healAnchor S.E S.hc target.toHealing →
          Block.Preceq C A →
          C ∈ proposalWalkTargetTree S rho (s + 1) v:= by
    intro _hanchorA C hanchorC hCneAnchor hCA
    have hCfull: C ∈ Protocol.get_filtered_block_tree
        target.toHealing.toFG:= by
      simpa only [target] using
        (votePath_of_candidate S adm
          (by simpa only [target] using h.pivotTarget)
          C (by simpa only [target] using hanchorC)
          (by simpa only [target] using hCneAnchor) hCA)
    have hCP: Block.Preceq C (proposedBlock S rho (s + 1)):=
      Block.preceq_trans hCA hAP
    have hCfrozen:= voterCandidate_above_fullPivot S adm
      (by simpa only [target] using h.proposalCandidate) hCfull
        (Block.preceq_self C) hCP
    have hCne: C ≠ proposedBlock S rho (s + 1):= by
      intro heq
      exact hAne
        (Block.preceq_antisymm (by simpa only [heq] using hCA) hAP).symm
    simp only [proposalWalkTargetTree]
    exact Finset.mem_erase.mpr ⟨hCne, hCfrozen⟩
  have hrawExtra:= voter_raw_extra_equivocates_proposal_afterGST
    S adm (Nat.succ_pos s) (by simpa only [Nat.add_sub_cancel] using hpost)
      hprop hv
      (le_trans
        (le_of_lt (Protocol.proposal_time_lt_vote_time S.E (s + 1)))
        hvoteHor)
      (frozenVoterCandidateTree_subset_filtered S.E target.toHealing
        (by simpa only [target] using h.proposalCandidate))
  exact
    { proposalCandidate:= h.proposalCandidate
      pivotCandidate:= hpivotCandidate
      pivotAnchorCompatible:= h.pivotAnchorCompatible
      proposalAnchorCompatible:= h.proposalAnchorCompatible
      pivotPath:= by simpa only [target] using hpivotPath
      suffix:= proposalPivotSuffixTransfer_of_frozenProposalNoRise
        S adm (Nat.succ_pos s)
          (by simpa only [Nat.add_sub_cancel] using hpost)
          hprop hv hvoteHor h
      rawExtra:= hrawExtra }

/-- Cap-reflection and exact-frontier facts assemble the Claim-4 opening vote
without routing through a lifecycle record. -/
theorem sgOpeningFrozenVoteAt_of_capReflection
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {s: Slot} {A: Block V} {floor: Height}
    (hsource:
      RecoveryProposalCapSourceInputs S rho (s + 1) A floor)
    {v: V} (hv: v ∈ rho.honest)
    (hreflection:
      RecoveryProposalCapReflectionInputs S rho (s + 1) A floor v)
    (hsourceAnchor: Block.Preceq
      (Proofs.Optimistic.healAnchor S.E S.hc
        (proposerDutyStore S rho (s + 1)).toHealing) A)
    (hAparent: Block.Preceq A (proposedParent S rho (s + 1)))
    (hAheight: (derived_state S.E S.cfg A).h = floor)
    (hcap:
      honestHMaxAt S rho (Protocol.vote_time S.E (s + 1)) ≤ floor):
    SGOpeningFrozenVoteAt S rho s A v:= by
  have hAproposal: Block.Preceq A (proposedBlock S rho (s + 1)):=
    Block.preceq_trans hAparent
      (proposedParent_preceq_proposedBlock S rho (s + 1))
  have hfrozen: FrozenProposalSuffixInputs S rho (s + 1) A v:=
    frozenProposalSuffixInputs_of_capReflection
      S adm hsource hv hreflection hsourceAnchor hAproposal hAheight hcap
  exact sgOpeningFrozenVoteAt_of_frozenProposalNoRise
    S adm
      (by simpa only [Nat.add_sub_cancel] using hsource.post)
      hsource.proposer hv hsource.horizon hAparent hfrozen

/-- The direct common-pivot reconstruction feeds the Claim-4 opening-vote
constructor without a recovery-cap reflection record. -/
theorem sgOpeningFrozenVoteAt_of_commonExactHeightCap
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {s: Slot}
    (hpost: S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hprop: S.E.proposer (s + 1) ∈ rho.honest)
    {v: V} (hv: v ∈ rho.honest)
    (hvoteHor: Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    {A: Block V} {floor: Height}
    (hASource: A ∈ (proposerDutyStore S rho (s + 1)).T)
    (hproposalTarget: proposedBlock S rho (s + 1) ∈
      (Proofs.Optimistic.voteDutyStore S rho v (s + 1)).T)
    (hAheight: (derived_state S.E S.cfg A).h = floor)
    (hcap:
      honestHMaxAt S rho (Protocol.vote_time S.E (s + 1)) ≤ floor)
    (hsourceAnchor: Block.Preceq
      (Proofs.Optimistic.healAnchor S.E S.hc
        (proposerDutyStore S rho (s + 1)).toHealing) A)
    (hrootA: Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho v (s + 1)).toHealing.toFG) A)
    (hAparent: Block.Preceq A (proposedParent S rho (s + 1)))
    (hAAnchorCompatible: Block.compatible
      (Proofs.Optimistic.healAnchor S.E S.hc
        (Proofs.Optimistic.voteDutyStore S rho v (s + 1)).toHealing) A = true)
    (hproposalAnchorCompatible: Block.compatible
      (Proofs.Optimistic.healAnchor S.E S.hc
        (Proofs.Optimistic.voteDutyStore S rho v (s + 1)).toHealing)
      (proposedBlock S rho (s + 1)) = true):
    SGOpeningFrozenVoteAt S rho s A v:= by
  have hAproposal: Block.Preceq A (proposedBlock S rho (s + 1)):=
    Block.preceq_trans hAparent
      (proposedParent_preceq_proposedBlock S rho (s + 1))
  have hfrozen: FrozenProposalSuffixInputs S rho (s + 1) A v:=
    frozenProposalSuffixInputs_of_commonExactHeightCap
      S adm hprop hv hASource hproposalTarget hAheight hcap
        hsourceAnchor hrootA hAproposal
        hAAnchorCompatible hproposalAnchorCompatible
  exact sgOpeningFrozenVoteAt_of_frozenProposalNoRise
    S adm hpost hprop hv hvoteHor hAparent hfrozen

 -/

#print axioms frozenVoterCandidateTree_subset_filtered

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
