module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedViability
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.VoteStoreExtends

@[expose] public section

/-!
# The vote-duty head reaches the local band, given an anchor descendant

`SeedViabilityRun.voteDutyHead_height_ge_frontier_sub_one_of_candidate` needs a
full cone bundle (`GoldfishConeVoteInputs`) and an anchor-precedes-candidate
premise to place a viability witness inside the voter's own frozen candidate
tree. Both are more than the band-reach conclusion itself needs: what actually
drives the descent is the existence of *some* processed (frozen-view)
descendant of the voter's anchor that already clears the `h_max - 1` band --
everything else in that bundle is machinery to produce such a descendant from a
run-level cone, not part of what the local Goldfish-walk argument consumes.

This file isolates exactly that hypothesis, on the named runtime. The walk runs
on the prepared vote-duty read `voteDutyRead S rho w (s + 1)`: its erased core
is `voteDutyStore`, its contract anchor is `voterAnchorAt`, its frozen tree is
`voterCandidateTreeAt` and its head is `voterHeadAt`. The "walk blocked inside
the tree" case closes unconditionally
(`voteDuty_parentClosed_agrees_rootInjective`,
`namedFrozenCandidate_child_towards_witness`,
`eligible_child_false_at_ghost_result`); the "walk never left the anchor" case
is exactly where a processed-descendant witness for the anchor is needed, and
`hdesc` supplies it via
`namedAncestorCandidate_of_processedDescendant_and_hMax`.

**Anchor activity.** The anchor is the contract read's anchor, not the plain
`get_sg_root`, so the prior `DepReachableStore` route is replaced by the named
run-level filtered FG-root producer
(`named_fgRoot_mem_filtered_stateBeforeTime`) followed by the frame-contract
step `nodeAnchor_mem_filtered_of_fgRoot_mem_filtered` below (the local twin of
the private `SeedActivityRun.frame_anchor_mem_filtered_of_fgRoot_mem_filtered`,
restated on `nodeAnchor` so no import is added).

**Heights are named.** `derive_named` and `derived_state` differ on the timeout
arm, and the store-level `DerivedStateAgrees` is retired, so neither the
descendant premise nor the head conclusion can be phrased on
`derived_state S.E S.cfg ·` any more. Both are phrased on the prepared read's
own cached chain state, which the named coherence invariant does supply: the
primary form takes a *named* descendant and `derive_named`; the `_sigma`
wrappers take, and conclude on, `(voteDutyStore S rho w (s + 1)).σ ·`, which is
the same number by `Internal.NamedDerivedStateAgrees`.

**Slot form.** `namedFrozenCandidate_child_towards_witness` and
`namedAncestorCandidate_of_processedDescendant_and_hMax` -- the only pieces that
turn a witness into frozen-tree membership -- are both stated at the vote-duty
read of slot `s + 1`, the codebase-wide convention for "the slot after the one
being described". There is no general-`d` (in particular no `d = 0`) version of
either in the tree, so the theorems below are stated at `s + 1` rather than at a
free `d: Slot`.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.PhaseGrades
open Protocol
open Internal.NamedRecoveryRead
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The prepared read's contract anchor is active whenever its FG root is.
Local twin of the private `SeedActivityRun` frame lemma, restated directly on
`nodeAnchor` so that no import has to be added here. -/
private theorem nodeAnchor_mem_filtered_of_fgRoot_mem_filtered
    (S : Setup V) (n : NamedNodeState V) (r : Round)
    (hroot : Protocol.get_fg_root n.st.core.toHealing.toFG ∈
      Protocol.get_filtered_block_tree n.st.core.toHealing.toFG) :
    nodeAnchor S n r ∈
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
                (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).1

/-- The band-reach core: the named head witness, its retained cached chain
state, and the band bound. -/
private theorem voteDutyHead_band_core
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) (s : Slot)
    (hdesc : ∃ C : NamedBlock V,
      Block.Preceq (voterAnchorAt S rho w (s + 1)) C.erase ∧
      RunBlock S rho C ∧
      C.erase ∈ Protocol.voter_processed_block_tree S.E
        (voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
        (voteDutyStore S rho w (s + 1)).toHealing.s ∧
      (voteDutyStore S rho w (s + 1)).h_max ≤
        (derive_named S.E S.cfg C).h + 1) :
    ∃ Hn : NamedBlock V,
      Hn.erase = voterHeadAt S rho w (s + 1) ∧ RunBlock S rho Hn ∧
        (voteDutyStore S rho w (s + 1)).σ (voterHeadAt S rho w (s + 1)) =
          derive_named S.E S.cfg Hn ∧
        (voteDutyStore S rho w (s + 1)).h_max - 1 ≤
          (derive_named S.E S.cfg Hn).h := by
  let read := voteDutyRead S rho w (s + 1)
  let duty := read.st.core
  let tree := voterCandidateTreeAt S rho w (s + 1)
  let A := voterAnchorAt S rho w (s + 1)
  let score := Protocol.goldfish_score S.E duty.T
    (Protocol.voter_view S.E duty.toHealing.toFG.toSG.toGoldfishStore duty.s)
    (Protocol.voter_support_view S.E duty.toHealing.toFG.toSG.toGoldfishStore duty.s)
    (duty.s - 1)
  let eligible := Protocol.goldfish_eligible S.E duty.σ duty.h_max duty.T
    duty.s (Protocol.voter_view S.E duty.toHealing.toFG.toSG.toGoldfishStore duty.s)
    (Protocol.voter_support_view S.E duty.toHealing.toFG.toSG.toGoldfishStore duty.s)
    (duty.s - 1)
  let H := voterHeadAt S rho w (s + 1)
  have hHghost : H = Protocol.ghost A tree score eligible := by
    rfl
  have hfacts := voteDuty_parentClosed_agrees_rootInjective S adm hw (s + 1)
  have htreeT : tree ⊆ duty.T := by
    intro B hB
    have hprocessed := Proofs.Records.get_filtered_block_tree_from_subset
      duty.toHealing.toFG
      (Protocol.voter_processed_block_tree S.E
        duty.toHealing.toFG.toSG.toGoldfishStore duty.s) hB
    exact (Finset.mem_filter.mp hprocessed).1
  have hrootTree : RootInjectiveBelow tree :=
    Protocol.RootInjectiveBelow.mono hfacts.2.2 htreeT
  have hrootFiltered : Protocol.get_fg_root duty.toHealing.toFG ∈
      Protocol.get_filtered_block_tree duty.toHealing.toFG := by
    simpa only [duty, read, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using
      named_fgRoot_mem_filtered_stateBeforeTime S rho
        (Protocol.vote_time S.E (s + 1)) w
  have hAfull : A ∈ Protocol.get_filtered_block_tree duty.toHealing.toFG :=
    nodeAnchor_mem_filtered_of_fgRoot_mem_filtered S read
      (S.hc.round_of duty.s) hrootFiltered
  have hroot : Protocol.get_fg_root duty.toHealing.toFG ∈ duty.T :=
    Proofs.Records.get_filtered_block_tree_subset duty.toHealing.toFG hrootFiltered
  have hAT : A ∈ duty.T :=
    Proofs.NamedConfirmationMembership.runtime_anchor_mem read.cache
      S.E S.hc duty.toHealing (S.hc.round_of duty.s) hroot
  have hHT : H ∈ duty.T := by
    rw [hHghost]
    exact Proofs.Records.ghost_mem_of _ _ hAT htreeT
  have hHpre : H ∈
      (rho.stateBeforeTime S (Protocol.vote_time S.E (s + 1)) w).st.core.T := by
    simpa only [read, duty, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hHT
  obtain ⟨Hn, hHnBody, hHnErase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (Protocol.vote_time S.E (s + 1)) w hHpre
  have hHnRun : RunBlock S rho Hn := by
    obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (Protocol.vote_time S.E (s + 1))
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw (i := n)
    simpa only [Run.storeBeforeTime, hn] using hHnBody
  have hHnRead : Hn ∈ read.st.bodies := by
    simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hHnBody
  have hSigma : duty.σ H = derive_named S.E S.cfg Hn := by
    rw [← hHnErase]
    exact hfacts.2.1 Hn hHnRead
  refine ⟨Hn, hHnErase, hHnRun, hSigma, ?_⟩
  by_contra hnot
  have hHlow : (duty.σ H).h < duty.h_max - 1 := by
    rw [hSigma]
    exact Nat.lt_of_not_ge hnot
  have stopContradiction : ∀ (Z W : Block V),
      Z = H → Z ∈ tree →
      W ∈ Protocol.voter_processed_block_tree S.E
        duty.toHealing.toFG.toSG.toGoldfishStore duty.s →
      Block.Preceq Z W → duty.h_max - 1 ≤ (duty.σ W).h → False := by
    intro Z W hZH hZtree hWprocessed hZW hWheight
    subst Z
    have hHneW : H ≠ W := by
      intro hEq
      subst W
      exact (Nat.not_lt_of_ge hWheight) hHlow
    obtain ⟨D, hDparent, hDW⟩ := exists_child_towards W hZW hHneW
    have hDtree : D ∈ tree := by
      simpa only [tree, duty, read, voteDutyStore] using
        namedFrozenCandidate_child_towards_witness S adm hw hZtree
          hWprocessed hDparent hDW hWheight
    have hDeligible : eligible D = true := by
      rw [Proofs.Optimistic.goldfish_eligible_iff, parent_eq_of_parent? hDparent]
      exact Or.inl hHlow
    have hDfalse : eligible D = false := by
      have hparent := hDparent
      rw [hHghost] at hparent
      exact eligible_child_false_at_ghost_result hrootTree hDtree hparent
    rw [hDfalse] at hDeligible
    contradiction
  rcases Proofs.Records.ghost_mem A tree score eligible with hHA | hHtree
  · have hHA' : H = A := by simpa only [hHghost] using hHA
    obtain ⟨C, hAC, hCrun, hCprocessed, hmax⟩ := hdesc
    have hAcandidate : A ∈ tree := by
      simpa only [tree, duty, read, voteDutyStore, voterCandidateTreeAt] using
        namedAncestorCandidate_of_processedDescendant_and_hMax S adm hw
          hCprocessed hCrun (by simpa only [A] using hAC)
          (by simpa only [duty, read, voteDutyStore] using hAfull) hmax
    have hHdata := hAcandidate
    simp only [tree, voterCandidateTreeAt, Protocol.voter_filtered_block_tree,
      Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq] at hHdata
    obtain ⟨⟨⟨-, -⟩, W, hWprocessed, hAW, hWheight⟩, -⟩ := hHdata
    exact stopContradiction A W hHA'.symm hAcandidate
      (by simpa only [duty, read, voteDutyStore] using hWprocessed)
      hAW (by simpa only [duty, read, voteDutyStore] using hWheight)
  · have hHtree' : H ∈ tree := by simpa only [hHghost] using hHtree
    have hHdata := hHtree'
    simp only [tree, voterCandidateTreeAt, Protocol.voter_filtered_block_tree,
      Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq] at hHdata
    obtain ⟨⟨⟨-, -⟩, W, hWprocessed, hHW, hWheight⟩, -⟩ := hHdata
    exact stopContradiction H W rfl hHtree'
      (by simpa only [duty, read, voteDutyStore] using hWprocessed)
      hHW (by simpa only [duty, read, voteDutyStore] using hWheight)

/-- The vote-duty head reaches the local `h_max - 1` band whenever some
processed (frozen-view) named run block below the voter's anchor already clears
it. No cone or candidate-tree premise beyond `hdesc` is used. -/
theorem voteDutyHead_height_ge_frontier_sub_one_of_anchorDescendant
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) (s : Slot)
    (hdesc : ∃ C : NamedBlock V,
      Block.Preceq (voterAnchorAt S rho w (s + 1)) C.erase ∧
      RunBlock S rho C ∧
      C.erase ∈ Protocol.voter_processed_block_tree S.E
        (voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
        (voteDutyStore S rho w (s + 1)).toHealing.s ∧
      (voteDutyStore S rho w (s + 1)).h_max ≤
        (derive_named S.E S.cfg C).h + 1) :
    ∃ Hn : NamedBlock V,
      Hn.erase = voterHeadAt S rho w (s + 1) ∧ RunBlock S rho Hn ∧
        (voteDutyStore S rho w (s + 1)).h_max - 1 ≤
          (derive_named S.E S.cfg Hn).h := by
  obtain ⟨Hn, hErase, hRun, -, hband⟩ :=
    voteDutyHead_band_core S adm hw s hdesc
  exact ⟨Hn, hErase, hRun, hband⟩


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
