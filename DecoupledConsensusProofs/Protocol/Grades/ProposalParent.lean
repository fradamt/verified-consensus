module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.StoreRoots
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.DutyInputDefaults
public import DecoupledConsensusModel.Protocol.Grades

@[expose] public section

/-! Membership of the actual shared proposal read for both concrete
runtime modes. This producer is independent of the named duty constructor. -/
namespace DecoupledConsensusModel.Proofs.NamedProposalParent
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The walk needs only a retained anchor and a subset of the stored tree. -/
theorem get_head_with_mem (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (votes support : Finset (GoldfishVote V)) (k : Slot)
    (hanchor : (gc.read E hc st (hc.round_of st.s)).anchor ∈ st.T) :
    Protocol.get_head_with gc E hc st votes support k ∈ st.T := by
  exact Proofs.Records.ghost_mem_of _ _ hanchor (Proofs.Records.get_filtered_block_tree_subset st.toFG)

omit [Fintype V] in
/-- A frame prefix is selected from the actual filtered tree. Its saved root
does not itself need to belong to that tree. -/
theorem activePrefix_mem (tree : Finset (Block V)) (root B : Block V)
    (h : DecoupledConsensusModel.Protocol.activePrefix tree root = some B) : B ∈ tree := by
  exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem h)).1

theorem frame_anchor_mem (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) (g1 : Option (Option (Block V)))
    (hroot : Protocol.get_fg_root st.toFG ∈ st.T) :
    DecoupledConsensusModel.Protocol.anchor E hc st r g1 ∈ st.T := by
  cases g1 with
  | none => exact hroot
  | some opt =>
    cases opt with
    | none => exact hroot
    | some root =>
      change (DecoupledConsensusModel.Protocol.activePrefix
        (Protocol.get_filtered_block_tree st.toFG) root).getD
          (Protocol.get_fg_root st.toFG) ∈ st.T
      cases hp : DecoupledConsensusModel.Protocol.activePrefix
          (Protocol.get_filtered_block_tree st.toFG) root with
      | none => exact hroot
      | some B =>
        exact Proofs.Records.get_filtered_block_tree_subset st.toFG
          (activePrefix_mem _ root B hp)

/-- This covers both concrete grade contracts, for any cache. It makes no
claim about an arbitrary caller-supplied contract. -/
theorem runtime_get_head_mem
    (cache : DecoupledConsensusModel.Protocol.Cache V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (votes support : Finset (GoldfishVote V)) (k : Slot)
    (hroot : Protocol.get_fg_root st.toFG ∈ st.T) :
    Protocol.get_head_with (DecoupledConsensusModel.Protocol.frameContract cache)
      E hc st votes support k ∈ st.T := by
  apply get_head_with_mem
  exact frame_anchor_mem E hc st (hc.round_of st.s)
    (DecoupledConsensusModel.Protocol.readFrame cache st (hc.round_of st.s)).g1 hroot

/-- The local named-store root invariant supplies the shared read's parent. -/
theorem proposal_parent_mem
    (cache : DecoupledConsensusModel.Protocol.Cache V) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (h : Proofs.NamedStoreRoots.RootsInTree st) :
    (Protocol.proposal_input_with (DecoupledConsensusModel.Protocol.frameContract cache)
      E hc nd st.core.toHealing).parent ∈ st.core.T := by
  rw [DutyInputDefaults.proposal_input_parent]
  exact runtime_get_head_mem cache E hc st.core.toHealing _ _ _
    (Proofs.NamedStoreRoots.fg_root_mem st h)

/-- TreeView and scoped ErasureUnique supply exactly one retained full body
for the actual parent. No global erasure-injectivity premise is used. -/
theorem proposal_parent_named_body_unique
    (cache : DecoupledConsensusModel.Protocol.Cache V) (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (h : Proofs.NamedStoreRoots.Invariant E cfg st) :
    ∃! B : NamedBlock V, B ∈ st.bodies ∧ B.erase =
      (Protocol.proposal_input_with (DecoupledConsensusModel.Protocol.frameContract cache)
        E hc nd st.core.toHealing).parent := by
  have hmem := proposal_parent_mem cache E hc nd st h.2
  rw [h.1.1] at hmem
  obtain ⟨B, hB, hErase⟩ := Finset.mem_image.mp hmem
  refine ⟨B, ⟨hB, hErase⟩, ?_⟩
  intro C hC
  exact h.1.2.1 C hC.1 B hB (hC.2.trans hErase.symm)

/-- GF vote processing preserves the two mutable roots and the core tree. -/
theorem roots_goldfish_vote_with (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (h : Proofs.NamedStoreRoots.RootsInTree st) :
    Proofs.NamedStoreRoots.RootsInTree
      { st with core := (Protocol.goldfish_vote_with gc E hc nd st.core).1 } := by
  dsimp only [Protocol.goldfish_vote_with]
  split_ifs
  · unfold Proofs.NamedStoreRoots.RootsInTree
    simpa only [(coreEq_on_goldfish_vote_checked E st.core _).F_eq,
      (coreEq_on_goldfish_vote_checked E st.core _).J_eq,
      on_goldfish_vote_checked_T] using h
  · exact h

/-- Confirmation changes only confirmation fields, so it preserves the roots. -/
theorem roots_update_confirmation_with (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.NamedStore V) (s : Slot)
    (h : Proofs.NamedStoreRoots.RootsInTree st) :
    Proofs.NamedStoreRoots.RootsInTree
      { st with core := Protocol.update_confirmation_with gc E hc st.core s } := h

#print axioms get_head_with_mem
#print axioms activePrefix_mem
#print axioms frame_anchor_mem
#print axioms runtime_get_head_mem
#print axioms proposal_parent_mem
#print axioms proposal_parent_named_body_unique
#print axioms roots_goldfish_vote_with
#print axioms roots_update_confirmation_with
end DecoupledConsensusModel.Proofs.NamedProposalParent

end
