module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.StoreFinalityRun
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsProducers

@[expose] public section

/-!
# Candidate-tree totality at a healing frontier rise

`ActivityLossRun` shows that a strict `h_max - 1` rise can remove an old
graded block from one store's filtered tree. This file isolates what that rise
does *not* do in a dependency-reachable Section 7 store: it cannot make the
filtered tree empty.

The non-cascade root is `F`, whose viability is the existing reachable-store
invariant. In the cascade case `h_max = h_j + 1`, justification provenance
supplies a processed block `C` whose derived state installed `(J, h_j)`.
`J \preceq C` and `h_j < derived_state(C).h`, so `C` is a viability witness for
`J` at the cascade threshold. Thus the FG root belongs to the filtered tree in
both cases, and every composed Section 7 head belongs to that tree as well.

This does not prove that a fresh child of the returned head is viable. A child
can leave the head's viability witness on a sibling branch. The proposal step
therefore still needs a frontier-height or carrier-replay producer before it can
serve as the next moving common prefix.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]


/-- If the FG root is in the filtered tree, the final SG root is in it too.
The fresh branch selects from the tree. The relative branch is a GHOST walk
whose anchor and range are both the same tree. -/
theorem getSgRoot_mem_filtered_of_fgRoot_mem
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (r : Round)
    (hroot : Protocol.get_fg_root st.toFG ∈
      Protocol.get_filtered_block_tree st.toFG) :
    Protocol.get_sg_root E hc st r ∈
      Protocol.get_filtered_block_tree st.toFG := by
  simp only [Protocol.get_sg_root, Protocol.get_sg_root_with,
    Protocol.GradeContract.current, Protocol.currentGradeRead]
  cases hanchor : Protocol.fresh_anchor E hc st r with
  | some A =>
      exact Proofs.Records.fresh_anchor_mem E hc st r hanchor
  | none =>
      dsimp only
      split
      · exact hroot
      · unfold Protocol.majority_fork_choice
        exact Proofs.Records.ghost_mem_of _ _ hroot (Finset.Subset.refl _)

/-- With the FG-root totality fact, every final composed head is itself a
filtered-tree member, for arbitrary Goldfish inputs. -/
theorem getHead_mem_filtered_of_fgRoot_mem
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (votes supportVotes : Finset (GoldfishVote V)) (k : Slot)
    (hroot : Protocol.get_fg_root st.toFG ∈
      Protocol.get_filtered_block_tree st.toFG) :
    Protocol.get_head_hc E hc st votes supportVotes k ∈
      Protocol.get_filtered_block_tree st.toFG := by
  have hanchor : Protocol.get_sg_root E hc st (hc.round_of st.s) ∈
      Protocol.get_filtered_block_tree st.toFG :=
    getSgRoot_mem_filtered_of_fgRoot_mem E hc st (hc.round_of st.s) hroot
  simp only [Protocol.get_head_hc, Protocol.get_head_in_tree_hc,
    Protocol.goldfish_fork_choice, Protocol.get_filtered_block_tree,
    Protocol.get_filtered_block_tree_from] at hanchor ⊢
  exact Proofs.Records.ghost_mem_of _ _ hanchor (Finset.Subset.refl _)

/-! ## Named read facades -/

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
