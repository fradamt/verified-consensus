module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ProgressCanonicality
public import DecoupledConsensusProofs.Generic.EvaluationStore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Agreement
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.StoreFinalityConsequences

@[expose] public section

/-!
# Reader-local canonical-cone retention

This file isolates the local fork-choice split for a fixed protected floor `P`.
It does not require `P` itself to remain in the filtered tree after the FG root
has advanced above it.

There are two root orientations.

* If `P ⪯ get_fg_root`, every final Section 7 head already descends `P`.
* If `get_fg_root ⪯ P`, one processed witness above `P` at the local
  `h_max - 1` frontier makes `P`, and every processed segment from `P` to that
  witness, a filtered candidate.

The final theorem combines this split with the two ways that the integrated
head can remain in `P`'s cone. An SG root already above `P` is sufficient by
itself. If the SG root is below `P`, a Goldfish vote cone drives the walk along
the filtered path to `P`.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V]

/-- A local height-frontier witness in the cone of `P`.

The witness is deliberately a processed descendant, not `P` itself. This is
the form supplied by the moving-height argument when the fixed historical floor
is below the current frontier. -/
def CanonicalConeWitness (st : Protocol.Store V) (P : Block V) : Prop :=
  ∃ W ∈ st.T, Block.Preceq P W ∧ st.h_max - 1 ≤ (st.σ W).h

/-- A relayed descendant becomes a cone witness exactly with the missing
one-step upper bound on the reader's local frontier. -/
theorem canonicalConeWitness_of_processedDescendant_and_hMax_le_succ
    {st : Protocol.Store V} {P W : Block V}
    (hWT : W ∈ st.T) (hPW : Block.Preceq P W)
    (hbound : st.h_max ≤ (st.σ W).h + 1) :
    CanonicalConeWitness st P := by
  unfold CanonicalConeWitness
  refine ⟨W, hWT, hPW, ?_⟩
  exact Nat.sub_le_iff_le_add.mpr hbound


/-- A block on the processed segment from `P` to a canonical-cone frontier
witness belongs to the filtered tree, provided the FG root is below `P`.

This is the exact descendant-retention direction. The same witness does not
make an arbitrary branch descendant of `P` viable; `D ⪯ W` is essential. -/
theorem canonicalConeSegment_mem_filtered_of_root_preceq
    {st : Protocol.Store V} (hpc : ParentClosed st)
    (hFJ : Block.Preceq st.F st.J)
    {P W D : Block V}
    (hrootP : Block.Preceq
      (Protocol.get_fg_root st.toHealing.toFG) P)
    (hWT : W ∈ st.T)
    (hheight : st.h_max - 1 ≤ (st.σ W).h)
    (hPD : Block.Preceq P D) (hDW : Block.Preceq D W) :
    D ∈ Protocol.get_filtered_block_tree st.toHealing.toFG := by
  have hDT : D ∈ st.T :=
    Proofs.Records.mem_of_preceq ((parentClosed_iff st).mp hpc).2 D W hWT hDW
  have hFD : Block.Preceq st.F D :=
    Block.preceq_trans
      (Proofs.Records.preceq_get_fg_root_of_F (st := st.toHealing.toFG) hFJ)
      (Block.preceq_trans hrootP hPD)
  have hrootD : Block.Preceq
      (Protocol.get_fg_root st.toHealing.toFG) D :=
    Block.preceq_trans hrootP hPD
  have hV : D ∈ Protocol.V_tree st.toHealing.toFG := by
    simp only [Protocol.V_tree, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq, Protocol.Store.toHealing]
    exact ⟨⟨hDT, hFD⟩, W, hWT, hDW, hheight⟩
  exact Proofs.Records.mem_filtered_of_mem_V_tree hV hrootD

/-- The reader-local root split for a fixed floor.

Compatibility gives two orientations. The advanced-root orientation is kept
as `P ⪯ root`; no filtered membership for historical `P` is asserted there.
In the reverse orientation, the cone witness makes `P` a current candidate. -/
theorem canonicalFloor_preceq_root_or_mem_filtered
    {st : Protocol.Store V} (hpc : ParentClosed st)
    (hFJ : Block.Preceq st.F st.J) {P : Block V}
    (hcompat : Block.compatible
      (Protocol.get_fg_root st.toHealing.toFG) P = true)
    (hwitness : CanonicalConeWitness st P) :
    Block.Preceq P (Protocol.get_fg_root st.toHealing.toFG) ∨
      P ∈ Protocol.get_filtered_block_tree st.toHealing.toFG := by
  simp only [Block.compatible, Bool.or_eq_true] at hcompat
  rcases hcompat with hrootP | hProot
  · right
    obtain ⟨W, hWT, hPW, hheight⟩ := hwitness
    exact canonicalConeSegment_mem_filtered_of_root_preceq hpc hFJ
      hrootP hWT hheight (Block.preceq_self P) hPW
  · exact Or.inl hProot

variable [Fintype V]



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
