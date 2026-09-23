module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FinalityFilterRetention

@[expose] public section

/-!
# Ancestor projection for full finality-filter quietness

Full noninterference for a protected descendant projects to an ancestor at the
same actual protocol read. This is not a blanket ancestor-closure claim about
an arbitrary filtered tree. The proof obtains processed ancestor membership
from dependency reachability and handles the actual selected-root orientation
explicitly.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the complete finality-filter stage does not displace `B`, then it does
not displace an ancestor `P` at the same actual read. -/
theorem FinalityFilterNoninterferenceAtRead.ancestor
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} {read : Time} {P B : Block V}
    (hPB : Block.Preceq P B)
    (hBquiet : FinalityFilterNoninterferenceAtRead S rho w read B) :
    FinalityFilterNoninterferenceAtRead S rho w read P := by
  rcases hBquiet with hBroot | hBfiltered
  · exact Or.inl (Block.preceq_trans hPB hBroot)
  · let st : Protocol.NamedStore V := rho.storeBeforeTime S w read
    have hrootB : Block.Preceq
        (Protocol.get_fg_root st.toHealing.toFG) B := by
      exact Proofs.Records.preceq_get_fg_root_of_mem_filtered
        (by simpa only [st] using hBfiltered)
    rcases Block.preceq_linear hrootB hPB with hrootP | hProot
    · right
      have hpc : ParentClosed st.core :=
        Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho read w
      have hBT : B ∈ st.core.T :=
        Proofs.Records.get_filtered_block_tree_subset st.toHealing.toFG
          (by simpa only [st] using hBfiltered)
      have hPT : P ∈ st.core.T :=
        Proofs.Records.mem_of_preceq ((parentClosed_iff st.core).mp hpc).2
          P B hBT hPB
      have hFJ : Block.Preceq st.core.F st.core.J :=
        Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho read w
      have hPfiltered : P ∈
          Protocol.get_filtered_block_tree st.toHealing.toFG :=
        Proofs.Records.mem_filtered_of_preceq
          (st := st.toHealing.toFG)
          (by simpa only [Protocol.NamedStore.toHealing] using hFJ)
          (by simpa only [st] using hBfiltered) hPT hPB hrootP
      exact (by simpa only [st] using hPfiltered)
    · exact Or.inl (by simpa only [st] using hProot)



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
