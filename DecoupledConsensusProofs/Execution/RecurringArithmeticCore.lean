module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.AlignedRoundLemmas
public import DecoupledConsensusProofs.Protocol.ChainState.Main
public import DecoupledConsensusInternal.Execution.Assumptions
public import DecoupledConsensusProofs.Protocol.ChainState.NjGap

@[expose] public section

/-!
# Low arithmetic for recurring finality

This module contains four recovery-independent facts used by the recurring
finality proof: faulty validators alone cannot form a quorum, a bounded
nonjustifiable height exists above every lower bound, a periodic height's
successor has a clear `nj` latch, and a strict height inequality orients
compatible blocks.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]



/-- A set containing only faulty validators cannot be a finality-gadget
quorum under the below-one-third fault bound. -/
theorem not_isQuorum_of_subset_faulty
    {S : Setup V} {rho : Run V}
    (hbot : BelowOneThird S rho.honest) {Q : Finset V}
    (hQ : Q ⊆ Finset.univ \ rho.honest) :
    ¬ S.E.electorate.IsQuorum Q := by
  intro hquorum
  obtain ⟨v, hvQ, hvHonest⟩ :=
    AlignedRoundLemmas.honest_member_of_quorum hbot hquorum
  exact (Finset.mem_sdiff.mp (hQ hvQ)).2 hvHonest




end HealingSurface
end Proofs
end DecoupledConsensusModel

end
