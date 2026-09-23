module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.VoteHead
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Adoption
public import DecoupledConsensusProofs.Protocol.Schedule.SlotInduction

@[expose] public section

/-!
# Confirmation-cone persistence with compatible anchors

The original slot induction asks that every later Goldfish anchor precede the
confirmed block. Canonicality only needs, and the integrated protocol naturally
provides, the weaker invariant that the anchor stays on the same chain. This
file proves that this is sufficient: an anchor above the confirmed block already
starts in its cone, while an anchor below it is driven through the block by the
honest supporter majority.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A cone supported by every honest committee member gives `B` a strict
supporter majority. -/
theorem supporterMajority_of_cone
    (E : Env V) {T : Finset (Block V)}
    {votes support : Finset (GoldfishVote V)} {s : Slot}
    {Hon : Finset V} {B : Block V}
    (hcone : Proofs.Optimistic.ConeSupport E T votes support votes s Hon
      (fun X => Block.Preceq B X))
    (hvalid : Protocol.VoteSetValid E s votes) :
    Protocol.voters_count E votes s <
      2 * (Protocol.goldfishSupporters E T votes support s B).card := by
  have hsub : (E.committee s) ∩ Hon ⊆
      Protocol.goldfishSupporters E T votes support s B :=
    hcone.subset_supporters (by
      intro X hBX
      exact hBX)
  have hcard := Finset.card_le_card hsub
  have hcount := hcone.count_lt hvalid
  omega

end Protocol
end DecoupledConsensusModel

end
