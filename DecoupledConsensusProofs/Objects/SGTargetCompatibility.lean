module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.SlotInduction

@[expose] public section
/-!
# Compatibility of two SG targets from one honest Goldfish head

This file isolates the same-slot part of Claim 2. The substantive lemma is
pure ancestry: two blocks below one honest Goldfish head are compatible. The
run wrapper only supplies that common head from two Claim-1-shaped vote cones.
It uses committee honest-majority to choose one honest committee member, honest
single-vote emission to identify the two vote roots, and run-wide root
collision freedom to identify the two emitted heads.
-/


namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Proofs.Optimistic

variable {V : Type} [DecidableEq V]

/-- Two blocks extended by one honest Goldfish head are compatible.

The conclusion is the generic ancestry fact and does not inspect SG targets or
any fork-choice case.
-/
theorem compatible_of_common_honest_goldfish_head
    {T1 T2 X : Block V}
    (hT1 : Block.Preceq T1 X)
    (hT2 : Block.Preceq T2 X) :
    Block.compatible T1 T2 = true := by
  exact Block.compatible_of_preceq_common hT1 hT2


/-- Two Claim-1-shaped cones at one slot give compatible targets.

The committee-majority inequality makes the chosen committee intersect the
honest set. Both cones therefore provide emitted votes for the same honest
validator. `emits_gfVote_unique` identifies those votes (their slots are
both `s`), and `RootCollisionFree` identifies the named run blocks behind
their common root. The resulting common head is then consumed (through
`.erase`) by `compatible_of_common_honest_goldfish_head`.

/named-lifecycle proof: `HonestVotesCone` is
`NamedHonestVotesCone`, so the cone witness is a `NamedBlock` and the target
predicate reads its `.erase`; `RootCollisionFree.root_injective` is stated
directly over that named witness, dropping the prior ancestor-set existential.
-/
theorem sgTargetCompatible_of_honestVotesCone [Fintype V]
    (S : Setup V) {rho : Run V} {s : Slot} {T1 T2 : Block V}
    (hcom : HonestCommittees S rho.honest)
    (hsch : ScheduleWellFormed S rho)
    (hcf : RootCollisionFree S rho)
    (hT1 : NamedHonestVotesCone S rho s (fun X => Block.Preceq T1 X))
    (hT2 : NamedHonestVotesCone S rho s (fun X => Block.Preceq T2 X)) :
    Block.compatible T1 T2 = true := by
  have hmajority := hcom s
  have hpos : 0 < ((S.E.committee s) ∩ rho.honest).card := by
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  obtain ⟨hxcommittee, hxhonest⟩ := Finset.mem_inter.mp hx
  obtain ⟨X1, hT1X1, hX1, he1⟩ := hT1 x hxhonest hxcommittee
  obtain ⟨X2, hT2X2, hX2, he2⟩ := hT2 x hxhonest hxcommittee
  have huv :
      (⟨x, s, X1.erase.root⟩ : GoldfishVote V) = ⟨x, s, X2.erase.root⟩ :=
    emits_gfVote_unique S hsch he1 he2 rfl
  have hroot : X1.erase.root = X2.erase.root :=
    congrArg (fun u : GoldfishVote V => u.head) huv
  have hrootN : X1.root = X2.root :=
    (Proofs.NamedWire.erase_root X1).symm.trans (hroot.trans (Proofs.NamedWire.erase_root X2))
  have hX12 : X1 = X2 :=
    NamedRootCollisionFree.root_injective hcf X1 X2 hX1 hX2 X1 X2
      (Or.inl (Proofs.NamedAncestry.named_self X1))
      (Or.inr (Proofs.NamedAncestry.named_self X2)) hrootN
  rw [← hX12] at hT2X2
  exact compatible_of_common_honest_goldfish_head hT1X1 hT2X2

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
