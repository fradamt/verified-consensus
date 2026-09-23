module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.Ancestry
public import Mathlib.Data.Nat.Find

@[expose] public section

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- A nonempty family of ancestors of one block has a greatest member. -/
theorem greatest_member_of_common_ancestor_bound
    (P : Block V → Prop) {D H : Block V}
    (hD : P D) (hbound : ∀ B, P B → Block.Preceq B H) :
    ∃ Base, P Base ∧ ∀ B, P B → Block.Preceq B Base := by
  classical
  let Q : Nat → Prop := fun n => ∃ B, P B ∧ B.depth = n
  let m := Nat.findGreatest Q H.depth
  have hm : Q m := Nat.findGreatest_spec
    (Block.preceq_depth_le (hbound D hD)) ⟨D, hD, rfl⟩
  obtain ⟨Base, hBase, hdepth⟩ := hm
  refine ⟨Base, hBase, ?_⟩
  intro B hB
  have hle : B.depth ≤ m := Nat.le_findGreatest
    (Block.preceq_depth_le (hbound B hB)) ⟨B, hB, rfl⟩
  have hdepthLe : B.depth ≤ Base.depth := by simpa only [hdepth] using hle
  rcases Block.preceq_linear (hbound B hB) (hbound Base hBase) with h | h
  · exact h
  · have heq := Block.preceq_eq_of_depth_le h hdepthLe
    simpa only [heq] using Block.preceq_self Base

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
