module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.Main
public import DecoupledConsensusInternal.Execution.Assumptions

@[expose] public section

namespace DecoupledConsensusModel
namespace Protocol

open Protocol (HeightConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The block in `T_h` has the state height recorded in `h`. -/
theorem derived_target_height (E : Env V) (cfg : HeightConfig) :
    ∀ B : Block V,
      (derived_state E cfg (derived_state E cfg B).T_h).h =
        (derived_state E cfg B).h := by
  intro B
  induction B with
  | genesis => rfl
  | node p s r gv gsv ats i ih =>
      rw [derived_state_node, process_height_events_eq]
      split_ifs with ht hp
      · rw [advance_height_T_h, advance_height_h, afterFin_L, afterFin_h, foldBlock_L]
        rw [derived_state_node, process_height_events_eq, if_pos ht,
          advance_height_h, afterFin_h]
      · rw [advance_height_T_h, advance_height_h, afterFin_L, afterFin_h, foldBlock_L]
        rw [derived_state_node, process_height_events_eq, if_neg ht, if_pos hp,
          advance_height_h, afterFin_h]
      · rw [afterFin_T_h, afterFin_h, foldBlock_T_h, foldBlock_h]
        exact ih

/-- A justification is genesis-height zero, or its target has state height
`h_j`. -/
theorem derived_justified_height (E : Env V) (cfg : HeightConfig) :
    ∀ B : Block V,
      (derived_state E cfg B).h_j = 0 ∨
        (derived_state E cfg (derived_state E cfg B).J).h =
          (derived_state E cfg B).h_j := by
  intro B
  induction B with
  | genesis => exact Or.inl rfl
  | node p s r gv gsv ats i ih =>
      rw [derived_state_node, process_height_events_eq]
      split_ifs
      · right
        rw [advance_height_J, advance_height_h_j, afterFin_T_h, afterFin_h,
          foldBlock_T_h, foldBlock_h]
        exact derived_target_height E cfg p
      · rw [advance_height_J, advance_height_h_j, afterFin_J, afterFin_h_j,
          foldBlock_J, foldBlock_h_j]
        exact ih
      · rw [afterFin_J, afterFin_h_j, foldBlock_J, foldBlock_h_j]
        exact ih

/-- One child transition cannot lower the derived state height. -/
theorem derived_h_le_node (E : Env V) (cfg : HeightConfig)
    (p : Block V) (s : Slot) (r : BlockId) (gv : List (GoldfishVote V))
    (gsv : List (GoldfishVote V)) (ats : List (CombinedAttestation V)) (i : V) :
    (derived_state E cfg p).h ≤
      (derived_state E cfg (Block.node p s r gv gsv ats i)).h := by
  rw [derived_state_node, process_height_events_eq]
  split_ifs
  · rw [advance_height_h, afterFin_h, foldBlock_h]
    exact Nat.le_succ _
  · rw [advance_height_h, afterFin_h, foldBlock_h]
    exact Nat.le_succ _
  · rw [afterFin_h, foldBlock_h]

/-- Derived state height is monotone along block ancestry. -/
theorem derived_h_mono (E : Env V) (cfg : HeightConfig) {A B : Block V}
    (hAB : Block.preceq A B = true) :
    (derived_state E cfg A).h ≤ (derived_state E cfg B).h := by
  induction B with
  | genesis =>
      simp only [Block.preceq, decide_eq_true_eq] at hAB
      subst A
      exact Nat.le_refl _
  | node p s r gv gsv ats i ih =>
      simp only [Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at hAB
      rcases hAB with rfl | hAp
      · exact Nat.le_refl _
      · exact Nat.le_trans (ih hAp) (derived_h_le_node E cfg p s r gv gsv ats i)

end Protocol
end DecoupledConsensusModel

end
