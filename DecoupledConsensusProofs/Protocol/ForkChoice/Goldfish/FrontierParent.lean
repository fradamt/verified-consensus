module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.ProgressQuorumCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FrontierRise
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore

@[expose] public section

/-!
# The final head stays within two heights of the frontier

The candidate-tree witness for a final Section 7 head can lie on a descendant
branch rather than at the head itself. Even so, the head cannot be more than
one transition below that tree's `h_max - 1` boundary. If it were lower, the
first candidate child towards the witness would pass the low-height clause of
the final Goldfish gate, so the GHOST walk could not stop at the head.

The pure GHOST statement below also closes the finite-fuel detail: a walk with
`tree.card` fuel ends at a block whose next `ghost_step` is `none`. Otherwise
the traversed path plus one more child would contain more members than `tree`.

Root collision freedom is needed only to turn an eligible child into an actual
`argmax?` step. At the execution layer this is the existing hash idealization,
`RootCollisionFree`; it is not implied by bare dependency reachability.
-/

/-! ## A finite GHOST walk really open items -/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]



omit [Fintype V] in
/-- Every strict block between the start and the result of a fuelled GHOST walk
is a member of the walk tree. -/
theorem ghost_walk_path_mem
    {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} :
    ∀ (n : Nat) (A D : Block V),
      Block.Preceq A D → D ≠ A →
      Block.Preceq D (Protocol.ghost_walk tree score eligible n A) →
      D ∈ tree := by
  intro n
  induction n with
  | zero =>
      intro A D hAD hne hDwalk
      simp only [Protocol.ghost_walk] at hDwalk
      exact False.elim (hne (Block.preceq_antisymm hDwalk hAD))
  | succ n ih =>
      intro A D hAD hne hDwalk
      cases hstep : Protocol.ghost_step tree score eligible A with
      | none =>
          simp only [Protocol.ghost_walk, hstep] at hDwalk
          exact False.elim (hne (Block.preceq_antisymm hDwalk hAD))
      | some C =>
          have hCdata := Protocol.ghost_step_child hstep
          have hCwalk : Block.Preceq C
              (Protocol.ghost_walk tree score eligible n C) :=
            Protocol.ghost_walk_preceq tree score eligible n C
          have hDwalk' : Block.Preceq D
              (Protocol.ghost_walk tree score eligible n C) := by
            simpa only [Protocol.ghost_walk, hstep] using hDwalk
          rcases Block.preceq_linear hDwalk' hCwalk with hDC | hCD
          · have hAdepth : A.depth ≤ D.depth := Block.preceq_depth_le hAD
            have hdepthNe : A.depth ≠ D.depth := by
              intro heq
              apply hne
              exact (Block.preceq_eq_of_depth_le hAD (by omega)).symm
            have hCdepth : C.depth = A.depth + 1 :=
              Protocol.depth_of_parent? hCdata.2.1
            have hCDdepth : C.depth ≤ D.depth := by omega
            have hEq : D = C := Block.preceq_eq_of_depth_le hDC hCDdepth
            rw [hEq]
            exact hCdata.1
          · by_cases hEq : D = C
            · rw [hEq]
              exact hCdata.1
            · exact ih C D hCD hEq hDwalk'

omit [Fintype V] in
/-- If the result still has a next step, the walk used every unit of fuel. -/
theorem ghost_walk_result_depth_of_next_step
    {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} :
    ∀ (n : Nat) (A C : Block V),
      Protocol.ghost_step tree score eligible
          (Protocol.ghost_walk tree score eligible n A) = some C →
      (Protocol.ghost_walk tree score eligible n A).depth = A.depth + n := by
  intro n
  induction n with
  | zero =>
      intro A C _
      simp only [Protocol.ghost_walk, Nat.add_zero]
  | succ n ih =>
      intro A C hout
      cases hstep : Protocol.ghost_step tree score eligible A with
      | none =>
          simp only [Protocol.ghost_walk, hstep] at hout
          contradiction
      | some B =>
          have hout' : Protocol.ghost_step tree score eligible
              (Protocol.ghost_walk tree score eligible n B) = some C := by
            simpa only [Protocol.ghost_walk, hstep] using hout
          have hd := ih B C hout'
          have hBdepth : B.depth = A.depth + 1 :=
            Protocol.depth_of_parent?
              (Protocol.ghost_step_child hstep).2.1
          simp only [Protocol.ghost_walk, hstep]
          omega

omit [Fintype V] in
/-- `tree.card` fuel cannot expire at a block that has another selected child. -/
theorem ghost_step_at_ghost_eq_none
    (anchor : Block V) (tree : Finset (Block V))
    (score : Block V → Nat) (eligible : Block V → Bool) :
    Protocol.ghost_step tree score eligible
        (Protocol.ghost anchor tree score eligible) = none := by
  by_contra hne
  obtain ⟨C, hnext'⟩ := Option.ne_none_iff_exists.mp hne
  have hnext := hnext'.symm
  let H := Protocol.ghost anchor tree score eligible
  have hCdata := Protocol.ghost_step_child hnext
  have hanchorH : Block.Preceq anchor H :=
    Protocol.ghost_preceq anchor tree score eligible
  have hHC : Block.Preceq H C :=
    Protocol.preceq_of_parent? hCdata.2.1
  have hanchorC : Block.Preceq anchor C :=
    Block.preceq_trans hanchorH hHC
  have hpath : ∀ D : Block V, Block.Preceq anchor D → D ≠ anchor →
      Block.Preceq D C → D ∈ tree := by
    intro D hAD hneA hDC
    by_cases hDCeq : D = C
    · rw [hDCeq]
      exact hCdata.1
    · have hDH : Block.Preceq D H := by
        rcases Block.preceq_linear hDC hHC with hDH | hHD
        · exact hDH
        · have hDdepth : D.depth ≤ C.depth := Block.preceq_depth_le hDC
          have hdepthNe : D.depth ≠ C.depth := by
            intro heq
            exact hDCeq (Block.preceq_eq_of_depth_le hDC (by omega))
          have hCdepth : C.depth = H.depth + 1 :=
            Protocol.depth_of_parent? hCdata.2.1
          have hDtoH : D.depth ≤ H.depth := by omega
          have hEq : H = D := Block.preceq_eq_of_depth_le hHD hDtoH
          rw [hEq]
          exact Block.preceq_self _
      apply ghost_walk_path_mem tree.card anchor D hAD hneA
      simpa only [Protocol.ghost, H] using hDH
  have hcard := Protocol.path_card anchor C tree hanchorC hpath
  have hHdepth : H.depth = anchor.depth + tree.card := by
    apply ghost_walk_result_depth_of_next_step tree.card anchor C
    simpa only [Protocol.ghost, H] using hnext
  have hCdepth : C.depth = H.depth + 1 :=
    Protocol.depth_of_parent? hCdata.2.1
  omega

omit [Fintype V] in
/-- With collision-free roots, the result has no eligible child in the tree. -/
theorem eligible_child_false_at_ghost_result
    {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} {anchor C : Block V}
    (hroot : RootInjectiveBelow tree)
    (hC : C ∈ tree)
    (hparent : C.parent? = some (Protocol.ghost anchor tree score eligible)) :
    eligible C = false := by
  cases helig : eligible C with
  | false => rfl
  | true =>
      have hchild : C ∈ Protocol.ghost_children tree eligible
          (Protocol.ghost anchor tree score eligible) := by
        simp only [Protocol.ghost_children, Finset.mem_filter]
        exact ⟨hC, hparent, helig⟩
      have hsub : Protocol.ghost_children tree eligible
          (Protocol.ghost anchor tree score eligible) ⊆ tree := by
        intro D hD
        exact (Finset.mem_filter.mp hD).1
      obtain ⟨D, -, hstep⟩ :=
        Protocol.exists_argmax?_eq_some_of_rootInjectiveBelow
          hroot ⟨C, hchild⟩ hsub
      have hnone := ghost_step_at_ghost_eq_none anchor tree score eligible
      change Protocol.ghost_step tree score eligible
          (Protocol.ghost anchor tree score eligible) = some D at hstep
      rw [hnone] at hstep
      contradiction

/-! ## Frontier bounds from local store facts
The previous proofs use only parent closure, root injectivity, and filtered FG-root
membership. The named read supplies all three facts without a reachability
conversion. -/


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
