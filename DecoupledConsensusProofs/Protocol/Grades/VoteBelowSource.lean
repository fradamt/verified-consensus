module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.PerHeight

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol (GradeView HealConfig)
open Internal
open Execution
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. F6.6 — "deepest" is total over a chain (PROTOCOL.md#the-complete-protocol) -/

omit [Fintype V] in
/-- **Distinct depths on a chain** (PROTOCOL.md#the-complete-protocol). Two ancestors of one
block are comparable, and comparable blocks of equal depth are equal. This is
the whole reason the root tie-break never fires inside `deepest_clear`. -/
theorem eq_of_depth_eq_of_chain {T : Finset (Block V)} {C : Block V}
    (hchain : ∀ X ∈ T, Block.preceq X C = true) {X Y : Block V}
    (hX : X ∈ T) (hY : Y ∈ T) (hd : X.depth = Y.depth) : X = Y := by
  rcases Block.preceq_linear (hchain X hX) (hchain Y hY) with h | h
  · exact Block.preceq_eq_of_depth_le h (le_of_eq hd.symm)
  · exact (Block.preceq_eq_of_depth_le h (le_of_eq hd)).symm

omit [Fintype V] in
/-- **F6.6, proved** (PROTOCOL.md#the-complete-protocol; `Protocol.deepest_clear`'s own note).

`Block.deepest?` is total on a nonempty set of ancestors of one block. The
degenerate tie it returns `none` on — two distinct blocks sharing a depth *and*
a root — cannot occur on a chain, because sharing a depth already forces
equality there.

Stated for any chain-contained `Finset`, not only for `deepest_clear`'s own
range, since every `deepest?` the model runs over a chain wants it. -/
theorem deepest?_isSome_of_chain {T : Finset (Block V)} {C : Block V}
    (hchain : ∀ X ∈ T, Block.preceq X C = true) (hne : T.Nonempty) :
    (Block.deepest? T).isSome = true := by
  obtain ⟨L, hLmem, hLeq⟩ := Finset.exists_mem_eq_sup' hne Block.depth
  have hLmax : ∀ X ∈ T, X.depth ≤ L.depth := by
    intro X hX
    rw [← hLeq]
    exact Finset.le_sup' Block.depth hX
  have hdeepL : Block.isDeepestIn T L = true := by
    simp only [Block.isDeepestIn, decide_eq_true_eq]
    intro X hX
    simp only [Block.deeper, Bool.or_eq_false_iff, Bool.and_eq_false_imp,
      decide_eq_false_iff_not, Nat.not_lt]
    refine ⟨hLmax X hX, ?_⟩
    intro heq
    have hXL : X = L :=
      eq_of_depth_eq_of_chain hchain hX hLmem (of_decide_eq_true heq).symm
    subst hXL
    simp
  have hex : ∃! a, a ∈ T ∧ Block.isDeepestIn T a = true := by
    refine ⟨L, ⟨hLmem, hdeepL⟩, ?_⟩
    rintro L' ⟨hL'mem, hL'deep⟩
    simp only [Block.isDeepestIn, decide_eq_true_eq] at hL'deep
    have hLL' := hL'deep L hLmem
    simp only [Block.deeper, Bool.or_eq_false_iff, Bool.and_eq_false_imp,
      decide_eq_false_iff_not, Nat.not_lt] at hLL'
    exact eq_of_depth_eq_of_chain hchain hL'mem hLmem
      (le_antisymm (hLmax L' hL'mem) hLL'.1)
  unfold Block.deepest? pickUnique?
  rw [dif_pos hex]
  rfl

omit [Fintype V] in
/-- **`deepest_clear` is total when its range is nonempty**
(PROTOCOL.md#the-complete-protocol, F6.6). The instance the round action reads: the range
is a subset of `chain_of C`, so the previous lemma applies with `C` itself as
the chain's tip. -/
theorem deepest_clear_isSome_of_mem {floor : Option (Block V)} {C B : Block V}
    {test : Block V → Bool} (hfloor : floor.elim True (fun a => Block.preceq a B = true))
    (hB : B ∈ Protocol.chain_of C) (htest : test B = true) :
    (Protocol.deepest_clear floor C test).isSome = true := by
  refine deepest?_isSome_of_chain (C := C) ?_ ⟨B, ?_⟩
  · intro X hX
    exact Proofs.Engine.mem_chain_of_preceq (List.mem_toFinset.mp (Finset.mem_filter.mp hX).1)
  · refine Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hB, ?_, htest⟩
    cases floor with
    | none => rfl
    | some a => simpa using hfloor

omit [Fintype V] in
/-- **"Deepest" is total on any nonempty pairwise-compatible set**
(PROTOCOL.md#the-complete-protocol).

The generalization of the chain version, and the one the *tree* selections want.
A finite pairwise-comparable set has a greatest element under `⪯`: take the one
of maximal depth, and comparability plus `preceq_eq_of_depth_le` makes every
other member an ancestor of it. So the set is a chain with its own maximum as
the tip, and `deepest?_isSome_of_chain` applies.

This is what makes `fresh_anchor` and `grade2_block` total wherever their grade
sets are nonempty — the document's "conflicting blocks cannot both hold grade 1,
so *deepest* is well defined" (PROTOCOL.md#the-complete-protocol), which the
model until now carried as the F6.6 tie-break caveat. -/
theorem deepest?_isSome_of_compatible {T : Finset (Block V)}
    (hcmp : ∀ X ∈ T, ∀ Y ∈ T, Block.compatible X Y = true) (hne : T.Nonempty) :
    (Block.deepest? T).isSome = true := by
  obtain ⟨L, hLmem, hLeq⟩ := Finset.exists_mem_eq_sup' hne Block.depth
  have hLmax : ∀ X ∈ T, X.depth ≤ L.depth := by
    intro X hX
    rw [← hLeq]
    exact Finset.le_sup' Block.depth hX
  refine deepest?_isSome_of_chain (C := L) ?_ hne
  intro X hX
  have hc := hcmp X hX L hLmem
  simp only [Block.compatible, Bool.or_eq_true] at hc
  rcases hc with h | h
  · exact h
  · have : L = X := Block.preceq_eq_of_depth_le h (hLmax X hX)
    subst this
    exact Block.preceq_self _








/-! ## The endpoint of a nonempty clear walk -/

/-- If the live confirmation itself is above the SG anchor and veto-free, the
clear walk returns that live confirmation. It is the deepest member of its
own ancestor chain. -/
theorem frame_sg_vote_preceq_source
    (S : Setup V) (n : NamedNodeState V) (r : Round) {Q C : Block V}
    (hQ : Protocol.grade2_block_with (NamedProfile.gradeContract n.cache)
      S.E S.hc n.st.core.toHealing r = some Q)
    (hQA : Block.Preceq Q
      (DecoupledConsensusModel.Protocol.frameGradeRead n.cache S.E S.hc
        n.st.core.toHealing r).anchor)
    (hsource : Protocol.fg_source_with (NamedProfile.gradeContract n.cache)
      S.E S.hc n.st.core.toHealing r
      (Protocol.grade2_block_with (NamedProfile.gradeContract n.cache)
        S.E S.hc n.st.core.toHealing r) = some C) :
    Block.Preceq
      (Protocol.get_sg_vote_with (NamedProfile.gradeContract n.cache)
        S.E S.hc n.st.core.toHealing r
        (Protocol.grade2_block_with (NamedProfile.gradeContract n.cache)
          S.E S.hc n.st.core.toHealing r)) C := by
  let st := n.st.core.toHealing
  let grades := DecoupledConsensusModel.Protocol.frameGradeRead n.cache S.E S.hc st r
  have hQread : grades.Q2 = some Q := by
    simpa only [grades, st, Protocol.grade2_block_with,
      NamedProfile.gradeContract, DecoupledConsensusModel.Protocol.frameContract] using hQ
  have hanchor : Block.Preceq Q grades.anchor := by
    simpa only [grades, st] using hQA
  have hsg : Protocol.get_sg_vote_with (NamedProfile.gradeContract n.cache)
      S.E S.hc n.st.core.toHealing r
      (Protocol.grade2_block_with (NamedProfile.gradeContract n.cache)
        S.E S.hc n.st.core.toHealing r) =
      Protocol.currentSGVote st {grades with Q2 := some Q} := by
    simp only [NamedProfile.gradeContract, DecoupledConsensusModel.Protocol.frameContract,
      Protocol.get_sg_vote_with, Protocol.grade2_block_with]
    rw [hQread]
  have hsource' :
      (match Protocol.deepest_clear (some Q) st.live_confirmed grades.clear with
      | some B => some B
      | none => some Q) = some C := by
    simpa only [Protocol.fg_source_with, Protocol.grade2_block_with,
      NamedProfile.gradeContract, DecoupledConsensusModel.Protocol.frameContract,
      hQread, grades, st] using hsource
  cases hw : Protocol.deepest_clear (some Q)
      st.live_confirmed grades.clear with
  | none =>
      have hsourceQ : C = Q := by
        exact (Option.some.inj (by simpa [hw] using hsource')).symm
      rw [hsourceQ]
      cases hv : Protocol.deepest_clear (some grades.anchor)
          st.live_confirmed grades.clear with
      | none =>
          rw [hsg]
          simp only [Protocol.currentSGVote, hv]
          exact Block.preceq_self _
      | some B =>
          have hmem := Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hv)
          have hQB : Block.Preceq Q B :=
            Block.preceq_trans hanchor hmem.2.1
          have hsome := deepest_clear_isSome_of_mem
            (floor := some Q) (C := st.live_confirmed) (B := B)
            (by simpa using hQB) (List.mem_toFinset.mp hmem.1) hmem.2.2
          simp [hw] at hsome
  | some Cfg =>
      have hsourceCfg : C = Cfg := by
        exact (Option.some.inj (by simpa [hw] using hsource')).symm
      rw [hsourceCfg]
      have hmemCfg := Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hw)
      have hQCfg : Block.Preceq Q Cfg := hmemCfg.2.1
      cases hv : Protocol.deepest_clear (some grades.anchor)
          st.live_confirmed grades.clear with
      | none =>
          rw [hsg]
          simp only [Protocol.currentSGVote, hv]
          exact hQCfg
      | some B =>
          have hmemB := Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hv)
          have hBLive : Block.Preceq B st.live_confirmed :=
            Proofs.Engine.mem_chain_of_preceq (List.mem_toFinset.mp hmemB.1)
          have hCfgLive : Block.Preceq Cfg st.live_confirmed :=
            Proofs.Engine.mem_chain_of_preceq (List.mem_toFinset.mp hmemCfg.1)
          have hBCfg : Block.compatible B Cfg = true :=
            Block.compatible_of_preceq_common hBLive hCfgLive
          have hBCfg' : Block.Preceq B Cfg := by
            refine Proofs.HealingLemmas.deepest?_dominates hw
              (Finset.mem_filter.mpr ⟨hmemB.1, ?_, hmemB.2.2⟩) ?_
            · exact Block.preceq_trans hanchor hmemB.2.1
            · exact hBCfg
          rw [hsg]
          simp only [Protocol.currentSGVote, hv]
          exact hBCfg'

#print axioms frame_sg_vote_preceq_source

-- `voteBelowSource'` (the discharge of the public `Props` statement) is


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
