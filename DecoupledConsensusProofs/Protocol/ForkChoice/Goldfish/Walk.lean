module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Records

@[expose] public section

/-!
# P3(a) — the GHOST descent
(§2.4 `def:goldfish-walk`, PROTOCOL.md#the-complete-protocol; §7.2's confirmation walk,
PROTOCOL.md#the-complete-protocol)

Everything here is about `Protocol.ghost` and nothing else: no store, no run, no
synchrony. The walk serves the Goldfish fork choice, the §3 majority fork choice
and available confirmation alike (`Goldfish/ForkChoice.lean`), so a lemma proved
once here is available to all three.

Three facts, in the order the availability proof consumes them.

* **The walk never retreats past its anchor.** Every step moves to a *child* of
  The current head, so the result is `⪰` the anchor. With the composed
  evaluation this reads at `get_sg_root`: a genuine confirmation is `⪰` the
  round's anchor, and with `root ⪯ A` it is what makes
  `Protocol.live_confirmed_preceq_root` unconditional
  (PROTOCOL.md#the-complete-protocol).
* **Strict score domination decides the `argmax`.** `Protocol.argmax?` is
  `pickUnique?` over `is_best_in`, so it commits to `C` exactly when `C` is the
  unique unbeaten child. A child that strictly outscores every sibling is that
  child, and the root tie-break (F1.2) is never inspected.
* **Domination along a path drives the walk to its end.** If every block on the
  path from the anchor to `target` is the strict `argmax` at its parent, and
  `target` itself has no eligible child, the walk returns `target` exactly. The
  fuel is `tree.card`, so the lemma also has to show the path fits in the tree —
  `path_card`, the only place `Finset.card` appears.

`ghost_walk_mem` (`Proofs/Proofs.Records.lean`) is the fourth fact and is already
proved; it is not restated.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## `pickUnique?`, decided

`Protocol.argmax?` and `Block.deepest?` are both `pickUnique?`
(`Substrate/Blocks.lean`), which returns `none` on an empty set *and* on a tie it
cannot break. Two lemmas fix both ends. -/

omit [Fintype V] in
/-- `pickUnique?` commits to `C` when `C` passes the test and is the only member
that does. -/
theorem pickUnique?_eq_some {α : Type} [DecidableEq α] {T : Finset α} {p : α → Bool}
    {C : α} (hC : C ∈ T) (hp : p C = true) (huniq : ∀ a ∈ T, p a = true → a = C) :
    pickUnique? T p = some C := by
  have hex : ∃! a, a ∈ T ∧ p a = true := ⟨C, ⟨hC, hp⟩, fun b hb => huniq b hb.1 hb.2⟩
  unfold pickUnique?
  rw [dif_pos hex]
  refine congrArg some ?_
  have hspec := Finset.choose_spec (fun a => p a = true) T hex
  exact huniq _ hspec.1 hspec.2

omit [Fintype V] in
/-- `pickUnique?` returns `none` on an empty set: there is no member to be the
unique one. -/
theorem pickUnique?_empty {α : Type} [DecidableEq α] {T : Finset α} {p : α → Bool}
    (h : T = ∅) : pickUnique? T p = none := by
  unfold pickUnique?
  rw [dif_neg]
  rintro ⟨a, ⟨ha, -⟩, -⟩
  rw [h] at ha
  exact absurd ha (by simp)

/-! ## The `argmax` (PROTOCOL.md#the-complete-protocol) -/

omit [DecidableEq V] [Fintype V] in
/-- §2.4 an unbeaten member of a set with a strict maximum is that maximum
(PROTOCOL.md#the-complete-protocol). -/
theorem eq_of_is_best_in {score : Block V → Nat} {children : Finset (Block V)}
    {C a : Block V} (hC : C ∈ children) (ha : a ∈ children)
    (hdom : ∀ D ∈ children, D ≠ C → score D < score C)
    (hbest : Protocol.is_best_in score children a = true) : a = C := by
  by_contra hne
  simp only [Protocol.is_best_in, decide_eq_true_eq] at hbest
  have hCa := hbest C hC
  simp only [Protocol.outranks, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hCa
  exact absurd (hdom a ha hne) hCa.1

omit [Fintype V] in
/-- §2.4 a child that strictly outscores every sibling is the `argmax`
(PROTOCOL.md#the-complete-protocol).

The tie-break is never reached: `outranks` puts the root order behind an equality
of scores, and strict domination rules that out. -/
theorem argmax?_eq_some_of_dominates {score : Block V → Nat}
    {children : Finset (Block V)} {C : Block V} (hC : C ∈ children)
    (hdom : ∀ D ∈ children, D ≠ C → score D < score C) :
    Protocol.argmax? score children = some C := by
  refine pickUnique?_eq_some hC ?_ (fun a ha hbest => eq_of_is_best_in hC ha hdom hbest)
  simp only [Protocol.is_best_in, decide_eq_true_eq]
  intro D hD
  by_cases hDC : D = C
  · subst hDC
    simp [Protocol.outranks]
  · have hlt := hdom D hD hDC
    simp only [Protocol.outranks, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
      decide_eq_false_iff_not]
    exact ⟨by omega, Or.inl (by omega)⟩

omit [Fintype V] in
/-- A nonempty finite child set has a selected `argmax` when its roots are
injective in the containing tree. The proof first maximizes the score and then
maximizes the root among the score-maximal children. Root injectivity makes
that lexicographic maximum a unique block. -/
theorem exists_argmax?_eq_some_of_rootInjectiveBelow
    {tree children : Finset (Block V)} {score : Block V → Nat}
    (hroot : RootInjectiveBelow tree) (hne : children.Nonempty)
    (hsub : children ⊆ tree) :
    ∃ C ∈ children, Protocol.argmax? score children = some C := by
  obtain ⟨M, hM, hMscore⟩ := Finset.exists_mem_eq_sup' hne score
  have hscoreMax : ∀ D ∈ children, score D ≤ score M := by
    intro D hD
    rw [← hMscore]
    exact Finset.le_sup' score hD
  let top := children.filter (fun D => score D = score M)
  have hMtop : M ∈ top := by
    dsimp only [top]
    exact Finset.mem_filter.mpr ⟨hM, rfl⟩
  obtain ⟨C, hCtop, hCroot⟩ :=
    Finset.exists_mem_eq_sup' ⟨M, hMtop⟩ Block.root
  have hCdata : C ∈ children ∧ score C = score M := by
    simpa only [top, Finset.mem_filter] using hCtop
  have hrootMax : ∀ D ∈ top, D.root ≤ C.root := by
    intro D hD
    rw [← hCroot]
    exact Finset.le_sup' Block.root hD
  have hCbest : Protocol.is_best_in score children C = true := by
    simp only [Protocol.is_best_in, decide_eq_true_eq]
    intro D hD
    simp only [Protocol.outranks, Bool.or_eq_false_iff,
      Bool.and_eq_false_iff, decide_eq_false_iff_not]
    refine ⟨?_, ?_⟩
    · have := hscoreMax D hD
      omega
    · by_cases heq : score C = score D
      · right
        have hDtop : D ∈ top := by
          dsimp only [top]
          exact Finset.mem_filter.mpr ⟨hD, heq.symm.trans hCdata.2⟩
        exact not_lt_of_ge (hrootMax D hDtop)
      · exact Or.inl heq
  refine ⟨C, hCdata.1, pickUnique?_eq_some hCdata.1 hCbest ?_⟩
  intro D hD hDbest
  simp only [Protocol.is_best_in, decide_eq_true_eq] at hDbest
  have hCD := hDbest C hCdata.1
  simp only [Protocol.outranks, Bool.or_eq_false_iff,
    Bool.and_eq_false_iff, decide_eq_false_iff_not] at hCD
  have hDscoreLe : score D ≤ score C := by
    have := hscoreMax D hD
    omega
  have hscoreEq : score D = score C :=
    le_antisymm hDscoreLe (le_of_not_gt hCD.1)
  have hDtop : D ∈ top := by
    dsimp only [top]
    exact Finset.mem_filter.mpr ⟨hD, hscoreEq.trans hCdata.2⟩
  have hrootNot : ¬ D.root < C.root := by
    rcases hCD.2 with hneScore | hnot
    · exact False.elim (hneScore hscoreEq)
    · exact hnot
  have hrootEq : D.root = C.root :=
    le_antisymm (hrootMax D hDtop) (le_of_not_gt hrootNot)
  exact hroot D C
    ⟨D, hsub hD, Block.preceq_self D⟩
    ⟨C, hsub hCdata.1, Block.preceq_self C⟩ hrootEq

/-! ## One step of the walk (PROTOCOL.md#the-complete-protocol) -/

omit [Fintype V] in
/-- §2.4 a step of the walk lands on an eligible child of the current head that
belongs to the tree (PROTOCOL.md#the-complete-protocol). -/
theorem ghost_step_child {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} {H C : Block V}
    (h : Protocol.ghost_step tree score eligible H = some C) :
    C ∈ tree ∧ C.parent? = some H ∧ eligible C = true := by
  have hmem : C ∈ Protocol.ghost_children tree eligible H :=
    Proofs.Engine.pickUnique?_mem h
  rw [Protocol.ghost_children, Finset.mem_filter] at hmem
  exact ⟨hmem.1, hmem.2.1, hmem.2.2⟩

omit [Fintype V] in

/-- §2.4 the walk open items where the head has no eligible child
(PROTOCOL.md#the-complete-protocol). -/
theorem ghost_step_none {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} {H : Block V}
    (h : ∀ C ∈ tree, C.parent? = some H → eligible C = false) :
    Protocol.ghost_step tree score eligible H = none := by
  refine pickUnique?_empty ?_
  rw [Finset.eq_empty_iff_forall_notMem]
  intro C hC
  rw [Protocol.ghost_children, Finset.mem_filter] at hC
  exact absurd hC.2.2 (by rw [h C hC.1 hC.2.1]; simp)

omit [DecidableEq V] [Fintype V] in
/-- §1 a child is one edge deeper than its parent (PROTOCOL.md#the-complete-protocol). -/
theorem depth_of_parent? {C H : Block V} (h : C.parent? = some H) :
    C.depth = H.depth + 1 := by
  cases C with
  | genesis => simp [Block.parent?] at h
  | node p _ _ _ _ _ _ =>
      simp only [Block.parent?, Option.some.injEq] at h
      subst h
      rfl

omit [Fintype V] in
/-- §1 a parent precedes its child (PROTOCOL.md#the-complete-protocol). -/
theorem preceq_of_parent? {C H : Block V} (h : C.parent? = some H) :
    Block.preceq H C = true := by
  have hp := Proofs.parent_eq_of_parent? h
  rw [← hp]
  exact Proofs.preceq_parent C

/-! ## The walk never retreats past its anchor -/

omit [Fintype V] in
/-- §2.4 the descent only ever moves to children, so its result descends from the
block it started at (PROTOCOL.md#the-complete-protocol). -/
theorem ghost_walk_preceq (tree : Finset (Block V)) (score : Block V → Nat)
    (eligible : Block V → Bool) :
    ∀ (n : Nat) (H : Block V),
      Block.Preceq H (Protocol.ghost_walk tree score eligible n H) := by
  intro n
  induction n with
  | zero => intro H; exact Block.preceq_self _
  | succ n ih =>
      intro H
      rw [Protocol.ghost_walk]
      split
      · exact Block.preceq_self _
      · rename_i C hstep
        exact Block.preceq_trans (preceq_of_parent? (ghost_step_child hstep).2.1) (ih C)

omit [Fintype V] in
/-- §7.2 the confirmation walk's result descends from its anchor
(PROTOCOL.md#the-complete-protocol): with the composed evaluation's anchor
`get_sg_root(Σ, round(Σ.s))`, this is the genuine-confirmation half of
`Protocol.live_confirmed_preceq_root`. -/
theorem ghost_preceq (anchor : Block V) (tree : Finset (Block V))
    (score : Block V → Nat) (eligible : Block V → Bool) :
    Block.Preceq anchor (Protocol.ghost anchor tree score eligible) :=
  ghost_walk_preceq tree score eligible tree.card anchor

omit [Fintype V] in
/-- §2.4 the descent's result is either the anchor or a block the gate let
through (PROTOCOL.md#the-complete-protocol). This is what turns a confirmation walk into an
*eligible* block, which is the object the counting argument reasons about. -/
theorem ghost_walk_eligible (tree : Finset (Block V)) (score : Block V → Nat)
    (eligible : Block V → Bool) :
    ∀ (n : Nat) (H : Block V),
      Protocol.ghost_walk tree score eligible n H = H ∨
        eligible (Protocol.ghost_walk tree score eligible n H) = true := by
  intro n
  induction n with
  | zero => intro H; exact Or.inl rfl
  | succ n ih =>
      intro H
      rw [Protocol.ghost_walk]
      split
      · exact Or.inl rfl
      · rename_i C hstep
        rcases ih C with h | h
        · exact Or.inr (by rw [h]; exact (ghost_step_child hstep).2.2)
        · exact Or.inr h

omit [Fintype V] in
/-- §7.2 the confirmed block is the anchor or clears the gate
(PROTOCOL.md#the-complete-protocol). -/
theorem ghost_eligible (anchor : Block V) (tree : Finset (Block V))
    (score : Block V → Nat) (eligible : Block V → Bool) :
    Protocol.ghost anchor tree score eligible = anchor ∨
      eligible (Protocol.ghost anchor tree score eligible) = true :=
  ghost_walk_eligible tree score eligible tree.card anchor

/-! ## Steps towards a target -/

omit [Fintype V] in
/-- §1 a child does not precede its parent: it is one edge deeper
(PROTOCOL.md#the-complete-protocol). This is why a slot-`(s+1)` child of `B` is not among the
blocks an honest slot-`s` vote supports. -/
theorem preceq_parent_false {C H : Block V} (h : C.parent? = some H) :
    Block.preceq C H = false := by
  rw [← Bool.not_eq_true]
  intro hpre
  have := Block.preceq_depth_le hpre
  rw [depth_of_parent? h] at this
  omega


omit [Fintype V] in
/-- §1 a strict ancestor of `B` has a child that is still an ancestor of `B`:
the next block on the path (PROTOCOL.md#the-complete-protocol). -/
theorem exists_child_towards {H : Block V} :
    ∀ B : Block V, Block.preceq H B = true → H ≠ B →
      ∃ C, C.parent? = some H ∧ Block.preceq C B = true := by
  intro B
  induction B with
  | genesis =>
      intro hpre hne
      exact absurd (by simpa only [Block.preceq, decide_eq_true_eq] using hpre) hne
  | node p s r gv gsv ats i ih =>
      intro hpre hne
      by_cases hHp : H = p
      · subst hHp
        exact ⟨Block.node H s r gv gsv ats i, rfl, Block.preceq_self _⟩
      · have hp : Block.preceq H p = true := by
          simp only [Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at hpre
          rcases hpre with h | h
          · exact absurd h hne
          · exact h
        obtain ⟨C, hpar, hCp⟩ := ih hp hHp
        refine ⟨C, hpar, Block.preceq_trans hCp ?_⟩
        simp only [Block.preceq, Bool.or_eq_true]
        exact Or.inr (Block.preceq_self _)

omit [Fintype V] in
/-- Two children of one block that both precede a common descendant are equal:
they sit at the same depth on one chain (PROTOCOL.md#the-complete-protocol). -/
theorem child_towards_unique {H C D B : Block V} (hC : C.parent? = some H)
    (hD : D.parent? = some H) (hCB : Block.preceq C B = true)
    (hDB : Block.preceq D B = true) : D = C := by
  rcases Block.preceq_linear hDB hCB with h | h
  · exact Block.preceq_eq_of_depth_le h (by rw [depth_of_parent? hC, depth_of_parent? hD])
  · exact (Block.preceq_eq_of_depth_le h
      (by rw [depth_of_parent? hC, depth_of_parent? hD])).symm

/-! ## The path fits in the tree

`Protocol.ghost` runs on `tree.card` fuel (PROTOCOL.md#the-complete-protocol, F2.6). A path from
the anchor to a target whose every intermediate block lies in the tree is
therefore never cut short: the blocks of the path are distinct members of the
tree, one per depth. -/

omit [Fintype V] in
/-- The blocks strictly below the anchor and at or above the target are distinct
members of the tree, so the depth gap is at most `tree.card`. -/
theorem path_card (anchor : Block V) :
    ∀ (target : Block V) (tree : Finset (Block V)), Block.Preceq anchor target →
      (∀ C : Block V, Block.Preceq anchor C → C ≠ anchor → Block.Preceq C target →
        C ∈ tree) →
      target.depth ≤ anchor.depth + tree.card := by
  intro target
  induction target with
  | genesis =>
      intro tree hpre _
      have hg : anchor = Block.genesis := by
        simpa only [Block.Preceq, Block.preceq, decide_eq_true_eq] using hpre
      subst hg
      simp
  | node p s r gv gsv ats i ih =>
      intro tree hpre hmem
      set T : Block V := Block.node p s r gv gsv ats i with hT
      by_cases hEq : anchor = T
      · rw [hEq]
        omega
      · have hanp : Block.Preceq anchor p := by
          simp only [Block.Preceq, hT, Block.preceq, Bool.or_eq_true,
            decide_eq_true_eq] at hpre
          rcases hpre with h | h
          · exact absurd h hEq
          · exact h
        have hpT : Block.Preceq p T := by
          simp only [Block.Preceq, hT, Block.preceq, Bool.or_eq_true]
          exact Or.inr (Block.preceq_self _)
        have hTmem : T ∈ tree := hmem T hpre (Ne.symm hEq) (Block.preceq_self _)
        have hmem' : ∀ C : Block V, Block.Preceq anchor C → C ≠ anchor →
            Block.Preceq C p → C ∈ tree.erase T := by
          intro C h1 h2 h3
          refine Finset.mem_erase.mpr ⟨?_, hmem C h1 h2 (Block.preceq_trans h3 hpT)⟩
          intro hCT
          have : (T : Block V).depth ≤ p.depth := by
            rw [← hCT]; exact Block.preceq_depth_le h3
          simp only [hT, Block.depth] at this
          omega
        have hIH := ih (tree.erase T) hanp hmem'
        have hcard : (tree.erase T).card = tree.card - 1 := Finset.card_erase_of_mem hTmem
        have hpos : 1 ≤ tree.card := Finset.card_pos.mpr ⟨T, hTmem⟩
        have hdT : (T : Block V).depth = p.depth + 1 := by simp [hT, Block.depth]
        omega

/-! ## Domination along a path drives the walk to its end -/

omit [Fintype V] in
/-- The fuelled descent reaches `target` when every block strictly between the
current head and `target` is the walk's own next step, and `target` has no
eligible child (PROTOCOL.md#the-complete-protocol). -/
theorem ghost_walk_reaches {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} {anchor target : Block V}
    (hstop : Protocol.ghost_step tree score eligible target = none)
    (hstep : ∀ H : Block V, Block.Preceq anchor H → Block.Preceq H target → H ≠ target →
      ∃ C, Protocol.ghost_step tree score eligible H = some C ∧ Block.Preceq C target) :
    ∀ (n : Nat) (H : Block V), Block.Preceq anchor H → Block.Preceq H target →
      target.depth ≤ H.depth + n →
      Protocol.ghost_walk tree score eligible n H = target := by
  intro n
  induction n with
  | zero =>
      intro H _ hpre hd
      have : H = target := Block.preceq_eq_of_depth_le hpre (by omega)
      simpa only [Protocol.ghost_walk] using this
  | succ n ih =>
      intro H hanch hpre hd
      by_cases hHt : H = target
      · subst hHt
        simp only [Protocol.ghost_walk, hstop]
      · obtain ⟨C, hCs, hCp⟩ := hstep H hanch hpre hHt
        have hchild := ghost_step_child hCs
        have hdepth : C.depth = H.depth + 1 := depth_of_parent? hchild.2.1
        simp only [Protocol.ghost_walk, hCs]
        exact ih C (Block.preceq_trans hanch (preceq_of_parent? hchild.2.1)) hCp (by omega)

omit [Fintype V] in
/-- **The descent lemma**. `ghost` returns `target` exactly when the path from the
anchor lies in the tree, every block of it is the walk's own next step, and
`target` has no eligible child (PROTOCOL.md#the-complete-protocol).

This is the shape the confirmation argument uses: `hstep` comes from strict score
domination along the path (`Confirmation.lean`), `hstop` from the fact that a
slot-`(s+1)` block carries no slot-`s` vote below it, and `hpath` from the
membership of the proposal's ancestors in the live tree. -/
theorem ghost_reaches {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} {anchor target : Block V}
    (hpre : Block.Preceq anchor target)
    (hpath : ∀ C : Block V, Block.Preceq anchor C → C ≠ anchor → Block.Preceq C target →
      C ∈ tree)
    (hstop : Protocol.ghost_step tree score eligible target = none)
    (hstep : ∀ H : Block V, Block.Preceq anchor H → Block.Preceq H target → H ≠ target →
      ∃ C, Protocol.ghost_step tree score eligible H = some C ∧ Block.Preceq C target) :
    Protocol.ghost anchor tree score eligible = target :=
  ghost_walk_reaches hstop hstep tree.card anchor (Block.preceq_self _) hpre
    (path_card anchor target tree hpre hpath)

end Protocol
end DecoupledConsensusModel

end
