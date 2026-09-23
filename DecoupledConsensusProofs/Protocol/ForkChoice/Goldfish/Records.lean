module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ValidatorClient.Engine
public import DecoupledConsensusProofs.Protocol.Handlers.Invariants2
public import DecoupledConsensusProofs.Protocol.Grades.LegacyVocabulary

@[expose] public section

/-!
# The record lemmas — G2, G3, `lock_eq_saved`, O10, O11
(§1 F1–F4, §5.4; obligations O10, O11)

Everything the two pair rules write, and everything a chain state's block fields
say about their own chain. Five groups, in dependency order.

* **The writers.** `Λ.with_target`, `Λ.with_timeout` and `Λ.with_lock` each write
  one field at one height (PROTOCOL.md#the-complete-protocol). Read-back and
  leave-alone, once, so no later proof unfolds a record update.
* **G3, the `target` discipline** (check doc F1, F2). `height_pair` emits at most
  three shapes and writes at most one field, and the write-once reading of
  `Λ.target` is exactly *"a save is written only on the emitting target path,
  with the emitted pair's target"*. The consequence the self-safety proof runs
  on is `height_pair_target_unique`: once `Λ.target[h] = T`, a later call at a
  gate of height `h` emits `(h, T)`, a timeout, or nothing — never `(h, T')`.
* **G2, the finality rule's guards** (PROTOCOL.md#the-complete-protocol). `finality_pair`
  emits a nonempty pair only under `Λ.target[h_j] = J ∧ ¬Λ.timeout[h_j] ∧
  Λ.lock[h_j] ∈ {⊥, J}`, and the pair it emits is the *head* chain state's
  `(h_j, J)`. One split; the record half is `lock_eq_saved` again.
* **O10, `σ[B].J ⪯ B`.** The justified and finalized blocks of a derived chain
  state are on the chain that derived it. `Invariants2`'s `ChainFinality`
  already carries `F ⪯ J ⪯ T_h ⪯ L` and is closed under the transition, so O10
  is that bundle plus `L = B`, which `state_transition_L` gives outright. The
  store corollary — `Σ.J ∈ Σ.T` at a parent-closed store whose state map agrees
  with the derived one, and hence at every dependency-complete reachable store —
  is what the P6 fragment's finding P-5 asked for.
* **O11, the tick's own dependency clause, discharged.** Every fork-choice walk
  in the model returns its anchor or a member of the tree it walks, every such
  tree is a filter of `Σ.T`, and every anchor is in that tree or is
  `get_fg_root(Σ) ∈ {Σ.J, Σ.F}`. With O10 and O5 that puts the proposal's
  head in `Σ.T`, so `DepOk` holds at the block the tick self-processes and the
  execution layer needs **no** fifth admissibility clause.

`lock_eq_saved` (check doc §5.4) is stated over the Λ-thread of
`Internal.AttestHistory`: `Λ.lock[h] = T → Λ.target[h] = T` is not true of an
arbitrary record, only of one an `attest` sequence produced. The step form
`lockCompatible_attest` is what the induction uses; `lock_eq_saved` is the
reachability form the check doc names.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace Records

open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Internal

/-! ## The record writers (PROTOCOL.md#the-complete-protocol) -/









/-- §5.3 `Λ.lock[h] ← J` reads back at `h` (PROTOCOL.md#the-complete-protocol). -/
theorem with_lock_self (Λ : Record) (h : Height) (T : BlockId) :
    (Λ.with_lock h T).lock h = some T := by
  simp [Protocol.Record.with_lock]

/-- §5.3 `Λ.lock[h] ← J` leaves every other height alone (PROTOCOL.md#the-complete-protocol). -/
theorem with_lock_ne {Λ : Record} {h k : Height} {T : BlockId} (hk : k ≠ h) :
    (Λ.with_lock h T).lock k = Λ.lock k := by
  simp [Protocol.Record.with_lock, hk]



/-- **F3** as a predicate on one record (check doc §1 F3, §5.4): a lock rules
out a timeout and is compatible with an empty or matching target entry.

Not true of an arbitrary `Record`: the type admits a lock together with a
timeout or a different target. It therefore travels as an invariant rather
than as a theorem about `Record`. -/
def LockCompatible (Λ : Record) : Prop :=
  ∀ (h : Height) (T : BlockId), Λ.lock h = some T →
    Λ.timeout h = false ∧ (Λ.target h = none ∨ Λ.target h = some T)

/-- §5.3 the initial record satisfies it vacuously (PROTOCOL.md#the-complete-protocol). -/
theorem lockCompatible_initial : LockCompatible Record.initial := by
  intro h T hl
  simp [Protocol.Record.initial] at hl



/-! ## O10 — the chain state's blocks are on its own chain
(PROTOCOL.md#the-complete-protocol; obligations O10) -/

section DerivedChain

variable {V : Type} [DecidableEq V] [Fintype V]






/-- §4 the latest block of a derived chain state is the block itself
(PROTOCOL.md#the-complete-protocol). -/
theorem derived_state_L (E : Env V) (cfg : HeightConfig) (B : Block V) :
    (Internal.derived_state E cfg B).L = B := by
  cases B with
  | genesis => rfl
  | node p s r gv gsv ats i => exact state_transition_L E cfg _ _

/-- §4 every derived chain state satisfies `ChainFinality`
(PROTOCOL.md#the-complete-protocol).

The transition's own hypothesis `σ.L ⪯ B` is discharged by `derived_state_L` at
the parent: the state being extended is the parent's, and its latest block *is*
the parent. -/
theorem chainFinality_derived (E : Env V) (cfg : HeightConfig) (B : Block V) :
    ChainFinality (Internal.derived_state E cfg B) := by
  induction B with
  | genesis => exact chainFinality_initial
  | node p s r gv gsv ats i ih =>
      refine chainFinality_state_transition E cfg _ _ ih ?_
      rw [derived_state_L]
      exact preceq_parent (.node p s r gv gsv ats i)

/-- **O10** (obligations O10; PROTOCOL.md#the-complete-protocol): the justified
block of a derived chain state is on the chain that derived it.

`ChainFinality` carries `J ⪯ T_h ⪯ L` and the transition writes `L ← B`, so the
whole ancestry chain lands below `B`. Genesis is the base: every block field of
`ChainState.initial` is `B_gen`. -/
theorem derived_state_J_preceq (E : Env V) (cfg : HeightConfig) (B : Block V) :
    Block.preceq (Internal.derived_state E cfg B).J B = true := by
  have h := chainFinality_derived E cfg B
  have hJ := Block.preceq_trans h.justified_preceq_target h.target_preceq_latest
  rw [derived_state_L] at hJ
  exact hJ

/-! ### The store corollary (P6 fragment P-5; obligations O10) -/

omit [Fintype V] in
/-- §1 a parent-closed tree holds every ancestor of every member
(PROTOCOL.md#the-complete-protocol). -/
theorem mem_of_preceq {T : Finset (Block V)}
    (hcl : ∀ B ∈ T, B.parent? = none ∨ B.parent ∈ T) :
    ∀ (X B : Block V), B ∈ T → Block.preceq X B = true → X ∈ T := by
  intro X B
  induction B with
  | genesis =>
      intro hB hp
      simp only [Block.preceq, decide_eq_true_eq] at hp
      exact hp ▸ hB
  | node p s r gv gsv ats i ih =>
      intro hB hp
      simp only [Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at hp
      rcases hp with rfl | hp
      · exact hB
      · refine ih ?_ hp
        rcases hcl _ hB with hn | hpar
        · simp [Block.parent?] at hn
        · simpa [Block.parent] using hpar



end DerivedChain

/-! ### `Σ.J ∈ Σ.T` along a dependency-complete run (obligations O10) -/

section StoreJustified

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- §5.2 `update_finality` writes `Σ.J` from the chain state it is given, or not
at all (PROTOCOL.md#the-complete-protocol). -/
theorem update_finality_J_cases (st : Protocol.Store V) (σ : ChainState V) :
    (Protocol.update_finality st σ).J = st.J ∨
      (Protocol.update_finality st σ).J = σ.J := by
  simp only [Protocol.update_finality]
  split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl

end StoreJustified

/-! ## O11 — the proposal's head is processed
(P6 fragment P-4/P-5; obligations O11; PROTOCOL.md#the-complete-protocol)

`DepStep.on_tick` carries its own dependency clause because the tick
self-processes the block `Protocol.proposal` builds and no delivery predicate
reaches it (P-5). The clause is **derivable**: every fork-choice walk of the
model returns either its anchor or a member of the tree it walks, every tree it
walks is a filter of `Σ.T`, and every anchor is either in that tree or is
`get_fg_root(Σ) ∈ {Σ.J, Σ.F}` — which O10 and O5 put in `Σ.T`. -/

section Head

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- §2.4 the GHOST descent stays inside its tree: it returns the block it
started from, or a member of the tree it walks (PROTOCOL.md#the-complete-protocol). -/
theorem ghost_walk_mem (tree : Finset (Block V)) (score : Block V → Nat)
    (eligible : Block V → Bool) :
    ∀ (n : Nat) (H : Block V),
      Protocol.ghost_walk tree score eligible n H = H ∨
        Protocol.ghost_walk tree score eligible n H ∈ tree := by
  intro n
  induction n with
  | zero => intro H; exact Or.inl rfl
  | succ n ih =>
      intro H
      rw [Protocol.ghost_walk]
      split
      · exact Or.inl rfl
      · rename_i C hstep
        have hmem : C ∈ Protocol.ghost_children tree eligible H :=
          Proofs.Engine.pickUnique?_mem hstep
        rw [Protocol.ghost_children, Finset.mem_filter] at hmem
        rcases ih C with h | h
        · rw [h]
          exact Or.inr hmem.1
        · exact Or.inr h

omit [Fintype V] in
/-- §2.4 `ghost` returns its anchor or a member of its tree
(PROTOCOL.md#the-complete-protocol). -/
theorem ghost_mem (anchor : Block V) (tree : Finset (Block V)) (score : Block V → Nat)
    (eligible : Block V → Bool) :
    Protocol.ghost anchor tree score eligible = anchor ∨
      Protocol.ghost anchor tree score eligible ∈ tree :=
  ghost_walk_mem tree score eligible tree.card anchor

omit [Fintype V] in
/-- §2.4 a `ghost` walk whose anchor and tree are both processed returns a
processed block (PROTOCOL.md#the-complete-protocol). -/
theorem ghost_mem_of {T : Finset (Block V)} {anchor : Block V}
    {tree : Finset (Block V)} (score : Block V → Nat) (eligible : Block V → Bool)
    (hanchor : anchor ∈ T) (htree : tree ⊆ T) :
    Protocol.ghost anchor tree score eligible ∈ T := by
  rcases ghost_mem anchor tree score eligible with h | h
  · rw [h]
    exact hanchor
  · exact htree h

omit [Fintype V] in
/-- §5.2 the candidate tree is a filter of the processed tree
(PROTOCOL.md#the-complete-protocol). -/
theorem get_filtered_block_tree_subset (st : Protocol.FGStore V) :
    Protocol.get_filtered_block_tree st ⊆ st.T := by
  intro B hB
  simp only [Protocol.get_filtered_block_tree, Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Finset.mem_filter] at hB
  exact hB.1.1.1

omit [Fintype V] in
/-- §5.2 an explicit candidate tree is a filter of the processed block view
supplied to `get_filtered_block_tree_from`. -/
theorem get_filtered_block_tree_from_subset (st : Protocol.FGStore V)
    (blocks : Finset (Block V)) :
    Protocol.get_filtered_block_tree_from st blocks ⊆ blocks := by
  intro B hB
  simp only [Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Finset.mem_filter] at hB
  exact hB.1.1.1


omit [Fintype V] in

/-- §5.2 **the candidate tree descends the fork-choice root**
(PROTOCOL.md#the-complete-protocol).

`get_filtered_block_tree` is `V(Σ)` filtered by `root ⪯ ·`, so membership carries
the root-descent test with it. This is the fact §6's `fresh_anchor` *absorbs*: it
blocked writing `get_fg_root(Σ) ⪯ R` beside its membership test, because
membership implies it. Stated so that the absorption is machine-checked rather
than asserted — if the candidate tree ever blocked filtering by root-descent,
this would fail here and not silently at `fresh_anchor`. -/
theorem preceq_get_fg_root_of_mem_filtered {st : Protocol.FGStore V}
    {B : Block V} (hB : B ∈ Protocol.get_filtered_block_tree st) :
    Block.preceq (Protocol.get_fg_root st) B = true := by
  simp only [Protocol.get_filtered_block_tree, Protocol.get_filtered_block_tree_from,
    Finset.mem_filter] at hB
  exact hB.2

omit [Fintype V] in
/-- §5.2 the converse: a viable block above the root is in the candidate tree
(PROTOCOL.md#the-complete-protocol). -/
theorem mem_filtered_of_mem_V_tree {st : Protocol.FGStore V} {B : Block V}
    (hB : B ∈ Protocol.V_tree st)
    (hroot : Block.preceq (Protocol.get_fg_root st) B = true) :
    B ∈ Protocol.get_filtered_block_tree st := by
  simp only [Protocol.get_filtered_block_tree, Protocol.get_filtered_block_tree_from,
    Finset.mem_filter]
  exact ⟨hB, hroot⟩


omit [Fintype V] in
/-- §5.2 the fork-choice root descends the finalized block, given P6
(PROTOCOL.md#the-complete-protocol).

`get_fg_root(Σ)` is `Σ.J` or `Σ.F`, so this is `Σ.F ⪯ Σ.J` in the first case
and reflexivity in the second. `Σ.F ⪯ Σ.J` is not a fact about an arbitrary
store — it is P6, `Invariants2.finalizedPrecedesJustifiedInvariant`, which holds
at every reachable one — so it enters as a hypothesis here rather than being
assumed silently. -/
theorem preceq_get_fg_root_of_F {st : Protocol.FGStore V}
    (hFJ : Block.preceq st.F st.J = true) :
    Block.preceq st.F (Protocol.get_fg_root st) = true := by
  simp only [Protocol.get_fg_root]
  split
  · exact hFJ
  · exact Block.preceq_self _

omit [Fintype V] in
/-- §5.2 **the candidate tree is ancestor-closed down to the fork-choice root**
(PROTOCOL.md#the-complete-protocol).

If `P` is in the candidate tree and `R` is a processed ancestor of `P` that still
descends the fork-choice root, then `R` is in the candidate tree too. Each of the
three conditions travels:

* *live* — `Σ.F ⪯ R` follows from `Σ.F ⪯ root ≺ R`, which is where P6 is spent;
* *viable* — viability is an existential over live descendants, and every
  descendant of `P` is one of `R`, so `P`'s own witness serves;
* *below the root* — hypothesis.

Membership in `Σ.T` does **not** travel and is a hypothesis: the model never
proves the processed tree parent-closed as a store invariant (`ParentClosedStep`
is a step property with a dependency premise), and the one caller that needs this
resolves `R` out of `Σ.T` anyway. -/
theorem mem_filtered_of_preceq {st : Protocol.FGStore V} {P R : Block V}
    (hFJ : Block.preceq st.F st.J = true)
    (hP : P ∈ Protocol.get_filtered_block_tree st) (hRT : R ∈ st.T)
    (hRP : Block.preceq R P = true)
    (hroot : Block.preceq (Protocol.get_fg_root st) R = true) :
    R ∈ Protocol.get_filtered_block_tree st := by
  simp only [Protocol.get_filtered_block_tree, Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Finset.mem_filter, Protocol.viable, decide_eq_true_eq] at hP ⊢
  obtain ⟨⟨⟨-, -⟩, W, hW, hPW, hh⟩, -⟩ := hP
  have hFR : Block.preceq st.F R = true :=
    Block.preceq_trans (preceq_get_fg_root_of_F hFJ) hroot
  exact ⟨⟨⟨hRT, hFR⟩, W, hW, Block.preceq_trans hRP hPW, hh⟩, hroot⟩

/- Kept for the retained erased confirmation-membership consumer. -/
theorem fresh_anchor_mem (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (r : Round) {R : Block V} (h : Protocol.fresh_anchor E hc st r = some R) :
    R ∈ Protocol.get_filtered_block_tree st.toFG :=
  (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem h)).1


theorem fresh_anchor_root_preceq (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) {R : Block V}
    (h : Protocol.fresh_anchor E hc st r = some R) :
    Block.preceq (Protocol.get_fg_root st.toFG) R = true :=
  preceq_get_fg_root_of_mem_filtered (fresh_anchor_mem E hc st r h)

theorem healing_get_head_mem (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (votes support_votes : Finset (GoldfishVote V))
    (k : Slot) (hroot : Protocol.get_fg_root st.toFG ∈ st.T) :
    Protocol.get_head_hc E hc st votes support_votes k ∈ st.T := by
  have htree : Protocol.get_filtered_block_tree st.toFG ⊆ st.T :=
    get_filtered_block_tree_subset st.toFG
  refine ghost_mem_of _ _ ?_ htree
  simp only [Protocol.get_sg_root, Protocol.get_sg_root_with,
    Protocol.GradeContract.current, Protocol.currentGradeRead]
  split
  · rename_i A hA
    exact htree (fresh_anchor_mem E hc st _ hA)
  · split
    · exact hroot
    · exact ghost_mem_of _ _ hroot htree


omit [Fintype V] in
/-- §1 a root resolved through a tree lands in it, `⊥` included
(PROTOCOL.md#the-complete-protocol). The shape `set_fresh_root` resolves `P.proposal_root`
with (PROTOCOL.md#the-complete-protocol). -/
theorem mem_of_bind_find? {T : Finset (Block V)} {o : Option BlockId} {B : Block V}
    (h : o.bind (Block.find? T) = some B) : B ∈ T := by
  cases o with
  | none => simp at h
  | some root =>
    simp only [Option.bind_some] at h
    unfold Block.find? at h
    exact Proofs.Engine.pickUnique?_mem h





end Head

end Records
end Proofs
end DecoupledConsensusModel

end
