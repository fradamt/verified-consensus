module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusModel
public import DecoupledConsensusInternal

@[expose] public section

noncomputable section

/-! # Proof-internal compatibility vocabulary
These definitions were part of the erased absolute-grade model before the
selected protocol was made the only model path. They remain here only because
the proof library still states established lemmas in that vocabulary.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Protocol (SGVote)

variable {V : Type} [DecidableEq V] [Fintype V]




/-- §6.2 round `r`'s batch: "round `r` grades read only `Σ.sg_votes[r−1]`"
(PROTOCOL.md `def:grades`).

`Round = ℕ`, so `r − 1` truncates; the guard is what makes "round 0 has an empty
batch and no grades" (PROTOCOL.md `def:grades`) hold instead of reading
round 0's own pool. -/
def round_batch (gv : GradeView V) (r : Round) : Finset (SGVote V) :=
  if r = 0 then ∅ else gv.sg_votes (r - 1)

/-- §6.2 the tie-break on equal timestamps, as modeling-choices row 2 fixes it:
the fixed root order of PROTOCOL.md `sec:substrate`, with `⊥` least (F6.3). -/
def head_lt : Option BlockId → Option BlockId → Bool
  | none, none => false
  | none, some _ => true
  | some _, none => false
  | some left, some right => decide (left < right)


/-- §6.2 the batch order: by timestamp, ties by head (PROTOCOL.md `def:grades`).

An unstamped vote sorts last. The pool never holds one — every pooled vote is
stamped on insertion (PROTOCOL.md `sec:substrate`, PROTOCOL.md `alg:sg-store`)
— but the map is partial
(modeling-choices row 10), so the order has to be total anyway, and "never
processed" is the same `+∞` the summary gives an absent vote. -/
def batch_before (ts : TimestampMap (SGVote V)) (left right : SGVote V) : Bool :=
  match ts left, ts right with
  | none, none => head_lt left.confirmed right.confirmed
  | none, some _ => false
  | some _, none => true
  | some x, some y =>
    decide (x < y) || (decide (x = y) && head_lt left.confirmed right.confirmed)


/-- §6.2 whether no member of `batch` comes before `u` in the batch order. -/
def is_first_in (ts : TimestampMap (SGVote V)) (batch : Finset (SGVote V))
    (u : SGVote V) : Bool :=
  decide (∀ w ∈ batch, batch_before ts w u = false)


/-- §6.2 "`v`'s first vote" under the batch order (PROTOCOL.md `def:grades`).

Inside one round's pool, the votes of one validator differ exactly in their head,
so the order is a strict total order on them and the minimum is unique. `none` is
returned on an empty set — and, mirroring modeling-choices row 16, on a
degenerate set where the order fails to decide. Computable and choice-free, like
`Block.deepest?` and `Protocol.argmax?`. -/
def batch_first? (ts : TimestampMap (SGVote V)) (batch : Finset (SGVote V)) :
    Option (SGVote V) :=
  pickUnique? batch (is_first_in ts batch)

/-- §6.2 `e_v`: "the time at which the pool first holds two of `v`'s votes with
distinct confirmed blocks, an empty value included — the receipt timestamp of the
second — or `+∞` when it never does" (PROTOCOL.md `def:grades`).

Read off the receipt-earliest vote and the receipt-earliest vote whose confirmed
block differs from it. That is exactly the stated instant: if some pair `(u, w)`
with distinct confirmed blocks coexists by time `m`, one of the two already
differs from the receipt-earliest vote and is stamped at or before `m`, so
pairing *it* with the earliest vote is no later. Both selections are
`batch_first?`, so no fold over pairs is needed and the term stays choice-free.

**It reads the receipt clock and no tree.** That is the τ fold's split, and it is
also what makes the equivocation instant tree-independent — the property
`Proofs.HealingLemmas.Grades.summary_e_v_none_of_sole` relies on. It is stated apart
from `summary` for the same reason: `.e_v` must reduce without unfolding
anything that mentions `Σ.T`. -/
def equivocation_instant (ts : TimestampMap (SGVote V))
    (batch : Finset (SGVote V)) : Occurrence :=
  match batch_first? ts batch with
  | none => none
  | some first =>
    match batch_first? ts (batch.filter (fun u => u.confirmed ≠ first.confirmed)) with
    | none => none
    | some second => ts second


/-- §6.2 the per-validator batch summary `(C_v, t_v, e_v)`
(PROTOCOL.md `def:grades`).

**The two marks read different clocks**, and the τ fold is what split them.
`(C_v, t_v)` is a **resolution** reading: "the confirmed block of `v`'s first
resolved vote naming one, in resolution-time order, and `t_v` that resolution
time". `e_v` is a **receipt** reading: "the time at which the pool first holds
two of `v`'s votes with distinct confirmed blocks, an empty value included — the
receipt timestamp of the second". So a vote that never resolves still convicts
its caster, and only a resolved vote can support a block. -/
structure BatchSummary where
  /-- §6.2 `C_v`: the confirmed block of `v`'s first resolved vote naming one,
  or `⊥`. -/
  C_v : Option BlockId
  /-- §6.2 `t_v`: that vote's **resolution** time, or `+∞`. -/
  t_v : Occurrence
  /-- §6.2 `e_v`: the **receipt** timestamp at which the pool first holds two of
  `v`'s votes with distinct confirmed blocks, the empty value included, or
  `+∞`. -/
  e_v : Occurrence


/-- §6.2 the batch summary of `v` in round `r` (PROTOCOL.md `def:grades`).

`(C_v, t_v) = (⊥, +∞)` when `v` casts no resolved vote naming a block
(modeling-choices row 1, F6.2). An **unresolved** vote is one of the ways that
happens, and it is the τ fold's addition: such a validator supplies no direct
support at any cutoff, yet its `e_v` still fires if it cast a second vote.

`e_v` is read off the receipt-earliest vote and the receipt-earliest vote whose
confirmed block differs from it. That is exactly "the time at which the pool
first holds two of `v`'s votes with distinct confirmed blocks": if some pair
`(u, w)` with distinct confirmed blocks coexists by time `m`, one of the two
already differs from the receipt-earliest vote and is stamped at or before `m`,
so pairing *it* with the earliest vote is no later. Both are `batch_first?`
selections, so no fold over pairs is needed and the term stays choice-free.

Nothing forces `t_v < e_v`: a `⊥`-confirmed vote received before `v`'s first
block-naming vote resolves makes `e_v < t_v` (F6.1). Such a validator supplies no
direct support at any cutoff but does land in `favorable_support`'s second set.
The τ fold widens that gap — `t_v` can now sit arbitrarily far after the receipt
of the same vote — which is why the two marks are separate fields and why only
`e_v` is called immutable. -/
def summary (gv : GradeView V) (r : Round) (v : V) : BatchSummary :=
  let batch := Protocol.sg_votes_by (round_batch gv r) v
  let τ := Protocol.sg_resolution_time gv.T gv.timestamp_block gv.timestamp_sg_vote
  let headed := batch_first? τ (batch.filter (fun u =>
    u.confirmed.isSome ∧ Protocol.sg_resolved gv.T u = true))
  { C_v := headed.bind SGVote.confirmed
    t_v := headed.elim none τ
    e_v := equivocation_instant gv.timestamp_sg_vote batch }

/-! ## Support (PROTOCOL.md `def:grades`) -/

/-- §6.2 `direct_support(Σ, r, Γ_h, Γ_e, B)`
`= w({v ∈ V: t_v < Γ_h, B ⪯ C_v, e_v ≥ Γ_e})` (PROTOCOL.md `alg:grades`).

"Direct support deletes equivocators, as `sg_support` does"
(PROTOCOL.md `def:grades`, "Direct support deletes equivocators"): the
`e_v ≥ Γ_e` clause is what drops a validator whose head changed before the
cutoff. -/
def direct_support (E : Env V) (gv : GradeView V) (r : Round) (Γ_h Γ_e : Time)
    (B : Block V) : Nat :=
  E.electorate.weightOf (Finset.univ.filter (fun v =>
    let s := summary gv r v
    occurrenceBefore s.t_v Γ_h = true ∧ head_covers gv.T B s.C_v = true ∧
      occurrenceAtLeast s.e_v Γ_e = true))

/-- §6.2 `favorable_support(Σ, r, Γ, B)`
`= w({v ∈ V: t_v < Γ, B ⪯ C_v} ∪ {v ∈ V: e_v < Γ})` (PROTOCOL.md `alg:grades`).

"Favorable support credits them, as `goldfish_score` does"
(PROTOCOL.md `def:grades`, "favorable support credits them"): the second set
is independent of `B`, so a validator whose head changed before `Γ` is
credited on every branch — which is why favorable grades can conflict
(PROTOCOL.md `sec:grades`).

The union of two subsets of `V` is one filter over `Finset.univ` rather than a
`Finset.union`: the two spell the same set, and `Finset.union` drags
`Classical.choice` into a term the fork choice reads. -/
def favorable_support (E : Env V) (gv : GradeView V) (r : Round) (Γ : Time)
    (B : Block V) : Nat :=
  E.electorate.weightOf (Finset.univ.filter (fun v =>
    let s := summary gv r v
    (occurrenceBefore s.t_v Γ = true ∧ head_covers gv.T B s.C_v = true) ∨
      occurrenceBefore s.e_v Γ = true))

/-- §6.2 `G2(B) ⟺ direct_support(Σ, r, Γ_r^{−1}, Γ_r^2, B) ≥ m`
(PROTOCOL.md `alg:grades`, "G2"). The height-pair grade. -/
def G2 (E : Env V) (gv : GradeView V) (hc : HealConfig) (r : Round)
    (B : Block V) : Bool :=
  decide (E.m ≤ direct_support E gv r (hc.Γ_neg1 E.Δ r) (hc.Γ_2 E.Δ r) B)

/-- §6.2 `G1(B) ⟺ direct_support(Σ, r, Γ_r^0, Γ_r^0, B) ≥ m`
(PROTOCOL.md `alg:grades`, "G1"). The anchor grade. -/
def G1 (E : Env V) (gv : GradeView V) (hc : HealConfig) (r : Round)
    (B : Block V) : Bool :=
  decide (E.m ≤ direct_support E gv r (hc.Γ_0 E.Δ r) (hc.Γ_0 E.Δ r) B)

/-- §6.2 `G0(B) ⟺ favorable_support(Σ, r, Γ_r^1, B) ≥ m`
(PROTOCOL.md `alg:grades`, "G0"). The veto grade. -/
def G0 (E : Env V) (gv : GradeView V) (hc : HealConfig) (r : Round)
    (B : Block V) : Bool :=
  decide (E.m ≤ favorable_support E gv r (hc.Γ_1 E.Δ r) B)


/-- §6.2 `g0_clear(Σ, r, B)` (PROTOCOL.md `G0_conflict_free`): no processed
block stamped before the freeze `Γ_r^1` conflicts with `B` and holds grade 0.

**The range is `Σ.T`, every processed block, since ** — not the
filtered tree. See the block comment above: the veto is the one negative use of
a grade, and restricting it to active blocks let a conflicting grade-1 block
outside the band escape the source's test and then anchor another reader.

**Both the freeze and the veto window moved from `Γ_r^2` to `Γ_r^1`** with the
 replacement of §6. Grade 1 closes earlier, at `Γ_r^0`. Grade 2 is
swept through `Γ_r^2`; under graded delivery, that extra window is what makes
a grade-2 block never vetoed in any honest store (PROTOCOL.md, "Grades").

Only the block filter is frozen: "a block learned after the freeze never becomes
a veto". `G0` itself resolves against the **live** store. That is sound under
the τ fold and it was not before:
`G0` is `favorable_support(Γ_r^1)`, whose first set requires `t_v < Γ_r^1`, and
`t_v` is a **resolution** time, so a vote inside the cutoff has its confirmed
block processed by construction rather than by a delivery contract
(PROTOCOL.md `sec:goldfish-store`, PROTOCOL.md `sec:grades`). The second
set is independent of the block and needs no resolution at all.

The argument `B` is used for the conflict test alone and is not required to be in
the tree (F6.13); genesis is always clear, because nothing conflicts with it.

The figure's `vetoes = ∅` is spelled `vetoes.card = 0`: `Finset`'s `DecidableEq`
instance reports `Classical.choice`, and this test gates the SG vote and the
height-pair source the graded action emits. -/
def g0_clear (E : Env V) (gv : GradeView V) (hc : HealConfig) (r : Round)
    (B : Block V) : Bool :=
  let freeze := hc.Γ_1 E.Δ r
  let vetoes := gv.T.filter (fun B' =>
    stampedBefore gv.timestamp_block freeze B' = true ∧
      Block.conflicts B' B = true ∧
      G0 E gv hc r B' = true)
  decide (vetoes.card = 0)

/-! ## The fresh SG root (PROTOCOL.md `sec:fresh-anchor`, `alg:fresh-anchor`) -/

/-- §6.4 the fresh SG root: "the deepest block of the filtered tree with
grade 1" (PROTOCOL.md `sec:fresh-anchor`).
This named projection is the first branch of §6's `get_sg_root`
(PROTOCOL.md `alg:fresh-anchor`). The anchor lemmas of
`Proofs/Optimistic/Anchor.lean` and the grade layer state facts about the fresh
branch specifically, so the model keeps the name, the same way `fg_source`
names `get_fg_vote`'s internal `C_fg`.
**Non-strict, and the root is in range.** The selection computes no root of its
own: the filtered tree already carries `root ⪯ ·`, so the anchor is a plain
deepest-with-`G1` over that tree.
Three things the document is explicit about, and the model keeps all three.
* **The rationale is the graded anchor, not strictness.** A fresh SG root is a
  grade-1 block in the reading store. Under the graded-delivery conditions, by
  `Γ_r^1` it has grade 0 at each honest store whose filtered tree contains it;
  at every other store it is inactive (PROTOCOL.md `sec:fresh-anchor`). The
  veto lets a validator on the relative path protect such an active fresh SG
  root even when it is not that validator's selected root
  (PROTOCOL.md `sec:fresh-anchor`).
  Thus, the ordering is a safety-source ordering, like the SG vote's fallback
  tiers. The protection is conditional on membership in the receiver's filtered
  tree. It is not an unconditional veto at every honest store.
  The low-participation worry is **void**, and that is what closes the question:
  `G1` needs `m` of *total* stake, not of participating stake, so no
  participation means no grades, `fresh_anchor` is `⊥`, and §6 reduces exactly to
  the relative machinery of §§2–5. There is no regime in which a thinly-supported
  root displaces a well-supported relative anchor.
* **Nothing is stored.** the previous version looked up `Σ.fresh_root[r]` and re-ran
  two tests against it. This version runs the selection at each call. For each
  fixed block, its grade-1 predicate is fixed from `Γ_r^0` through the rest of
  the round (PROTOCOL.md `sec:fresh-anchor`). This is a property of the
  marks, not of a cache.
* **"Deepest" is well defined** because conflicting blocks cannot both hold
  grade 1 (PROTOCOL.md `sec:grades`, `sec:fresh-anchor`): grade 1 is
  *direct*, where it is favorable. The root-order tie-break of
  PROTOCOL.md `sec:substrate` is still what makes the selection a function
  in the model, since `Block.deepest?` ranges over a tree rather than a chain
  (F6.6).
The range is **the same as `Protocol.grade2_block`'s**, differing only in the
grade. `G2 ⟹ G1` then gives `Q₂ ⪯ fresh_anchor` as a within-store chain fact
(`Proofs.HealingLemmas.Grades.grade2_preceq_fresh_anchor`), where under the strict
version it needed a case split on `Q₂ = root`.
The opening proposer's head reads this before `Γ_r^1`, "with the cutoff
predicates reading the evidence held so far; that read only steers its proposal"
(PROTOCOL.md#the-complete-protocol). The model needs no case for it: the marks are read
live either way. -/
def fresh_anchor (E : Env V) (hc : HealConfig) (st : HealingStore V) (r : Round) :
    Option (Block V) :=
  Block.deepest? ((Protocol.get_filtered_block_tree st.toFG).filter
    (fun B => G1 E st.gradeView hc r B = true))


/-- The round's stable-record root under the inactive absolute-grade contract: the deepest G2
block of the CANDIDATE tree, or the FG root when that projection is empty
(addendum 34 29,; range fixed by 26).
Named rather than inlined so that `grade_default%`'s unfolding of
`currentGradeRead` stays symmetric.

The stable record follows CONFIRMATION'S VIABILITY RULE, the whole of it:
`get_filtered_block_tree` is the viable tree filtered by `get_fg_root ⪯ B`, so
the record only ever takes a G2 root that the node's own fork choice can walk
to from its own FG root. This is the same range as the SG candidate `Q2`, and
that is the point of 26: the two records are then ordered by
construction, and `update_confirmation_with` floors the confirmation record on
this one.

The stable write never empties. When the projection is empty, the FG root is
written; `advance_confirmed` keeps the record when that root is an ancestor of
the prior value, so the fallback never retracts it. Finality is included because
the FG root is `J` at the justified height and `F` otherwise. -/
def current_stable_root (E : Env V) (hc : HealConfig) (st : HealingStore V)
    (r : Round) : Option (Block V) :=
  some (match Block.deepest? ((Protocol.get_filtered_block_tree st.toFG).filter
      (fun B => G2 E st.gradeView hc r B = true)) with
    | some G => G
    | none => Protocol.get_fg_root st.toFG)

/-- The inactive absolute-grade read, with the original predicates and cutoffs. -/
def currentGradeRead (E : Env V) (hc : HealConfig) (st : HealingStore V)
    (r : Round) : GradeRead V where
  anchor :=
    match fresh_anchor E hc st r with
    | some A => A
    | none =>
      let root := Protocol.get_fg_root st.toFG
      let tree := Protocol.get_filtered_block_tree st.toFG
      if (st.T.filter (fun B => G1 E st.gradeView hc r B = true)).Nonempty then root
      else Protocol.majority_fork_choice E st.sg_votes hc.η_SG st.T root tree r
  Q2 := Block.deepest? ((Protocol.get_filtered_block_tree st.toFG).filter
    (fun B => G2 E st.gradeView hc r B = true))
  clear := fun B => g0_clear E st.gradeView hc r B
  rawG2 := (st.T.filter (fun B => G2 E st.gradeView hc r B = true)).Nonempty
  rawG2_decidable := inferInstance

/-- The inactive absolute-grade reference contract. -/
def GradeContract.current : GradeContract V where
  read := currentGradeRead
  sgVote := currentSGVote
  confirmationSG := .optional (fun E hc st _ =>
    some (currentSGVote st (currentGradeRead E hc st (hc.round_of st.s))))
  stableRoot := current_stable_root

/-- The inactive absolute-grade reference instance of `grade2_block_with`. -/
def grade2_block (E : Env V) (hc : HealConfig) (st : HealingStore V) (r : Round) :
    Option (Block V) :=
  grade2_block_with GradeContract.current E hc st r

/-- The inactive absolute-grade reference instance of `fg_source_with`. -/
def fg_source (E : Env V) (hc : HealConfig) (st : HealingStore V) (r : Round)
    (A_G2 : Option (Block V)) : Option (Block V) :=
  fg_source_with GradeContract.current E hc st r A_G2

/-- §6.4 `get_sg_root(Σ, r)`, the **§6 redefinition** (PROTOCOL.md `alg:fresh-anchor`):
the fresh SG root when one exists, §5's relative-majority body otherwise. The
first branch is the figure's inline selection, kept model-side as the named
projection `fresh_anchor` (`Anchor.lean`) so the anchor lemmas can state facts
about it.

The two are alternatives, never composed: the walk runs once, from whichever is
selected. `sg_support`'s ancestry argument stays `Σ.T`, as at §3 and §5 (F3.2,
choices S3.5, S5.6).

**Do not "improve" this to the deeper of the two.** Taking
`deeper (fresh_anchor, majority_fork_choice)` is the obvious-looking composition
and it was considered and **rejected** (`the design` §9, degradation
audit): it leaves ungraded anchors in play while grades exist, which breaks the
uniform graded-anchor property the round action's safety argument runs on. An
anchor in use at an honest validator is a grade-1 block of its store. Under the
graded-delivery conditions, by `Γ_r^1` it holds grade 0 in each honest store
whose filtered tree contains it; at every other store it is inactive
(PROTOCOL.md `sec:fresh-anchor`). Gradedness is a safety property; depth is
not.

The accepted cost of that choice is recorded too, and it is narrow: in the band
where participation is `≥ m`, current votes are dispersed, and a
sleeper-stale-backed relative chain is deeper — roughly `p ∈ (1/2, 2/3)` — the
grade takes **one round** of precedence over the deeper relative anchor. That is
transient, and it is the intended fresh-precedence rather than a defect.

When no block holds a round-`(r−1)` grade this is §5's `get_sg_root`
syntactically, which is the fork-choice half of the zero-grade reduction —
now **by construction** in the tex, since §6 redefines only this body. -/
def get_sg_root (E : Env V) (hc : HealConfig) (st : HealingStore V) (r : Round) :
    Block V :=
  get_sg_root_with GradeContract.current E hc st r

/-- §5.2 `get_head_in_tree_hc(Σ, tree, votes, support_votes, k)` at §6's
`get_sg_root`: the final explicit-tree composed head.

The supplied `tree` is only the Goldfish walk's candidate tree.
`get_sg_root` still reads the ordinary full-store filtered tree, and score and
eligibility resolution still read `Σ.T` with the unchanged store fields. -/
def get_head_in_tree_hc (E : Env V) (hc : HealConfig) (st : HealingStore V)
    (tree : Finset (Block V)) (votes support_votes : Finset (GoldfishVote V))
    (k : Slot) : Block V :=
  get_head_in_tree_with_layer GradeContract.current E hc st tree votes support_votes k

/-- §5.2 `get_head_hc(Σ, votes, support_votes, k)` at §6's `get_sg_root`: the
ordinary full-tree composed head. It computes the full-store candidate tree and
delegates to `get_head_in_tree_hc`.

The document late-binds `get_sg_root`; this wrapper and the explicit-tree body
above provide that binding for Lean without changing the §5 Goldfish walk. -/
def get_head_hc (E : Env V) (hc : HealConfig) (st : HealingStore V)
    (votes support_votes : Finset (GoldfishVote V)) (k : Slot) : Block V :=
  get_head_with GradeContract.current E hc st votes support_votes k

end Protocol

namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- §6.4 `get_head_in_tree(Σ, tree, votes, support_votes, k)` at the cumulative
store. It projects to §6's explicit-tree head. The supplied tree changes only
the Goldfish child domain; the SG anchor, score resolution, and eligibility
inputs remain the full store. -/
def get_head_in_tree (E : Env V) (hc : Protocol.HealConfig) (st : Store V)
    (tree : Finset (Block V)) (votes support_votes : Finset (GoldfishVote V))
    (k : Slot) : Block V :=
  get_head_in_tree_with Protocol.GradeContract.current E hc st tree votes support_votes k

/-- §6.4 `get_head(Σ, votes, support_votes, k)` at the cumulative store: the
ordinary full-tree wrapper through the §6 projection.

"At slot 0 the head is genesis" (PROTOCOL.md `sec:public-handlers`) needs no clause, but
not because the current-slot eligibility clause is false. It holds from
`Store.init`, whose `Σ.T` is `{B_gen}`, so the walk has no child to descend
to. -/
def get_head (E : Env V) (hc : Protocol.HealConfig) (st : Store V)
    (votes support_votes : Finset (GoldfishVote V)) (k : Slot) : Block V :=
  get_head_in_tree_with Protocol.GradeContract.current E hc st
    (Protocol.get_filtered_block_tree st.toHealing.toFG) votes support_votes k

end Protocol

namespace Internal

open Protocol (HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- §7.2 the store the tick's duties run against, after the time write
(PROTOCOL.md#the-complete-protocol). -/
def tick_store (E : Env V) (st : Protocol.Store V) (t : Time) : Protocol.Store V :=
  { st with t := t, s := E.slotOf t }

end Internal
end DecoupledConsensusModel

end
