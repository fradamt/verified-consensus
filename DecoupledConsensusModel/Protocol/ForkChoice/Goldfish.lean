module
public import Mathlib.Data.Prod.Lex
public import DecoupledConsensusModel.Protocol.StoreBase
public import DecoupledConsensusModel.Protocol.Schedule
public import DecoupledConsensusModel.Protocol.ForkChoice.Views
public import DecoupledConsensusModel.Protocol.ChainState

@[expose] public section

/-!
# `DecoupledConsensusModel/Protocol/ForkChoice/Goldfish.lean`

Purpose: Section 7, block 2a — goldfish_score, ghost, the SG and FG store layers, viable_tree, get_fg_root, get_filtered_block_tree, goldfish_eligible, goldfish_fork_choice.
Paper: `docs/PROTOCOL.md` `sec:complete-store`; algorithm block: `alg:goldfish` / `alg:fg-store`.

Defines: raw_equivocators, raw_participants, raw_voters_count, voters_count, targets_under, raw_supporters, raw_goldfish_score, goldfish_score, outranks, is_best_in, argmax?, ghost_children, ghost_step, ghost_walk, ghost, no_second_vote_in, SGVote, Store, latest_window, HeightId, HeightId.rank_injective, finalized_descendants, viable, viable_tree, get_fg_root, get_filtered_block_tree_from, get_filtered_block_tree, goldfish_eligible, goldfish_fork_choice.

Read after: `DecoupledConsensusModel.Protocol.StoreBase`, `DecoupledConsensusModel.Protocol.Schedule`, `DecoupledConsensusModel.Protocol.ForkChoice.Views`
Read next: `DecoupledConsensusModel.Protocol.ForkChoice.Head`.

State read: the protocol environment, schedule, store layers, and the view inputs named by the definitions.
State written: the returned store, chain state, record, or view value; pure readers write no state.

Representation notes: Typed Lean records, finite collections, and projections preserve the executable protocol representation. This module states no proof theorem.
MODEL_MAP rows: raw_equivocators, raw_participants, raw_voters_count, voters_count, targets_under, raw_supporters, raw_goldfish_score, goldfish_score, outranks, is_best_in, argmax?, ghost_children, ghost_step, ghost_walk, ghost, no_second_vote_in, SGVote, Store, latest_window, HeightId, HeightId.rank_injective, finalized_descendants, viable, viable_tree, get_fg_root, get_filtered_block_tree_from, get_filtered_block_tree, goldfish_eligible, goldfish_fork_choice.
-/

-- ── from Goldfish/ForkChoice.lean ──
section
/-!
# §2.4 Goldfish fork choice
(PROTOCOL.md `sec:one-slot-ghost`, `def:goldfish-walk`, `alg:goldfish`)

`sec:one-slot-ghost`, `def:goldfish-walk`, `alg:goldfish`.

The pure core of the section: the score, the walk, the gate, and the two
compositions. `ghost` takes `score` and `eligible` as plain function arguments,
so the same walk serves the Goldfish fork choice, the §3 majority fork choice and
available confirmation (conventions: "pure core, thin stores").

Two model-forced parameters appear in front of the document's argument lists.

* `T`, the tree ancestry is resolved in. Votes name their target by root, so `B ⪯ B'` needs a tree to turn `vote.head` into
  `B'`. It is `Σ.T` at every §2 call site, and is kept separate from the `tree`
  the walk descends — the same split §3 states explicitly for `sg_support`
  (PROTOCOL.md `def:majority-fork-choice`,
  "still supports the child through which it descends").
* `cur`, the current slot `Σ.s`, read only by `goldfish_eligible`'s second
  clause.

The active counts quantify over every validator represented in the supplied
vote sets. Their `E` and `s` arguments remain in the public API so downstream
call sites do not need an unrelated signature migration. Committee membership
is enforced when a vote enters the pool, not repeated in these calculations.

The `committee_*` definitions are committee-filtered proof helpers. They agree
with the raw forms
when the input is slot-uniform and every voter belongs to `K_s`.
-/

namespace DecoupledConsensusModel
namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

namespace VoteSetValid

end VoteSetValid

/-- The source-exact equivocator set: no committee filter is applied here. -/
def raw_equivocators (votes : Finset (GoldfishVote V)) : Finset V :=
  Finset.univ.filter (fun v => equivocates votes v = true)

/-- The source-exact participant set: every validator represented in `votes`. -/
def raw_participants (votes : Finset (GoldfishVote V)) : Finset V :=
  Finset.univ.filter (fun v => participates votes v = true)

/-- The source-exact participant count. -/
def raw_voters_count (votes : Finset (GoldfishVote V)) : Nat :=
  (raw_participants votes).card

/-- The active source-exact participant count. -/
def voters_count (_E : Env V) (votes : Finset (GoldfishVote V)) (_s : Slot) : Nat :=
  raw_voters_count votes

/-! ## Score (PROTOCOL.md `def:goldfish-walk`) -/

/-- §2.4 whether `vote`'s target resolves in `T` to a block descending from `B`,
i.e. the `B ⪯ B'` of the supporter test (PROTOCOL.md `def:goldfish-walk`,
"holds a vote whose head descends from").

A target that `T` does not resolve supports nothing. Under the
dependency-complete contract a pooled vote's target is always in the store
(PROTOCOL.md `sec:goldfish-store`, "a vote is resolved when it does"), but
a vote carried by a proposal need not be, and
the model may not use choice or panic on it. -/
def targets_under (T : Finset (Block V)) (B : Block V) (vote : GoldfishVote V) :
    Bool :=
  match Block.find? T vote.head with
  | some B' => decide (B'.slot ≤ vote.slot) && Block.preceq B B'
  | none => false

/-- The source-exact supporter set: no committee filter is applied here. -/
def raw_supporters (T : Finset (Block V))
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (B : Block V) :
    Finset V :=
  Finset.univ.filter (fun v =>
    equivocates votes v = false ∧
    ∃ vote ∈ votes_by support_votes v, vote.slot = s ∧ targets_under T B vote = true)

/-- The source-exact Goldfish score, over all represented validators. -/
def raw_goldfish_score (T : Finset (Block V))
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (B : Block V) : Nat :=
  (raw_equivocators votes).card + (raw_supporters T votes support_votes s B).card

/-- The active source-exact Goldfish score.

An equivocator counts for every block and stays among the participants, so it
can neither create nor block a descent. A non-equivocating validator counts
once, in one subtree (PROTOCOL.md `def:goldfish-walk`,
"counts once, in one subtree"). `E` remains only as a compatibility
parameter. -/
def goldfish_score (_E : Env V) (T : Finset (Block V))
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) (B : Block V) : Nat :=
  raw_goldfish_score T votes support_votes s B

/-! ## The walk (PROTOCOL.md `alg:goldfish`) -/

/-- §2.4 the `argmax` order of the walk: higher score wins, ties by the fixed root
order (PROTOCOL.md `alg:goldfish`, "ties by root order"). `outranks score B C`
says `B` beats `C`; the
greatest root wins a tie, as in `Block.deeper`. -/
def outranks (score : Block V → Nat) (B C : Block V) : Bool :=
  decide (score C < score B) ||
    (decide (score C = score B) && decide (C.root < B.root))

/-- §2.4 whether no member of `children` beats `B`
(PROTOCOL.md `alg:goldfish`, "ties by root order"). -/
def is_best_in (score : Block V → Nat) (children : Finset (Block V))
    (B : Block V) : Bool :=
  decide (∀ C ∈ children, outranks score C B = false)

/-- §2.4 `argmax_{B ∈ children} score(B)`, ties by root order
(PROTOCOL.md `alg:goldfish`, "ties by root order"). `none` on an empty set of
children, and on the
degenerate tie where two distinct children share a score *and* a root — a tree
outside the document, where the stated tie-break does not decide. Computable and
choice-free, like `Block.deepest?`. -/
def argmax? (score : Block V → Nat) (children : Finset (Block V)) :
    Option (Block V) :=
  pickUnique? children (is_best_in score children)

/-- §2.4 the eligible children of `H` in `tree` (PROTOCOL.md `alg:goldfish`). The child edge comes from the full parent relation and membership in
`tree` is tested on the child only, so a walk may descend out of an anchor that
`tree` does not hold (PROTOCOL.md `alg:goldfish`). `parent?` rather than the
total `parent` is what keeps genesis from being its own child. -/
def ghost_children (tree : Finset (Block V)) (eligible : Block V → Bool)
    (H : Block V) : Finset (Block V) :=
  tree.filter (fun B => B.parent? = some H ∧ eligible B = true)

/-- §2.4 one step of the walk: the argmax over the eligible children, or `none`
where the loop returns `H` (PROTOCOL.md `alg:goldfish`). -/
def ghost_step (tree : Finset (Block V)) (score : Block V → Nat)
    (eligible : Block V → Bool) (H : Block V) : Option (Block V) :=
  argmax? score (ghost_children tree eligible H)

/-- §2.4 the fuelled descent (PROTOCOL.md `alg:goldfish`). Returns the current head on
both "no eligible child" and fuel exhaustion. -/
def ghost_walk (tree : Finset (Block V)) (score : Block V → Nat)
    (eligible : Block V → Bool) : Nat → Block V → Block V
  | 0, H => H
  | n + 1, H =>
    match ghost_step tree score eligible H with
    | none => H
    | some C => ghost_walk tree score eligible n C

/-- §2.4 `ghost(anchor, tree, score, eligible)`: descend from `anchor` through
eligible children in `tree`, taking the highest score at each step, and stop
where no child is eligible (PROTOCOL.md `def:goldfish-walk`,
"open items where no child is eligible").

Termination is not argued in the document. Fuel is `tree.card`: every step
after the first moves to a member of `tree` of strictly greater depth, so no
member is visited twice and the walk cannot outlast the tree. -/
def ghost (anchor : Block V) (tree : Finset (Block V)) (score : Block V → Nat)
    (eligible : Block V → Bool) : Block V :=
  ghost_walk tree score eligible tree.card anchor

end Protocol
end DecoupledConsensusModel
end

-- ── from Goldfish/Confirmation.lean ──
section
/-! §2 vote-cleanliness predicate used by the complete confirmation walk. -/

namespace DecoupledConsensusModel
namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- §2.6 whether `late` holds no second distinct vote by `vote`'s validator
(PROTOCOL.md `alg:confirmation`).

Stated literally, over `late` rather than as a count: `early ⊆ late` is a stated
property (PROTOCOL.md `sec:available-confirmation`,
"equivocates in late_votes too"), not a hypothesis this test may
assume. -/
def no_second_vote_in (late : Finset (GoldfishVote V)) (vote : GoldfishVote V) :
    Bool :=
  decide (∀ u ∈ late, u = vote ∨ u.val_index ≠ vote.val_index)

end Protocol
end DecoupledConsensusModel
end

-- ── from MajoritySG/Objects.lean ──
section
/-!
# §3.1 Rounds and SG votes — `sec:sg-schedule` (PROTOCOL.md `sec:sg-schedule`)

The round grid, this layer's fixed parameters, the SG vote, and the vote-set
vocabulary that both the store handler and the majority fork choice read.

Three shapes are forced here.

* **The SG vote is a bare triple** `(validator, round, confirmed)` at this layer
  (PROTOCOL.md `sec:sg-schedule`). §7 retypes the pool to hold combined
  attestations and reads their `(validator, round, confirmed)` projection
  instead (PROTOCOL.md `sec:complete-store`). A Lean `extends` chain cannot
  retype a field, so every SG-facing function below takes the *pool
  projection* `Round → Finset (SGVote V)` as an argument and never a store
  type. §7 supplies its own projection into the
  same functions.
* **`R`, `η_SG` and `a_r` are a parameter structure.** `a_r` is "a public
  parameter" with no stated relation to round `r`'s slots at this layer
  (PROTOCOL.md `sec:sg-schedule`); §6 fixes `a_r = t_{rR} + 6Δ`
  (PROTOCOL.md `sec:healing-schedule`). It stays free here, as the document
  writes it.
* **`confirmed` is `Option BlockId`.** The confirmed block is a block or `⊥`
  (PROTOCOL.md `sec:sg-schedule`), and wire objects name blocks by root; consumers resolve the root through a tree.

`SGVote` is the §3 layer's own wire object, so — unlike `GoldfishVote` and
`CombinedAttestation` — it is *not* in the substrate: no `Block` field carries
it. "SG votes travel only on the wire. Blocks do not carry them, and they never
enter a Goldfish vote set" (PROTOCOL.md `sec:sg-store`).
-/

namespace DecoupledConsensusModel
namespace Protocol

/-- §3.1 an SG vote `(v, r, C)` from validator `v` with confirmed block `C`, a
block or `⊥` (PROTOCOL.md `sec:sg-schedule`).

At `a_r` an honest validator votes its current `live_confirmed`, which is a
block; the empty value appears only in **adversarial** votes
(PROTOCOL.md `sec:sg-schedule`, `sec:healing-action`). The graded protocol
has no honest empty-confirmed path either. The confirmed block is carried by root.

The fork-choice helpers resolve this root against the processed tree. -/
structure SGVote (V : Type) where
  /-- §3.1 `vote.val_index`, an element of `V`
  (PROTOCOL.md `sec:sg-schedule`, `sec:sg-store`). -/
  val_index : V
  /-- §3.1 `vote.round` (PROTOCOL.md `sec:sg-schedule`). -/
  round : Round
  /-- §3.1 `vote.confirmed`: a block, by root, or `⊥`
  (PROTOCOL.md `sec:sg-schedule`). -/
  confirmed : Option BlockId
deriving DecidableEq, Repr

end Protocol
end DecoupledConsensusModel
end

-- ── from MajoritySG/Store.lean ──
section
/-!
# §3.2 Store — `sec:sg-store` (PROTOCOL.md `sec:sg-store`)

"This layer adds one field: `Σ.sg_votes[r]`, the set of processed round-`r` SG
votes" (PROTOCOL.md `sec:sg-store`). The store is therefore §2's store plus
that field — the first link of the `extends` chain §2 → §3 → §5 → §6.

Two shapes are forced.

* The pool "is timestamped" (PROTOCOL.md `sec:sg-store`). §2 already split
  the document's single `timestamp[·]` into one typed map per object kind,
  because Lean has no untyped key; the SG vote is a third
  kind, so it gets a third fibre, `timestamp_sg_vote`.
* `sg_votes[r]` is a `Finset`, not a `List`. `gf_votes[k]` had to be a list
  because a proposal copies it and `Finset.toList` is noncomputable; nothing copies the SG pool, and the document calls it a set.
-/

namespace DecoupledConsensusModel
namespace Protocol

/-- §3.2 the §3 store: §2's seven components plus `Σ.sg_votes[·]`
(PROTOCOL.md `sec:sg-store`).

`Σ.sg_votes[r]` keeps at most two distinct votes per validator, "which is all
any rule reads"; the cap is enforced by `on_sg_vote`, not by the type
(PROTOCOL.md `sec:sg-store`). A total map over all rounds with the empty
default: `η_SG` makes old rounds unreadable but the document states no
pruning rule. -/
structure SGStore (V : Type) extends Protocol.GoldfishStore V where
  /-- §3.2 `Σ.sg_votes[r]`: the processed round-`r` SG votes
  (PROTOCOL.md `sec:sg-store`). -/
  sg_votes : Round → Finset (SGVote V)
  /-- §3.2 the SG-vote fibre of `Σ.timestamp[·]` (PROTOCOL.md `sec:sg-store`). No rule of §3 reads it; the grades of §6 do
  (PROTOCOL.md `def:grades`). -/
  timestamp_sg_vote : TimestampMap (SGVote V)

namespace SGStore

variable {V : Type} [DecidableEq V]

end SGStore

end Protocol
end DecoupledConsensusModel
end

-- ── from MajoritySG/ForkChoice.lean ──
section
/-!
# §3.3 Latest votes and majority root (PROTOCOL.md `sec:sg-fork-choice`)

`sec:sg-fork-choice`, `def:majority-fork-choice`, `alg:sg-fork-choice`.

The pure core of the section: the expiry window, the represented weight, the
support weight, and the walk that runs `ghost` with them. "The two walks are the
same function with different scores and gates" (PROTOCOL.md `sec:sg-fork-choice`),
so nothing here re-implements the descent — `Protocol.ghost` takes this score
and this gate.

Every function takes the **pool projection** `pool: Round → Finset (SGVote V)`
rather than a store, because §7 retypes the pool to attestations and reads their
`(validator, round, confirmed)` projection through the same rules
(PROTOCOL.md `sec:complete-store`).

Two model-forced arguments appear in front of the document's lists, as in §2.

* `η_SG`, which the document keeps in the prose rather than in `latest`'s
  argument list (PROTOCOL.md `def:majority-fork-choice`).
* `T`, the tree ancestry is resolved in. The document is explicit that this is
  **not** the walked `tree`: "ancestry is read in the processed block tree `T`,
  so a head
  outside a restricted child tree still supports the child through which it
  descends" (PROTOCOL.md `def:majority-fork-choice`). It doubles as the tree
  that turns a head root into a block.

Counting here is by **weight** over all of `V` (PROTOCOL.md `sec:sg-schedule`),
never by committee cardinality: the two regimes must not be conflated.
-/

namespace DecoupledConsensusModel
namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Latest vote and representation
(PROTOCOL.md `def:majority-fork-choice`, `sec:sg-schedule`) -/

/-- §3.3 the expiry window `[max{0, r−η_SG}, r)`, in ascending order
(PROTOCOL.md `def:majority-fork-choice`, `sec:sg-schedule`).

`Round = ℕ`, so `r − η_SG` is truncated subtraction and already *is*
`max{0, r−η_SG}`; the window's length is then `min r η_SG`. Half-open on the
right, which is what makes a round-`r` vote readable only from round `r+1`
(PROTOCOL.md `sec:sg-schedule`). At `r = 0` it is empty.

A `List` rather than `Finset.Ico`: Mathlib's `LocallyFiniteOrder ℕ` instance
drags `Classical.choice` into every term that mentions it, and `latest` is on
the fork-choice path (conventions: the fork-choice core stays choice-free). -/
def latest_window (η_SG : Round) (r : Round) : List Round :=
  List.range' (r - η_SG) (min r η_SG)

end Protocol
end DecoupledConsensusModel
end

-- ── from FGForkChoice/Finality.lean ──
section
/-!
# §5.1 Stored states and finality updates (PROTOCOL.md `sec:fg-fork-choice`)

The store map `Σ.σ[·]`, the four finality fields, the three derived sets, and
the in-place mutator that maintains them.

Four shapes are forced here.

* **`Σ.σ[·]` is a total map** defaulting to the initial chain state of
  `def:chain-state`. The document writes `σ[·]` only in
  `on_block`, so it is defined exactly on `Σ.T` and never initialized at
  genesis; `on_block` on a child of genesis nevertheless reads
  `Σ.σ[B.parent]` (PROTOCOL.md `alg:fg-store`), and the initial state is the only
  value consistent with the document.
* **`update_finality` mutates sequentially.** Its three statements execute in
  order and each reads the results of the previous one: the viability test uses
  the *new* `h_max` and the *old* `F`, the `σ.F ⪯ Σ.J` test uses the
  possibly-just-updated `Σ.J`, and the final recomputation uses the *new* `F`. Each `let` below is one of the document's
  statements, and the next one reads the store the previous one produced — a
  pre-call snapshot would be a different protocol.
* **`h_max` is monotone.** The finalized-ancestor admission
  rule makes each block that raises the maximum live when it is admitted.
* **The derived sets are pure functions of plain data.** `T_F` and `V` are
  `Σ`-shaped in the document; each has a pure core over `(F, T)` or
  `(σ, h_max, live)` plus a thin store reader, so §6 and §7 feed their own
  fields to the same rules (conventions: "pure core, thin stores"). Nothing is
  cached: "the store does not cache … a live tree, a viable tree, or a filtered
  tree: each is derived when used" (PROTOCOL.md `sec:complete-store`,
  "derived when used").

  Processed finality evidence is not a store field: no protocol rule reads it.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Protocol (ChainState)

/-! ## The justification event and its order (PROTOCOL.md `alg:fg-store`) -/

/-- §5 a justification event `(h_j, J.root)`, the pair `update_finality` compares
lexicographically (PROTOCOL.md `alg:fg-store`).

This is the document's second use of the fixed root order: the first is
`ghost`'s argmax and "deepest" (PROTOCOL.md `sec:substrate`, `alg:goldfish`),
and it is the same total order, applied to `J`'s root rather than to a walk child. -/
@[ext]
structure HeightId where
  /-- The justification height `h_j`. -/
  height : Height
  /-- The justified block's root `J.root`. -/
  id : BlockId
deriving DecidableEq, Repr

private theorem HeightId.rank_injective :
    Function.Injective (fun value : HeightId => (value.height, value.id)) := by
  intro left right equal
  exact HeightId.ext (congrArg Prod.fst equal) (congrArg Prod.snd equal)

/-- §5 the lexicographic `(h_j, J.root)` order (PROTOCOL.md `alg:fg-store`). -/
instance : LinearOrder HeightId :=
  LinearOrder.lift'
    (fun value => toLex (value.height, value.id))
    (fun _ _ equal => by exact HeightId.rank_injective (toLex.injective equal))

/-! ## The store (PROTOCOL.md `sec:fg-fork-choice`) -/

/-- §5.1 the §5 store: §3's store plus the block state map and the four finality
fields (PROTOCOL.md `sec:fg-fork-choice`).

The document lists them as `Σ.σ[·]` and `(Σ.F, Σ.J, Σ.h_j, Σ.h_max)`;
the field order below is that list. "It retains every processed block; the live
tree is derived below the finalized block" (PROTOCOL.md#the-complete-protocol) — `Σ.T` is
never pruned.

The parent projection is named `toSG` rather than left to Lean's default. Lean
flattens an `extends` chain, and `Protocol.SGStore` already carries a field
`toStore` for *its* parent, which the default name for this one would collide
with. §6 must name its parent for the same reason. Field access is unaffected:
`st.T`, `st.sg_votes` and the rest resolve through the chain. -/
structure FGStore (V : Type) extends toSG : Protocol.SGStore V where
  /-- §5.1 `Σ.σ[B]`: the post-state of `B`, written by `on_block`
  (PROTOCOL.md `sec:fg-fork-choice`). Total, with `ChainState.initial` as the
  default. -/
  σ : Block V → ChainState V
  /-- §5.1 `Σ.F`: the store's finalized block (PROTOCOL.md `sec:fg-fork-choice`). -/
  F : Block V
  /-- §5.1 `Σ.J`: the store's justified block (PROTOCOL.md `sec:fg-fork-choice`). -/
  J : Block V
  /-- §5.1 `Σ.h_j`: its height (PROTOCOL.md `sec:fg-fork-choice`). -/
  h_j : Height
  /-- §5.1 `Σ.h_max`: the running maximum state height
  (PROTOCOL.md `sec:fg-fork-choice`). **Monotone** — the field only grows; every block that
  raises it is live at that moment (the admission guard), which is what keeps
  `Σ.F` viable (`Proofs.NamedFinalizedViable.finalizedViable_readAt`). -/
  h_max : Height

namespace FGStore

variable {V : Type} [DecidableEq V]

end FGStore

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Derived sets (PROTOCOL.md `def:fg-candidate-tree`, `def:chain-state`) -/

/-- §5.1 the descendants of the finalized block — a prose notion, with no separate name in the protocol: the document writes the `Σ.F ⪯ B` filter inline wherever it
needs it ("descendants of the finalized block", `viable_tree`'s first
conjunct). The model keeps the def as the prose selection's transcription — a
**deliberate deviation, recorded in the ledger**: the branch analyses of the
tick lean on the term's opacity (an inline filter re-exposes the store's
`if`-projections to `split_ifs`), and the def carries no content beyond the
prose sentence. Named `finalized_descendants` after the inline prose;
`live_tree` until the retirement. -/
def finalized_descendants (F : Block V) (T : Finset (Block V)) :
    Finset (Block V) :=
  T.filter (fun B => Block.preceq F B = true)

/-- §5.2 the viability witness (PROTOCOL.md `def:fg-candidate-tree`): a **processed**
descendant whose state height is at most one below the current maximum. The
witness ranges over `Σ.T` — the liveness conjunct is redundant by transitivity (`Σ.F ⪯ B ⪯ W`);
`Proofs.Records.viable_tree_witness_live` is the tripwire.

`Height = ℕ`, so `h_max − 1` truncates at zero; the integer reading `h ≥ −1`
and the truncated reading `h ≥ 0` are both satisfied by every height, so
truncation does not change the answer. -/
def viable (σ : Block V → ChainState V) (h_max : Height)
    (T : Finset (Block V)) (B : Block V) : Bool :=
  decide (∃ W ∈ T, Block.Preceq B W ∧ h_max - 1 ≤ (σ W).h)

/-- §5.2 `viable_tree(Σ)` (PROTOCOL.md `alg:fg-store`):
`{B ∈ Σ.T: Σ.F ⪯ B, ∃ W ∈ Σ.T, B ⪯ W, σ[W].h ≥ h_max − 1}` — the
finalized-descendants filter, then the viability test with its witness over
the **processed** tree.

Derived at every use, including inside `update_finality` while the store is
mid-update. -/
def viable_tree (σ : Block V → ChainState V) (F : Block V) (h_max : Height)
    (T : Finset (Block V)) : Finset (Block V) :=
  (finalized_descendants F T).filter (fun B => viable σ h_max T B = true)

/-- §5.2 `get_fg_root(Σ)`: the block the walk starts from
(PROTOCOL.md `alg:fg-store`).

`Σ.J` when the store's maximum state height is exactly one above the
justification, `Σ.F` otherwise. The document states no invariant relating
`h_max` and `h_j + 1`, so neither the "never `J`" nor the "always `J`" degenerate
case is excluded here. `Σ.J` need not be viable, so the anchor can sit
outside the tree the walk descends — which PROTOCOL.md `sec:fg-fork-choice` allows
explicitly.

This is `decoupled-consensus-full`'s `simplexRoot` rule with one difference: it
returns the **block**, not its root, because `majority_fork_choice` takes a
block anchor and `get_filtered_block_tree` filters by `root ⪯ B`. -/
def get_fg_root (st : FGStore V) : Block V :=
  if st.h_max = st.h_j + 1 then st.J else st.F

end Protocol
end DecoupledConsensusModel
end

-- ── from FGForkChoice/ForkChoice.lean ──
section
/-!
# §5.2 Fork choice — `def:fg-candidate-tree`, `alg:fg-store` (PROTOCOL.md `def:fg-candidate-tree`, `alg:fg-store`)

The composed head: an FG floor and candidate tree, one SG anchor inside it, one
Goldfish walk from that anchor (PROTOCOL.md `alg:sg-fork-choice`).

```
get_fg_root → get_filtered_block_tree → majority_fork_choice → goldfish_fork_choice
```

Three things the document leaves to the model.

* **`goldfish_fork_choice` has to be restated.** The document redefines
  `goldfish_eligible` here (PROTOCOL.md `alg:fg-store`) and leaves
  `goldfish_fork_choice` alone, because the gate is late-bound in its prose.
  Lean resolves it at definition time, so the composition is written again with
  the §5 gate; its body is §2's, letter for letter
  (PROTOCOL.md `alg:goldfish`). The same reason restates the two duties in
  `Attest.lean`.
* **The anchor may sit outside the tree.** `get_fg_root` can return `Σ.J`
  while `get_filtered_block_tree` filters by viability, so the walk's first
  `children` set is computed from an anchor the tree need not hold.
  "Goldfish starts at the root even if the root is not in the filtered tree"
  (PROTOCOL.md `sec:fg-fork-choice`) — `Protocol.ghost` already tests membership on the
  child only, so nothing extra is needed.
* **Available confirmation does not come through here.** It "runs its own walk
  from `Σ.F` over `T_F(Σ)`; it uses neither the candidate tree, the SG root, nor
  the height filter" (PROTOCOL.md#the-complete-protocol). §7 re-anchors it
  (PROTOCOL.md `alg:store`); §5 leaves §2's version alone.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Protocol (ChainState)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- §5.2 `get_filtered_block_tree_from(Σ, blocks)`: recompute viability inside
an explicit processed-block view, then keep the viable blocks below the
full-store fork-choice root. Passing `blocks` to `viable_tree` restricts both
candidate membership and viability witnesses to that set; `Σ.σ`, `Σ.F`,
`Σ.h_max`, and `get_fg_root(Σ)` keep their ordinary full-store values. -/
def get_filtered_block_tree_from (st : FGStore V) (blocks : Finset (Block V)) :
    Finset (Block V) :=
  let root := get_fg_root st
  (viable_tree st.σ st.F st.h_max blocks).filter (fun B =>
    Block.preceq root B = true)

/-- §5.2 `get_filtered_block_tree(Σ)`: the ordinary full processed-tree
specialization of `get_filtered_block_tree_from`. -/
def get_filtered_block_tree (st : FGStore V) : Finset (Block V) :=
  get_filtered_block_tree_from st st.T

/-- §5.2 `goldfish_eligible(Σ, votes, s, B)`, the **final** version
(PROTOCOL.md `alg:fg-store`). §2's two clauses plus the height clause, keyed on the
block the walk stands on ( change): "a child of a
block whose state height is below `Σ.h_max − 1` is eligible without a majority"
(PROTOCOL.md `sec:fg-fork-choice`). The majority gate therefore applies exactly when the
current block is inside the band `{h_max − 1, h_max}`, so the walk always
reaches height `h_max − 1` (every viable block below the band has a viable
child) and never passes through the band unsupported. `B.parent` is the total
accessor (genesis is its own parent).

`Height = ℕ`, so `h_max − 1` truncates at zero. Truncation cannot change this
test: for `h_max ≤ 1` the truncated reading asks `h < 0` and the integer reading
asks `h < h_max − 1 ≤ 0`, and both are false for every height.

Takes `σ`, `h_max` and `cur = Σ.s` as plain arguments rather than a store, like
§2's version: §6 redefines the walk around it and §7 keeps its
own store type.

**Not touched again** — this is the version §6 and §7 use. -/
def goldfish_eligible (E : Env V) (σ : Block V → ChainState V) (h_max : Height)
    (T : Finset (Block V)) (cur : Slot)
    (votes support_votes : Finset (GoldfishVote V))
    (s : Slot) (B : Block V) : Bool :=
  decide ((σ B.parent).h < h_max - 1) ||
    decide (Protocol.voters_count E votes s <
      2 * Protocol.goldfish_score E T votes support_votes s B) ||
    decide (B.slot = cur)

/-- §2.4 `goldfish_fork_choice(Σ, anchor, tree, votes, s)` with the §5 gate
(PROTOCOL.md `alg:goldfish`, `alg:fg-store`). The body is §2's; only `goldfish_eligible`
differs. -/
def goldfish_fork_choice (E : Env V) (σ : Block V → ChainState V)
    (h_max : Height) (T : Finset (Block V)) (cur : Slot) (anchor : Block V)
    (tree : Finset (Block V))
    (votes support_votes : Finset (GoldfishVote V)) (s : Slot) :
    Block V :=
  Protocol.ghost anchor tree
    (Protocol.goldfish_score E T votes support_votes s)
    (goldfish_eligible E σ h_max T cur votes support_votes s)

end Protocol
end DecoupledConsensusModel
end

end
