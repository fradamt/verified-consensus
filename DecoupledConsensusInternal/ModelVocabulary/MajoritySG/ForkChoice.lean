module
public import DecoupledConsensusModel
public import DecoupledConsensusInternal.ModelVocabulary.MajoritySG.Objects

@[expose] public section

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
(PROTOCOL.md `sec:complete-store`, modeling-choices row 21).

Two model-forced arguments appear in front of the document's lists, as in §2.

* `η_SG`, which the document keeps in the prose rather than in `latest`'s
  argument list (PROTOCOL.md `def:majority-fork-choice`).
* `T`, the tree ancestry is resolved in. The document is explicit that this is
  **not** the walked `tree`: "ancestry is read in the processed block tree `T`,
  so a head
  outside a restricted child tree still supports the child through which it
  descends" (PROTOCOL.md `def:majority-fork-choice`). It doubles as the tree
  that turns a head root into a block (modeling-choices row 12).

Counting here is by **weight** over all of `V` (PROTOCOL.md `sec:sg-schedule`),
never by committee cardinality: the two regimes must not be conflated.
-/

namespace DecoupledConsensusModel
namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- §3.3 the support-round selection: the greatest round
`k ∈ [max{0, r−η_SG}, r)` in which `sg_votes[k]` holds a **resolved** vote by
`v`, or `⊥` when there is none (baseline `c9c98df`; the whole of the previous
`latest`, kept as the selection half of `latest_support_vote`).
The window is ascending, so `getLast?` *is* `max eligible`, and its `none` *is*
the pseudocode's `eligible = ∅` return.
`T` is the tree resolution is tested in, and is the same `Σ.T` every other
resolution reader takes. It joins the model-forced arguments in front of the
document's list, beside `η_SG`. -/
def latest_support_round (pool : Round → Finset (SGVote V)) (η_SG : Round)
    (T : Finset (Block V)) (v : V) (r : Round) : Option Round :=
  ((latest_window η_SG r).filter (fun k =>
    holds_resolved_vote_by T (pool k) v)).getLast?


/-- §3.3 `latest_support_vote(Σ, v, r)` (baseline `c9c98df`): the unique SG
vote by `v` in its support round, or `⊥` when no in-window round holds a
resolved vote by `v` **or** the selected round holds more than one distinct
vote by `v`.

Two consequences the tex states outright, both by construction here:
equivocation is **receipt-level in the support round** — `sole_vote?` reads the
whole bucket, so a receipt-level distinct pair silences `v` even when one of
the two is unresolved — and **a newer round with no resolved vote does not
replace the standing support vote**, because the selection filters on
resolution before taking the maximum.

**The cross-round equivocation asymmetry is deliberate** (doc audit, W5.34):
a receipt-level pair in a newer round with **no** resolved vote is *skipped*
by the selection — it does not touch the standing support — while the same
pair kills support the moment its round is selected. Per-validator cone
uniqueness holds either way: whatever round is selected, `v` supports at most
one chain. -/
def latest_support_vote (pool : Round → Finset (SGVote V)) (η_SG : Round)
    (T : Finset (Block V)) (v : V) (r : Round) : Option (SGVote V) :=
  match latest_support_round pool η_SG T v r with
  | none => none
  | some k => sole_vote? (pool k) v

/-- §3.3 `v` is *represented* at round `r` (baseline `c9c98df`): **the expiry
window holds any of its votes, resolved or not** — the raw denominator, the SG
analogue of the Goldfish walk's raw `votes`. Representation no longer reads
resolution, so `T` is gone from its arguments. -/
def represented (pool : Round → Finset (SGVote V)) (η_SG : Round)
    (v : V) (r : Round) : Bool :=
  (latest_window η_SG r).any (fun k => holds_vote_by (pool k) v)

/-- §3.3 the denominator's set (baseline `c9c98df`):
`{v ∈ V: ∃ k ∈ [max{0, r−η_SG}, r), sg_votes[k] holds a vote by v}`. Over all
of `V`, not over a committee. -/
def represented_set (pool : Round → Finset (SGVote V)) (η_SG : Round)
    (r : Round) : Finset V :=
  Finset.univ.filter (fun v => represented pool η_SG v r = true)

/-- §3.3 `W_r`, the entire represented weight, written `total` in the
pseudocode — raw since baseline `c9c98df`. -/
def W_r (E : Env V) (pool : Round → Finset (SGVote V)) (η_SG : Round)
    (r : Round) : Nat :=
  E.electorate.weightOf (represented_set pool η_SG r)

/-! ## Support (PROTOCOL.md `def:majority-fork-choice`) -/

/-- §3.3 the `H ≠ ⊥ and B ⪯ H` half of the supporter test
(PROTOCOL.md `def:majority-fork-choice`): the vote's head resolves in `T`
to a block descending from `B`.

A timeout head (`⊥`) supports nothing, and a head that `T` does not resolve —
absent, or two blocks with one root — supports nothing either (choices S2.5,
modeling-choices row 16). The §2 analogue is `Protocol.targets_under`. -/
def heads_under (T : Finset (Block V)) (B : Block V) (vote : SGVote V) : Bool :=
  match vote.confirmed with
  | none => false
  | some r =>
    match Block.find? T r with
    | some H => Block.preceq B H
    | none => false

/-- §3.3 `v` supports `B` at round `r` (baseline `c9c98df`): its
`latest_support_vote` is a vote `(v, k, C)` with `C ≠ ⊥` and `B ⪯ C` — the
exact factoring the tex performed, so the body is one selector read and one
ancestry test.

Two clocks meet inside the selector, and the split is the τ fold's. The
support-round selection is resolution-filtered — its own reader. The
uniqueness test is **receipt-based**: `sole_vote?` ranges over the whole
bucket, so a second vote silences the validator whether or not it resolves.
The support arm is resolution-filtered by construction: `heads_under` resolves
the confirmed root through `T` and returns `false` when it cannot, so an
unresolved sole vote supplies no support without needing its own filter.

An empty or equivocating support round therefore supplies no support and, because
only that round is read, also silences every older vote; a later clean
round restores support. -/
def supports (pool : Round → Finset (SGVote V)) (η_SG : Round)
    (T : Finset (Block V)) (r : Round) (B : Block V) (v : V) : Bool :=
  match latest_support_vote pool η_SG T v r with
  | none => false
  | some vote => heads_under T B vote

/-- §3.3 the supporter set of `B` at round `r`
(PROTOCOL.md `def:majority-fork-choice`). -/
def sgSupporters (pool : Round → Finset (SGVote V)) (η_SG : Round)
    (T : Finset (Block V)) (r : Round) (B : Block V) : Finset V :=
  Finset.univ.filter (fun v => supports pool η_SG T r B v = true)

/-- §3.3 `sg_support(Σ, r, B)`: the weight supporting `B`.

A represented validator whose support round holds two distinct votes counts in
`W_r` but in no `sg_support` — and since the raw denominator (baseline
`c9c98df`) so does one whose in-window votes are all unresolved — so
non-supporting weight can only raise the bar (F3.3). -/
def sg_support (E : Env V) (pool : Round → Finset (SGVote V)) (η_SG : Round)
    (T : Finset (Block V)) (r : Round) (B : Block V) : Nat :=
  E.electorate.weightOf (sgSupporters pool η_SG T r B)

/-! ## The majority walk
(PROTOCOL.md `def:majority-fork-choice`, `alg:sg-fork-choice`) -/

/-- §3.3 `majority_fork_choice(Σ, anchor, tree, r)`: `ghost` with `sg_support` as
the score and a strict majority of `W_r` as the gate
(PROTOCOL.md `def:majority-fork-choice`).

Because an equivocator supplies no support but stays in the denominator, and
conflicting children have disjoint supporter sets, two conflicting children
cannot both pass `2·sg_support > total`; the descent is uniquely determined
(PROTOCOL.md `def:majority-fork-choice`). At `r = 0` nothing is represented, `total = 0`, and
`2·0 > 0` is false, so the walk returns its anchor unchanged (F3.4). -/
def majority_fork_choice (E : Env V) (pool : Round → Finset (SGVote V))
    (η_SG : Round) (T : Finset (Block V)) (anchor : Block V)
    (tree : Finset (Block V)) (r : Round) : Block V :=
  let total := W_r E pool η_SG r
  let score := sg_support E pool η_SG T r
  Protocol.ghost anchor tree score (fun B => decide (total < 2 * score B))

end Protocol
end DecoupledConsensusModel

end
