module
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Finset.Lattice.Fold
public import DecoupledConsensusModel.Protocol.Schedule

@[expose] public section

/-!
# `DecoupledConsensusModel/Protocol/StoreBase.lean`

Purpose: Section 7.1, base of the store chain — the §2 store layer, resolution, and the resolution time tau.
Paper: `docs/PROTOCOL.md` `sec:complete-store`; algorithm block: `def:store`.

Defines: Store, resolved, resolution_time, pool, tau.

Read after: `DecoupledConsensusModel.Protocol.Schedule`
Read next: `DecoupledConsensusModel.Protocol.ForkChoice.Views`.

State read: the protocol environment, schedule, store layers, and the view inputs named by the definitions.
State written: the returned store, chain state, record, or view value; pure readers write no state.

Representation notes: Typed Lean records, finite collections, and projections preserve the executable protocol representation. This module states no proof theorem.
MODEL_MAP rows: Store, resolved, resolution_time, pool, tau.
-/

-- ── from Goldfish/Store.lean ──
/-!
# §2.2 Store — `sec:goldfish-store`, `def:store` (PROTOCOL.md `sec:goldfish-store`)

The seven components of `def:store`, the initial store, and the three derived
notions the section states over it: equivocation detection, *resolution*, and
the resolution time `τ`.

Three shapes are forced here.

* The document's single `timestamp[·]`, keyed by "block or vote"
  (PROTOCOL.md `def:store`), becomes two typed maps. Lean has no untyped key.
* `gf_votes[k]` is a *list*, not a `Finset`. `Block.gf_votes` already is one, and `Finset.toList` is noncomputable in Mathlib, so
  a `Finset` pool could not be copied into a proposal at all. The handler's
  duplicate guard (PROTOCOL.md `alg:goldfish-store`, "no rule needs a third
  pool entry") is what keeps the list a set; set-valued reads go through
  `Store.pool`.
* The store binder is `st`. `Σ` is Sigma-type notation in Lean and cannot be a
  binder name.

This is the base of the `extends` chain: §3, §5, §6 and §7 add fields to *this*
structure and never rename one (PROTOCOL.md `sec:substrate`).
-/

namespace DecoupledConsensusModel
namespace Protocol

/-- §2.2 the store `Σ = (t, s, T, timestamp[·], gf_votes[·], live_confirmed,
latest_confirmed)` (PROTOCOL.md `def:store`).

"The store keeps messages and their timestamps, and nothing else. Every rule
below is a timestamp comparison on this one pool" (PROTOCOL.md
`sec:goldfish-store`, "keeps messages and their timestamps"). -/
structure GoldfishStore (V : Type) where
  /-- §2.2 `Σ.t`: the current time, written by `on_tick` only
  (PROTOCOL.md `def:store`, `alg:goldfish-store`, "on_tick"). -/
  t : Time
  /-- §2.2 `Σ.s`: the current slot, written by `on_tick` only
  (PROTOCOL.md `def:store`, `alg:goldfish-store`, "on_tick"). -/
  s : Slot
  /-- §2.2 `Σ.T`: the tree of processed blocks (PROTOCOL.md `def:store`,
  "tree of processed blocks"). -/
  T : Finset (Block V)
  /-- §2.2 `Σ.timestamp[·]` on blocks (PROTOCOL.md `def:store`). -/
  timestamp_block : TimestampMap (Block V)
  /-- §2.2 `Σ.timestamp[·]` on Goldfish votes (PROTOCOL.md `def:store`). -/
  timestamp_vote : TimestampMap (GoldfishVote V)
  /-- §2.2 `Σ.gf_votes[k]`: the processed slot-`k` votes, which keep at most two
  distinct votes per validator (PROTOCOL.md `def:store`, "keeps at most two
  distinct votes per validator"). A total map with the
  empty default; duplicate-free by `on_goldfish_vote`. -/
  gf_votes : Slot → List (GoldfishVote V)
  /-- §2.2 `Σ.live_confirmed`: the block the last evaluated slot confirmed
  (PROTOCOL.md `def:store`, "the block the last evaluated slot confirmed").
  Not monotone. -/
  live_confirmed : Block V
  /-- §2.2 `Σ.latest_confirmed`: the monotone record the node exposes; no rule in
  this protocol reads it (PROTOCOL.md `def:store`, "no rule in this protocol
  reads it"). -/
  latest_confirmed : Block V

section Resolution

variable {V : Type} [DecidableEq V]

/-! ## Resolution (PROTOCOL.md `sec:goldfish-store`, "resolution time")

"A vote is processed on receipt, whether or not the store holds its head. A vote
is *resolved* when the store holds a valid head. For a vote with head `H`, the resolution time is
`τ(vote) = max{Σ.timestamp(vote), Σ.timestamp(H)}`, infinite while `H` is
missing."

Both are pure functions of `(Σ.T, Σ.timestamp[·])`, stated over those fields
rather than over a store: `voter_view` applies `resolved` to a *carried* set that
is in no pool (PROTOCOL.md `sec:view-merge`, "does not require the vote to
have entered"), and §7 supplies its own fields.
-/

/-- §2.2 whether the store holds the block `vote` names AND the vote is valid for it:
the head is a stored block from the vote's slot or earlier (PROTOCOL.md line 141,
"a Goldfish vote is a tuple (v, s, B) with B.slot ≤ s"; `sec:goldfish-store`,
"whether or not the store holds its head"). A vote for a block the store never
receives never resolves and is never counted. Absent or
ambiguous roots leave the vote unresolved as before. -/
def resolved (T : Finset (Block V)) (vote : GoldfishVote V) : Bool :=
  match Block.find? T vote.head with
  | some B => decide (B.slot ≤ vote.slot)
  | none => false

/-- §2.2 `τ(vote) = max{Σ.timestamp(vote), Σ.timestamp(H)}`, `+∞` while `H` is
missing (PROTOCOL.md `sec:goldfish-store`, "resolution time"), as a
timestamp map on votes.

Nothing is mutated: the two stamps are the frozen receipt instants of §1, and
`τ` is a maximum of them recomputed at every read. A vote the store never
processed already carries `+∞` on the first argument, so it is `+∞` here too.

It is a `TimestampMap` because that is exactly what it is — a second clock on the
same objects — so every reader that wants a `τ` cutoff writes `beforeCutoff
st.tau Γ` and reuses §1's one cutoff view. `Σ.timestamp(B_gen) = −∞` needs no
special case: `−∞` is the least `Stamp` and drops out of the maximum, so a vote
naming genesis resolves at its own receipt.

`τ(vote) ≥ Σ.timestamp(H)` by construction, which is what makes "inside a
support cutoff ⟹ the named block is processed" hold without a delivery premise —
the timing gap the re-stamp variant left open (obligations O14). -/
def resolution_time (T : Finset (Block V)) (tb : TimestampMap (Block V))
    (tv : TimestampMap (GoldfishVote V)) : TimestampMap (GoldfishVote V) :=
  fun vote =>
    match Block.find? T vote.head with
    | none => none
    | some H => if H.slot ≤ vote.slot then occurrenceMax (tv vote) (tb H) else none

end Resolution

namespace GoldfishStore

variable {V : Type} [DecidableEq V]

/-- §2.2 `Σ.gf_votes[k]` read as the set it stands for (PROTOCOL.md `def:store`,
"processed slot-$k$ votes"). The list is duplicate-free, so this loses
nothing. -/
def pool (st : GoldfishStore V) (k : Slot) : Finset (GoldfishVote V) :=
  (st.gf_votes k).toFinset

/-- §2.2 `τ(·)` read off the store (PROTOCOL.md `sec:goldfish-store`,
"resolution time"). -/
def tau (st : GoldfishStore V) : TimestampMap (GoldfishVote V) :=
  resolution_time st.T st.timestamp_block st.timestamp_vote

end GoldfishStore

end Protocol
end DecoupledConsensusModel

end
