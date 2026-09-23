module
public import DecoupledConsensusModel

@[expose] public section

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
  type (modeling-choices row 21). §7 supplies its own projection into the
  same functions.
* **`R`, `η_SG` and `a_r` are a parameter structure.** `a_r` is "a public
  parameter" with no stated relation to round `r`'s slots at this layer
  (PROTOCOL.md `sec:sg-schedule`, F3.1); §6 fixes `a_r = t_{rR} + 6Δ`
  (PROTOCOL.md `sec:healing-schedule`). It stays free here, as the document
  writes it.
* **`confirmed` is `Option BlockId`.** The confirmed block is a block or `⊥`
  (PROTOCOL.md `sec:sg-schedule`), and wire objects name blocks by root
  (modeling-choices row 12); consumers resolve the root through a tree.

`SGVote` is the §3 layer's own wire object, so — unlike `GoldfishVote` and
`CombinedAttestation` — it is *not* in the substrate: no `Block` field carries
it. "SG votes travel only on the wire. Blocks do not carry them, and they never
enter a Goldfish vote set" (PROTOCOL.md `sec:sg-store`).
-/

namespace DecoupledConsensusModel
namespace Protocol

section Resolved

variable {V : Type} [DecidableEq V]

/-- §3.2 an SG vote is resolved when the store holds its confirmed block;
an empty confirmed block resolves at receipt. -/
def sg_resolved (T : Finset (Block V)) (vote : SGVote V) : Bool :=
  match vote.confirmed with
  | none => true
  | some root => (Block.find? T root).isSome

end Resolved

section Vocabulary

variable {V : Type} [DecidableEq V]

/-! ## Vote-set vocabulary (PROTOCOL.md `def:majority-fork-choice`,
`sec:sg-schedule`)

`latest`, `sg_support` and `on_sg_vote` each phrase their own test over one
round's pool; the three phrasings are stated once here, over a plain set of
votes, so that §7 can feed them its attestation projection unchanged
(modeling-choices row 21).
-/

/-- §3.2 the votes of `votes` cast by `v` (PROTOCOL.md `sec:sg-store`). -/
def sg_votes_by (votes : Finset (SGVote V)) (v : V) : Finset (SGVote V) :=
  votes.filter (fun vote => vote.val_index = v)

/-- §3.2 `τ(vote) = max{Σ.timestamp(vote), Σ.timestamp(C)}`, `+∞` while `C` is
missing; a `⊥`-confirmed vote resolves at its own receipt
(PROTOCOL.md `sec:sg-store`, `sec:complete-store`).

Read by §6's grades — `t_v` is a resolution time (PROTOCOL.md `def:grades`)
— and by nothing in §3, which is round-indexed and needs only `sg_resolved`.

Like §2's, it is a `TimestampMap`, so a `τ` cutoff is `beforeCutoff st.sg_tau Γ`
and no second cutoff view exists. -/
def sg_resolution_time (T : Finset (Block V)) (tb : TimestampMap (Block V))
    (ts : TimestampMap (SGVote V)) : TimestampMap (SGVote V) :=
  fun vote =>
    match vote.confirmed with
    | none => ts vote
    | some root =>
      match Block.find? T root with
      | none => none
      | some C => occurrenceMax (ts vote) (tb C)

/-- §3.3 "`sg_votes[k]` holds a resolved vote by `v`"
(PROTOCOL.md `def:majority-fork-choice`).

**Resolution-filtered, and it is the only §3 reader that is.** `latest` selects
the round a validator is represented by, and an unresolved vote must not claim
that round from a resolved older one. The uniqueness test of `sg_support` reads
the whole bucket at receipt (`sole_vote?`), and its support arm is
resolution-filtered by construction, because `heads_under` resolves the root. -/
def holds_resolved_vote_by (T : Finset (Block V)) (votes : Finset (SGVote V))
    (v : V) : Bool :=
  decide (0 < ((sg_votes_by votes v).filter (fun u => sg_resolved T u = true)).card)

/-- §3.3 "`sg_votes[k]` holds a vote by `v`", **resolved or not**
(baseline `c9c98df`): the raw-participation test the represented weight reads —
the SG analogue of the Goldfish denominator's raw `votes`. -/
def holds_vote_by (votes : Finset (SGVote V)) (v : V) : Bool :=
  decide (0 < (sg_votes_by votes v).card)

/-- §3.3 "`sg_votes[k]` holds exactly one distinct vote by `v`"
(PROTOCOL.md `alg:sg-fork-choice`), returned so that its confirmed block
can be read.

`none` when `v` has no vote in the set and when it has two or more — the
"empty or equivocating latest round supplies no support" of
PROTOCOL.md `def:majority-fork-choice`. Built on the substrate's
`pickUnique?`, so it is computable and choice-free.

With §7's pool the required reading is "exactly one distinct **confirmed
block**" (F3.6). The projection `(validator, round, confirmed)` of two
attestations that differ only in their pair fields is one `SGVote`
(PROTOCOL.md `sec:complete-store`), so a `Finset` of projections collapses
them and this test reads confirmed blocks there without changing. -/
def sole_vote? (votes : Finset (SGVote V)) (v : V) : Option (SGVote V) :=
  pickUnique? votes (fun vote => decide (vote.val_index = v))

end Vocabulary

end Protocol
end DecoupledConsensusModel

end
