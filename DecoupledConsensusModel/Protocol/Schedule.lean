module
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.Ring
public import DecoupledConsensusModel.Objects.Time
public import DecoupledConsensusModel.Objects.Identifiers
public import DecoupledConsensusModel.Objects.Parameters
public import DecoupledConsensusModel.Objects.Blocks
public import DecoupledConsensusModel.Objects.Weights

@[expose] public section

/-!
# `DecoupledConsensusModel/Protocol/Schedule.lean`

Purpose: Section 7, shared schedule — the slot cutoffs, vote and proposal instants, and well-formedness of carried votes.
Paper: `docs/PROTOCOL.md` `sec:complete-store`; algorithm block: `sec:goldfish-schedule`.

Defines: Node, proposal_time, vote_time, and confirmation_time.

Read after: `DecoupledConsensusModel.Objects.Time`, `DecoupledConsensusModel.Objects.Identifiers`, `DecoupledConsensusModel.Objects.Parameters`
Read next: `DecoupledConsensusModel.Protocol.StoreBase`.

State read: the protocol environment, schedule, store layers, and the view inputs named by the definitions.
State written: the returned store, chain state, record, or view value; pure readers write no state.

Representation notes: Typed Lean records, finite collections, and projections preserve the executable protocol representation. This module states no proof theorem.
-/

-- ── from Goldfish/Objects.lean ──
/-!
# §2.1 Schedule and wire objects — `sec:goldfish-schedule`
(PROTOCOL.md `sec:goldfish-schedule`)

The five per-slot public instants, the identity `val_index` of the validator running the
node, the two wire constraints the section states, and the vote-set vocabulary
that both the store and the fork choice read.

The wire objects themselves are not defined here: `GoldfishVote` and
`Block.gf_votes` live in the substrate, because Lean cannot add a field to a
structure after the fact. This module only names the
schedule and the stated constraints.

`confirmation_time E s = support_cutoff E (s+1)` (PROTOCOL.md
`sec:goldfish-schedule`, "the last action is also the support action of
slot") is what lets `on_tick` dispatch the slot-`s` confirmation evaluation
from the slot-`(s+1)` support branch.
-/

namespace DecoupledConsensusModel
namespace Protocol

/-- §2.5 the validator running the node, written `val_index`; a node whose `val_index` holds no
duty for the slot simply does not run it (PROTOCOL.md `sec:goldfish-handlers`,
"does not run the duty").

`new_root` has no document counterpart: `propose_block` builds "a block with
`B.parent = H`, `B.slot = s`, `B.gf_votes = votes`" (PROTOCOL.md
`alg:goldfish-store`, "a block with") and
never says what `B.root` is, yet `Block.root` is a §1 field and every root
tie-break reads it. The nominal root of the block this node proposes in a slot is
therefore supplied here, as fixed data of the node. -/
structure Node (V : Type) where
  /-- §2.5 `val_index` (PROTOCOL.md `sec:goldfish-handlers`, "the local
  validator index"). -/
  val_index : V
  /-- The nominal root of the block this node proposes in a given slot. -/
  new_root : Slot → BlockId
  /-- Participation at each round action. A false value suppresses the
  whole combined attestation duty; clock ticks and Goldfish duties remain. -/
  awake : Round → Bool

section Vocabulary

variable {V : Type} [DecidableEq V]

/-! ## Vote-set vocabulary (PROTOCOL.md `sec:goldfish-store`, "has equivocated
as of", `def:goldfish-walk`)

`def:goldfish-walk` names these over the walk's `votes` argument, and §2.2's
"has equivocated as of `t`" needs the same two tests over a cutoff view of the
pool. They are therefore stated once, over a plain set of votes.
-/

/-- §2.4 the votes of `votes` cast by `v` (PROTOCOL.md `def:goldfish-walk`).
Distinctness of votes is tuple equality, which `Finset` membership
already gives. -/
def votes_by (votes : Finset (GoldfishVote V)) (v : V) : Finset (GoldfishVote V) :=
  votes.filter (fun vote => vote.val_index = v)

/-- §2.4 `v` *equivocates* in `votes` when they hold two of its distinct votes
(PROTOCOL.md `def:goldfish-walk`, "equivocates"); §2.2 reads the same test
over a cutoff view of the pool (PROTOCOL.md `sec:goldfish-store`, "has
equivocated as of").

Read literally: the document qualifies the *supporter* test by slot
(`(v,s,B') ∈ votes`, PROTOCOL.md `alg:goldfish`, "goldfishSupporters") and leaves
this one unqualified, so a validator with two votes of different slots in a
merged view equivocates. -/
def equivocates (votes : Finset (GoldfishVote V)) (v : V) : Bool :=
  decide (2 ≤ (votes_by votes v).card)

/-- §2.4 `v` *participates* in `votes` when they hold at least one of its votes
(PROTOCOL.md `def:goldfish-walk`, "participates"). Unqualified by slot,
exactly as written. -/
def participates (votes : Finset (GoldfishVote V)) (v : V) : Bool :=
  decide (0 < (votes_by votes v).card)

end Vocabulary

section Schedule

variable {V : Type} [DecidableEq V] [Fintype V]

/-- §2.1 `t_s`: the proposal instant of slot `s` (PROTOCOL.md
`sec:goldfish-schedule`, "proposal"). -/
def proposal_time (E : Env V) (s : Slot) : Time :=
  E.t s

/-- §2.1 `t_s + Δ`: the Goldfish vote instant of slot `s` (PROTOCOL.md
`sec:goldfish-schedule`, "Goldfish vote"). -/
def vote_time (E : Env V) (s : Slot) : Time :=
  E.t s + E.Δ

/-- §2.1 `t_s + 2Δ`: the support cutoff of slot `s` (PROTOCOL.md
`sec:goldfish-schedule`, "support cutoff"). -/
def support_cutoff (E : Env V) (s : Slot) : Time :=
  E.t s + 2 * E.Δ

/-- §2.1 `t_s + 3Δ`: the view freeze of slot `s` (PROTOCOL.md
`sec:goldfish-schedule`, "view freeze"). -/
def view_freeze (E : Env V) (s : Slot) : Time :=
  E.t s + 3 * E.Δ

/-- §2.1 `t_s + 6Δ`: the confirmation evaluation of slot `s` (PROTOCOL.md
`sec:goldfish-schedule`, "confirmation evaluation"). -/
def confirmation_time (E : Env V) (s : Slot) : Time :=
  E.t s + 6 * E.Δ

/-- The receiver-independent part of §2.1's Goldfish-vote constraint: the voter
is in its own slot's committee (PROTOCOL.md `sec:goldfish-schedule`,
"A Goldfish vote is a tuple").

The same source line also requires the named block's slot to be at most
`vote.slot`. That condition is enforced at the tree lookup:
`Protocol.resolved` and the Goldfish support lookup reject a later-slot head.
`Block.find?` remains a read-side operation used when support or another
protocol rule resolves the head. -/
def vote_well_formed (E : Env V) (vote : GoldfishVote V) : Bool :=
  decide (vote.val_index ∈ E.committee vote.slot)

end Schedule

/-- The wire constraint checked by the selected named receipt on a block's
carried raw set: `B.votes` holds slot-`(B.slot − 1)` votes. Written
`vote.slot + 1 = B.slot` to avoid truncated subtraction, which also makes a
slot-`0` block carrying any vote fail it. The named ingress applies this check
before block admission. -/
def carried_votes_well_formed {V : Type} (B : Block V) : Bool :=
  B.gf_votes.all (fun vote => decide (vote.slot + 1 = B.slot))

/-- §2.1 the proposal's support view is a subset of its carried raw view
(PROTOCOL.md `sec:goldfish-schedule`, "The support subset records the
proposer's view"). The support list is metadata for the fixed proposer
view; `on_block` processes only `B.gf_votes`. -/
def carried_support_well_formed {V : Type} [DecidableEq V] (B : Block V) : Bool :=
  B.gf_support_votes.all (fun vote => decide (vote ∈ B.gf_votes))

end Protocol
end DecoupledConsensusModel

end
