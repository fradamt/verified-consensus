module
public import Mathlib.Data.Finset.Union
public import DecoupledConsensusModel.Protocol.StoreBase

@[expose] public section

/-!
# `DecoupledConsensusModel/Protocol/ForkChoice/Views.lean`

Purpose: Section 7, block 2a — the voter and proposer views of the vote pool and the processed block tree they induce.
Paper: `docs/PROTOCOL.md` `sec:complete-store`; algorithm block: `alg:goldfish` / `alg:fg-store`.

Defines: voter_view, voter_support_view, and proposer_view.

Read after: `DecoupledConsensusModel.Protocol.StoreBase`
Read next: `DecoupledConsensusModel.Protocol.ForkChoice.Goldfish`.

State read: the protocol environment, schedule, store layers, and the view inputs named by the definitions.
State written: the returned store, chain state, record, or view value; pure readers write no state.

Representation notes: Typed Lean records, finite collections, and projections preserve the executable protocol representation. This module states no proof theorem.
-/

-- ── from Goldfish/ViewMerge.lean ──
/-!
# §2.3 View merge — `sec:view-merge` (PROTOCOL.md `sec:view-merge`, `alg:goldfish-store`)

The vote duty reads two merged vote views and one merged processed-block view.
The raw vote view uses the receipt cutoff on its pool arm and includes every
correctly slotted carried vote. The support vote view uses the resolution clock
on its pool arm and includes only finite-resolution carried votes. The block
view contains blocks received before the previous-slot freeze together with the
stored ancestors of current-slot proposals. Neither vote construction drops
equivocators; `goldfish_score` reads the raw view for equivocation and the
support view for ancestry support.

The voter's raw view is modeled as the document writes it, with its remaining
known oddity left in place:

* it is a **union of a pool projection with carried sets**, so it need not be a
  subset of the pool: it can hold rejected votes and more than two votes per
  validator;
* the loop runs over **every** stored slot-`s` block, so an equivocating proposer
  contributes several disjoint carried sets, which can manufacture equivocators in
  the merged view.

**The wrong-slot arm is closed** (PROTOCOL.md `sec:view-merge`, "included in
an admitted").
Both carried comprehensions now require `vote.slot = s − 1`; the support arm
also requires finite resolution. Thus, a carried vote of another slot never
enters either view. `Block.gf_votes` is described as the carried slot-`(B.slot − 1)` votes but
nothing enforced it, and a block carrying wrong-slot votes inflated
`voters_count` at the merge. The comprehension filters these votes by slot.

The carried support arm asks whether the named head resolves as a valid vote in
the receiver's tree. The proposer has already fixed the support classification in
`B.gf_support_votes`; receiver-local pool admission and receipt timestamps must
not erase it. This exception applies only to proposal-carried support votes.
The pool arm still uses its historical resolution-time cutoff.

The **pool** arm needs no slot conjunct and never did: it reads
`Σ.gf_votes[s−1]` (`st.pool (s − 1)`), which is slot-indexed by construction.
`proposer_view` is the same — its bucket is `Σ.gf_votes[s−1]`.
-/

namespace DecoupledConsensusModel
namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- §2.3 the voter's **raw** merged view in slot `s` — the `votes` half of the
two-view pair (PROTOCOL.md): the slot-`(s−1)` votes
**received** before the view freeze `t_{s−1} + 3Δ` (the receipt clock, not
`τ`), together with **every** slot-`(s−1)` vote carried by an admitted slot-`s`
block, resolved or not. Raw participation drives the denominators and the
equivocation test; `voter_support_view` below is the support half.

`s − 1` is truncated subtraction on `Slot = ℕ`; `goldfish_vote` runs only under
`on_tick`'s `s > 0` guard, so slot `0` is not reachable here. -/
def voter_view (E : Env V) (st : GoldfishStore V) (s : Slot) : Finset (GoldfishVote V) :=
  beforeCutoff st.timestamp_vote (view_freeze E (s - 1)) (st.pool (s - 1)) ∪
    (st.T.filter (fun B => B.slot = s)).biUnion (fun B =>
      B.gf_votes.toFinset.filter (fun vote => vote.slot = s - 1))

/-- §2.3 the voter's **support** view — the `support_votes ⊆ votes` half: the
  pool votes whose resolution time is before the freeze, and the members of a
  current proposal's fixed proposal-time support subset whose heads resolve in
  the receiver's tree. Ancestry support reads this; participation does not.

  The carried arm deliberately does not test the vote's local receipt stamp.
  `B.gf_support_votes` records the proposer's frozen support classification; at
  the receiver, only head availability remains to be checked. Thus the ordinary
  two-vote pool cap can reject a carried vote without erasing its proposal-only
  support role. A carried raw vote outside `B.gf_support_votes` never becomes
  support merely because its head resolves later in the receiver's store. -/
def voter_support_view (E : Env V) (st : GoldfishStore V) (s : Slot) :
    Finset (GoldfishVote V) :=
  beforeCutoff st.tau (view_freeze E (s - 1)) (st.pool (s - 1)) ∪
    (st.T.filter (fun B => B.slot = s)).biUnion (fun B =>
      B.gf_support_votes.toFinset.filter (fun vote =>
        resolved st.T vote = true ∧ vote.slot = s - 1))

/-- §2.3 `voter_processed_block_tree(Σ, s)`: the processed-block view used by
the slot-`s` voter. It contains each block in `Σ.T` whose receipt stamp is
strictly before `view_freeze E (s − 1)`, together with each stored ancestor
(including itself) of every stored slot-`s` proposal.

This block-domain merge is independent of `voter_view` and
`voter_support_view`; those definitions continue to control only vote
participation and support. -/
def voter_processed_block_tree (E : Env V) (st : GoldfishStore V) (s : Slot) :
    Finset (Block V) :=
  let freeze := view_freeze E (s - 1)
  let proposals := st.T.filter (fun P => P.slot = s)
  st.T.filter (fun B =>
    stampedBefore st.timestamp_block freeze B = true ∨
      ∃ P ∈ proposals, Block.preceq B P = true)

/-- §2.3 the proposer's **raw** view in slot `s`: the
whole bucket `Σ.gf_votes[s−1]`, with no filter at all — "the proposer does not
apply the freeze; it uses all previous-slot votes in the pool as `votes`".

Kept as a list, because this is exactly what the proposal carries: since the
two-view fold `B.gfPool` is the **raw** bucket ("everything"), so a vote the
proposer holds unresolved is still forwarded by the proposal. -/
def proposer_view (st : GoldfishStore V) (s : Slot) : List (GoldfishVote V) :=
  st.gf_votes (s - 1)

/-- §2.3 the proposer's **support** view: the resolved subset. -/
def proposer_support_view (st : GoldfishStore V) (s : Slot) : List (GoldfishVote V) :=
  (st.gf_votes (s - 1)).filter (fun vote => resolved st.T vote = true)

end Protocol
end DecoupledConsensusModel

end
