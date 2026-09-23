module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Availability
public import DecoupledConsensusProofs.Protocol.Handlers.TickBridges

@[expose] public section



namespace DecoupledConsensusModel
namespace Protocol

open Protocol (HealConfig)
open Internal
open Execution
open Internal.NamedRecoveryRead
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]


/-! ## The slot instants are ordered -/

theorem proposal_time_le_confirmation_time (E : Env V) (s : Slot) :
    Protocol.proposal_time E s ≤ Protocol.confirmation_time E s := by
  have h : ∀ a d : Int, 0 < d → a ≤ a + 6 * d := by intro a d hd; omega
  exact h (E.t s) E.Δ E.Δ_pos

theorem vote_time_le_confirmation_time (E : Env V) (s : Slot) :
    Protocol.vote_time E s ≤ Protocol.confirmation_time E s := by
  have h : ∀ a d : Int, 0 < d → a + d ≤ a + 6 * d := by intro a d hd; omega
  exact h (E.t s) E.Δ E.Δ_pos

/-! ## The store residuals -/


/-- **Residual  — the vote stores extend the proposer's walk.** At `t_s + Δ`
every honest committee member's store meets `VoteStoreExtends` for the slot-`s`
proposal: its own walk, over its own anchor and the proposal-free part of its own
tree, returns the head the proposer built on.

**This replaces a refuted clause.** The first version asked for
`VoteStoreAligned`, whose `merged` clause says the honest slot-`(s−1)` votes in
the voter's merged view all name one head. That clause is **false**, and for two
independent reasons (`docs/fragments/review-merged-cx.md`):

* *The tree splits the honest votes.* At the slot-`(s−1)` vote instant the gate's
  current-slot exemption makes **any** stored slot-`(s−1)` block eligible with no
  votes behind it, so a node that holds a Byzantine block descends into it while
  a node that does not open items at the parent. Same votes, same scores, different
  heads — and `merged` fails even in runs where P3(a)'s own conclusion holds, so
  it was strictly stronger than the statement it served.
* *The boundary.* At `s = 1` the clause quantifies over honest slot-`0` committee
  members and asks each for a slot-`0` vote, but `on_tick`'s `0 < s` guard means
  no validator ever emits one, and `HonestCommittees` forces the committee
  nonempty. So it is unsatisfiable at slot 1 in **every** honest run, with no
  Byzantine proposer anywhere.

The determinism form has neither problem. It names no committee, no honest set
and no majority; it is not an induction over slots; and it is satisfiable at
`s = 1`, where the walk simply returns the anchor because no slot-`0` vote exists
to move it. What it costs is `.walk` and `.blocked` — the voter's walk agreeing
with the proposer's, and `H` having no other eligible child in the voter's tree,
the second of which is what `AtFrontier` carried in the counting form.

**Named.** The `head` residual reads the contract's own
anchor at the prepared vote read (`NamedVoteStoreExtends`, `Optimistic/
Agreement.lean`), not the unparameterised `Protocol.get_head_in_tree_hc`; the
proposal is a named block. -/
def VoteStoresExtend (S : Setup V) (ρ : Run V) (s : Slot) (B : NamedBlock V) : Prop :=
  ∀ v ∈ ρ.honest, v ∈ S.E.committee s →
    ∃ (tree₀ : Finset (Block V)) (H : Block V),
      NamedVoteStoreExtends S ρ v s tree₀ H B



/-! ## O12 and the separate O13 predicate, from store residuals -/



/-! ## P3(a) -/




/-! ## What P4's (C1) inherits

(C1) is `AvailableChainFrom` at `a_{r₀}` together with one clause about
`Σ.latest_confirmed`. The first conjunct is the theorem above at a different
endpoint, so **(C1)'s availability half needs no new residual**: it is the same
two store premises and the absorption premise P3(a) runs on. The
`latest_confirmed` clause stays, because
compatibility with `Can r₀` is a statement about the canonical family and not
about the confirmation walk. -/


end Protocol
end DecoupledConsensusModel

end
