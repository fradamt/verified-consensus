module
public import DecoupledConsensusModel

@[expose] public section

/-!
# §7.1 Cumulative node store — `sec:complete-store` (PROTOCOL.md `sec:complete-store`)

The final store, the SG-vote projection, and the one adapter that feeds §6's
decisions.

`Σ` is **its own flat structure**, not the end of the `extends` chain
(modeling-choices row 21). The chain §2 → §3 → §5 → §6 carries a pool of bare SG
votes; here the pool holds combined attestations and every SG rule reads their
`(validator, round, confirmed)` projection
(PROTOCOL.md `sec:complete-store`, "every SG rule and grade reads only this
projection"). A Lean `extends`
chain cannot retype a field, so the layers are joined by `toHealing` instead: one
projection, used read-only, through which every §6 decision applies unchanged.

Three shapes are forced here.

* **The pool is a `List`.** `propose_block` copies processed attestations into
  the block it builds (PROTOCOL.md `alg:duties`) and `Finset.toList` is
  noncomputable in Mathlib — the same reason `gf_votes[k]` is a list
  (choices S2.2). `on_sg_vote`'s duplicate test is what keeps it a set;
  set-valued reads go through `Store.sg_pool`.
* **The SG fibre of `Σ.timestamp[·]` is keyed by the projection.** The pool
  admits at most one attestation per `(validator, head)` in a round
  (PROTOCOL.md `sec:complete-store`, `alg:store`), so the projection is
  injective on it and the two keyings agree on every pooled object; every rule
  that reads the stamp reads it through the projection
  (PROTOCOL.md `sec:complete-store`).
* **`Λ` is not here.** "It belongs to the validator, not to the store"
  (PROTOCOL.md `sec:complete-store`, choices S5.8).

The 13 components of PROTOCOL.md `sec:complete-store` are 15 Lean fields: `timestamp[·]`
is one component and three typed maps, because Lean has no untyped key
(choices S2.1).
-/

namespace DecoupledConsensusModel
namespace Protocol

open Protocol (ChainState)
open Protocol (SGVote)

namespace Store

variable {V : Type} [DecidableEq V]

/-- Proof-facing finalized height derived from the final store's live fields.

The protocol does not store `h_F`. For a non-genesis finalized block, its
height is the height of that block's stored post-state. Genesis is the height-0
checkpoint although its initial chain state has current height 1. Reachability
and derived-state agreement establish that this view matches the finalized
checkpoint recorded by the chain state that caused the `F` update. -/
def finalized_height (st : Store V) : Height :=
  if st.F = Block.genesis then 0 else (st.σ st.F).h

/-- §7.1 the processed attestations, as `propose_block` reads them
(PROTOCOL.md `alg:duties`, F7.3).

`on_sg_vote` rejects any attestation of a future round
(PROTOCOL.md `alg:store`), so the pool is empty above `round(Σ.s)` and the range is
the whole of it. Order is by ascending round, then pool order; the document
states none (F7.3c). -/
def processed_attestations (hc : Protocol.HealConfig) (st : Store V) :
    List (CombinedAttestation V) :=
  (List.range (hc.round_of st.s + 1)).flatMap st.sg_votes

end Store

end Protocol
end DecoupledConsensusModel

end
