module
public import DecoupledConsensusModel.Protocol.Duties.Inputs

@[expose] public section

/-!
# `DecoupledConsensusModel/Protocol/Store.lean`

Purpose: Section 7.1, the cumulative store Sigma — its fields, its pool reads, and the projections the earlier layers are read through.
Paper: `docs/PROTOCOL.md` `sec:complete-store`; algorithm block: `def:store`.

Defines: sgVote, Store, init, pool, sg_pool, tau, toHealing.

Read after: `DecoupledConsensusModel.Protocol.Duties.Inputs`
Read next: `DecoupledConsensusModel.Protocol.Handlers`.

State read: the protocol environment, schedule, store layers, and the view inputs named by the definitions.
State written: the returned store, chain state, record, or view value; pure readers write no state.

Representation notes: Typed Lean records, finite collections, and projections preserve the executable protocol representation. This module states no proof theorem.
MODEL_MAP rows: sgVote, Store, init, pool, sg_pool, tau, toHealing.
-/

-- ── from Protocol/Store.lean ──
/-!
# §7.1 Cumulative node store — `sec:complete-store` (PROTOCOL.md `sec:complete-store`)

The final store, the SG-vote projection, and the one adapter that feeds §6's
decisions.

`Σ` is **its own flat structure**, separate from the `extends` chain. The chain §2 → §3 → §5 → §6 carries a pool of bare SG
votes; here the pool holds combined attestations and every SG rule reads their
`(validator, round, confirmed)` projection
(PROTOCOL.md `sec:complete-store`, "every SG rule and grade reads only this
projection"). A Lean `extends`
chain cannot retype a field, so the layers are joined by `toHealing` instead: one
projection, used read-only, through which every §6 decision applies unchanged.

Three shapes are forced here.

* **The pool is a `List`.** `propose_block` copies processed attestations into
  the block it builds (PROTOCOL.md `alg:duties`) and `Finset.toList` is
  noncomputable in Mathlib — the same reason `gf_votes[k]` is a list. `on_sg_vote`'s duplicate test is what keeps it a set;
  set-valued reads go through `Store.sg_pool`.
* **The SG fibre of `Σ.timestamp[·]` is keyed by the projection.** The pool
  admits at most one attestation per `(validator, head)` in a round
  (PROTOCOL.md `sec:complete-store`, `alg:store`), so the projection is
  injective on it and the two keyings agree on every pooled object; every rule
  that reads the stamp reads it through the projection
  (PROTOCOL.md `sec:complete-store`).
* **`Λ` is not here.** "It belongs to the validator, not to the store"
  (PROTOCOL.md `sec:complete-store`).

The 17 components listed in PROTOCOL.md `sec:complete-store` are represented
by 16 Lean fields in `Store`: `timestamp[·]` is split into three typed maps,
because Lean has no untyped key. The saved relative G2/G1/G0 grades are not
Store fields; they live in `NamedNodeState.cache`.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Protocol (ChainState)
open Protocol (SGVote)

/-- §7.1 the SG vote of a combined attestation: "an SG vote is an attestation's
`(validator, round, confirmed)` projection, and every SG rule and grade reads only
this projection" (PROTOCOL.md `sec:complete-store`).

Two attestations differing only in their pair fields are one vote
(PROTOCOL.md `sec:complete-store`), which is exactly what this map collapses. -/
def sgVote {V : Type} (a : CombinedAttestation V) : SGVote V :=
  ⟨a.val_index, a.round, a.confirmed⟩

/-- §7.1 the cumulative node store. The paper lists 17 components:
`(t, s, T, timestamp[·], σ[·], gfPool[·], attestations[·], Gtwo, Gone,
Gzero, F, J, h_j, h_max, live_confirmed, latest_confirmed, latest_stable)`
(PROTOCOL.md `sec:complete-store`). Lean has 16 core fields: the paper's one
timestamp component is three typed maps, and its three saved grades are held in
the external `NamedNodeState.cache`. Fields are in the document's tuple order.

`fresh_root[·]` is **gone**: the replacement of §6 deleted the round
decision, and with it the one entry the store serves to cache
(PROTOCOL.md `sec:complete-store`, "does not cache a view, a quorum set"). -/
structure Store (V : Type) where
  /-- §2.2 `Σ.t`: the current time (PROTOCOL.md `sec:substrate`, `sec:complete-store`). -/
  t : Time
  /-- §2.2 `Σ.s`: the current slot (PROTOCOL.md `sec:substrate`, `sec:complete-store`). -/
  s : Slot
  /-- §2.2 `Σ.T`: the processed block tree, never pruned
  (PROTOCOL.md `def:store`, `sec:fg-fork-choice`). -/
  T : Finset (Block V)
  /-- §1 `Σ.timestamp[·]` on blocks (PROTOCOL.md `sec:substrate`, `alg:store`). -/
  timestamp_block : TimestampMap (Block V)
  /-- §1 `Σ.timestamp[·]` on Goldfish votes (PROTOCOL.md `sec:substrate`, `alg:store`). -/
  timestamp_vote : TimestampMap (GoldfishVote V)
  /-- §1 `Σ.timestamp[·]` on the SG fibre, keyed by the vote projection
  (PROTOCOL.md `sec:complete-store`). -/
  timestamp_sg_vote : TimestampMap (SGVote V)
  /-- §5.1 `Σ.σ[B]`: the post-state of `B`. Total, defaulting to
  `ChainState.initial`. -/
  σ : Block V → ChainState V
  /-- §2.2 `Σ.gf_votes[k]`: the processed slot-`k` Goldfish votes, at most two
  distinct per validator (PROTOCOL.md `def:store`). -/
  gf_votes : Slot → List (GoldfishVote V)
  /-- §7.1 `Σ.sg_votes[r]`: the processed round-`r` **combined attestations**, at
  most two with distinct heads per validator (PROTOCOL.md `sec:complete-store`).
  A list, because `propose_block` copies it into a block. -/
  sg_votes : Round → List (CombinedAttestation V)
  /-- §5.1 `Σ.F`: the finalized block (PROTOCOL.md `def:chain-state`). -/
  F : Block V
  /-- §5.1 `Σ.J`: the justified block (PROTOCOL.md `def:chain-state`). -/
  J : Block V
  /-- §5.1 `Σ.h_j`: its height (PROTOCOL.md `def:chain-state`). -/
  h_j : Height
  /-- §5.1 `Σ.h_max`: the running maximum state height; **monotone** (PROTOCOL.md `sec:fg-fork-choice`, "finalization never reverts"). -/
  h_max : Height
  /-- The protocol-facing confirmation used by voting: an eligible Goldfish
  walk result, or the FG-root floor when the eligibility test fails. -/
  live_confirmed : Block V
  /-- The user-facing confirmation record. An ancestor candidate leaves it
  unchanged; an extension or conflict replaces it. `get_confirmed` also
  accounts for local finality (PROTOCOL.md `sec:complete-store`). -/
  latest_confirmed : Block V
  /-- The user-facing stable record: the
  latest G2 root, advanced by `advance_confirmed`, so an ancestor candidate
  leaves it unchanged while an extension or a conflict replaces it.
  `Protocol.get_stable` accounts for local finality on top of it. -/
  latest_stable : Block V

namespace Store

variable {V : Type} [DecidableEq V]

/-- §7.1 the initial store (PROTOCOL.md `sec:complete-store`): `t = s = 0`,
`T = {B_gen}`, `timestamp(B_gen) = −∞`, `h_max = 1`,
`F = J = B_gen`, `h_j = 0`,
`live_confirmed = latest_confirmed = B_gen`, and every pool empty.

`Σ.σ[·]` is a total post-state map and defaults to the initial chain state
everywhere. This is the value `on_block` reads at a child of genesis
(`sec:complete-store`). -/
def init : Store V where
  t := 0
  s := 0
  T := {Block.genesis}
  timestamp_block := fun B => if B = Block.genesis then some genesisStamp else none
  timestamp_vote := fun _ => none
  timestamp_sg_vote := fun _ => none
  σ := fun _ => ChainState.initial
  gf_votes := fun _ => []
  sg_votes := fun _ => []
  F := Block.genesis
  J := Block.genesis
  h_j := 0
  h_max := 1
  live_confirmed := Block.genesis
  latest_confirmed := Block.genesis
  latest_stable := Block.genesis

/-- §2.2 `Σ.gf_votes[k]` read as the set it stands for (PROTOCOL.md `def:store`).
The list is duplicate-free, so this loses nothing. -/
def pool (st : Store V) (k : Slot) : Finset (GoldfishVote V) :=
  (st.gf_votes k).toFinset

/-- §7.1 `Σ.sg_votes[r]` read as the set it stands for
(PROTOCOL.md `sec:complete-store`). -/
def sg_pool (st : Store V) (r : Round) : Finset (CombinedAttestation V) :=
  (st.sg_votes r).toFinset

/-- §2.2 `τ(·)` on Goldfish votes at the cumulative store
(PROTOCOL.md `sec:goldfish-store`). `Σ` is its own structure, so §2's `Store.tau`
does not reach it; the pure core `Protocol.resolution_time` does. -/
def tau (st : Store V) : TimestampMap (GoldfishVote V) :=
  Protocol.resolution_time st.T st.timestamp_block st.timestamp_vote

/-- §7.1 the store read as a §6 store: the one adapter
that lets every §6 decision — `get_head`, `fresh_anchor`, `fresh_root_value`,
`proposal`, `round_action` — apply here unchanged.

The single difference between the two records is the SG pool: this one holds
combined attestations, and the §6 rules read `(validator, round, confirmed)`
projections (PROTOCOL.md `sec:complete-store`). Everything else is copied.

`Finset.image` reports `Classical.choice`, which is why the
projection sits inside the field's lambda: it is computed only for the rounds a
rule actually reads. -/
def toHealing (st : Store V) : Protocol.HealingStore V where
  t := st.t
  s := st.s
  T := st.T
  timestamp_block := st.timestamp_block
  timestamp_vote := st.timestamp_vote
  gf_votes := st.gf_votes
  live_confirmed := st.live_confirmed
  latest_confirmed := st.latest_confirmed
  sg_votes := fun r => (st.sg_pool r).image sgVote
  timestamp_sg_vote := st.timestamp_sg_vote
  σ := st.σ
  F := st.F
  J := st.J
  h_j := st.h_j
  h_max := st.h_max

end Store

end Protocol
end DecoupledConsensusModel

end
