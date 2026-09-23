module
public import DecoupledConsensusModel.Execution.Setup
public import DecoupledConsensusModel.Protocol.Store
public import DecoupledConsensusModel.Protocol.ChainState

@[expose] public section

/-!
# `DecoupledConsensusModel/Protocol/Evidence.lean`

Purpose: Section 7 — the quorum-crossing and committee-pool evidence the review statements read.
Paper: `docs/PROTOCOL.md` `sec:complete-store`; algorithm block: the Section 7 block described by this module.

Defines: chain_attestations, store_attestations, SlashableBetween, HasIntersectionWeight, HasSlashableWeightBetween.

Read after: `DecoupledConsensusModel.Execution.Setup`, `DecoupledConsensusModel.Protocol.Store`, `DecoupledConsensusModel.Protocol.ChainState`
Read next: `DecoupledConsensusStatements.Instantiation.Certificates`.

State read: the protocol environment, schedule, store layers, and the view inputs named by the definitions.
State written: the returned store, chain state, record, or view value; pure readers write no state.

Representation notes: Typed Lean records, finite collections, and projections preserve the executable protocol representation. This module states no proof theorem.
MODEL_MAP rows: chain_attestations, store_attestations, SlashableBetween, HasIntersectionWeight, HasSlashableWeightBetween.
-/

-- ── from FinalityGadget/Slashing.lean ──
/-!
# Finality slashing evidence

Purpose: define the protocol-side evidence sets and slashing-weight
predicates used by accountable finality.
An auditor checks the chain/store evidence construction, the per-validator
slashability relation, and the quorum-weight threshold.

Defines: `chain_attestations`, `store_attestations`, `SlashableBetween`,
`HasIntersectionWeight`, and `HasSlashableWeightBetween`.
Read after: the finality-gadget attestations and protocol store.
Read next: `DecoupledConsensusStatements.Instantiation`.
-/

namespace DecoupledConsensusModel

open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The attestations carried by `B`'s chain: `⋃_{C ⪯ B} C.attestations`
(`sec:complete-store`, with the finality evidence relation in
`sec:state-machine`).

Every attestation any transition on this chain folds is a member, and no other
attestation can move `derived_state E cfg B`, so this is the evidence set the
accountability relation quantifies over. Duplicates across blocks collapse:
the fold is idempotent. -/
def chain_attestations : Block V → Finset (CombinedAttestation V)
  | .genesis => ∅
  | .node p _ _ _ _ ats _ => ats.toFinset ∪ chain_attestations p

/-- The evidence a store holds: the carried attestations of every processed
block (`sec:complete-store`).

`Σ.T` is never pruned, and `Σ.F` moves only through
`update_finality`, which is called only from `on_block` with `σ = Σ.σ[B]`
for a `B` this set covers. Block-carried attestations enter the SG pool through
the row-admission fold; this set remains the chain-attestation evidence used by
the accountability relation. -/
def store_attestations (st : Protocol.Store V) : Finset (CombinedAttestation V) :=
  st.T.biUnion chain_attestations

/-- A validator `i` is slashable **between** two evidence sets: one occurrence
from each, both `i`'s, satisfying E1 or E2 (`sec:state-machine`).

`a` and `b` are chosen independently, so `A₁ = A₂` and `a = b` are both
permitted — "the conflicting occurrences can be in one attestation", which at
`a = b` is `Protocol.selfSlashable a`.
`b.val_index = i` is stated explicitly so both occurrences expose the
validator identity at the binding site, although `Slashable` already carries
the `sameValidator` conjunct.

This is the accountability **conclusion** form: it names the histories exposing
the evidence. -/
def SlashableBetween (A₁ A₂ : Finset (CombinedAttestation V)) (i : V) : Prop :=
  ∃ a ∈ A₁, ∃ b ∈ A₂, a.val_index = i ∧ b.val_index = i ∧ Protocol.Slashable a b

/-- The weight floor `w(S) ≥ 2q − W` for an intersection of two quorums
(`sec:state-machine`).

Written additively as `2q ≤ W + w(S)` so that no natural-number subtraction
appears in the headline: `Height`, `Slot` and every weight are `Nat`, and `2q −
W` would truncate silently if `q` were ever re-defined below `W/2`. -/
def HasIntersectionWeight (E : Env V) (S : Finset V) : Prop :=
  2 * E.q ≤ E.W + E.electorate.weightOf S

/-- Slashable weight `2q − W` **between** two evidence sets. This is the
accountability conclusion form in `sec:state-machine`. -/
def HasSlashableWeightBetween (E : Env V)
    (A₁ A₂ : Finset (CombinedAttestation V)) : Prop :=
  ∃ S : Finset V, HasIntersectionWeight E S ∧ ∀ i ∈ S, SlashableBetween A₁ A₂ i

end DecoupledConsensusModel

end
