module
public import DecoupledConsensusModel.Objects.Blocks
public import DecoupledConsensusModel.Protocol.Store
public import DecoupledConsensusModel.Protocol.ChainState
public import DecoupledConsensusModel.Protocol.Schedule
public import DecoupledConsensusModel.Protocol.Grades

@[expose] public section

/-!
# `DecoupledConsensusModel/Protocol/Handlers.lean`

Purpose: Section 7, block 1 — advance, update_confirmation, get_stable, get_confirmed, on_block, on_goldfish_vote, on_sg_vote, update_finality, the admission paths they use, and the scheduler on_tick drives.
Paper: `docs/PROTOCOL.md` `sec:public-handlers`; algorithm block: `alg:public-handlers`.

Defines: advance_confirmed, floor_on_stable, state_transition, update_finality, on_goldfish_vote, on_goldfish_vote_checked, on_block_using, on_block, carried_attestations_admissible, on_block_checked_using, on_block_checked, round_votes, on_sg_vote, update_confirmation_with, get_head_in_tree_with, voter_filtered_block_tree, goldfish_vote_with, get_stable, get_confirmed, CarriedAdmission, NamedStore, initial, setClock, commitBlock, process_block_core, admit_row, admit_rows, admit_carried, on_block_with, TickOps, runWith.

Read after: `DecoupledConsensusModel.Objects.Blocks`, `DecoupledConsensusModel.Protocol.Store`, `DecoupledConsensusModel.Protocol.ChainState`
Read next: `DecoupledConsensusModel.Protocol.Tick`.

State read: the protocol environment, schedule, store layers, and the view inputs named by the definitions.
State written: the returned store, chain state, record, or view value; pure readers write no state.

Representation notes: Typed Lean records, finite collections, and projections preserve the executable protocol representation. This module states no proof theorem.
MODEL_MAP rows: advance_confirmed, floor_on_stable, state_transition, update_finality, on_goldfish_vote, on_goldfish_vote_checked, on_block_using, on_block, carried_attestations_admissible, on_block_checked_using, on_block_checked, round_votes, on_sg_vote, update_confirmation_with, get_head_in_tree_with, voter_filtered_block_tree, goldfish_vote_with, get_stable, get_confirmed, CarriedAdmission, NamedStore, initial, setClock, commitBlock, process_block_core, admit_row, admit_rows, admit_carried, on_block_with, TickOps, runWith.
-/

-- ── from Protocol/ConfirmationPolicy.lean ──
section
/-! # User confirmation record update -/

namespace DecoupledConsensusModel
namespace Protocol

variable {V : Type} [DecidableEq V]

/-- Retain confirmed progress when the candidate is an ancestor. Otherwise
accept the candidate, including when it conflicts with an old record.
Safety regimes must establish compatibility before claiming monotonicity. -/
def advance_confirmed (old candidate : Block V) : Block V :=
  if Block.preceq candidate old then old else candidate

/-- **The confirmation record's floor on the stable record**. Three cases, in order:

* the duty's own candidate, when it extends the new stable record;
* otherwise the prior record, while that still extends the new stable record, so
  a confirmation head that has left the stable branch is ignored rather than
  recorded;
* otherwise the stable record, which is the only case where the record moves
  off the prior record's chain, and it moves onto the stable one.

Two properties are branch conditions rather than theorems: `stable` precedes
the result in all three cases, and the result is never a strict ancestor of a
prefix the prior record already held — in the third case the guard
`¬ (stable ⪯ old)` is what rules that out.

Named AND `irreducible` so the tick's `rfl` seams stop here instead of
unfolding three nested conditionals inside every specialization: inlined, the
scheduler's literal-body equations cost minutes of `whnf` each. Proofs that need
the three cases `unfold` it, which the equation lemmas still allow. -/
@[irreducible] def floor_on_stable (stable candidate old : Block V) : Block V :=
  if Block.preceq stable candidate then candidate
  else if Block.preceq stable old then old else stable

end Protocol
end DecoupledConsensusModel
end

-- ── from Protocol/Handlers.lean ──
section
/-!
# §7.2 Duties and handlers — `sec:public-handlers` (PROTOCOL.md `sec:public-handlers`)

The shared cumulative handler cores used by the named runtime. The selected
executable path is `NamedRun → NamedNode.tick → NamedProfile.tick`. Named duty
adapters reuse these algorithms with saved frame grades.

The module is thin by construction. Everything §6 decides — the head, the round
decision, the proposal, the graded action — is called through
`Protocol.Store.toHealing`, so no rule of §6 is restated here. The integrated
reference store writes stay here because Lean binds a store type at definition time and
`Σ` is its own structure. Named reduction theorems in
the proof library guard these calls to the lower component cores.

One ordering is load-bearing, and it is branch order, not prose: the
confirmation evaluation runs **before** `attest` at `a_r = t_{rR+1} + 2Δ`, so
`attest` reads a `Σ.live_confirmed` recomputed in the same tick
(PROTOCOL.md `sec:healing-schedule`). The `t_s + Δ` branch's other ordering —
`set_fresh_root` before `goldfish_vote` — went with the round decision.

All four branches are independent `if`s, not `elif`s, and each reads the store as
mutated so far in the tick.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Protocol (ChainState HeightConfig)
open Protocol (SGVote)

variable {V : Type} [DecidableEq V] [Fintype V]

def state_transition (E : Env V) (cfg : HeightConfig) (σ : ChainState V)
    (B : Block V) : ChainState V :=
  let afterSlot := { σ with s := B.slot }
  let afterAttestations := B.attestations.foldl Protocol.process_attestation afterSlot
  Protocol.process_height_events E cfg { afterAttestations with L := B }

/-! ## The finality update at the cumulative store (PROTOCOL.md `alg:fg-store`) -/

/-- §5.2 `update_finality(Σ, σ)` (PROTOCOL.md `alg:fg-store`), restated at `Σ`.

The three statements run in order; each reads the store produced by the
previous statement. The body uses §5's pure `viable_tree` core, with the live
filter inlined. The third guard is `σ.F ∈ viable_tree(Σ)` (PROTOCOL.md
`alg:fg-store`). The `Σ.h_max` field only grows. -/
def update_finality (st : Store V) (σ : ChainState V) : Store V :=
  let afterMax : Store V := { st with h_max := max st.h_max σ.h }
  let afterJustification : Store V :=
    if Block.preceq afterMax.F σ.J &&
        decide (Protocol.HeightId.mk afterMax.h_j afterMax.J.root <
          Protocol.HeightId.mk σ.h_j σ.J.root) then
      { afterMax with J := σ.J, h_j := σ.h_j }
    else afterMax
  if Block.prec afterJustification.F σ.F &&
      Block.preceq σ.F afterJustification.J &&
      decide (σ.F ∈ Protocol.viable_tree afterJustification.σ
        afterJustification.F afterJustification.h_max afterJustification.T) then
    { afterJustification with F := σ.F }
  else afterJustification

/-! ## The four store handlers (PROTOCOL.md `alg:store`) -/

/-- §7.2 `on_goldfish_vote(Σ, vote)`, the **final** version
(PROTOCOL.md `alg:store`) — identical to §2's (PROTOCOL.md `alg:goldfish-store`).

The slot guard and the duplicate test, the two-vote cap, and the insertion that
stamps the vote. A rejected vote is never stamped. -/
def on_goldfish_vote (st : Store V) (vote : GoldfishVote V) : Store V :=
  if vote.slot < st.s - 1 ∨ st.s < vote.slot ∨ vote ∈ st.gf_votes vote.slot then
    st
  else if Protocol.equivocates (st.pool vote.slot) vote.val_index then
    st
  else
    { st with
      gf_votes := fun k =>
        if k = vote.slot then st.gf_votes k ++ [vote] else st.gf_votes k
      timestamp_vote := fun u =>
        if u = vote then some (st.t : Stamp) else st.timestamp_vote u }

/-- The source-aligned §7 ingress rejects a vote from outside its slot committee.
Vote head-slot validity is enforced when the head is resolved, as specified by
PROTOCOL.md `sec:goldfish-store`; unknown and later-slot heads remain in the
pool. For a committee vote this delegates to the existing admitted-vote handler. -/
def on_goldfish_vote_checked (E : Env V) (st : Store V)
    (vote : GoldfishVote V) : Store V :=
  if vote.val_index ∉ E.committee vote.slot then st else on_goldfish_vote st vote

/-- §7.2 raw valid-core `on_block(Σ, B)` (PROTOCOL.md `alg:store`).

`on_block_checked` is the receiver-facing handler. It runs this core only after
the carried-attestation round predicate passes.

The post-state is computed and stored before the block enters the tree, the
carried votes are unpacked in list order, and the finality caches
are folded afterwards. `Σ.σ[B.parent]` at a child of genesis is the initial chain
state.

The guard set is **slot-or-duplicate-or-unknown-parent, then admission, then
the transition's assert**. The first guard's third clause
is new: a block whose parent is not yet in the tree is rejected without marking
the block; a later delivery can be accepted after the parent arrives. Then
`Σ.F ⋠ B → return` (the finalized-ancestor check), then
`state_transition`'s `assert B.proposer = proposer(B.slot)` transcribed as an
admission guard, followed by the parent-slot assertion
`B.parent.slot < B.slot` as a no-op guard. Both assertions stay outside the
total `state_transition`. §5's figure now carries the same guard sequence, so
the definitions stay separate only because the store types differ.

The admission guard is load-bearing twice: it is what makes every `Σ.h_max`
bump live at bump time — `Σ.F` is always viable, with no fault bound
(`Proofs.NamedFinalizedViable.finalizedViable_readAt`) — and it makes **resolution
admission-dependent**: a vote resolves only when its head is in the receiving
store. The resolution-transfer conditionals carry that scoping
(`HeadArrivesBefore`, `HeadsResolveIn`, `BatchDelivered`).

The second clause makes re-processing a tree member a no-op, where §5's would
re-run the whole body: `Σ.timestamp(B)` becomes write-once on `Σ.T`, the
carried-vote fold does not run twice, and `update_finality` is not re-entered on
a block already held. Nothing below leans on any of the three yet — the clause
only removes work, so no proof needed it. -/
def on_block_using (E : Env V) (st : Store V) (B : Block V)
    (buildState : ChainState V → ChainState V) : Store V :=
  if st.s < B.slot ∨ B ∈ st.T ∨ B.parent ∉ st.T then
    st
  else if !Block.preceq st.F B then
    st
  else if B.proposer? ≠ some (E.proposer B.slot) then
    st
  else if ¬ (B.parent.slot < B.slot) then
    st
  else
    let state := buildState (st.σ B.parent)
    let stored : Store V :=
      { st with
        σ := fun C => if C = B then state else st.σ C
        T := insert B st.T
        timestamp_block := fun C =>
          if C = B then some (st.t : Stamp) else st.timestamp_block C }
    let unpacked := B.gf_votes.foldl (on_goldfish_vote_checked E) stored
    update_finality unpacked (unpacked.σ B)

/-- The default specializes the shared block-processing body. The elaborator
checks definitional equality and retains the unfolded body. -/
def on_block (E : Env V) (cfg : HeightConfig) (st : Store V) (B : Block V) :
    Store V :=
  on_block_using E st B
    (fun parentState => state_transition E cfg parentState B)

/-- A block is admissible only when every carried attestation is from its slot's
round or an earlier round. -/
def carried_attestations_admissible (hc : Protocol.HealConfig) (B : Block V) : Bool :=
  B.attestations.all (fun a => decide (a.round ≤ hc.round_of B.slot))

/-- The receiver-side block handler. Invalid carried attestations reject the
entire block before the raw valid-core handler runs. -/
def on_block_checked_using (handle : Store V → Store V) (hc : Protocol.HealConfig)
    (st : Store V) (B : Block V) : Store V :=
  if carried_attestations_admissible hc B then handle st else st

/-- The checked wrapper specializes the same carried-round guard. -/
def on_block_checked (E : Env V) (hc : Protocol.HealConfig) (cfg : HeightConfig)
    (st : Store V) (B : Block V) : Store V :=
  on_block_checked_using (fun current => on_block E cfg current B) hc st B

/-- §7.2 the figure's set binding, "the validator's confirmed blocks this
round" (PROTOCOL.md `alg:store`):
`round_votes ← {b.confirmed: b ∈ Σ.sg_votes[a.round], b.val_index = a.val_index}`
— named `round_votes` here.

A `Finset` image over the pool's set reading, so it is a **set** of confirmed
blocks — same-confirmed duplicates collapse, `⊥`-confirmed included — which is
what makes the figure's `|round_votes| = 2` guard mean two *distinct* confirmed
blocks. A top-level definition rather than the figure's inline binding, so the
guard equivalence (`Proofs.Optimistic.on_sg_vote_eq_two_guard`) can state
facts about it. -/
def round_votes (st : Store V) (a : CombinedAttestation V) : Finset (Option BlockId) :=
  ((st.sg_pool a.round).filter (fun b => b.val_index = a.val_index)).image
    (fun b => b.confirmed)

/-- §7.2 `on_sg_vote(Σ, a)`, the complete-store SG admission rule
(`alg:store`, with the SG rule defined in `alg:sg-store`).

The handler rejects stale or future-round attestations, duplicate projected
votes, and a third distinct confirmed head by one validator in a round. The
`round_votes` set is the projected `(validator, round, confirmed)` view, so
pair fields do not create additional SG votes. The guard is the complete-store
form of the paper's two-vote equivocation cap; the proof-side equivalence
result records its relation to the lower-layer representation.

Direct attestations reach the raw pool through the named admission path. Carried
rows reach `on_sg_vote` through `admit_carried`, then `admit_rows`, then
`admit_row`, after the named block is admitted. -/
def on_sg_vote (hc : Protocol.HealConfig) (st : Store V)
    (a : CombinedAttestation V) : Store V :=
  if a.round < hc.round_of st.s - hc.η_SG ∨ hc.round_of st.s < a.round ∨
      a.confirmed ∈ round_votes st a ∨ (round_votes st a).card = 2 then
    st
  else
    { st with
      sg_votes := fun r =>
        if r = a.round then st.sg_votes r ++ [a] else st.sg_votes r
      timestamp_sg_vote := fun u =>
        if u = sgVote a then some (st.t : Stamp) else st.timestamp_sg_vote u }

/-- §7.2 `update_confirmation(Σ, s)`, the **final** version
(PROTOCOL.md `alg:store`): the composed fork choice, genuine-or-nothing.

```
tree ← get_filtered_block_tree(Σ); root ← get_fg_root(Σ)
A ← get_sg_root(Σ, round(Σ.s))
H ← ghost(A, tree, goldfish_score(votes, s, ·), eligible)
Σ.live_confirmed ← H if eligible(H), else root
if H ⋠ Σ.latest_confirmed then Σ.latest_confirmed ← H
```

The window sets — `early_votes`, `late_votes`, `support_votes`,
`voters_count`, `eligible` — are §2's, byte for byte, self-pair score included: support excludes equivocators outright and the
denominator is the late participants. The walk and its tail use these rules:

* **The walk is the composed fork choice's.** Anchor `get_sg_root(Σ, round(Σ.s))`
  over `get_filtered_block_tree(Σ)`.
* **Genuine-or-nothing.** The confirmation advances only when the walk's result
  itself carries a window majority, and otherwise the slot confirms nothing —
  `Σ.live_confirmed ← root`. A walk-*stepped* result satisfies `eligible` by
  construction (each step passed the gate, `Protocol.ghost_eligible`),
  so the guard bites only at `H = A`, where it reads `eligible(A)`: "a window
  majority confirms the anchor itself".
* **The root value is a floor marker, not a confirmation.** It sits below both
  of `attest`'s walk floors (`root ⪯ A` and `root ⪯ A_G2`, the candidate tree's
  own filter), so on an unconfirmed slot the veto segments `[A, C]` and
  `[A_G2, C]` are empty and `attest`'s grade-2 and anchor fallbacks fire
  (PROTOCOL.md `sec:public-handlers`).
* **The two confirmation values have different uses.** `Σ.live_confirmed`
  supplies voting and can retreat to the root. The user record
  `Σ.latest_confirmed` takes the walk result, which equals the SG anchor when
  the eligibility test fails. It retains an old descendant and accepts an
  extension or a conflicting replacement. Its monotonicity is therefore a
  safety-regime theorem. Consensus duties do not read this field. The client
  accessor `get_confirmed` combines it with `F`; finality updates do not write it.

Rationale — safety ranked over totality: confirmation is genuine or absent,
which decouples confirmation safety from healing at the cost that a
no-Goldfish-majority, no-`A_G2` slot confirms nothing
(`the design` §9, "Confirmation-safety statement").

The vote sets are frozen at `t_s + 2Δ` and `t_s + 6Δ` while the tree, the root
and the anchor are read at call time; the two are not remarked on together. The figure's conditional assignment and its guarded tail are transcribed
as two conditional field values in one record update — same store, because the
two writes are sequenced only through the selected value `C`. -/
def update_confirmation_with (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Store V)
    (s : Slot) : Store V :=
  let early_votes := beforeCutoff st.tau (Protocol.support_cutoff E s) (st.pool s)
  let late_votes :=
    beforeCutoff st.timestamp_vote (Protocol.confirmation_time E s) (st.pool s)
  let support_votes :=
    early_votes.filter (fun vote =>
      Protocol.no_second_vote_in late_votes vote = true)
  let count := Protocol.voters_count E late_votes s
  let score := Protocol.goldfish_score E st.T support_votes support_votes s
  let eligible := fun B => decide (count < 2 * score B)
  let tree := Protocol.get_filtered_block_tree st.toHealing.toFG
  let root := Protocol.get_fg_root st.toHealing.toFG
  let A := Protocol.get_sg_root_with contract E hc st.toHealing (hc.round_of st.s)
  let H := Protocol.ghost A tree score eligible
  let C := if eligible H then H else root
  { st with
    live_confirmed := C
    -- The optional G2 candidate is advanced on the store's round. The later
    -- confirmation write floors the result on the stable record.
    latest_stable :=
      match contract.stableRoot E hc st.toHealing (hc.round_of st.s) with
      | some G => advance_confirmed st.latest_stable G
      | none => st.latest_stable
    -- The confirmation record is floored on the stable record produced by this
    -- write. The three arms keep an extending candidate, the prior record, or
    -- the stable record.
    latest_confirmed :=
      floor_on_stable
        (match contract.stableRoot E hc st.toHealing (hc.round_of st.s) with
          | some G => advance_confirmed st.latest_stable G
          | none => st.latest_stable)
        (match contract.confirmationSG with
          | .optional select =>
            if eligible H then advance_confirmed st.latest_confirmed H
            else
              match select E hc st.toHealing s with
              | some candidate => advance_confirmed st.latest_confirmed candidate
              | none => st.latest_confirmed)
        st.latest_confirmed }

/-! ## The four duties (PROTOCOL.md `alg:duties`)

Materialized in the assembly's own pseudocode ; the
bodies are §2's and §6's, and only the store writes are this layer's. -/

/-- §6.4 `get_head_in_tree(Σ, tree, votes, support_votes, k)` at the cumulative
store. It projects to §6's explicit-tree head. The supplied tree changes only
the Goldfish child domain; the SG anchor, score resolution, and eligibility
inputs remain the full store. -/
def get_head_in_tree_with (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Store V)
    (tree : Finset (Block V)) (votes support_votes : Finset (GoldfishVote V))
    (k : Slot) : Block V :=
  Protocol.get_head_in_tree_with_layer contract E hc st.toHealing tree votes support_votes k

/-- §7.2 `voter_filtered_block_tree(Σ, s)`: form the voter's frozen
processed-block view and recompute viability and the FG-root filter inside that
view. This is not an intersection with the ordinary full-store candidate tree:
a late witness outside the processed-block view cannot make an earlier block
viable for this vote. -/
def voter_filtered_block_tree (E : Env V) (st : Store V) (s : Slot) :
    Finset (Block V) :=
  let blocks :=
    Protocol.voter_processed_block_tree E st.toHealing.toFG.toSG.toGoldfishStore s
  Protocol.get_filtered_block_tree_from st.toHealing.toFG blocks

/-- §2.5 `goldfish_vote(Σ)` at the cumulative store
(PROTOCOL.md `alg:goldfish-store`, `alg:duties`). The two merged vote views retain their §2
semantics. The vote duty alone restricts the Goldfish child domain to
`voter_filtered_block_tree`; proposal, confirmation, attestation, and ordinary
`get_head` calls remain full-tree. -/
def goldfish_vote_with (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (st : Store V) : Store V × Option (GoldfishVote V) :=
  let s := st.s
  let votes := Protocol.voter_view E st.toHealing.toFG.toSG.toGoldfishStore s
  let support_votes := Protocol.voter_support_view E st.toHealing.toFG.toSG.toGoldfishStore s
  let tree := voter_filtered_block_tree E st s
  let H := get_head_in_tree_with contract E hc st tree votes support_votes (s - 1)
  if nd.val_index ∈ E.committee s then
    let vote : GoldfishVote V := ⟨nd.val_index, s, H.root⟩
    (on_goldfish_vote_checked E st vote, some vote)
  else
    (st, none)

end Protocol
end DecoupledConsensusModel
end

-- ── from Protocol/Confirmed.lean ──
section
/-! # The three user-facing chains

The store exposes three outputs, nested by construction: finalized (`Σ.F`),
stable (`get_stable`), confirmed (`get_confirmed`). Addendum 34 22.
-/

namespace DecoupledConsensusModel
namespace Protocol

variable {V : Type} [DecidableEq V]

/-- The client-facing stable tip. The stored stable record is used only if it
extends the current finalized block; otherwise finality is the output. The
stable chain is the SG layer: its record is the latest G2 root, advanced by
`advance_confirmed` at the confirmation duty. This accessor does not change the
historical record or any voting rule. -/
def get_stable (st : Store V) : Block V :=
  if Block.preceq st.F st.latest_stable then st.latest_stable else st.F

/-- The client-facing confirmed tip. The confirmed chain is the fast layer over
the stable chain, so the stored confirmation record is used only if it extends
the stable output; otherwise the stable output is returned. A record that lags
behind or conflicts with the stable chain is not exposed. This accessor does not
change the historical record or any voting rule. -/
def get_confirmed (st : Store V) : Block V :=
  if Block.preceq (get_stable st) st.latest_confirmed then st.latest_confirmed
  else get_stable st

end Protocol
end DecoupledConsensusModel
end

-- ── from Protocol/CarriedAdmission.lean ──
section
/-! Carried-attestation admission seam for the selected named runtime. -/
namespace DecoupledConsensusModel
namespace Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

inductive CarriedAdmission where
  | alsoCarried
  deriving DecidableEq

end Protocol
end DecoupledConsensusModel
end

-- ── from Protocol/NamedStore.lean ──
section
/-! Active named block-processing path using the shared handler. The core keeps
the named body and geometry aligned; `NamedAdmission.on_block_with.alsoCarried`
then admits carried rows after the finality update. -/
namespace DecoupledConsensusModel.Protocol

structure NamedStore (V : Type) where
  core : Store V
  bodies : Finset (NamedBlock V)
  sg_rows : Round → List (NamedAttestation V)

namespace NamedStore
variable {V : Type} [DecidableEq V] [Fintype V]

def initial : NamedStore V := ⟨Store.init, {NamedBlock.genesis}, fun _ => []⟩

/-- Clock staging changes no signed body or pool entry. -/
def setClock (E : Env V) (st : NamedStore V) (t : Time) : NamedStore V :=
  { st with core := { st.core with t := t, s := E.slotOf t } }

/-- Commit the named body only when the common handler inserted its fresh
geometry. Existing-erasure aliases do not replace the retained signed body. -/
def commitBlock (before : NamedStore V) (after : Store V) (B : NamedBlock V) : NamedStore V :=
  if B.erase ∉ before.core.T ∧ B.erase ∈ after.T then
    { before with core := after, bodies := insert B before.bodies }
  else { before with core := after }

/-- The exact named parent must be held. All ordinary guards, insertion,
GF carried-vote processing and finality updates use the shared block core.
The state builder is fixed here to B's actual named rows. No metadata callback
is an argument to this operation. Pool admission deliberately remains a tail. -/
def process_block_core (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : NamedStore V) (B : NamedBlock V) : NamedStore V :=
  if B.parent ∉ st.bodies then st else
    let after := on_block_checked_using
      (fun current => on_block_using E current B.erase
        (fun parentState => Protocol.named_transition E cfg parentState B)) hc st.core B.erase
    commitBlock st after B

end NamedStore
end DecoupledConsensusModel.Protocol
end

-- ── from Protocol/NamedAdmission.lean ──
section
/-! Named carried-row admission. The existing `on_sg_vote` decides admission once.
The first admitted original named row is retained; SG-projection duplicates
are still rejected. The selected `.alsoCarried` path admits carried rows after
the named block core. -/
namespace DecoupledConsensusModel.Protocol.NamedAdmission
variable {V : Type} [DecidableEq V] [Fintype V]

/-- New erased-row membership witnesses actual admission by the existing SG
handler. No guard or receipt algorithm is copied. Metadata is the input row. -/
def admit_row (hc : Protocol.HealConfig) (st : NamedStore V) (row : NamedAttestation V) :
    NamedStore V :=
  let after := on_sg_vote hc st.core row.erase
  if row.erase ∉ st.core.sg_pool row.round ∧ row.erase ∈ after.sg_pool row.round then
    { st with
      core := after
      sg_rows := fun r => if r = row.round then st.sg_rows r ++ [row] else st.sg_rows r }
  else { st with core := after }

def admit_rows (hc : Protocol.HealConfig) (st : NamedStore V)
    (rows : List (NamedAttestation V)) : NamedStore V := rows.foldl (admit_row hc) st

/-- Only a newly admitted full named body triggers the carried row tail.
The tail reads its original row list after block-core processing. -/
def admit_carried (admission : CarriedAdmission) (hc : Protocol.HealConfig)
    (before after : NamedStore V) (B : NamedBlock V) : NamedStore V :=
  if B ∉ before.bodies ∧ B ∈ after.bodies then admit_rows hc after B.attestations else after

/-- Concrete named block core followed by the named carried-row admission. The
active named receipt path calls this admission operation. -/
def on_block_with (admission : CarriedAdmission) (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : NamedStore V) (B : NamedBlock V) : NamedStore V :=
  admit_carried admission hc st (NamedStore.process_block_core E hc cfg st B) B

end DecoupledConsensusModel.Protocol.NamedAdmission
end

-- ── from Protocol/TickScheduler.lean ──
section
/-! Shared timetable and duty order. Operations are fixed by each concrete
family. Payload constructors and the final continuation consume computed
outputs; they do not provide protocol observations. -/
namespace DecoupledConsensusModel.Protocol.TickScheduler

structure TickOps (State Record BlockOut VoteOut AttOut : Type) where
  clock : State → Time → Slot → State
  slot : State → Slot
  proposal : State → State × Option BlockOut
  vote : State → State × Option VoteOut
  confirmation : State → Slot → State
  attestation : State → Record → State × Record × AttOut

/-- All branches read the state produced by the preceding duty. The final
round and awake guard use the state after confirmation. -/
def runWith {V State Record BlockOut VoteOut AttOut Out Result : Type}
    [DecidableEq V] [Fintype V] (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (ops : TickOps State Record BlockOut VoteOut AttOut)
    (blockOut : BlockOut → Out) (voteOut : VoteOut → Out) (attOut : AttOut → Out)
    (finish : State → Record → List Out → Result)
    (st : State) (record : Record) (t : Time) : Result :=
  let s := E.slotOf t
  let st0 := ops.clock st t s
  let st1 :=
    if 0 < s ∧ t = Protocol.proposal_time E s ∧ E.proposer s = nd.val_index then
      (ops.proposal st0).1
    else st0
  let emitted1 : List Out :=
    if 0 < s ∧ t = Protocol.proposal_time E s ∧ E.proposer s = nd.val_index then
      match (ops.proposal st0).2 with
      | none => []
      | some B => [blockOut B]
    else []
  let st2 :=
    if 0 < s ∧ t = Protocol.vote_time E s then (ops.vote st1).1
    else st1
  let emitted2 : List Out :=
    if 0 < s ∧ t = Protocol.vote_time E s then
      (ops.vote st1).2.toList.map voteOut
    else []
  let st3 :=
    if 0 < s ∧ t = Protocol.support_cutoff E s then ops.confirmation st2 (s - 1)
    else st2
  if t = hc.a E.Δ (hc.round_of (ops.slot st3)) ∧
      nd.awake (hc.round_of (ops.slot st3)) = true then
    let attested := ops.attestation st3 record
    finish attested.1 attested.2.1 (emitted1 ++ emitted2 ++ [attOut attested.2.2])
  else
    finish st3 record (emitted1 ++ emitted2)

end DecoupledConsensusModel.Protocol.TickScheduler
end

end
