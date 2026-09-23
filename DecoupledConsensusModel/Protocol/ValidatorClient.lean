module
public import DecoupledConsensusModel.Protocol.ForkChoice.Goldfish
public import DecoupledConsensusModel.Objects.NamedBlocks

@[expose] public section

/-!
# `DecoupledConsensusModel/Protocol/ValidatorClient.lean`

Purpose: Section 7, block 4 — the validator client: the validator record Lambda, finality_pair, height_pair, create_attestation, record_attestation.
Paper: `docs/PROTOCOL.md` `sec:public-handlers`; algorithm block: `alg:pair-rules`.

Defines: Record, finality_pair, height_pair, and create_attestation.

Read after: `DecoupledConsensusModel.Protocol.ForkChoice.Goldfish`, `DecoupledConsensusModel.Objects.NamedBlocks`
Read next: `DecoupledConsensusModel.Protocol.Duties.Proposals`.

State read: the protocol environment, schedule, store layers, and the view inputs named by the definitions.
State written: the returned store, chain state, record, or view value; pure readers write no state.

Representation notes: Typed Lean records, finite collections, and projections preserve the executable protocol representation. This module states no proof theorem.
-/

-- ── from FGForkChoice/Attest.lean ──
section
/-!
# §5.3 SG/FG attestation — `def:antislashing`, `alg:pair-rules`
(PROTOCOL.md `def:antislashing`, `alg:pair-rules`)

The anti-slashing record, the two pair rules, the duty that assembles a combined
attestation from them, and the §5 store handlers.

The intermediate §5 proposer, Goldfish voter, and tick are not retained as a
second executable protocol. Their only caller was that intermediate tick. The
final versions are `Protocol.propose_block`, `Protocol.goldfish_vote`, and
`Protocol.on_tick`, which preserve the ordered independent branches. At §5 the
proposer and voter selected this layer's `get_head`, and the attestation branch
ran last at `a_r` without an `s > 0` guard. The §5 `attest` remains here because
the record-safety and gating proofs use its exact ordinary-attestation view.

Four shapes are forced here.

* **`Λ` is not a store field.** "It belongs to the validator, not to the store,
  and `record_attestation` is the only place that writes it"
  (PROTOCOL.md `def:antislashing`). Every function that the figure shows
  mutating `Λ` therefore takes it and returns it, beside whatever else it
  produces (PROTOCOL.md `alg:pair-rules`).
* **Targets are compared by root.** `Λ.target[h]` and `Λ.lock[h]` are compared
  against `σ[C].T_h` and `σ[H].J`, which are blocks, and the pair the rule
  returns carries a `BlockId`. One side has to be
  projected; roots answer every test and are what the wire object needs anyway,
  which is the choice §4 already made for `process_attestation`.
* **The pair rules take no store and write no record.** `create_attestation`
  "never reads the store" (PROTOCOL.md `def:antislashing`) and
  `record_attestation` is "the only writer of `Λ`" (PROTOCOL.md
  `alg:pair-rules`), so the two rules take plain
  fields and return pairs. `height_pair` receives the same attestation's finality
  pair rather than reading a lock the other rule just wrote.
* **The two rules read different chain states.** The height pair is built from a
  confirmed block's height fields; the finality pair from the head's finality
  fields (PROTOCOL.md `alg:pair-rules`, "built from a confirmed block's
  height fields"). The caller projects both, "and the graded action passes its
  own confirmed block and head" (PROTOCOL.md `alg:pair-rules`).
-/

namespace DecoupledConsensusModel
namespace Protocol

open Protocol (ChainState HeightConfig)

/-! ## The anti-slashing record (PROTOCOL.md `def:antislashing`) -/

/-- §5.3 `def:antislashing`: the record `Λ`, holding for every height the
validator's first target, whether it emitted an empty-target vote, and the target
of its first finality pair (PROTOCOL.md `def:antislashing`).

Three total maps over `Height` with the stated default `(⊥, false, ⊥)`: the
document indexes by height with no pruning and no bound. Targets are
roots.

The record carries no validator parameter — it belongs to one validator, the
node's `val_index`, and holds no field that mentions another.

`Record` contains the three map fields
`(target[·], timeout[·], lock[·])`. The complete §7 `Λ` also contains the
timeout-history set carried by `NamedRecord`, initially empty, owned by the
validator with `record_attestation` its only writer (PROTOCOL.md
`sec:complete-store`). -/
structure Record where
  /-- §5.3 `Λ.target[h]`: the validator's first target at height `h`
  (PROTOCOL.md `def:antislashing`). -/
  target : Height → Option BlockId
  /-- §5.3 `Λ.timeout[h]`: whether it emitted an empty-target vote at height `h`
  (PROTOCOL.md `def:antislashing`). -/
  timeout : Height → Bool
  /-- §5.3 `Λ.lock[h]`: the target of its first finality pair at height `h`
  (PROTOCOL.md `def:antislashing`). -/
  lock : Height → Option BlockId

namespace Record

/-- §5.3 the initial record: `(⊥, false, ⊥)` at every height
(PROTOCOL.md `def:antislashing`). -/
def initial : Record where
  target := fun _ => none
  timeout := fun _ => false
  lock := fun _ => none

/-- §5.3 `Λ.target[h] ← T` (PROTOCOL.md `alg:pair-rules`, "record_attestation"). -/
def with_target (Λ : Record) (h : Height) (T : BlockId) : Record :=
  { Λ with target := fun k => if k = h then some T else Λ.target k }

/-- §5.3 `Λ.timeout[h] ← true` (PROTOCOL.md `alg:pair-rules`, "record_attestation"). -/
def with_timeout (Λ : Record) (h : Height) : Record :=
  { Λ with timeout := fun k => if k = h then true else Λ.timeout k }

/-- §5.3 `Λ.lock[h] ← J` (PROTOCOL.md `alg:pair-rules`, "record_attestation"). -/
def with_lock (Λ : Record) (h : Height) (J : BlockId) : Record :=
  { Λ with lock := fun k => if k = h then some J else Λ.lock k }

end Record

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The pair rules and the record interface
(PROTOCOL.md `def:antislashing`, `alg:pair-rules`)

This module structures the two pair rules separately. They take plain fields and return a
pair. `create_attestation` is the record's whole interface — "it takes the record
and the vote information, produces the attestation, and updates the record before
releasing it; it never reads the store" (PROTOCOL.md `def:antislashing`) — and
`record_attestation` is the only writer.

Two consequences, and both are semantic rather than cosmetic.

* **`height_pair` sees its own attestation's lock.** It receives the finality
  pair and overrides the lock at that height, so one attestation cannot form
  E1 evidence (PROTOCOL.md `alg:pair-rules`).
* **`target[h]` is written whenever a nonempty target is emitted at a fresh
  height**, not only on the "no history" row. `record_attestation` folds the
  emitted attestation, so the lock-repeat and target-repeat rows also write
  `target[h]` if it was empty.
-/

/-- §5.3 `finality_pair(Λ, h_j, J, h_F)` (PROTOCOL.md `alg:pair-rules`). **Final.**

Reads the finality fields the caller took from the head's chain state — "its
subject is already justified, so it may read an unconfirmed chain, and the head
chain state carries the freshest justification" (PROTOCOL.md `alg:pair-rules`). Emits
`(h_j, J)` exactly when a justification is not yet finalized *and* the record
allows it; otherwise the empty pair, which is `none` of an `Option FinalityPair`.

**It no longer writes the lock.** `record_attestation` does, from the emitted
attestation.

The record test allows `Λ.target[h_j]` to be empty or equal to `J`. A validator
that never voted at `h_j` can therefore emit the finality pair. The emitted pair
writes `Λ.lock[h_j] = J`, so later height pairs at that height can only target
`J` or abstain. A recorded timeout or a different target still blocks the pair. -/
def finality_pair (Λ : Record) (h_j : Height) (J : BlockId) (h_F : Height) :
    Option FinalityPair :=
  if h_F < h_j then
    if (Λ.target h_j = none ∨ Λ.target h_j = some J) ∧
        Λ.timeout h_j = false ∧
        (Λ.lock h_j = none ∨ Λ.lock h_j = some J) then
      some ⟨h_j, J⟩
    else
      none
  else
    none

/-- §5.3 the lock `height_pair` reads: the record's lock at `h_c`, overridden by
this attestation's own finality pair when the two heights agree
(PROTOCOL.md `alg:pair-rules`, "this attestation's own lock").

"`height_pair` receives the same attestation's finality pair as the lock at its
height, so one attestation never forms E1 evidence" (PROTOCOL.md `alg:pair-rules`).
The helper makes the same-attestation lock explicit for `height_pair`'s branch
analysis. -/
def own_lock (Λ : Record) (h_c : Height) (fp : Option FinalityPair) :
    Option BlockId :=
  match fp with
  | some p => if p.height = h_c then some p.target else Λ.lock h_c
  | none => Λ.lock h_c

/-- §5.3 `height_pair(Λ, h_c, T_c, ν, h_f, T_f)` (PROTOCOL.md `alg:pair-rules`).
**Final.**

Reads the height fields the caller took from a confirmed block's chain state —
"a target vote can create a justification, and only confirmed blocks may be
justified" (PROTOCOL.md `alg:pair-rules`).

The three height fields arrive as one `Option`: `(⊥, ⊥, ⊥)` is what §6 passes
when there is no fresh quorum (PROTOCOL.md `alg:round-action`, "no fresh
quorum"), and the document's
`h_c = ⊥` guard tests exactly that. The finality pair arrives whole, and the lock
at `h_c` is overridden by it when the two heights agree.

The branches, in the document's order, with its fall-through:

| `timeout[h_c]` | `lock` | `target[h_c]` | `ν` | Result |
|---|---|---|---|---|
| true | — | — | — | `(h_c, ⊥)` |
| false | `= T_c` | — | — | `(h_c, T_c)` |
| false | `≠ ⊥`, `≠ T_c` | — | — | `(⊥, ⊥)` |
| false | `⊥` | `= T_c` | — | `(h_c, T_c)` |
| false | `⊥` | `≠ ⊥`, `≠ T_c` | — | `(h_c, ⊥)` |
| false | `⊥` | `⊥` | false | `(h_c, T_c)` |
| false | `⊥` | `⊥` | true | `(h_c, ⊥)` |

The asymmetry between rows 3 and 5 is the subtle part and is written as stated: a
validator **locked elsewhere** returns the *empty pair* and so abstains from the
height entirely ("wait out the height"), while a validator whose **recorded**
target disagrees falls through to a timeout at `h_c` and keeps participating in
progress. Both target tests are equalities, not ancestry. -/
def height_pair (Λ : Record) (fields : Option (Height × BlockId × Bool))
    (fp : Option FinalityPair) : HeightPair :=
  match fields with
  | none => .empty
  | some (h_c, T_c, ν) =>
    if Λ.timeout h_c then
      .timeout h_c
    else
      match own_lock Λ h_c fp with
      | some locked => if locked = T_c then .target h_c T_c else .empty
      | none =>
        match Λ.target h_c with
        | some recorded => if recorded = T_c then .target h_c T_c else .timeout h_c
        | none => if ν then .timeout h_c else .target h_c T_c

/-- §5.3 `record_attestation(Λ, a)` (PROTOCOL.md `alg:pair-rules`): the **only**
writer of `Λ`, folding the attestation about to be released.

`target[h]` is write-once, as the guard `Λ.target[h] = ⊥` says; `timeout[h]` and
`lock[h_f]` are idempotent at the values the pair rules can emit. -/
def record_attestation (Λ : Record) (a : CombinedAttestation V) : Record :=
  let afterLock :=
    match a.finality_pair with
    | some p => Λ.with_lock p.height p.target
    | none => Λ
  match a.height_pair with
  | .empty => afterLock
  | .timeout h => afterLock.with_timeout h
  | .target h T => if afterLock.target h = none then afterLock.with_target h T else afterLock

/-- §5.3 `create_attestation(Λ, r, confirmed, h_c, T_c, ν, h_j, J, h_F)`
(PROTOCOL.md `alg:pair-rules`): the validator-client side, with
**no store access**.

The two pair rules, then the attestation, then the record — "record, then
release". Returns the updated record beside the attestation, because `Λ` is not a
store field (PROTOCOL.md `def:antislashing`). -/
def create_attestation (Λ : Record) (val_index : V) (r : Round)
    (confirmed : Option BlockId) (fields : Option (Height × BlockId × Bool))
    (h_j : Height) (J : BlockId) (h_F : Height) :
    Record × CombinedAttestation V :=
  let fp := finality_pair Λ h_j J h_F
  let hp := height_pair Λ fields fp
  let a : CombinedAttestation V := ⟨val_index, r, confirmed, hp, fp⟩
  (record_attestation Λ a, a)

end Protocol
end DecoupledConsensusModel
end

-- ── from FGForkChoice/NamedRecord.lean ──
section
/-! Named-row signing state. `Record` contains the target, timeout, and lock maps;
`NamedRecord` adds the active timeout-history set. The history records timeout
annotations; it never suppresses a repeated transmission or replaces a
height-wide target/finality lock. -/
namespace DecoupledConsensusModel.Protocol

structure NamedRecord where
  legacy : Record
  timeoutHistory : Finset (Height × BlockId)

namespace NamedRecord

/-- Exact input fields supplied to the existing signing client. -/
structure Input (V : Type) where
  val_index : V
  round : Round
  confirmed : Option BlockId
  fields : Option (Height × BlockId × Bool)
  h_j : Height
  J : BlockId
  h_F : Height

def initial : NamedRecord := ⟨Record.initial, ∅⟩

/-- A fixed codec. The creator proves its old output agrees with these actual
source fields; no receiver state or context callback participates. -/
def encodeHeight (fields : Option (Height × BlockId × Bool))
    (pair : HeightPair) : NamedHeightPair :=
  match pair, fields with
  | .empty, _ => .empty
  | .target _ _, some (h, entry, _) => .vote h entry false
  | .timeout _, some (h, entry, _) => .vote h entry true
  | _, none => .empty

def encodeRow {V : Type} (fields : Option (Height × BlockId × Bool))
    (row : CombinedAttestation V) : NamedAttestation V :=
  ⟨row.val_index, row.round, row.confirmed, encodeHeight fields row.height_pair,
    row.finality_pair⟩

/-- Set insertion is idempotent; membership is not an emission guard. -/
def rememberTimeout (history : Finset (Height × BlockId)) : NamedHeightPair →
    Finset (Height × BlockId)
  | .vote h entry true => insert (h, entry) history
  | _ => history

def legacyCreate {V : Type} (record : Record) (input : Input V) :
    Record × CombinedAttestation V :=
  create_attestation record input.val_index input.round input.confirmed input.fields
    input.h_j input.J input.h_F

/-- The base client makes all pair decisions and updates its record once.
The extra history records exactly the resulting named timeout pair. -/
def create {V : Type} (record : NamedRecord) (input : Input V) :
    NamedRecord × NamedAttestation V :=
  let old := legacyCreate record.legacy input
  let row := encodeRow input.fields old.2
  (⟨old.1, rememberTimeout record.timeoutHistory row.height_pair⟩, row)

end NamedRecord
end DecoupledConsensusModel.Protocol
end

end
