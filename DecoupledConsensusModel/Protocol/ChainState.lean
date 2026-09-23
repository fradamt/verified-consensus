module
public import DecoupledConsensusModel.Objects.Time
public import DecoupledConsensusModel.Objects.Identifiers
public import DecoupledConsensusModel.Objects.Parameters
public import DecoupledConsensusModel.Objects.Blocks
public import DecoupledConsensusModel.Objects.Weights
public import DecoupledConsensusModel.Objects.NamedBlocks

@[expose] public section

/-!
# `DecoupledConsensusModel/Protocol/ChainState.lean`

Purpose: Section 7, block 5 — the chain state sigma, its quorum reads, state_transition, process_attestation, process_height_events, advance_height, and the E1/E2 slashing conditions.
Paper: `docs/PROTOCOL.md` `sec:public-handlers`; algorithm block: `alg:state-transition`.

Defines: ChainState, process_attestation, and process_height_events.

Read after: `DecoupledConsensusModel.Objects.Time`, `DecoupledConsensusModel.Objects.Identifiers`, `DecoupledConsensusModel.Objects.Parameters`
Read next: `DecoupledConsensusModel.Protocol.Handlers`.

State read: the protocol environment, schedule, store layers, and the view inputs named by the definitions.
State written: the returned store, chain state, record, or view value; pure readers write no state.

Representation notes: Typed Lean records, finite collections, and projections preserve the executable protocol representation. This module states no proof theorem.
-/

-- ── from FinalityGadget/Attestations.lean ──
section
/-!
# §4 Combined attestations — slashing and equivocation (PROTOCOL.md
`sec:state-machine`)

The attestation record itself, and the two derived pairs, are `Substrate`: `Block` carries attestations, so the type must exist
before `Block` does. What is left for this module is everything the document
says *about* pair occurrences — the slashing conditions E1 and E2, the SG
head-equivocation test that reads the attestation's `head` projection, and the
honest emission budget.

Targets are `BlockId`. Signature validity is an execution premise; no handler
verifies a signature. These predicates concern the attestation's pair
occurrences and head equivocation.

Nothing in §4–§7 calls these predicates: E1 and E2 constrain honest behaviour
and accountability only, and no handler, validity rule or slashing function
references them. They are here because the document states them.
-/

namespace DecoupledConsensusModel

namespace Protocol

/-- §4 the height-pair half of E1: a height pair `(h,T')` conflicts with a
nonempty finality pair `(h,T)` when the heights agree and `T' ≠ T`, `T' = ⊥`
included (PROTOCOL.md `sec:state-machine`, "one finality pair is").

The empty height pair has height `⊥` and so conflicts with nothing
(PROTOCOL.md `sec:state-machine`, "An empty height pair has height"). -/
def conflictsWithFinality : HeightPair → FinalityPair → Bool
  | .empty, _ => false
  | .timeout height, pair => decide (height = pair.height)
  | .target height target, pair =>
      decide (height = pair.height) && !decide (target = pair.target)

variable {V : Type} [DecidableEq V]

/-- §4 "two pair occurrences from one validator" (PROTOCOL.md
`sec:state-machine`, "Two pair occurrences from one validator"). -/
def sameValidator (left right : CombinedAttestation V) : Bool :=
  decide (left.val_index = right.val_index)

/-- §3 one round, the scope of the head-equivocation test. -/
def sameRound (left right : CombinedAttestation V) : Bool :=
  decide (left.round = right.round)

/-- §4 E1's field conflict, before the one-signer test (PROTOCOL.md
`sec:state-machine`, "one finality pair is").
Either attestation may supply the finality pair; taking `left = right` is what
makes "the conflicting occurrences can be in one attestation"
(PROTOCOL.md `sec:state-machine`, "The conflicting occurrences can be in
one attestation") hold. -/
def e1Fields (left right : CombinedAttestation V) : Bool :=
  left.finality_pair.elim false (conflictsWithFinality right.height_pair) ||
    right.finality_pair.elim false (conflictsWithFinality left.height_pair)

/-- §4 E2's field conflict, before the one-signer test
(PROTOCOL.md `sec:state-machine`, "two height pairs are"): two height pairs
`(h,T)`, `(h,T')` with `T,T' ≠ ⊥` and
`T ≠ T'`. A timeout or empty pair on either side is not E2. -/
def e2Fields (left right : CombinedAttestation V) : Bool :=
  match left.height_pair, right.height_pair with
  | .target leftHeight leftTarget, .target rightHeight rightTarget =>
      decide (leftHeight = rightHeight) && !decide (leftTarget = rightTarget)
  | _, _ => false

/-- §4 **E1**: one finality pair is `(h,T)` with `T ≠ ⊥`, and one height pair is
`(h,T')` with `T' ≠ T`, including `T' = ⊥` (PROTOCOL.md `sec:state-machine`,
"one finality pair is"). -/
def e1Slashable (left right : CombinedAttestation V) : Bool :=
  sameValidator left right && e1Fields left right

/-- §4 **E2**: two height pairs are `(h,T)` and `(h,T')` with `T,T' ≠ ⊥` and
`T ≠ T'` (PROTOCOL.md `sec:state-machine`, "two height pairs are"). -/
def e2Slashable (left right : CombinedAttestation V) : Bool :=
  sameValidator left right && e2Fields left right

/-- §4 slashable under either condition (PROTOCOL.md `sec:state-machine`,
"slashable under either condition"). -/
def slashable (left right : CombinedAttestation V) : Bool :=
  e1Slashable left right || e2Slashable left right

/-- §4 the conflicting occurrences can be in one attestation. -/
def selfSlashable (a : CombinedAttestation V) : Bool :=
  slashable a a

/-- §3, §7 two distinct heads from one validator in one round. -/
def sgHeadEquivocation (left right : CombinedAttestation V) : Bool :=
  sameValidator left right && sameRound left right &&
    !decide (left.confirmed = right.confirmed)

/-- §4 E1 as a proposition. -/
def E1Slashable (left right : CombinedAttestation V) : Prop :=
  e1Slashable left right = true

/-- §4 E2 as a proposition. -/
def E2Slashable (left right : CombinedAttestation V) : Prop :=
  e2Slashable left right = true

/-- §4 slashability as a proposition (PROTOCOL.md `sec:state-machine`,
"slashable under either condition"). -/
def Slashable (left right : CombinedAttestation V) : Prop :=
  slashable left right = true

/-- §3, §7 head equivocation as a proposition. -/
def SGHeadEquivocation (left right : CombinedAttestation V) : Prop :=
  sgHeadEquivocation left right = true

instance (left right : CombinedAttestation V) : Decidable (Slashable left right) :=
  inferInstanceAs (Decidable (slashable left right = true))

instance (left right : CombinedAttestation V) :
    Decidable (E1Slashable left right) :=
  inferInstanceAs (Decidable (e1Slashable left right = true))

instance (left right : CombinedAttestation V) :
    Decidable (E2Slashable left right) :=
  inferInstanceAs (Decidable (e2Slashable left right = true))

instance (left right : CombinedAttestation V) :
    Decidable (SGHeadEquivocation left right) :=
  inferInstanceAs (Decidable (sgHeadEquivocation left right = true))

/-- At most one member of `xs` per key: the shape of all three clauses of the
honest emission budget (PROTOCOL.md `sec:state-machine`, "one proposal per
slot"). -/
def atMostOnePer {α β : Type} [DecidableEq β] (key : α → β) (xs : List α) : Prop :=
  ∀ k : β, (xs.filter (fun x => decide (key x = k))).length ≤ 1

/-- §4 the honest emission budget: "an honest validator emits at most one
proposal per slot, one Goldfish vote per slot, and one combined attestation per
round" (PROTOCOL.md `sec:state-machine`, "one proposal per slot").

The three lists are one honest validator's emissions over an execution. A
`Block` carries its proposer field, while the Goldfish vote and the attestation
carry their validator index; the caller supplies the objects for that
validator.

This constrains honest behaviour; no handler enforces it. -/
def HonestEmissionBudget (blocks : List (Block V))
    (gf_votes : List (GoldfishVote V))
    (attestations : List (CombinedAttestation V)) : Prop :=
  atMostOnePer Block.slot blocks ∧
    atMostOnePer GoldfishVote.slot gf_votes ∧
      atMostOnePer CombinedAttestation.round attestations

end Protocol

end DecoupledConsensusModel
end

-- ── from FinalityGadget/ChainState.lean ──
section
/-!
# §4 Chain state (PROTOCOL.md `sec:state-machine`)

`def:chain-state` as one flat twelve-field structure, in the document's order:
`σ = (L, s, h, T_h, nj, target_participation, progress, finalize, J, h_j, F,
h_F)` (PROTOCOL.md `def:chain-state`).

`T_h` is a `Block`, never `⊥`: `advance_height` sets `T_h ← L`, and the initial
state sets `T_h = B_gen`. The state is flat and has no post-state root field.

The three participation arrays are `Finset V`: the
document's `V → Bool` array and its derived quorum set carry the same
information, and every rule reads the set. `Repr` is therefore not derivable —
Mathlib's `Repr (Finset α)` is an `unsafe` instance — so this structure derives
`DecidableEq` only.
-/

namespace DecoupledConsensusModel

namespace Protocol

/-- §4 the fixed height parameters `K ≥ 4`, `D ≥ 2`, and the timeout delay
`δ_t ≥ 0` in slots (PROTOCOL.md `sec:state-machine`).
They are the §4
parameters that
are not already in `Env`: `w(·)` and `q = ⌈2W/3⌉` come from `Env.electorate`
(PROTOCOL.md `sec:sg-schedule`, `sec:state-machine`).

**The domain is `K ≥ 4`, `D ≥ 2`, and the two bounds are not symmetric in
intent**: "`K` is meant large and `D` minimal" (PROTOCOL.md
`sec:state-machine`, "$K$ is meant large, $D$ minimal").

* `D ≥ 2` is a **structural floor**: the steady pipeline enters heights at debt
  `h − h_F = 2`, so a smaller `D` would fire `nj` on the pipeline's own normal
  operation. `D = 2` is therefore the intended value, and it doubles as the
  banked-backlog cap.
* `K ≥ 3` **excludes a self-regenerating skip cadence at `K = 2`**: at that value
  the skipped heights land back on multiples of `K` and the pattern reproduces
  itself.

The weaker bounds `K ≥ 2` and `D ≥ 1` follow as `K_ge_two` and `D_ge_one`. -/
structure HeightConfig where
  /-- §4 `K`: the nonjustifiable period (PROTOCOL.md `sec:state-machine`,
  "Fix constants $K\geq4$, $D\geq2$"). -/
  K : Nat
  /-- §4 `D`: the finality-debt bound (PROTOCOL.md `sec:state-machine`,
  "Fix constants $K\geq4$, $D\geq2$"). -/
  D : Nat
  /-- §4 `δ_t`: the delay before a progress quorum that can contain timeout
  rows is consumed (PROTOCOL.md `sec:state-machine`, "consumed only by a
  block whose slot is at least"). -/
  timeoutDelay : Nat
  /-- §4 `K ≥ 4` (PROTOCOL.md `sec:state-machine`): `K = 2` regenerates its own
  skip cadence, and `K = 3` leaves no room for the opening-window gap
  (`gap ≥ 2` and `gap + 2 ≤ K`), so the finality contracts would be vacuous. -/
  K_ge_four : 4 ≤ K
  /-- §4 `D ≥ 2` (PROTOCOL.md `sec:state-machine`, "steady pipeline enters
  heights at debt"): the steady pipeline enters heights at
  debt `2`. -/
  D_ge_two : 2 ≤ D

namespace HeightConfig

end HeightConfig

/-- §4 a chain state `σ` (PROTOCOL.md `def:chain-state`, `def:chain-state`).
The fields are in the document's tuple order. -/
structure ChainState (V : Type) where
  /-- §4 `L`: the latest block (PROTOCOL.md `def:chain-state`). -/
  L : Block V
  /-- §4 `s = L.slot` (PROTOCOL.md `def:chain-state`). Held as a field
  because `state_transition` writes it before it writes `L` (PROTOCOL.md
  `alg:state-transition`). -/
  s : Slot
  /-- §4 `h`: the current height (PROTOCOL.md `def:chain-state`). -/
  h : Height
  /-- §4 `T_h`: the block that carried the transition into height `h`
  (PROTOCOL.md `def:chain-state`). -/
  T_h : Block V
  /-- §4 `nj`: computed when the chain enters `h`, fixed until the height
  changes (PROTOCOL.md `def:chain-state`). -/
  nj : Bool
  /-- §4 `target_participation` (PROTOCOL.md `def:chain-state`), as its
  quorum set. -/
  target_participation : Finset V
  /-- §4 `progress` (PROTOCOL.md `def:chain-state`), as its quorum set. -/
  progress : Finset V
  /-- §4 `finalize` (PROTOCOL.md `def:chain-state`), as its quorum set. -/
  finalize : Finset V
  /-- §4 `J`: the latest justification on the chain (PROTOCOL.md
  `def:chain-state`). -/
  J : Block V
  /-- §4 `h_j`: the height of that justification (PROTOCOL.md
  `def:chain-state`). -/
  h_j : Height
  /-- §4 `F`: the latest finalization on the chain (PROTOCOL.md
  `def:chain-state`). -/
  F : Block V
  /-- §4 `h_F`: the height of that finalization (PROTOCOL.md
  `def:chain-state`). -/
  h_F : Height
deriving DecidableEq

namespace ChainState

variable {V : Type}

/-- §4 the initial chain state: `L = T_h = J = F = B_gen`, `s = 0`, `h = 1`,
`h_j = h_F = 0`, `nj = false`, every array entry false
(PROTOCOL.md `def:chain-state`).

This is the default of the total map `Σ.σ[·]`, so
`σ[B_gen]` and `σ[B_gen.parent]` are both this state. `nj` is the document's
literal `false`, not the `nj` formula evaluated at `h = 1`; with `K ≥ 2`
the two agree. -/
def initial : ChainState V :=
  { L := .genesis
    s := 0
    h := 1
    T_h := .genesis
    nj := false
    target_participation := ∅
    progress := ∅
    finalize := ∅
    J := .genesis
    h_j := 0
    F := .genesis
    h_F := 0 }

/-- §4 `Q_target(σ) = {i: σ.target_participation[i]}` (PROTOCOL.md
`def:chain-state`).
Here the array *is* its quorum set, so the three derived
sets are identities; they exist so that every name the document uses is
spellable in Lean. -/
def Q_target (σ : ChainState V) : Finset V :=
  σ.target_participation

/-- §4 `Q_prog(σ) = {i: σ.progress[i]}` (PROTOCOL.md `def:chain-state`). -/
def Q_prog (σ : ChainState V) : Finset V :=
  σ.progress

/-- §4 `Q_finality(σ) = {i: σ.finalize[i]}` (PROTOCOL.md `def:chain-state`).
-/
def Q_finality (σ : ChainState V) : Finset V :=
  σ.finalize

variable [DecidableEq V] [Fintype V]

/-- §4 `w(Q_target(σ)) ≥ q` (PROTOCOL.md `alg:state-transition`). Weights
and `q` are the electorate's (PROTOCOL.md `sec:sg-schedule`,
`sec:state-machine`, "weighted quorum threshold"); Goldfish's unit counts
never reach this test. -/
def targetQuorum (E : Env V) (σ : ChainState V) : Bool :=
  E.electorate.quorumCheck σ.Q_target

/-- §4 `w(Q_prog(σ)) ≥ q` (PROTOCOL.md `alg:state-transition`, "timeouts
count only after the delay"). -/
def progQuorum (E : Env V) (σ : ChainState V) : Bool :=
  E.electorate.quorumCheck σ.Q_prog

/-- §4 `w(Q_finality(σ)) ≥ q` (PROTOCOL.md `alg:state-transition`). -/
def finalityQuorum (E : Env V) (σ : ChainState V) : Bool :=
  E.electorate.quorumCheck σ.Q_finality

end ChainState

end Protocol

end DecoupledConsensusModel
end

-- ── from FinalityGadget/Transition.lean ──
section
/-!
# §4 The deterministic state transition (PROTOCOL.md `alg:state-transition`)

`alg:state-transition`, line for line. The section is pure: there is no store
here. `σ[B] = state_transition(σ[B.parent], B)` is a deterministic function of
the chain ending at `B` (PROTOCOL.md `sec:state-machine`), so these
functions take a chain
state, a block, and the fixed parameters — nothing else. §5 owns the store map
`Σ.σ[·]` and calls `state_transition` from `on_block`.

The transition runs per block; an empty slot triggers no height event. `T_h`
is always a block set by `advance_height`. Progress requires the exact pair
`(h, T_h)` or `(h, ⊥)`. `process_height_events` updates `(J, h_j)` and clears
the finality set. The transition has no failure result.

The document gives `B.attestations` no validity conditions at all — no round
constraint, no duplicate rule, no length bound — and this fold applies
every element as written.
-/

namespace DecoupledConsensusModel

namespace Protocol

/-- §4 the nonjustifiability rule `nj ← (K | h) ∧ (h − h_F > D)`
(PROTOCOL.md `sec:state-machine`, `alg:state-transition`). Both the prose and
`advance_height` state it,
and both read the *already-updated* `h_F`, so a finalization applied by the same
transition is visible here.

`Height` is `Nat`, so `h − h_F` truncates at zero; with `D ≥ 1` a state with
`h < h_F` gives `false` either way. -/
def nonjustifiable (cfg : HeightConfig) (h h_F : Height) : Bool :=
  decide (cfg.K ∣ h) && decide (cfg.D < h - h_F)

section Attestations

variable {V : Type} [DecidableEq V]

/-- §4 `process_attestation(σ, a)` (PROTOCOL.md `alg:state-transition`).

The two tests are independent guarded `if`s: one call can set the finality bit
*and* a height bit. The height branch is an `if`/`elif`, so a target vote sets
both height bits and a timeout vote sets only `progress`; any other pair — a
different height, or the empty pair — sets neither.

Equality of pairs is equality of roots: a
carried `target` is a `BlockId`, and `σ.T_h`, `σ.J` are blocks, so the tests
compare `σ.T_h.root` and `σ.J.root`. Nothing here requires the target block
itself to be in the store; the document states a dependency only for the
attestation's head (PROTOCOL.md `sec:fg-fork-choice`, "the head's finality
fields").

The function reads `σ.h, σ.T_h, σ.h_j, σ.J, σ.h_F` and writes none of them, so
the fold in `state_transition` is order-independent and idempotent.

The finality guard omits `σ.F ⪯ σ.J`
(PROTOCOL.md `alg:state-transition`). It is redundant: in a chain state `J`
is only ever assigned `σ.T_h` and `F` only ever assigned `σ.J`, so the two are
ordered by ancestry at every reachable state and the guard's remaining
`h_F < h_j` carries the rest. The redundancy is **not** taken on trust — it is
`Protocol.ChainOrder.finalized_preceq_justified`, which
`chainOrder_derived_state` establishes for every derived state, and
`Protocol.process_attestation_eq_guarded` proves the prior guard and this one
agree there. Store-level thinking is what put it here; §5's own `Σ.F ⪯ σ.J`
guard in `update_finality` is a different claim about a different object and
stays. -/
def process_attestation (σ : ChainState V) (a : CombinedAttestation V) :
    ChainState V :=
  let i := a.val_index
  let afterFinality :=
    if decide (σ.h_F < σ.h_j) &&
        decide (a.finality_pair = some ⟨σ.h_j, σ.J.root⟩) then
      { σ with finalize := insert i σ.finalize }
    else σ
  if a.height_pair = .target σ.h σ.T_h.root then
    { afterFinality with
      target_participation := insert i afterFinality.target_participation
      progress := insert i afterFinality.progress }
  else if a.height_pair = .timeout σ.h then
    { afterFinality with progress := insert i afterFinality.progress }
  else afterFinality

end Attestations

section Transition

variable {V : Type} [DecidableEq V] [Fintype V]

/-- §4 the finality guard of `process_height_events`
(PROTOCOL.md `alg:state-transition`): `h_j > h_F`, and `Q_finality` is a
quorum. The first
clause is the guard of `process_attestation`'s finality branch as well
(PROTOCOL.md `alg:state-transition`); the document states it as a runtime
guard, not as an invariant of the chain state.

The guard omits `F ⪯ J` (PROTOCOL.md `alg:state-transition`) because `process_attestation` records: it is implied at every reachable chain
state by the ancestry the assignments already force, and the tripwire
`Protocol.finalityReady_eq_guarded` proves the prior guard and this one agree
under `ChainOrder`. §5's store-side `Σ.F ⪯ σ.J` in `update_finality` is
untouched and remains load-bearing — it compares a *store* field with an
incoming block's chain state, which is a genuinely different test. -/
def finalityReady (E : Env V) (σ : ChainState V) : Bool :=
  decide (σ.h_F < σ.h_j) && σ.finalityQuorum E

/-- §4 the justification guard (PROTOCOL.md `alg:state-transition`): `¬nj`,
and `Q_target` is a quorum. There is no "`T_h` is set" clause — `T_h` is
always a block. -/
def targetReady (E : Env V) (σ : ChainState V) : Bool :=
  !σ.nj && σ.targetQuorum E

/-- §4 the progress guard (PROTOCOL.md `sec:state-machine`, "an exact target
quorum is consumed immediately"). An exact target quorum is
consumed immediately. A progress quorum that can contain timeout rows is
consumed only at or after `T_h.slot + timeoutDelay`. Timeout rows remain in
`progress` while this gate is closed. -/
def progReady (E : Env V) (cfg : HeightConfig) (σ : ChainState V) : Bool :=
  σ.targetQuorum E ||
    (decide (σ.T_h.slot + cfg.timeoutDelay ≤ σ.s) && σ.progQuorum E)

/-- §4 `advance_height(σ)` (PROTOCOL.md `alg:state-transition`). It
increments the height,
carries the latest block into `T_h`, recomputes the `nj` flag from the new
height and the already-updated `h_F`, and clears the target and progress sets.

`σ.finalize` is deliberately **not** cleared here: only the justification branch
clears it (PROTOCOL.md `alg:state-transition`), so a finality bit set at
height `h` can still
trigger finalization several progress advances later, as long as `(J, h_j)` has
not moved.

The document's `advance_height` takes only `σ`; the justification write lives in
the caller, so there is no `justify` argument. -/
def advance_height (cfg : HeightConfig) (σ : ChainState V) : ChainState V :=
  let next := σ.h + 1
  { σ with
    h := next
    T_h := σ.L
    nj := nonjustifiable cfg next σ.h_F
    target_participation := ∅
    progress := ∅ }

/-- §4 `process_height_events(σ)` (PROTOCOL.md `alg:state-transition`).

Three branches in the document's order. The finality branch falls through — it
mutates `(F, h_F)` and the two height branches then read the mutated state, so a
finalization applied here is what `advance_height`'s `nj` latch sees. The
justification branch has priority over progress: whenever both height thresholds
hold, target wins.

The justification write `(J, h_j) ← (T_h, h)` uses the height being *left*, so
the new height is `h_j + 1`; §5's `get_fg_root` depends on it. -/
def process_height_events (E : Env V) (cfg : HeightConfig) (σ : ChainState V) :
    ChainState V :=
  let afterFinality :=
    if finalityReady E σ then { σ with F := σ.J, h_F := σ.h_j } else σ
  if targetReady E afterFinality then
    advance_height cfg
      { afterFinality with
        J := afterFinality.T_h
        h_j := afterFinality.h
        finalize := ∅ }
  else if progReady E cfg afterFinality then
    advance_height cfg afterFinality
  else afterFinality

end Transition

end Protocol

end DecoupledConsensusModel
end

-- ── from FinalityGadget/TimeoutBinding.lean ──
section
/-! Generic height-pair interpretation for the finality transition. -/
namespace DecoupledConsensusModel.Protocol

/-- A leaf interface over an arbitrary row representation. It does not assert
signed provenance; an actual runtime must supply that separately. -/
structure TimeoutBinding (V Row : Type) where
  base : Row → CombinedAttestation V
  heightPair : ChainState V → Row → HeightPair

namespace TimeoutBinding
variable {V Row : Type}

/-- Preserve the base row's signer, SG projection and finality pair. -/
def view (binding : TimeoutBinding V Row) (st : ChainState V) (row : Row) :
    CombinedAttestation V :=
  { binding.base row with height_pair := binding.heightPair st row }

end TimeoutBinding

/-- The leaf adapter calls the existing processor once, on the interpreted row.
No finality-processing or height-processing algorithm is copied. -/
def process_attestation_with {V Row : Type} [DecidableEq V]
    (binding : TimeoutBinding V Row) (st : ChainState V) (row : Row) : ChainState V :=
  process_attestation st (binding.view st row)

end DecoupledConsensusModel.Protocol
end

-- ── from FinalityGadget/TargetedTimeoutBinding.lean ──
section
/-! Concrete entry-bound row interpretation. No activity field is added. The
selected named transition passes this height view to the existing fold. -/
namespace DecoupledConsensusModel.Protocol

namespace TimeoutBinding

/-- One unified height/entry match. A mismatch erases only the height field;
the base row still supplies the original finality component. -/
def targetedHeightPair {V : Type} (st : ChainState V) (row : NamedAttestation V) : HeightPair :=
  if row.height_pair.matchesEntry st.h st.T_h.root then row.height_pair.erase else .empty

def targeted (V : Type) : TimeoutBinding V (NamedAttestation V) where
  base := NamedAttestation.erase
  heightPair := targetedHeightPair

end TimeoutBinding
end DecoupledConsensusModel.Protocol
end

-- ── from FinalityGadget/BoundTransition.lean ──
section
/-! Row-parametric block folding. The named specialization reads the full
row list of its actual NamedBlock. No free checkpoint/context lookup exists. -/
namespace DecoupledConsensusModel.Protocol
variable {V Row : Type} [DecidableEq V] [Fintype V]

def fold_rows (binding : TimeoutBinding V Row) (st : ChainState V)
    (geometry : Block V) (rows : List Row) : ChainState V :=
  { rows.foldl (process_attestation_with binding) { st with s := geometry.slot }
      with L := geometry }

def transition_rows (binding : TimeoutBinding V Row) (E : Env V) (cfg : HeightConfig)
    (st : ChainState V) (geometry : Block V) (rows : List Row) : ChainState V :=
  process_height_events E cfg (fold_rows binding st geometry rows)

/-- This binding uses exactly the named block's own signed rows. -/
def named_transition (E : Env V) (cfg : HeightConfig) (st : ChainState V)
    (B : NamedBlock V) : ChainState V :=
  transition_rows (TimeoutBinding.targeted V) E cfg st B.erase B.attestations

/-- Deterministic named derivation from recursively retained full metadata. -/
def derive_named (E : Env V) (cfg : HeightConfig) : NamedBlock V → ChainState V
  | .genesis => .initial
  | B@(.node p _ _ _ _ _ _) => named_transition E cfg (derive_named E cfg p) B

end DecoupledConsensusModel.Protocol
end

end
