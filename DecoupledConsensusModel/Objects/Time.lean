module
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Data.Finset.Basic
public import Mathlib.Order.WithBot
public import DecoupledConsensusModel.Objects.Identifiers

@[expose] public section

/-!
# `DecoupledConsensusModel/Objects/Time.lean`

Purpose: §1 time — stamps, timestamp maps, cutoff views, slot arithmetic.
Paper: `docs/PROTOCOL.md` `sec:complete-store`; algorithm block: the Section 7 wire objects and parameters.

Defines: Time, Stamp, TimestampMap, and stampedBefore.

Read after: `DecoupledConsensusModel.Objects.Identifiers`
Read next: `DecoupledConsensusModel.Objects.Blocks`.

State read: the identifier, time, weight, parameter, and wire types imported by this subject.
State written: typed wire values, parameters, and pure projections; no mutable state is written.

Representation notes: The paper objects use typed Lean inductives/structures and finite collections. Named payloads retain their erased twin where both are active.
-/

-- ── from Substrate/Time.lean ──
/-!
# §1 Time, timestamps and strict cutoff views

The time domain is `Int`: the document needs only
`4Δs` arithmetic and strict comparisons, and `Γ_r^{−1} = t_0 − Δ` is negative at
round 0.

Two infinities appear. `Σ.timestamp(B_gen) = −∞` (PROTOCOL.md `def:store`,
`sec:complete-store`), so a
stamp is a `WithBot Time`; the §6 batch summary uses `t_v = e_v = +∞` for "never
occurred", so an occurrence is a `WithTop Time`.

`Σ.timestamp[·]` is written exactly once, when the object first enters its pool,
and never changes (PROTOCOL.md `sec:substrate`, `sec:goldfish-store`). A
rejected object is never
stamped at all, so the map is partial. Every
phase cutoff is then a **strict** inequality over frozen stamps, which is what
makes `beforeCutoff` immutable.

A cutoff reads one of **two** clocks, and the τ fold is what split them
(PROTOCOL.md `sec:goldfish-store`, "resolution time"). The receipt clock is
`Σ.timestamp[·]` itself, read
through `stampedBefore` / `beforeCutoff`. The resolution clock is
`τ(x) = max{Σ.timestamp(x), Σ.timestamp(H)}` for an object naming a block `H`,
infinite while `H` is missing; it is read through `resolvedBefore` /
`beforeResolution`. Neither clock mutates: `τ` is a maximum of two frozen
stamps, not a re-stamping.
-/

namespace DecoupledConsensusModel

/-- §1 the time domain. -/
abbrev Time := Int

/-- §1 a processing instant: a time, or `⊥ = −∞` for genesis
(PROTOCOL.md `sec:substrate`, `def:store`). -/
abbrev Stamp := WithBot Time

/-- §2, §6 an *event instant*: a stamp, or `+∞` when the event never occurs.

`+∞` is the `none`, and `−∞` is `some ⊥`, so this one type carries both
infinities the document uses: the `t_v`/`e_v` defaults of the round batch summary
(PROTOCOL.md `def:grades`), the `τ = ∞` of an unresolved vote
(PROTOCOL.md `sec:goldfish-store`, "resolution time"), and genesis's own
`−∞` (PROTOCOL.md `def:store`).

It is **the same type as a `TimestampMap`'s codomain**, deliberately. A
resolution time is a timestamp map like any other — `Σ.timestamp[·]` is one, `τ`
is another — so every cutoff test in the model is `stampedBefore` against one of
them, and no second order instance and no second cutoff view exist. -/
abbrev Occurrence := Option Stamp

/-- §1 `Σ.timestamp(B_gen) = −∞` (PROTOCOL.md `def:store`, `sec:complete-store`). -/
def genesisStamp : Stamp := ⊥

/-- §1 `Σ.timestamp[·]`: the insertion time of a processed object
(PROTOCOL.md `sec:substrate`). `none` means the object was never processed into the pool —
a duplicate or rejected object returns before the stamp is written and so has no
timestamp at all. -/
abbrev TimestampMap (α : Type) := α → Option Stamp

variable {α : Type}

/-- §1 the strict-cutoff test `timestamp(x) < Γ` (PROTOCOL.md `sec:view-merge`,
`sec:available-confirmation`, `alg:grades`). An unstamped object fails it. -/
def stampedBefore (ts : TimestampMap α) (Γ : Time) (x : α) : Bool :=
  match ts x with
  | none => false
  | some u => decide (u < (Γ : Stamp))

/-- §1 the strict cutoff view `{x: timestamp(x) < Γ}` of a processed set: what
an action scheduled at `Γ` sees (PROTOCOL.md `sec:substrate`). -/
def beforeCutoff [DecidableEq α] (ts : TimestampMap α) (Γ : Time)
    (S : Finset α) : Finset α :=
  S.filter (fun x => stampedBefore ts Γ x = true)

/-- §1 the strict cutoff test on a bare occurrence, `x < Γ`
(PROTOCOL.md `sec:goldfish-store`, `alg:grades`). `+∞` fails it; `−∞` passes it.

`stampedBefore ts Γ x` is this test applied to `ts x`, and `occurrence_before_eq`
below records that. -/
def occurrenceBefore (x : Occurrence) (Γ : Time) : Bool :=
  match x with
  | none => false
  | some u => decide (u < (Γ : Stamp))

/-- §2 `τ` as a maximum of two occurrences, `+∞` absorbing
(PROTOCOL.md `sec:goldfish-store`, "resolution time").

`max` on `Stamp` already puts `−∞` below everything, so genesis's stamp drops out
of the maximum with no special case; `+∞` on either side is `+∞`, which is the
"infinite while the block is missing" of the document. -/
def occurrenceMax (x y : Occurrence) : Occurrence :=
  match x, y with
  | some a, some b => some (max a b)
  | _, _ => none

/-- §1 `t_s = 4Δs`: the start of slot `s` (PROTOCOL.md `sec:substrate`). -/
def slotStart (Δ : Time) (s : Slot) : Time :=
  4 * Δ * (s : Time)

/-- §1 `s = ⌊t / 4Δ⌋`: the slot containing `t`
(PROTOCOL.md `alg:goldfish-store`, `alg:pair-rules`, `alg:store`).
Floor division, so the identity `slotOfTime Δ (slotStart Δ s) = s` holds; times
before `t_0` clamp to slot 0, which the document never reads. -/
def slotOfTime (Δ : Time) (t : Time) : Slot :=
  (Int.fdiv t (4 * Δ)).toNat

end DecoupledConsensusModel

end
