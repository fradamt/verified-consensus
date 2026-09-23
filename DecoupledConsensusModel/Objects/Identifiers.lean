module
public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Basic

@[expose] public section

/-!
# `DecoupledConsensusModel/Objects/Identifiers.lean`

Purpose: §1 identifiers — slots, heights, rounds, block ids.
Paper: `docs/PROTOCOL.md` `sec:complete-store`; algorithm block: the Section 7 wire objects and parameters.

Defines: Slot, Height, Round, BlockId, and genesisRoot.

Read after: the preceding Model subjects.
Read next: `DecoupledConsensusModel.Objects.Time`.

State read: the identifier, time, weight, parameter, and wire types imported by this subject.
State written: typed wire values, parameters, and pure projections; no mutable state is written.

Representation notes: The paper objects use typed Lean inductives/structures and finite collections. Named payloads retain their erased twin where both are active.
-/

-- ── from Substrate/Identifiers.lean ──
/-!
# §1 Identifiers

The arithmetic protocol coordinates and the nominal block root, with the fixed
total order that every root tie-break in the document uses.

`BlockId` supplies the ordered root. The model has no state-root, signature,
or object-identity identifier at this layer.
-/

namespace DecoupledConsensusModel

/-- §1 slot number (PROTOCOL.md `sec:substrate`). -/
abbrev Slot := Nat

/-- §4 height: the finality counter, separate from slot
(PROTOCOL.md `sec:state-machine`, "Height is a finality counter"). -/
abbrev Height := Nat

/-- §3 round index; round `r` is slots `rR … rR+R−1` (PROTOCOL.md `sec:sg-schedule`). -/
abbrev Round := Nat

/-- §1 `B.root`: the nominal block identity (PROTOCOL.md `sec:substrate`). -/
@[ext]
structure BlockId where
  /-- The underlying nominal value. Roots are opaque; only equality and the
  fixed order below are used. -/
  value : Nat
deriving DecidableEq, Repr

private theorem BlockId.value_injective : Function.Injective BlockId.value := by
  intro left right equal
  exact BlockId.ext equal

/-- §1 the fixed root order: the tie-break for "deepest" (PROTOCOL.md `sec:substrate`)
and for `ghost`'s argmax (PROTOCOL.md `alg:goldfish`, "ties by root order"). The
document asserts the order but never constructs it. -/
instance : LinearOrder BlockId :=
  LinearOrder.lift' BlockId.value (by exact BlockId.value_injective)

/-- §1 the root of `B_gen`. The document never gives genesis its own fields; the model fixes the least root, so genesis loses every root tie-break. -/
def genesisRoot : BlockId := ⟨0⟩

end DecoupledConsensusModel

end
