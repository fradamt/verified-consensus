import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

namespace DecoupledConsensus

/-! # Accountable Safety Model: primitives

Basic validator, quorum, block-id, and vote/slashing definitions. This module is
part of the executable/model layer and intentionally contains no proof lemmas. -/

variable {n : ℕ}

/-- A validator is an index in `Fin n`. -/
abbrev Validator (n : ℕ) := Fin n

/-- The **literal BFT quorum threshold**: `card ≥ 2 * f + 1`. This is the
    user-facing statement under the convention `n = 3 * f + 1`. -/
abbrev IsQuorum (f : ℕ) (Q : Finset (Validator n)) : Prop :=
  Q.card ≥ 2 * f + 1

/-- The **strict 2/3 quorum threshold**: `3 * card ≥ 2 * n + 1`. Used by
    the state machine (`Justified`, `TimeoutFires`, `applyFinality`) to
    avoid threading `f` through every transition. Equivalent to `IsQuorum`
    under `n = 3 * f + 1`. -/
abbrev IsQuorumStrict (n : ℕ) (Q : Finset (Validator n)) : Prop :=
  3 * Q.card ≥ 2 * n + 1

/-- Executable strict-quorum test used by the state transition. The Prop-level
    predicate above is kept for theorem statements and arithmetic proofs. -/
def isQuorumStrictBool (n : ℕ) (Q : Finset (Validator n)) : Bool :=
  Nat.ble (2 * n + 1) (3 * Q.card)

/-- Opaque block identifiers. In protocol terms these model block hashes. -/
abbrev BlockId := ℕ

/-! ## Votes and slashing -/

structure Vote (n : ℕ) where
  validator : Validator n
  height : ℕ
  target : Option BlockId -- `none` represents `⊥`, a timeout vote
  finalize : Option (ℕ × BlockId) -- optional `(height, target-id)` finalize commitment
  deriving DecidableEq

namespace Vote

/-- Slashing rule E1 (one-sided form): vote `b` commits a finalize at
    height `h_f` to block id `T_f ≠ ⊥`, and vote `a` is at the same
    height with a different (or `⊥`) target id. -/
def slashConflict (a b : Vote n) : Prop :=
  ∃ hf Tf, b.finalize = some (hf, Tf) ∧
        a.height = hf ∧
        a.target ≠ some Tf

/-- A pair of votes is slashable iff they have the same validator field and are
    in finalize-conflict (in either direction). -/
def Slashable (a b : Vote n) : Prop :=
  a.validator = b.validator ∧ (slashConflict a b ∨ slashConflict b a)

end Vote

end DecoupledConsensus
