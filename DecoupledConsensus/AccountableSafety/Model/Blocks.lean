import DecoupledConsensus.AccountableSafety.Model.Primitives

namespace AccountableSafety

/-! # Accountable Safety Model: blocks

Raw block trees, parent-pointer ancestry, id lookup, and compatibility
predicates. Geometric facts about these definitions live in `Proof.Facts`. -/

/-! ## Blocks and chain order -/

/-- A block carries an id, a parent, a slot, and the votes included in it. -/
inductive Block (n : ℕ) : Type
  | genesis : Block n
  | mk (id : BlockId) (parent : Block n) (slot : ℕ) (votes : List (Vote n)) : Block n
  deriving DecidableEq

namespace Block

variable {n : ℕ}

/-- Identifier of a block. Genesis uses reserved id 0. -/
def id : Block n → BlockId
  | genesis => 0
  | mk bid _ _ _ => bid

/-- Slot of a block. Genesis has slot 0. -/
def slot : Block n → ℕ
  | genesis => 0
  | mk _ _ s _ => s

/-- Votes embedded in a block. Genesis carries no votes. -/
def votes : Block n → List (Vote n)
  | genesis => []
  | mk _ _ _ vs => vs

/-- Well-formedness: slots strictly increase along parent links.

    `Block` itself is raw tree data and can describe malformed parent/slot
    pairs. Valid chains are represented by `Chain`, whose `extend`
    constructor enforces this predicate at chain tips. -/
def WellFormed : Block n → Prop
  | genesis => True
  | mk _ p s _  => p.slot < s ∧ WellFormed p

/-- Parent-pointer ancestry. `B ≼ C` means that `B` is obtained by following
    parent pointers from `C`, or `B = C`.

    This relation deliberately does not check slot monotonicity. Slot-order
    facts are recovered by combining `≼` with `Block.WellFormed`; see
    `Ancestor.slot_le` and `Ancestor.le_of_slot_le`. This keeps raw ancestry
    usable for id lookup on arbitrary block trees. -/
inductive Ancestor : Block n → Block n → Prop
  | refl (B : Block n) : Ancestor B B
  | step {B C : Block n} {bid s : ℕ} {vs : List (Vote n)}
      (h : Ancestor B C) : Ancestor B (mk bid C s vs)

scoped infix:50 " ≼ " => Block.Ancestor

/-- Strict ancestor relation. `B ≺ C` means `B` is a proper ancestor of `C`. -/
def StrictAncestor (B C : Block n) : Prop := B ≼ C ∧ B ≠ C

scoped infix:50 " ≺ " => Block.StrictAncestor

/-- Find the nearest parent-pointer ancestor of `root` whose id is `bid`.

    No well-formedness or id-injectivity is required for lookup itself. If ids
    collide, this returns the closest match to `root`; safety theorems assume
    `Block.IdInjective n` when they need equal ids to imply equal blocks. -/
def findById : Block n → BlockId → Option (Block n)
  | genesis, bid => if bid = 0 then some genesis else none
  | mk selfId parent s vs, bid =>
      if bid = selfId then some (mk selfId parent s vs) else findById parent bid

/-- Collision-free block ids. This models hashes identifying blocks and is used
    only where the safety proof must convert id equality into block equality. -/
def IdInjective (n : ℕ) : Prop :=
  ∀ {A B : Block n}, A.id = B.id → A = B

/-- Two blocks are compatible if one is an ancestor of the other. -/
def Compatible (B C : Block n) : Prop := B ≼ C ∨ C ≼ B

scoped infix:50 " ~ " => Block.Compatible

/-- Two blocks conflict if they are not compatible. -/
def Conflicts (B C : Block n) : Prop := ¬ Compatible B C

end Block

end AccountableSafety
