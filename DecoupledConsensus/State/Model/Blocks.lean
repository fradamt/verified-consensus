import DecoupledConsensus.State.Model.Primitives

namespace DecoupledConsensus

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

/-- Parent of a non-genesis block. Genesis has no parent. -/
def parent? : Block n → Option (Block n)
  | genesis => none
  | mk _ parent _ _ => some parent

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

/-- Executable parent-pointer ancestry test, scanning from the candidate
    descendant toward genesis. -/
def isAncestorOf (B : Block n) : Block n → Bool
  | genesis => decide (B = genesis)
  | mk bid parent s vs =>
      decide (B = mk bid parent s vs) || isAncestorOf B parent

/-- Executable strict ancestry test. -/
def isStrictAncestorOf (B C : Block n) : Bool :=
  isAncestorOf B C && decide (B ≠ C)

/-- Find the nearest parent-pointer ancestor of `root` whose id is `bid`.

    No well-formedness or id-injectivity is required for lookup itself. If ids
    collide, this returns the closest match to `root`; safety theorems assume
    scoped id injectivity over the chains they compare when they need equal ids
    to imply equal blocks. -/
def findById : Block n → BlockId → Option (Block n)
  | genesis, bid => if bid = 0 then some genesis else none
  | mk selfId parent s vs, bid =>
      if bid = selfId then some (mk selfId parent s vs) else findById parent bid

/-- Collision-free ids scoped to the two block histories being compared.

    This is the hash idealization used by safety: malformed raw blocks may
    reuse ids, but every ancestor of either considered tip has a unique id
    within that comparison boundary. -/
def IdInjectiveOnAncestors (tip₁ tip₂ : Block n) : Prop :=
  ∀ {A B : Block n},
    (A ≼ tip₁ ∨ A ≼ tip₂) →
    (B ≼ tip₁ ∨ B ≼ tip₂) →
    A.id = B.id →
    A = B

/-- Two blocks are compatible if one is an ancestor of the other. -/
def Compatible (B C : Block n) : Prop := B ≼ C ∨ C ≼ B

scoped infix:50 " ~ " => Block.Compatible

end Block

end DecoupledConsensus
