import DecoupledConsensus.AccountableSafety.State.Model.StateMachine

namespace AccountableSafety

/-! # Accountable Safety Store Model

Executable section-3 store definitions: accepted block tree, store-level
justification/finality updates, viable tree, and confirmed candidates.

The TeX store carries a partial map `σ` from accepted blocks to post-states.
Here the accepted tree stores a `Chain` witness for each accepted block and
derives `σ[B]` as `stateOf chain`. This keeps the executable model from
admitting inconsistent block-state maps. -/

variable {n : ℕ}

open scoped Block

/-! ## Accepted entries and lookup -/

/-- An accepted store block together with the valid chain producing its state. -/
structure StoreEntry (n : ℕ) where
  block : Block n
  chain : Chain n block

namespace StoreEntry

/-- The post-state `σ[B]` of an accepted entry. -/
def state (e : StoreEntry n) : State n :=
  stateOf e.chain

/-- Cached height of the post-state of an accepted entry. -/
def height (e : StoreEntry n) : ℕ :=
  e.state.h

/-- Genesis as an accepted store entry. -/
def genesis (n : ℕ) : StoreEntry n where
  block := Block.genesis
  chain := Chain.genesis

/-- View an entry's chain as a chain for a specified block, when the block
    fields agree. -/
def chainAs? (e : StoreEntry n) (B : Block n) : Option (Chain n B) :=
  if h : e.block = B then
    some (h ▸ e.chain)
  else
    none

end StoreEntry

/-- Section-3 store tuple `(σ, T, F, J, h_j, hmax)`.

`entries` is the finite accepted tree `T` plus enough chain data to compute
the derived state map `σ`. Under reachable execution it is duplicate-free; the
raw executable structure does not bake that proof into the data. -/
structure Store (n : ℕ) where
  entries : List (StoreEntry n)
  F : Block n
  J : Block n
  hj : ℕ
  hmax : ℕ

namespace Store

/-- The genesis store. Genesis starts finalized and justified at height 0, and
    the genesis state has state height 1. -/
def genesis (n : ℕ) : Store n where
  entries := [StoreEntry.genesis n]
  F := Block.genesis
  J := Block.genesis
  hj := 0
  hmax := 1

/-- Prop-level membership in the accepted tree. -/
def Contains (S : Store n) (B : Block n) : Prop :=
  ∃ e ∈ S.entries, e.block = B

/-- Find an accepted chain for `B`, if `B` is in the store. -/
def findChain? (S : Store n) (B : Block n) : Option (Chain n B) :=
  S.entries.findSome? fun e => e.chainAs? B

/-- Executable accepted-block membership. -/
def containsBlockBool (S : Store n) (B : Block n) : Bool :=
  (S.findChain? B).isSome

/-- Derived partial state map `σ[B]`. -/
def stateOf? (S : Store n) (B : Block n) : Option (State n) :=
  (S.findChain? B).map stateOf

/-- Derived partial height map `σ[B].h`. -/
def heightOf? (S : Store n) (B : Block n) : Option ℕ :=
  (S.stateOf? B).map State.h

/-! ## Justification key and store updates -/

/-- Lexicographic key comparison on `(height, block-id)`. -/
def keyGreater (h' : ℕ) (J' : Block n) (h : ℕ) (J : Block n) : Bool :=
  h < h' || (h = h' && J.id < J'.id)

/-- Guard for `updateJustified`: only descendants of finalized root can
    replace `J`, and only when their key is strictly larger. -/
def shouldUpdateJustified (S : Store n) (J' : Block n) (h' : ℕ) : Bool :=
  Block.isAncestorOf S.F J' && keyGreater h' J' S.hj S.J

/-! ## Viable tree -/

/-- Height-filter threshold `hmax - 1`. -/
def heightThreshold (S : Store n) : ℕ :=
  S.hmax - 1

/-- A store block has a strict accepted descendant. -/
def hasStrictDescendantBool (S : Store n) (B : Block n) : Bool :=
  S.entries.any fun e =>
    Block.isAncestorOf B e.block && decide (B ≠ e.block)

/-- Executable leaf test for accepted blocks. -/
def isLeafBool (S : Store n) (B : Block n) : Bool :=
  S.containsBlockBool B && !S.hasStrictDescendantBool B

/-- Prop-level leaf predicate: accepted and with no proper accepted descendant. -/
def IsLeaf (S : Store n) (B : Block n) : Prop :=
  Contains S B ∧ ∀ {C : Block n}, Contains S C → B ≼ C → C = B

/-- Prop-level state-height lower bound for an accepted block. -/
def HasHeightAtLeast (S : Store n) (B : Block n) (k : ℕ) : Prop :=
  ∃ e ∈ S.entries, e.block = B ∧ k ≤ e.height

/-- Executable viable leaf test. -/
def isViableLeafEntryBool (S : Store n) (e : StoreEntry n) : Bool :=
  S.isLeafBool e.block && decide (S.heightThreshold ≤ e.height)

/-- Executable viable-tree membership.

For valid stores this is equivalent to the leaf-witness characterization in
the TeX: any high accepted descendant can be extended to a leaf whose
state-height is at least as large by state-height monotonicity. Using the
high-descendant form keeps the executable filter simple and avoids making
`getConfirmed` depend on a maximal-leaf search. -/
def isViableBool (S : Store n) (B : Block n) : Bool :=
  S.containsBlockBool B &&
    S.entries.any (fun e =>
      decide (S.heightThreshold ≤ e.height) && Block.isAncestorOf B e.block)

/-- Prop-level viable-tree membership.

This uses the high-descendant form equivalent to the section-3 leaf definition
on valid stores: `B` is viable iff an accepted descendant of `B` meets the
height filter. -/
def Viable (S : Store n) (B : Block n) : Prop :=
  Contains S B ∧
    ∃ D : Block n,
      Contains S D ∧ B ≼ D ∧ HasHeightAtLeast S D S.heightThreshold

/-- Executable finite representation of the viable tree. Reachable stores have
    no duplicate blocks, so this list acts as the finite set of viable blocks. -/
def viableTree (S : Store n) : List (Block n) :=
  S.entries.filterMap fun e =>
    if S.isViableBool e.block then some e.block else none

/-! ## Store-level finality and confirmation -/

/-- Guard for `updateFinalized`: move `F` only to a strict descendant that is
    below the current store justification and is still in the viable tree. -/
def shouldUpdateFinalized (S : Store n) (F' : Block n) : Bool :=
  Block.isStrictAncestorOf S.F F' &&
    Block.isAncestorOf F' S.J &&
    S.isViableBool F'

/-- Store-level justified-root update. -/
def updateJustified (S : Store n) (J' : Block n) (h' : ℕ) : Store n :=
  if S.shouldUpdateJustified J' h' then
    { S with J := J', hj := h' }
  else
    S

/-- Store-level finalized-root update. -/
def updateFinalized (S : Store n) (F' : Block n) : Store n :=
  if S.shouldUpdateFinalized F' then
    { S with F := F' }
  else
    S

/-- Root used for confirmed outputs. At the height boundary, confirmations are
    rooted at `J`; otherwise they are rooted at `F`. -/
def confirmationRoot (S : Store n) : Block n :=
  if S.hmax = S.hj + 1 then S.J else S.F

/-- Prop-level set of possible `getConfirmed` outputs. -/
def ConfirmedCandidate (S : Store n) (B : Block n) : Prop :=
  Viable S B ∧
    S.confirmationRoot ≼ B ∧
    HasHeightAtLeast S B S.heightThreshold

/-- Executable candidate test for one accepted entry. -/
def isConfirmedCandidateEntryBool (S : Store n) (e : StoreEntry n) : Bool :=
  S.isViableBool e.block &&
    Block.isAncestorOf S.confirmationRoot e.block &&
    decide (S.heightThreshold ≤ e.height)

/-- All possible `getConfirmed` outputs, represented as an executable finite
    list rather than selecting one output with an oracle `Ω`. -/
def getConfirmed (S : Store n) : List (Block n) :=
  S.entries.filterMap fun e =>
    if S.isConfirmedCandidateEntryBool e then some e.block else none

/-! ## Block acceptance -/

/-- Add a fresh accepted entry and bump `hmax` using the entry state. -/
def addEntry (S : Store n) (e : StoreEntry n) : Store n :=
  { S with entries := S.entries ++ [e], hmax := max S.hmax e.height }

/-- Section-3 `onBlock`. Returns `none` when a TeX assertion fails.

Duplicate accepted blocks are treated as idempotent replays. For a fresh block,
the parent must already be accepted, the slot must strictly extend the parent
chain, and the current finalized root must be an ancestor of the block. -/
def onBlock (S : Store n) (B : Block n) : Option (Store n) :=
  if S.containsBlockBool B then
    some S
  else
    match B with
    | Block.genesis => none
    | Block.mk bid parent newSlot votes =>
        match S.findChain? parent with
        | none => none
        | some parentChain =>
            if hSlot : newSlot > parent.slot then
              let child := Block.mk bid parent newSlot votes
              if Block.isAncestorOf S.F child then
                let entry : StoreEntry n :=
                  { block := child
                    chain := Chain.extend parentChain bid newSlot votes hSlot }
                let σ' := entry.state
                let S1 := S.addEntry entry
                let S2 := S1.updateJustified σ'.J σ'.hj
                some (S2.updateFinalized σ'.F)
              else
                none
            else
              none

end Store

end AccountableSafety
