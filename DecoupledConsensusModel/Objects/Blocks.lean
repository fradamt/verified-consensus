module
public import Mathlib.Data.Finset.Basic
public import DecoupledConsensusModel.Objects.Identifiers

@[expose] public section

/-!
# `DecoupledConsensusModel/Objects/Blocks.lean`

Purpose: §1 wire objects — height and finality pairs, Goldfish votes, combined attestations, blocks and ancestry.
Paper: `docs/PROTOCOL.md` `sec:complete-store`; algorithm block: the Section 7 wire objects and parameters.

Defines: HeightPair, FinalityPair, GoldfishVote, CombinedAttestation, Block, slot, root, parent?, parent, gf_votes, gf_support_votes, attestations, proposer?, depth, preceq, prec, Preceq, Prec, compatible, Compatible, deeper, decidableExistsUniqueMem, pickUnique?, find?, isDeepestIn, deepest?.

Read after: `DecoupledConsensusModel.Objects.Identifiers`
Read next: `DecoupledConsensusModel.Objects.NamedBlocks`.

State read: the identifier, time, weight, parameter, and wire types imported by this subject.
State written: typed wire values, parameters, and pure projections; no mutable state is written.

Representation notes: The paper objects use typed Lean inductives/structures and finite collections. Named payloads retain their erased twin where both are active.
MODEL_MAP rows: HeightPair, FinalityPair, GoldfishVote, CombinedAttestation, Block, slot, root, parent?, parent, gf_votes, gf_support_votes, attestations, proposer?, depth, preceq, prec, Preceq, Prec, compatible, Compatible, deeper, decidableExistsUniqueMem, pickUnique?, find?, isDeepestIn, deepest?.
-/

-- ── from Substrate/Pairs.lean ──
section
/-!
# §4 Height and finality pairs

The two derived pairs of a combined attestation (PROTOCOL.md `sec:state-machine`). They
live in the substrate because `Block` carries attestations and must be defined
once, with all of its fields.

The height pair has three wire cases, so an empty pair cannot be confused with a
timeout at height zero. Targets are `BlockId`, with no signature wrapper. E1,
E2, and the equivocation predicates are defined in the §4 module.
-/

namespace DecoupledConsensusModel

/-- §4 the height pair: a target vote `(h,T)` with `T ≠ ⊥`, an empty-target
vote `(h,⊥)`, or the empty pair `(⊥,⊥)` (PROTOCOL.md `sec:state-machine`). -/
inductive HeightPair where
  /-- The empty pair `(⊥,⊥)`. Its height is `⊥`, so it triggers neither E1 nor
  E2 (PROTOCOL.md `sec:state-machine`, "triggers neither condition"). -/
  | empty
  /-- An empty-target vote `(h,⊥)`. -/
  | timeout (height : Height)
  /-- A target vote `(h,T)` with `T ≠ ⊥`. -/
  | target (height : Height) (target : BlockId)
deriving DecidableEq, Repr

namespace HeightPair

end HeightPair

/-- §4 the finality pair `(h_f, T_f)` with `T_f ≠ ⊥` (PROTOCOL.md `sec:state-machine`).
The empty finality pair is the `none` of an `Option FinalityPair` at the use
site, so an empty pair carries no height. -/
structure FinalityPair where
  /-- §4 `a.finalize_height` (PROTOCOL.md `sec:state-machine`). -/
  height : Height
  /-- §4 `a.finalize_target` (PROTOCOL.md `sec:state-machine`). -/
  target : BlockId
deriving DecidableEq, Repr

end DecoupledConsensusModel
end

-- ── from Substrate/Blocks.lean ──
section
/-!
# §1 Wire objects, ancestry and tree resolution

Lean cannot add fields to a structure after the fact, so the three wire objects
that later sections extend are defined **once**, here, carrying every field from
every section. Each field's doc comment cites the section that introduces it.

`Block` is a structural inductive: `genesis`, or a node holding its `parent`
directly. Ancestry, depth and the chain are then structural, and no store is
needed to walk upwards.

Both vote objects reference blocks **by root**, never by block. This is what
keeps `Block` a plain recursive inductive instead of a mutual one.

Resolution is a **read-side** notion, not a processing contract. A vote is
processed on receipt whether or not the store holds the block it names, and is
*resolved* when the store holds a unique head whose slot is no later than the
vote's slot (PROTOCOL.md `sec:goldfish-store`, `sec:sg-store`,
`sec:complete-store`). A consumer therefore turns a root into a block with
`Block.find?` and gets `none` for an unresolved name — a pooled vote whose block
has not arrived, or a carried vote naming a block the receiver never held, are
the same unresolved case.
-/

namespace DecoupledConsensusModel

/-- §2 a Goldfish vote, written `(v, s, B)` in the document
(PROTOCOL.md `sec:goldfish-schedule`). The named block has no field name in the
text; it is matched positionally, and is carried here by root. -/
structure GoldfishVote (V : Type) where
  /-- §2 `vote.val_index`; the honest constraint is `v ∈ K_s`
  (PROTOCOL.md `sec:goldfish-schedule`, `alg:goldfish-store`). -/
  val_index : V
  /-- §2 `vote.slot` (PROTOCOL.md `sec:goldfish-schedule`, `alg:goldfish-store`). -/
  slot : Slot
  /-- §2 the block the vote names, by root; the honest constraint is
  `B.slot ≤ s` (PROTOCOL.md `sec:goldfish-schedule`).

  The `head` field names a block by root. `Protocol.targets_under` resolves
  that root against the supplied tree. -/
  head : BlockId
deriving DecidableEq, Repr

/-- §4 the combined attestation
`(validator, round, confirmed, height, target, finalize_height, finalize_target)`
(PROTOCOL.md `sec:state-machine`). The four finality fields are carried as the
two derived pairs, which is the same information with the wire cases made
explicit; the seven document field names are recovered by the accessors below. -/
structure CombinedAttestation (V : Type) where
  /-- §4 `a.val_index` (PROTOCOL.md `sec:state-machine`). -/
  val_index : V
  /-- §4 `a.round` (PROTOCOL.md `sec:state-machine`). -/
  round : Round
  /-- §3, §6 `a.confirmed`: the SG-vote projection, `⊥` in a timeout vote
  (PROTOCOL.md `sec:sg-schedule`, `sec:complete-store`, `alg:grades`). Carried
  by root. -/
  confirmed : Option BlockId
  /-- §4 the height pair `(a.height, a.target)` (PROTOCOL.md `sec:state-machine`). -/
  height_pair : HeightPair
  /-- §4 the finality pair `(a.finalize_height, a.finalize_target)`; `none` is
  the empty pair (PROTOCOL.md `sec:state-machine`). -/
  finality_pair : Option FinalityPair
deriving DecidableEq, Repr

namespace CombinedAttestation

variable {V : Type}

end CombinedAttestation

/-- §1 a block (PROTOCOL.md `sec:substrate`), carrying every field every section adds.

The final document has no post-state-root field. `σ[B]` is derived from the
chain ending at `B`. -/
inductive Block (V : Type) where
  /-- §1 `B_gen`. Its own fields are never given by the document; the
  accessors below fix slot `0`, root `genesisRoot`, and no parent. -/
  | genesis
  /-- §1 a non-genesis block, with every field every section adds:

  * `parent: Block V` — §1 `B.parent` (PROTOCOL.md `sec:substrate`);
  * `slot: Slot` — §1 `B.slot` (PROTOCOL.md `sec:substrate`);
  * `root: BlockId` — §1 `B.root` (PROTOCOL.md `sec:substrate`);
  * `gf_votes: List (GoldfishVote V)` — §2 `B.votes`, every carried
    slot-`(B.slot − 1)` vote and the protocol's only vote relay channel
    (PROTOCOL.md `sec:goldfish-schedule`);
  * `gf_support_votes: List (GoldfishVote V)` — §2 `B.support_votes`, the
    subset of `gf_votes` that was resolved in the proposer's proposal-time
    view. It records that fixed view and is not processed as a second vote set
    (PROTOCOL.md `sec:goldfish-schedule`);
  * `attestations: List (CombinedAttestation V)` — §4 `B.attestations`, folded
    by `state_transition` (PROTOCOL.md `sec:state-machine`, `alg:state-transition`);
  * `proposer: V` — §1 `B.proposer`, the proposer index:
    "a slot-`s` block is valid only when `B.proposer = proposer(s)`", asserted
    by `state_transition` and read by `Object.author` — the F-c oracle
    idealization retires with it.

  There is **no** `proposal_root`. §6 carried one while an opening proposer
  could propose a graded root and a receiver could adopt it; the 
  replacement of §6 deleted the proposal mechanism outright — "there is no
  proposal mechanism at this layer" (PROTOCOL.md `sec:healing`,
  "no proposal mechanism at this layer").

  Both vote lists name blocks by root. -/
  | node (parent : Block V) (slot : Slot) (root : BlockId)
      (gf_votes : List (GoldfishVote V))
      (gf_support_votes : List (GoldfishVote V))
      (attestations : List (CombinedAttestation V))
      (proposer : V)
deriving DecidableEq, Repr

namespace Block

variable {V : Type}

/-- §1 `B.slot` (PROTOCOL.md `sec:substrate`); genesis is slot `0`. -/
def slot : Block V → Slot
  | .genesis => 0
  | .node _ s _ _ _ _ _ => s

/-- §1 `B.root` (PROTOCOL.md `sec:substrate`). -/
def root : Block V → BlockId
  | .genesis => genesisRoot
  | .node _ _ r _ _ _ _ => r

/-- §1 `B.parent`, absent at genesis. -/
def parent? : Block V → Option (Block V)
  | .genesis => none
  | .node p _ _ _ _ _ _ => some p

/-- §1 `B.parent` as a total function, genesis being its own parent. This is
what makes `σ[B.parent]` at genesis the initial chain state. -/
def parent : Block V → Block V
  | .genesis => .genesis
  | .node p _ _ _ _ _ _ => p

/-- §2 `B.votes` (PROTOCOL.md `sec:goldfish-schedule`). -/
def gf_votes : Block V → List (GoldfishVote V)
  | .genesis => []
  | .node _ _ _ votes _ _ _ => votes

/-- §2 `B.support_votes`, the fixed proposal-time support subset
(PROTOCOL.md `sec:goldfish-schedule`). -/
def gf_support_votes : Block V → List (GoldfishVote V)
  | .genesis => []
  | .node _ _ _ _ support _ _ => support

/-- §4 `B.attestations` (PROTOCOL.md `sec:state-machine`). -/
def attestations : Block V → List (CombinedAttestation V)
  | .genesis => []
  | .node _ _ _ _ _ ats _ => ats

/-- §1 `B.proposer`, absent at genesis. -/
def proposer? : Block V → Option V
  | .genesis => none
  | .node _ _ _ _ _ _ i => some i

/-- §1 depth: the number of parent edges from genesis (PROTOCOL.md `sec:substrate`). -/
def depth : Block V → Nat
  | .genesis => 0
  | .node p _ _ _ _ _ _ => p.depth + 1

section Ancestry

variable [DecidableEq V]

/-- §1 `B ⪯ C`: `B = C`, or `B` is an ancestor of `C` (PROTOCOL.md `sec:substrate`).
Executable, by walking `C` upwards. -/
def preceq (B : Block V) : Block V → Bool
  | .genesis => decide (B = Block.genesis)
  | C@(.node p _ _ _ _ _ _) => decide (B = C) || preceq B p

/-- §1 `B ≺ C`: strict ancestry (PROTOCOL.md `sec:substrate`). -/
def prec (B C : Block V) : Bool :=
  !decide (B = C) && preceq B C

/-- §1 `B ⪯ C` as a proposition (PROTOCOL.md `sec:substrate`). -/
def Preceq (B C : Block V) : Prop :=
  preceq B C = true

/-- §1 `B ≺ C` as a proposition (PROTOCOL.md `sec:substrate`). -/
def Prec (B C : Block V) : Prop :=
  prec B C = true

instance (B C : Block V) : Decidable (Preceq B C) :=
  inferInstanceAs (Decidable (preceq B C = true))

instance (B C : Block V) : Decidable (Prec B C) :=
  inferInstanceAs (Decidable (prec B C = true))

/-- §1 two blocks are compatible when one is an ancestor of the other
(PROTOCOL.md `sec:substrate`). -/
def compatible (B C : Block V) : Bool :=
  preceq B C || preceq C B

/-- One block is an ancestor of the other, or they are equal. -/
def Compatible (B C : Block V) : Prop :=
  Block.compatible B C = true

/-- §1 the "deepest" order: greater depth wins, ties by the fixed root order
(PROTOCOL.md `sec:substrate`). `deeper B C` says `B` beats `C`; the greatest root wins a
tie. -/
def deeper (B C : Block V) : Bool :=
  decide (C.depth < B.depth) ||
    (decide (C.depth = B.depth) && decide (C.root < B.root))

end Ancestry

end Block

section Pick

variable {α : Type} [DecidableEq α]

instance decidableExistsUniqueMem (T : Finset α) (p : α → Prop)
    [DecidablePred p] : Decidable (∃! a, a ∈ T ∧ p a) :=
  decidable_of_iff (∃ a ∈ T, p a ∧ ∀ b ∈ T, p b → b = a) <| by
    constructor
    · rintro ⟨a, haT, hpa, huniq⟩
      exact ⟨a, ⟨haT, hpa⟩, fun b hb => huniq b hb.1 hb.2⟩
    · rintro ⟨a, ⟨haT, hpa⟩, huniq⟩
      exact ⟨a, haT, hpa, fun b hbT hpb => huniq b ⟨hbT, hpb⟩⟩

/-- The unique member of `T` satisfying `p`, or `none` when there is no such
member or more than one. Computable, and total without a choice principle. -/
def pickUnique? (T : Finset α) (p : α → Bool) : Option α :=
  if h : ∃! a, a ∈ T ∧ p a = true then
    some (T.choose (fun a => p a = true) h)
  else
    none

end Pick

namespace Block

variable {V : Type} [DecidableEq V]

/-- §1 root → block resolution in a processed tree (PROTOCOL.md `sec:substrate`). A root
is a block's identity, so a tree that holds two blocks with one root resolves it
to neither. -/
def find? (T : Finset (Block V)) (r : BlockId) : Option (Block V) :=
  pickUnique? T (fun B => decide (B.root = r))

/-- Whether no block of `T` beats `B` in the `deeper` order. -/
def isDeepestIn (T : Finset (Block V)) (B : Block V) : Bool :=
  decide (∀ C ∈ T, deeper C B = false)

/-- §1 "deepest": maximum depth, ties by the fixed root order
(PROTOCOL.md `sec:substrate`). `none` on an empty tree, and on the degenerate tie where two
distinct blocks share a depth *and* a root. -/
def deepest? (T : Finset (Block V)) : Option (Block V) :=
  pickUnique? T (isDeepestIn T)

end Block

@[inherit_doc] scoped infix:50 " ⪯ " => Block.Preceq
@[inherit_doc] scoped infix:50 " ≺ " => Block.Prec

end DecoupledConsensusModel
end

end
