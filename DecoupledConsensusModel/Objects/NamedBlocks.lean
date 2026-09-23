module
public import DecoupledConsensusModel.Objects.Blocks

@[expose] public section

/-!
# `DecoupledConsensusModel/Objects/NamedBlocks.lean`

Purpose: §1 wire objects with full payloads — named pairs, named attestations, named blocks and their erasure.
Paper: `docs/PROTOCOL.md` `sec:complete-store`; algorithm block: the Section 7 wire objects and parameters.

Defines: NamedHeightPair, erase, matchesEntry, NamedAttestation, NamedBlock, slot, root, parent, gf_votes, attestations, proposer?, preceq, Preceq.

Read after: `DecoupledConsensusModel.Objects.Blocks`
Read next: `DecoupledConsensusModel.Protocol.ChainState`.

State read: the identifier, time, weight, parameter, and wire types imported by this subject.
State written: typed wire values, parameters, and pure projections; no mutable state is written.

Representation notes: The paper objects use typed Lean inductives/structures and finite collections. Named payloads retain their erased twin where both are active.
MODEL_MAP rows: NamedHeightPair, erase, matchesEntry, NamedAttestation, NamedBlock, slot, root, parent, gf_votes, attestations, proposer?, preceq, Preceq.
-/

-- ── from Substrate/NamedAttestations.lean ──
section
/-! Separate named wire payload for entry-bound height votes. The selected
receipt and admission path carries the entry annotation in the signed row; it
is not receiver-only metadata. -/
namespace DecoupledConsensusModel

inductive NamedHeightPair where
  | empty
  | vote (height : Height) (entry : BlockId) (timeout : Bool)
  deriving DecidableEq, Repr

namespace NamedHeightPair

/-- Erasure is for prior SG/accountability views, not signed-row identity. -/
def erase : NamedHeightPair → HeightPair
  | .empty => .empty
  | .vote h entry timeout => if timeout then .timeout h else .target h entry

/-- Both proper targets and timeouts use the same height/entry match. -/
def matchesEntry (height : Height) (entry : BlockId) : NamedHeightPair → Bool
  | .empty => false
  | .vote h target _ => decide (h = height ∧ target = entry)

end NamedHeightPair

structure NamedAttestation (V : Type) where
  val_index : V
  round : Round
  confirmed : Option BlockId
  height_pair : NamedHeightPair
  finality_pair : Option FinalityPair
  deriving DecidableEq, Repr

namespace NamedAttestation

/-- Timeout annotations erase to prior timeouts, never to proper targets. -/
def erase {V : Type} (row : NamedAttestation V) : CombinedAttestation V :=
  ⟨row.val_index, row.round, row.confirmed, row.height_pair.erase, row.finality_pair⟩

end NamedAttestation
end DecoupledConsensusModel
end

-- ── from Substrate/NamedBlocks.lean ──
section
/-! Separate recursive block data with full named rows at every ancestor.
No prior block constructor changes. Erasure forgets timeout annotations;
it is a geometry projection, not a globally injective identity encoding. -/
namespace DecoupledConsensusModel

inductive NamedBlock (V : Type) where
  | genesis
  | node (parent : NamedBlock V) (slot : Slot) (root : BlockId)
      (gf_votes : List (GoldfishVote V)) (gf_support_votes : List (GoldfishVote V))
      (attestations : List (NamedAttestation V)) (proposer : V)
  deriving DecidableEq, Repr

namespace NamedBlock
variable {V : Type}

def slot : NamedBlock V → Slot
  | .genesis => 0
  | .node _ s _ _ _ _ _ => s

def root : NamedBlock V → BlockId
  | .genesis => genesisRoot
  | .node _ _ r _ _ _ _ => r

def parent : NamedBlock V → NamedBlock V
  | .genesis => .genesis
  | .node p _ _ _ _ _ _ => p

def gf_votes : NamedBlock V → List (GoldfishVote V)
  | .genesis => []
  | .node _ _ _ votes _ _ _ => votes

def attestations : NamedBlock V → List (NamedAttestation V)
  | .genesis => []
  | .node _ _ _ _ _ rows _ => rows

def proposer? : NamedBlock V → Option V
  | .genesis => none
  | .node _ _ _ _ _ _ proposer => some proposer

/-- The named tree keeps its own payload; only this view erases annotations. -/
def erase : NamedBlock V → Block V
  | .genesis => .genesis
  | .node p s r votes support rows proposer =>
      .node p.erase s r votes support (rows.map NamedAttestation.erase) proposer

section Ancestry
variable [DecidableEq V]

/-- Equality here compares full named payloads, including all ancestor rows. -/
def preceq (A : NamedBlock V) : NamedBlock V → Bool
  | .genesis => decide (A = .genesis)
  | B@(.node p _ _ _ _ _ _) => decide (A = B) || preceq A p

def Preceq (A B : NamedBlock V) : Prop := preceq A B = true

instance (A B : NamedBlock V) : Decidable (Preceq A B) :=
  inferInstanceAs (Decidable (preceq A B = true))

end Ancestry
end NamedBlock
end DecoupledConsensusModel
end

end
