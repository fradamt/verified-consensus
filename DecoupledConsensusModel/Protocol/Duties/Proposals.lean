module
public import Mathlib.Data.Finset.Sort
public import DecoupledConsensusModel.Protocol.Handlers
public import DecoupledConsensusModel.Protocol.Duties.Inputs
public import DecoupledConsensusModel.Protocol.ValidatorClient

@[expose] public section

/-!
# `DecoupledConsensusModel/Protocol/Duties/Proposals.lean`

Purpose: Section 7, block 3 — proposal_attestations, propose_block, goldfish_vote and attest over the cumulative store.
Paper: `PROTOCOL.md` `sec:public-handlers`; algorithm block: `alg:duties`.

Defines: `NamedProposalRows.select` (the eligible pool and carried rows), `excludeOnChain`,
`capPerSigner` and `proposalRows` (the bounded proposal payload), `NamedActions.proposal_with`
(the honest proposal), and the vote and attestation duties.

Read after: `DecoupledConsensusModel.Protocol.Handlers`, `DecoupledConsensusModel.Protocol.Duties.Inputs`, `DecoupledConsensusModel.Protocol.ValidatorClient`
Read next: `DecoupledConsensusModel/Protocol/Tick.lean` (where the duties run), then
`docs/MODELING_CHOICES.md` section 1.6 (the bounded proposal rows).

State read: the protocol environment, schedule, store layers, and the view inputs named by the definitions.
State written: the returned store, chain state, record, or view value; pure readers write no state.

Representation notes: Typed Lean records, finite collections, and projections preserve the executable protocol representation. This module states no proof theorem.
MODEL_MAP rows: `proposal_attestations`, `propose_block`, `goldfish_vote`, `attest`.
-/

-- ── from Protocol/ProposalRows.lean ──
section
/-!
# Proposal rows

This module selects the source and bounds the proposal payload. The source contains
window-filtered processed pool rows, including unresolved SG heads, followed
by carried rows from eligible processed blocks. `proposalRows` removes rows
already on the parent chain and keeps at most two distinct full rows per
(validator, round).
-/
namespace DecoupledConsensusModel
namespace Protocol

inductive ProposalRowSource where
  | poolAndCarried
  deriving DecidableEq, Repr

namespace ProposalRows
variable {V : Type} [DecidableEq V]

/-- The inclusive SG admission window, applied to the row's own round. -/
def inWindow (hc : Protocol.HealConfig) (st : Store V) (r : Round) : Bool :=
  decide (hc.round_of st.s - hc.η_SG ≤ r ∧ r ≤ hc.round_of st.s)

end ProposalRows
end Protocol
end DecoupledConsensusModel
end

-- ── from Protocol/NamedProposalRows.lean ──
section
/-! Full named proposal rows. Erasure is used only for the prior round/SG-resolution
predicates; it is never a signed-row identity or an on-chain exclusion key. -/
namespace DecoupledConsensusModel.Protocol.NamedProposalRows
variable {V : Type} [DecidableEq V]

def processedRows (hc : Protocol.HealConfig) (st : NamedStore V) : List (NamedAttestation V) :=
  (List.range (hc.round_of st.core.s + 1)).flatMap st.sg_rows

def orderedRoots (st : NamedStore V) : List BlockId :=
  (st.bodies.image NamedBlock.root).sort (fun a b => a ≤ b)

/-- A root collision has no unique answer, just as in the current resolver. -/
def orderedBodies (st : NamedStore V) : List (NamedBlock V) :=
  (orderedRoots st).filterMap fun root =>
    pickUnique? st.bodies (fun B => decide (B.root = root))

def eligibleBody (hc : Protocol.HealConfig) (st : NamedStore V) (B : NamedBlock V) : Bool :=
  ProposalRows.inWindow hc st.core (hc.round_of B.slot) &&
    carried_attestations_admissible hc B.erase

def poolRows (hc : Protocol.HealConfig) (st : NamedStore V) : List (NamedAttestation V) :=
  (processedRows hc st).filter (fun row => ProposalRows.inWindow hc st.core row.round)

def carriedRows (hc : Protocol.HealConfig) (st : NamedStore V) : List (NamedAttestation V) :=
  (orderedBodies st).flatMap fun B =>
    if eligibleBody hc st B then
      B.attestations.filter (fun row => ProposalRows.inWindow hc st.core row.round)
    else []

def select (source : ProposalRowSource) (hc : Protocol.HealConfig) (st : NamedStore V) :
    List (NamedAttestation V) :=
  poolRows hc st ++ carriedRows hc st

-- Divergence from the paper: the proposal keeps at most two distinct rows per (validator, round) (bounded block size); the paper copies every eligible row.

/-- Full named rows on the head's recursive ancestor chain. -/
def chainRows : NamedBlock V → List (NamedAttestation V)
  | .genesis => []
  | .node p _ _ _ _ rows _ => rows ++ chainRows p

def excludeOnChain (head : NamedBlock V) (rows : List (NamedAttestation V)) :
    List (NamedAttestation V) := rows.filter (fun row => !decide (row ∈ chainRows head))

/-- Keep the first two distinct full rows of each (validator, round), in list
order; later rows of that pair and repeated rows are dropped. -/
def capPerSigner (rows : List (NamedAttestation V)) : List (NamedAttestation V) :=
  rows.foldl (fun acc row =>
    if row ∈ acc ||
        decide (2 ≤ (acc.filter (fun a =>
          decide (a.val_index = row.val_index ∧ a.round = row.round))).length)
    then acc else acc ++ [row]) []

/-- The honest proposal's rows: drop rows already on the parent chain, then keep
at most two distinct rows per (validator, round). At most
`2 · |V| · (η_SG + 1)` rows result. -/
def proposalRows (parent : NamedBlock V) (rows : List (NamedAttestation V)) :
    List (NamedAttestation V) :=
  capPerSigner (excludeOnChain parent rows)

end DecoupledConsensusModel.Protocol.NamedProposalRows
end

-- ── from Healing/NamedActions.lean ──
section
/-! Named constructors from the shared actual duty reads. The local
invariant proves parent lookup succeeds for the concrete current/frame
contracts. The optional result exposes failed lookup for arbitrary stores. -/
namespace DecoupledConsensusModel.Protocol.NamedActions
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Find the retained signed body of the actual selected core parent.
Comparison uses complete erasure, not only the root identifier. -/
def parentBody? (st : Protocol.NamedStore V) (parent : Block V) : Option (NamedBlock V) :=
  pickUnique? st.bodies (fun B => decide (B.erase = parent))

/-- Use the actual shared read, then remove full named rows already on the
selected named chain. No erased-row equality is used for the parent-chain exclusion. -/
def proposal_with (contract : GradeContract V) (source : Protocol.ProposalRowSource)
    (E : Env V) (hc : HealConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) : Option (NamedBlock V) :=
  with_proposal_input contract E hc nd st.core.toHealing fun input =>
    (parentBody? st input.parent).map fun parent =>
      NamedBlock.node parent input.slot input.root input.gf_votes input.gf_support_votes
        (Protocol.NamedProposalRows.proposalRows parent
          (Protocol.NamedProposalRows.select source hc st)) input.proposer

/-- Structural conversion only. The shared read already computed every
field, including the separate SG head, FG source and finality head. -/
def creatorInput (input : AttestationInput V) : Protocol.NamedRecord.Input V :=
  ⟨input.val_index, input.round, input.confirmed, input.fields,
    input.h_j, input.J, input.h_F⟩

/-- The actual source fields name a timeout's entry. The signing client
updates its height-wide locks and named timeout history exactly once. -/
def round_action_with (contract : GradeContract V)
    (E : Env V) (hc : HealConfig) (nd : Protocol.Node V)
    (st : HealingStore V) (record : Protocol.NamedRecord) :
    Protocol.NamedRecord × NamedAttestation V :=
  with_attestation_input contract E hc nd st fun input =>
    Protocol.NamedRecord.create record (creatorInput input)

end DecoupledConsensusModel.Protocol.NamedActions
end

-- ── from Protocol/NamedDuties.lean ──
section
/-! Concrete named duties with carried-row admission and pool and carried
proposal rows. GF and confirmation use the existing core algorithms. The scheduler
and event runtime bind these operations in separate modules. -/
namespace DecoupledConsensusModel.Protocol.NamedDuties
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Process the exact constructed named block with carried-row admission.
A failed lookup changes nothing. Local reachability proofs must rule out
that branch when an honest proposal duty is scheduled. -/
def propose_block_with (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (nd : Protocol.Node V) (st : NamedStore V) : NamedStore V × Option (NamedBlock V) :=
  match Protocol.NamedActions.proposal_with contract .poolAndCarried E hc nd st with
  | none => (st, none)
  | some B => (NamedAdmission.on_block_with .alsoCarried E hc cfg st B, some B)

/-- Direct use of the existing GF duty. The retained named data is unchanged. -/
def goldfish_vote_with (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (st : NamedStore V) : NamedStore V × Option (GoldfishVote V) :=
  let out := Protocol.goldfish_vote_with contract E hc nd st.core
  ({ st with core := out.1 }, out.2)

/-- Direct use of the existing confirmation update. -/
def update_confirmation_with (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : NamedStore V) (s : Slot) : NamedStore V :=
  { st with core := Protocol.update_confirmation_with contract E hc st.core s }

/-- Construct and locally accept the original named row once. The caller
must supply the actual post-confirmation store at the action time. -/
def attest_with (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (st : NamedStore V) (record : Protocol.NamedRecord) :
    NamedStore V × Protocol.NamedRecord × NamedAttestation V :=
  let out := Protocol.NamedActions.round_action_with contract E hc nd st.core.toHealing record
  (NamedAdmission.admit_row hc st out.2, out.1, out.2)

end DecoupledConsensusModel.Protocol.NamedDuties
end

end
