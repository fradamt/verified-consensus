module
public import DecoupledConsensusModel.Objects.Blocks
public import DecoupledConsensusModel.Protocol.ForkChoice.Head

@[expose] public section

/-!
# `DecoupledConsensusModel/Protocol/Duties/Inputs.lean`

Purpose: Section 7, block 3 — the duty inputs and the vote duties get_sg_vote and get_fg_vote over the saved grades.
Paper: `docs/PROTOCOL.md` `sec:public-handlers`; algorithm block: `alg:duties`.

Defines: ProposalInput, AttestationInput, and get_sg_vote_with.

Read after: `DecoupledConsensusModel.Objects.Blocks`, `DecoupledConsensusModel.Protocol.ForkChoice.Head`
Read next: `DecoupledConsensusModel.Protocol.Duties.Proposals`.

State read: the protocol environment, schedule, store layers, and the view inputs named by the definitions.
State written: the returned store, chain state, record, or view value; pure readers write no state.

Representation notes: Typed Lean records, finite collections, and projections preserve the executable protocol representation. This module states no proof theorem.
-/

-- ── from Healing/DutyInputs.lean ──
section
/-! Common read data for the duty constructors. These records contain actual
selector results, not open or provenance assumptions. -/
namespace DecoupledConsensusModel.Protocol

structure ProposalInput (V : Type) where
  parent : Block V
  slot : Slot
  root : BlockId
  gf_votes : List (GoldfishVote V)
  gf_support_votes : List (GoldfishVote V)
  proposer : V

/-- The Boolean inside fields is the source state's NJ bit, not a timeout flag. -/
structure AttestationInput (V : Type) where
  val_index : V
  round : Round
  confirmed : Option BlockId
  fields : Option (Height × BlockId × Bool)
  h_j : Height
  J : BlockId
  h_F : Height

end DecoupledConsensusModel.Protocol
end

-- ── from Healing/Action.lean ──
section
/-!
# The proposal and round action

These are the selected contract-parameterised decision cores. The named runtime
supplies the contract and applies the final store writes at the protocol layer.
-/

namespace DecoupledConsensusModel
namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- One shared proposal read. -/
def with_proposal_input {Result : Type} (contract : GradeContract V)
    (E : Env V) (hc : HealConfig) (nd : Protocol.Node V) (st : HealingStore V)
    (use : ProposalInput V → Result) : Result :=
  let s := st.s
  let votes := Protocol.proposer_view st.toFG.toSG.toGoldfishStore s
  let support_votes := Protocol.proposer_support_view st.toFG.toSG.toGoldfishStore s
  let H := get_head_with contract E hc st votes.toFinset support_votes.toFinset (s - 1)
  use ⟨H, s, nd.new_root s, votes, support_votes, nd.val_index⟩

/-! ## The round action -/

/-- The contract's grade-2 candidate for round `r`. -/
def grade2_block_with (contract : GradeContract V)
    (E : Env V) (hc : HealConfig) (st : HealingStore V) (r : Round) :
    Option (Block V) :=
  (contract.read E hc st r).Q2

/-- The selected SG vote, with the grade-2 candidate supplied by the caller. -/
def get_sg_vote_with (contract : GradeContract V)
    (E : Env V) (hc : HealConfig) (st : HealingStore V) (r : Round)
    (A_G2 : Option (Block V)) : Block V :=
  contract.sgVote st { contract.read E hc st r with Q2 := A_G2 }

/-- The contract's finality-gadget source for a grade-2 candidate. -/
def fg_source_with (contract : GradeContract V)
    (E : Env V) (hc : HealConfig) (st : HealingStore V) (r : Round)
    (A_G2 : Option (Block V)) : Option (Block V) :=
  match A_G2 with
  | none => none
  | some q =>
    match deepest_clear (some q) st.live_confirmed
        (contract.read E hc st r).clear with
    | some B => some B
    | none => some q

/-- The finality-gadget fields read by the attestation action. -/
def get_fg_vote_with (contract : GradeContract V)
    (E : Env V) (hc : HealConfig) (st : HealingStore V) (r : Round)
    (A_G2 : Option (Block V)) :
    Option (Height × BlockId × Bool) × Height × BlockId × Height :=
  let votes := st.pool st.s
  let support_votes :=
    (st.pool st.s).filter (fun u => Protocol.resolved st.T u = true)
  let H := get_head_with contract E hc st votes support_votes st.s
  ((fg_source_with contract E hc st r A_G2).map
      (fun q => ((st.σ q).h, (st.σ q).T_h.root, (st.σ q).nj)),
    (st.σ H).h_j, (st.σ H).J.root, (st.σ H).h_F)

/-- One shared attestation read. -/
def with_attestation_input {Result : Type} (contract : GradeContract V)
    (E : Env V) (hc : HealConfig) (nd : Protocol.Node V) (st : HealingStore V)
    (use : AttestationInput V → Result) : Result :=
  let r := hc.round_of st.s
  let A_G2 := grade2_block_with contract E hc st r
  let fg := get_fg_vote_with contract E hc st r A_G2
  use ⟨nd.val_index, r, some (get_sg_vote_with contract E hc st r A_G2).root,
    fg.1, fg.2.1, fg.2.2.1, fg.2.2.2⟩

end Protocol
end DecoupledConsensusModel
end

end
