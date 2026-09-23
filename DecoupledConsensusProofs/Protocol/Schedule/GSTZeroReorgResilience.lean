module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.GSTZeroProposalEvaluation
public import DecoupledConsensusProofs.Protocol.Grades.GSTZeroSelectionSafety
public import DecoupledConsensusProofs.Protocol.Grades.GSTZeroConfirmationZero
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ConePersistence

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# GST-zero honest-proposal reorganization resilience

The pure schedule arithmetic in this file is live in the named tree. The
proposal-walk and frontier chain is not:  records its producers as absent.
The live declarations keep their old names, while proposal-facing statements
use the named proposal witness and prepared voter head, erasing only for
block geometry.
-/



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The next proposal occurs strictly before the current proposal's
confirmation evaluation. -/
theorem proposal_time_succ_lt_confirmation_time
    (E : Env V) (s : Slot) :
    Protocol.proposal_time E (s + 1) < Protocol.confirmation_time E s := by
  unfold Protocol.proposal_time Protocol.confirmation_time Env.t slotStart
  push_cast
  have h46 : 4 * E.Δ < 6 * E.Δ :=
    Int.mul_lt_mul_of_pos_right (by decide : (4 : Time) < 6) E.Δ_pos
  calc
    4 * E.Δ * ((s : Time) + 1) =
        4 * E.Δ * (s : Time) + 4 * E.Δ := by ring
    _ < 4 * E.Δ * (s : Time) + 6 * E.Δ :=
      Int.add_lt_add_left h46 _

/-- A slot's support cutoff is strictly before the next slot's proposal. -/
theorem support_cutoff_lt_proposal_time_succ
    (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s < Protocol.proposal_time E (s + 1) := by
  unfold Protocol.support_cutoff Protocol.proposal_time Env.t slotStart
  push_cast
  have h24 : 2 * E.Δ < 4 * E.Δ :=
    Int.mul_lt_mul_of_pos_right (by decide : (2 : Time) < 4) E.Δ_pos
  calc
    4 * E.Δ * (s : Time) + 2 * E.Δ <
        4 * E.Δ * (s : Time) + 4 * E.Δ :=
      Int.add_lt_add_left h24 _
    _ = 4 * E.Δ * ((s : Time) + 1) := by ring


/-- Two slot starts leave the current confirmation evaluation strictly in the
past. -/
theorem confirmation_time_lt_proposal_time_of_add_two_le
    (E : Env V) {s k : Slot} (hsk : s + 2 <= k) :
    Protocol.confirmation_time E s < Protocol.proposal_time E k := by
  have hbase : Protocol.confirmation_time E s <
      Protocol.proposal_time E (s + 2) := by
    unfold Protocol.confirmation_time Protocol.proposal_time Env.t slotStart
    push_cast
    have h68 : 6 * E.Δ < 8 * E.Δ :=
      Int.mul_lt_mul_of_pos_right (by decide : (6 : Time) < 8) E.Δ_pos
    calc
      4 * E.Δ * (s : Time) + 6 * E.Δ <
          4 * E.Δ * (s : Time) + 8 * E.Δ :=
        Int.add_lt_add_left h68 _
      _ = 4 * E.Δ * ((s : Time) + 2) := by ring
  exact lt_of_lt_of_le hbase (proposal_time_mono E hsk)







/-- The named replacement for the two ordinary Section 7 head-call families.
The proposal witness is explicit, and geometric conclusions use `B.erase`. -/
structure HonestProposalProposalVoteResilience
    (S : Setup V) (rho : Run V) (s : Slot) : Prop where
  proposal_calls : ∀ {k : Slot}, s < k ->
    Protocol.proposal_time S.E k <= rho.horizon ->
    S.E.proposer k ∈ rho.honest ->
    ∀ B : NamedBlock V,
      Statements.Instantiation.proposedBlockAt S rho s = some B ->
      Block.Preceq B.erase (Proofs.HealingSurface.proposedParent S rho k)
  vote_calls : ∀ {k : Slot}, s <= k ->
    Protocol.vote_time S.E k <= rho.horizon ->
    ∀ B : NamedBlock V,
      Statements.Instantiation.proposedBlockAt S rho s = some B ->
      ∀ {v : V}, v ∈ rho.honest ->
      Block.Preceq B.erase (voterHeadAt S rho v k)





#print axioms proposal_time_succ_lt_confirmation_time
#print axioms support_cutoff_lt_proposal_time_succ
#print axioms confirmation_time_lt_proposal_time_of_add_two_le

end Protocol
end DecoupledConsensusModel

end
