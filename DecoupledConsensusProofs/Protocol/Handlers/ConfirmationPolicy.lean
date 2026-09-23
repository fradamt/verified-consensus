module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusModel.Protocol.Handlers
public import DecoupledConsensusProofs.Objects.Ancestry

@[expose] public section

/-!
# User confirmation policy: progress, replacement, and prefix preservation

These are algebraic facts about the record update. The execution proofs must
derive candidate compatibility and freshness from their protocol regimes.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace ConfirmationPolicy

variable {V : Type} [DecidableEq V]

/-- Every candidate is included in the resulting record. -/
theorem candidate_preceq_advance (old candidate : Block V) :
    Block.Preceq candidate (Protocol.advance_confirmed old candidate) := by
  unfold Protocol.advance_confirmed
  split
  · assumption
  · exact Block.preceq_self _

/-- The record is always either the previous record or the new candidate. -/
theorem advance_eq_old_or_candidate (old candidate : Block V) :
    Protocol.advance_confirmed old candidate = old ∨
      Protocol.advance_confirmed old candidate = candidate := by
  unfold Protocol.advance_confirmed
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A candidate below the previous record does not remove confirmed progress. -/
theorem advance_eq_old (old candidate : Block V)
    (h : Block.Preceq candidate old) :
    Protocol.advance_confirmed old candidate = old := by
  exact if_pos h





/-- A candidate extending the protected prefix establishes that prefix even
when the previous record was unsafe. -/
theorem prefix_preceq_advance_of_candidate {B old candidate : Block V}
    (h : Block.Preceq B candidate) :
    Block.Preceq B (Protocol.advance_confirmed old candidate) :=
  Block.preceq_trans h (candidate_preceq_advance old candidate)

/-- Once recorded, a prefix survives any compatible candidate. The candidate
may be an ancestor of the prefix; it need not extend the previous record's suffix. -/
theorem prefix_preceq_advance_of_compatible {B old candidate : Block V}
    (hold : Block.Preceq B old)
    (hcandidate : Block.compatible B candidate = true) :
    Block.Preceq B (Protocol.advance_confirmed old candidate) := by
  simp only [Block.compatible, Bool.or_eq_true] at hcandidate
  rcases hcandidate with h | h
  · exact prefix_preceq_advance_of_candidate h
  · rw [advance_eq_old old candidate (Block.preceq_trans h hold)]
    exact hold

/-- Compatibility of the resulting record also suffices for preservation.
This form lets an execution proof use agreement of actual node outputs. -/
theorem prefix_preceq_advance_of_result_compatible {B old candidate : Block V}
    (hold : Block.Preceq B old)
    (hresult : Block.compatible B (Protocol.advance_confirmed old candidate) = true) :
    Block.Preceq B (Protocol.advance_confirmed old candidate) := by
  by_cases hretain : Block.Preceq candidate old
  · simpa only [advance_eq_old old candidate hretain] using hold
  · have hreplace : Protocol.advance_confirmed old candidate = candidate := if_neg hretain
    rw [hreplace] at hresult ⊢
    simp only [Block.compatible, Bool.or_eq_true] at hresult
    rcases hresult with h | h
    · exact h
    · exact False.elim (hretain (Block.preceq_trans h hold))


/-- Slot freshness suffices when strict ancestry raises slots in the relevant
execution. The slot-order condition is explicit and is not a model axiom. -/
theorem advance_eq_candidate_of_slot (old candidate : Block V)
    (hslot : old.slot ≤ candidate.slot)
    (hstrict : Block.Preceq candidate old → candidate ≠ old → candidate.slot < old.slot) :
    Protocol.advance_confirmed old candidate = candidate := by
  unfold Protocol.advance_confirmed
  split
  · rename_i hpre
    by_cases heq : candidate = old
    · exact heq.symm
    · exact False.elim ((Nat.not_lt_of_ge hslot) (hstrict hpre heq))
  · rfl


end ConfirmationPolicy
end Proofs
end DecoupledConsensusModel

end
