module
public import DecoupledConsensusInternal.Legacy.Instance
public import DecoupledConsensusStatements.Instantiation.RoundTimes

@[expose] public section

/-!
# Round-time bridge

Purpose: connect the explicit round-time definition to the historical
`Nat.find` specification.
An auditor checks that the closed form is only a representation change and
that the least-action-round contract is unchanged.

Defines: `nextRound_eq_find`.
Read after: the instantiation round schedule and its compatibility lemmas.
Read next: the generic bridge consumers.
-/

namespace DecoupledConsensusModel
namespace Proofs

open Internal Execution Statements

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The explicit `nextRound` equals the historical least-round expression. -/
theorem nextRound_eq_find (S : Setup V) (t : Time) :
    Statements.Instantiation.nextRound S t =
      Nat.find (show ∃ r : Round, t ≤ S.a r from
        ⟨Statements.Instantiation.roundAt S t, Statements.roundAt_spec S t⟩) := by
  let h : ∃ r : Round, t ≤ S.a r :=
    ⟨Statements.Instantiation.roundAt S t, Statements.roundAt_spec S t⟩
  have hfind : t ≤ S.a (Nat.find h) := Nat.find_spec h
  have hmin : Nat.find h ≤ Statements.Instantiation.roundAt S t :=
    Nat.find_min' h (Statements.roundAt_spec S t)
  have hnext : Statements.Instantiation.roundAt S t ≤ Nat.find h := by
    by_contra hlt
    have hlt' : Nat.find h < Statements.Instantiation.roundAt S t := Nat.lt_of_not_ge hlt
    exact (Statements.roundAt_min S t hlt') hfind
  change Statements.Instantiation.roundAt S t = Nat.find h
  exact hnext.antisymm hmin

end Proofs
end DecoupledConsensusModel

end
