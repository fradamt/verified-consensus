module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusModel.Objects.Identifiers

@[expose] public section

/-!
# W4 — the joint cover/grade induction ( shared scaffold)

The persistence cover and the later-round grade are mutually recursive, which
is the circularity the corresponding branch and w4-mc2 each hit while trying to prove one
assuming the other (w4-c1's note,
`W4GSTZeroOpeningLifecycleRun.lean:1500-1519`).

They are well founded together. A round-`k` grade reads only rounds strictly
below `k`, so it may consume the covers of those rounds; the round-`k` cover
then consumes the round-`k` grade, which is what the non-eligible branch's
tier-two SG vote needs (that vote IS the round's frozen G2 root, and
`B ⪯ Q2 k` holds exactly when `B` is G2-graded at `k`).

This scaffold is regime-free: only the two per-round steps differ between
`WeakGenesis` and `WeakContinuation`, so it is proved once and instantiated
twice. Both steps are also handed the earlier grades, which costs nothing and
saves a branches from renegotiating the shape if its step wants them.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace W4CoverGrade

/-- **The joint strong induction on the round.** `Grade k` is allowed the
covers and grades of all strictly earlier rounds; `Cover k` is allowed those
and the grade of its own round. -/
theorem coverAndGrade_of_steps
    (Cover Grade : Round → Prop)
    (hgradeStep : ∀ k : Round,
      (∀ j : Round, j < k → Cover j) →
      (∀ j : Round, j < k → Grade j) → Grade k)
    (hcoverStep : ∀ k : Round,
      (∀ j : Round, j < k → Cover j) →
      (∀ j : Round, j < k → Grade j) →
      Grade k → Cover k) :
    ∀ k : Round, Cover k ∧ Grade k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      have hc : ∀ j : Round, j < k → Cover j := fun j hj => (ih j hj).1
      have hg : ∀ j : Round, j < k → Grade j := fun j hj => (ih j hj).2
      have hgk : Grade k := hgradeStep k hc hg
      exact ⟨hcoverStep k hc hg hgk, hgk⟩

#print axioms coverAndGrade_of_steps

/-- The cover half on its own, for a consumer that only needs it. -/
theorem cover_of_steps
    (Cover Grade : Round → Prop)
    (hgradeStep : ∀ k : Round,
      (∀ j : Round, j < k → Cover j) →
      (∀ j : Round, j < k → Grade j) → Grade k)
    (hcoverStep : ∀ k : Round,
      (∀ j : Round, j < k → Cover j) →
      (∀ j : Round, j < k → Grade j) →
      Grade k → Cover k) :
    ∀ k : Round, Cover k :=
  fun k => (coverAndGrade_of_steps Cover Grade hgradeStep hcoverStep k).1

#print axioms cover_of_steps



end W4CoverGrade
end Proofs
end DecoupledConsensusModel

end
