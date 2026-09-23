module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.Wire

@[expose] public section

/-!
# Named ancestry, at substrate level 

Reflexivity, one-step extension, and the lift of an erased ancestor back to a
named one. All three are pure facts about `NamedBlock` and `NamedBlock.erase`,
with no runtime, handler or admissibility content.

They existed only as `private` copies inside `NamedFinalityCertificates` and
`NamedJustificationCertificates`, both of which sit above `Bridges`. The erased
root-collision bridge in `Bridges` needs the same lift, so they are restated
here, below everything that uses them.
-/



namespace DecoupledConsensusModel.Proofs.NamedAncestry

variable {V : Type} [DecidableEq V]

theorem named_self (B : NamedBlock V) : NamedBlock.Preceq B B := by
  cases B <;> simp [NamedBlock.Preceq, NamedBlock.preceq]

theorem named_extend {A parent : NamedBlock V} (s : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V)) (rows : List (NamedAttestation V))
    (proposer : V) (h : NamedBlock.Preceq A parent) :
    NamedBlock.Preceq A (.node parent s root votes support rows proposer) := by
  simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
  exact Or.inr h

/-- Existence inside the full recursive chain. This is not injectivity of
`erase`: it says an erased ancestor of a named body is the erasure of some named
ancestor of that body. -/
theorem erased_ancestor_lift (B : NamedBlock V) {raw : Block V}
    (h : Block.Preceq raw B.erase) :
    ∃ A : NamedBlock V, NamedBlock.Preceq A B ∧ A.erase = raw := by
  induction B with
  | genesis =>
    have hr : raw = Block.genesis := by
      simpa only [Block.Preceq, Block.preceq, NamedBlock.erase,
        decide_eq_true_eq] using h
    subst raw
    exact ⟨.genesis, named_self _, rfl⟩
  | node parent s root votes support rows proposer ih =>
    let B := NamedBlock.node parent s root votes support rows proposer
    have hcases : raw = B.erase ∨ Block.Preceq raw parent.erase := by
      simpa only [B, NamedBlock.erase, Block.Preceq, Block.preceq,
        Bool.or_eq_true, decide_eq_true_eq] using h
    rcases hcases with heq | hp
    · exact ⟨B, named_self B, heq.symm⟩
    · obtain ⟨A, hA, hErase⟩ := ih hp
      exact ⟨A, named_extend s root votes support rows proposer hA, hErase⟩

end DecoupledConsensusModel.Proofs.NamedAncestry

end
