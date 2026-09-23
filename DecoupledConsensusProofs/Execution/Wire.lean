module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.ModelVocabulary.Execution.NamedEvent
public import DecoupledConsensusProofs.Objects.Ancestry

@[expose] public section

/-! Structural projection facts for named wire data. There is
no erasure-injectivity claim, handler, network execution or runtime selection. -/
namespace DecoupledConsensusModel.Proofs.NamedWire
open Execution
variable {V : Type}

theorem erase_root (B : NamedBlock V) : B.erase.root = B.root := by cases B <;> rfl

theorem erase_slot (B : NamedBlock V) : B.erase.slot = B.slot := by cases B <;> rfl

theorem erase_parent_optional (B : NamedBlock V) :
    B.erase.parent? = B.parent?.map NamedBlock.erase := by cases B <;> rfl

theorem erase_parent (B : NamedBlock V) : B.erase.parent = B.parent.erase := by
  cases B <;> rfl


theorem erase_goldfish_votes (B : NamedBlock V) : B.erase.gf_votes = B.gf_votes := by
  cases B <;> rfl

theorem erase_goldfish_support (B : NamedBlock V) :
    B.erase.gf_support_votes = B.gf_support_votes := by cases B <;> rfl

/-- Every row position is projected; no named payload is reconstructed from erasure. -/
theorem erase_attestations (B : NamedBlock V) :
    B.erase.attestations = B.attestations.map NamedAttestation.erase := by cases B <;> rfl

theorem erase_proposer (B : NamedBlock V) : B.erase.proposer? = B.proposer? := by
  cases B <;> rfl

section Ancestry
variable [DecidableEq V]

/-- Only the forward direction is asserted: full named ancestry projects to geometry. -/
theorem erase_preceq {A B : NamedBlock V} (h : NamedBlock.Preceq A B) :
    Block.Preceq A.erase B.erase := by
  induction B with
  | genesis =>
    simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at h
    subst A
    exact Block.preceq_self _
  | node p s r votes support rows proposer ih =>
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with rfl | hparent
    · exact Block.preceq_self _
    · change Block.preceq A.erase (.node p.erase s r votes support
        (rows.map NamedAttestation.erase) proposer) = true
      simp only [Block.preceq, Bool.or_eq_true]
      exact Or.inr (ih hparent)

theorem erase_compatible {A B : NamedBlock V} (h : NamedBlock.compatible A B = true) :
    Block.compatible A.erase B.erase = true := by
  simp only [NamedBlock.compatible, Bool.or_eq_true] at h
  simp only [Block.compatible, Bool.or_eq_true]
  exact h.elim (fun h => Or.inl (erase_preceq h)) (fun h => Or.inr (erase_preceq h))

end Ancestry

#print axioms erase_root
#print axioms erase_slot
#print axioms erase_parent_optional
#print axioms erase_parent
#print axioms erase_goldfish_votes
#print axioms erase_goldfish_support
#print axioms erase_attestations
#print axioms erase_proposer
#print axioms erase_preceq
#print axioms erase_compatible
end DecoupledConsensusModel.Proofs.NamedWire

end
