module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.DerivationGeometry
public import DecoupledConsensusProofs.Protocol.Handlers.BlockProcessingDefaults

@[expose] public section

/-! # Named justification monotonicity along named ancestry

The named twin of `derivedJustification_strict_or_eq_of_parent` and
`derivedJustification_strict_or_eq_of_preceq`
(`RecurringFinalityRun.lean:959` and `:992`, both parked inside the module's
423-1897 comment block).

earlier's opening-carrier finality uses the erased pair to turn "some ancestor of
the later carrier's `+1` proposal justifies the earlier carrier's opening
height" into the `hjust` premise of the common-finality step. Every height in
the selection is `Protocol.derive_named` of a named proposal, so the erased
pair does not apply, and this was the one missing piece that forced branches
w4-d2's `W4CarrierChainFinalityPin` to bundle four of earlier's steps.

The proof is the erased one with the named derivation substituted. The single
protocol fact it needs, that a chain state's justification height is below its
own height, is `NamedDerivationGeometry.chainOrder_derive_named`, the named
chain order. Nothing here is an execution or authenticity claim, and no
`derive_named` is applied to an erased block.

The three row-fold projections are verbatim copies of the private
`fold_h`/`fold_J`/`fold_h_j` of `NamedCheckpointAlgebraRun.lean:111,127,135`,
which cannot be imported because they are `private`. Both they and this file
read them off `NamedDerivationGeometry.fold_context_fields`. -/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol Internal Execution

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem nfold_h (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) st geometry rows).h = st.h := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { st with s := geometry.slot }).2.1

omit [Fintype V] in
private theorem nfold_J (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) st geometry rows).J = st.J := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { st with s := geometry.slot }).2.2.2.1

omit [Fintype V] in
private theorem nfold_h_j (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) st geometry rows).h_j = st.h_j := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { st with s := geometry.slot }).2.2.2.2.1

/-- Along one named parent edge the named justification height strictly
increases, or the exact named justification checkpoint is unchanged. -/
theorem namedJustification_strict_or_eq_of_parent
    (E : Env V) (cfg : HeightConfig)
    (parent : NamedBlock V) (slot : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V))
    (rows : List (NamedAttestation V)) (proposer : V) :
    (derive_named E cfg parent).h_j <
        (derive_named E cfg
          (.node parent slot root votes support rows proposer)).h_j ∨
      ((derive_named E cfg parent).h_j =
          (derive_named E cfg
            (.node parent slot root votes support rows proposer)).h_j ∧
        (derive_named E cfg parent).J =
          (derive_named E cfg
            (.node parent slot root votes support rows proposer)).J) := by
  let B := NamedBlock.node parent slot root votes support rows proposer
  let folded := fold_rows (TimeoutBinding.targeted V)
    (derive_named E cfg parent) B.erase rows
  rw [show derive_named E cfg B = process_height_events E cfg folded by rfl,
    Protocol.process_height_events_eq]
  split_ifs
  · left
    rw [Protocol.advance_height_h_j, Protocol.afterFin_h, nfold_h]
    exact (NamedDerivationGeometry.chainOrder_derive_named E cfg
      parent).justified_below_height
  · right
    constructor
    · rw [Protocol.advance_height_h_j, Protocol.afterFin_h_j, nfold_h_j]
    · rw [Protocol.advance_height_J, Protocol.afterFin_J, nfold_J]
  · right
    constructor
    · rw [Protocol.afterFin_h_j, nfold_h_j]
    · rw [Protocol.afterFin_J, nfold_J]

/-- Along named ancestry the named justification height strictly increases, or
the exact named `(height, checkpoint)` pair is retained. -/
theorem namedJustification_strict_or_eq_of_preceq
    (E : Env V) (cfg : HeightConfig) {A B : NamedBlock V}
    (hAB : NamedBlock.Preceq A B) :
    (derive_named E cfg A).h_j < (derive_named E cfg B).h_j ∨
      ((derive_named E cfg A).h_j = (derive_named E cfg B).h_j ∧
        (derive_named E cfg A).J = (derive_named E cfg B).J) := by
  induction B with
  | genesis =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
      subst A
      exact Or.inr ⟨rfl, rfl⟩
  | node p s r gv support ats i ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hAp
      · exact Or.inr ⟨rfl, rfl⟩
      · have hprefix := ih hAp
        have hedge := namedJustification_strict_or_eq_of_parent E cfg p s r gv
          support ats i
        rcases hprefix with hprefix | ⟨hhPrefix, hJPrefix⟩
        · rcases hedge with hedge | ⟨hhEdge, -⟩
          · exact Or.inl (hprefix.trans hedge)
          · exact Or.inl (hprefix.trans_eq hhEdge)
        · rcases hedge with hedge | ⟨hhEdge, hJEdge⟩
          · exact Or.inl (hhPrefix.trans_lt hedge)
          · exact Or.inr ⟨hhPrefix.trans hhEdge, hJPrefix.trans hJEdge⟩

/-- The `≤` form the finality step actually consumes. -/
theorem namedJustification_le_of_preceq
    (E : Env V) (cfg : HeightConfig) {A B : NamedBlock V}
    (hAB : NamedBlock.Preceq A B) :
    (derive_named E cfg A).h_j ≤ (derive_named E cfg B).h_j := by
  rcases namedJustification_strict_or_eq_of_preceq E cfg hAB with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

/-! ## Axiom roster. Every public theorem of this file. Each must report a
subset of `propext`, `Classical.choice`, `Quot.sound` and nothing else. A
theorem reporting NO axioms is hollow: it means an import's olean lacked a name
and Lean recovered silently, which still exits zero. -/

#print axioms namedJustification_strict_or_eq_of_parent
#print axioms namedJustification_strict_or_eq_of_preceq
#print axioms namedJustification_le_of_preceq


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
