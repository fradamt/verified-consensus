module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight

@[expose] public section

/-! # Named checkpoint heights 

`Protocol.derived_justified_height` and `Protocol.derived_finalized_height` say
that a chain state's justified and finalized blocks carry state heights `h_j`
and `h_F`. Both recompute a derived state on an *erased* block, which 
1636 retires: the erased derivation and `derive_named` agree only on
timeout-free chains.

The named forms below say the same thing without that recomputation. The
checkpoint is produced as a full named ancestor of the block, the way
`Proofs.NamedEntryHeight.entry_ancestor_same_height` produces the height entry, and
the height is read on that ancestor's own named derivation. The justification
case is that entry lemma one step on: `process_height_events` writes
`J ← T_h, h_j ← h`, so the justification witness IS the height entry of the
parent. The finalization case is the justification case one step on again,
because the finality branch writes `F ← J, h_F ← h_j`.
-/



namespace DecoupledConsensusModel.Proofs.NamedCheckpointHeights
open Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem named_extend {A parent : NamedBlock V} (s : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V)) (rows : List (NamedAttestation V)) (proposer : V)
    (h : NamedBlock.Preceq A parent) :
    NamedBlock.Preceq A (.node parent s root votes support rows proposer) := by
  simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
  exact Or.inr h

omit [Fintype V] in
private theorem fold_J (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) st geometry rows).J = st.J :=
  (NamedDerivationGeometry.fold_context_fields (TimeoutBinding.targeted V) rows
    { st with s := geometry.slot }).2.2.2.1

omit [Fintype V] in
private theorem fold_h_j (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) st geometry rows).h_j = st.h_j :=
  (NamedDerivationGeometry.fold_context_fields (TimeoutBinding.targeted V) rows
    { st with s := geometry.slot }).2.2.2.2.1

omit [Fintype V] in
private theorem fold_F (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) st geometry rows).F = st.F :=
  (NamedDerivationGeometry.fold_context_fields (TimeoutBinding.targeted V) rows
    { st with s := geometry.slot }).2.2.2.2.2.1

omit [Fintype V] in
private theorem fold_h_F (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) st geometry rows).h_F = st.h_F :=
  (NamedDerivationGeometry.fold_context_fields (TimeoutBinding.targeted V) rows
    { st with s := geometry.slot }).2.2.2.2.2.2

omit [Fintype V] in
private theorem fold_h (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) st geometry rows).h = st.h :=
  (NamedDerivationGeometry.fold_context_fields (TimeoutBinding.targeted V) rows
    { st with s := geometry.slot }).2.1

omit [Fintype V] in
private theorem fold_T_h (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) st geometry rows).T_h = st.T_h :=
  (NamedDerivationGeometry.fold_context_fields (TimeoutBinding.targeted V) rows
    { st with s := geometry.slot }).2.2.1


/-- The named justification carries the state height of a full named ancestor.
This is the -1636 form of `Protocol.derived_justified_height`. -/
theorem justified_ancestor_height (E : Env V) (cfg : HeightConfig) (B : NamedBlock V) :
    (derive_named E cfg B).h_j = 0 ∨
      ∃ J : NamedBlock V, NamedBlock.Preceq J B ∧
        J.erase = (derive_named E cfg B).J ∧
        (derive_named E cfg J).h = (derive_named E cfg B).h_j := by
  induction B with
  | genesis => exact Or.inl rfl
  | node parent s root votes support rows proposer ih =>
    have hstate : derive_named E cfg (.node parent s root votes support rows proposer) =
        process_height_events E cfg (fold_rows (TimeoutBinding.targeted V)
          (derive_named E cfg parent)
          (NamedBlock.node parent s root votes support rows proposer).erase
          (NamedBlock.node parent s root votes support rows proposer).attestations) := rfl
    rw [hstate, Protocol.process_height_events_eq]
    split_ifs
    · right
      obtain ⟨entry, hentry, herase, hheight⟩ :=
        Proofs.NamedEntryHeight.entry_ancestor_same_height E cfg parent
      refine ⟨entry, named_extend s root votes support rows proposer hentry, ?_, ?_⟩
      · rw [Protocol.advance_height_J]
        change entry.erase = (Protocol.afterFin E _).T_h
        rw [Protocol.afterFin_T_h, fold_T_h]
        exact herase
      · rw [Protocol.advance_height_h_j]
        change (derive_named E cfg entry).h = (Protocol.afterFin E _).h
        rw [Protocol.afterFin_h, fold_h]
        exact hheight
    · rcases ih with hz | ⟨J, hJ, herase, hheight⟩
      · left
        rw [Protocol.advance_height_h_j, Protocol.afterFin_h_j, fold_h_j]
        exact hz
      · right
        refine ⟨J, named_extend s root votes support rows proposer hJ, ?_, ?_⟩
        · rw [Protocol.advance_height_J, Protocol.afterFin_J, fold_J]
          exact herase
        · rw [Protocol.advance_height_h_j, Protocol.afterFin_h_j, fold_h_j]
          exact hheight
    · rcases ih with hz | ⟨J, hJ, herase, hheight⟩
      · left
        rw [Protocol.afterFin_h_j, fold_h_j]
        exact hz
      · right
        refine ⟨J, named_extend s root votes support rows proposer hJ, ?_, ?_⟩
        · rw [Protocol.afterFin_J, fold_J]
          exact herase
        · rw [Protocol.afterFin_h_j, fold_h_j]
          exact hheight


/-- The named finalization carries the state height of a full named ancestor.
This is the -1636 form of `Protocol.derived_finalized_height`. -/
theorem finalized_ancestor_height (E : Env V) (cfg : HeightConfig) (B : NamedBlock V) :
    (derive_named E cfg B).h_F = 0 ∨
      ∃ F : NamedBlock V, NamedBlock.Preceq F B ∧
        F.erase = (derive_named E cfg B).F ∧
        (derive_named E cfg F).h = (derive_named E cfg B).h_F := by
  induction B with
  | genesis => exact Or.inl rfl
  | node parent s root votes support rows proposer ih =>
    have hstate : derive_named E cfg (.node parent s root votes support rows proposer) =
        process_height_events E cfg (fold_rows (TimeoutBinding.targeted V)
          (derive_named E cfg parent)
          (NamedBlock.node parent s root votes support rows proposer).erase
          (NamedBlock.node parent s root votes support rows proposer).attestations) := rfl
    have hafter : (Protocol.afterFin E (fold_rows (TimeoutBinding.targeted V)
          (derive_named E cfg parent)
          (NamedBlock.node parent s root votes support rows proposer).erase
          (NamedBlock.node parent s root votes support rows proposer).attestations)).h_F = 0 ∨
        ∃ F : NamedBlock V,
          NamedBlock.Preceq F (.node parent s root votes support rows proposer) ∧
          F.erase = (Protocol.afterFin E (fold_rows (TimeoutBinding.targeted V)
            (derive_named E cfg parent)
            (NamedBlock.node parent s root votes support rows proposer).erase
            (NamedBlock.node parent s root votes support rows proposer).attestations)).F ∧
          (derive_named E cfg F).h = (Protocol.afterFin E (fold_rows (TimeoutBinding.targeted V)
            (derive_named E cfg parent)
            (NamedBlock.node parent s root votes support rows proposer).erase
            (NamedBlock.node parent s root votes support rows proposer).attestations)).h_F := by
      rw [Protocol.afterFin_F, Protocol.afterFin_h_F]
      split_ifs
      · rcases justified_ancestor_height E cfg parent with hz | ⟨J, hJ, herase, hheight⟩
        · left
          rw [fold_h_j]
          exact hz
        · right
          refine ⟨J, named_extend s root votes support rows proposer hJ, ?_, ?_⟩
          · rw [fold_J]
            exact herase
          · rw [fold_h_j]
            exact hheight
      · rcases ih with hz | ⟨F, hF, herase, hheight⟩
        · left
          rw [fold_h_F]
          exact hz
        · right
          refine ⟨F, named_extend s root votes support rows proposer hF, ?_, ?_⟩
          · rw [fold_F]
            exact herase
          · rw [fold_h_F]
            exact hheight
    rw [hstate, Protocol.process_height_events_eq]
    split_ifs <;> exact hafter

#print axioms justified_ancestor_height
#print axioms finalized_ancestor_height

end DecoupledConsensusModel.Proofs.NamedCheckpointHeights

end
