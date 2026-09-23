module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.W4FKChainJustification

@[expose] public section

/-! # W4 branches fk-chain, part 5: the named checkpoint algebra

Two open items in the selection name the same absent block of lemmas:

* `CanonicalRegimeSecondCheckpointRun.lean:314-327`, whose parked
  `carrierFinalitySecondCheckpointAt_of_regime` reads the record guards at the
  justification height;
* `PostRecoveryLivenessFinalityRun.lean:362-379`, verbatim: "its own
  justification arithmetic (`derivedJustification_preceq_of_le_height`,
  `Protocol.chainOrder_derived_state`, `derived_h_le_succ_of_parent`) is the same
  erased checkpoint algebra that the named proposal `P1` has no twin for".

This file is that twin. earlier's three lemmas
(`derivedTarget_eq_justification_of_sameHeight`,
`derivedNj_false_at_justificationHeight`,
`derivedJustification_preceq_of_le_height`, all live in the selection at
`CanonicalRegimeSecondCheckpointRun.lean:119,143,168` but over `derived_state`)
each start from `Protocol.derived_justified_height`, which applies
`derived_state` to the state's own `J` field. Over `derive_named` that step
does not typecheck, so the induction below carries the justification witness as
an actual NAMED ancestor together with the two facts earlier reads off it: it is
its own height target, and its height segment is justifiable.

The branch analysis is the state machine. The target branch writes the parent's
entry, which `Proofs.NamedEntryHeight.entry_eq_on_plateau` makes its own target, and
whose latch equals the parent's — false, because `targetReady` tested it. Every
other branch retains the parent's justification.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Protocol (ChainState HeightConfig derive_named fold_rows
  process_attestation_with TimeoutBinding)

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- Two named ancestors of one named block are ordered: a named chain is a
list. Named twin of `preceq_or_preceq_of_common`
(`CanonicalRegimeSecondCheckpointRun.lean:110`). -/
theorem namedPreceq_or_preceq_of_common {A B C : NamedBlock V}
    (hA : NamedBlock.Preceq A C) (hB : NamedBlock.Preceq B C) :
    NamedBlock.Preceq A B ∨ NamedBlock.Preceq B A := by
  induction C with
  | genesis =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hA hB
      subst A
      subst B
      exact Or.inl (Proofs.NamedAncestry.named_self _)
  | node p s root gv gsv ats proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hA hB
      rcases hA with rfl | hAp
      · rcases hB with rfl | hBp
        · exact Or.inl (Proofs.NamedAncestry.named_self _)
        · exact Or.inr (Proofs.NamedAncestry.named_extend s root gv gsv ats proposer hBp)
      · rcases hB with rfl | hBp
        · exact Or.inl (Proofs.NamedAncestry.named_extend s root gv gsv ats proposer hAp)
        · exact ih hAp hBp

omit [Fintype V] in
private theorem w4caFold_nj
    (rows : List (NamedAttestation V)) (sigma : ChainState V) :
    (rows.foldl (process_attestation_with (TimeoutBinding.targeted V))
      sigma).nj = sigma.nj := by
  induction rows generalizing sigma with
  | nil => rfl
  | cons row rows ih =>
      rw [List.foldl_cons, ih]
      exact NjGap.process_attestation_nj sigma _

omit [Fintype V] in
private theorem w4caRows_nj (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).nj = sigma.nj := by
  unfold fold_rows
  exact w4caFold_nj rows { sigma with s := geometry.slot }

omit [Fintype V] in
private theorem w4caRows_h (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).h = sigma.h := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { sigma with s := geometry.slot }).2.1

omit [Fintype V] in
private theorem w4caRows_T_h (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).T_h = sigma.T_h := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { sigma with s := geometry.slot }).2.2.1

omit [Fintype V] in
private theorem w4caRows_J (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).J = sigma.J := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { sigma with s := geometry.slot }).2.2.2.1

omit [Fintype V] in
private theorem w4caRows_h_j (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).h_j = sigma.h_j := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { sigma with s := geometry.slot }).2.2.2.2.1

/-- The named justification is the erasure of an actual named ancestor that is
its own height target, sits in a justifiable height segment, and carries the
recorded justification height unless that height is still zero. Named twin of
`Protocol.derived_justified_height` together with
`derivedJustification_selfTarget` and `derivedJustification_nj_false`
(`CanonicalRegimeSecondCheckpointRun.lean:60,78`). -/
theorem namedJustificationWitness (E : Env V) (cfg : HeightConfig) (B : NamedBlock V) :
    ∃ J : NamedBlock V, NamedBlock.Preceq J B ∧
      J.erase = (derive_named E cfg B).J ∧
      (derive_named E cfg J).T_h = J.erase ∧
      (derive_named E cfg J).nj = false ∧
      ((derive_named E cfg B).h_j = 0 ∨
        (derive_named E cfg J).h = (derive_named E cfg B).h_j) := by
  induction B with
  | genesis =>
      exact ⟨.genesis, Proofs.NamedAncestry.named_self _, rfl, rfl, rfl, Or.inl rfl⟩
  | node p s root gv gsv ats proposer ih =>
      obtain ⟨JP, hJPle, hJPerase, hJPself, hJPnj, hJPheight⟩ := ih
      set tau := fold_rows (TimeoutBinding.targeted V) (derive_named E cfg p)
        (NamedBlock.node p s root gv gsv ats proposer).erase
        (NamedBlock.node p s root gv gsv ats proposer).attestations with htau
      have hderive : derive_named E cfg (.node p s root gv gsv ats proposer) =
          Protocol.process_height_events E cfg tau := rfl
      by_cases htarget : Protocol.targetReady E (Protocol.afterFin E tau) = true
      · obtain ⟨entry, hentryLe, hentryErase, hentryHeight⟩ :=
          Proofs.NamedEntryHeight.entry_ancestor_same_height E cfg p
        have hnjParent : (derive_named E cfg p).nj = false := by
          have hready := htarget
          simp only [Protocol.targetReady, Bool.and_eq_true] at hready
          have hnjAfter : (Protocol.afterFin E tau).nj = false := by
            simpa only [Bool.not_eq_true'] using hready.1
          rw [Protocol.afterFin_nj, w4caRows_nj] at hnjAfter
          exact hnjAfter
        refine ⟨entry, Proofs.NamedAncestry.named_extend s root gv gsv ats proposer hentryLe,
          ?_, ?_, ?_, ?_⟩
        · rw [hderive, Protocol.process_height_events_eq, if_pos htarget,
            Protocol.advance_height_J, Protocol.afterFin_T_h, w4caRows_T_h, hentryErase]
        · rw [Proofs.NamedEntryHeight.entry_eq_on_plateau E cfg hentryLe hentryHeight,
            hentryErase]
        · rw [namedNj_eq_of_preceq_same_height E cfg hentryLe hentryHeight.symm] at hnjParent
          exact hnjParent
        · right
          rw [hderive, Protocol.process_height_events_eq, if_pos htarget,
            Protocol.advance_height_h_j, Protocol.afterFin_h, w4caRows_h, hentryHeight]
      · have hJout : (derive_named E cfg (.node p s root gv gsv ats proposer)).J =
            (derive_named E cfg p).J := by
          rw [hderive, Protocol.process_height_events_eq, if_neg htarget]
          split_ifs
          · rw [Protocol.advance_height_J, Protocol.afterFin_J, w4caRows_J]
          · rw [Protocol.afterFin_J, w4caRows_J]
        have hHjout : (derive_named E cfg (.node p s root gv gsv ats proposer)).h_j =
            (derive_named E cfg p).h_j := by
          rw [hderive, Protocol.process_height_events_eq, if_neg htarget]
          split_ifs
          · rw [Protocol.advance_height_h_j, Protocol.afterFin_h_j, w4caRows_h_j]
          · rw [Protocol.afterFin_h_j, w4caRows_h_j]
        exact ⟨JP, Proofs.NamedAncestry.named_extend s root gv gsv ats proposer hJPle,
          by rw [hJPerase, hJout], hJPself, hJPnj, by rw [hHjout]; exact hJPheight⟩

/-- Named twin of `derivedTarget_eq_justification_of_sameHeight`
(`CanonicalRegimeSecondCheckpointRun.lean:119`): a named chain block at the
justification height carries the justification as its height target. -/
theorem namedTarget_eq_justification_of_sameHeight
    (E : Env V) (cfg : HeightConfig) {B Q : NamedBlock V}
    (hQB : NamedBlock.Preceq Q B)
    (hpos : 0 < (derive_named E cfg B).h_j)
    (hh : (derive_named E cfg Q).h = (derive_named E cfg B).h_j) :
    (derive_named E cfg Q).T_h = (derive_named E cfg B).J := by
  obtain ⟨J, hJB, hJerase, hJself, -, hJheight⟩ := namedJustificationWitness E cfg B
  rcases hJheight with hzero | hJheight
  · exact absurd hzero (Nat.ne_of_gt hpos)
  rcases namedPreceq_or_preceq_of_common hQB hJB with hQJ | hJQ
  · rw [Proofs.NamedEntryHeight.entry_eq_on_plateau E cfg hQJ (hh.trans hJheight.symm),
      hJself, hJerase]
  · rw [← Proofs.NamedEntryHeight.entry_eq_on_plateau E cfg hJQ (hJheight.trans hh.symm),
      hJself, hJerase]

/-- Named twin of `derivedNj_false_at_justificationHeight`
(`CanonicalRegimeSecondCheckpointRun.lean:143`): a named chain block at the
justification height is justifiable. -/
theorem namedNj_false_at_justificationHeight
    (E : Env V) (cfg : HeightConfig) {B Q : NamedBlock V}
    (hQB : NamedBlock.Preceq Q B)
    (hpos : 0 < (derive_named E cfg B).h_j)
    (hh : (derive_named E cfg Q).h = (derive_named E cfg B).h_j) :
    (derive_named E cfg Q).nj = false := by
  obtain ⟨J, hJB, -, -, hJnj, hJheight⟩ := namedJustificationWitness E cfg B
  rcases hJheight with hzero | hJheight
  · exact absurd hzero (Nat.ne_of_gt hpos)
  rcases namedPreceq_or_preceq_of_common hQB hJB with hQJ | hJQ
  · rw [← namedNj_eq_of_preceq_same_height E cfg hQJ (hJheight.trans hh.symm)]
    exact hJnj
  · rw [namedNj_eq_of_preceq_same_height E cfg hJQ (hh.trans hJheight.symm)]
    exact hJnj


#print axioms namedPreceq_or_preceq_of_common
#print axioms namedJustificationWitness

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
