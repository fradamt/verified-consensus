module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.CanonicalRegimeFromChain
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Protocol.ChainState.TargetedTimeoutBinding

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Protocol (ChainState HeightConfig derive_named fold_rows
  process_attestation_with TimeoutBinding)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. Finality bits through the targeted row fold -/

omit [Fintype V] in
/-- The targeted fold never removes a finality bit. -/
private theorem w4fwFold_finalize_subset
    (rows : List (NamedAttestation V)) (sigma : ChainState V) :
    sigma.finalize ⊆
      (rows.foldl (process_attestation_with (TimeoutBinding.targeted V))
        sigma).finalize := by
  induction rows generalizing sigma with
  | nil => exact Finset.Subset.refl _
  | cons row rows ih =>
      rw [List.foldl_cons]
      refine Finset.Subset.trans ?_ (ih _)
      intro i hi
      rw [TargetedTimeoutBinding.process_finality_eq sigma row,
        Protocol.process_attestation_finalize]
      split_ifs
      · exact Finset.mem_insert_of_mem hi
      · exact hi

omit [Fintype V] in
/-- An exact finality row for the state's own live checkpoint enters the fold's
finality set while the debt is positive. -/
private theorem w4fwFold_mem_finalize_of_finality
    {a : NamedAttestation V} :
    ∀ (rows : List (NamedAttestation V)) (sigma : ChainState V),
      a ∈ rows →
      sigma.h_F < sigma.h_j →
      a.finality_pair = some ⟨sigma.h_j, sigma.J.root⟩ →
      a.val_index ∈
        (rows.foldl (process_attestation_with (TimeoutBinding.targeted V))
          sigma).finalize := by
  intro rows
  induction rows with
  | nil => intro _ ha _ _; simp at ha
  | cons row rows ih =>
      intro sigma ha hlt hpair
      rw [List.foldl_cons]
      rcases List.mem_cons.mp ha with rfl | hmem
      · apply w4fwFold_finalize_subset
        rw [TargetedTimeoutBinding.process_finality_eq sigma a,
          Protocol.process_attestation_finalize]
        simp [hlt, hpair, NamedAttestation.erase]
      · apply ih _ hmem
        · have hfields := TimeoutBindingDefaults.process_context_fields
            (TimeoutBinding.targeted V) sigma row
          rw [hfields.2.2.2.2.1, hfields.2.2.2.2.2.2]
          exact hlt
        · have hfields := TimeoutBindingDefaults.process_context_fields
            (TimeoutBinding.targeted V) sigma row
          rw [hfields.2.2.2.2.1, hfields.2.2.2.1]
          exact hpair

omit [Fintype V] in
private theorem w4fwRows_h_j (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).h_j = sigma.h_j := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { sigma with s := geometry.slot }).2.2.2.2.1

omit [Fintype V] in
private theorem w4fwRows_J (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).J = sigma.J := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { sigma with s := geometry.slot }).2.2.2.1

omit [Fintype V] in
private theorem w4fwRows_h_F (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).h_F = sigma.h_F := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { sigma with s := geometry.slot }).2.2.2.2.2.2

omit [Fintype V] in
private theorem w4fwRows_finalize (sigma : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) sigma geometry rows).finalize =
      (rows.foldl (process_attestation_with (TimeoutBinding.targeted V))
        { sigma with s := geometry.slot }).finalize := rfl

/-! ## 2. Named finality coverage -/

/-- Named twin of `FinalityQuorumCoveredByChild` (`FinalityQuorumCore.lean:185`):
the checkpoint is named explicitly, and each quorum member is already in the
parent's finality set or carries an exact row for that same checkpoint among
the child's named rows. -/
def NamedFinalityQuorumCoveredByChild
    (E : Env V) (sigma : ChainState V) (B : NamedBlock V)
    (h_j : Height) (J : Block V) : Prop :=
  sigma.h_j = h_j ∧ sigma.J = J ∧
    ∃ Q : Finset V, E.electorate.IsQuorum Q ∧
      ∀ i ∈ Q,
        i ∈ sigma.finalize ∨
        ∃ a ∈ B.attestations,
          a.val_index = i ∧
          a.finality_pair = some ⟨h_j, J.root⟩

/-- Honest finality coverage is a named finality quorum under the fault
bound. -/
theorem namedFinalityQuorumCoveredByChild_of_honest
    (S : Setup V) {rho : Run V} (hfb : BelowOneThird S rho.honest)
    {sigma : ChainState V} {B : NamedBlock V} {h_j : Height} {J : Block V}
    (hhj : sigma.h_j = h_j) (hJ : sigma.J = J)
    (hcovered : ∀ i ∈ rho.honest,
      i ∈ sigma.finalize ∨
      ∃ a ∈ B.attestations,
        a.val_index = i ∧
        a.finality_pair = some ⟨h_j, J.root⟩) :
    NamedFinalityQuorumCoveredByChild S.E sigma B h_j J :=
  ⟨hhj, hJ, rho.honest,
    AlignedRoundLemmas.honestQuorum_of_belowOneThird hfb, hcovered⟩

/-- Positive debt and named finality coverage make the folded child
finality-ready at the preserved checkpoint. -/
theorem namedFinalityReady_of_covered
    (E : Env V) {sigma : ChainState V} {B : NamedBlock V}
    {h_j : Height} {J : Block V}
    (hcovered : NamedFinalityQuorumCoveredByChild E sigma B h_j J)
    (hlt : sigma.h_F < h_j) :
    Protocol.finalityReady E
      (fold_rows (TimeoutBinding.targeted V) sigma B.erase B.attestations) = true := by
  obtain ⟨hhj, hJ, Q, hQ, hcov⟩ := hcovered
  have hltSigma : sigma.h_F < sigma.h_j := by simpa only [hhj] using hlt
  have hquorumSet : E.electorate.IsQuorum
      (fold_rows (TimeoutBinding.targeted V) sigma B.erase B.attestations).finalize := by
    apply Protocol.isQuorum_of_subset hQ
    intro i hi
    rw [w4fwRows_finalize]
    rcases hcov i hi with hold | ⟨a, ha, hai, hpair⟩
    · exact w4fwFold_finalize_subset _ _ hold
    · rw [← hai]
      refine w4fwFold_mem_finalize_of_finality _ _ ha hltSigma ?_
      simpa only [hhj, hJ] using hpair
  have hquorum :
      (fold_rows (TimeoutBinding.targeted V) sigma B.erase
        B.attestations).finalityQuorum E = true := by
    simpa only [ChainState.finalityQuorum, ChainState.Q_finality,
      Electorate.quorumCheck, decide_eq_true_eq] using hquorumSet
  simp only [Protocol.finalityReady, Bool.and_eq_true]
  refine ⟨?_, hquorum⟩
  simp only [decide_eq_true_eq]
  rw [w4fwRows_h_F, w4fwRows_h_j, hhj]
  exact hlt

/-- Named twin of `finalizedAt_of_finalityQuorumCoveredByChild`
(`RecurringFinalityRun.lean:682`): live parent-or-child finality coverage
performs the actual named finality write. -/
theorem namedFinalizedAt_of_finalityQuorumCoveredByChild
    (E : Env V) (cfg : HeightConfig) {B : NamedBlock V} {J : Block V} {h : Height}
    (hBne : B ≠ NamedBlock.genesis)
    (hcovered : NamedFinalityQuorumCoveredByChild E (derive_named E cfg B.parent) B h J)
    (hdebt : (derive_named E cfg B.parent).h_F < h) :
    NamedFinalizedAt E cfg B J h := by
  cases B with
  | genesis => exact (hBne rfl).elim
  | node p s root gv gsv ats proposer =>
      have hready := namedFinalityReady_of_covered E hcovered hdebt
      have hderive : derive_named E cfg (.node p s root gv gsv ats proposer) =
          Protocol.process_height_events E cfg
            (fold_rows (TimeoutBinding.targeted V) (derive_named E cfg p)
              (NamedBlock.node p s root gv gsv ats proposer).erase
              (NamedBlock.node p s root gv gsv ats proposer).attestations) := rfl
      have hwrite := process_height_events_actual_F E cfg
        (fold_rows (TimeoutBinding.targeted V) (derive_named E cfg p)
          (NamedBlock.node p s root gv gsv ats proposer).erase
          (NamedBlock.node p s root gv gsv ats proposer).attestations) hready
      obtain ⟨hhj, hJ, -⟩ := hcovered
      refine ⟨?_, ?_⟩
      · rw [hderive, hwrite.1, w4fwRows_J]
        exact hJ
      · rw [hderive, hwrite.2, w4fwRows_h_j]
        exact hhj

/-! ## 3. Exact honest action rows perform the write -/

/-- Named twin of `finalizedAt_of_actionRows` (`RecurringFinalityRun.lean:904`):
a selected proposal performs the exact named finality write once every honest
first-action row is live in its parent or carried in its own rows. The coverage
premise is verbatim the `secondRowsCoveredAtPlusTwo` field of
`RecurringFinalityPhaseAt` (`RecurringFinalityRun.lean:149-153`). -/
theorem namedFinalizedAt_of_actionRows
    (S : Setup V) {rho : Run V} (hbot : BelowOneThird S rho.honest)
    {r : Round} {s : Slot} {hJ : Height} {TJ : BlockId} {J : Block V}
    {B : NamedBlock V}
    (hB : proposedBlockAt S rho s = some B)
    (hcoverage : ∀ v ∈ rho.honest,
      let a := actionAttestationAt S rho v r
      (a ∈ Protocol.named_chain_attestations B.parent ∧
          v ∈ (derive_named S.E S.cfg B.parent).finalize) ∨
        a ∈ B.attestations)
    (hparentHJ : (derive_named S.E S.cfg B.parent).h_j = hJ)
    (hparentJ : (derive_named S.E S.cfg B.parent).J = J)
    (hroot : J.root = TJ)
    (hdebt : (derive_named S.E S.cfg B.parent).h_F < hJ)
    (hfinality : ∀ v ∈ rho.honest,
      (actionAttestationAt S rho v r).finality_pair = some ⟨hJ, TJ⟩) :
    NamedFinalizedAt S.E S.cfg B J hJ := by
  have hne : B ≠ NamedBlock.genesis := by
    obtain ⟨p, hp, -⟩ := proposedBlockAt_parent S rho s hB
    intro hgen
    rw [hgen] at hp
    cases hp
  refine namedFinalizedAt_of_finalityQuorumCoveredByChild S.E S.cfg hne ?_ hdebt
  refine namedFinalityQuorumCoveredByChild_of_honest S hbot hparentHJ hparentJ ?_
  intro v hv
  have hcovered := hcoverage v hv
  dsimp only at hcovered
  rcases hcovered with hparent | hchild
  · exact Or.inl hparent.2
  · refine Or.inr ⟨actionAttestationAt S rho v r, hchild,
      (actionAttestationAt_shape S rho v r).1, ?_⟩
    rw [hfinality v hv, hroot]

#print axioms namedFinalityQuorumCoveredByChild_of_honest
#print axioms namedFinalityReady_of_covered
#print axioms namedFinalizedAt_of_finalityQuorumCoveredByChild
#print axioms namedFinalizedAt_of_actionRows

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
