module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Protocol.Handlers.BlockProcessingDefaults

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # W4 branches fk-chain, part 4: named justification and finality witnesses

`Internal.CommonFinalizedWitnessAt` (`DecoupledConsensusInternal/LocalFinality.lean:25`)
asks for the finalized checkpoint as a NAMED run block whose own named height is
the finalized height. earlier reads both facts off `Protocol.derived_justified_height`
and `Protocol.derived_finalized_height`, which apply `derived_state` to the
chain state's own `J`/`F` field — an erased block. That step is not available
over `derive_named`: the named derivation is a function of named bodies, and
`(derive_named E cfg B).J` is a bare `Block V`.

This file supplies the named replacement, in the shape
`Proofs.NamedEntryHeight.entry_ancestor_same_height` uses for the entry `T_h`: the
checkpoint fields are erasures of actual NAMED ancestors, and each carries the
recorded height unless the field is still at its genesis value. The induction is
the state machine itself — the target branch writes the parent's entry, the
finality branch writes the parent's justification, and every other branch
retains — so nothing here is a protocol claim.

The corollaries are the two facts the finality kernel consumes: a positive named
justification or finalization height is the named height of an actual named
ancestor, and a finalized checkpoint above height one is not genesis.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Protocol (ChainState HeightConfig derive_named fold_rows
  process_attestation_with TimeoutBinding)

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem w4clNamedExtend {A parent : NamedBlock V} (s : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V)) (rows : List (NamedAttestation V))
    (proposer : V) (h : NamedBlock.Preceq A parent) :
    NamedBlock.Preceq A (.node parent s root votes support rows proposer) :=
  Proofs.NamedAncestry.named_extend s root votes support rows proposer h

/-- The named checkpoint fields are erasures of actual named ancestors, each at
its recorded height unless the field is still the genesis default. -/
theorem namedCheckpointAncestors (E : Env V) (cfg : HeightConfig) (B : NamedBlock V) :
    (∃ J : NamedBlock V, NamedBlock.Preceq J B ∧
        J.erase = (derive_named E cfg B).J ∧
        ((derive_named E cfg B).h_j = 0 ∨
          (derive_named E cfg J).h = (derive_named E cfg B).h_j)) ∧
      (∃ F : NamedBlock V, NamedBlock.Preceq F B ∧
        F.erase = (derive_named E cfg B).F ∧
        ((derive_named E cfg B).h_F = 0 ∨
          (derive_named E cfg F).h = (derive_named E cfg B).h_F)) := by
  induction B with
  | genesis =>
      exact ⟨⟨.genesis, Proofs.NamedAncestry.named_self _, rfl, Or.inl rfl⟩,
        ⟨.genesis, Proofs.NamedAncestry.named_self _, rfl, Or.inl rfl⟩⟩
  | node p s root gv gsv ats proposer ih =>
      obtain ⟨⟨JP, hJPle, hJPerase, hJPheight⟩, ⟨FP, hFPle, hFPerase, hFPheight⟩⟩ := ih
      set tau := fold_rows (TimeoutBinding.targeted V) (derive_named E cfg p)
        (NamedBlock.node p s root gv gsv ats proposer).erase
        (NamedBlock.node p s root gv gsv ats proposer).attestations with htau
      have hderive : derive_named E cfg (.node p s root gv gsv ats proposer) =
          Protocol.process_height_events E cfg tau := rfl
      have hfields := NamedDerivationGeometry.fold_context_fields
        (TimeoutBinding.targeted V)
        (NamedBlock.node p s root gv gsv ats proposer).attestations
        { derive_named E cfg p with
          s := (NamedBlock.node p s root gv gsv ats proposer).erase.slot }
      have htauH : tau.h = (derive_named E cfg p).h := hfields.2.1
      have htauT : tau.T_h = (derive_named E cfg p).T_h := hfields.2.2.1
      have htauJ : tau.J = (derive_named E cfg p).J := hfields.2.2.2.1
      have htauHj : tau.h_j = (derive_named E cfg p).h_j := hfields.2.2.2.2.1
      have htauF : tau.F = (derive_named E cfg p).F := hfields.2.2.2.2.2.1
      have htauHF : tau.h_F = (derive_named E cfg p).h_F := hfields.2.2.2.2.2.2
      obtain ⟨entry, hentryLe, hentryErase, hentryHeight⟩ :=
        Proofs.NamedEntryHeight.entry_ancestor_same_height E cfg p
      -- the finality branch first: `afterFin` writes the parent's justification
      by_cases hfin : Protocol.finalityReady E tau = true
      · have hafterF : (Protocol.afterFin E tau).F = tau.J := by
          rw [Protocol.afterFin_F, if_pos hfin]
        have hafterHF : (Protocol.afterFin E tau).h_F = tau.h_j := by
          rw [Protocol.afterFin_h_F, if_pos hfin]
        have hFout : (derive_named E cfg (.node p s root gv gsv ats proposer)).F =
            (derive_named E cfg p).J := by
          rw [hderive, Protocol.process_height_events_F, hafterF, htauJ]
        have hHFout : (derive_named E cfg (.node p s root gv gsv ats proposer)).h_F =
            (derive_named E cfg p).h_j := by
          rw [hderive, Protocol.process_height_events_h_F, hafterHF, htauHj]
        refine ⟨?_, ⟨JP, w4clNamedExtend s root gv gsv ats proposer hJPle,
          by rw [hJPerase, hFout], ?_⟩⟩
        · by_cases htarget :
              Protocol.targetReady E (Protocol.afterFin E tau) = true
          · refine ⟨entry, w4clNamedExtend s root gv gsv ats proposer hentryLe, ?_, ?_⟩
            · rw [hderive, Protocol.process_height_events_eq, if_pos htarget,
                Protocol.advance_height_J, Protocol.afterFin_T_h, htauT, hentryErase]
            · right
              rw [hderive, Protocol.process_height_events_eq, if_pos htarget,
                Protocol.advance_height_h_j, Protocol.afterFin_h, htauH, hentryHeight]
          · refine ⟨JP, w4clNamedExtend s root gv gsv ats proposer hJPle, ?_, ?_⟩
            · rw [hderive, Protocol.process_height_events_eq, if_neg htarget]
              split_ifs
              · rw [Protocol.advance_height_J, Protocol.afterFin_J, htauJ, hJPerase]
              · rw [Protocol.afterFin_J, htauJ, hJPerase]
            · have hsame : (derive_named E cfg
                  (.node p s root gv gsv ats proposer)).h_j =
                  (derive_named E cfg p).h_j := by
                rw [hderive, Protocol.process_height_events_eq, if_neg htarget]
                split_ifs
                · rw [Protocol.advance_height_h_j, Protocol.afterFin_h_j, htauHj]
                · rw [Protocol.afterFin_h_j, htauHj]
              rw [hsame]
              exact hJPheight
        · rw [hHFout]
          exact hJPheight
      · have hnot : ¬ Protocol.finalityReady E tau = true := hfin
        have hafterF : (Protocol.afterFin E tau).F = tau.F := by
          rw [Protocol.afterFin_F, if_neg hnot]
        have hafterHF : (Protocol.afterFin E tau).h_F = tau.h_F := by
          rw [Protocol.afterFin_h_F, if_neg hnot]
        have hFout : (derive_named E cfg (.node p s root gv gsv ats proposer)).F =
            (derive_named E cfg p).F := by
          rw [hderive, Protocol.process_height_events_F, hafterF, htauF]
        have hHFout : (derive_named E cfg (.node p s root gv gsv ats proposer)).h_F =
            (derive_named E cfg p).h_F := by
          rw [hderive, Protocol.process_height_events_h_F, hafterHF, htauHF]
        refine ⟨?_, ⟨FP, w4clNamedExtend s root gv gsv ats proposer hFPle,
          by rw [hFPerase, hFout], by rw [hHFout]; exact hFPheight⟩⟩
        by_cases htarget :
            Protocol.targetReady E (Protocol.afterFin E tau) = true
        · refine ⟨entry, w4clNamedExtend s root gv gsv ats proposer hentryLe, ?_, ?_⟩
          · rw [hderive, Protocol.process_height_events_eq, if_pos htarget,
              Protocol.advance_height_J, Protocol.afterFin_T_h, htauT, hentryErase]
          · right
            rw [hderive, Protocol.process_height_events_eq, if_pos htarget,
              Protocol.advance_height_h_j, Protocol.afterFin_h, htauH, hentryHeight]
        · refine ⟨JP, w4clNamedExtend s root gv gsv ats proposer hJPle, ?_, ?_⟩
          · rw [hderive, Protocol.process_height_events_eq, if_neg htarget]
            split_ifs
            · rw [Protocol.advance_height_J, Protocol.afterFin_J, htauJ, hJPerase]
            · rw [Protocol.afterFin_J, htauJ, hJPerase]
          · have hsame : (derive_named E cfg
                (.node p s root gv gsv ats proposer)).h_j =
                (derive_named E cfg p).h_j := by
              rw [hderive, Protocol.process_height_events_eq, if_neg htarget]
              split_ifs
              · rw [Protocol.advance_height_h_j, Protocol.afterFin_h_j, htauHj]
              · rw [Protocol.afterFin_h_j, htauHj]
            rw [hsame]
            exact hJPheight


/-- Named twin of `Protocol.derived_finalized_height`. -/
theorem namedFinalized_witness (E : Env V) (cfg : HeightConfig)
    (B : NamedBlock V) (hpos : 0 < (derive_named E cfg B).h_F) :
    ∃ F : NamedBlock V, NamedBlock.Preceq F B ∧
      F.erase = (derive_named E cfg B).F ∧
      (derive_named E cfg F).h = (derive_named E cfg B).h_F := by
  obtain ⟨-, ⟨F, hle, herase, hheight⟩⟩ := namedCheckpointAncestors E cfg B
  rcases hheight with hzero | hheight
  · exact absurd hzero (Nat.ne_of_gt hpos)
  · exact ⟨F, hle, herase, hheight⟩

/-- Named twin of `derived_height_eq_of_finalizedAt` together with the witness
`CommonFinalizedWitnessAt` asks for: the finalized checkpoint of a named block
is the erasure of a named ancestor whose own named height is the finalized
height. -/
theorem namedCheckpoint_of_namedFinalizedAt
    (E : Env V) (cfg : HeightConfig) {B : NamedBlock V} {T : Block V} {h : Height}
    (hcheckpoint : NamedFinalizedAt E cfg B T h) (hpos : 0 < h) :
    ∃ checkpoint : NamedBlock V, NamedBlock.Preceq checkpoint B ∧
      checkpoint.erase = T ∧ (derive_named E cfg checkpoint).h = h := by
  obtain ⟨F, hle, herase, hheight⟩ :=
    namedFinalized_witness E cfg B (by rw [hcheckpoint.2]; exact hpos)
  exact ⟨F, hle, by rw [herase, hcheckpoint.1], by rw [hheight, hcheckpoint.2]⟩

/-- Named twin of `finalizedCheckpoint_ne_genesis`
(`RecurringFinalityRun.lean:944`): a finalized checkpoint above height one is
not genesis. -/
theorem namedFinalizedCheckpoint_ne_genesis
    (E : Env V) (cfg : HeightConfig) {B : NamedBlock V} {T : Block V} {h : Height}
    (hcheckpoint : NamedFinalizedAt E cfg B T h) (hone : 1 < h) :
    T ≠ Block.genesis := by
  obtain ⟨checkpoint, -, herase, hheight⟩ :=
    namedCheckpoint_of_namedFinalizedAt E cfg hcheckpoint (Nat.zero_lt_of_lt hone)
  intro hgen
  rw [hgen] at herase
  have hcp : checkpoint = NamedBlock.genesis := by
    cases checkpoint with
    | genesis => rfl
    | node p s root gv gsv ats proposer =>
        simp only [NamedBlock.erase, reduceCtorEq] at herase
  rw [hcp] at hheight
  have hgenHeight : (derive_named E cfg (NamedBlock.genesis : NamedBlock V)).h = 1 := rfl
  rw [hgenHeight] at hheight
  exact (Nat.ne_of_lt hone) hheight

#print axioms namedCheckpointAncestors
#print axioms namedFinalized_witness
#print axioms namedCheckpoint_of_namedFinalizedAt
#print axioms namedFinalizedCheckpoint_ne_genesis

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
