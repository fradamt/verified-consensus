module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.CarrierTimeoutGate
public import DecoupledConsensusProofs.Protocol.ChainState.CheckpointHeights
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Protocol.ChainState.JustificationCertificates

@[expose] public section

/-!
# Named checkpoint algebra

This module is the named counterpart of the small checkpoint algebra used by
the erased carrier and finality proofs. Every checkpoint witness below is a
`NamedBlock`; its height is read from `derive_named` on that witness. No
`derive_named` application is made to an erased checkpoint.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace NamedCheckpointAlgebra

open Protocol
open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem named_self (B : NamedBlock V) : NamedBlock.Preceq B B := by
  cases B <;> simp [NamedBlock.Preceq, NamedBlock.preceq]

omit [Fintype V] in
private theorem named_extend {A parent : NamedBlock V} (s : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V)) (rows : List (NamedAttestation V))
    (proposer : V) (h : NamedBlock.Preceq A parent) :
    NamedBlock.Preceq A (.node parent s root votes support rows proposer) := by
  simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
  exact Or.inr h



omit [Fintype V] in
private theorem named_fold_nj (rows : List (NamedAttestation V))
    (st : ChainState V) :
    (rows.foldl (process_attestation_with (TimeoutBinding.targeted V)) st).nj = st.nj := by
  induction rows generalizing st with
  | nil => rfl
  | cons row rows ih =>
      rw [List.foldl_cons, ih]
      unfold process_attestation_with process_attestation
      split_ifs <;> rfl

omit [Fintype V] in
private theorem named_fold_s (rows : List (NamedAttestation V))
    (st : ChainState V) (geometry : Block V) :
    (fold_rows (TimeoutBinding.targeted V) st geometry rows).s = geometry.slot := by
  have hrow : ∀ (st : ChainState V) (row : NamedAttestation V),
      (process_attestation_with (TimeoutBinding.targeted V) st row).s = st.s := by
    intro st row
    unfold process_attestation_with process_attestation
    split_ifs <;> rfl
  have hfold : ∀ (rows : List (NamedAttestation V)) (st : ChainState V),
      (rows.foldl (process_attestation_with (TimeoutBinding.targeted V)) st).s = st.s := by
    intro rows
    induction rows with
    | nil => intro st; rfl
    | cons row rows ih =>
        intro st
        rw [List.foldl_cons, ih, hrow]
  unfold fold_rows
  exact hfold rows { st with s := geometry.slot }

omit [Fintype V] in
private theorem fold_h (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) st geometry rows).h = st.h := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { st with s := geometry.slot }).2.1

omit [Fintype V] in
private theorem fold_T_h (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) st geometry rows).T_h = st.T_h := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { st with s := geometry.slot }).2.2.1

omit [Fintype V] in
private theorem fold_J (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) st geometry rows).J = st.J := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { st with s := geometry.slot }).2.2.2.1

omit [Fintype V] in
private theorem fold_h_j (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) st geometry rows).h_j = st.h_j := by
  unfold fold_rows
  exact (NamedDerivationGeometry.fold_context_fields
    (TimeoutBinding.targeted V) rows { st with s := geometry.slot }).2.2.2.2.1

omit [Fintype V] in
private theorem fold_nj (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) st geometry rows).nj = st.nj := by
  unfold fold_rows
  exact named_fold_nj rows { st with s := geometry.slot }

omit [Fintype V] in
private theorem fold_s (st : ChainState V) (geometry : Block V)
    (rows : List (NamedAttestation V)) :
    (fold_rows (TimeoutBinding.targeted V) st geometry rows).s = geometry.slot :=
  named_fold_s rows st geometry

private theorem afterFin_s (E : Env V) (st : ChainState V) :
    (Protocol.afterFin E st).s = st.s := by
  unfold Protocol.afterFin
  split_ifs <;> rfl


private theorem named_node_nj_eq_of_height_eq
    (E : Env V) (cfg : HeightConfig) (parent : NamedBlock V)
    (slot : Slot) (root : BlockId) (votes support : List (GoldfishVote V))
    (rows : List (NamedAttestation V)) (proposer : V)
    (hh : (derive_named E cfg
        (.node parent slot root votes support rows proposer)).h =
      (derive_named E cfg parent).h) :
    (derive_named E cfg
        (.node parent slot root votes support rows proposer)).nj =
    (derive_named E cfg parent).nj := by
  change (process_height_events E cfg
      (fold_rows (TimeoutBinding.targeted V) (derive_named E cfg parent)
        (NamedBlock.node parent slot root votes support rows proposer).erase rows)).h =
    (derive_named E cfg parent).h at hh
  change (process_height_events E cfg
      (fold_rows (TimeoutBinding.targeted V) (derive_named E cfg parent)
        (NamedBlock.node parent slot root votes support rows proposer).erase rows)).nj =
    (derive_named E cfg parent).nj
  rw [Protocol.process_height_events_eq] at hh ⊢
  split_ifs with htarget hprogress
  · have hh' := hh
    rw [if_pos htarget] at hh'
    rw [Protocol.advance_height_h, Protocol.afterFin_h,
      fold_h (derive_named E cfg parent)
        (NamedBlock.node parent slot root votes support rows proposer).erase rows] at hh'
    exact False.elim ((Nat.ne_of_lt (Nat.lt_succ_self _)) hh'.symm)
  · have hh' := hh
    rw [if_neg htarget, if_pos hprogress] at hh'
    rw [Protocol.advance_height_h, Protocol.afterFin_h,
      fold_h (derive_named E cfg parent)
        (NamedBlock.node parent slot root votes support rows proposer).erase rows] at hh'
    exact False.elim ((Nat.ne_of_lt (Nat.lt_succ_self _)) hh'.symm)
  · rw [Protocol.afterFin_nj]
    exact fold_nj (derive_named E cfg parent)
      (NamedBlock.node parent slot root votes support rows proposer).erase rows

/-- Same-height named ancestors have the same `nj` bit. -/
theorem namedNj_eq_of_preceq_sameHeight
    (E : Env V) (cfg : HeightConfig) {A B : NamedBlock V}
    (hAB : NamedBlock.Preceq A B)
    (hh : (derive_named E cfg B).h = (derive_named E cfg A).h) :
    (derive_named E cfg B).nj = (derive_named E cfg A).nj := by
  induction B generalizing A with
  | genesis =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
      subst A
      rfl
  | node parent slot root votes support rows proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hA
      · rfl
      · have hparentLe : (derive_named E cfg A).h ≤
            (derive_named E cfg parent).h :=
          Proofs.NamedEntryHeight.derive_height_mono E cfg hA
        have hnodeLe : (derive_named E cfg parent).h ≤
            (derive_named E cfg
              (.node parent slot root votes support rows proposer)).h :=
          Proofs.NamedEntryHeight.derive_height_mono E cfg
            (named_extend slot root votes support rows proposer (named_self parent))
        have hparentEq : (derive_named E cfg parent).h =
            (derive_named E cfg A).h := by
          have hAparent : (derive_named E cfg A).h =
              (derive_named E cfg parent).h := by
            apply Nat.le_antisymm
            · exact hparentLe
            · exact hnodeLe.trans_eq hh
          exact hAparent.symm
        have hnodeEq : (derive_named E cfg
              (.node parent slot root votes support rows proposer)).h =
            (derive_named E cfg parent).h := hh.trans hparentEq.symm
        exact (named_node_nj_eq_of_height_eq E cfg parent slot root votes support
          rows proposer hnodeEq).trans (ih hA hparentEq)

private theorem named_justification_data
    (E : Env V) (cfg : HeightConfig) (B : NamedBlock V) :
    (derive_named E cfg B).h_j = 0 ∨
      ∃ J : NamedBlock V, NamedBlock.Preceq J B ∧
        J.erase = (derive_named E cfg B).J ∧
        (derive_named E cfg J).h = (derive_named E cfg B).h_j ∧
        (derive_named E cfg J).T_h = J.erase ∧
        (derive_named E cfg J).nj = false := by
  induction B with
  | genesis => exact Or.inl rfl
  | node parent slot root votes support rows proposer ih =>
      let B := NamedBlock.node parent slot root votes support rows proposer
      let folded := fold_rows (TimeoutBinding.targeted V)
        (derive_named E cfg parent) B.erase rows
      rw [show derive_named E cfg B = process_height_events E cfg folded by rfl,
        Protocol.process_height_events_eq]
      split_ifs with htarget hprogress
      · have hparentNj : (derive_named E cfg parent).nj = false := by
          have hguard := htarget
          simp only [targetReady, Bool.and_eq_true, Bool.not_eq_true'] at hguard
          rw [Protocol.afterFin_nj, fold_nj] at hguard
          exact hguard.1
        obtain ⟨entry, hentry, herase, hheight⟩ :=
          Proofs.NamedEntryHeight.entry_ancestor_same_height E cfg parent
        have hself : (derive_named E cfg entry).T_h = entry.erase := by
          exact (Proofs.NamedEntryHeight.entry_eq_on_plateau E cfg hentry hheight).trans
            herase.symm
        have hnj : (derive_named E cfg entry).nj = false := by
          exact (namedNj_eq_of_preceq_sameHeight E cfg hentry hheight.symm).symm.trans
            hparentNj
        refine Or.inr ⟨entry,
          named_extend slot root votes support rows proposer hentry, ?_, ?_, hself, hnj⟩
        · rw [Protocol.advance_height_J, Protocol.afterFin_T_h,
            fold_T_h]
          exact herase
        · rw [Protocol.advance_height_h_j, Protocol.afterFin_h, fold_h]
          exact hheight
      · rcases ih with hz | ⟨J, hJ, herase, hheight, hself, hnj⟩
        · left
          rw [Protocol.advance_height_h_j, Protocol.afterFin_h_j, fold_h_j]
          exact hz
        · right
          refine ⟨J, named_extend slot root votes support rows proposer hJ, ?_, ?_, hself, hnj⟩
          · rw [Protocol.advance_height_J, Protocol.afterFin_J, fold_J]
            exact herase
          · rw [Protocol.advance_height_h_j, Protocol.afterFin_h_j, fold_h_j]
            exact hheight
      · rcases ih with hz | ⟨J, hJ, herase, hheight, hself, hnj⟩
        · left
          rw [Protocol.afterFin_h_j, fold_h_j]
          exact hz
        · right
          refine ⟨J, named_extend slot root votes support rows proposer hJ, ?_, ?_, hself, hnj⟩
          · rw [Protocol.afterFin_J, fold_J]
            exact herase
          · rw [Protocol.afterFin_h_j, fold_h_j]
            exact hheight

/-- A positive named justification has a named certificate witness which is
the entry at the justified height, and that height is justifiable. -/
theorem namedJustification_ancestor_data
    (E : Env V) (cfg : HeightConfig) (B : NamedBlock V)
    (hpos : 0 < (derive_named E cfg B).h_j) :
    ∃ J : NamedBlock V, NamedBlock.Preceq J B ∧
      J.erase = (derive_named E cfg B).J ∧
      (derive_named E cfg J).h = (derive_named E cfg B).h_j ∧
      (derive_named E cfg J).T_h = J.erase ∧
      (derive_named E cfg J).nj = false := by
  exact (named_justification_data E cfg B).resolve_left
    (Nat.ne_of_gt hpos)


/-- A named justification is its own height entry. -/
theorem namedJustification_selfTarget
    (E : Env V) (cfg : HeightConfig) (B : NamedBlock V)
    (hpos : 0 < (derive_named E cfg B).h_j) :
    ∃ J : NamedBlock V, NamedBlock.Preceq J B ∧
      J.erase = (derive_named E cfg B).J ∧
      (derive_named E cfg J).h = (derive_named E cfg B).h_j ∧
      (derive_named E cfg J).T_h = J.erase := by
  obtain ⟨J, hJ, hErase, hHeight, hTarget, _⟩ :=
    namedJustification_ancestor_data E cfg B hpos
  exact ⟨J, hJ, hErase, hHeight, hTarget⟩




/-! ## The slot-`+1` checkpoint split -/

private theorem named_target_or_quiet_of_gate_closed
    (E : Env V) (cfg : HeightConfig) {P0 P1 : NamedBlock V}
    (hparent : NamedBlock.parent? P1 = some P0)
    (hgate : ¬ (derive_named E cfg P0).T_h.slot + cfg.timeoutDelay ≤ P1.slot)
    (hnj : (derive_named E cfg P0).nj = false) :
    Internal.NamedJustifiedAt E cfg P1
        (derive_named E cfg P0).T_h (derive_named E cfg P0).h ∨
      ((derive_named E cfg P1).h = (derive_named E cfg P0).h ∧
        (derive_named E cfg P1).T_h = (derive_named E cfg P0).T_h) := by
  cases hp : P1 with
  | genesis =>
      simp only [hp, NamedBlock.parent?, reduceCtorEq] at hparent
  | node parent slot root votes support rows proposer =>
      have hparentEq : parent = P0 := by
        simpa only [hp, NamedBlock.parent?, Option.some.injEq] using hparent
      subst parent
      subst P1
      let P1' : NamedBlock V :=
        .node P0 slot root votes support rows proposer
      let τ := fold_rows (TimeoutBinding.targeted V) (derive_named E cfg P0)
        P1'.erase rows
      have hfoldNj : τ.nj = (derive_named E cfg P0).nj := by
        exact fold_nj (derive_named E cfg P0) P1'.erase rows
      have hτgate : ¬ τ.T_h.slot + cfg.timeoutDelay ≤ τ.s := by
        intro hmature
        apply hgate
        change (fold_rows (TimeoutBinding.targeted V) (derive_named E cfg P0)
          P1'.erase rows).T_h.slot + cfg.timeoutDelay ≤
          (fold_rows (TimeoutBinding.targeted V) (derive_named E cfg P0)
            P1'.erase rows).s at hmature
        rw [fold_T_h, fold_s] at hmature
        simpa only [P1', Proofs.NamedWire.erase_slot] using hmature
      have htargetEq : targetReady E (Protocol.afterFin E τ) =
          (Protocol.afterFin E τ).targetQuorum E := by
        unfold targetReady
        rw [Protocol.afterFin_nj, hfoldNj, hnj]
        simp
      have hprogEq : progReady E cfg (Protocol.afterFin E τ) =
          (Protocol.afterFin E τ).targetQuorum E := by
        unfold progReady
        have hmature : decide (τ.T_h.slot + cfg.timeoutDelay ≤ τ.s) = false := by
          simp only [decide_eq_false_iff_not]
          exact hτgate
        rw [Protocol.afterFin_T_h, afterFin_s, hmature]
        simp
      change
        ((process_height_events E cfg τ).J = (derive_named E cfg P0).T_h ∧
          (process_height_events E cfg τ).h_j = (derive_named E cfg P0).h) ∨
        ((process_height_events E cfg τ).h = (derive_named E cfg P0).h ∧
          (process_height_events E cfg τ).T_h = (derive_named E cfg P0).T_h)
      rw [Protocol.process_height_events_eq]
      by_cases hquorum : (Protocol.afterFin E τ).targetQuorum E = true
      · left
        have htargetTrue : targetReady E (Protocol.afterFin E τ) = true :=
          htargetEq.trans hquorum
        rw [if_pos htargetTrue]
        constructor
        · rw [Protocol.advance_height_J, Protocol.afterFin_T_h]
          exact fold_T_h (derive_named E cfg P0) P1'.erase rows
        · rw [Protocol.advance_height_h_j, Protocol.afterFin_h]
          exact fold_h (derive_named E cfg P0) P1'.erase rows
      · right
        have htfalse : targetReady E (Protocol.afterFin E τ) = false := by
          simpa only [htargetEq, hquorum]
        have hpfalse : progReady E cfg (Protocol.afterFin E τ) = false := by
          simpa only [hprogEq, hquorum]
        simp only [htfalse, hpfalse, Bool.false_eq_true, ↓reduceIte]
        exact ⟨(Protocol.afterFin_h (E := E) (σ := τ)).trans
            (fold_h (derive_named E cfg P0) P1'.erase rows),
          (Protocol.afterFin_T_h (E := E) (σ := τ)).trans
            (fold_T_h (derive_named E cfg P0) P1'.erase rows)⟩

/-- A named child at a slot whose timeout gate is closed either justifies its
parent's opening checkpoint or preserves that checkpoint's height and entry. -/
theorem namedCheckpointReady_of_parent_of_gate_closed
    (E : Env V) (cfg : HeightConfig) {P0 P1 : NamedBlock V}
    (hparent : NamedBlock.parent? P1 = some P0)
    (hgate : ¬ (derive_named E cfg P0).T_h.slot + cfg.timeoutDelay ≤ P1.slot)
    (hnj : (derive_named E cfg P0).nj = false) :
    Internal.NamedJustifiedAt E cfg P1
        (derive_named E cfg P0).T_h (derive_named E cfg P0).h ∨
      ((derive_named E cfg P1).h = (derive_named E cfg P0).h ∧
        (derive_named E cfg P1).T_h = (derive_named E cfg P0).T_h) := by
  exact named_target_or_quiet_of_gate_closed E cfg hparent hgate hnj

#print axioms namedNj_eq_of_preceq_sameHeight
#print axioms namedJustification_ancestor_data
#print axioms namedJustification_selfTarget
#print axioms namedCheckpointReady_of_parent_of_gate_closed

end NamedCheckpointAlgebra
end Proofs
end DecoupledConsensusModel

end
