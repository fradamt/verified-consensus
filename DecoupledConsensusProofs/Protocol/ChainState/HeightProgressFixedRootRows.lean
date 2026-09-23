module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.FixedHeightRootCore
public import DecoupledConsensusProofs.Execution.SeedActionRowCarriage

@[expose] public section

/-!
# Fixed-root target and action-row inputs

The named justification target input is independent of the lifecycle.
The action-row input below open items at the opening/carrier slot mismatch. The
fixed-root consumer now scopes that residual to its actual local window facts:
the original read-to-`r` bound and `r + 3 ≤ q1`, the q1 carrier and timing,
endpoint horizon/cap and the named q1 `+2` proposal facts, both locks and
records, the persisted grade, later-parent relation, and q2 maturity and
spacing. the prior universal row callback omitted facts required by this route;
the records alone did not establish the honesty of the `+2` proposer.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]




open Protocol (HeightConfig derive_named fold_rows TimeoutBinding)

/-- The justification has a full named ancestor that is its own height entry.
The induction follows the actual named transition, including targeted timeouts. -/
private theorem namedJustification_entry_ancestor
    (E : Env V) (cfg : HeightConfig) (B : NamedBlock V) :
    ∃ J : NamedBlock V, NamedBlock.Preceq J B ∧
      J.erase = (derive_named E cfg B).J ∧
      (derive_named E cfg J).T_h = J.erase := by
  induction B with
  | genesis => exact ⟨.genesis, Proofs.NamedAncestry.named_self _, rfl, rfl⟩
  | node parent s root votes support rows proposer ih =>
      let B := NamedBlock.node parent s root votes support rows proposer
      have hfields := Proofs.NamedStoreRoots.fold_context_fields (TimeoutBinding.targeted V)
        rows { derive_named E cfg parent with s := B.erase.slot }
      have hcases : (derive_named E cfg B).J = (derive_named E cfg parent).T_h ∨
          (derive_named E cfg B).J = (derive_named E cfg parent).J := by
        let folded := fold_rows (TimeoutBinding.targeted V)
          (derive_named E cfg parent) B.erase rows
        change (Protocol.process_height_events E cfg folded).J = _ ∨
          (Protocol.process_height_events E cfg folded).J = _
        simp only [Protocol.process_height_events_eq]
        split_ifs
        · left
          rw [Protocol.advance_height_J, Protocol.afterFin_T_h]
          exact hfields.2.2.1
        · right
          rw [Protocol.advance_height_J, Protocol.afterFin_J]
          exact hfields.2.2.2.1
        · right
          rw [Protocol.afterFin_J]
          exact hfields.2.2.2.1
      rcases hcases with hnew | hstay
      · obtain ⟨entry, hentry, herase, hheight⟩ :=
          Proofs.NamedEntryHeight.entry_ancestor_same_height E cfg parent
        refine ⟨entry, Proofs.NamedAncestry.named_extend s root votes support rows proposer hentry,
          herase.trans hnew.symm, ?_⟩
        exact (Proofs.NamedEntryHeight.entry_eq_on_plateau E cfg hentry hheight).trans herase.symm
      · obtain ⟨J, hJ, herase, hself⟩ := ih
        exact ⟨J, Proofs.NamedAncestry.named_extend s root votes support rows proposer hJ,
          herase.trans hstay.symm, hself⟩

/-- The fixed read's justification is the named target's own height entry.
All named identities use the run's root-injectivity condition. -/
theorem namedJustification_targetRoot_of_fixedRoot
    (S : Setup V) {rho : Run V} (adm : Admissible S rho) :
    ∀ {H : Height} {w : V} {read0 : Time}
      {C : NamedBlock V},
      FixedHeightJustificationRootAtRead S rho H w read0 →
      C.erase = (rho.storeBeforeTime S w read0).J →
      RunBlock S rho C →
      (Protocol.derive_named S.E S.cfg C).h = H - 1 →
      (Protocol.derive_named S.E S.cfg C).T_h.root =
        (rho.storeBeforeTime S w read0).J.root := by
  intro H w read0 C hfix hCerase hCrun _hheight
  obtain ⟨D, _hDbody, hDrun, hjust⟩ := hfix.carrierExists
  obtain ⟨J, hJD, hJerase, hJself⟩ := namedJustification_entry_ancestor S.E S.cfg D
  have hJrun : RunBlock S rho J :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hDrun hJD
  have hJCerase : J.erase = C.erase :=
    hJerase.trans (hjust.1.trans hCerase.symm)
  have hJCroot : J.root = C.root := by
    rw [← Proofs.NamedWire.erase_root J, ← Proofs.NamedWire.erase_root C, hJCerase]
  have hJC : J = C :=
    adm.toNamedRootCollisionFree.root_injective J C hJrun hCrun J C
      (Or.inl (Proofs.NamedAncestry.named_self J))
      (Or.inr (Proofs.NamedAncestry.named_self C)) hJCroot
  have hCself : (derive_named S.E S.cfg C).T_h = C.erase := by
    simpa only [hJC] using hJself
  exact congrArg Block.root (hCself.trans hCerase)

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
