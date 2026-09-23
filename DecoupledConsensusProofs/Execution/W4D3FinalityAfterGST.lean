module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.W4FinalityAdapters
public import DecoupledConsensusProofs.Objects.AdmissibleCore
public import DecoupledConsensusProofs.Execution.W4FinalityDeadlines

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # W4 branches d2,: the shared finality adapter (design §5 D3)

Both public finality contracts read one common recovery round and one pair of
round deadlines. earlier packages that read in the private theorem
`finality_afterGST` (`LivenessContractsRun.lean:86-117`); the corresponding branch has already
pinned its exact statement as `FinalityAfterGSTPin` and built the two public
adapters over it.

This file discharges that pin from the recovery-plus-finality export of the
opening-carrier assembly. In earlier that export is
`arbitraryGSTSafetyLiveness_of_openingCarrierRecurrence`; in the selection it is
`Proofs.HealingSurface.uniformCanonicalRecoveryWithFinality_after_GST_openingCarrierRecurrence`
(`OpeningCarrierAssemblyRun.lean:71-109`), whose import path is still red
because it runs through `CanonicalCarrierAfterSafetyRun` (the corresponding branch) and
`OpeningCarrierFinalityRun`.

`UniformRecoveryFinalityPin` below uses the closed startup and deadline
formulas from the statement layer. The handoff witness, the canonical suffix
execution and the healed two-slot handoff are dropped, since
`finality_afterGST` projects none of them.

earlier's extra work in `finality_afterGST` -- lifting
`retainedStableBelowHead` to `HonestHeadExtendsStableFrom` and shifting the
`strongHeadsThreshold` from `delayExtra = 0` -- has no counterpart here: the
selection's frozen `StrongFinalityRun` (`Regimes.lean:47`) carries no
`retainedStableBelowHead` field, and the selection's assembly export takes no
heads premise. The removed field stays removed. -/



namespace DecoupledConsensusModel
namespace Proofs

open Internal Execution Statements

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Pin: the recovery-plus-finality export of the opening-carrier assembly,
`Proofs.HealingSurface.uniformCanonicalRecoveryWithFinality_after_GST_openingCarrierRecurrence`
(`OpeningCarrierAssemblyRun.lean:71`), with the startup and deadline formulas
closed in the statement layer and the unprojected handoff outputs dropped. -/
def UniformRecoveryFinalityPin (S : Setup V) : Prop :=
  ∀ (extra : Nat), TimeoutDelayBound S extra → ∀ gap : Round,
    ∀ (rho : Run V) (rGST : Round),
      Admissible S rho → HonestCommittees S rho.honest →
      BelowOneThird S rho.honest →
      ProposerOpeningCarrierRecurrence S rho gap →
      S.E.t_GST ≤ S.a rGST → gap + 2 ≤ S.cfg.K →
      healingBoundaryTime S
          (rGST + Statements.Instantiation.finalityStartup S gap extra) ≤ rho.horizon →
      ∃ q : Round, rGST ≤ q ∧
        q ≤ rGST + Statements.Instantiation.finalityStartup S gap extra ∧
        RecurringFinalityFrom S rho q (Statements.Instantiation.finalityDeadline S gap extra) ∧
        HonestProposalFinalityFrom S rho q (Statements.Instantiation.finalityDeadline S gap extra)

/-- D3. The shared finality adapter: the strong finality regime supplies every
premise of the recovery-plus-finality export, so the export's common round and
deadlines are exactly the pair both public finality contracts read. -/
theorem finalityAfterGSTPin_of_uniformRecoveryFinality (S : Setup V)
    (hpin : UniformRecoveryFinalityPin S) : FinalityAfterGSTPin S := by
  intro extra hdelay gap
  intro rho rGST h hpost hhor
  exact hpin extra hdelay gap rho rGST h.admissible h.committees h.belowThird
    h.recurrence hpost h.gapBound hhor

/-- The two public finality fields, closed over the same single pin. -/
theorem finalizedChainGrowth_of_uniformRecoveryFinality (S : Setup V)
    (hpin : UniformRecoveryFinalityPin S) : FinalizedChainGrowth S :=
  finalizedChainGrowth_of_pins S (finalityAfterGSTPin_of_uniformRecoveryFinality S hpin)

/-- Honest-proposal finalization over the same single pin. -/
theorem honestProposalFinalization_of_uniformRecoveryFinality (S : Setup V)
    (hpin : UniformRecoveryFinalityPin S) : HonestProposalFinalization S :=
  honestProposalFinalization_of_pins S
    (finalityAfterGSTPin_of_uniformRecoveryFinality S hpin)

/-! ## Axiom roster. Every public theorem of this file. Each must report a
subset of `propext`, `Classical.choice`, `Quot.sound` and nothing else. A
theorem reporting NO axioms is hollow: it means an import's olean lacked a name
and Lean recovered silently, which still exits zero. -/

#print axioms finalityAfterGSTPin_of_uniformRecoveryFinality
#print axioms finalizedChainGrowth_of_uniformRecoveryFinality
#print axioms honestProposalFinalization_of_uniformRecoveryFinality


end Proofs
end DecoupledConsensusModel

end
