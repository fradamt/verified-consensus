module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.SeedBoundaryConeLead
public import DecoupledConsensusProofs.Execution.RecoveryFinalityEntrance
public import DecoupledConsensusProofs.Protocol.Handlers.StoreFinality
public import DecoupledConsensusProofs.Protocol.ChainState.Main
public import DecoupledConsensusInternal.Execution.Assumptions
public import DecoupledConsensusProofs.Protocol.ChainState.Chain
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityComparison
public import DecoupledConsensusProofs.Protocol.Handlers.JustificationBound

@[expose] public section

/-!
# Finalized blocks are canonical above their height

A block finalized at height `h_F` in any honest tree is below every run block
whose ladder height exceeds `h_F` (`Protocol.finalized_preceq_of_height_lt`).
Under the gate-off frame an honest node's finalized root has `h_F ≤ h_j ≤ M - 2`,
so every band block, in particular every honest vote head, descends it,
whether or not the reader has adopted it. This is what lets the seed run
without a common root: every honest SG vote is above every finalized root, so
each node's root has grade 2 everywhere and no honest vote falls to the raw
anchor tier.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

/-- **Canonicity at the band.** An honest node's finalized root, read while
its gate is off with frontier `M`, is below every run block of derived height
at least `M - 1`. -/
theorem finalizedRoot_preceq_of_band
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {v : V} (hv : v ∈ rho.honest) {t : Time} {M : Height}
    (hgate : (rho.storeBeforeTime S v t).h_j + 2 ≤ M)
    {X : NamedBlock V} (hXrun : RunBlock S rho X)
    (hXh : M - 1 ≤ (Protocol.derive_named S.E S.cfg X).h) :
    Block.Preceq (rho.storeBeforeTime S v t).core.F X.erase := by
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  obtain ⟨B, hBT, hBF⟩ := exists_carrier_of_F S adm hv t
  have hBrun : RunBlock S rho B := by
    obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed t
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i := n)
    simpa only [Run.storeBeforeTime, hn] using hBT
  have hnoHigh : NamedNoHighJustifications S.E S.cfg
      (rho.storeBeforeTime S v t) :=
    NamedJustificationBound.noHighJustifications_stateBeforeTime S rho t v
  have hhj : (Protocol.derive_named S.E S.cfg B).h_j ≤
      (rho.storeBeforeTime S v t).core.h_j := by
    exact hnoHigh B hBT
  have hhF : (Protocol.derive_named S.E S.cfg B).h_F ≤
      (Protocol.derive_named S.E S.cfg B).h_j :=
    (NamedDerivationGeometry.chainOrder_derive_named S.E S.cfg B).heights_ordered
  have hlt : (Protocol.derive_named S.E S.cfg B).h_F <
      (Protocol.derive_named S.E S.cfg X).h := by
    have h1 : (Protocol.derive_named S.E S.cfg B).h_F + 1 + 1 ≤ M :=
      (Nat.add_le_add_right (hhF.trans hhj) 2).trans hgate
    exact lt_of_lt_of_le (Nat.lt_of_succ_le (Nat.le_sub_of_add_le h1)) hXh
  have hpre := NamedFinalizationBridge.finalized_preceq_of_height_lt
    S rho X B hsb adm.toNamedAdmissibleCore.toNamedRootCollisionFree hXrun hBrun hlt
  simpa only [hBF] using hpre

#print axioms finalizedRoot_preceq_of_band

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
