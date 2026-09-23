module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.FixedHeightRootAdmission
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradePersistence
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.Store.BoundaryRows
public import DecoupledConsensusProofs.Execution.Wire

@[expose] public section

/-!
# Fixed-root grade persistence at the next G2 read

This proof-only module supplies the missing fixed-root activity fact in the
public height handoff. earlier obtained this fact from the fixed action-store root.
The relative-grade runtime reads earlier, at the next G2 domain cutoff. The
named fixed-root relay theorem identifies the root at that exact read after one
post-GST delay. The previous grade then supplies the retained body, and the
fixed height supplies its viability.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open Proofs.HealingLemmas
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A processed named block above an exact fixed root is filtered when its
derived height is within one of the exact local frontier. -/
theorem fixedRootGrade_mem_filtered_of_exactRoot
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {M : Height} {u w : V} {read0 target : Time} {B : NamedBlock V}
    (hw : w ∈ rho.honest)
    (hBRun : RunBlock S rho B)
    (hprocessed : B.erase ∈ (rho.storeBeforeTime S w target).core.T)
    (hJB : Block.Preceq (rho.storeBeforeTime S u read0).J B.erase)
    (hBheight : M - 1 ≤ (Protocol.derive_named S.E S.cfg B).h)
    (hroot : Protocol.get_fg_root
      (rho.storeBeforeTime S w target).core.toHealing.toFG =
        (rho.storeBeforeTime S u read0).J)
    (hmax : (rho.storeBeforeTime S w target).core.h_max = M) :
    B.erase ∈ Protocol.get_filtered_block_tree
      (rho.storeBeforeTime S w target).core.toHealing.toFG := by
  let st := rho.storeBeforeTime S w target
  obtain ⟨D, hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
      S rho target w hprocessed
  obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
    S rho adm.toNamedScheduleWellFormed.sorted target
  have hDprefix : D ∈ (rho.stateBefore S i w).st.bodies := by
    change D ∈ (NamedRun.stateBefore S rho i w).st.bodies
    rw [← hi]
    exact hDbody
  have hDRun : RunBlock S rho D :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hw hDprefix
  have hrootEq : D.root = B.root := by
    rw [← Proofs.NamedWire.erase_root D, ← Proofs.NamedWire.erase_root B, hDerase]
  have hDB : D = B :=
    adm.toNamedRootCollisionFree.root_injective D B hDRun hBRun D B
      (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self B)) hrootEq
  have hBbody : B ∈ st.bodies := by
    simpa only [hDB, st] using hDbody
  have hview : st.core.σ B.erase =
      Protocol.derive_named S.E S.cfg B := by
    simpa only [st] using
      Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho target w B hBbody
  have hFJ : Block.Preceq st.core.F st.core.J := by
    simpa only [st] using
      Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        S rho target w
  have hFroot : Block.Preceq st.core.F
      (Protocol.get_fg_root st.core.toHealing.toFG) := by
    simpa only [Protocol.Store.toHealing] using
      (Proofs.Records.preceq_get_fg_root_of_F
        (st := st.core.toHealing.toFG) (by
          simpa only [Protocol.Store.toHealing] using hFJ))
  have hrootB : Block.Preceq
      (Protocol.get_fg_root st.core.toHealing.toFG) B.erase := by
    rw [show Protocol.get_fg_root st.core.toHealing.toFG =
        (rho.storeBeforeTime S u read0).J by
      simpa only [st] using hroot]
    exact hJB
  have hFB : Block.Preceq st.core.F B.erase :=
    Block.preceq_trans hFroot hrootB
  have hV : B.erase ∈ Protocol.V_tree st.core.toHealing.toFG := by
    simp only [Protocol.V_tree, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, Protocol.Store.toHealing, decide_eq_true_eq]
    refine ⟨⟨hprocessed, hFB⟩, B.erase, hprocessed,
      Block.preceq_self B.erase, ?_⟩
    rw [show st.core.h_max = M by simpa only [st] using hmax, hview]
    exact hBheight
  exact Proofs.Records.mem_filtered_of_mem_V_tree hV hrootB


/-- A grade block above the fixed justification target remains in the filtered
tree at the next relative G2 read when the fixed frontier has not risen.

This is the  restatement of earlier's fixed-root action-read activity step. The
new argument is the exact relative G2 read, so the fixed-root relay delay and
its horizon guard are explicit proof-layer inputs. -/
theorem fixedRootGrade_mem_filteredTree_nextG2_of_noRise
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {u : V} {read0 : Time}
    (hroot : FixedHeightJustificationRootAtRead S rho M u read0)
    {r : Round} {B : NamedBlock V}
    (hforms : NamedGradeFormsAt S rho r B.erase)
    (hBRun : RunBlock S rho B)
    (hJB : Block.Preceq (rho.storeBeforeTime S u read0).J B.erase)
    (hBheight : M - 1 ≤ (Protocol.derive_named S.E S.cfg B).h)
    (hpost : S.E.t_GST ≤ read0)
    (hdelay : read0 + S.E.Δ ≤ domain S.E S.hc (r + 1) .g2)
    (hhor : domain S.E S.hc (r + 1) .g2 ≤ rho.horizon)
    (hcap : honestHMaxAt S rho (domain S.E S.hc (r + 1) .g2) ≤ M)
    {w : V} (hw : w ∈ rho.honest) :
    B.erase ∈ filteredTree (relativeG2Read S rho (r + 1) w) := by
  let target := domain S.E S.hc (r + 1) .g2
  let st := rho.storeBeforeTime S w target
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hfixed :=
    fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
      S adm hsb hroot hw hpost hdelay hhor hcap
  have hprocessed : B.erase ∈ st.core.T := by
    have hactionDomain : S.a r ≤ target := by
      exact NamedOutageClosure.action_le_domain S S.hc.R_ge_three
        (Nat.lt_succ_self r)
    simpa only [st, target] using
      namedGradeFormsAt_processedAtRead_of_action_le
        S adm hforms hw hactionDomain
  have hfiltered := fixedRootGrade_mem_filtered_of_exactRoot
    S adm hw hBRun hprocessed hJB hBheight hfixed.1 hfixed.2
  simpa only [filteredTree, relativeG2Read, PhaseGrades.readAt, target, st,
    Run.storeBeforeTime] using hfiltered

#print axioms fixedRootGrade_mem_filtered_of_exactRoot
#print axioms fixedRootGrade_mem_filteredTree_nextG2_of_noRise

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
