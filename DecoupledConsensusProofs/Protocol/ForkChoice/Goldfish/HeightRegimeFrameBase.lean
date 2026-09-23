module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightRegimeFrame

@[expose] public section

/-!
# Named height-regime frame base

This low module contains the named predecessor-height frame contract. It is
separate from the complete named regime record so recovery source-frame
producers can consume the contract without an import cycle.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The named predecessor-height finality floor. -/
def NamedFinalityFloorAt
    (S : Setup V) (rho : Run V) (blocked : Height) (stop : Nat)
    (Tprev : NamedBlock V) : Prop :=
  ∀ v ∈ rho.honest, ∀ n : Nat, n ≤ stop →
    ∀ X : NamedBlock V, RunBlock S rho X →
      blocked ≤ (Protocol.derive_named S.E S.cfg X).h →
      NamedBlock.Preceq Tprev X →
      Block.Preceq (rho.stateBefore S n v).st.core.F X.erase

/-- The height-regime frame with named predecessor and source bodies. -/
structure NamedHeightRegimeFrame
    (S : Setup V) (rho : Run V) (blocked : Height) (stop : Nat)
    (Tprev : NamedBlock V) (c0 : Round) : Prop where
  floor : NamedFinalityFloorAt S rho blocked stop Tprev
  prevRun : RunBlock S rho Tprev
  prevHeight : (Protocol.derive_named S.E S.cfg Tprev).h ≤ blocked
  rootBelow : ∀ v ∈ rho.honest, ∀ n : Nat, n ≤ stop →
    ∀ Q : NamedBlock V, Q ∈ (rho.stateBefore S n v).st.bodies →
      (Protocol.derive_named S.E S.cfg Q).h = blocked + 1 →
      NamedBlock.Preceq Tprev Q →
      Block.Preceq
        (Protocol.get_fg_root
          (rho.stateBefore S n v).st.core.toHealing.toFG) Q.erase
  sourceAbove : ∀ p ∈ rho.honest, ∀ r : Round,
    strictEventIndex rho (S.a r) ≤ stop → S.a r ≤ rho.horizon →
    ∀ B : NamedBlock V,
      B ∈ (actionStoreAt S rho p r).st.bodies →
      actionFGSource S (actionStoreAt S rho p r) = some B.erase →
      (Protocol.derive_named S.E S.cfg B).h = blocked + 1 →
      NamedBlock.Preceq Tprev B

/-- A named store body at the source height is retained in the reader's
finality-filtered tree, and the local FG root is below it. -/
theorem NamedHeightRegimeFrame.fgRoot_preceq_and_filteredMem
    {S : Setup V} {rho : Run V} {blocked : Height} {stop : Nat}
    {Tprev : NamedBlock V} {c0 : Round}
    (h : NamedHeightRegimeFrame S rho blocked stop Tprev c0)
    (adm : Admissible S rho)
    (hfrontier : honestHMaxBeforeIndex S rho stop < blocked + 2)
    {n : Nat} {reader : V} {Q : NamedBlock V}
    (hreader : reader ∈ rho.honest) (hnstop : n ≤ stop)
    (hQmem : Q ∈ (rho.stateBefore S n reader).st.bodies)
    (hQheight : (Protocol.derive_named S.E S.cfg Q).h = blocked + 1)
    (hTQ : NamedBlock.Preceq Tprev Q) :
    Block.Preceq (Protocol.get_fg_root
        (rho.stateBefore S n reader).st.core.toHealing.toFG) Q.erase ∧
      Q.erase ∈ Protocol.get_filtered_block_tree
        (rho.stateBefore S n reader).st.core.toHealing.toFG := by
  have hcoh :=
    (Proofs.NamedRuntime.stateBefore_invariants S rho n reader).1.1.1
  have hQraw : Q.erase ∈ (rho.stateBefore S n reader).st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hQmem
  have hQstored :
      ((rho.stateBefore S n reader).st.core.σ Q.erase).h = blocked + 1 := by
    rw [Proofs.NamedStoreBridge.derivedView_stateBefore S rho n reader Q hQmem,
      hQheight]
  have hmax : (rho.stateBefore S n reader).st.core.h_max = blocked + 1 :=
    localHMax_eq_blocked_succ_of_rawMem_of_prefixFrontier
      S adm hfrontier hreader hnstop hQraw hQstored
  have hrootQ := h.rootBelow reader hreader n hnstop Q hQmem hQheight hTQ
  have hQrun : RunBlock S rho Q :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hreader hQmem
  have hFQ : Block.Preceq
      (rho.stateBefore S n reader).st.core.F Q.erase :=
    h.floor reader hreader n hnstop Q hQrun
      (by rw [hQheight]; exact Nat.le_succ blocked) hTQ
  have hV : Q.erase ∈ Protocol.V_tree
      (rho.stateBefore S n reader).st.core.toHealing.toFG := by
    simp only [Protocol.V_tree, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, Protocol.Store.toHealing, decide_eq_true_eq]
    refine ⟨⟨hQraw, hFQ⟩, Q.erase, hQraw, Block.preceq_self _, ?_⟩
    rw [hmax, hQstored]
    exact Nat.sub_le _ _
  exact ⟨hrootQ, Proofs.Records.mem_filtered_of_mem_V_tree hV hrootQ⟩


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
