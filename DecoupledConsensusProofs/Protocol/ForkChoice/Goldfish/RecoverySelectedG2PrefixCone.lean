module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoverySelectedActionG2VoteCone
public import DecoupledConsensusProofs.Execution.RecoverySelectedG2PrefixVisibility
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightRegimeFrame
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FinalityFilterRetention
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityComparison
public import DecoupledConsensusProofs.Protocol.Handlers.JustificationCarrier
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

/-!
# Prefix-capped filtered retention and opening vote cone for a selected G2

The selected-G2 visibility leaf gives raw membership at the action and opening
vote reads. This module derives the actual finality-filtered membership at
those exact reads from only finite-prefix facts. The proof protects the exact
selected block, not its height checkpoint.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-- At one honest prefix read, the finite finality cap fixes the actual FG root
at `F` and retains a raw exact-height selected block. The `J` branch is 
out from the derived prefix NJ universe; finality safety is applied to the
exact height-`blocked` ancestor of `Q`. -/
theorem fgRoot_eq_F_and_filteredMem_of_prefixCap_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {stop : Nat} {hF0 blocked : Height}
    (hcap : HonestPrefixFinalityCap S rho stop hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (hfrontier : honestHMaxBeforeIndex S rho stop < blocked + 2)
    {n : Nat} {reader : V} {Q P : Block V}
    (hreader : reader ∈ rho.honest) (hnstop : n ≤ stop)
    (hQmem : Q ∈ (rho.stateBefore S n reader).st.core.T)
    (hQheight : ((rho.stateBefore S n reader).st.core.σ Q).h = blocked + 1)
    (hPQ : Block.Preceq P Q)
    (hPheight : ((rho.stateBefore S n reader).st.core.σ P).h = blocked) :
    Protocol.get_fg_root
      (rho.stateBefore S n reader).st.core.toHealing.toFG =
        (rho.stateBefore S n reader).st.core.F ∧
      Q ∈ Protocol.get_filtered_block_tree
        (rho.stateBefore S n reader).st.core.toHealing.toFG := by
  have hmax : (rho.stateBefore S n reader).st.core.h_max = blocked + 1 :=
    localHMax_eq_blocked_succ_of_rawMem_of_prefixFrontier
      S adm hfrontier hreader hnstop hQmem hQheight
  have hcapN : HonestPrefixFinalityCap S rho n hF0 :=
    honestPrefixFinalityCap_of_le S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hnstop hcap
  have huniverse : HonestPrefixNJUniverse S rho n blocked :=
    honestPrefixNJUniverse_of_finalityCap S
      adm.toNamedAdmissibleCore.toNamedDeliveryWellFormed hcapN hrec
  have hhj : (rho.stateBefore S n reader).st.core.h_j ≠ blocked := by
    obtain ⟨D, hD, -, hDj⟩ :=
      NamedJustificationCarrier.justification_carrier_stateBefore
        S rho n reader
    have hDne := (huniverse reader hreader D hD).2
    intro h
    apply hDne
    exact hDj.trans h
  have hpc : ParentClosed (rho.stateBefore S n reader).st.core :=
    Proofs.NamedStoreBridge.parentClosed_stateBefore S rho n reader
  have hPmem : P ∈ (rho.stateBefore S n reader).st.core.T :=
    Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
      P Q hQmem hPQ
  obtain ⟨P', hPbody, hPerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n reader hPmem
  have hPrun : RunBlock S rho P' :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hreader hPbody
  have hPheight' : (Protocol.derive_named S.E S.cfg P').h = blocked := by
    have hview := Proofs.NamedStoreBridge.derivedView_stateBefore
      S rho n reader P' hPbody
    rw [← hview, hPerase, hPheight]
  obtain ⟨C, hCbody, hF, -⟩ :=
    Proofs.Bridges.storeFinalizationOnChain_stateBefore S rho n reader
  have hCrun : RunBlock S rho C :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hreader hCbody
  have hcapC : (Protocol.derive_named S.E S.cfg C).h_F ≤ hF0 :=
    hcapN reader hreader C hCbody
  have hcrossed : (Protocol.derive_named S.E S.cfg C).h_F <
      (Protocol.derive_named S.E S.cfg P').h := by
    rw [hPheight']
    exact hcapC.trans_lt
      ((Nat.lt_succ_self hF0).trans (NjGap.lt_of_recoveryHeight hrec))
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hbelow
  have hFP : Block.Preceq
      (rho.stateBefore S n reader).st.core.F P := by
    have hpre : Block.Preceq
        (Protocol.derive_named S.E S.cfg C).F P'.erase :=
      NamedFinalizationBridge.finalized_preceq_of_height_lt S rho P' C hsb
        adm.toNamedAdmissibleCore.toNamedRootCollisionFree hPrun hCrun hcrossed
    simpa only [hF, hPerase] using hpre
  have hFQ : Block.Preceq (rho.stateBefore S n reader).st.core.F Q :=
    Block.preceq_trans hFP hPQ
  have hgate : ¬ ((rho.stateBefore S n reader).st.core.h_max =
      (rho.stateBefore S n reader).st.core.h_j + 1) := by
    intro hgate
    apply hhj
    exact (Nat.add_right_cancel (hmax.symm.trans hgate)).symm
  have hrootF : Protocol.get_fg_root
      (rho.stateBefore S n reader).st.core.toHealing.toFG =
        (rho.stateBefore S n reader).st.core.F := by
    simp only [Protocol.get_fg_root, Protocol.Store.toHealing, if_neg hgate]
  have hV : Q ∈ Protocol.V_tree
      (rho.stateBefore S n reader).st.core.toHealing.toFG := by
    simp only [Protocol.V_tree, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, Protocol.Store.toHealing, decide_eq_true_eq]
    refine ⟨⟨hQmem, hFQ⟩, Q, hQmem, Block.preceq_self _, ?_⟩
    rw [hmax, hQheight]
    exact Nat.sub_le _ _
  have hrootQ : Block.preceq
      (Protocol.get_fg_root
        (rho.stateBefore S n reader).st.core.toHealing.toFG) Q = true := by
    rw [hrootF]
    exact hFQ
  exact ⟨hrootF, Proofs.Records.mem_filtered_of_mem_V_tree hV hrootQ⟩

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
