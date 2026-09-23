module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.Bridges
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.ReleasedCertificateHeightProgress

@[expose] public section

/-!
# Finality-filter interference at strict reads

This low proof interface separates the two ways in which the finality-gadget
filter can displace a protected block at an actual strict read.

* The selected `get_fg_root` can be incompatible with the protected block.
* A compatible root can be a strict ancestor while the height/viability filter
  removes the protected block.

The complement theorem is store-semantic only. The height-filter theorem then
uses the reachable strict-read store itself: derived-state agreement makes the
processed protected block a local viability witness whenever `h_max ≤ H + 1`.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Both finality-gadget filters are noninterfering at one actual read. -/
def FinalityFilterNoninterferenceAtRead
    (S : Setup V) (rho : Run V) (w : V) (read : Time)
    (P : Block V) : Prop :=
  Block.Preceq P
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w read).toHealing.toFG) ∨
    P ∈ Protocol.get_filtered_block_tree
      (rho.storeBeforeTime S w read).toHealing.toFG

/-- The selected finality-gadget root conflicts with the protected block. -/
def FGRootInterferenceAt (st : Protocol.NamedStore V) (P : Block V) : Prop :=
  Block.compatible
    (Protocol.get_fg_root st.toHealing.toFG) P = false

/-- The selected root is strictly below the protected block, but the local
height/viability filter removes the protected block. -/
def HeightFilterInterferenceAt (st : Protocol.NamedStore V) (P : Block V) : Prop :=
  Block.Prec (Protocol.get_fg_root st.toHealing.toFG) P ∧
    P ∉ Protocol.get_filtered_block_tree st.toHealing.toFG

/-- Failure of full finality-filter noninterference has exactly two causes:
an incompatible selected root, or removal by the height/viability filter below
a strict-ancestor selected root. -/
theorem not_finalityFilterNoninterferenceAtRead_iff
    (S : Setup V) (rho : Run V) (w : V) (read : Time) (P : Block V) :
    (¬ FinalityFilterNoninterferenceAtRead S rho w read P) ↔
      FGRootInterferenceAt (rho.storeBeforeTime S w read) P ∨
      HeightFilterInterferenceAt (rho.storeBeforeTime S w read) P := by
  let st : Protocol.NamedStore V := rho.storeBeforeTime S w read
  change
    (¬ (Block.Preceq P (Protocol.get_fg_root st.toHealing.toFG) ∨
      P ∈ Protocol.get_filtered_block_tree st.toHealing.toFG)) ↔
      FGRootInterferenceAt st P ∨ HeightFilterInterferenceAt st P
  constructor
  · intro hnot
    have hnotPRoot : ¬ Block.Preceq P
        (Protocol.get_fg_root st.toHealing.toFG) := by
      intro hPRoot
      exact hnot (Or.inl hPRoot)
    have hnotFiltered :
        P ∉ Protocol.get_filtered_block_tree st.toHealing.toFG := by
      intro hfiltered
      exact hnot (Or.inr hfiltered)
    by_cases hrootP : Block.Preceq
        (Protocol.get_fg_root st.toHealing.toFG) P
    · right
      refine ⟨?_, hnotFiltered⟩
      have hne : Protocol.get_fg_root st.toHealing.toFG ≠ P := by
        intro heq
        apply hnotPRoot
        rw [heq]
        exact Block.preceq_self P
      change Block.prec (Protocol.get_fg_root st.toHealing.toFG) P = true
      simp only [Block.prec, Bool.and_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not]
      exact ⟨hne, hrootP⟩
    · left
      unfold FGRootInterferenceAt
      simp only [Block.compatible, Bool.or_eq_false_iff]
      exact ⟨Bool.eq_false_of_not_eq_true hrootP,
        Bool.eq_false_of_not_eq_true hnotPRoot⟩
  · intro hint hquiet
    rcases hint with hroot | hheight
    · unfold FGRootInterferenceAt at hroot
      have hcompat : Block.compatible
          (Protocol.get_fg_root st.toHealing.toFG) P = true := by
        simp only [Block.compatible, Bool.or_eq_true]
        rcases hquiet with hPRoot | hfiltered
        · exact Or.inr hPRoot
        · exact Or.inl
            (Proofs.Records.preceq_get_fg_root_of_mem_filtered hfiltered)
      rw [hcompat] at hroot
      simp at hroot
    · rcases hheight with ⟨hstrict, hnotFiltered⟩
      rcases hquiet with hPRoot | hfiltered
      · change Block.prec
          (Protocol.get_fg_root st.toHealing.toFG) P = true at hstrict
        simp only [Block.prec, Bool.and_eq_true, Bool.not_eq_true',
          decide_eq_false_iff_not] at hstrict
        exact hstrict.1 (Block.preceq_antisymm hstrict.2 hPRoot)
      · exact hnotFiltered hfiltered


/-- A processed protected named body at or above the selected finality-gadget
root cannot be absent from the filtered tree while the reader's raw local
maximum is at most `H + 1`.

/derived-state class: the protected block is a named
body `D`; the height premise is `derive_named`-valued (the retired
`derived_state`/`DerivedStateAgrees` bridge at a `DepReachableStore` does not
exist), and the store's cached agreement with it comes from
`Proofs.NamedStore.Coherent`'s `DerivedView` clause
(`Proofs.NamedStoreBridge.derivedView_stateBeforeTime`), read at the reader's own
named prefix invariant. -/
theorem filteredOut_hMax_of_root_preceq
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (_hw : w ∈ rho.honest) {read : Time} {H : Height} {D : NamedBlock V}
    (hDmem : D ∈ (rho.storeBeforeTime S w read).bodies)
    (hheight : H ≤ (Protocol.derive_named S.E S.cfg D).h)
    (hrootP : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w read).toHealing.toFG) D.erase)
    (hnotFiltered : D.erase ∉ Protocol.get_filtered_block_tree
      (rho.storeBeforeTime S w read).toHealing.toFG) :
    H + 2 ≤ (rho.storeBeforeTime S w read).h_max := by
  let st : Protocol.NamedStore V := rho.storeBeforeTime S w read
  have hDmem' : D ∈ st.bodies := by
    simpa only [st] using hDmem
  have hrootP' : Block.Preceq
      (Protocol.get_fg_root st.toHealing.toFG) D.erase := by
    simpa only [st] using hrootP
  have hnotFiltered' :
      D.erase ∉ Protocol.get_filtered_block_tree st.toHealing.toFG := by
    simpa only [st] using hnotFiltered
  change H + 2 ≤ st.h_max
  by_contra hnotProgress
  have hlt : st.h_max < H + 2 := Nat.lt_of_not_ge hnotProgress
  have hcap : st.h_max ≤ H + 1 :=
    Nat.lt_succ_iff.mp (by
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hlt)
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg st := by
    simpa only [st, Run.storeBeforeTime] using
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho read w).1.1.1
  have hPmem' : D.erase ∈ st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem _ hDmem'
  have hlocalHeight : H ≤ (st.core.σ D.erase).h := by
    rw [show st.core.σ D.erase = Protocol.derive_named S.E S.cfg D from by
      simpa only [st, Run.storeBeforeTime] using
        Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho read w D hDmem']
    exact hheight
  have hFJ : Block.Preceq st.F st.J := by
    simpa only [st, Run.storeBeforeTime] using
      Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho read w
  have hFP : Block.Preceq st.F D.erase :=
    Block.preceq_trans
      (Proofs.Records.preceq_get_fg_root_of_F (st := st.toHealing.toFG) hFJ)
      hrootP'
  have hbound : st.h_max ≤ (st.core.σ D.erase).h + 1 :=
    hcap.trans (Nat.add_le_add_right hlocalHeight 1)
  have hfrontier : st.h_max - 1 ≤ (st.core.σ D.erase).h :=
    Nat.sub_le_iff_le_add.mpr hbound
  have hV : D.erase ∈ Protocol.V_tree st.toHealing.toFG := by
    simp only [Protocol.V_tree, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq, Protocol.Store.toHealing]
    exact ⟨⟨hPmem', hFP⟩, D.erase, hPmem', Block.preceq_self D.erase, hfrontier⟩
  have hfiltered :
      D.erase ∈ Protocol.get_filtered_block_tree st.toHealing.toFG :=
    Proofs.Records.mem_filtered_of_mem_V_tree hV hrootP'
  exact hnotFiltered' hfiltered


/-- Height-filter interference at an honest reachable strict read forces the
reader's raw local maximum past `H + 1`. -/
theorem heightFilterInterference_hMax
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (_hw : w ∈ rho.honest) {read : Time} {H : Height} {D : NamedBlock V}
    (hDmem : D ∈ (rho.storeBeforeTime S w read).bodies)
    (hheight : H ≤ (Protocol.derive_named S.E S.cfg D).h)
    (hint : HeightFilterInterferenceAt
      (rho.storeBeforeTime S w read) D.erase) :
    H + 2 ≤ (rho.storeBeforeTime S w read).h_max := by
  exact filteredOut_hMax_of_root_preceq S adm _hw hDmem hheight
    (Block.preceq_of_prec hint.1) hint.2


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
