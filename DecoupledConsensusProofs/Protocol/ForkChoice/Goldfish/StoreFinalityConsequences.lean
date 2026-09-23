module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.StoreFinalityCore
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusInternal.StoreFinality
public import DecoupledConsensusProofs.Protocol.Grades.Main
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordClean

@[expose] public section

/-!
# Persistent consequences of store finality

This file contains the corrected B9 viable-descendant statement and the
fork-choice-root consequences after local finality acceptance. The properties
of a named finalized or justified checkpoint stop at `get_fg_root`. A separate
generic lemma transports any root prefix through the SG anchor and the final
Goldfish walk.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace StoreFinality

open Protocol (HeightConfig)
open Protocol (HealConfig)
open Internal

variable {V : Type} [DecidableEq V]

/-- B9's store-field core while the current finalized block is at or below the
historical block. A maximum-height witness is viable once containment puts it
above `F`. -/
theorem historical_mem_viableTree_of_current_preceq
    {st : Protocol.Store V} {F : Block V}
    (hcur : Block.preceq st.F F = true)
    (hFT : F ∈ st.T)
    (hmax : HMaxInTree st)
    (hcontain : ∀ W ∈ st.T, st.h_max ≤ (st.σ W).h →
      Block.preceq F W = true) :
    F ∈ Protocol.V_tree st.toHealing.toFG := by
  obtain ⟨W, hWT, hh⟩ := hmax
  simp only [Protocol.V_tree, Protocol.viable_tree,
    Protocol.finalized_descendants, Protocol.viable,
    Finset.mem_filter, decide_eq_true_eq, Protocol.Store.toHealing]
  exact ⟨⟨hFT, hcur⟩, W, hWT, hcontain W hWT hh,
    Nat.le_trans (Nat.sub_le _ _) hh⟩

/-- Corrected B9. If `F` and the current finalized block are comparable, then
the viable tree contains a descendant of historical `F`. When finality has
already advanced, the current finalized block is the witness. -/
theorem historical_hasViableDescendant_of_compare
    {st : Protocol.Store V} {F : Block V}
    (hbefore : Block.preceq st.F F = true →
      F ∈ Protocol.V_tree st.toHealing.toFG)
    (hfinal : FinalizedViable st)
    (hcompare : Block.preceq st.F F = true ∨ Block.preceq F st.F = true) :
    HasViableDescendant st F := by
  rcases hcompare with hcur | hpast
  · exact ⟨F, hbefore hcur, Block.preceq_self F⟩
  · exact ⟨st.F, hfinal, hpast⟩

/-- B3 and B8 provide the comparison needed by corrected B9 because both
`st.F` and historical `F` precede `st.J`. -/
theorem historical_hasViableDescendant_of_upgrade
    {st : Protocol.Store V} {F : Block V}
    (hFT : F ∈ st.T)
    (hmax : HMaxInTree st)
    (hcontain : ∀ W ∈ st.T, st.h_max ≤ (st.σ W).h →
      Block.preceq F W = true)
    (hfinal : FinalizedViable st)
    (hcurJ : Block.preceq st.F st.J = true)
    (hupgrade : Block.preceq F st.J = true) :
    HasViableDescendant st F :=
  historical_hasViableDescendant_of_compare
    (fun hcur =>
      historical_mem_viableTree_of_current_preceq hcur hFT hmax hcontain)
    hfinal (Block.preceq_linear hcurJ hupgrade)

variable [Fintype V]


omit [Fintype V] in
/-- A locally justified checkpoint precedes the FG root if either the cascade
gate selects `J` or local finality has already reached that checkpoint. This is
the exact boundary for the lock-in translation. -/
theorem justified_preceq_fgRoot {st : Protocol.Store V} {F : Block V}
    (hFJ : Block.preceq F st.J = true)
    (hlocalOrCascade : Block.preceq F st.F = true ∨ st.h_max = st.h_j + 1) :
    Block.Preceq F (Protocol.get_fg_root st.toHealing.toFG) := by
  rcases hlocalOrCascade with hlocal | hgate
  · simp only [Protocol.get_fg_root, Protocol.Store.toHealing]
    split
    · exact hFJ
    · exact hlocal
  · have hroot : Protocol.get_fg_root st.toHealing.toFG = st.J := by
      simp [Protocol.get_fg_root, Protocol.Store.toHealing, hgate]
    rw [hroot]
    exact hFJ

end StoreFinality
end Proofs
end DecoupledConsensusModel

end
