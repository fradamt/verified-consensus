module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Execution.LegacyFinality
public import DecoupledConsensusProofs.Protocol.Grades.SafetySlotInduction
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityComparison
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge

@[expose] public section

/-! # the previous finalized-root obligation without a fault-bound premise
The continuation consumes `FinalizedRootsBelowAtRead`. A post-GST
export can derive it from the accountable bound. The cap-zero instance
is unconditional because finalized height zero means genesis.
The root consumer needs core admissibility only. Its justified-root
branch is excluded by the frontier gap; its finalized-root branch uses
the stated certificate fact. Existing strong interfaces are unchanged.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]



/-- Accountable finality supplies the certificate fact for a block above
The previous-height cap. This is the post-GST export, not a continuation premise. -/
theorem finalizedRootsBelowAtRead_of_accountable
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hsb : SlashableBound S rho) {cap : Height} {P : NamedBlock V}
    (hP : RunBlock S rho P) (hheight : cap < (derive_named S.E S.cfg P).h) :
    FinalizedRootsBelowAtRead S rho cap P.erase := by
  intro v hv t C hC hcap
  have hCrun : RunBlock S rho C := by
    obtain ⟨n, hn, _⟩ :=
      Proofs.Bridges.stateBeforeTime_eq_stateBefore S adm.toNamedScheduleWellFormed t
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i := n)
    rw [← hn]
    exact hC
  exact NamedFinalizationBridge.finalized_preceq_of_height_lt S rho P C hsb
    adm.toNamedRootCollisionFree hP hCrun (hcap.trans_lt hheight)

omit [Fintype V] in
private theorem namedAncestorBodyMem {st : Protocol.NamedStore V}
    (hpc : NamedStore.NamedParentClosed st) {A B : NamedBlock V}
    (hB : B ∈ st.bodies) (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
    intro hB hAB
    simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
    exact hAB ▸ hB
  | node parent slot root votes support rows proposer ih =>
    intro hB hAB
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
      decide_eq_true_eq] at hAB
    rcases hAB with rfl | hparent
    · exact hB
    · exact ih (hpc.2 _ hB) hparent

/-- A low FG root lies below `P` once the reader has passed the cap.
The only historical-finality input is the certificate fact. There is
no accountable bound, full participation, or height condition on `P`. -/
theorem lowFGRoot_preceq_of_frontier_gap_of_finalizedRootsBelow
    (S : Setup V) {rho : Run V}
    {v : V} (hv : v ∈ rho.honest) {time : Time} {cap : Height} {P : Block V}
    (hlegacy : FinalizedRootsBelowAtRead S rho cap P)
    (hfrontier : cap + 1 < (rho.storeBeforeTime S v time).h_max)
    {D : NamedBlock V}
    (hD : D ∈ (rho.storeBeforeTime S v time).bodies)
    (hDR : D.erase = Protocol.get_fg_root
      (rho.storeBeforeTime S v time).toHealing.toFG)
    (hheight : (derive_named S.E S.cfg D).h ≤ cap) :
    Block.Preceq
      (Protocol.get_fg_root (rho.storeBeforeTime S v time).toHealing.toFG) P := by
  let st := rho.storeBeforeTime S v time
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg st := by
    simpa only [st] using
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho time v).1.1.1
  have hpc := hcoh.2.2.1
  by_cases hgate : st.core.h_max = st.core.h_j + 1
  · have hroot : Protocol.get_fg_root st.toHealing.toFG = st.core.J := by
      change (if st.core.h_max = st.core.h_j + 1 then st.core.J else st.core.F) =
        st.core.J
      exact if_pos hgate
    obtain ⟨J, hJ, hJJ, hJh⟩ :=
      Proofs.Bridges.storeJustificationOnChain_stateBeforeTime S rho time v
    have hJJ' : (derive_named S.E S.cfg J).J = st.core.J := by
      simpa only [st] using hJJ
    have hJh' : (derive_named S.E S.cfg J).h_j = st.core.h_j := by
      simpa only [st] using hJh
    rcases NamedCheckpointHeights.justified_ancestor_height S.E S.cfg J with
      hz | ⟨K, hKJ, hKerase, hKheight⟩
    · have hgen : (derive_named S.E S.cfg J).J = Block.genesis :=
        NamedJustificationCertificates.justified_zero_is_genesis S.E S.cfg J hz
      have hstJ : st.core.J = Block.genesis := by
        exact hJJ'.symm.trans hgen
      rw [hroot, hstJ]
      exact Protocol.preceq_genesis P
    · have hK : K ∈ st.bodies := namedAncestorBodyMem hpc hJ hKJ
      have hKD : K.erase = D.erase := by
        calc
          K.erase = (derive_named S.E S.cfg J).J := hKerase
          _ = st.core.J := hJJ'
          _ = Protocol.get_fg_root st.toHealing.toFG := hroot.symm
          _ = D.erase := hDR.symm
      have hKD' : K = D := hcoh.2.1 K hK D hD hKD
      have hDheight : (derive_named S.E S.cfg D).h = st.core.h_j := by
        exact (congrArg (fun X => (derive_named S.E S.cfg X).h) hKD'.symm).trans
          (hKheight.trans hJh')
      have hcap : st.core.h_j ≤ cap := by
        rw [← hDheight]
        exact hheight
      have hmax : st.core.h_max ≤ cap + 1 := by
        rw [hgate]
        exact Nat.add_le_add_right hcap 1
      exact False.elim ((Nat.not_lt_of_ge hmax) hfrontier)
  · have hroot : Protocol.get_fg_root st.toHealing.toFG = st.core.F := by
      change (if st.core.h_max = st.core.h_j + 1 then st.core.J else st.core.F) =
        st.core.F
      exact if_neg hgate
    obtain ⟨F, hF, hFF, hFh⟩ :=
      Proofs.Bridges.storeFinalizationOnChain_stateBeforeTime S rho time v
    have hFF' : (derive_named S.E S.cfg F).F = st.core.F := by
      simpa only [st] using hFF
    rcases NamedCheckpointHeights.finalized_ancestor_height S.E S.cfg F with
      hz | ⟨K, hKF, hKerase, hKheight⟩
    · have hgen : (derive_named S.E S.cfg F).F = Block.genesis :=
        NamedFinalityCertificates.finalized_zero_is_genesis S.E S.cfg F hz
      have hstF : st.core.F = Block.genesis := by
        exact hFF'.symm.trans hgen
      rw [hroot, hstF]
      exact Protocol.preceq_genesis P
    · have hK : K ∈ st.bodies := namedAncestorBodyMem hpc hF hKF
      have hKD : K.erase = D.erase := by
        calc
          K.erase = (derive_named S.E S.cfg F).F := hKerase
          _ = st.core.F := hFF'
          _ = Protocol.get_fg_root st.toHealing.toFG := hroot.symm
          _ = D.erase := hDR.symm
      have hKD' : K = D := hcoh.2.1 K hK D hD hKD
      have hDheight : (derive_named S.E S.cfg D).h =
          (derive_named S.E S.cfg F).h_F := by
        exact (congrArg (fun X => (derive_named S.E S.cfg X).h) hKD'.symm).trans
          hKheight
      have hcap : (derive_named S.E S.cfg F).h_F ≤ cap := by
        rw [← hDheight]
        exact hheight
      change Block.Preceq (Protocol.get_fg_root st.toHealing.toFG) P
      rw [hroot, ← hFF']
      exact hlegacy v hv time F hF hcap

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
