module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityComparison

@[expose] public section

/-! Actual named finalization agreement. This proves only agreement of actual named
finalizations. It does not prove one-Delta propagation or candidate admission.
No compatibility Run, compatibility derived_state, SG invariant, or hno premise is used. -/
namespace DecoupledConsensusModel.Proofs.NamedFinalityAgreement
open Execution Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The accountable bound makes the finalizations of two actual full named
run bodies compatible. No checkpoint-height realization theorem is needed:
compare the two finalized heights, then put both finalizations on the carrier
with the greater finalized height. -/
theorem finalized_compatible
    (S : Setup V) (rho : NamedRun V) (C D : NamedBlock V)
    (hsb : Internal.NamedOutageEntry.SlashableBound S rho)
    (hroot : NamedRootCollisionFree S rho)
    (hC : NamedRun.blockInRun S rho C)
    (hD : NamedRun.blockInRun S rho D) :
    Block.compatible (derive_named S.E S.cfg C).F
      (derive_named S.E S.cfg D).F = true := by
  have hCorder := Proofs.NamedStoreRoots.chainOrder_derive_named S.E S.cfg C
  have hDorder := Proofs.NamedStoreRoots.chainOrder_derive_named S.E S.cfg D
  have hCanchor := (Proofs.NamedStoreRoots.derive_named_anchors_preceq S.E S.cfg C).1
  have hDanchor := (Proofs.NamedStoreRoots.derive_named_anchors_preceq S.E S.cfg D).1
  have hlinear :
      Block.Preceq (derive_named S.E S.cfg C).F (derive_named S.E S.cfg D).F ∨
      Block.Preceq (derive_named S.E S.cfg D).F (derive_named S.E S.cfg C).F := by
    rcases le_total (derive_named S.E S.cfg C).h_F
        (derive_named S.E S.cfg D).h_F with hCD | hDC
    · have hlt : (derive_named S.E S.cfg C).h_F <
          (derive_named S.E S.cfg D).h :=
        lt_of_le_of_lt (hCD.trans hDorder.heights_ordered)
          hDorder.justified_below_height
      have hCtoD := NamedFinalizationBridge.finalized_preceq_of_height_lt
        S rho D C hsb hroot hD hC hlt
      exact Block.preceq_linear hCtoD hDanchor
    · have hlt : (derive_named S.E S.cfg D).h_F <
          (derive_named S.E S.cfg C).h :=
        lt_of_le_of_lt (hDC.trans hCorder.heights_ordered)
          hCorder.justified_below_height
      have hDtoC := NamedFinalizationBridge.finalized_preceq_of_height_lt
        S rho C D hsb hroot hC hD hlt
      exact Block.preceq_linear hCanchor hDtoC
  simpa only [Block.compatible, Bool.or_eq_true] using hlinear

/-- Agreement at arbitrary honest event-prefix stores follows from their
actual named finalization carriers. This includes distinct prefix indices. -/
theorem stateBefore_finalized_compatible
    (S : Setup V) (rho : NamedRun V)
    (hsb : Internal.NamedOutageEntry.SlashableBound S rho)
    (hroot : NamedRootCollisionFree S rho)
    (i j : Nat) (source target : V)
    (hsource : source ∈ rho.honest) (htarget : target ∈ rho.honest) :
    Block.compatible (NamedRun.stateBefore S rho i source).st.core.F
      (NamedRun.stateBefore S rho j target).st.core.F = true := by
  obtain ⟨C, hCmem, hCF, _⟩ :=
    NamedFinalizationBridge.finalization_carrier_stateBefore S rho i source
  obtain ⟨D, hDmem, hDF, _⟩ :=
    NamedFinalizationBridge.finalization_carrier_stateBefore S rho j target
  have hC : NamedRun.blockInRun S rho C :=
    Proofs.NamedRuntime.blockInRun_of_direct S rho (Or.inr ⟨source, hsource, i, hCmem⟩)
  have hD : NamedRun.blockInRun S rho D :=
    Proofs.NamedRuntime.blockInRun_of_direct S rho (Or.inr ⟨target, htarget, j, hDmem⟩)
  simpa only [hCF, hDF] using finalized_compatible S rho C D hsb hroot hC hD

/-- Strict-time agreement needs sorted events only to identify the two
concrete prefix stores. It imposes no timing gap or delivery assumption. -/
theorem stateBeforeTime_finalized_compatible
    (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho)
    (hsb : Internal.NamedOutageEntry.SlashableBound S rho)
    (hroot : NamedRootCollisionFree S rho)
    (read out : Time) (source target : V)
    (hsource : source ∈ rho.honest) (htarget : target ∈ rho.honest) :
    Block.compatible (NamedRun.stateBeforeTime S rho read source).st.core.F
      (NamedRun.stateBeforeTime S rho out target).st.core.F = true := by
  obtain ⟨i, hi, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho sch.sorted read
  obtain ⟨j, hj, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho sch.sorted out
  rw [hi, hj]
  exact stateBefore_finalized_compatible S rho hsb hroot i j source target
    hsource htarget

end DecoupledConsensusModel.Proofs.NamedFinalityAgreement

end
