module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.PreparedV4PhaseShiftSafety
public import DecoupledConsensusProofs.Execution.HandoverPreparedV4Direct
public import DecoupledConsensusProofs.Objects.HandoverPreparedV4Transfer
public import DecoupledConsensusProofs.Execution.PreparedV4Finality
public import DecoupledConsensusProofs.Generic.BoundedSafetyCompletePins

@[expose] public section

/-! # Bounded phase safety from the prepared V4 latest-seed pin -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]


theorem preparedV4_postCutSelection_of_le {S : Setup V} {rho : Run V}
    {c c' : Round} (h : c ≤ c') {B : Block V}
    (hsel : PostCutSelection S rho c' B) : PostCutSelection S rho c B := by
  obtain ⟨v, hv, q, hq, hqhor, hB⟩ := hsel
  refine ⟨v, hv, q, ?_, hqhor, hB⟩
  exact (by
    simpa only [Protocol.HealConfig.opening_slot] using
      Nat.mul_le_mul_right S.hc.R h : S.hc.opening_slot c ≤ S.hc.opening_slot c').trans hq

/-- The phase-shift record only weakens when its cut round grows. -/
theorem preparedV4_phaseShiftSafety_mono_cut {S : Setup V} {rho : Run V}
    {c c' : Round} {start : Slot} {P : Block V} (h : c ≤ c')
    (hp : PhaseShiftSafety S rho c start P) : PhaseShiftSafety S rho c' start P where
  finality := hp.finality
  userConfirmation := hp.userConfirmation
  refreshedLatest :=
    { compatible := fun u hu v hv t t' ht ht' hs hs' =>
        hp.refreshedLatest.compatible u hu v hv t t' ht ht'
          (preparedV4_postCutSelection_of_le h hs)
          (preparedV4_postCutSelection_of_le h hs')
      finalityRoot := fun u hu v hv t ht hthor hs =>
        hp.refreshedLatest.finalityRoot u hu v hv t ht hthor
          (preparedV4_postCutSelection_of_le h hs) }
  liveMonotone := hp.liveMonotone
  liveCompatible := fun last hlast hstart t u ht hu htl hul v hv w hw =>
    hp.liveCompatible last hlast hstart t u
      ((Assembly.a_mono S h).trans ht) ((Assembly.a_mono S h).trans hu) htl hul v hv w hw
  genuine := hp.genuine
  liveAtConfirmation := fun s hs hshor u hu v hv t ht hts =>
    hp.liveAtConfirmation s hs hshor u hu v hv t ((Assembly.a_mono S h).trans ht) hts
  seedAtVote := hp.seedAtVote
  liveAtVote := fun d hd hdhor u hu v hv t ht hthor htd =>
    hp.liveAtVote d hd hdhor u hu v hv t ((Assembly.a_mono S h).trans ht) hthor htd
  honestProposalLive := hp.honestProposalLive
  honestProposalReads := hp.honestProposalReads

private theorem preparedV4_awakeWindows_of_prefix
    (S : Setup V) {source rho : Run V} (adm : Admissible S source)
    {lastStrong : Round} (hprefix : source.horizon = S.a lastStrong)
    (hretain : rho.honest ⊆ source.honest)
    (hcovered : S.a lastStrong ≤ rho.horizon)
    (hawake : ∀ r, lastStrong < r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r) :
    ∀ r, 0 < r → S.E.t_GST ≤ S.a (r - 1) →
      S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r := by
  have hmajority : HonestWeightMajority S rho.honest :=
    WeakSG.honestWeightMajority_of_awakeWindowMajority S
      (hawake (lastStrong + 1) (Nat.lt_succ_self _)
        (by simpa only [Nat.add_sub_cancel] using hcovered))
  intro r hr hpostPrev hhor
  by_cases hafter : lastStrong < r
  · exact hawake r hafter hhor
  have heq : honestAwakeWindow (fun v => (S.node v).awake)
      rho.honest S.hc.η_SG r = rho.honest := by
    apply Finset.Subset.antisymm
      (WeakSG.honestAwakeWindow_subset _ _ _ _)
    intro v hv
    refine WeakSG.mem_honestAwakeWindow_iff.mpr
      ⟨hv, r - 1,
        pred_mem_latest_window S.hc.η_SG r S.hc.η_SG_ge_one hr, ?_⟩
    apply adm.all_awake v (hretain hv) (r - 1) hpostPrev
    change S.a (r - 1) ≤ source.horizon
    rw [hprefix]
    exact Assembly.a_mono S
      ((Nat.sub_le r 1).trans (Nat.le_of_not_gt hafter))
  unfold AwakeWindowMajority
  rw [heq]
  exact hmajority




theorem preparedV4_awakeWindows_of_prefix_core
    (S : Setup V) {source rho : Run V} (adm : Admissible S source)
    {lastStrong : Round} (hprefix : source.horizon = S.a lastStrong)
    (hretain : rho.honest ⊆ source.honest)
    (hcovered : S.a lastStrong ≤ rho.horizon)
    (hawake : ∀ r, lastStrong < r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r) :
    ∀ r, 0 < r → S.E.t_GST ≤ S.a (r - 1) →
      S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r :=
  preparedV4_awakeWindows_of_prefix S adm hprefix hretain hcovered hawake

#print axioms preparedV4_awakeWindows_of_prefix_core

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
