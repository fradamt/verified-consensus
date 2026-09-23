module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.AlignedRoundLemmas
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
public import DecoupledConsensusProofs.Protocol.Grades.RelativeSupporter
public import DecoupledConsensusProofs.Protocol.Grades.RelativeOneChain
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedActivity
public import DecoupledConsensusProofs.Protocol.Grades.HealthyHeadReady
public import DecoupledConsensusProofs.Protocol.Grades.FrameForward
public import DecoupledConsensusProofs.Protocol.Grades.Inclusions

@[expose] public section

/-!
# Gate-off relative carrier window

The source route is the existing earlier body-ready route. The gate-off frontier
witness is its common upper block: the previous action carrier is below that
witness, and the current finalized root is below it. The common-upper input
producer then supplies the interpreted SG input and the existing named head
relay supplies its body, stamp, and lookup.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.NamedOutageEntry
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Grade formation input -/

/-- Full participation turns the global adversarial bound into grade formation. -/
theorem gradeFormingMajority_of_admissible_belowOneThird
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest) {r : Round} (hr : 0 < r)
    (hhor : domain S.E S.hc r .g2 ≤ rho.horizon)
    (hpost : S.E.t_GST ≤ S.a (r - 1)) :
    GradeFormingMajority S rho r := by
  have hq : HonestWeightMajority S rho.honest :=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hfb
  have hprev : S.a (r - 1) ≤ rho.horizon :=
    (NamedOutageClosure.action_le_domain S S.hc.R_ge_three
      (Nat.sub_lt hr (by decide))).trans hhor
  have hvoters : honestRoundVoters S rho (r - 1) = rho.honest := by
    apply Finset.Subset.antisymm
    · intro v hv
      exact ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho v (r - 1)).mp hv).1
    · intro v hv
      apply (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho v (r - 1)).mpr
      have hemit := honest_emits_exact_actionAttestationAt S adm hv (r - 1) hprev hpost
      have hshape := actionAttestationAt_shape S rho v (r - 1)
      exact ⟨hv, actionAttestationAt S rho v (r - 1), hshape.1,
        hshape.2.1, hemit⟩
  have hhistorical : historicalHonestVoters S rho r ⊆ rho.honest := by
    intro v hv
    obtain ⟨k, _, hvote⟩ := Finset.mem_biUnion.mp hv
    exact ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho v k).mp hvote).1
  have hstale : staleHistoricalVoters S rho r = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro v hv
    have hvoter : v ∈ honestRoundVoters S rho (r - 1) := by
      rw [hvoters]
      exact hhistorical (Finset.mem_sdiff.mp hv).1
    exact (Finset.mem_sdiff.mp hv).2 hvoter
  unfold GradeFormingMajority
  rw [hvoters, hstale, Finset.union_empty]
  exact hq

/-! ## The gate-off carrier window -/

/-- The round-`r - 1` action carrier is an interpreted input at round `r`'s
phase read under the gate-off frontier hypotheses. -/
theorem relativeCarrierWindowAt_of_gateOff
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest) {r : Round} (hr : 0 < r)
    {p : Phase} {M : Height} (hpost : S.E.t_GST ≤ S.a (r - 1))
    (hprev : ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (r - 1))).h_max = M)
    (hfrontier : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a r)).h_max = M)
    (hgateOff : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a r)).h_j + 2 ≤ M)
    (hhor : domain S.E S.hc r p ≤ rho.horizon) :
    RelativeCarrierWindowAt S rho (r - 1) p := by
  have hsb : Internal.NamedOutageEntry.SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hqr : r - 1 < r := Nat.sub_lt hr (by decide)
  have hk : r - 1 ∈ Protocol.latest_window S.hc.η_SG r := by
    apply NamedOutageClosure.mem_latest_window
    · exact Nat.sub_le_sub_left S.hc.η_SG_ge_one r
    · exact hqr
  have hpred : r - 1 + 1 = r := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hr)
  have hdeadline : max (S.a (r - 1)) S.E.t_GST + S.E.Δ ≤
      early S.E S.hc r p := by
    rw [max_eq_left hpost]
    apply (NamedOutageClosure.action_delta_le_early
      S S.hc.R_ge_three hqr).trans
    cases p <;> simp only [early, Phase.earlyOffset] <;>
      linarith [S.E.Δ_pos]
  have horder : early S.E S.hc r p ≤ domain S.E S.hc r p :=
    by
      cases p <;> simp only [early, domain, Phase.earlyOffset,
        Phase.domainOffset] <;> linarith [S.E.Δ_pos]
  have hcut : early S.E S.hc r p ≤ rho.horizon := horder.trans hhor
  have hdomainG2P : domain S.E S.hc r .g2 ≤ domain S.E S.hc r p := by
    cases p <;> simp only [domain, Phase.domainOffset] <;>
      linarith [S.E.Δ_pos]
  have hsourceHor : S.a (r - 1) ≤ rho.horizon :=
    (NamedOutageClosure.action_le_domain S S.hc.R_ge_three hqr).trans
      (hdomainG2P.trans hhor)
  intro w hw u hu
  have huHon : u ∈ rho.honest :=
    ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u (r - 1)).mp hu).1
  let a := actionAttestationAt S rho u (r - 1)
  have hshape : a.val_index = u ∧ a.round = r - 1 ∧
      a.confirmed = some (actionSGBlockAt S rho u (r - 1)).root := by
    simpa only [a] using actionAttestationAt_shape S rho u (r - 1)
  have hemit : NamedRun.emits S rho u (Object.attest a) (S.a (r - 1)) := by
    simpa only [a] using
      honest_emits_exact_actionAttestationAt S adm huHon (r - 1) hsourceHor (by assumption)
  obtain ⟨i, hi, _, hhead⟩ := Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
  dsimp at hhead
  obtain ⟨H, hH, hconfirmed⟩ := hhead
  obtain ⟨W, hWbody, hcarrierW, hWheight⟩ :=
    actionSGBlockAt_frontierWitness S adm (hprev u huHon)
  have hWsource : W ∈
      (rho.storeBeforeTime S u (S.a (r - 1))).bodies := by
    simpa only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
      NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hWbody
  have hWrun : RunBlock S rho W := by
    obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.a (r - 1))
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S huHon (i := n)
    rw [← hn]
    exact hWsource
  have hrootW : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w (S.a r)).toHealing.toFG) W.erase :=
    frontierRoot_preceq_of_gateOff S adm hsb hw
      (X := W.erase) (Xn := W) rfl hWrun hWheight
      (hfrontier w hw) (hgateOff w hw)
  have hgate : ¬ (rho.storeBeforeTime S w (S.a r)).h_max =
      (rho.storeBeforeTime S w (S.a r)).h_j + 1 := by
    apply Nat.ne_of_gt
    rw [hfrontier w hw]
    exact Nat.lt_of_succ_le (by
      simpa only [Nat.add_assoc] using hgateOff w hw)
  have hrootF : Protocol.get_fg_root
      (rho.storeBeforeTime S w (S.a r)).toHealing.toFG =
      (rho.storeBeforeTime S w (S.a r)).F := by
    simp only [Protocol.get_fg_root, Protocol.Store.toHealing, if_neg hgate]
  have hFmono : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) w).st.core.F
      (rho.storeBeforeTime S w (S.a r)).F := by
    exact NamedOutageClosure.incl_strict_F_mono S rho
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed w
      (FrameForward.domain_le_a S r p)
  have hFfrontier : Block.Preceq
      (rho.storeBeforeTime S w (S.a r)).F W.erase := by
    rw [← hrootF]
    exact hrootW
  have hFC : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) w).st.core.F W.erase :=
    Block.preceq_trans hFmono hFfrontier
  have hbodySource : H ∈
      (NamedRun.stateBeforeTime S rho (S.a (r - 1)) u).st.bodies := by
    have hi' : rho.events[i]? = some (.tick u (S.a (r - 1))) := by
      simpa only [hshape.2.1] using hi
    have hstate := NamedActionSources.action_read_index S rho
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed i u (r - 1) hi'
    change H ∈ (NamedRun.stateBefore S rho i u).st.bodies at hH
    rw [← hstate]
    exact hH
  have hcarrierMem : actionSGBlockAt S rho u (r - 1) ∈
      (NamedRun.stateBeforeTime S rho (S.a (r - 1)) u).st.core.T := by
    exact actionSGBlockAt_mem_storeBeforeTime S rho u (r - 1)
  obtain ⟨D, hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (S.a (r - 1)) u hcarrierMem
  obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted (S.a (r - 1))
  have hDprefix : D ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact hDbody
  have hHprefix : H ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact hbodySource
  have hDrun : RunBlock S rho D :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S huHon (i := n) hDprefix
  have hHrun : RunBlock S rho H :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S huHon (i := n) hHprefix
  have hroot : D.root = H.root := by
    rw [← Proofs.NamedWire.erase_root D, hDerase]
    exact Option.some.inj (hshape.2.2.symm.trans hconfirmed)
  have hDH : D = H :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective D H
      hDrun hHrun D H (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self H)) hroot
  have hHErase : H.erase = actionSGBlockAt S rho u (r - 1) := by
    rw [← hDH, hDerase]
  have hHC : Block.Preceq H.erase W.erase := by
    rw [hHErase]
    exact hcarrierW
  have hinput : Protocol.sgVote a.erase ∈
      DecoupledConsensusModel.Protocol.interpretedInputs
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) w).st.core.F
        S.hc.η_SG r (early S.E S.hc r p) u :=
    by
      have hpostA : S.E.t_GST ≤ S.a a.round := by
        simpa only [hshape.2.1] using hpost
      have hdeadlineA : max (S.a a.round) S.E.t_GST + S.E.Δ ≤
          early S.E S.hc r p := by
        simpa only [hshape.2.1] using hdeadline
      exact action_vote_mem_interpretedInputs_after_gst_common_upper
        S adm.toNamedAdmissibleCore p hk huHon hw
        ⟨hshape.1, hshape.2.1, hemit⟩
        ⟨i, hi, hH, hconfirmed⟩ hHC hFC hpostA hdeadlineA horder hcut
  have hWtarget : W ∈
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) w).st.bodies ∧
      stampedBefore
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) w).st.core.timestamp_block
        (early S.E S.hc r p) W.erase = true ∧
      Block.find?
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) w).st.core.T W.erase.root =
        some W.erase := by
    exact NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
      S rho adm.toNamedAdmissibleCore u huHon w hw W (S.a (r - 1))
      (early S.E S.hc r p) (domain S.E S.hc r p) hWsource hdeadline horder hcut hFC
  have htargetCore : W.erase ∈
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) w).st.core.T := by
    have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
      (domain S.E S.hc r p) w).1.1.1
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hWtarget.1
  have hcarrierTarget : actionSGBlockAt S rho u (r - 1) ∈
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) w).st.core.T := by
    have hclosed := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
      (domain S.E S.hc r p) w
    exact Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hclosed).2 _ _
      htargetCore hcarrierW
  have hfind : Block.find?
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) w).st.core.T
      (actionSGBlockAt S rho u (r - 1)).root =
      some (actionSGBlockAt S rho u (r - 1)) := by
    apply Proofs.Optimistic.find?_eq_some_of_unique hcarrierTarget
    intro Y hY hYroot
    obtain ⟨Yn, hYerase, hYrun⟩ :=
      Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hw
        (domain S.E S.hc r p) hY
    have hYHroot : Yn.root = H.root := by
      rw [← Proofs.NamedWire.erase_root Yn, hYerase, hYroot, ← hHErase,
        Proofs.NamedWire.erase_root H]
    have hYH := adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      Yn H hYrun hHrun Yn H (Or.inl (Proofs.NamedAncestry.named_self Yn))
      (Or.inr (Proofs.NamedAncestry.named_self H)) hYHroot
    rw [← hYerase, hYH, hHErase]
  change ∃ y ∈ DecoupledConsensusModel.Protocol.interpretedInputs
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc ((r - 1) + 1) p) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc ((r - 1) + 1) p) w).st.core.F
      S.hc.η_SG ((r - 1) + 1) (early S.E S.hc ((r - 1) + 1) p) u,
    y.round = r - 1 ∧
      y.confirmed = some (actionSGBlockAt S rho u (r - 1)).root ∧
      Block.find?
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc ((r - 1) + 1) p) w).st.core.T
        (actionSGBlockAt S rho u (r - 1)).root =
          some (actionSGBlockAt S rho u (r - 1))
  refine ⟨Protocol.sgVote a.erase, ?_, ?_⟩
  · simpa only [hpred] using hinput
  refine ⟨?_, ?_, ?_⟩
  · simpa only [NamedOutageClosure.sgVote_round] using hshape.2.1
  · rw [NamedOutageClosure.sgVote_confirmed, hshape.2.2]
  · simpa only [hpred] using hfind

end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms gradeFormingMajority_of_admissible_belowOneThird
#print axioms relativeCarrierWindowAt_of_gateOff
end DecoupledConsensusModel.Proofs.HealingSurface

end
