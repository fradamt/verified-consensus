module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.FixedHeightRootAdmission
public import DecoupledConsensusProofs.Protocol.Grades.RelativeCarrierWindowGateOff

@[expose] public section

/-!
# The fixed-root relative carrier window

`relativeCarrierWindowAt_of_gateOff` (`RelativeCarrierWindowGateOffRun.lean`)
needs `h_j + 2 ≤ h_max` at the round-`r` action read, and the fixed-height
justification regime carries the opposite, `h_max = h_j + 1`. This module is
that theorem's fixed-root twin: same conclusion, same route, one changed step.

With the gate off, the reader's selected FG root is its finalized block, and
`frontierRoot_preceq_of_gateOff` orders that block below the frontier witness
by an accountable-safety height crossing. With the gate on the selected root
is the justification root instead, so the height crossing is unavailable and
the ordering comes from the fixed target itself:

* one post-GST relay delay pins the selected FG root of **every** honest store
  at both `S.a (r - 1)` and `S.a r` to the one fixed target `J`
  (`fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise`),
  which is where `uniqueAtHeight` is spent;
* the round-`(r - 1)` action carrier is in the filtered tree its own action
  read computed, and that tree is cut at the reader's selected FG root, so
  `J` is below the carrier and hence below the frontier witness `W`;
* the reader's finalized block is below its own selected FG root — the store
  invariant `F ⪯ J` — which is `J` again.

The two remaining inputs of the gate-off route are unchanged: the previous
action store's exact frontier height supplies the frontier witness, and the
common-upper input producer plus the named head relay supply the interpreted
SG input, its body, stamp and lookup.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.NamedOutageEntry
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The round-`r - 1` action carrier is an interpreted input at round `r`'s
phase read while one fixed-height justification root stands. -/
theorem relativeCarrierWindowAt_of_fixedRoot
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest) {r : Round} (hr : 0 < r) {p : Phase}
    {H : Height} {w : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho H w read)
    (hpostRead : S.E.t_GST ≤ read)
    (hpost : S.E.t_GST ≤ S.a (r - 1))
    (hprevDelay : read + S.E.Δ ≤ S.a (r - 1)) (hprevHor : S.a (r - 1) ≤ rho.horizon)
    (hprevCap : honestHMaxAt S rho (S.a (r - 1)) ≤ H)
    (hactionDelay : read + S.E.Δ ≤ S.a r) (hactionHor : S.a r ≤ rho.horizon)
    (hactionCap : honestHMaxAt S rho (S.a r) ≤ H)
    (hhor : domain S.E S.hc r p ≤ rho.horizon) :
    RelativeCarrierWindowAt S rho (r - 1) p := by
  have hsb : Internal.NamedOutageEntry.SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hprevPkg : ∀ q ∈ rho.honest,
      Protocol.get_fg_root
            (rho.storeBeforeTime S q (S.a (r - 1))).toHealing.toFG =
          (rho.storeBeforeTime S w read).J ∧
        (rho.storeBeforeTime S q (S.a (r - 1))).h_max = H := by
    intro q hq
    exact
      fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
        S adm hsb hfix hq hpostRead hprevDelay hprevHor hprevCap
  have hactionPkg : ∀ q ∈ rho.honest,
      Protocol.get_fg_root
            (rho.storeBeforeTime S q (S.a r)).toHealing.toFG =
          (rho.storeBeforeTime S w read).J ∧
        (rho.storeBeforeTime S q (S.a r)).h_max = H := by
    intro q hq
    exact
      fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
        S adm hsb hfix hq hpostRead hactionDelay hactionHor hactionCap
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
  have hsourceHor : S.a (r - 1) ≤ rho.horizon := hprevHor
  intro v hv u hu
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
  obtain ⟨Hb, hHb, hconfirmed⟩ := hhead
  obtain ⟨W, hWbody, hcarrierW, hWheight⟩ :=
    actionSGBlockAt_frontierWitness S adm (hprevPkg u huHon).2
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
  -- The one changed step: the fixed target is below the carrier, hence below
  -- the frontier witness, and the reader's finalized block is below the target.
  have hcarrierFiltered : actionSGBlockAt S rho u (r - 1) ∈
      Protocol.get_filtered_block_tree
        (actionStoreAt S rho u (r - 1)).toHealing.toFG :=
    actionSGBlockAt_mem_filtered_actionStore S adm u (r - 1)
  have hrootCarrier : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S u (S.a (r - 1))).toHealing.toFG)
      (actionSGBlockAt S rho u (r - 1)) := by
    have hmem := Proofs.Records.preceq_get_fg_root_of_mem_filtered hcarrierFiltered
    rwa [actionStoreAt_fgRoot_eq_storeBeforeTime S rho u (r - 1)] at hmem
  have hJcarrier : Block.Preceq (rho.storeBeforeTime S w read).J
      (actionSGBlockAt S rho u (r - 1)) := by
    rw [← (hprevPkg u huHon).1]
    exact hrootCarrier
  have hJW : Block.Preceq (rho.storeBeforeTime S w read).J W.erase :=
    Block.preceq_trans hJcarrier hcarrierW
  have hFroot : Block.Preceq (rho.storeBeforeTime S v (S.a r)).F
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v (S.a r)).toHealing.toFG) :=
    StoreFinality.finalized_preceq_fgRoot
      (st := (rho.storeBeforeTime S v (S.a r)).core)
      (Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
        (S.a r) v)
  have hFfrontier : Block.Preceq
      (rho.storeBeforeTime S v (S.a r)).F W.erase := by
    refine Block.preceq_trans hFroot ?_
    rw [(hactionPkg v hv).1]
    exact hJW
  have hFmono : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) v).st.core.F
      (rho.storeBeforeTime S v (S.a r)).F := by
    exact NamedOutageClosure.incl_strict_F_mono S rho
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v
      (FrameForward.domain_le_a S r p)
  have hFC : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) v).st.core.F W.erase :=
    Block.preceq_trans hFmono hFfrontier
  have hbodySource : Hb ∈
      (NamedRun.stateBeforeTime S rho (S.a (r - 1)) u).st.bodies := by
    have hi' : rho.events[i]? = some (.tick u (S.a (r - 1))) := by
      simpa only [hshape.2.1] using hi
    have hstate := NamedActionSources.action_read_index S rho
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed i u (r - 1) hi'
    change Hb ∈ (NamedRun.stateBefore S rho i u).st.bodies at hHb
    rw [← hstate]
    exact hHb
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
  have hHprefix : Hb ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact hbodySource
  have hDrun : RunBlock S rho D :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S huHon (i := n) hDprefix
  have hHrun : RunBlock S rho Hb :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S huHon (i := n) hHprefix
  have hroot : D.root = Hb.root := by
    rw [← Proofs.NamedWire.erase_root D, hDerase]
    exact Option.some.inj (hshape.2.2.symm.trans hconfirmed)
  have hDH : D = Hb :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective D Hb
      hDrun hHrun D Hb (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self Hb)) hroot
  have hHErase : Hb.erase = actionSGBlockAt S rho u (r - 1) := by
    rw [← hDH, hDerase]
  have hHC : Block.Preceq Hb.erase W.erase := by
    rw [hHErase]
    exact hcarrierW
  have hinput : Protocol.sgVote a.erase ∈
      DecoupledConsensusModel.Protocol.interpretedInputs
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) v).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) v).st.core.F
        S.hc.η_SG r (early S.E S.hc r p) u :=
    by
      have hpostA : S.E.t_GST ≤ S.a a.round := by
        simpa only [hshape.2.1] using hpost
      have hdeadlineA : max (S.a a.round) S.E.t_GST + S.E.Δ ≤
          early S.E S.hc r p := by
        simpa only [hshape.2.1] using hdeadline
      exact action_vote_mem_interpretedInputs_after_gst_common_upper
        S adm.toNamedAdmissibleCore p hk huHon hv
        ⟨hshape.1, hshape.2.1, hemit⟩
        ⟨i, hi, hHb, hconfirmed⟩ hHC hFC hpostA hdeadlineA horder hcut
  have hWtarget : W ∈
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) v).st.bodies ∧
      stampedBefore
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) v).st.core.timestamp_block
        (early S.E S.hc r p) W.erase = true ∧
      Block.find?
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) v).st.core.T W.erase.root =
        some W.erase := by
    exact NamedHealthyHeadReady.healthy_head_body_at_read_after_gst
      S rho adm.toNamedAdmissibleCore u huHon v hv W (S.a (r - 1))
      (early S.E S.hc r p) (domain S.E S.hc r p) hWsource hdeadline horder hcut hFC
  have htargetCore : W.erase ∈
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) v).st.core.T := by
    have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
      (domain S.E S.hc r p) v).1.1.1
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hWtarget.1
  have hcarrierTarget : actionSGBlockAt S rho u (r - 1) ∈
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) v).st.core.T := by
    have hclosed := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
      (domain S.E S.hc r p) v
    exact Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hclosed).2 _ _
      htargetCore hcarrierW
  have hfind : Block.find?
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r p) v).st.core.T
      (actionSGBlockAt S rho u (r - 1)).root =
      some (actionSGBlockAt S rho u (r - 1)) := by
    apply Proofs.Optimistic.find?_eq_some_of_unique hcarrierTarget
    intro Y hY hYroot
    obtain ⟨Yn, hYerase, hYrun⟩ :=
      Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv
        (domain S.E S.hc r p) hY
    have hYHroot : Yn.root = Hb.root := by
      rw [← Proofs.NamedWire.erase_root Yn, hYerase, hYroot, ← hHErase,
        Proofs.NamedWire.erase_root Hb]
    have hYH := adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      Yn Hb hYrun hHrun Yn Hb (Or.inl (Proofs.NamedAncestry.named_self Yn))
      (Or.inr (Proofs.NamedAncestry.named_self Hb)) hYHroot
    rw [← hYerase, hYH, hHErase]
  change ∃ y ∈ DecoupledConsensusModel.Protocol.interpretedInputs
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc ((r - 1) + 1) p) v).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc ((r - 1) + 1) p) v).st.core.F
      S.hc.η_SG ((r - 1) + 1) (early S.E S.hc ((r - 1) + 1) p) u,
    y.round = r - 1 ∧
      y.confirmed = some (actionSGBlockAt S rho u (r - 1)).root ∧
      Block.find?
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc ((r - 1) + 1) p) v).st.core.T
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

end
