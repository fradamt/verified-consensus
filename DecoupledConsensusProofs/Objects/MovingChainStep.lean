module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.MovingChainState
public import DecoupledConsensusProofs.Generic.CanonicalSuffix
public import DecoupledConsensusProofs.Protocol.ChainState.JustificationCertificates

@[expose] public section

/-!
# Moving-frontier roots and completion

This module puts every selected FG root on the endpoint chain after two rises.
It also exports a completed moving-frontier event fold to the public
proposal-chain suffix. The endpoint is clipped at the completed cursor. Thus,
it stays constant after the finite run event list, where no canonical
observation can occur.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]


/-- An event before the strict cursor of `t` happened before `t`. The cursor
is the length of the `< t` filter, and the schedule's key order makes that
filter a prefix of the event list. -/
theorem time_lt_of_index_lt_strictEventIndex
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {t : Time} {j : Nat} {e : Event V}
    (hj : j < strictEventIndex rho t)
    (hget : rho.events[j]? = some e) : e.time < t := by
  have hfilt : rho.events.filter (fun x => decide (x.time < t)) =
      rho.events.take (strictEventIndex rho t) := by
    simpa only [strictEventIndex] using
      Proofs.Optimistic.filter_eq_take S sch _ (Proofs.Optimistic.downward_lt t)
  have hmem : e ∈ rho.events.take (strictEventIndex rho t) := by
    refine List.mem_of_getElem? (i := j) ?_
    rw [List.getElem?_take_of_lt hj]
    exact hget
  rw [← hfilt] at hmem
  simpa only [decide_eq_true_eq] using (List.mem_filter.mp hmem).2



/-
/-- Event-prefix form of `newRoot_on_endpointChain`. It applies immediately
after any admission event because it reads the exact post-event prefix store.
-/
theorem MovingFrontierChainState.newRoot_on_endpointChainAtIndex
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {n0 i: Nat} {End: Nat → Block V}
    (h: MovingFrontierChainState S rho t1 M0 n0 i End)
    {k: Nat} (hki: k ≤ i) {v: V} (hv: v ∈ rho.honest)
    (htwoRises: M0 + 2 ≤ (rho.stateBefore S k v).st.h_max):
    Block.Preceq
      (Protocol.get_fg_root
        (rho.stateBefore S k v).st.toHealing.toFG) (End i):= by
  let st:= (rho.stateBefore S k v).st
  change M0 + 2 ≤ st.h_max at htwoRises
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node v) st:= by
    simpa only [st] using
      (Proofs.Bridges.depReachable_of_admissible
        S adm.toDeliveryWellFormed v k)
  have hbelow: st.h_j < st.h_max:=
    FixedHeightRootCore.justificationBelowMax_depReachable
      S.E S.hc S.cfg (S.node v) hdep
  have hmajority: HonestWeightMajority S rho.honest:=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S:= S) hfb
  have hsb: SlashableBound S rho:=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hlocal: st.h_max ≤ honestHMaxBeforeIndex S rho i:= by
    have hlocalK: st.h_max ≤ honestHMaxBeforeIndex S rho k:= by
      simpa only [st] using
        localHMax_le_honestHMaxBeforeIndex S rho k hv
    exact hlocalK.trans (honestHMaxBeforeIndex_mono S rho hki)
  have hendFloor: st.h_max - 1 ≤
      (derived_state S.E S.cfg (End i)).h:= by
    exact (Nat.sub_le_sub_right hlocal 1).trans
      (h.frontier_sub_one_le_endpointHeight S adm hmajority)
  have hEndRun: RunBlock S rho (End i):=
    h.endpointRun i h.start_le (Nat.le_refl i)
  by_cases hgate: st.h_max = st.h_j + 1
  · have hhjHigh: M0 < st.h_j:= by
      have htwo': M0 + 1 + 1 ≤ st.h_j + 1:= by
        simpa only [Nat.add_assoc] using htwoRises.trans_eq hgate
      exact Nat.lt_iff_add_one_le.mpr
        (Nat.le_of_add_le_add_right htwo')
    obtain ⟨C, hC, hhj, hJ⟩:=
      (Proofs.Bridges.provenance_depReachable
        S.E S.hc S.cfg (S.node v) hdep).2
    have hhjNe: (derived_state S.E S.cfg C).h_j ≠ 0:= by
      rw [hhj]
      exact Nat.ne_of_gt (Nat.zero_lt_of_lt hhjHigh)
    obtain ⟨Q, hQ, hwit⟩:=
      AlignedRoundLemmas.justification_certificate
        S.E S.cfg C hhjNe
    obtain ⟨signer, hsignerQ, hsignerHonest⟩:=
      HonestWeightMajority.exists_honest_member_of_quorum hmajority hQ
    obtain ⟨a, haC, haSigner, haPair⟩:= hwit signer hsignerQ
    have haHonest: a.val_index ∈ rho.honest:= by
      rw [haSigner]
      exact hsignerHonest
    have haTarget:
        a.height_pair = HeightPair.target st.h_j st.J.root:= by
      rw [← hhj, ← hJ]
      exact haPair
    obtain ⟨j, _ta, hjk, hjevent, hja, _hemit⟩:=
      honestCarriedAttestation_emittedBeforeIndex
        S adm (by simpa only [st] using hC) haC haHonest
    have hJmem: st.J ∈ st.T:=
      Proofs.Records.justifiedInTree_depReachable
        S.E S.hc S.cfg (S.node v) st hdep
    have hJrun: RunBlock S rho st.J:= by
      apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i:= k)
      simpa only [st] using hJmem
    simp only [Protocol.get_fg_root, Protocol.Store.toHealing,
      if_pos (by simpa only [st] using hgate)]
    by_cases hj0: j < n0
    · exact h.preCutoffTarget_preceq_endpoint S adm.toScheduleWellFormed
        haHonest hjevent hja hj0
        ((Nat.sub_le M0 1).trans (Nat.le_of_lt hhjHigh)) haTarget hJrun rfl
    · have hn0j: n0 ≤ j:= Nat.le_of_not_gt hj0
      have hji: j < i:= lt_of_lt_of_le hjk hki
      have hJnext: Block.Preceq st.J (End (j + 1)):=
        (h.outputs j hn0j hji).targets
          haHonest hjevent hja st.h_j st.J.root haTarget
          st.J hJrun rfl
      exact Block.preceq_trans hJnext
        (h.endpoint_mono (hn0j.trans (Nat.le_succ j))
          (Nat.succ_le_iff.mpr hji) (Nat.le_refl i))
  · have hgateOff: st.h_j + 2 ≤ st.h_max:= by
      have hsucc: st.h_j + 1 ≤ st.h_max:=
        Nat.succ_le_iff.mpr hbelow
      have hstrict: st.h_j + 1 < st.h_max:=
        lt_of_le_of_ne hsucc (fun heq => hgate heq.symm)
      simpa only [Nat.add_assoc] using Nat.succ_le_iff.mpr hstrict
    have hhjlt: st.h_j < st.h_max - 1:= by
      rw [Nat.lt_sub_iff_add_lt]
      exact Nat.lt_of_succ_le (by
        simpa only [Nat.add_assoc] using hgateOff)
    have hnoHigh: NoHighJustifications S.E S.cfg st:=
      FixedHeightRootCore.noHighJustifications_depReachable
        S.E S.hc S.cfg (S.node v) hdep
    obtain ⟨C, hC, hF⟩:=
      Proofs.Bridges.storeFinalizationOnChain_depReachable
        S.E S.hc S.cfg (S.node v) hdep
    have hCrun: RunBlock S rho C:= by
      apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i:= k)
      simpa only [st] using hC
    have hcrossed: (derived_state S.E S.cfg C).h_F <
        (derived_state S.E S.cfg (End i)).h:= by
      calc
        (derived_state S.E S.cfg C).h_F ≤
            (derived_state S.E S.cfg C).h_j:=
          (Protocol.chainOrder_derived_state S.E S.cfg C).heights_ordered
        _ ≤ st.h_j:= hnoHigh C hC
        _ < st.h_max - 1:= hhjlt
        _ ≤ (derived_state S.E S.cfg (End i)).h:= hendFloor
    have hFEnd: Block.Preceq st.F (End i):= by
      have hpre: Block.Preceq (derived_state S.E S.cfg C).F (End i):=
        Protocol.finalized_preceq_of_height_lt hsb hCrun hEndRun
          (adm.toRootCollisionFree.root_injective (End i) C hEndRun hCrun)
          ⟨rfl, rfl⟩ hcrossed
      simpa only [hF] using hpre
    simp only [Protocol.get_fg_root, Protocol.Store.toHealing,
      if_neg (by simpa only [st] using hgate)]
    exact hFEnd

/-- **The index form of the root bound, with no rise premise.**

Same conclusion as `newRoot_on_endpointChainAtIndex`, from the moving state's
own boundary fields instead of two public height rises. The read index must be
at or after the history cutoff, which every read the fold performs is. -/
theorem MovingFrontierChainState.newRoot_on_endpointChainAtIndex_of_start
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {n0 i: Nat} {End: Nat → Block V}
    (h: MovingFrontierChainState S rho t1 M0 n0 i End)
    {k: Nat} (hn0k: n0 ≤ k) (hki: k ≤ i) {v: V} (hv: v ∈ rho.honest):
    Block.Preceq
      (Protocol.get_fg_root
        (rho.stateBefore S k v).st.toHealing.toFG) (End i):= by
  let st:= (rho.stateBefore S k v).st
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node v) st:= by
    simpa only [st] using
      (Proofs.Bridges.depReachable_of_admissible
        S adm.toDeliveryWellFormed v k)
  have hbelow: st.h_j < st.h_max:=
    FixedHeightRootCore.justificationBelowMax_depReachable
      S.E S.hc S.cfg (S.node v) hdep
  have hmajority: HonestWeightMajority S rho.honest:=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S:= S) hfb
  have hsb: SlashableBound S rho:=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hlocal: st.h_max ≤ honestHMaxBeforeIndex S rho i:= by
    have hlocalK: st.h_max ≤ honestHMaxBeforeIndex S rho k:= by
      simpa only [st] using
        localHMax_le_honestHMaxBeforeIndex S rho k hv
    exact hlocalK.trans (honestHMaxBeforeIndex_mono S rho hki)
  have hendFloor: st.h_max - 1 ≤
      (derived_state S.E S.cfg (End i)).h:= by
    exact (Nat.sub_le_sub_right hlocal 1).trans
      (h.frontier_sub_one_le_endpointHeight S adm hmajority)
  have hEndRun: RunBlock S rho (End i):=
    h.endpointRun i h.start_le (Nat.le_refl i)
  have hfloorM: M0 ≤ st.h_max:= by
    simpa only [st] using h.frontierFloor v hv k hn0k
  obtain ⟨C, hC, hhj, hJ⟩:=
    (Proofs.Bridges.provenance_depReachable
      S.E S.hc S.cfg (S.node v) hdep).2
  have hJmem: st.J ∈ st.T:=
    Proofs.Records.justifiedInTree_depReachable
      S.E S.hc S.cfg (S.node v) st hdep
  have hJrun: RunBlock S rho st.J:= by
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i:= k)
    simpa only [st] using hJmem
  by_cases hgate: st.h_max = st.h_j + 1
  · refine h.gateOnRoot_preceq_of_boundary S adm hhj hJ hJrun
      hfloorM hgate ?_
    intro hz
    have hhjNe: (derived_state S.E S.cfg C).h_j ≠ 0:= by
      rw [hhj]
      exact hz
    obtain ⟨Q, hQ, hwit⟩:=
      AlignedRoundLemmas.justification_certificate
        S.E S.cfg C hhjNe
    obtain ⟨signer, hsignerQ, hsignerHonest⟩:=
      HonestWeightMajority.exists_honest_member_of_quorum hmajority hQ
    obtain ⟨a, haC, haSigner, haPair⟩:= hwit signer hsignerQ
    have haHonest: a.val_index ∈ rho.honest:= by
      rw [haSigner]
      exact hsignerHonest
    have haTarget:
        a.height_pair = HeightPair.target st.h_j st.J.root:= by
      rw [← hhj, ← hJ]
      exact haPair
    obtain ⟨j, ta, hjk, hjevent, hja, _hemit⟩:=
      honestCarriedAttestation_emittedBeforeIndex
        S adm (by simpa only [st] using hC) haC haHonest
    exact ⟨a, ta, j, haHonest, hjevent, hja, haTarget,
      lt_of_lt_of_le hjk hki⟩
  · have hgateOff: st.h_j + 2 ≤ st.h_max:= by
      have hsucc: st.h_j + 1 ≤ st.h_max:=
        Nat.succ_le_iff.mpr hbelow
      have hstrict: st.h_j + 1 < st.h_max:=
        lt_of_le_of_ne hsucc (fun heq => hgate heq.symm)
      simpa only [Nat.add_assoc] using Nat.succ_le_iff.mpr hstrict
    have hhjlt: st.h_j < st.h_max - 1:= by
      rw [Nat.lt_sub_iff_add_lt]
      exact Nat.lt_of_succ_le (by
        simpa only [Nat.add_assoc] using hgateOff)
    have hnoHigh: NoHighJustifications S.E S.cfg st:=
      FixedHeightRootCore.noHighJustifications_depReachable
        S.E S.hc S.cfg (S.node v) hdep
    obtain ⟨C, hC, hF⟩:=
      Proofs.Bridges.storeFinalizationOnChain_depReachable
        S.E S.hc S.cfg (S.node v) hdep
    have hCrun: RunBlock S rho C:= by
      apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i:= k)
      simpa only [st] using hC
    have hcrossed: (derived_state S.E S.cfg C).h_F <
        (derived_state S.E S.cfg (End i)).h:= by
      calc
        (derived_state S.E S.cfg C).h_F ≤
            (derived_state S.E S.cfg C).h_j:=
          (Protocol.chainOrder_derived_state S.E S.cfg C).heights_ordered
        _ ≤ st.h_j:= hnoHigh C hC
        _ < st.h_max - 1:= hhjlt
        _ ≤ (derived_state S.E S.cfg (End i)).h:= hendFloor
    have hFEnd: Block.Preceq st.F (End i):= by
      have hpre: Block.Preceq (derived_state S.E S.cfg C).F (End i):=
        Protocol.finalized_preceq_of_height_lt hsb hCrun hEndRun
          (adm.toRootCollisionFree.root_injective (End i) C hEndRun hCrun)
          ⟨rfl, rfl⟩ hcrossed
      simpa only [hF] using hpre
    simp only [Protocol.get_fg_root, Protocol.Store.toHealing,
      if_neg (by simpa only [st] using hgate)]
    exact hFEnd


/-- **The time form of the root bound, with no rise premise.**

The read store at `t` is the prefix store at the strict cursor of `t`, and
`t1 ≤ t` puts that cursor at or after the history cutoff. -/
theorem MovingFrontierChainState.newRoot_on_endpointChain_of_start
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {n0 i: Nat} {End: Nat → Block V}
    (h: MovingFrontierChainState S rho t1 M0 n0 i End)
    {t: Time} {v: V} (hv: v ∈ rho.honest)
    (hcursor: strictEventIndex rho t ≤ i)
    (hstart: t1 ≤ t):
    Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v t).toHealing.toFG) (End i):= by
  have hn0k: n0 ≤ strictEventIndex rho t:= by
    rw [h.historyStart]
    exact strictEventIndex_mono rho hstart
  have hres:= h.newRoot_on_endpointChainAtIndex_of_start S adm hfb
    hn0k hcursor hv
  rw [← storeBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toScheduleWellFormed v t] at hres
  exact hres

/-- After two rises above the fixed old-frontier bound, every honest selected
FG root is an ancestor of the current moving endpoint.

In the gate-on branch, the justification certificate has an honest target
row. Its emission cannot be before the history cursor because its height is
above `M0`; the moving output history therefore puts `J` below the endpoint.
In the gate-off branch, the justification is at least two heights below the
frontier, so accountable finality crossing puts `F` below the endpoint. -/
theorem MovingFrontierChainState.newRoot_on_endpointChain
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {n0 i: Nat} {End: Nat → Block V}
    (h: MovingFrontierChainState S rho t1 M0 n0 i End)
    {t: Time} {v: V} (hv: v ∈ rho.honest)
    (hcursor: strictEventIndex rho t ≤ i)
    (htwoRises: M0 + 2 ≤ (rho.storeBeforeTime S v t).h_max):
    Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v t).toHealing.toFG) (End i):= by
  let st:= rho.storeBeforeTime S v t
  change M0 + 2 ≤ st.h_max at htwoRises
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node v) st:= by
    simpa only [st, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed t v)
  have hbelow: st.h_j < st.h_max:=
    FixedHeightRootCore.justificationBelowMax_depReachable
      S.E S.hc S.cfg (S.node v) hdep
  have hmajority: HonestWeightMajority S rho.honest:=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S:= S) hfb
  have hsb: SlashableBound S rho:=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hlocal: st.h_max ≤ honestHMaxBeforeIndex S rho i:= by
    have hlocalStrict: st.h_max ≤
        honestHMaxBeforeIndex S rho (strictEventIndex rho t):= by
      have hlocal':= localHMax_le_honestHMaxBeforeIndex
        S rho (strictEventIndex rho t) hv
      rw [← storeBeforeTime_eq_stateBefore_strictEventIndex
        S adm.toScheduleWellFormed v t] at hlocal'
      simpa only [st] using hlocal'
    exact hlocalStrict.trans
      (honestHMaxBeforeIndex_mono S rho hcursor)
  have hendFloor: st.h_max - 1 ≤
      (derived_state S.E S.cfg (End i)).h:= by
    exact (Nat.sub_le_sub_right hlocal 1).trans
      (h.frontier_sub_one_le_endpointHeight S adm hmajority)
  have hEndRun: RunBlock S rho (End i):=
    h.endpointRun i h.start_le (Nat.le_refl i)
  by_cases hgate: st.h_max = st.h_j + 1
  · have hhjHigh: M0 < st.h_j:= by
      have htwo': M0 + 1 + 1 ≤ st.h_j + 1:= by
        simpa only [Nat.add_assoc] using htwoRises.trans_eq hgate
      exact Nat.lt_iff_add_one_le.mpr
        (Nat.le_of_add_le_add_right htwo')
    obtain ⟨C, hC, hhj, hJ⟩:=
      (Proofs.Bridges.provenance_depReachable
        S.E S.hc S.cfg (S.node v) hdep).2
    have hhjNe: (derived_state S.E S.cfg C).h_j ≠ 0:= by
      rw [hhj]
      exact Nat.ne_of_gt (Nat.zero_lt_of_lt hhjHigh)
    obtain ⟨Q, hQ, hwit⟩:=
      AlignedRoundLemmas.justification_certificate
        S.E S.cfg C hhjNe
    obtain ⟨signer, hsignerQ, hsignerHonest⟩:=
      HonestWeightMajority.exists_honest_member_of_quorum hmajority hQ
    obtain ⟨a, haC, haSigner, haPair⟩:= hwit signer hsignerQ
    have haHonest: a.val_index ∈ rho.honest:= by
      rw [haSigner]
      exact hsignerHonest
    obtain ⟨ta, hta, hemit⟩:=
      Proofs.Bridges.carriedArePastEmissions_of_admissible
        S adm t v hC a haC haHonest
    have haTarget:
        a.height_pair = HeightPair.target st.h_j st.J.root:= by
      rw [← hhj, ← hJ]
      exact haPair
    obtain ⟨j, hjevent, hja⟩:= hemit
    have hJmem: st.J ∈ st.T:=
      Proofs.Records.justifiedInTree_depReachable
        S.E S.hc S.cfg (S.node v) st hdep
    obtain ⟨k, hk, -⟩:=
      Proofs.Bridges.stateBeforeTime_eq_stateBefore S adm.toScheduleWellFormed t
    have hJrun: RunBlock S rho st.J:= by
      apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i:= k)
      simpa only [st, Run.storeBeforeTime, hk] using hJmem
    simp only [Protocol.get_fg_root, Protocol.Store.toHealing,
      if_pos (by simpa only [st] using hgate)]
    by_cases hbefore: ta < t1
    · exact Block.preceq_trans
        (h.boundaryTargets a ta haHonest ⟨j, hjevent, hja⟩ hbefore
          st.h_j st.J.root ((Nat.sub_le M0 1).trans (Nat.le_of_lt hhjHigh))
          haTarget st.J hJrun rfl)
        (h.endpoint_mono (Nat.le_refl n0) h.start_le (Nat.le_refl i))
    · have hn0j: n0 ≤ j:= by
        rw [h.historyStart]
        exact filterBefore_length_le_tickIndex
          S adm.toScheduleWellFormed hjevent (le_of_not_gt hbefore)
      have hjread: j < strictEventIndex rho t:=
        emission_index_lt_beforeTime_prefix S adm.toScheduleWellFormed hjevent hta
      have hji: j < i:= lt_of_lt_of_le hjread hcursor
      have hJnext: Block.Preceq st.J (End (j + 1)):=
        (h.outputs j hn0j hji).targets
          haHonest hjevent hja st.h_j st.J.root haTarget st.J hJrun rfl
      exact Block.preceq_trans hJnext
        (h.endpoint_mono (hn0j.trans (Nat.le_succ j))
          (Nat.succ_le_iff.mpr hji) (Nat.le_refl i))
  · have hgateOff: st.h_j + 2 ≤ st.h_max:= by
      have hsucc: st.h_j + 1 ≤ st.h_max:=
        Nat.succ_le_iff.mpr hbelow
      have hstrict: st.h_j + 1 < st.h_max:=
        lt_of_le_of_ne hsucc (fun heq => hgate heq.symm)
      simpa only [Nat.add_assoc] using Nat.succ_le_iff.mpr hstrict
    have hhjlt: st.h_j < st.h_max - 1:= by
      rw [Nat.lt_sub_iff_add_lt]
      exact Nat.lt_of_succ_le (by
        simpa only [Nat.add_assoc] using hgateOff)
    have hnoHigh: NoHighJustifications S.E S.cfg st:=
      FixedHeightRootCore.noHighJustifications_depReachable
        S.E S.hc S.cfg (S.node v) hdep
    obtain ⟨C, hC, hF⟩:=
      Proofs.Bridges.storeFinalizationOnChain_depReachable
        S.E S.hc S.cfg (S.node v) hdep
    obtain ⟨k, hk, -⟩:=
      Proofs.Bridges.stateBeforeTime_eq_stateBefore
        S adm.toScheduleWellFormed t
    have hCrun: RunBlock S rho C:= by
      apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i:= k)
      simpa only [st, Run.storeBeforeTime, hk] using hC
    have hcrossed: (derived_state S.E S.cfg C).h_F <
        (derived_state S.E S.cfg (End i)).h:= by
      calc
        (derived_state S.E S.cfg C).h_F ≤
            (derived_state S.E S.cfg C).h_j:=
          (Protocol.chainOrder_derived_state S.E S.cfg C).heights_ordered
        _ ≤ st.h_j:= hnoHigh C hC
        _ < st.h_max - 1:= hhjlt
        _ ≤ (derived_state S.E S.cfg (End i)).h:= hendFloor
    have hFEnd: Block.Preceq st.F (End i):= by
      have hpre: Block.Preceq (derived_state S.E S.cfg C).F (End i):=
        Protocol.finalized_preceq_of_height_lt hsb hCrun hEndRun
          (adm.toRootCollisionFree.root_injective (End i) C hEndRun hCrun)
          ⟨rfl, rfl⟩ hcrossed
      simpa only [hF] using hpre
    simp only [Protocol.get_fg_root, Protocol.Store.toHealing,
      if_neg (by simpa only [st] using hgate)]
    exact hFEnd
-/





end HealingSurface
end Proofs
end DecoupledConsensusModel

end
