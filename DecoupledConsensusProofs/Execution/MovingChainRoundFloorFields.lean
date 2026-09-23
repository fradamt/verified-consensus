module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ValidatorClient.MovingChainRow
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.MovingChainCeiling
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionConfirmationCore
public import DecoupledConsensusProofs.Protocol.ChainState.Main
public import DecoupledConsensusInternal.Execution.Assumptions
public import Mathlib.Data.Int.LeastGreatest
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RawHeightProgress
public import DecoupledConsensusProofs.Protocol.ChainState.SlashableBoundBridge
public import DecoupledConsensusProofs.Objects.EmittedHeightBound
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityCertificates
public import DecoupledConsensusProofs.Execution.OutageProvenance
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryCapturedNextActionExact

@[expose] public section

/-!
# The round-level fields of the two hand-off records, from the slot fold

Three facts the finality records ask for at every post-boundary round, each
read off the fold's own invariant:

* `liveAboveEndpoint` — the honest live confirmation of a round action is at or
  above the fold's endpoint at that round's opening slot. The round action IS
  the opening slot's confirmation evaluation, and the fold certifies every
  honest slot-`d` confirmation against the endpoint the NEXT slot enters with,
  which is above the one slot `d` entered with.
* `batchAligned` — with the carriers below the endpoint and the endpoint below
  the live confirmation, every honest round batch is aligned on the reader's
  own live confirmation.
* `actionSGBlock_eq_liveConfirmed` — hence the round's SG carrier IS that live
  confirmation: the relative-majority walk starts at the SG root, which the
  fold puts below the endpoint, and alignment clears every block up to the
  live confirmation, so the walk reaches the tip.

The last one is what makes the floor record's `floorBelowCarriers` a statement
about live confirmations rather than about the SG fork choice.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]




/-
/-- **The round's SG carrier is the reader's own live confirmation.**

The relative-majority walk starts at the SG root and climbs towards
`live_confirmed` while `g0_clear` holds. Alignment clears every block at or
below the live confirmation, and the root is below it, so the walk reaches the
tip and the `A_G2` fallback tier is never taken. -/
theorem actionSGBlockAt_eq_liveConfirmed_of_aligned
    (S: Setup V) {rho: Run V} (hfb: BelowOneThird S rho.honest)
    {r: Round} {v: V}
    (hal: Proofs.Optimistic.BatchAligned
      (actionStoreAt S rho v r).st.core.toHealing.gradeView rho.honest r
      (actionStoreAt S rho v r).st.core.live_confirmed)
    (hanchor: Block.Preceq
      (Proofs.Optimistic.healAnchor S.E S.hc
        (actionStoreAt S rho v r).st.core.toHealing)
      (actionStoreAt S rho v r).st.core.live_confirmed):
    actionSGBlockAt S rho v r = (actionStoreAt S rho v r).st.core.live_confirmed:= by
  have hround: S.hc.round_of (actionStoreAt S rho v r).st.core.s = r:= by
    simpa only [Protocol.Store.toHealing] using actionStoreAt_round S rho v r
  have hrootEq: Protocol.get_sg_root S.E S.hc
      (actionStoreAt S rho v r).st.core.toHealing r =
        Proofs.Optimistic.healAnchor S.E S.hc
          (actionStoreAt S rho v r).st.core.toHealing:= by
    rw [Proofs.Optimistic.healAnchor_eq_get_sg_root, hround]
  have hclear: Protocol.g0_clear S.E
      (actionStoreAt S rho v r).st.core.toHealing.gradeView S.hc r
      (actionStoreAt S rho v r).st.core.live_confirmed = true:=
    Proofs.Optimistic.g0_clear_of_preceq S.E hal hfb
      (Block.preceq_self _)
  have hfloor: (Option.some
      (Protocol.get_sg_root S.E S.hc
        (actionStoreAt S rho v r).st.core.toHealing r)).elim True
        (fun a => Block.preceq a
          (actionStoreAt S rho v r).st.core.live_confirmed = true):= by
    simp only [Option.elim, hrootEq]
    exact hanchor
  have hwalk: Protocol.deepest_clear
      (some (Protocol.get_sg_root S.E S.hc
        (actionStoreAt S rho v r).st.core.toHealing r))
      (actionStoreAt S rho v r).st.core.live_confirmed
      (fun B => Protocol.g0_clear S.E
        (actionStoreAt S rho v r).st.core.toHealing.gradeView S.hc r B) =
        some (actionStoreAt S rho v r).st.core.live_confirmed:=
    deepest_clear_eq_tip hfloor hclear
  change Protocol.get_sg_vote S.E S.hc
      (actionStoreAt S rho v r).st.core.toHealing r
      (Protocol.grade2_block S.E S.hc
        (actionStoreAt S rho v r).st.core.toHealing r) = _
  rw [Protocol.get_sg_vote.eq_def, hwalk]
  rfl
-/


/-! ## The convergence premise, and the floor block it fills -/




/-
/-- **The gate-off half of the residue follows from the band alone.**

When the read is gate-off the selected root is the store's finalized block, and
`h_F ≤ h_j ≤ h_max - 2` puts it strictly below any block at the band.
Accountable finality crossing then puts it on that block's chain. So the
residue's root clause only ever has content in the GATE-ON case. -/
theorem gateOffRoot_preceq_of_band
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {v: V} (hv: v ∈ rho.honest) {t: Time} {A: Block V}
    (hArun: RunBlock S rho A)
    (hband: (rho.storeBeforeTime S v t).h_max - 1 ≤
      (derived_state S.E S.cfg A).h)
    (hgate: ¬ ((rho.storeBeforeTime S v t).h_max =
      (rho.storeBeforeTime S v t).h_j + 1)):
    Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v t).toHealing.toFG) A:= by
  let pre:= rho.storeBeforeTime S v t
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node v) pre:= by
    simpa only [pre, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed t v)
  have hbelow: pre.h_j < pre.h_max:=
    FixedHeightRootCore.justificationBelowMax_depReachable
      S.E S.hc S.cfg (S.node v) hdep
  have hsb: SlashableBound S rho:=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hgateOff: pre.h_j + 2 ≤ pre.h_max:= by
    have hsucc: pre.h_j + 1 ≤ pre.h_max:= Nat.succ_le_iff.mpr hbelow
    have hstrict: pre.h_j + 1 < pre.h_max:=
      lt_of_le_of_ne hsucc (fun heq => hgate heq.symm)
    simpa only [Nat.add_assoc] using Nat.succ_le_iff.mpr hstrict
  have hhjlt: pre.h_j < pre.h_max - 1:= by
    rw [Nat.lt_sub_iff_add_lt]
    exact Nat.lt_of_succ_le (by simpa only [Nat.add_assoc] using hgateOff)
  have hnoHigh: NoHighJustifications S.E S.cfg pre:=
    FixedHeightRootCore.noHighJustifications_depReachable
      S.E S.hc S.cfg (S.node v) hdep
  obtain ⟨B, hB, hF⟩:=
    Proofs.Bridges.storeFinalizationOnChain_depReachable
      S.E S.hc S.cfg (S.node v) hdep
  obtain ⟨m, hm, -⟩:= Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toScheduleWellFormed t
  have hBrun: RunBlock S rho B:= by
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i:= m)
    simpa only [pre, Run.storeBeforeTime, hm] using hB
  have hcrossed: (derived_state S.E S.cfg B).h_F <
      (derived_state S.E S.cfg A).h:= by
    calc
      (derived_state S.E S.cfg B).h_F ≤
          (derived_state S.E S.cfg B).h_j:=
        (Protocol.chainOrder_derived_state S.E S.cfg B).heights_ordered
      _ ≤ pre.h_j:= hnoHigh B hB
      _ < pre.h_max - 1:= hhjlt
      _ ≤ (derived_state S.E S.cfg A).h:= hband
  have hFA: Block.Preceq pre.F A:= by
    have hpre: Block.Preceq (derived_state S.E S.cfg B).F A:=
      Protocol.finalized_preceq_of_height_lt hsb hBrun hArun
        (adm.toRootCollisionFree.root_injective A B hArun hBrun)
        ⟨rfl, rfl⟩ hcrossed
    simpa only [hF] using hpre
  simp only [Protocol.get_fg_root, Protocol.Store.toHealing,
    if_neg (by simpa only [pre] using hgate)]
  exact hFA
-/




/-
/-- **`floorActiveAtPlusTwoProposal`, reduced to the `+2` proposal read.**

The floor is carried forward from the round read by tree growth, the root
clause is the same gate split as everywhere else, and what is left is the band
at the `+2` proposal read. So this field asks for nothing new in kind: it is
the cover's own band clause, read one instant later. -/
theorem floorActive_at_plusTwoProposal_of_band
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {r: Round} {C: Block V}
    (hprop: S.E.proposer (S.hc.opening_slot r + 2) ∈ rho.honest)
    (hCrun: RunBlock S rho C)
    (hmemRound: C ∈ (rho.storeBeforeTime S
      (S.E.proposer (S.hc.opening_slot r + 2)) (S.a r)).T)
    (hband: (rho.storeBeforeTime S
        (S.E.proposer (S.hc.opening_slot r + 2))
        (Protocol.proposal_time S.E (S.hc.opening_slot r + 2))).h_max - 1 ≤
        (derived_state S.E S.cfg C).h)
    (hgateOn: (rho.storeBeforeTime S
          (S.E.proposer (S.hc.opening_slot r + 2))
          (Protocol.proposal_time S.E (S.hc.opening_slot r + 2))).h_max =
        (rho.storeBeforeTime S
          (S.E.proposer (S.hc.opening_slot r + 2))
          (Protocol.proposal_time S.E (S.hc.opening_slot r + 2))).h_j + 1 →
        Block.Preceq
          (Protocol.get_fg_root
            (rho.storeBeforeTime S
              (S.E.proposer (S.hc.opening_slot r + 2))
              (Protocol.proposal_time S.E
                (S.hc.opening_slot r + 2))).toHealing.toFG) C):
    C ∈ Protocol.get_filtered_block_tree
      (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot r + 2)).toHealing.toFG:= by
  have hmem: C ∈ (rho.storeBeforeTime S
      (S.E.proposer (S.hc.opening_slot r + 2))
      (Protocol.proposal_time S.E (S.hc.opening_slot r + 2))).T:=
    storeBeforeTime_mem_of_le S adm.toScheduleWellFormed
      (le_of_lt (action_lt_plusTwo_proposal S r)) hmemRound
  have hroot: Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S
          (S.E.proposer (S.hc.opening_slot r + 2))
          (Protocol.proposal_time S.E
            (S.hc.opening_slot r + 2))).toHealing.toFG) C:= by
    by_cases hgate: (rho.storeBeforeTime S
        (S.E.proposer (S.hc.opening_slot r + 2))
        (Protocol.proposal_time S.E (S.hc.opening_slot r + 2))).h_max =
        (rho.storeBeforeTime S
          (S.E.proposer (S.hc.opening_slot r + 2))
          (Protocol.proposal_time S.E (S.hc.opening_slot r + 2))).h_j + 1
    · exact hgateOn hgate
    · exact gateOffRoot_preceq_of_band S adm hfb hprop hCrun hband hgate
  have hfiltered:= storeBeforeTime_mem_filtered_of_band S adm hmem hroot hband
  simpa only [Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
    Run.storeBeforeTime] using hfiltered
-/

/-! ## The floor's cone witness -/


/-- **A processed descendant at the band is a cone witness.**

`CanonicalConeWitness` asks for a processed block above `A` whose LOCAL height
reaches the band. A processed block's local height is its derived height, so a
descendant of `A` that the fold already puts at the band serves directly.

design note: the witness is the retained NAMED body and its height is
`Protocol.derive_named`, because that is the only derivation the named
store agrees with on its own bodies
(`Proofs.NamedStoreBridge.derivedView_stateBeforeTime`); `derived_state` of the
erasure agrees with it only under `NamedDerivationAgreesWithoutTimeoutsQuery`,
which is a hypothesis. The retired `DepReachableStore` route the earlier
proof used is gone, and with the named derivation the admissibility argument
is not needed at all. -/
theorem canonicalConeWitness_of_bandDescendant
    (S : Setup V) {rho : Run V}
    {v : V} {t : Time} {A : Block V} {W : NamedBlock V}
    (hAW : Block.Preceq A W.erase)
    (hmem : W ∈ (rho.storeBeforeTime S v t).bodies)
    (hband : (rho.storeBeforeTime S v t).h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg W).h) :
    CanonicalConeWitness (rho.storeBeforeTime S v t).core A := by
  have htree : (rho.storeBeforeTime S v t).core.T =
      (rho.storeBeforeTime S v t).bodies.image NamedBlock.erase :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t v).1.1.1.1
  have hmemT : W.erase ∈ (rho.storeBeforeTime S v t).core.T := by
    rw [htree]
    exact Finset.mem_image_of_mem NamedBlock.erase hmem
  have hsigma : (rho.storeBeforeTime S v t).core.σ W.erase =
      Protocol.derive_named S.E S.cfg W :=
    Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho t v W hmem
  refine ⟨W.erase, hmemT, hAW, ?_⟩
  rw [hsigma]
  exact hband


/-
/-- **The floor's cone witness, from the fold, with NO band premise.**

The floor is `F (o + 1)` for `o = opening_slot (r - 1)`, and the witness is the
fold's own endpoint at the round's opening slot: `endpointMonotone` orders the
two, the fold already proves the band at the later endpoint
(`actionFrontier_sub_one_le_endpointHeight`), and the only input is that the
later endpoint is processed at the round read — which is the `floorProcessed`
shape the records already carry.

This is what closes the cover once `floorHeight` is the cone witness rather
than a height bound at the floor itself: the fold never has to put the FLOOR at
the band, only a descendant of it. -/
theorem MovingSlotFoldAt.floorConeWitness
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {s0 s: Slot} {F: Slot → Block V}
    {End: Block V}
    (hfold: MovingSlotFoldAt S rho t1 M0 s0 s F End)
    {r: Round} (hr: 0 < r)
    (hlow: s0 ≤ S.hc.opening_slot (r - 1) + 1)
    (hhigh: S.hc.opening_slot r ≤ s)
    (hmem: ∀ v ∈ rho.honest,
      F (S.hc.opening_slot r) ∈ (rho.storeBeforeTime S v (S.a r)).T):
    ∀ v ∈ rho.honest,
      CanonicalConeWitness (rho.storeBeforeTime S v (S.a r))
        (F (S.hc.opening_slot (r - 1) + 1)):= by
  have hstep: S.hc.opening_slot (r - 1) + 1 ≤ S.hc.opening_slot r:= by
    have h2:= openingSlot_add_two_le_openingSlot_of_lt S
      (m:= r - 1) (r:= r) (Nat.sub_lt hr Nat.one_pos)
    exact (Nat.le_succ _).trans h2
  intro v hv
  refine canonicalConeWitness_of_bandDescendant S adm
    (hfold.mono _ _ hlow hstep hhigh) (hmem v hv) ?_
  exact hfold.actionFrontier_sub_one_le_endpointHeight S adm hfb
    (hlow.trans hstep) hhigh hv
-/

/-! ## The unconditional two-rise store bound -/








/-
/-- The strict-store form of the honest emission height bound. -/
private theorem floorHonestEmittedHeight_le_storeBeforeTime
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {v: V} {a: CombinedAttestation V} {t: Time} {h: Height}
    (hemit: rho.emits S v (Object.attest a) t)
    (hh: a.height_pair.height? = some h):
    h ≤ (rho.storeBeforeTime S v t).h_max:= by
  have htime:= (Proofs.Optimistic.emits_attest_shape S hemit).2
  obtain ⟨i, hi, hmem⟩:= hemit
  subst t
  rw [Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
    S adm.toScheduleWellFormed hi] at hmem
  obtain ⟨hact, -⟩:=
    Proofs.Optimistic.attest_eq_of_mem_on_tick_emit S (S.node v)
      (rho.stateBeforeTime S (S.a a.round) v).st
      (rho.stateBeforeTime S (S.a a.round) v).Λ
      (r:= a.round) rfl hmem
  have hround: h ≤ (actionStoreAt S rho v a.round).h_max:= by
    apply roundActionHeight_le_actionHMax S adm v a.round
      (rho.stateBeforeTime S (S.a a.round) v).Λ
    change (Protocol.round_action S.E S.hc (S.node v)
      (Proofs.Optimistic.attestStore S
        (rho.stateBeforeTime S (S.a a.round) v).st
        (S.a a.round)).toHealing
      (rho.stateBeforeTime S (S.a a.round) v).Λ).2.height_pair.height? = some h
    rw [← hact]
    exact hh
  have hpre: (actionStoreAt S rho v a.round).h_max =
      (rho.storeBeforeTime S v (S.a a.round)).h_max:=
    (attestStore_finality S
      (rho.stateBeforeTime S (S.a a.round) v).st
      (S.a a.round)).2.2.1
  rw [hpre] at hround
  exact hround

/-- A reader's strict round-`r` frontier is at most two heights above the
fold endpoint at the previous round's opening slot. -/
theorem MovingSlotFoldAt.storeHMax_le_prevEndpoint_add_two
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {s0 s: Slot} {F: Slot → Block V}
    {End: Block V}
    (hfold: MovingSlotFoldAt S rho t1 M0 s0 s F End)
    {r: Round} (hr: 0 < r)
    (hlow: s0 ≤ S.hc.opening_slot (r - 1))
    (hhigh: S.hc.opening_slot (r - 1) + 1 ≤ s)
    (v: V):
    (rho.storeBeforeTime S v (S.a r)).h_max ≤
      (derived_state S.E S.cfg
        (F (S.hc.opening_slot (r - 1)))).h + 2:= by
  let T: Height:=
    (derived_state S.E S.cfg (F (S.hc.opening_slot (r - 1)))).h + 2
  by_contra hno
  have hhigh2: T + 1 ≤ (rho.storeBeforeTime S v (S.a r)).h_max:=
    floorNat_succ_le_of_not_le hno
  have hstore: rho.storeBeforeTime S v (S.a r) =
      (rho.stateBefore S (strictEventIndex rho (S.a r)) v).st:=
    storeBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toScheduleWellFormed v (S.a r)
  have hdep:= Proofs.Bridges.depReachable_of_admissible
    S adm.toDeliveryWellFormed v (strictEventIndex rho (S.a r))
  obtain ⟨W, hWT, hWlower⟩:=
    hMaxInTree_depReachable S.E S.hc S.cfg (S.node v) hdep
  have htree:=
    treeHeightsLeHMax_depReachable S.E S.hc S.cfg (S.node v) hdep
  have hagree:=
    derivedStateAgrees_depReachable S.E S.hc S.cfg (S.node v) _ hdep
  have hWheight: (derived_state S.E S.cfg W).h =
      (rho.stateBefore S (strictEventIndex rho (S.a r)) v).st.h_max:= by
    rw [← hagree W hWT]
    exact Nat.le_antisymm (htree W hWT) hWlower
  have hWhigh: T < (derived_state S.E S.cfg W).h:= by
    rw [hWheight, ← hstore]
    exact Nat.lt_of_succ_le hhigh2
  obtain ⟨P, hPW, hPheight⟩:=
    exists_derivedHeight_eq_on_chain S.E S.cfg
      (floorNat_one_le_add_two _) (Nat.le_of_lt hWhigh)
  obtain ⟨C, Q, hCQ, hCW, hQheight, hCheight⟩:=
    exists_heightCrossingEdge_on_chain S.E S.cfg hPW hPheight hWhigh
  have hpc:=
    parentClosed_depReachable S.E S.hc S.cfg (S.node v) _ hdep
  have hCmem: C ∈
      (rho.stateBefore S (strictEventIndex rho (S.a r)) v).st.T:=
    Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2 C W hWT hCW
  have hcrossC: (derived_state S.E S.cfg Q).h <
      (derived_state S.E S.cfg C).h:= by
    rw [hQheight, hCheight]
    exact Nat.lt_succ_self _
  obtain ⟨a, ha, hah, hheight⟩:=
    heightEvent_honestRow_of_crossing S hfb hCQ hcrossC
  have hheightM: a.height_pair.height? = some T:= by
    rw [hheight, hQheight]
  have hCmemTime: C ∈ (rho.stateBeforeTime S (S.a r) v).st.T:= by
    change C ∈ (rho.storeBeforeTime S v (S.a r)).T
    rw [hstore]
    exact hCmem
  obtain ⟨u, hulk, hemit⟩:=
    Proofs.Bridges.carriedArePastEmissions_of_admissible S adm (S.a r) v
      hCmemTime a ha hah
  have hu: u = S.a a.round:= (Proofs.Optimistic.emits_attest_shape S hemit).2
  subst hu
  have hEmit: T ≤
      (rho.storeBeforeTime S a.val_index (S.a a.round)).h_max:=
    floorHonestEmittedHeight_le_storeBeforeTime S adm hemit hheightM
  have hround: a.round < r:= by
    by_contra hge
    exact absurd (Assembly.a_mono S (Nat.le_of_not_gt hge))
      (not_le.mpr hulk)
  have hroundLe: a.round ≤ r - 1:=
    floorNat_le_pred_of_lt_pos hr hround
  have htimeLe: S.a a.round ≤ S.a (r - 1):=
    Assembly.a_mono S hroundLe
  have hEmitPrev: T ≤
      (rho.storeBeforeTime S a.val_index (S.a (r - 1))).h_max:=
    hEmit.trans (storeBeforeTime_hMax_mono S adm.toScheduleWellFormed
      a.val_index htimeLe)
  have hband:= hfold.actionFrontier_sub_one_le_endpointHeight
    S adm hfb (r:= r - 1) hlow ((Nat.le_succ _).trans hhigh) hah
  have hprevMax:
      (rho.storeBeforeTime S a.val_index (S.a (r - 1))).h_max ≤
        (derived_state S.E S.cfg
          (F (S.hc.opening_slot (r - 1)))).h + 1:=
    floorNat_le_add_one_of_pred_le hband
  have hcontr: T ≤
      (derived_state S.E S.cfg
        (F (S.hc.opening_slot (r - 1)))).h + 1:=
    hEmitPrev.trans hprevMax
  exact floorNat_not_add_two_le_add_one _ (by simpa only [T] using hcontr)

/-- The gate-off justification height is at the previous endpoint. -/
theorem MovingSlotFoldAt.justificationHeight_le_prevEndpoint
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {s0 s: Slot} {F: Slot → Block V}
    {End: Block V}
    (hfold: MovingSlotFoldAt S rho t1 M0 s0 s F End)
    {r: Round} (hr: 0 < r)
    (hlow: s0 ≤ S.hc.opening_slot (r - 1))
    (hhigh: S.hc.opening_slot (r - 1) + 1 ≤ s)
    {v: V}
    (hgate: (rho.storeBeforeTime S v (S.a r)).h_j + 2 ≤
      (rho.storeBeforeTime S v (S.a r)).h_max):
    (rho.storeBeforeTime S v (S.a r)).h_j ≤
      (derived_state S.E S.cfg
        (F (S.hc.opening_slot (r - 1) + 1))).h:= by
  have hbound:=
    hfold.storeHMax_le_prevEndpoint_add_two S adm hfb hr hlow hhigh v
  have hjle: (rho.storeBeforeTime S v (S.a r)).h_j ≤
      (derived_state S.E S.cfg
        (F (S.hc.opening_slot (r - 1)))).h:=
    floorNat_le_of_add_two_le_add_two (hgate.trans hbound)
  have hstep: Block.Preceq (F (S.hc.opening_slot (r - 1)))
      (F (S.hc.opening_slot (r - 1) + 1)):=
    hfold.mono _ _ hlow (Nat.le_succ _) hhigh
  exact hjle.trans (Protocol.derived_h_mono S.E S.cfg hstep)

/-- The gate-off selected root is below the previous round's next endpoint. -/
theorem MovingSlotFoldAt.gateOffRoot_preceq_prevEndpoint
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {s0 s: Slot} {F: Slot → Block V}
    {End: Block V}
    (hfold: MovingSlotFoldAt S rho t1 M0 s0 s F End)
    {r: Round} (hr: 0 < r)
    (hlow: s0 ≤ S.hc.opening_slot (r - 1))
    (hhighPrev: S.hc.opening_slot (r - 1) + 1 ≤ s)
    (hlowR: s0 ≤ S.hc.opening_slot r)
    (hhighR: S.hc.opening_slot r ≤ s)
    (hstep: S.hc.opening_slot (r - 1) + 1 ≤ S.hc.opening_slot r)
    {v: V} (hv: v ∈ rho.honest)
    (hstart: t1 ≤ S.a r)
    (hgate: ¬ ((rho.storeBeforeTime S v (S.a r)).h_max =
      (rho.storeBeforeTime S v (S.a r)).h_j + 1)):
    Block.Preceq
      (Protocol.get_fg_root (healStoreAt S rho v r).toFG)
      (F (S.hc.opening_slot (r - 1) + 1)):= by
  set pre:= rho.storeBeforeTime S v (S.a r) with hpre
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node v) pre:= by
    simpa only [hpre, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed (S.a r) v)
  have hbelow: pre.h_j < pre.h_max:=
    FixedHeightRootCore.justificationBelowMax_depReachable
      S.E S.hc S.cfg (S.node v) hdep
  have hgateOff: pre.h_j + 2 ≤ pre.h_max:= by
    have hsucc: pre.h_j + 1 ≤ pre.h_max:= Nat.succ_le_iff.mpr hbelow
    have hstrict: pre.h_j + 1 < pre.h_max:=
      lt_of_le_of_ne hsucc (fun heq => hgate heq.symm)
    simpa only [Nat.add_assoc] using Nat.succ_le_iff.mpr hstrict
  have hrootEq: Protocol.get_fg_root (healStoreAt S rho v r).toFG =
      pre.F:= by
    simp only [healStoreAt, Protocol.get_fg_root,
      Protocol.Store.toHealing, hpre,
      if_neg (by simpa only [hpre] using hgate)]
  rw [hrootEq]
  have hjle: pre.h_j ≤
      (derived_state S.E S.cfg
        (F (S.hc.opening_slot (r - 1) + 1))).h:=
    hfold.justificationHeight_le_prevEndpoint S adm hfb hr hlow
      hhighPrev hgateOff
  have hnoHigh: NoHighJustifications S.E S.cfg pre:=
    FixedHeightRootCore.noHighJustifications_depReachable
      S.E S.hc S.cfg (S.node v) hdep
  obtain ⟨B, hB, hF⟩:=
    Proofs.Bridges.storeFinalizationOnChain_depReachable
      S.E S.hc S.cfg (S.node v) hdep
  have hrootChain: Block.Preceq pre.F (F (S.hc.opening_slot r)):= by
    have hraw:= hfold.actionRoot_preceq_endpoint S adm hfb hlowR hhighR hv
      hstart
    rw [show Protocol.get_fg_root
        (rho.storeBeforeTime S v (S.a r)).toHealing.toFG = pre.F from by
      simp only [Protocol.get_fg_root, Protocol.Store.toHealing, hpre,
        if_neg (by simpa only [hpre] using hgate)]] at hraw
    exact hraw
  have hprevChain: Block.Preceq (F (S.hc.opening_slot (r - 1) + 1))
      (F (S.hc.opening_slot r)):=
    hfold.mono _ _ (hlow.trans (Nat.le_succ _)) hstep hhighR
  rcases Protocol.derived_finalized_height S.E S.cfg B with hzero | hheq
  · have hgen: (derived_state S.E S.cfg B).F = Block.genesis:=
      Protocol.derived_state_F_of_h_F_zero S.E S.cfg B hzero
    rw [← hF, hgen]
    exact Protocol.preceq_genesis _
  · have hself: (derived_state S.E S.cfg pre.F).T_h = pre.F:= by
      rw [← hF]
      exact Protocol.derived_finalized_isTarget S.E S.cfg B
    have hheight: (derived_state S.E S.cfg pre.F).h ≤
        (derived_state S.E S.cfg
          (F (S.hc.opening_slot (r - 1) + 1))).h:= by
      calc
        (derived_state S.E S.cfg pre.F).h
            = (derived_state S.E S.cfg B).h_F:= by rw [← hF]; exact hheq
        _ ≤ (derived_state S.E S.cfg B).h_j:=
          (Protocol.chainOrder_derived_state S.E S.cfg B).heights_ordered
        _ ≤ pre.h_j:= hnoHigh B hB
        _ ≤ _:= hjle
    exact Protocol.entryTarget_preceq_of_h_le S.E S.cfg hrootChain hprevChain
      hself hheight

/-- **The cover from the fold, by cases on the gate.**

The fold NAMES the witness — `F (o + 1)` for `o = opening_slot (r - 1)`, the
endpoint the slot after the previous round's opening entered with — and
discharges THREE of the cover's four clauses outright:

* the run-block fact, from the fold's own history at that slot;
* the carrier cover, from `carrierSandwich` at round `r - 1`;
* the CONE WITNESS, from `floorConeWitness`: `F (opening_slot r)` is a
  processed descendant of it at the band, so the floor never has to reach the
  band itself. This is what the records' move from `floorHeight` to
  `floorWitness` bought.

The fourth clause, the root clause, splits by the gate. A GATE-OFF read is
closed here, by the unconditional two-rise store bound and the entry-block
lemma. A GATE-ON read is the caller's: there the selected root is the
justified block, which sits AT the band and can be strictly above an honest
carrier, so no block
is both below every carrier and above every root. That is the case the
records' lost-round exemption covers, and `hgateOn` is where the caller
supplies it. -/
theorem MovingSlotFoldAt.bandCoverAt_of_gateCases
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {s0 s: Slot} {F: Slot → Block V}
    {End: Block V}
    (hfold: MovingSlotFoldAt S rho t1 M0 s0 s F End)
    {r: Round} (hr: 0 < r)
    (hlow: s0 ≤ S.hc.opening_slot (r - 1))
    (hhigh: S.hc.opening_slot (r - 1) + 1 < s)
    (hlowR: s0 ≤ S.hc.opening_slot r)
    (hhighR: S.hc.opening_slot r ≤ s)
    (hstep: S.hc.opening_slot (r - 1) + 1 ≤ S.hc.opening_slot r)
    (hstart: t1 ≤ S.a r)
    (hal: ∀ v ∈ rho.honest,
      Proofs.Optimistic.BatchAligned
        (actionStoreAt S rho v (r - 1)).toHealing.gradeView rho.honest (r - 1)
        (actionStoreAt S rho v (r - 1)).live_confirmed)
    (hanchor: ∀ v ∈ rho.honest,
      Block.Preceq
        (Proofs.Optimistic.healAnchor S.E S.hc
          (actionStoreAt S rho v (r - 1)).toHealing)
        (actionStoreAt S rho v (r - 1)).live_confirmed)
    (hmem: ∀ v ∈ rho.honest,
      F (S.hc.opening_slot r) ∈ (rho.storeBeforeTime S v (S.a r)).T)
    (hgateOn: ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v (S.a r)).h_max =
          (rho.storeBeforeTime S v (S.a r)).h_j + 1 →
        Block.Preceq
          (Protocol.get_fg_root (healStoreAt S rho v r).toFG)
          (F (S.hc.opening_slot (r - 1) + 1))):
    MovingChainBandCoverAt S rho r:= by
  obtain ⟨EndAt, hstate, hval⟩:=
    hfold.historyAt (S.hc.opening_slot (r - 1) + 1)
      (hlow.trans (Nat.le_succ _)) (le_of_lt hhigh)
  refine ⟨F (S.hc.opening_slot (r - 1) + 1), ?_, ?_, ?_, ?_⟩
  · rw [← hval]
    exact hstate.endpointRun _ hstate.start_le (Nat.le_refl _)
  · intro v hv
    exact (hfold.carrierSandwich S hfb hlow hhigh hv (hal v hv)
      (hanchor v hv)).1
  · exact hfold.floorConeWitness S adm hfb hr
      (hlow.trans (Nat.le_succ _)) hhighR hmem
  · intro v hv
    by_cases hgate: (rho.storeBeforeTime S v (S.a r)).h_max =
        (rho.storeBeforeTime S v (S.a r)).h_j + 1
    · exact hgateOn v hv hgate
    · exact hfold.gateOffRoot_preceq_prevEndpoint S adm hfb hr hlow
        (le_of_lt hhigh) hlowR hhighR hstep hv hstart hgate

/-- **The cover's witness is processed at the round read.**

It is below this reader's own round-`(r-1)` carrier, that carrier is below the
round's endpoint, the endpoint is in the reader's processed tree, and a
processed tree is parent-closed. Nothing beyond activity at the read is
used. -/
theorem bandCoverWitness_processed
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {r: Round} {C E: Block V}
    (hCcover: ActionCarriersCover S rho (r - 1) C)
    (hcarriers: ∀ w ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho w (r - 1)) E)
    (hmem: ∀ v ∈ rho.honest, E ∈ (rho.storeBeforeTime S v (S.a r)).T):
    ∀ v ∈ rho.honest, C ∈ (rho.storeBeforeTime S v (S.a r)).T:= by
  intro v hv
  let pre:= rho.storeBeforeTime S v (S.a r)
  have hCE: Block.Preceq C E:=
    Block.preceq_trans (hCcover v hv) (hcarriers v hv)
  have hpc: ParentClosed pre:=
    parentClosed_depReachable S.E S.hc S.cfg (S.node v) pre (by
      simpa only [pre, Run.storeBeforeTime] using
        (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
          adm.toDeliveryWellFormed (S.a r) v))
  exact Proofs.Records.mem_of_preceq ((parentClosed_iff pre).mp hpc).2
    C E (hmem v hv) hCE

/-- **The floor block of both hand-off records, at one round, from the cover.**

Three of the four fields are the cover's own clauses. The fourth,
`floorProcessed`, is activity at the round read and needs nothing new: the
cover's witness is below this reader's own round-`(r-1)` carrier, that carrier
is below the fold's endpoint, the endpoint is in the reader's processed tree,
and a processed tree is parent-closed. -/
theorem movingChainFloorFields_of_bandCover
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {r: Round} (hcover: MovingChainBandCoverAt S rho r)
    {E: Block V}
    (hcarriers: ∀ w ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho w (r - 1)) E)
    (hmem: ∀ v ∈ rho.honest, E ∈ (rho.storeBeforeTime S v (S.a r)).T):
    ∃ C: Block V,
      (∀ w ∈ rho.honest, Block.Preceq C (actionSGBlockAt S rho w (r - 1))) ∧
        (∀ v ∈ rho.honest,
          Block.Preceq
            (Protocol.get_fg_root (healStoreAt S rho v r).toFG) C) ∧
          (∀ v ∈ rho.honest, C ∈ (rho.storeBeforeTime S v (S.a r)).T) ∧
            ∀ v ∈ rho.honest,
              CanonicalConeWitness (rho.storeBeforeTime S v (S.a r)) C:= by
  obtain ⟨C, _hCrun, hCcover, hCband, hCroots⟩:= hcover
  exact ⟨C, hCcover, hCroots,
    bandCoverWitness_processed S adm hCcover hcarriers hmem, hCband⟩
-/

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
