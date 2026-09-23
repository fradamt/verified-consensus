module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.HeightRegimeNamedClosed

@[expose] public section

/-! # Run-scoped named height regimes
These records are additive twins of `NamedHeightRegime` and
`NamedHeightRegimeBase`. They replace only the previous-root contract with
`NamedOldTargetRootBelowRun`, so named-root equality can use the execution's
root-collision contract.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A named height regime whose old-root contract ranges only over run
blocks. -/
structure NamedHeightRegimeRun
    (S : Setup V) (rho : Run V) (r0 : Round) (blocked : Height)
    (first i : Nat) (a : NamedAttestation V) (ta : Time)
    (Cfg T Tprev : NamedBlock V) (c0 : Round) : Prop where
  seed : PrefixFGSelectorConeAt S rho
    (inclusiveEventIndex rho (S.a r0)) first blocked i a ta Cfg T.erase
  checkpointPreceq : NamedBlock.Preceq T Cfg
  checkpointErase : T.erase =
    (Protocol.derive_named S.E S.cfg Cfg).T_h
  crossing : HeightWindowAt S rho (blocked + 1) first
  frame : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0
  c0le : c0 ≤ a.round
  ready : GradeRoundReady S rho a.round
  postPrev : S.E.t_GST ≤ S.a (a.round - 1)
  g1 : ∀ w ∈ rho.honest, ∃ Q : Block V, namedG1At S rho w a.round Q
  pred : NamedOldTargetRootBelowRun S rho first blocked T
  minimal : ∀ (b : NamedAttestation V) (tb : Time),
    b.val_index ∈ rho.honest →
    NamedRun.emits S rho b.val_index (Object.attest b) tb →
    b.height_pair.erase.height? = some (blocked + 1) → a.round ≤ b.round

/-- The additive run-scoped twin of `NamedHeightRegimeBase`. -/
structure NamedHeightRegimeBaseRun
    (S : Setup V) (rho : Run V) (r0 : Round) (blocked : Height)
    (first : Nat) (Tprev : NamedBlock V) : Prop where
  crossing : FirstHeightProgressAt S rho (blocked + 1) first
  start : honestHMaxBeforeIndex S rho
    (inclusiveEventIndex rho (S.a r0)) < blocked
  positive : 1 ≤ blocked
  frame : ∀ c : Round,
    (∀ (a : NamedAttestation V) (ta : Time),
      a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (Object.attest a) ta →
      a.height_pair.erase.height? = some (blocked + 1) → c ≤ a.round) →
    NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c
  oldRoot : ∀ (a : NamedAttestation V) (ta : Time),
    a.val_index ∈ rho.honest →
    NamedRun.emits S rho a.val_index (Object.attest a) ta →
    strictEventIndex rho (S.a a.round) < first →
    ∀ R : NamedBlock V, RunBlock S rho R →
      (Protocol.derive_named S.E S.cfg R).h = blocked →
      a.height_pair.erase = HeightPair.target blocked R.erase.root →
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
        some R.erase →
      ∀ w ∈ rho.honest, ∀ time : Time,
        blocked < (rho.storeBeforeTime S w time).h_max →
        Protocol.get_fg_root
          (rho.storeBeforeTime S w time).core.toHealing.toFG = R.erase →
        ∀ X : NamedBlock V, RunBlock S rho X →
          (Protocol.derive_named S.E S.cfg X).h = blocked + 1 →
          NamedBlock.Preceq Tprev X → NamedBlock.Preceq R X

namespace NamedHeightRegimeRun

variable {S : Setup V} {rho : Run V} {r0 : Round} {blocked : Height}
  {first i : Nat} {a : NamedAttestation V} {ta : Time}
  {Cfg T Tprev : NamedBlock V} {c0 : Round}

/-- Every existing named regime weakens to the run-scoped record. -/
theorem ofNamed
    (h : NamedHeightRegime S rho r0 blocked first i a ta Cfg T Tprev c0) :
    NamedHeightRegimeRun S rho r0 blocked first i a ta Cfg T Tprev c0 := {
  seed := h.seed
  checkpointPreceq := h.checkpointPreceq
  checkpointErase := h.checkpointErase
  crossing := h.crossing
  frame := h.frame
  c0le := h.c0le
  ready := h.ready
  postPrev := h.postPrev
  g1 := h.g1
  pred := h.oldRootRun
  minimal := h.minimal }

#print axioms NamedHeightRegimeRun.ofNamed

private theorem actionBody_runBlock
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionStoreAt S rho v r).st.bodies) :
    RunBlock S rho D := by
  have hDpre : D ∈
      (NamedRun.stateBeforeTime S rho (S.a r) v).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hD
  obtain ⟨j, hj, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedScheduleWellFormed.sorted (S.a r)
  have hDj : D ∈ (rho.stateBefore S j v).st.bodies := by
    change D ∈ (NamedRun.stateBefore S rho j v).st.bodies
    rw [← hj]
    exact hDpre
  exact Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv j hDj)

/-- The checkpoint of a run-scoped named regime is a run block at the source
height. -/
theorem checkpoint_runBlock
    (adm : Admissible S rho)
    (h : NamedHeightRegimeRun S rho r0 blocked first i a ta
      Cfg T Tprev c0) :
    RunBlock S rho T ∧
      (Protocol.derive_named S.E S.cfg T).h = blocked + 1 := by
  have hCfgRun : RunBlock S rho Cfg :=
    actionBody_runBlock S adm h.seed.signerHonest h.seed.sourceMem
  have hTrun : RunBlock S rho T :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hCfgRun h.checkpointPreceq
  obtain ⟨K, hKCfg, hKerase, hKheight⟩ :=
    Proofs.NamedEntryHeight.entry_ancestor_same_height S.E S.cfg Cfg
  have hKrun : RunBlock S rho K :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hCfgRun hKCfg
  have hroot : T.root = K.root := by
    calc
      T.root = T.erase.root := (Proofs.NamedWire.erase_root T).symm
      _ = K.erase.root := by rw [h.checkpointErase, hKerase]
      _ = K.root := Proofs.NamedWire.erase_root K
  have hTK : T = K :=
    adm.toNamedRootCollisionFree.root_injective T K hTrun hKrun T K
      (Or.inl (Proofs.NamedAncestry.named_self T))
      (Or.inr (Proofs.NamedAncestry.named_self K)) hroot
  refine ⟨hTrun, ?_⟩
  rw [hTK, hKheight, h.seed.sourceDerivedHeight]


/-- A named body one height above a run-scoped regime can occur only after
the source round. -/
theorem round_succ_le_of_higherBlock
    (adm : Admissible S rho)
    (h : NamedHeightRegimeRun S rho r0 blocked first i a ta
      Cfg T Tprev c0)
    {p : V} (hp : p ∈ rho.honest) {r : Round} {B : NamedBlock V}
    (hBmem : B ∈ (actionStoreAt S rho p r).st.bodies)
    (hBh : (Protocol.derive_named S.E S.cfg B).h =
      blocked + 1 + 1) :
    a.round + 1 ≤ r := by
  by_contra hn
  have hle : r ≤ a.round := Nat.le_of_lt_succ (Nat.lt_of_not_le hn)
  have hBpre : B ∈
      (NamedRun.stateBeforeTime S rho (S.a r) p).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hBmem
  have heq := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedScheduleWellFormed (S.a r)) p
  rw [heq] at hBpre
  have hmaxB : blocked + 1 + 1 ≤
      (rho.stateBefore S (strictEventIndex rho (S.a r)) p).st.core.h_max := by
    have hbound := Proofs.NamedStoreBridge.heights_le_hMax_stateBefore
      S rho (strictEventIndex rho (S.a r)) p B hBpre
    rw [hBh] at hbound
    exact hbound
  have hfrontier :
      (rho.stateBefore S (strictEventIndex rho (S.a r)) p).st.core.h_max ≤
        blocked + 1 :=
    (localHMax_le_honestHMaxBeforeIndex S rho _ hp).trans
      (h.crossing.before _
        ((strictEventIndex_mono rho (Assembly.a_mono S hle)).trans_lt
          (h.seed.actionPrefix_lt adm.toNamedScheduleWellFormed)))
  exact Nat.not_succ_le_self (blocked + 1) (hmaxB.trans hfrontier)


end NamedHeightRegimeRun

namespace NamedHeightRegimeBaseRun

variable {S : Setup V} {rho : Run V} {r0 : Round} {blocked : Height}
  {first : Nat} {Tprev : NamedBlock V}

/-- Every existing named regime base weakens to the run-scoped base. -/
theorem ofNamed
    (h : NamedHeightRegimeBase S rho r0 blocked first Tprev) :
    NamedHeightRegimeBaseRun S rho r0 blocked first Tprev := by
  refine {
    crossing := h.crossing
    start := h.start
    positive := h.positive
    frame := h.frame
    oldRoot := ?_ }
  intro a ta ha hemit hbefore R _hRrun hRh hpair hR w hw time
    hfrontier hroot X hXrun hXheight hTprevX
  exact h.oldRoot a ta ha hemit hbefore R hRh hpair hR w hw time
    hfrontier hroot X hXrun hXheight hTprevX

#print axioms NamedHeightRegimeBaseRun.ofNamed

/-- The minimal honest row selected from a run-scoped base starts a
run-scoped named regime. -/
theorem exists_regime_closed
    (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (h : NamedHeightRegimeBaseRun S rho r0 blocked first Tprev) :
    ∃ (i : Nat) (a : NamedAttestation V) (ta : Time)
      (Cfg T : NamedBlock V),
      NamedHeightRegimeRun S rho r0 blocked first i a ta
        Cfg T Tprev a.round := by
  classical
  have hcross : PrefixHeightCrossingWitness S rho first blocked :=
    prefixHeightCrossingWitness_of_frontier_eq
      S adm h.positive h.crossing.frontier
  have hfresh : Internal.NoLocalHeightPairBefore S rho
      (inclusiveEventIndex rho (S.a r0)) blocked :=
    noLocalHeightPairBefore_of_frontier_lt S adm h.start
  obtain ⟨i0, a0, t0, _, _, _hiStart0, hiStop0, haHon0, hiEvent0,
    hiOutput0, _, _, _, _, _, _, _, _, hrow0⟩ :=
    prefixHeightCrossing_exactFGSelectorWitness
      S adm hbelow hcross hfresh
  have hrow0' : a0.height_pair.erase.height? = some (blocked + 1) := by
    rcases hrow0 with ht | ht <;> exact ht ▸ rfl
  let P : Round → Prop := fun r =>
    ∃ (j : Nat) (a : NamedAttestation V) (ta : Time),
      a.round = r ∧ j < first ∧ a.val_index ∈ rho.honest ∧
        rho.events[j]? = some (Event.tick a.val_index ta) ∧
        Object.attest a ∈ NamedRun.emittedAt S rho j a.val_index ta ∧
        a.height_pair.erase.height? = some (blocked + 1)
  have hex : ∃ r, P r :=
    ⟨a0.round, i0, a0, t0, rfl, hiStop0, haHon0, hiEvent0,
      hiOutput0, hrow0'⟩
  obtain ⟨i, a, ta, har, hi, haHon, hevent, hout, hrow⟩ :=
    Nat.find_spec hex
  have hemit : NamedRun.emits S rho a.val_index (Object.attest a) ta :=
    ⟨i, hevent, hout⟩
  have htime : ta = S.a a.round :=
    (Proofs.Optimistic.emits_attest_shape S hemit).2
  have hminimal : ∀ (b : NamedAttestation V) (tb : Time),
      b.val_index ∈ rho.honest →
      NamedRun.emits S rho b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) →
      a.round ≤ b.round := by
    intro b tb hbHon hbemit hbrow
    by_contra hnot
    have hlt : b.round < a.round := Nat.lt_of_not_ge hnot
    have htb : tb < ta := by
      rw [(Proofs.Optimistic.emits_attest_shape S hbemit).2, htime]
      exact action_strictMono S hlt
    obtain ⟨j, hj, hbout⟩ := hbemit
    have hjFirst : j < first :=
      (attestationIndex_lt_of_time_lt
        adm.toNamedScheduleWellFormed hj hevent htb).trans hi
    have hPb : P b.round :=
      ⟨j, b, tb, rfl, hjFirst, hbHon, hj, hbout, hbrow⟩
    have hle := Nat.find_min' hex hPb
    rw [← har] at hle
    exact (not_le_of_gt hlt) hle
  have hiStart : inclusiveEventIndex rho (S.a r0) ≤ i := by
    by_contra hnot
    have hfreshNext : Internal.NoLocalHeightPairBefore S rho
        (inclusiveEventIndex rho (S.a r0)) (blocked + 1) :=
      noLocalHeightPairBefore_of_frontier_lt S adm
        (h.start.trans_le (Nat.le_succ blocked))
    exact hfreshNext (Nat.lt_of_not_ge hnot) haHon hevent hout hrow
  have hframe : NamedHeightRegimeFrame S rho blocked
      (first - 1) Tprev a.round := h.frame a.round hminimal
  have hfrontierAt : honestHMaxBeforeIndex S rho i < blocked + 2 :=
    Nat.lt_succ_of_le (h.crossing.before i hi)
  obtain ⟨Cfg, T0, hseed, hpostPrev, hG1⟩ :=
    honestHeightRow_prefixFGSelectorCone_of_namedHeightRegimeFrame
      S adm hbelow hgst hframe hiStart hi haHon hevent hout hrow hfrontierAt
  have ready := hseed.ready_of_postGSTStart adm hgst
    (strictEventIndex_le_inclusiveEventIndex rho (S.a r0))
  obtain ⟨K, _hKmem, hKerase, hKheight, hKCfg, hKrun⟩ :=
    action_named_checkpoint S adm hseed.signerHonest hseed.sourceMem
  have hKT0 : K.erase = T0 := hKerase.trans hseed.checkpointDerived.symm
  have hseedK : PrefixFGSelectorConeAt S rho
      (inclusiveEventIndex rho (S.a r0)) first blocked i a ta Cfg K.erase := by
    rw [hKT0]
    exact hseed
  have hTprevCfg : NamedBlock.Preceq Tprev Cfg :=
    hframe.sourceAbove a.val_index hseed.signerHonest a.round
      (Nat.le_sub_one_of_lt
        (hseed.actionPrefix_lt adm.toNamedScheduleWellFormed))
      (hseed.actionHorizon adm) Cfg hseed.sourceMem hseed.exactFGSource
      hseed.sourceDerivedHeight
  have hTprevK : NamedBlock.Preceq Tprev K := by
    rcases Block.preceq_linear (Proofs.NamedWire.erase_preceq hTprevCfg)
        (Proofs.NamedWire.erase_preceq hKCfg) with hprevK | hKprev
    · obtain ⟨Q, hQK, hQerase⟩ :=
        Proofs.NamedAncestry.erased_ancestor_lift K hprevK
      have hQrun : RunBlock S rho Q :=
        Proofs.NamedRuntime.blockInRun_of_ancestor S rho hKrun hQK
      have hQTprev : Q = Tprev := by
        apply adm.toNamedRootCollisionFree.root_injective
          Q Tprev hQrun hframe.prevRun Q Tprev
          (Or.inl (Proofs.NamedAncestry.named_self Q))
          (Or.inr (Proofs.NamedAncestry.named_self Tprev))
        rw [← Proofs.NamedWire.erase_root Q, hQerase, Proofs.NamedWire.erase_root]
      rw [← hQTprev]
      exact hQK
    · obtain ⟨Q, hQTprev, hQerase⟩ :=
        Proofs.NamedAncestry.erased_ancestor_lift Tprev hKprev
      have hQrun : RunBlock S rho Q :=
        Proofs.NamedRuntime.blockInRun_of_ancestor S rho hframe.prevRun hQTprev
      have hQK : Q = K := by
        apply adm.toNamedRootCollisionFree.root_injective
          Q K hQrun hKrun Q K
          (Or.inl (Proofs.NamedAncestry.named_self Q))
          (Or.inr (Proofs.NamedAncestry.named_self K))
        rw [← Proofs.NamedWire.erase_root Q, hQerase, Proofs.NamedWire.erase_root]
      have hKTprev : NamedBlock.Preceq K Tprev := by
        rw [← hQK]
        exact hQTprev
      have hmono := Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hKTprev
      rw [hKheight, hseed.sourceDerivedHeight] at hmono
      exact False.elim
        (Nat.not_succ_le_self blocked (hmono.trans hframe.prevHeight))
  have hKsourceHeight :
      (Protocol.derive_named S.E S.cfg K).h = blocked + 1 :=
    hKheight.trans hseed.sourceDerivedHeight
  refine ⟨i, a, ta, Cfg, K, {
    seed := hseedK
    checkpointPreceq := hKCfg
    checkpointErase := hKerase
    crossing := h.crossing.toWindow
    frame := hframe
    c0le := Nat.le_refl _
    ready := ready
    postPrev := hpostPrev
    g1 := hG1
    pred := ?_
    minimal := hminimal }⟩
  intro b tb hb hbemit hbefore R hRrun hRh hpair hR w hw time
    hfrontier hroot
  exact h.oldRoot b tb hb hbemit hbefore R hRrun hRh hpair hR w hw time
    hfrontier hroot K hKrun hKsourceHeight hTprevK

#print axioms NamedHeightRegimeBaseRun.exists_regime_closed

end NamedHeightRegimeBaseRun

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
