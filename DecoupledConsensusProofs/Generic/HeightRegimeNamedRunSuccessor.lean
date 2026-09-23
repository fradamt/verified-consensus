module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.RecoveryInitialSourceNamedRunHistory

@[expose] public section

/-!
# Closed successors for run-scoped named height regimes
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

namespace NamedHeightRegimeRun

variable {S : Setup V} {rho : Run V} {r0 : Round} {blocked : Height}
  {first i : Nat} {a : NamedAttestation V} {ta : Time}
  {Cfg T Tprev : NamedBlock V} {c0 : Round}

/-- The successor frame with the run-scoped regime's closed history. -/
theorem frame_succ_main
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (h : NamedHeightRegimeRun S rho r0 blocked first i a ta
      Cfg T Tprev c0)
    (hblocked : 1 ≤ blocked)
    {first' : Nat}
    (hfirst' : HeightWindowAt S rho (blocked + 1 + 1) first') :
    NamedHeightRegimeFrame S rho (blocked + 1) (first' - 1) T
      (a.round + 1) := by
  obtain ⟨hTrun, hTheight⟩ := h.checkpoint_runBlock adm
  apply h.seed.heightRegimeFrame_succ_of_frameN
    adm hcom hbelow h.crossing h.frame h.c0le h.ready h.postPrev
      h.minimal hblocked hfirst' h.checkpointPreceq hTrun
        h.checkpointErase hTheight
  · intro b tb hb hemit hrow hround
    exact h.seed.confirmationWitness_of_sameRound_honestHeightRow_of_frame_named
      adm hcom hbelow h.crossing h.frame h.ready hb hemit hrow hround
  · intro r hr hhor w hw W hW
    exact ((h.laterHistory_main adm hcom hbelow hr).2 hhor).2 w hw W hW


/-- The closed run-scoped successor selected from an honest row in the next
height window. -/
theorem succ_of_row_named
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (h : NamedHeightRegimeRun S rho r0 blocked first i a ta
      Cfg T Tprev c0)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (hstart : honestHMaxBeforeIndex S rho
      (inclusiveEventIndex rho (S.a r0)) < blocked)
    (hblocked : 1 ≤ blocked)
    {first' : Nat} (hwin : HeightWindowAt S rho (blocked + 1 + 1) first')
    {i0 : Nat} {a0 : NamedAttestation V} {t0 : Time}
    (hiStop0 : i0 < first') (haHon0 : a0.val_index ∈ rho.honest)
    (hiEvent0 : rho.events[i0]? = some (Event.tick a0.val_index t0))
    (hiOutput0 : Object.attest a0 ∈
      NamedRun.emittedAt S rho i0 a0.val_index t0)
    (hrow0 : a0.height_pair.erase.height? = some (blocked + 1 + 1)) :
    ∃ (i' : Nat) (a' : NamedAttestation V) (ta' : Time)
      (Cfg' T' : NamedBlock V),
      NamedHeightRegimeRun S rho r0 (blocked + 1) first' i' a' ta'
        Cfg' T' T (a.round + 1) ∧
      a.round < a'.round ∧ Block.Preceq T.erase T'.erase := by
  classical
  have hframe' := h.frame_succ_main adm hcom hbelow hblocked hwin
  let P : Round → Prop := fun r =>
    ∃ (j : Nat) (b : NamedAttestation V) (tb : Time),
      b.round = r ∧ j < first' ∧ b.val_index ∈ rho.honest ∧
        rho.events[j]? = some (Event.tick b.val_index tb) ∧
        Object.attest b ∈ NamedRun.emittedAt S rho j b.val_index tb ∧
        b.height_pair.erase.height? = some (blocked + 1 + 1)
  have hex : ∃ r, P r :=
    ⟨a0.round, i0, a0, t0, rfl, hiStop0, haHon0, hiEvent0,
      hiOutput0, hrow0⟩
  obtain ⟨i', a', ta', har, hi, haHon, hevent, hout, hrow⟩ :=
    Nat.find_spec hex
  have hemit : NamedRun.emits S rho a'.val_index (Object.attest a') ta' :=
    ⟨i', hevent, hout⟩
  have htime : ta' = S.a a'.round :=
    (Proofs.Optimistic.emits_attest_shape S hemit).2
  have hminimal : ∀ (b : NamedAttestation V) (tb : Time),
      b.val_index ∈ rho.honest →
      NamedRun.emits S rho b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1 + 1) →
      a'.round ≤ b.round := by
    intro b tb hbHon hbemit hbrow
    by_contra hnot
    have hlt : b.round < a'.round := Nat.lt_of_not_ge hnot
    have htb : tb < ta' := by
      rw [(Proofs.Optimistic.emits_attest_shape S hbemit).2, htime]
      exact action_strictMono S hlt
    obtain ⟨j, hj, hbout⟩ := hbemit
    have hjFirst : j < first' :=
      (attestationIndex_lt_of_time_lt
        adm.toNamedScheduleWellFormed hj hevent htb).trans hi
    have hPb : P b.round :=
      ⟨j, b, tb, rfl, hjFirst, hbHon, hj, hbout, hbrow⟩
    have hle := Nat.find_min' hex hPb
    rw [← har] at hle
    exact (not_le_of_gt hlt) hle
  have hiStart : inclusiveEventIndex rho (S.a r0) ≤ i' := by
    by_contra hnot
    have hfreshNext : Internal.NoLocalHeightPairBefore S rho
        (inclusiveEventIndex rho (S.a r0)) (blocked + 1 + 1) :=
      noLocalHeightPairBefore_of_frontier_lt S adm
        (hstart.trans_le
          ((Nat.le_succ blocked).trans (Nat.le_succ _)))
    exact hfreshNext (Nat.lt_of_not_ge hnot) haHon hevent hout hrow
  obtain ⟨B, _, _, _, _, hBmem, _, hBh, _, _⟩ :=
    honestEmittedHeightRow_exactFGSelectorWitness S adm haHon hemit hrow
  have hc0' : a.round + 1 ≤ a'.round :=
    h.round_succ_le_of_higherBlock adm haHon hBmem hBh
  have hframeAt : NamedHeightRegimeFrame S rho (blocked + 1)
      (first' - 1) T a'.round := {
    floor := hframe'.floor
    prevRun := hframe'.prevRun
    prevHeight := hframe'.prevHeight
    rootBelow := hframe'.rootBelow
    sourceAbove := hframe'.sourceAbove }
  have hfrontierAt : honestHMaxBeforeIndex S rho i' < blocked + 1 + 2 :=
    Nat.lt_succ_of_le (hwin.before i' hi)
  obtain ⟨Cfg', T0, hseed', hpost', hG1'⟩ :=
    honestHeightRow_prefixFGSelectorCone_of_namedHeightRegimeFrame
      S adm hbelow hgst hframeAt hiStart hi haHon hevent hout hrow
        hfrontierAt
  obtain ⟨K, _hKmem, hKerase, hKheight, hKCfg, hKrun⟩ :=
    action_named_checkpoint S adm hseed'.signerHonest hseed'.sourceMem
  have hKT0 : K.erase = T0 :=
    hKerase.trans hseed'.checkpointDerived.symm
  have hseedK : PrefixFGSelectorConeAt S rho
      (inclusiveEventIndex rho (S.a r0)) first' (blocked + 1)
      i' a' ta' Cfg' K.erase := by
    rw [hKT0]
    exact hseed'
  have hTCfg' : NamedBlock.Preceq T Cfg' :=
    hframeAt.sourceAbove a'.val_index hseed'.signerHonest a'.round
      (Nat.le_sub_one_of_lt
        (hseed'.actionPrefix_lt adm.toNamedScheduleWellFormed))
      (hseed'.actionHorizon adm) Cfg' hseed'.sourceMem
      hseed'.exactFGSource hseed'.sourceDerivedHeight
  have hTK : NamedBlock.Preceq T K := by
    rcases Block.preceq_linear (Proofs.NamedWire.erase_preceq hTCfg')
        (Proofs.NamedWire.erase_preceq hKCfg) with hTKraw | hKTRaw
    · obtain ⟨Q, hQK, hQerase⟩ :=
        Proofs.NamedAncestry.erased_ancestor_lift K hTKraw
      have hQrun : RunBlock S rho Q :=
        Proofs.NamedRuntime.blockInRun_of_ancestor S rho hKrun hQK
      have hQT : Q = T := by
        apply adm.toNamedRootCollisionFree.root_injective
          Q T hQrun hframeAt.prevRun Q T
          (Or.inl (Proofs.NamedAncestry.named_self Q))
          (Or.inr (Proofs.NamedAncestry.named_self T))
        rw [← Proofs.NamedWire.erase_root Q, hQerase, Proofs.NamedWire.erase_root]
      rw [← hQT]
      exact hQK
    · obtain ⟨Q, hQT, hQerase⟩ :=
        Proofs.NamedAncestry.erased_ancestor_lift T hKTRaw
      have hQrun : RunBlock S rho Q :=
        Proofs.NamedRuntime.blockInRun_of_ancestor S rho hframeAt.prevRun hQT
      have hQK : Q = K := by
        apply adm.toNamedRootCollisionFree.root_injective
          Q K hQrun hKrun Q K
          (Or.inl (Proofs.NamedAncestry.named_self Q))
          (Or.inr (Proofs.NamedAncestry.named_self K))
        rw [← Proofs.NamedWire.erase_root Q, hQerase, Proofs.NamedWire.erase_root]
      have hKT : NamedBlock.Preceq K T := by
        rw [← hQK]
        exact hQT
      have hmono := Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hKT
      have hKsourceHeight :
          (Protocol.derive_named S.E S.cfg K).h = blocked + 1 + 1 :=
        hKheight.trans hseed'.sourceDerivedHeight
      rw [hKsourceHeight] at hmono
      exact False.elim
        (Nat.not_succ_le_self (blocked + 1)
          (hmono.trans hframeAt.prevHeight))
  have hKsourceHeight :
      (Protocol.derive_named S.E S.cfg K).h = blocked + 1 + 1 :=
    hKheight.trans hseed'.sourceDerivedHeight
  have hready := hseed'.ready_of_postGSTStart adm hgst
    (strictEventIndex_le_inclusiveEventIndex rho (S.a r0))
  refine ⟨i', a', ta', Cfg', K, {
    seed := hseedK
    checkpointPreceq := hKCfg
    checkpointErase := hKerase
    crossing := hwin
    frame := hframe'
    c0le := hc0'
    ready := hready
    postPrev := hpost'
    g1 := hG1'
    pred := ?_
    minimal := hminimal }, Nat.lt_of_succ_le hc0',
      Proofs.NamedWire.erase_preceq hTK⟩
  intro b tb hb hbemit _hbefore R hRrun _hRh hpair hR _w _hw _time
    _hfrontier _hroot
  have hbrow : b.height_pair.erase.height? = some (blocked + 1) := by
    rw [hpair]
    rfl
  have hRTerase : R.erase = T.erase :=
    Option.some.inj
      (hR.symm.trans (h.witness_eq adm hcom hbelow hb hbemit hbrow))
  obtain ⟨hTrun, _hTheight⟩ := h.checkpoint_runBlock adm
  have hRT : R = T := by
    apply adm.toNamedRootCollisionFree.root_injective
      R T hRrun hTrun R T
      (Or.inl (Proofs.NamedAncestry.named_self R))
      (Or.inr (Proofs.NamedAncestry.named_self T))
    rw [← Proofs.NamedWire.erase_root R, hRTerase, Proofs.NamedWire.erase_root]
  rw [hRT]
  exact hTK


/-- The closed successor at the next first height crossing. -/
theorem succ_named
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (h : NamedHeightRegimeRun S rho r0 blocked first i a ta
      Cfg T Tprev c0)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (hstart : honestHMaxBeforeIndex S rho
      (inclusiveEventIndex rho (S.a r0)) < blocked)
    (hblocked : 1 ≤ blocked)
    {first' : Nat}
    (hfirst' : FirstHeightProgressAt S rho (blocked + 1 + 1) first') :
    ∃ (i' : Nat) (a' : NamedAttestation V) (ta' : Time)
      (Cfg' T' : NamedBlock V),
      NamedHeightRegimeRun S rho r0 (blocked + 1) first' i' a' ta'
        Cfg' T' T (a.round + 1) ∧
      a.round < a'.round ∧ Block.Preceq T.erase T'.erase := by
  have hcross : PrefixHeightCrossingWitness S rho first' (blocked + 1) :=
    prefixHeightCrossingWitness_of_frontier_eq S adm
      (Nat.succ_le_succ (Nat.zero_le blocked)) hfirst'.frontier
  have hfresh : Internal.NoLocalHeightPairBefore S rho
      (inclusiveEventIndex rho (S.a r0)) (blocked + 1) :=
    noLocalHeightPairBefore_of_frontier_lt S adm
      (hstart.trans_le (Nat.le_succ blocked))
  obtain ⟨i0, a0, t0, _, _, -, hiStop0, haHon0, hiEvent0,
    hiOutput0, _, _, _, _, _, _, _, _, hrow0⟩ :=
    prefixHeightCrossing_exactFGSelectorWitness
      S adm hbelow hcross hfresh
  have hrow0' :
      a0.height_pair.erase.height? = some (blocked + 1 + 1) := by
    rcases hrow0 with ht | ht <;> exact ht ▸ rfl
  exact h.succ_of_row_named adm hcom hbelow hgst hstart hblocked
    hfirst'.toWindow hiStop0 haHon0 hiEvent0 hiOutput0 hrow0'


/-- The closed successor at a height that the run never crosses above. -/
theorem succ_uncrossed_named
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (h : NamedHeightRegimeRun S rho r0 blocked first i a ta
      Cfg T Tprev c0)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (hstart : honestHMaxBeforeIndex S rho
      (inclusiveEventIndex rho (S.a r0)) < blocked)
    (hblocked : 1 ≤ blocked)
    (hnever : ∀ j : Nat,
      honestHMaxBeforeIndex S rho j ≤ blocked + 1 + 1)
    {b : NamedAttestation V} {tb : Time}
    (hb : b.val_index ∈ rho.honest)
    (hemit : NamedRun.emits S rho b.val_index (Object.attest b) tb)
    (hrow : b.height_pair.erase.height? = some (blocked + 1 + 1)) :
    ∃ (i' : Nat) (a' : NamedAttestation V) (ta' : Time)
      (Cfg' T' : NamedBlock V),
      NamedHeightRegimeRun S rho r0 (blocked + 1)
        (rho.events.length + 1) i' a' ta' Cfg' T' T (a.round + 1) ∧
      a.round < a'.round ∧ Block.Preceq T.erase T'.erase := by
  obtain ⟨j, hj, hout⟩ := hemit
  have hjlt : j < rho.events.length :=
    (List.getElem?_eq_some_iff.mp hj).1
  exact h.succ_of_row_named adm hcom hbelow hgst hstart hblocked
    ⟨Nat.succ_pos _, fun k _ => hnever k⟩ (Nat.lt_succ_of_lt hjlt)
      hb hj hout hrow


end NamedHeightRegimeRun

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
