module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.FGConfirmationHistory
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.FirstProgressFGWitness
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightRegimeFrame
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightRegimeFrameBase
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.RecoveryFGRoundAgreement
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryFGSelectorPrefixSeed
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.RecoveryFirstFGCone
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryDelayedSourceSeed
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.RecoveryDelayedSourceSelectorInputs
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoverySelectedG2SGHistory
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedEntryCanonical
public import DecoupledConsensusProofs.Protocol.Grades.RelativeSeedK3
public import DecoupledConsensusProofs.Objects.SGTargetCompatibility
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.FGSourceRawGrade
public import Mathlib.Data.Int.LeastGreatest
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RawHeightProgress
public import DecoupledConsensusProofs.Protocol.ChainState.SlashableBoundBridge
public import DecoupledConsensusProofs.Objects.EmittedHeightBound
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityCertificates
public import DecoupledConsensusProofs.Execution.OutageProvenance
public import DecoupledConsensusProofs.Protocol.Grades.VoterAnchorSourceInputs
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusInternal.Definitions.NamedDutyReads
public import DecoupledConsensusInternal.Definitions.NamedLifecycle

@[expose] public section

/-!
# Named height-regime records

These records are the  twins of `HeightRegimeFrame`, `HeightRegime`, and
`HeightRegimeBase`. the prior records remain unchanged in their original modules.
Every block that has a derived height is a `NamedBlock`, and every emitted row
is a `NamedAttestation`.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Internal.NamedRecoveryRead

variable {V : Type} [DecidableEq V] [Fintype V]




namespace NamedHeightRegimeDelayed

variable {S : Setup V} {rho : Run V} {r0 : Round} {blocked : Height}
  {first i : Nat} {a : NamedAttestation V} {ta : Time}
  {Cfg T Tprev : NamedBlock V} {c0 : Round} {hF0 M : Height}



end NamedHeightRegimeDelayed

namespace NamedHeightRegime

variable {S : Setup V} {rho : Run V} {r0 : Round} {blocked : Height}
  {first i : Nat} {a : NamedAttestation V} {ta : Time}
  {Cfg T Tprev : NamedBlock V} {c0 : Round}






end NamedHeightRegime
/-- The named old-target root bound used by the base record. -/
def NamedOldTargetRootBelow
    (S : Setup V) (rho : Run V) (first : Nat) (blocked : Height)
    (T : NamedBlock V) : Prop :=
  ∀ (a : NamedAttestation V) (ta : Time), a.val_index ∈ rho.honest →
    NamedRun.emits S rho a.val_index (Object.attest a) ta →
    strictEventIndex rho (S.a a.round) < first →
    ∀ R : NamedBlock V,
      (Protocol.derive_named S.E S.cfg R).h = blocked →
      a.height_pair.erase = HeightPair.target blocked R.erase.root →
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
        some R.erase →
      ∀ w ∈ rho.honest, ∀ time : Time,
        blocked < (rho.storeBeforeTime S w time).h_max →
        Protocol.get_fg_root
          (rho.storeBeforeTime S w time).core.toHealing.toFG = R.erase →
        NamedBlock.Preceq R T

/-- A height regime with named source, checkpoint, predecessor, and row. -/
structure NamedHeightRegime
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
  g1 : ∀ w ∈ rho.honest,
    ∃ Q : Block V, namedG1At S rho w a.round Q
  pred : NamedOldTargetRootBelow S rho first blocked T
  minimal : ∀ (b : NamedAttestation V) (tb : Time),
    b.val_index ∈ rho.honest →
    NamedRun.emits S rho b.val_index (Object.attest b) tb →
    b.height_pair.erase.height? = some (blocked + 1) → a.round ≤ b.round

/-- A named height regime selected after a settled predecessor round.

This additive record retains the recovery and delayed-read inputs used by the
closed history folds. `NamedHeightRegime` remains unchanged for existing
callers. -/
structure NamedHeightRegimeDelayed
    (S : Setup V) (rho : Run V) (r0 : Round) (blocked : Height)
    (first i : Nat) (a : NamedAttestation V) (ta : Time)
    (Cfg T Tprev : NamedBlock V) (c0 : Round)
    (hF0 M : Height) : Prop extends
      NamedHeightRegime S rho r0 blocked first i a ta Cfg T Tprev c0 where
  firstProgress : FirstHeightProgressAt S rho (blocked + 1) first
  prefixCap : HonestPrefixFinalityCap S rho first hF0
  recoveryHeight : NjGap.RecoveryHeight S.cfg hF0 blocked
  delayedInputs : DelayedRecoverySourceInputs S rho a.round (blocked + 1)
  selectedG2 : ∃ Q : Block V,
    PhaseGrades.nodeQ2 S
        (actionReadAt S rho a.val_index a.round) a.round = some Q ∧
      Block.Preceq T.erase Q
  sourcePostTwo : S.E.t_GST ≤ S.a (a.round - 2)
  sourceTwoRoundHorizon : S.a (a.round + 2) ≤ rho.horizon
  settledPredecessor : GateOffFrameAt S rho M
    (a.round - 2) (a.round + 2)
  gateOffThrough : ∀ {c : Round}, a.round ≤ c → S.a c ≤ rho.horizon →
    GateOffFrameAt S rho M (a.round - 2) c
  readSide : ∀ {c : Round}, a.round ≤ c → S.a c ≤ rho.horizon →
    Nonempty (RecoverySGReadSidePackage S rho a.round c T.erase)

namespace NamedHeightRegimeDelayed

variable {S : Setup V} {rho : Run V} {r0 : Round} {blocked : Height}
  {first i : Nat} {a : NamedAttestation V} {ta : Time}
  {Cfg T Tprev : NamedBlock V} {c0 : Round} {hF0 M : Height}

/-- Project the underlying named regime. -/
theorem regime
    (h : NamedHeightRegimeDelayed S rho r0 blocked first i a ta
      Cfg T Tprev c0 hF0 M) :
    NamedHeightRegime S rho r0 blocked first i a ta Cfg T Tprev c0 :=
  h.toNamedHeightRegime

#print axioms NamedHeightRegimeDelayed.regime

end NamedHeightRegimeDelayed

namespace NamedHeightRegime

variable {S : Setup V} {rho : Run V} {r0 : Round} {blocked : Height}
  {first i : Nat} {a : NamedAttestation V} {ta : Time}
  {Cfg T Tprev : NamedBlock V} {c0 : Round}

/-- A named vote cone identifies the prepared head emitted by each honest
committee member. -/
theorem committeeHead_of_cone
    (adm : Admissible S rho) {s : Slot} (hs : 0 < s)
    (hhor : Protocol.vote_time S.E s ≤ rho.horizon) {B : Block V}
    (hcone : NamedHonestVotesCone S rho s (fun X => Block.Preceq B X))
    {w : V} (hw : w ∈ rho.honest) (hcommittee : w ∈ S.E.committee s) :
    Block.Preceq B (voterHeadAt S rho w s) := by
  obtain ⟨X, hBX, hXrun, hXemit⟩ := hcone w hw hcommittee
  obtain ⟨Y, hYhead, hYrun, hYemit⟩ :=
    named_voter_head_emits S adm hw hs hcommittee hhor
  have hvote : (⟨w, s, X.erase.root⟩ : GoldfishVote V) =
      ⟨w, s, Y.erase.root⟩ :=
    Proofs.Optimistic.emits_gfVote_unique S adm.toNamedScheduleWellFormed
      hXemit hYemit rfl
  have hroot : X.root = Y.root := by
    rw [← Proofs.NamedWire.erase_root X, ← Proofs.NamedWire.erase_root Y]
    exact congrArg GoldfishVote.head hvote
  have hXY : X = Y :=
    adm.toNamedRootCollisionFree.root_injective X Y hXrun hYrun X Y
      (Or.inl (Proofs.NamedAncestry.named_self X))
      (Or.inr (Proofs.NamedAncestry.named_self Y)) hroot
  rw [← hYhead, ← hXY]
  exact hBX

private theorem actionBody_runBlock_named_regime
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionStoreAt S rho v r).st.bodies) :
    RunBlock S rho D := by
  have hDpre : D ∈ (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    simpa only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
      NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hD
  obtain ⟨i, hi, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedScheduleWellFormed.sorted (S.a r)
  have hDi : D ∈ (rho.stateBefore S i v).st.bodies := by
    change D ∈ (NamedRun.stateBefore S rho i v).st.bodies
    rw [← hi]
    exact hDpre
  exact Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hDi)

/-- The named checkpoint is a run block at the source height. -/
theorem checkpoint_runBlock
    (adm : Admissible S rho)
    (h : NamedHeightRegime S rho r0 blocked first i a ta Cfg T Tprev c0) :
    RunBlock S rho T ∧
      (Protocol.derive_named S.E S.cfg T).h = blocked + 1 := by
  have hCfgRun : RunBlock S rho Cfg :=
    actionBody_runBlock_named_regime S adm h.seed.signerHonest h.seed.sourceMem
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

/-- A named body one height above the regime can occur only after the source
round. -/
theorem round_succ_le_of_higherBlock
    (adm : Admissible S rho)
    (h : NamedHeightRegime S rho r0 blocked first i a ta Cfg T Tprev c0)
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
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hBmem
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

end NamedHeightRegime

/-- The height-regime base with named predecessor, rows, roots, and blocks. -/
structure NamedHeightRegimeBase
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
    ∀ R : NamedBlock V,
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





/-- The named regime from a named base. The extra callback is the direct
fully named selector-frame route; it does not convert the predecessor height
to `derived_state` on the erased block. -/
theorem NamedHeightRegimeBase.exists_regime
    {S : Setup V} {rho : Run V} {r0 : Round} {blocked : Height}
    {first : Nat} {Tprev : NamedBlock V}
    (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (h : NamedHeightRegimeBase S rho r0 blocked first Tprev)
    (hselector : ∀ {i : Nat} {a : NamedAttestation V} {ta : Time},
      (hframe : NamedHeightRegimeFrame S rho blocked
        (first - 1) Tprev a.round) →
      inclusiveEventIndex rho (S.a r0) ≤ i → i < first →
      a.val_index ∈ rho.honest →
      rho.events[i]? = some (Event.tick a.val_index ta) →
      Object.attest a ∈ NamedRun.emittedAt S rho i a.val_index ta →
      a.height_pair.erase.height? = some (blocked + 1) →
      honestHMaxBeforeIndex S rho i < blocked + 2 →
      ∃ (Cfg : NamedBlock V) (T : Block V),
        PrefixFGSelectorConeAt S rho
          (inclusiveEventIndex rho (S.a r0)) first blocked i a ta Cfg T ∧
        S.E.t_GST ≤ S.a (a.round - 1) ∧
        ∀ w ∈ rho.honest, ∃ Q : Block V, namedG1At S rho w a.round Q) :
    ∃ (i : Nat) (a : NamedAttestation V) (ta : Time)
      (Cfg T : NamedBlock V),
      NamedHeightRegime S rho r0 blocked first i a ta Cfg T Tprev a.round := by
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
    hselector hframe hiStart hi haHon hevent hout hrow hfrontierAt
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
  intro b tb hb hbemit hbefore R hRh hpair hR w hw time hfrontier hroot
  exact h.oldRoot b tb hb hbemit hbefore R hRh hpair hR w hw time
    hfrontier hroot K hKrun hKsourceHeight hTprevK

#print axioms NamedHeightRegimeBase.exists_regime

/-- Closed named base constructor for rows selected after the delayed boundary.
The input family is instantiated only at the least selected row's round. -/
theorem NamedHeightRegimeBase.exists_regime_delayed
    {S : Setup V} {rho : Run V} {g : Round} {blocked : Height}
    {first : Nat} {Tprev : NamedBlock V}
    (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ (g + 1))
    (h : NamedHeightRegimeBase S rho (g + 1) blocked first Tprev)
    (hinputs : ∀ r : Round, g + 1 ≤ r →
      DelayedRecoverySourceInputs S rho r (blocked + 1)) :
    ∃ (i : Nat) (a : NamedAttestation V) (ta : Time)
      (Cfg T : NamedBlock V),
      NamedHeightRegime S rho (g + 1) blocked first i a ta
        Cfg T Tprev a.round := by
  apply h.exists_regime adm hbelow hgst
  intro i a ta hframe hiStart hiStop haHon hiEvent hiOutput hrow hfrontier
  have hemit : NamedRun.emits S rho a.val_index (Object.attest a) ta :=
    ⟨i, hiEvent, hiOutput⟩
  have htime : ta = S.a a.round :=
    (Proofs.Optimistic.emits_attest_shape S hemit).2
  have hround : g + 1 ≤ a.round := by
    by_contra hnot
    have htimeLt : ta < S.a (g + 1) := by
      rw [htime]
      exact action_strictMono S (Nat.lt_of_not_ge hnot)
    have hcursor : strictEventIndex rho (S.a (g + 1)) ≤ i :=
      (strictEventIndex_le_inclusiveEventIndex rho (S.a (g + 1))).trans
        hiStart
    have htimeLe : S.a (g + 1) ≤ ta :=
      Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed
        hcursor hiEvent
    exact (not_le_of_gt htimeLt) htimeLe
  have hrowInputs := hinputs a.round hround
  obtain ⟨Cfg, T0, hseed⟩ :=
    honestHeightRow_prefixFGSelectorCone_of_namedFrame_delayed
      S adm hbelow hgst hframe hrowInputs hiStart hiStop haHon
        hiEvent hiOutput hrow hfrontier
  obtain ⟨B, _J, _hta, _haAction, hsource, _hBmem,
      _hBstoredHeight, _hBheight, _hJderived, _hshape⟩ :=
    honestEmittedHeightRow_exactFGSelectorWitness S adm haHon hemit hrow
  have hactionHorizon : S.a a.round ≤ rho.horizon := by
    have hin := (adm.in_horizon (Event.tick a.val_index ta)
      (List.mem_of_getElem? hiEvent)).2
    simpa only [Event.time, htime] using hin
  have ready : GradeRoundReady S rho a.round :=
    gradeRoundReady_of_action_horizon S hgst hround hactionHorizon
  have hguard := crossReaderBodyReadyGuard_of_namedHeightRegimeFrame
    S adm hbelow hgst hframe hiStart hiStop haHon hiEvent hiOutput
      hrow hfrontier
  have hrawG1 := actionFGSource_rawG1_at_firstInterior
    S adm hbelow ready hactionHorizon haHon hsource hguard
  have hG1 : ∀ w ∈ rho.honest,
      ∃ Q : Block V, namedG1At S rho w a.round Q := by
    intro w hw
    obtain ⟨Q, _hQ, hgrade⟩ := hrawG1 w hw
    exact ⟨Q, hgrade⟩
  exact ⟨Cfg, T0, hseed, hrowInputs.postPrevious, hG1⟩

#print axioms NamedHeightRegimeBase.exists_regime_delayed



/-- The deadline wrapper, pre-built from the pending named base-regime
constructor. The hypothesis is the exact result that `exists_regime` must
produce. -/
theorem NamedHeightRegimeBase.exists_regime_before_deadline_of_exists_regime
    {S : Setup V} {rho : Run V} {r0 : Round} {blocked : Height}
    {first : Nat} {Tprev : NamedBlock V}
    (adm : Admissible S rho)
    (_h : NamedHeightRegimeBase S rho r0 blocked first Tprev)
    (hexists : ∃ (i : Nat) (a : NamedAttestation V) (ta : Time)
      (Cfg T : NamedBlock V),
      NamedHeightRegime S rho r0 blocked first i a ta Cfg T Tprev a.round)
    {deadline : Round}
    (hdeadline : first ≤ inclusiveEventIndex rho (S.a deadline)) :
    ∃ (i : Nat) (a : NamedAttestation V) (ta : Time)
      (Cfg T : NamedBlock V),
      NamedHeightRegime S rho r0 blocked first i a ta Cfg T Tprev a.round ∧
        a.round ≤ deadline := by
  obtain ⟨i, a, ta, Cfg, T, hreg⟩ := hexists
  refine ⟨i, a, ta, Cfg, T, hreg, ?_⟩
  have hi : i < inclusiveEventIndex rho (S.a deadline) :=
    hreg.seed.indexLtStop.trans_le hdeadline
  have hfilter : rho.events.filter (fun e => decide (e.time ≤ S.a deadline)) =
      rho.events.take (inclusiveEventIndex rho (S.a deadline)) := by
    simpa only [inclusiveEventIndex] using
      Proofs.Optimistic.filter_eq_take S adm.toNamedScheduleWellFormed _
        (Proofs.Optimistic.downward_le (S.a deadline))
  have hmem : Event.tick a.val_index ta ∈
      rho.events.take (inclusiveEventIndex rho (S.a deadline)) := by
    apply List.mem_of_getElem? (i := i)
    rw [List.getElem?_take_of_lt hi]
    exact hreg.seed.exactTick
  rw [← hfilter] at hmem
  have htime : S.a a.round ≤ S.a deadline := by
    simpa only [Event.time, hreg.seed.actionTime_eq, decide_eq_true_eq] using
      (List.mem_filter.mp hmem).2
  exact (action_strictMono S).le_iff_le.mp htime

#print axioms
  NamedHeightRegimeBase.exists_regime_before_deadline_of_exists_regime

/-- The delayed named base regime selected before a deadline. -/
theorem NamedHeightRegimeBase.exists_regime_before_deadline_named
    {S : Setup V} {rho : Run V} {g : Round} {blocked : Height}
    {first : Nat} {Tprev : NamedBlock V}
    (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ (g + 1))
    (h : NamedHeightRegimeBase S rho (g + 1) blocked first Tprev)
    (hinputs : ∀ r : Round, g + 1 ≤ r →
      DelayedRecoverySourceInputs S rho r (blocked + 1))
    {deadline : Round}
    (hdeadline : first ≤ inclusiveEventIndex rho (S.a deadline)) :
    ∃ (i : Nat) (a : NamedAttestation V) (ta : Time)
      (Cfg T : NamedBlock V),
      NamedHeightRegime S rho (g + 1) blocked first i a ta
          Cfg T Tprev a.round ∧
        a.round ≤ deadline := by
  exact NamedHeightRegimeBase.exists_regime_before_deadline_of_exists_regime
    adm h (h.exists_regime_delayed adm hbelow hgst hinputs) hdeadline

#print axioms NamedHeightRegimeBase.exists_regime_before_deadline_named


/-- The closed delayed base constructor with all inputs retained for the
history folds. The callback arguments package facts already produced by the
delayed recovery records; they are fields of the result, not premises of the
closed head methods. -/
theorem NamedHeightRegimeBase.exists_regime_before_deadline_delayed
    {S : Setup V} {rho : Run V} {g : Round} {blocked hF0 M : Height}
    {first : Nat} {Tprev : NamedBlock V}
    (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ (g + 1))
    (h : NamedHeightRegimeBase S rho (g + 1) blocked first Tprev)
    (hinputs : ∀ r : Round, g + 1 ≤ r →
      DelayedRecoverySourceInputs S rho r (blocked + 1))
    (hcap : HonestPrefixFinalityCap S rho first hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (hselected : ∀ {i : Nat} {a : NamedAttestation V} {ta : Time}
      {Cfg T : NamedBlock V},
      NamedHeightRegime S rho (g + 1) blocked first i a ta
          Cfg T Tprev a.round →
      ∃ Q : Block V,
        PhaseGrades.nodeQ2 S
            (actionReadAt S rho a.val_index a.round) a.round = some Q ∧
          Block.Preceq T.erase Q)
    (hsourceHorizon : ∀ {i : Nat} {a : NamedAttestation V} {ta : Time}
      {Cfg T : NamedBlock V},
      NamedHeightRegime S rho (g + 1) blocked first i a ta
          Cfg T Tprev a.round →
      S.a (a.round + 2) ≤ rho.horizon)
    (hsourcePost : ∀ {i : Nat} {a : NamedAttestation V} {ta : Time}
      {Cfg T : NamedBlock V},
      NamedHeightRegime S rho (g + 1) blocked first i a ta
          Cfg T Tprev a.round →
      S.E.t_GST ≤ S.a (a.round - 2))
    (hsettled : ∀ {i : Nat} {a : NamedAttestation V} {ta : Time}
      {Cfg T : NamedBlock V},
      NamedHeightRegime S rho (g + 1) blocked first i a ta
          Cfg T Tprev a.round →
      GateOffFrameAt S rho M (a.round - 2) (a.round + 2))
    (hgate : ∀ {i : Nat} {a : NamedAttestation V} {ta : Time}
      {Cfg T : NamedBlock V},
      NamedHeightRegime S rho (g + 1) blocked first i a ta
          Cfg T Tprev a.round →
      ∀ {c : Round}, a.round ≤ c → S.a c ≤ rho.horizon →
        GateOffFrameAt S rho M (a.round - 2) c)
    (hread : ∀ {i : Nat} {a : NamedAttestation V} {ta : Time}
      {Cfg T : NamedBlock V},
      (hreg : NamedHeightRegime S rho (g + 1) blocked first i a ta
        Cfg T Tprev a.round) →
      ∀ {c : Round}, a.round ≤ c → S.a c ≤ rho.horizon →
        RecoverySGReadSidePackage S rho a.round c T.erase)
    {deadline : Round}
    (hdeadline : first ≤ inclusiveEventIndex rho (S.a deadline)) :
    ∃ (i : Nat) (a : NamedAttestation V) (ta : Time)
      (Cfg T : NamedBlock V),
      NamedHeightRegimeDelayed S rho (g + 1) blocked first i a ta
          Cfg T Tprev a.round hF0 M ∧
        a.round ≤ deadline := by
  obtain ⟨i, a, ta, Cfg, T, hreg, hadeadline⟩ :=
    h.exists_regime_before_deadline_named adm hbelow hgst hinputs hdeadline
  have hround : g + 1 ≤ a.round := by
    by_contra hnot
    have htimeLt : ta < S.a (g + 1) := by
      rw [hreg.seed.actionTime_eq]
      exact action_strictMono S (Nat.lt_of_not_ge hnot)
    have hcursor : strictEventIndex rho (S.a (g + 1)) ≤ i :=
      (strictEventIndex_le_inclusiveEventIndex rho (S.a (g + 1))).trans
        hreg.seed.startLeIndex
    have htimeLe : S.a (g + 1) ≤ ta :=
      Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed
        hcursor hreg.seed.exactTick
    exact (not_le_of_gt htimeLt) htimeLe
  refine ⟨i, a, ta, Cfg, T, ?_, hadeadline⟩
  exact {
    toNamedHeightRegime := hreg
    firstProgress := h.crossing
    prefixCap := hcap
    recoveryHeight := hrec
    delayedInputs := hinputs a.round hround
    selectedG2 := hselected hreg
    sourcePostTwo := hsourcePost hreg
    sourceTwoRoundHorizon := hsourceHorizon hreg
    settledPredecessor := hsettled hreg
    gateOffThrough := hgate hreg
    readSide := fun hc hhor => ⟨hread hreg hc hhor⟩ }

#print axioms
  NamedHeightRegimeBase.exists_regime_before_deadline_delayed





end HealingSurface
end Proofs
end DecoupledConsensusModel

end
