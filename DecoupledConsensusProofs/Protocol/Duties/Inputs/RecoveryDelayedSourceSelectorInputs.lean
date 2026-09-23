module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoverySelectedG2SGHistory
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryDelayedSourceSeed
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryFGSelectorPrefixSeed
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.FGSourceRawGrade
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.RecoveryFirstFGCone
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedEntryCanonical
public import DecoupledConsensusProofs.Protocol.Grades.RelativeSeedK3
public import DecoupledConsensusProofs.Objects.SGTargetCompatibility
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightRegimeFrameBase

@[expose] public section

/-!
# Delayed recovery-source selector inputs
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic
open Internal.NamedRecoveryRead
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The local facts extracted from one settled gate-off predecessor round.
They are the exact inputs used by the fresh-anchor viability proof. -/
structure DelayedRecoverySourceInputs
    (S : Setup V) (rho : Run V) (r : Round) (M : Height) : Prop where
  positive : 0 < r
  postPrevious : S.E.t_GST ≤ S.a (r - 1)
  actionHorizon : S.a r ≤ rho.horizon
  previousFrontier : ∀ u ∈ rho.honest,
    (rho.storeBeforeTime S u (S.a (r - 1))).h_max = M
  sourceFrontier : ∀ u ∈ rho.honest,
    (rho.storeBeforeTime S u (S.a r)).h_max = M
  sourceGateOff : ∀ u ∈ rho.honest,
    (rho.storeBeforeTime S u (S.a r)).h_j + 2 ≤ M
  carrierG2 : RelativeCarrierWindowAt S rho (r - 1) .g2
  carrierG1 : RelativeCarrierWindowAt S rho (r - 1) .g1
  majority : Internal.NamedOutageEntry.GradeFormingMajority S rho r
/-- The genuine-clear selector branch from the fully named regime frame and
the delayed settled-predecessor inputs. -/
theorem voterAnchorSourceClearInputs_of_namedHeightRegimeFrame_delayed
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {r : Round} (ready : GradeRoundReady S rho r)
    {M : Height} (hinputs : DelayedRecoverySourceInputs S rho r M)
    {stop : Nat} {H : Height} {Prev : NamedBlock V} {c0 : Round}
    (hframe : NamedHeightRegimeFrame S rho H stop Prev c0)
    (hactionPrefix : strictEventIndex rho (S.a r) ≤ stop)
    (hfrontier : honestHMaxBeforeIndex S rho stop < H + 2)
    (hactionHor : S.a r ≤ rho.horizon)
    {p : V} (hp : p ∈ rho.honest) {A : Block V} (B : NamedBlock V)
    (hselected : PhaseGrades.nodeQ2
      S (actionReadAt S rho p r) r = some A)
    (hsource : actionFGSource S (actionStoreAt S rho p r) = some B.erase)
    (hBmem : B ∈ (actionStoreAt S rho p r).st.bodies)
    (hBheight : (Protocol.derive_named S.E S.cfg B).h = H + 1)
    (hnot : PhaseGrades.nodeQ2
      S (actionReadAt S rho p r) r ≠ some B.erase) :
    VoterAnchorSourceClearInputs S rho r p B.erase := by
  have hPrevB : NamedBlock.Preceq Prev B :=
    hframe.sourceAbove p hp r hactionPrefix hactionHor B hBmem
      hsource hBheight
  have hPrevBErase : Block.Preceq Prev.erase B.erase :=
    Proofs.NamedWire.erase_preceq hPrevB
  have hfloor : FinalityFloorAt S rho H stop Prev.erase := by
    intro v hv n hn X hXrun hXheight hPrevX
    exact hframe.floor v hv n hn X hXrun hXheight
      (Protocol.namedPreceq_of_runBlock_erase_preceq
        adm hframe.prevRun hXrun hPrevX)
  rcases actionFGSource_genuineClear_or_selectedG2_named
      S rho p r hselected hsource with hclear | hlocal
  · obtain ⟨C, hgenuine, -, -, -, hBC⟩ := hclear
    have hnext : ∀ w ∈ rho.honest, B.erase ∈ filteredTree
        (voteDutyRead S rho w (S.hc.opening_slot r + 1)) := by
      intro w hw
      let vote := Protocol.vote_time S.E (S.hc.opening_slot r + 1)
      have hbody := ancestorGenuineConfirmation_body_at_nextVote_of_floor
        S adm ready hp hgenuine hBC hBmem hfloor hBheight hPrevBErase
          hactionPrefix hactionHor hw
      have hbodyPre : B ∈
          (NamedRun.stateBeforeTime S rho vote w).st.bodies := by
        simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          NamedActionReads.preparedCache, Protocol.NamedStore.setClock,
          vote] using hbody
      have hvoteAction : vote ≤ S.a r := (next_vote_time_lt_action S r).le
      have hvotePrefix : strictEventIndex rho vote ≤ stop :=
        (strictEventIndex_mono rho hvoteAction).trans hactionPrefix
      have heq := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
        S adm.toNamedScheduleWellFormed vote) w
      have hbody' := hbodyPre
      rw [heq] at hbody'
      have hfiltered := hframe.fgRoot_preceq_and_filteredMem
        adm hfrontier hw hvotePrefix hbody' hBheight hPrevB
      rw [← heq] at hfiltered
      simpa only [filteredTree, voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        vote] using hfiltered.2
    refine ⟨hnext, ?_⟩
    intro w hw L hanchor hLB
    rcases voterAnchorAt_cases S rho w
        (S.hc.opening_slot r + 1) with hroot | hactive
    · exfalso
      apply hLB
      rw [← hanchor, hroot]
      exact Proofs.Records.preceq_get_fg_root_of_mem_filtered (hnext w hw)
    · obtain ⟨root, Anchor, hframeL, hactiveL, hanchorL⟩ := hactive
      have hroundDuty : S.hc.round_of
          (voteDutyRead S rho w
            (S.hc.opening_slot r + 1)).st.core.s = r := by
        simpa only [Proofs.Optimistic.voteDutyRead_slot] using
          Proofs.HealingLemmas.round_of_opening_succ S.hc r
      rw [hroundDuty] at hframeL
      have hAnchorEq : Anchor = L := hanchorL.symm.trans hanchor
      have hactiveL' : DecoupledConsensusModel.Protocol.activePrefix
          (filteredTree (voteDutyRead S rho w
            (S.hc.opening_slot r + 1))) root = some L := by
        simpa only [hAnchorEq] using hactiveL
      obtain ⟨Ln, hLnErase, hLnG0, hLnAction, hLnRun⟩ :=
        activeVoterAnchor_namedBody_at_sourceG0_and_action
          S adm hbelow hinputs.positive ready hactionHor hp hw
            hframeL hactiveL
      have hLnErase' : Ln.erase = L := hLnErase.trans hAnchorEq
      have hLgrade : PhaseGrades.storeGrade S.E S.hc
          (PhaseGrades.readAt S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st
          r .g1 L = true :=
        activeVoterAnchor_storeGrade_g1
          S adm hinputs.positive ready hw hframeL hactiveL'
      have hLvote : L ∈ filteredTree
          (voteDutyRead S rho w (S.hc.opening_slot r + 1)) := by
        unfold DecoupledConsensusModel.Protocol.activePrefix at hactiveL'
        exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactiveL')).1
      exact activeVoterAnchor_filtered_at_sourceReads_of_sgWindowNamed
        S adm hbelow hinputs.positive ready hinputs.previousFrontier
          hinputs.sourceFrontier hinputs.sourceGateOff hp hw hframe
          hfrontier hactionPrefix hBmem hBheight hPrevB hactionHor
          hinputs.majority hinputs.carrierG1 hLnErase' hLnG0 hLnAction
          hLnRun hLgrade hLvote hLB
  · exact False.elim (hnot (hlocal ▸ hselected))

/-- The closed delayed selector over the fully named height-regime frame. -/
theorem honestHeightRow_prefixFGSelectorCone_of_namedFrame_delayed
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {r0 : Round} (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    {stop : Nat} {H : Height} {Prev : NamedBlock V}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    (hframe : NamedHeightRegimeFrame S rho H (stop - 1) Prev a.round)
    (hinputs : DelayedRecoverySourceInputs S rho a.round (H + 1))
    (hiStart : inclusiveEventIndex rho (S.a r0) ≤ i)
    (hiStop : i < stop) (haHon : a.val_index ∈ rho.honest)
    (hiEvent : rho.events[i]? = some (Event.tick a.val_index ta))
    (hiOutput : Object.attest a ∈
      NamedRun.emittedAt S rho i a.val_index ta)
    (hrow : a.height_pair.erase.height? = some (H + 1))
    (hfrontier : honestHMaxBeforeIndex S rho i < H + 2) :
    ∃ (Cfg : NamedBlock V) (T : Block V),
      PrefixFGSelectorConeAt S rho
        (inclusiveEventIndex rho (S.a r0)) stop H i a ta Cfg T := by
  have hemit : NamedRun.emits S rho a.val_index (Object.attest a) ta :=
    ⟨i, hiEvent, hiOutput⟩
  obtain ⟨B, J, hta, haAction, hsource, hBmem, hBstoredHeight,
      hBheight, hJderived, hshape⟩ :=
    honestEmittedHeightRow_exactFGSelectorWitness S adm haHon hemit hrow
  have hstrictAction : strictEventIndex rho (S.a a.round) ≤ i := by
    simpa only [hta] using
      (strictEventIndex_le_tickIndex S adm.toNamedScheduleWellFormed hiEvent)
  have hactionHorizon : S.a a.round ≤ rho.horizon := by
    have hin := (adm.in_horizon (Event.tick a.val_index ta)
      (List.mem_of_getElem? hiEvent)).2
    simpa only [Event.time, hta] using hin
  have hroundFromStart : r0 ≤ a.round := by
    by_contra hnot
    have htimeLt : ta < S.a r0 := by
      rw [hta]
      exact action_strictMono S (Nat.lt_of_not_ge hnot)
    have hstartCursor : strictEventIndex rho (S.a r0) ≤ i :=
      (strictEventIndex_le_inclusiveEventIndex rho (S.a r0)).trans hiStart
    have htimeLe : S.a r0 ≤ ta :=
      Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed
        hstartCursor hiEvent
    exact (not_le_of_gt htimeLt) htimeLe
  have ready : GradeRoundReady S rho a.round :=
    gradeRoundReady_of_action_horizon S hgst hroundFromStart hactionHorizon
  obtain ⟨A, hselected⟩ : ∃ A : Block V,
      PhaseGrades.nodeQ2 S
        (actionReadAt S rho a.val_index a.round) a.round = some A := by
    cases hQ : PhaseGrades.nodeQ2
        S (actionReadAt S rho a.val_index a.round) a.round with
    | none =>
        have hsource' := hsource
        unfold actionFGSource at hsource'
        dsimp only at hsource'
        have hround : S.hc.round_of
            (actionStoreAt S rho a.val_index a.round).st.core.toHealing.s =
              a.round := by
          simpa only [Protocol.Store.toHealing] using
            actionStoreAt_round S rho a.val_index a.round
        rw [hround] at hsource'
        change Protocol.grade2_block_with
          (NamedProfile.gradeContract
            (actionReadAt S rho a.val_index a.round).cache)
          S.E S.hc
          (actionReadAt S rho a.val_index a.round).st.core.toHealing
          a.round = none at hQ
        simp only [actionStoreAt] at hsource'
        rw [Protocol.fg_source_with.eq_def, hQ] at hsource'
        cases hsource'
    | some A => exact ⟨A, rfl⟩
  have hframeAt : NamedHeightRegimeFrame S rho H i Prev a.round :=
    { floor := fun v hv n hn => hframe.floor v hv n
        (hn.trans (Nat.le_sub_one_of_lt hiStop))
      prevRun := hframe.prevRun
      prevHeight := hframe.prevHeight
      rootBelow := fun v hv n hn => hframe.rootBelow v hv n
        (hn.trans (Nat.le_sub_one_of_lt hiStop))
      sourceAbove := fun p hp r hr => hframe.sourceAbove p hp r
        (hr.trans (Nat.le_sub_one_of_lt hiStop)) }
  have hK6Q2 : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some B.erase →
      VoterAnchorSourceQ2Inputs S rho a.round a.val_index B.erase := by
    intro hlocal
    exact voterAnchorSourceQ2Inputs_of_namedHeightRegimeFrame_at_source
      S adm ready hframeAt hstrictAction hfrontier hactionHorizon
        haHon B hlocal hsource hBmem hBheight
  have hK6Clear : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round ≠ some B.erase →
      VoterAnchorSourceClearInputs S rho a.round a.val_index B.erase := by
    intro hnot
    exact voterAnchorSourceClearInputs_of_namedHeightRegimeFrame_delayed
      S adm hbelow ready hinputs hframeAt hstrictAction hfrontier
        hactionHorizon haHon B hselected hsource hBmem hBheight hnot
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hbelow
  have hcone :
      NamedHonestVotesCone S rho (S.hc.opening_slot a.round)
          (fun X => Block.Preceq B.erase X) ∨
        NamedHonestVotesCone S rho (S.hc.opening_slot a.round + 1)
          (fun X => Block.Preceq B.erase X) := by
    rcases recoveryFGSelectorSeed_beforeAction_of_sourceInputs
        S adm hsb hinputs.positive ready haHon hselected hsource hBmem
          hBheight hactionHorizon hK6Q2 hK6Clear with hopen | hrest
    · exact Or.inl hopen
    · rcases hrest with hprogress | hnext
      · rcases hprogress with ⟨v, hv, u, hu, hmax⟩
        have huBeforeAction : u < S.a a.round :=
          hu.trans_lt (next_vote_time_lt_action S a.round)
        have huCursor : inclusiveEventIndex rho u ≤
            strictEventIndex rho (S.a a.round) := by
          rw [strictEventIndex_eq_inclusiveEventIndex_pred]
          exact inclusiveEventIndex_mono rho
            (Int.le_sub_one_iff.mpr huBeforeAction)
        have hlocal : (rho.storeAt S v u).h_max ≤
            honestHMaxBeforeIndex S rho i := by
          rw [storeAt_eq_stateBefore_inclusiveEventIndex
            S adm.toNamedScheduleWellFormed v u]
          exact (localHMax_le_honestHMaxBeforeIndex S rho
            (inclusiveEventIndex rho u) hv).trans
            (honestHMaxBeforeIndex_mono S rho
              (huCursor.trans hstrictAction))
        have hHthree : H + 3 ≤ honestHMaxBeforeIndex S rho i := by
          have heq : H + 3 = (H + 1) + 2 := by
            simp only [Nat.add_assoc]
          rw [heq]
          exact hmax.trans hlocal
        have hstep : H + 2 < H + 3 := by
          simpa only [Nat.add_assoc] using Nat.lt_succ_self (H + 2)
        exact False.elim
          ((Nat.not_lt_of_ge (hstep.le.trans hHthree)) hfrontier)
      · exact Or.inr hnext
  have hBpre : B ∈
      (rho.stateBeforeTime S (S.a a.round) a.val_index).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hBmem
  have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime
    S rho (S.a a.round) a.val_index B hBpre
  have hcheckpoint : J =
      ((actionStoreAt S rho a.val_index a.round).st.core.σ B.erase).T_h := by
    have hviewAction :
        (actionStoreAt S rho a.val_index a.round).st.core.σ B.erase =
          Protocol.derive_named S.E S.cfg B := by
      simpa only [actionStoreAt, actionReadAt,
        NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
        NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hview
    calc
      J = (Protocol.derive_named S.E S.cfg B).T_h := hJderived
      _ = ((actionStoreAt S rho a.val_index a.round).st.core.σ
          B.erase).T_h := by rw [hviewAction]
  exact ⟨B, J, {
    startLeIndex := hiStart
    indexLtStop := hiStop
    signerHonest := haHon
    exactTick := hiEvent
    tickOutput := hiOutput
    emitted := hemit
    actionTime_eq := hta
    exactAction := haAction
    exactFGSource := hsource
    sourceMem := hBmem
    sourceStoredHeight := hBstoredHeight
    sourceDerivedHeight := hBheight
    checkpointStored := hcheckpoint
    checkpointDerived := hJderived
    targetOrTimeout := hshape
    cone := hcone }⟩

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
