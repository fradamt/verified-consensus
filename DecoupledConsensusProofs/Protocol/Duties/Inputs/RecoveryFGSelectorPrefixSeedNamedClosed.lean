module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.GateOffWindowCone
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryFGSelectorPrefixSeed
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryInitialSourceNamedHistory
public import DecoupledConsensusProofs.Protocol.Grades.SameRoundQ2Retained

@[expose] public section

/-!
# Closed named selector seed

This leaf closes the fully named height-regime selector without adding a
callback to the public statement. It stays above the pointwise Q2-retention
and earlier-shaped clear-source producers to avoid an import cycle in the older
selector module.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Internal.NamedRecoveryRead DecoupledConsensusModel.Protocol Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem namedClosed_nodeQ2_exists_of_actionFGSource
    (S : Setup V) (rho : Run V) (v : V) (r : Round)
    {B : NamedBlock V}
    (hsource : actionFGSource S (actionStoreAt S rho v r) = some B.erase) :
    ∃ A, nodeQ2 S (actionReadAt S rho v r) r = some A := by
  have hround : S.hc.round_of
      (actionReadAt S rho v r).st.core.toHealing.s = r := by
    simpa only [Protocol.Store.toHealing] using actionStoreAt_round S rho v r
  have hsource' : nodeFGSource S (actionReadAt S rho v r) r =
      some B.erase := by
    have h := hsource
    simp only [actionFGSource, actionStoreAt] at h
    rw [hround] at h
    simpa only [nodeFGSource] using h
  cases hQ : nodeQ2 S (actionReadAt S rho v r) r with
  | none =>
      have hbad := hsource'
      simp only [nodeFGSource, nodeQ2, nodeRead] at hbad hQ
      unfold Protocol.grade2_block_with at hbad
      rw [hQ] at hbad
      simp [Protocol.fg_source_with] at hbad
  | some A => exact ⟨A, rfl⟩

/-- The selected-Q2 inputs from a fully named frame. The exact action source
and action horizon are the local row facts that the frame needs to recover its
named predecessor relation. -/
theorem voterAnchorSourceQ2Inputs_of_namedHeightRegimeFrame
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (ready : GradeRoundReady S rho r)
    {stop : Nat} {H : Height} {Prev : NamedBlock V} {c0 : Round}
    (hframe : NamedHeightRegimeFrame S rho H stop Prev c0)
    (hactionPrefix : strictEventIndex rho (S.a r) ≤ stop)
    (hfrontier : honestHMaxBeforeIndex S rho stop < H + 2)
    (hactionHor : S.a r ≤ rho.horizon) :
    ∀ {p : V} (B : NamedBlock V),
      p ∈ rho.honest →
      B ∈ (actionStoreAt S rho p r).st.bodies →
      (Protocol.derive_named S.E S.cfg B).h = H + 1 →
      actionFGSource S (actionStoreAt S rho p r) = some B.erase →
      nodeQ2 S (actionReadAt S rho p r) r = some B.erase →
      VoterAnchorSourceQ2Inputs S rho r p B.erase := by
  intro p B hp hBmem hBheight hsource hselected
  have hretained := sameRoundSourceQ2Retained_of_namedFrame
    S adm ready hp hselected hsource hBmem hframe hBheight
      hactionPrefix hfrontier hactionHor
  refine ⟨fun w hw => (hretained w hw).1, ?_⟩
  intro w hw
  have hG0 := (hretained w hw).2.1
  rw [domain_g0_eq_Γ_1, Protocol.Γ_1_eq_vote_time] at hG0
  simpa only [filteredTree, PhaseGrades.readAt, voteDutyRead,
    NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom,
    NamedActionReads.preparedCache, Protocol.NamedStore.setClock] using hG0

#print axioms voterAnchorSourceQ2Inputs_of_namedHeightRegimeFrame

/-- earlier's named-frame selector producer. This ports
`honestHeightRow_prefixFGSelectorCone_of_frame` from earlier's
`RecoveryFGSelectorPrefixSeedRun.lean:307`. The selected-Q2 arm reuses the
existing phase-ladder cone theorem. The genuine-clear arm consumes the
earlier-shaped anchor-compatibility contract directly. -/
theorem honestHeightRow_prefixFGSelectorCone_of_namedHeightRegimeFrame
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {r0 : Round} (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    {stop : Nat} {H : Height} {Prev : NamedBlock V}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    (hframe : NamedHeightRegimeFrame S rho H (stop - 1) Prev a.round)
    (hiStart : inclusiveEventIndex rho (S.a r0) ≤ i)
    (hiStop : i < stop) (haHon : a.val_index ∈ rho.honest)
    (hiEvent : rho.events[i]? = some (Event.tick a.val_index ta))
    (hiOutput : Object.attest a ∈
      NamedRun.emittedAt S rho i a.val_index ta)
    (hrow : a.height_pair.erase.height? = some (H + 1))
    (hfrontier : honestHMaxBeforeIndex S rho i < H + 2) :
    ∃ (Cfg : NamedBlock V) (T : Block V),
      PrefixFGSelectorConeAt S rho
        (inclusiveEventIndex rho (S.a r0)) stop H i a ta Cfg T ∧
      S.E.t_GST ≤ S.a (a.round - 1) ∧
      ∀ w ∈ rho.honest, ∃ Q : Block V,
        namedG1At S rho w a.round Q := by
  have hemit : NamedRun.emits S rho a.val_index (Object.attest a) ta :=
    ⟨i, hiEvent, hiOutput⟩
  obtain ⟨B, J, hta, haAction, hsource, hBmem, hBstoredHeight,
      hBderivedHeight, hJderived, hshape⟩ :=
    honestEmittedHeightRow_exactFGSelectorWitness
      S adm haHon hemit hrow
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
    gradeRoundReady_of_action_horizon
      S hgst hroundFromStart hactionHorizon
  obtain ⟨A, hselected⟩ :=
    namedClosed_nodeQ2_exists_of_actionFGSource
      S rho a.val_index a.round hsource
  have hr : 0 < a.round := by
    apply Nat.pos_of_ne_zero
    intro hzero
    have hnone : nodeQ2 S
        (actionReadAt S rho a.val_index 0) 0 = none := by
      simpa only [nodeQ2, nodeRead] using
        WeakGenesis.actionGrade2Block_zero
          S adm.toNamedAdmissibleCore a.val_index
    rw [hzero, hnone] at hselected
    cases hselected
  have hiFrame : i ≤ stop - 1 := Nat.le_sub_one_of_lt hiStop
  have hframeAtSelector : NamedHeightRegimeFrame S rho H i Prev a.round := {
    floor := fun v hv n hn X hXrun hXheight hPrevX =>
      hframe.floor v hv n (hn.trans hiFrame) X hXrun hXheight hPrevX
    prevRun := hframe.prevRun
    prevHeight := hframe.prevHeight
    rootBelow := fun v hv n hn Q hQmem hQheight hPrevQ =>
      hframe.rootBelow v hv n (hn.trans hiFrame) Q hQmem hQheight hPrevQ
    sourceAbove := fun p hp r hprefix hhor Q hQmem hsource hQheight =>
      hframe.sourceAbove p hp r (hprefix.trans hiFrame) hhor Q hQmem
        hsource hQheight }
  have hpostPrev : S.E.t_GST ≤ S.a (a.round - 1) := by
    have hcut : gstLagged S ≤
        S.hc.Γ_neg1 S.E.Δ ((a.round - 1) + 1) := by
      rw [Nat.sub_add_cancel hr]
      exact hgst.trans
        (Γ_neg1_mono S.hc S.E.Δ_pos hroundFromStart)
    rw [Γ_neg1_add_rounds] at hcut
    simp only [gstLagged, readyLag, Nat.mul_one] at hcut
    have hprevCut : S.E.t_GST ≤
        S.hc.Γ_neg1 S.E.Δ (a.round - 1) := by
      linarith
    exact hprevCut.trans
      (((Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos
          (a.round - 1)).le.trans
        ((Proofs.HealingLemmas.Γ_0_lt_Γ_1 S.hc S.E.Δ_pos
          (a.round - 1)).le.trans
          (Proofs.HealingLemmas.Γ_1_lt_Γ_2 S.hc S.E.Δ_pos
            (a.round - 1)).le)).trans
        (Γ_2_le_a S.hc S.E.Δ_pos (a.round - 1)))
  have hguard := crossReaderBodyReadyGuard_of_namedHeightRegimeFrame
    S adm hbelow hgst hframe hiStart hiStop haHon hiEvent hiOutput
      hrow hfrontier
  have hpreparedG1 := actionFGSource_rawG1_at_firstInterior
    S adm hbelow ready hactionHorizon haHon hsource hguard
  have hG1 : ∀ w ∈ rho.honest, ∃ Q : Block V,
      namedG1At S rho w a.round Q := by
    intro w hw
    obtain ⟨Q, -, hQ⟩ := hpreparedG1 w hw
    exact ⟨Q, hQ⟩
  have hcone :
      NamedHonestVotesCone S rho (S.hc.opening_slot a.round)
          (fun X => Block.Preceq B.erase X) ∨
        NamedHonestVotesCone S rho (S.hc.opening_slot a.round + 1)
          (fun X => Block.Preceq B.erase X) := by
    by_cases hlocal : nodeQ2 S
        (actionReadAt S rho a.val_index a.round) a.round = some B.erase
    · have hK6 := voterAnchorSourceQ2Inputs_of_namedHeightRegimeFrame
        S adm ready hframeAtSelector hstrictAction
          (by simpa only [Nat.add_assoc] using hfrontier)
          hactionHorizon B haHon hBmem hBderivedHeight hsource hlocal
      exact Or.inl
        (selectedQ2_openingVotesCone S adm hbelow hr ready haHon hlocal hK6)
    · rcases actionFGSource_genuineClear_or_selectedG2_named
          S rho a.val_index a.round hselected hsource with hclear | hsourceQ2
      · obtain ⟨C, hgenuine, -, -, -, hBC⟩ := hclear
        have hmain := voterAnchorSourceClearInputsMain_of_namedFrame_source
          S adm hbelow hr ready hpostPrev hframeAtSelector hstrictAction
            (by simpa only [Nat.add_assoc] using hfrontier)
            hactionHorizon A B haHon hselected hsource hBmem
              hBderivedHeight hlocal
        rcases genuineClear_nextVoteCone_or_heightProgressThrough_of_mainInputs
            S adm ready haHon hgenuine hBC hBmem hBderivedHeight
              hactionHorizon hmain
                (through := Protocol.vote_time S.E
                  (S.hc.opening_slot a.round + 1))
                (le_refl _) with hprogress | hprotected
        · obtain ⟨w, hw, u, hu, hmax⟩ := hprogress
          have huAction : u < S.a a.round :=
            hu.trans_lt (next_vote_time_lt_action S a.round)
          have hcursor : inclusiveEventIndex rho u ≤
              strictEventIndex rho (S.a a.round) := by
            rw [strictEventIndex_eq_inclusiveEventIndex_pred]
            exact inclusiveEventIndex_mono rho
              (Int.le_sub_one_iff.mpr huAction)
          have hlocalMax : (rho.storeAt S w u).h_max ≤
              honestHMaxBeforeIndex S rho i := by
            rw [storeAt_eq_stateBefore_inclusiveEventIndex
              S adm.toNamedScheduleWellFormed w u]
            exact (localHMax_le_honestHMaxBeforeIndex S rho
              (inclusiveEventIndex rho u) hw).trans
                (honestHMaxBeforeIndex_mono S rho
                  (hcursor.trans hstrictAction))
          have hbad : H + 3 ≤ honestHMaxBeforeIndex S rho i := by
            calc
              H + 3 = (H + 1) + 2 := by simp only [Nat.add_assoc]
              _ ≤ (rho.storeAt S w u).h_max := hmax
              _ ≤ honestHMaxBeforeIndex S rho i := hlocalMax
          exact False.elim (Nat.not_lt_of_ge
            ((Nat.lt_succ_self (H + 2)).le.trans hbad) hfrontier)
        · exact Or.inr hprotected.2
      · exact False.elim (hlocal (hsourceQ2 ▸ hselected))
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
  refine ⟨B, J, ?_, hpostPrev, hG1⟩
  exact {
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
    sourceDerivedHeight := hBderivedHeight
    checkpointStored := hcheckpoint
    checkpointDerived := hJderived
    targetOrTimeout := hshape
    cone := hcone }

#print axioms honestHeightRow_prefixFGSelectorCone_of_namedHeightRegimeFrame

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
