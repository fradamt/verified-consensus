module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.HeightRegimeNamedRunScoped
public import DecoupledConsensusProofs.Objects.AdmissibleCore

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Closed history for run-scoped named height regimes
This module restates the named recovery history only where the previous-root
contract is consumed. The protocol argument is unchanged. The previous root is
now known to be a run block at the one call site that needs named ancestry.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem runHistory_relative_gradeBool_zero
    (E : Env V) (gv : Protocol.GradeView V) (F : Block V)
    (eta : Round) (early late : Time) (B : Block V) :
    DecoupledConsensusModel.Protocol.gradeBool E gv F eta 0 early late B = false := by
  simp [DecoupledConsensusModel.Protocol.gradeBool,
    DecoupledConsensusModel.Protocol.positive, DecoupledConsensusModel.Protocol.opposing,
    DecoupledConsensusModel.Protocol.readyView, DecoupledConsensusModel.Protocol.rawView,
    DecoupledConsensusModel.Protocol.interpretedInputs, DecoupledConsensusModel.Protocol.rawInputs,
    Protocol.latest_window_zero, DecoupledConsensusModel.Protocol.Supports,
    DecoupledConsensusModel.Protocol.Opposes, DecoupledConsensusModel.Protocol.CleanFrom]

private theorem runHistory_selectedQ2_round_pos
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} {r : Round} {Q : Block V}
    (hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r = some Q) :
    0 < r := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have hgrade := selectedQ2_storeGrade_at_g2Domain S adm hQ
  rw [hzero] at hgrade
  simp only [PhaseGrades.storeGrade, PhaseGrades.phaseGrade] at hgrade
  rw [runHistory_relative_gradeBool_zero] at hgrade
  cases hgrade

private theorem runHistory_sourceLastSlot_bounds
    (x b : Nat) (hb : 2 ≤ b) :
    x + 1 ≤ x + b - 1 ∧ x + b - 1 < x + b ∧
      0 < x + b - 1 ∧ x + b - 1 + 1 = x + b := by
  omega

private theorem runHistory_laterLastSlot_bounds (x b : Nat) (hb : 2 ≤ b) :
    x + 1 ≤ x + b - 1 ∧ x + b - 1 < x + b ∧
      0 < x + b - 1 ∧ x + b - 1 + 1 = x + b := by
  omega

private theorem runHistory_round_of_between_openings
    (hc : Protocol.HealConfig) {r s : Nat}
    (hlo : hc.opening_slot r ≤ s)
    (hhi : s < hc.opening_slot (r + 1)) :
    hc.round_of s = r := by
  rcases eq_or_lt_of_le hlo with h | h
  · rw [← h]
    exact round_of_opening_slot_eq_schedule hc r
  · exact round_of_eq_of_opening_succ_le_of_lt_next_opening hc h hhi

private theorem runHistory_openingVote_add_delta_le_action
    (S : Setup V) (r : Round) :
    Protocol.vote_time S.E (S.hc.opening_slot r) + S.E.Δ ≤ S.a r := by
  rw [← opening_confirmation_time_eq_action,
    ← vote_time_succ_add_delta_eq_confirmation_time]
  exact add_le_add (vote_time_mono_slots S.E (Nat.le_succ _))
    (le_refl S.E.Δ)

private theorem runHistory_action_le_interiorVote_add_delta
    (S : Setup V) {r : Round} {s : Slot}
    (hs : S.hc.opening_slot r + 1 ≤ s) :
    S.a r ≤ Protocol.vote_time S.E s + S.E.Δ := by
  rw [← opening_confirmation_time_eq_action,
    ← vote_time_succ_add_delta_eq_confirmation_time]
  exact add_le_add (vote_time_mono_slots S.E hs) (le_refl S.E.Δ)

omit [Fintype V] in
private theorem runHistory_compatible_checkpoint_below
    {L T C : Block V}
    (hLC : Block.compatible L C = true) (hTC : Block.Preceq T C) :
    Block.compatible L T = true := by
  rcases (show Block.Preceq L C ∨ Block.Preceq C L by
    simpa only [Block.compatible, Bool.or_eq_true] using hLC) with hLC | hCL
  · exact Block.compatible_of_preceq_common hLC hTC
  · simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr (Block.preceq_trans hTC hCL)

private theorem PrefixFGSelectorConeAt.readFrontier_le_before_nextAction_run
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hmajority : HonestWeightMajority S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    {read : Time} (hread : read ≤ S.a (a.round + 1)) (w : V) :
    (rho.storeBeforeTime S w read).core.h_max ≤ blocked + 2 := by
  have hbound : (rho.storeBeforeTime S w read).core.h_max ≤
      honestHMaxBeforeIndex S rho
        (strictEventIndex rho (S.a (a.round + 1 - 1))) + 1 := by
    by_cases hlarge : 1 < (rho.storeBeforeTime S w read).core.h_max
    · obtain ⟨b, tb, D, K, hb, hemit, ht, hrow, _, _, _, _, _, _⟩ :=
        frontier_confirmationWitness S adm hmajority hlarge
      have hround : b.round < a.round + 1 := by
        by_contra hn
        have htime : S.a b.round < S.a (a.round + 1) := by
          simpa only [(Proofs.Optimistic.emits_attest_shape S hemit).2] using
            ht.trans_le hread
        exact (not_lt_of_ge (Assembly.a_mono S (Nat.le_of_not_gt hn)))
          htime
      have htime : tb ≤ S.a (a.round + 1 - 1) := by
        rw [(Proofs.Optimistic.emits_attest_shape S hemit).2]
        exact Assembly.a_mono S (Nat.le_sub_one_of_lt hround)
      have hband := honestEmittedHeight_le_honestHMaxBeforeTime
        S adm hb hemit hrow htime
      calc
        _ = ((rho.storeBeforeTime S w read).core.h_max - 1) + 1 :=
          (Nat.sub_add_cancel (Nat.le_of_lt hlarge)).symm
        _ ≤ _ := Nat.add_le_add_right hband 1
    · exact (Nat.le_of_not_gt hlarge).trans
        (Nat.succ_le_succ (Nat.zero_le _))
  simp only [Nat.add_sub_cancel] at hbound
  exact hbound.trans (Nat.add_le_add_right
    (hfirst.before _
      (hseed.actionPrefix_lt adm.toNamedScheduleWellFormed)) 1)

omit [Fintype V] in
private theorem runHistory_namedAncestorBodyMem
    {st : Protocol.NamedStore V}
    (hpc : NamedStore.NamedParentClosed st) {A B : NamedBlock V}
    (hB : B ∈ st.bodies) (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq,
        decide_eq_true_eq] at hAB
      exact hAB ▸ hB
  | node parent slot root votes support rows proposer ih =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hparent
      · exact hB
      · exact ih (hpc.2 _ hB) hparent

/-- earlier's old-target-root bound with the named root restricted to a run
block. -/
theorem PrefixFGSelectorConeAt.oldTargetRoot_preceq_of_strictActionCut_of_frame_run
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta
      Cfg T.erase)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    (hframe : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (hc0 : c0 ≤ a.round)
    (ready : GradeRoundReady S rho a.round)
    (hpostPrev : S.E.t_GST ≤ S.a (a.round - 1))
    (hG1 : ∀ w ∈ rho.honest, ∃ Q : Block V,
      namedG1At S rho w a.round Q)
    (hpred : NamedOldTargetRootBelowRun S rho first blocked T)
    (hminimal : ∀ (b : NamedAttestation V) (tb : Time),
      b.val_index ∈ rho.honest →
      NamedRun.emits S rho b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) →
      a.round ≤ b.round)
    {cut : Round}
    (hcut : strictEventIndex rho (S.a (cut - 1)) < first)
    {w : V} (hw : w ∈ rho.honest) {time : Time}
    (hfrontier : blocked < (rho.storeBeforeTime S w time).h_max)
    {C : NamedBlock V} (hC : C ∈ (rho.storeBeforeTime S w time).bodies)
    {b : NamedAttestation V} {tb : Time}
    (hb : b.val_index ∈ rho.honest)
    (hemit : NamedRun.emits S rho b.val_index (Object.attest b) tb)
    (hold : b.round < cut)
    (hpair : b.height_pair.erase = HeightPair.target
      (Protocol.derive_named S.E S.cfg C).h_j
      (Protocol.derive_named S.E S.cfg C).J.root)
    (hJ : (Protocol.derive_named S.E S.cfg C).J =
      Protocol.get_fg_root
        (rho.storeBeforeTime S w time).toHealing.toFG)
    (hR : fgConfirmationWitness S
      (actionStoreAt S rho b.val_index b.round) =
        some (Protocol.get_fg_root
          (rho.storeBeforeTime S w time).toHealing.toFG)) :
    Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w time).toHealing.toFG) T.erase := by
  let R := Protocol.get_fg_root
    (rho.storeBeforeTime S w time).toHealing.toFG
  have htime : tb = S.a b.round :=
    (Proofs.Optimistic.emits_attest_shape S hemit).2
  have hactionLe : S.a b.round ≤ S.a (cut - 1) :=
    Assembly.a_mono S (Nat.le_sub_one_of_lt hold)
  have hheightCap : honestHMaxBeforeIndex S rho
      (strictEventIndex rho (S.a (cut - 1))) ≤ blocked + 1 :=
    hfirst.before _ hcut
  have hrow : b.height_pair.erase.height? = some
      (Protocol.derive_named S.E S.cfg C).h_j := by
    simp only [hpair, HeightPair.height?]
  have hupper : (Protocol.derive_named S.E S.cfg C).h_j ≤
      blocked + 1 :=
    (honestEmittedHeight_le_honestHMaxBeforeTime S adm hb hemit hrow
      (htime ▸ hactionLe)).trans hheightCap
  have hbefore : strictEventIndex rho (S.a b.round) < first :=
    (strictEventIndex_mono rho hactionLe).trans_lt hcut
  rcases NamedCheckpointHeights.justified_ancestor_height
      S.E S.cfg C with hz | ⟨K, hKC, hKerase, hKheight⟩
  · have hgen : (Protocol.derive_named S.E S.cfg C).J =
        Block.genesis :=
      NamedJustificationCertificates.justified_zero_is_genesis
        S.E S.cfg C hz
    rw [← hJ, hgen]
    exact Protocol.preceq_genesis T.erase
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg
      (rho.storeBeforeTime S w time) :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho time w).1.1.1
  have hK : K ∈ (rho.storeBeforeTime S w time).bodies :=
    runHistory_namedAncestorBodyMem hcoh.2.2.1 hC hKC
  obtain ⟨n, hn, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedScheduleWellFormed.sorted time
  have hKprefix : K ∈ (rho.stateBefore S n w).st.bodies := by
    change K ∈ (NamedRun.stateBefore S rho n w).st.bodies
    rw [← hn]
    exact hK
  have hKrun : RunBlock S rho K :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hw hKprefix
  have hKR : K.erase = R := hKerase.trans hJ
  have hR' : fgConfirmationWitness S
      (actionStoreAt S rho b.val_index b.round) = some K.erase := by
    simpa only [R, hKR] using hR
  by_cases heq : (Protocol.derive_named S.E S.cfg C).h_j =
      blocked + 1
  · have hrowH : b.height_pair.erase.height? = some (blocked + 1) :=
      heq ▸ hrow
    have hT := hseed.confirmationWitness_of_source_of_frame_named
      adm hcom hbelow hfirst hframe hc0 ready hpostPrev hG1 hb hemit
        hrowH (hminimal b tb hb hemit hrowH) hbefore
    have hRT : R = T.erase := Option.some.inj (hR.symm.trans hT)
    exact hRT ▸ Block.preceq_self R
  · have hlow : (Protocol.derive_named S.E S.cfg C).h_j ≤
        blocked := Nat.le_of_lt_succ (lt_of_le_of_ne hupper heq)
    have hKlow : (Protocol.derive_named S.E S.cfg K).h ≤ blocked := by
      rw [hKheight]
      exact hlow
    rcases eq_or_lt_of_le hKlow with heqB | hlt
    · have hpairB : b.height_pair.erase =
          HeightPair.target blocked K.erase.root := by
        rw [hpair, ← hKheight, heqB, hKerase]
      calc
        Protocol.get_fg_root
            (rho.storeBeforeTime S w time).toHealing.toFG = K.erase := by
          simpa only [R] using hKR.symm
        _ ⪯ T.erase := Proofs.NamedWire.erase_preceq
          (hpred b tb hb hemit hbefore K hKrun heqB hpairB hR'
            w hw time hfrontier (by simpa only [R] using hKR.symm))
    · have hlowPred : (Protocol.derive_named S.E S.cfg K).h ≤
          blocked - 1 := Nat.le_sub_one_of_lt hlt
      have hblockedPos : 0 < blocked := Nat.zero_lt_of_lt hlt
      have hfrontierPred : blocked - 1 + 1 <
          (rho.storeBeforeTime S w time).h_max := by
        rwa [Nat.sub_add_cancel (Nat.succ_le_iff.mpr hblockedPos)]
      obtain ⟨P, _, hPentry, hPheight0, _, hPrun⟩ :=
        action_named_checkpoint S adm hseed.signerHonest hseed.sourceMem
      have hPT : P.erase = T.erase :=
        hPentry.trans hseed.checkpointDerived.symm
      have hPheight : (Protocol.derive_named S.E S.cfg P).h =
          blocked + 1 := hPheight0.trans hseed.sourceDerivedHeight
      have hlegacy : FinalizedRootsBelowAtRead S rho
          (blocked - 1) P.erase :=
        Handover.finalizedRootsBelowAtRead_of_accountable S adm.toNamedAdmissibleCore
          (slashableBound_of_admissible_belowOneThird S adm hbelow)
          hPrun (by
            rw [hPheight]
            exact (Nat.sub_le blocked 1).trans_lt
              (Nat.lt_succ_self blocked))
      have hout :=
        Handover.lowFGRoot_preceq_of_frontier_gap_of_finalizedRootsBelow
          S hw hlegacy hfrontierPred hK hKR hlowPred
      simpa only [hPT] using hout

#print axioms
  PrefixFGSelectorConeAt.oldTargetRoot_preceq_of_strictActionCut_of_frame_run

private theorem PrefixFGSelectorConeAt.fgRoot_preceq_before_nextAction_of_frame_run
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta
      Cfg T.erase)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    (hframe : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (hc0 : c0 ≤ a.round)
    (ready : GradeRoundReady S rho a.round)
    (hpostPrev : S.E.t_GST ≤ S.a (a.round - 1))
    (hG1 : ∀ w ∈ rho.honest, ∃ Q : Block V,
      namedG1At S rho w a.round Q)
    (hpred : NamedOldTargetRootBelowRun S rho first blocked T)
    (hminimal : ∀ (b : NamedAttestation V) (tb : Time),
      b.val_index ∈ rho.honest →
      NamedRun.emits S rho b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) →
      a.round ≤ b.round)
    {read : Time} (hlo : S.a a.round ≤ read)
    (hhi : read ≤ S.a (a.round + 1))
    {w : V} (hw : w ∈ rho.honest) :
    Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w read).toHealing.toFG) T.erase := by
  rcases fgRoot_confirmationWitness_at_read S adm.toNamedAdmissibleCore
      (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow)
      hw read with hgen | ⟨C, hC, hJ, b, tb, hb, hemit, htb, hpair, hR⟩
  · rw [hgen]
    exact Protocol.preceq_genesis T.erase
  · have hold : b.round < a.round + 1 := by
      by_contra hn
      have ht : tb = S.a b.round :=
        (Proofs.Optimistic.emits_attest_shape S hemit).2
      have hle := Assembly.a_mono S (Nat.le_of_not_gt hn)
      exact (not_lt_of_ge hle) (ht ▸ htb.trans_le hhi)
    have hcut : strictEventIndex rho (S.a (a.round + 1 - 1)) < first := by
      simpa only [Nat.add_sub_cancel] using
        hseed.actionPrefix_lt adm.toNamedScheduleWellFormed
    exact hseed.oldTargetRoot_preceq_of_strictActionCut_of_frame_run
      adm hcom hbelow hfirst hframe hc0 ready hpostPrev hG1 hpred
        hminimal hcut hw
          (Nat.lt_of_succ_le
            (hseed.localFrontier_ge_from_source_of_frame_named
              adm hframe ready hlo hw))
          hC hb hemit hold hpair hJ hR

/-- The recent-witness FG-root bootstrap with the run-scoped old-root
contract. -/
theorem PrefixFGSelectorConeAt.fgRoot_compatible_of_recentWitnessHistory_of_frame_run
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta
      Cfg T.erase)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    (hframe : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (hc0 : c0 ≤ a.round)
    (ready : GradeRoundReady S rho a.round)
    (hpostPrev : S.E.t_GST ≤ S.a (a.round - 1))
    (hG1 : ∀ w ∈ rho.honest, ∃ Q : Block V,
      namedG1At S rho w a.round Q)
    (hpred : NamedOldTargetRootBelowRun S rho first blocked T)
    (hminimal : ∀ (b : NamedAttestation V) (tb : Time),
      b.val_index ∈ rho.honest →
      NamedRun.emits S rho b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) →
      a.round ≤ b.round)
    {read : Time} (hread : S.a a.round ≤ read)
    (hhistory : ∀ r, a.round + 1 ≤ r → S.a r < read →
      ∀ w ∈ rho.honest, ∀ W,
        fgConfirmationWitness S (actionStoreAt S rho w r) = some W →
          Block.compatible W T.erase = true)
    {w : V} (hw : w ∈ rho.honest) :
    Block.compatible
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w read).toHealing.toFG) T.erase = true := by
  apply fgRoot_compatible_of_bootstrap_and_recentActions_at_read S adm.toNamedAdmissibleCore
    (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow) hw
    (cut := a.round + 1)
  · intro r hr ht v hv W hW
    simpa only [Block.compatible, Bool.or_comm] using
      hhistory r hr ht v hv W hW
  · intro C b tb
    dsimp only
    intro hC hJ hb hemit _ hold hpair hR
    have hcut : strictEventIndex rho (S.a (a.round + 1 - 1)) < first := by
      simpa only [Nat.add_sub_cancel] using
        hseed.actionPrefix_lt adm.toNamedScheduleWellFormed
    have hactionPrefix : strictEventIndex rho (S.a a.round) ≤ first - 1 :=
      Nat.le_sub_one_of_lt
        (hseed.actionPrefix_lt adm.toNamedScheduleWellFormed)
    have hactionHor : S.a a.round ≤ rho.horizon := hseed.actionHorizon adm
    have hTprevCfg : NamedBlock.Preceq Tprev Cfg :=
      hframe.sourceAbove a.val_index hseed.signerHonest a.round
        hactionPrefix hactionHor Cfg hseed.sourceMem hseed.exactFGSource
          hseed.sourceDerivedHeight
    have hfloor : FinalityFloorAt S rho blocked (first - 1) Tprev.erase := by
      intro v hv n hn X hXrun hXheight hTX
      have hTXnamed := Protocol.namedPreceq_of_runBlock_erase_preceq
        adm hframe.prevRun hXrun hTX
      exact hframe.floor v hv n hn X hXrun hXheight hTXnamed
    obtain ⟨Q, hQ⟩ : ∃ Q : Block V, PhaseGrades.nodeQ2
        S (actionReadAt S rho a.val_index a.round) a.round = some Q := by
      cases hQ : PhaseGrades.nodeQ2
          S (actionReadAt S rho a.val_index a.round) a.round with
      | none =>
          have hsource := hseed.exactFGSource
          unfold actionFGSource at hsource
          dsimp only at hsource
          have hround : S.hc.round_of
              (actionStoreAt S rho a.val_index a.round).st.core.toHealing.s =
                a.round := by
            simpa only [Protocol.Store.toHealing] using
              actionStoreAt_round S rho a.val_index a.round
          rw [hround] at hsource
          change Protocol.grade2_block_with
            (NamedProfile.gradeContract
              (actionReadAt S rho a.val_index a.round).cache)
            S.E S.hc
            (actionReadAt S rho a.val_index a.round).st.core.toHealing
            a.round = none at hQ
          simp only [actionStoreAt] at hsource
          rw [Protocol.fg_source_with.eq_def, hQ] at hsource
          cases hsource
      | some Q => exact ⟨Q, rfl⟩
    have hsourceAt : Cfg ∈
        (actionStoreAt S rho w a.round).st.bodies := by
      rcases actionFGSource_genuineClear_or_selectedG2_named
          S rho a.val_index a.round hQ hseed.exactFGSource with
        hgenuine | hselected
      · obtain ⟨B, hgenuine, -, -, -, hCfgB⟩ := hgenuine
        have hvoteBody := ancestorGenuineConfirmation_body_at_nextVote_of_floor
          S adm ready hseed.signerHonest hgenuine hCfgB hseed.sourceMem
            hfloor hseed.sourceDerivedHeight
            (Proofs.NamedWire.erase_preceq hTprevCfg)
            hactionPrefix hactionHor hw
        let vote := Protocol.vote_time S.E
          (S.hc.opening_slot a.round + 1)
        have hvotePre : Cfg ∈
            (NamedRun.stateBeforeTime S rho vote w).st.bodies := by
          simpa only [Internal.NamedRecoveryRead.voteDutyRead,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom,
            NamedActionReads.preparedCache, Protocol.NamedStore.setClock,
            vote] using hvoteBody
        have heqVote := congrFun
          (stateBeforeTime_eq_stateBefore_strictEventIndex
            S adm.toNamedScheduleWellFormed vote) w
        have heqAction := congrFun
          (stateBeforeTime_eq_stateBefore_strictEventIndex
            S adm.toNamedScheduleWellFormed (S.a a.round)) w
        rw [heqVote] at hvotePre
        have hactionPre : Cfg ∈
            (NamedRun.stateBeforeTime S rho (S.a a.round) w).st.bodies := by
          rw [heqAction]
          exact NamedBodyRetention.stateBefore_bodies_mono S rho w
            (strictEventIndex_mono rho
              (Protocol.next_vote_time_lt_action S a.round).le)
            hvotePre
        simpa only [actionStoreAt, actionReadAt,
          NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
          NamedActionReads.confirmationReadFrom,
          NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using
            hactionPre
      · have hselectedCfg : PhaseGrades.nodeQ2
            S (actionReadAt S rho a.val_index a.round) a.round =
              some Cfg.erase := by
          simpa only [hselected] using hQ
        exact (selectedQ2_body_at_action_and_openingVote_of_floor
          S adm ready hseed.signerHonest hselectedCfg hseed.sourceMem
            hfloor hseed.sourceDerivedHeight
            (Proofs.NamedWire.erase_preceq hTprevCfg)
            hactionPrefix hw).1
    have hsourcePre : Cfg ∈
        (NamedRun.stateBeforeTime S rho (S.a a.round) w).st.bodies := by
      simpa only [actionStoreAt, actionReadAt,
        NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
        NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using
          hsourceAt
    have heqSource := congrFun
      (stateBeforeTime_eq_stateBefore_strictEventIndex
        S adm.toNamedScheduleWellFormed (S.a a.round)) w
    have heqRead := congrFun
      (stateBeforeTime_eq_stateBefore_strictEventIndex
        S adm.toNamedScheduleWellFormed read) w
    rw [heqSource] at hsourcePre
    have hCfgRead : Cfg ∈
        (NamedRun.stateBeforeTime S rho read w).st.bodies := by
      rw [heqRead]
      exact NamedBodyRetention.stateBefore_bodies_mono S rho w
        (strictEventIndex_mono rho hread) hsourcePre
    have hheight := Proofs.NamedStoreBridge.heights_le_hMax_stateBeforeTime
      S rho read w Cfg hCfgRead
    have hfrontier : blocked <
        (rho.storeBeforeTime S w read).h_max := by
      rw [hseed.sourceDerivedHeight] at hheight
      exact Nat.lt_of_succ_le hheight
    have hroot :=
      hseed.oldTargetRoot_preceq_of_strictActionCut_of_frame_run
        adm hcom hbelow hfirst hframe hc0 ready hpostPrev hG1 hpred
          hminimal hcut hw hfrontier hC hb hemit hold hpair hJ hR
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr hroot

#print axioms
  PrefixFGSelectorConeAt.fgRoot_compatible_of_recentWitnessHistory_of_frame_run

/-- earlier's named action-history vote step with the run-scoped old-root
contract. -/
theorem PrefixFGSelectorConeAt.checkpointVoteStep_of_actionHistories_of_frame_run
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta
      Cfg T.erase)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    (hframe : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (hc0 : c0 ≤ a.round)
    (ready : GradeRoundReady S rho a.round)
    (hpostPrev : S.E.t_GST ≤ S.a (a.round - 1))
    (hG1 : ∀ w ∈ rho.honest, ∃ Q : Block V,
      namedG1At S rho w a.round Q)
    (hpred : NamedOldTargetRootBelowRun S rho first blocked T)
    (hminimal : ∀ (b : NamedAttestation V) (tb : Time),
      b.val_index ∈ rho.honest →
      NamedRun.emits S rho b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) →
      a.round ≤ b.round)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hsourceRead : S.a a.round ≤ Protocol.vote_time S.E (s + 1))
    (hc : 1 ≤ S.hc.round_of (s + 1))
    (hsg : HonestSGEmissionsCompatibleAtRound S rho
      (S.hc.round_of (s + 1) - 1) T.erase)
    (hsgPost : S.E.t_GST ≤ S.a (S.hc.round_of (s + 1) - 1))
    (hhistory : ∀ r, a.round + 1 ≤ r →
      S.a r < Protocol.vote_time S.E (s + 1) →
      ∀ w ∈ rho.honest, ∀ W,
        fgConfirmationWitness S (actionStoreAt S rho w r) = some W →
          Block.compatible W T.erase = true)
    (hgf : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq T.erase X)) :
    (∀ w ∈ rho.honest,
      Block.Preceq T.erase (voterHeadAt S rho w (s + 1))) ∧
      NamedHonestVotesCone S rho (s + 1)
        (fun X => Block.Preceq T.erase X) := by
  have hmajority :=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow
  have hroots : ∀ w ∈ rho.honest, Block.compatible
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w
          (s + 1)).st.core.toHealing.toFG) T.erase = true := by
    intro w hw
    simpa only [Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
      Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using
      (hseed.fgRoot_compatible_of_recentWitnessHistory_of_frame_run
        adm hcom hbelow hfirst hframe hc0 ready hpostPrev hG1
          hpred hminimal hsourceRead hhistory hw)
  obtain ⟨K, _, hKT0, hKheight0, _, hKrun⟩ :=
    action_named_checkpoint S adm hseed.signerHonest hseed.sourceMem
  have hKT : K.erase = T.erase :=
    hKT0.trans hseed.checkpointDerived.symm
  have hKheight : (Protocol.derive_named S.E S.cfg K).h =
      blocked + 1 := hKheight0.trans hseed.sourceDerivedHeight
  have hwitnesses : ∀ w ∈ rho.honest, ∀ {C : NamedBlock V},
      C.erase = T.erase →
      (Protocol.derive_named S.E S.cfg C).h <
        (Internal.NamedRecoveryRead.voteDutyRead S rho w
          (s + 1)).st.core.h_max - 1 →
      RunBlock S rho C →
      ∀ (b : NamedAttestation V) (tb : Time) (J : NamedBlock V),
        b.val_index ∈ rho.honest →
        NamedRun.emits S rho b.val_index (Object.attest b) tb →
        tb < Protocol.vote_time S.E (s + 1) →
        b.height_pair.erase.height? =
          some ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).h_max - 1) →
        fgConfirmationWitness S
          (actionStoreAt S rho b.val_index b.round) =
            some (Protocol.derive_named S.E S.cfg J).T_h →
        RunBlock S rho J →
        Block.compatible C.erase
          (Protocol.derive_named S.E S.cfg J).T_h = true := by
    intro w hw C hCerase hhigh hCrun b tb J hb hemit htb hrow
      hselected _
    have hCK : C = K := by
      apply adm.toNamedRootCollisionFree.root_injective
        C K hCrun hKrun C K
          (Or.inl (Proofs.NamedAncestry.named_self C))
          (Or.inr (Proofs.NamedAncestry.named_self K))
      rw [← Proofs.NamedWire.erase_root C, hCerase, ← hKT,
        Proofs.NamedWire.erase_root]
    subst C
    by_cases hold : b.round < a.round + 1
    · have htime : tb ≤ S.a a.round := by
        rw [(Proofs.Optimistic.emits_attest_shape S hemit).2]
        exact Assembly.a_mono S (Nat.le_of_lt_succ hold)
      have hbound := honestEmittedHeight_le_honestHMaxBeforeTime
        S adm hb hemit hrow htime
      have hfloor : honestHMaxBeforeIndex S rho
          (strictEventIndex rho (S.a a.round)) ≤
            (Protocol.derive_named S.E S.cfg K).h := by
        rw [hKheight]
        exact hfirst.before _
          (hseed.actionPrefix_lt adm.toNamedScheduleWellFormed)
      have hrowLe :
          (Internal.NamedRecoveryRead.voteDutyRead S rho w
            (s + 1)).st.core.h_max - 1 ≤
            (Protocol.derive_named S.E S.cfg K).h := by
        have hbnd := hbound.trans hfloor
        simpa only [Internal.NamedRecoveryRead.voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
          Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hbnd
      exact False.elim ((Nat.not_lt_of_ge hrowLe) hhigh)
    · have hcompat := hhistory b.round (Nat.le_of_not_gt hold)
          (by simpa only [(Proofs.Optimistic.emits_attest_shape S hemit).2] using htb)
          b.val_index hb
            (Protocol.derive_named S.E S.cfg J).T_h hselected
      simpa only [hKT, Block.compatible, Bool.or_comm] using hcompat
  have hanchors : ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w (s + 1)) T.erase = true := by
    intro w hw
    exact voterAnchorAt_compatible_of_previousSGHistory_named
      S adm hbelow hhor hc hsg hsgPost hw (hroots w hw)
  exact WeakGoldfish.goldfishCone_succ_of_runFrontierWitnesses
    S adm.toNamedAdmissibleCore hcom hmajority hs hpost hhor hgf
      hwitnesses hroots hanchors

#print axioms
  PrefixFGSelectorConeAt.checkpointVoteStep_of_actionHistories_of_frame_run

private theorem PrefixFGSelectorConeAt.checkpointVoteStep_beforeNextAction_of_frame_run
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta
      Cfg T.erase)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    (hframe : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (hc0 : c0 ≤ a.round)
    (ready : GradeRoundReady S rho a.round)
    (hpostPrev : S.E.t_GST ≤ S.a (a.round - 1))
    (hG1 : ∀ w ∈ rho.honest, ∃ Q : Block V,
      namedG1At S rho w a.round Q)
    (hpred : NamedOldTargetRootBelowRun S rho first blocked T)
    (hminimal : ∀ (b : NamedAttestation V) (tb : Time),
      b.val_index ∈ rho.honest →
      NamedRun.emits S rho b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) →
      a.round ≤ b.round)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hread : S.a a.round ≤ Protocol.vote_time S.E (s + 1))
    (hnext : Protocol.vote_time S.E (s + 1) ≤ S.a (a.round + 1))
    (hnextOpening : Protocol.vote_time S.E (s + 1) ≤
      DecoupledConsensusModel.Protocol.opening S.E S.hc (a.round + 1))
    (hsround : S.hc.round_of (s + 1) = a.round)
    (hactionSettled : S.a a.round + S.E.Δ ≤
      Protocol.vote_time S.E (s + 1))
    (hvotes : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq T.erase X)) :
    (∀ w ∈ rho.honest,
      Block.Preceq T.erase (voterHeadAt S rho w (s + 1))) ∧
      NamedHonestVotesCone S rho (s + 1)
        (fun X => Block.Preceq T.erase X) := by
  have hmajority :=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow
  obtain ⟨P, _, hPentry, hPheight0, _, hPrun⟩ :=
    action_named_checkpoint S adm hseed.signerHonest hseed.sourceMem
  have hPT : P.erase = T.erase :=
    hPentry.trans hseed.checkpointDerived.symm
  have hPheight : (Protocol.derive_named S.E S.cfg P).h =
      blocked + 1 := hPheight0.trans hseed.sourceDerivedHeight
  apply WeakGoldfish.goldfishCone_succ_of_runFrontierWitnesses
    S adm.toNamedAdmissibleCore hcom hmajority hs hpost hhor hvotes
  · intro w hw C hCerase hhigh hCrun b tb K hb hemit ht hrow hW hKrun
    have hCP : C = P := by
      apply adm.toNamedRootCollisionFree.root_injective
        C P hCrun hPrun C P
          (Or.inl (Proofs.NamedAncestry.named_self C))
          (Or.inr (Proofs.NamedAncestry.named_self P))
      rw [← Proofs.NamedWire.erase_root C, hCerase, ← hPT,
        Proofs.NamedWire.erase_root]
    subst C
    have hupper := hseed.readFrontier_le_before_nextAction_run
      adm hmajority hfirst hnext w
    have hband :
        (Internal.NamedRecoveryRead.voteDutyRead S rho w
          (s + 1)).st.core.h_max - 1 ≤ blocked + 1 := by
      apply Nat.sub_le_iff_le_add.mpr
      simpa only [Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
        Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hupper
    rw [hPheight] at hhigh
    exact False.elim ((Nat.not_lt_of_ge hband) hhigh)
  · intro w hw
    have hroot := hseed.fgRoot_preceq_before_nextAction_of_frame_run
      adm hcom hbelow hfirst hframe hc0 ready hpostPrev hG1 hpred
        hminimal hread hnext hw
    simpa only [Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
      Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore,
      Block.compatible, Bool.or_eq_true] using Or.inl hroot
  · intro w hw
    rcases voterAnchorAt_cases S rho w (s + 1) with
      hroot | ⟨root, L, hframeL, hactiveL, hanchorL⟩
    · rw [hroot]
      have hroot' := hseed.fgRoot_preceq_before_nextAction_of_frame_run
        adm hcom hbelow hfirst hframe hc0 ready hpostPrev hG1 hpred
          hminimal hread hnext hw
      simpa only [Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
        Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore,
        Block.compatible, Bool.or_eq_true] using Or.inl hroot'
    · rw [hanchorL]
      obtain ⟨Q, hQ⟩ : ∃ Q : Block V, PhaseGrades.nodeQ2
          S (actionReadAt S rho a.val_index a.round) a.round = some Q := by
        cases hq : PhaseGrades.nodeQ2
            S (actionReadAt S rho a.val_index a.round) a.round with
        | none =>
            have hsource := hseed.exactFGSource
            unfold actionFGSource at hsource
            dsimp only at hsource
            have hround : S.hc.round_of
                (actionStoreAt S rho a.val_index a.round).st.core.toHealing.s =
                  a.round := by
              simpa only [Protocol.Store.toHealing] using
                actionStoreAt_round S rho a.val_index a.round
            rw [hround] at hsource
            change Protocol.grade2_block_with
              (NamedProfile.gradeContract
                (actionReadAt S rho a.val_index a.round).cache)
              S.E S.hc
              (actionReadAt S rho a.val_index a.round).st.core.toHealing
              a.round = none at hq
            simp only [actionStoreAt] at hsource
            rw [Protocol.fg_source_with.eq_def, hq] at hsource
            cases hsource
        | some Q => exact ⟨Q, rfl⟩
      have hr : 0 < a.round := runHistory_selectedQ2_round_pos S adm hQ
      have hslo : S.hc.opening_slot a.round ≤ s + 1 := by
        rw [← hsround]
        exact Nat.div_mul_le_self (s + 1) S.hc.R
      have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
        apply le_trans (le_of_lt ?_) hhor
        rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
        exact Int.lt_add_of_pos_right _ S.E.Δ_pos
      have hroundDuty : S.hc.round_of
          (Internal.NamedRecoveryRead.voteDutyRead S rho w
            (s + 1)).st.core.s = a.round := by
        simpa only [Proofs.Optimistic.voteDutyRead_slot] using hsround
      rw [hroundDuty] at hframeL
      have hsourceCompat :=
        activeVoterAnchor_compatible_actionFGSource_at_interior_named
          S adm hbelow hr ready (hseed.actionHorizon adm)
            hseed.signerHonest hw hslo hsround hnextOpening hvoteHor
            ((add_le_add (FrameForward.domain_le_a S a.round .g0)
              (le_refl S.E.Δ)).trans hactionSettled)
            hactionSettled hQ hseed.exactFGSource hframeL hactiveL
      have hTCfg : Block.Preceq T.erase Cfg.erase := by
        rw [hseed.checkpointDerived]
        exact Proofs.Optimistic.derive_named_T_h_preceq S.E S.cfg Cfg
      exact runHistory_compatible_checkpoint_below hsourceCompat hTCfg

/-- Source-round checkpoint protection for a run-scoped old-root
contract. -/
theorem PrefixFGSelectorConeAt.checkpointProtection_sourceRound_of_frame_run
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta
      Cfg T.erase)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    (hframe : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (hc0 : c0 ≤ a.round)
    (ready : GradeRoundReady S rho a.round)
    (hpostPrev : S.E.t_GST ≤ S.a (a.round - 1))
    (hG1 : ∀ w ∈ rho.honest, ∃ Q : Block V,
      namedG1At S rho w a.round Q)
    (hpred : NamedOldTargetRootBelowRun S rho first blocked T)
    (hminimal : ∀ (b : NamedAttestation V) (tb : Time),
      b.val_index ∈ rho.honest →
      NamedRun.emits S rho b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) →
      a.round ≤ b.round)
    {d : Slot} (hdlo : S.hc.opening_slot a.round + 1 ≤ d)
    (hdhi : d < S.hc.opening_slot (a.round + 1))
    (hhor : Protocol.vote_time S.E d + S.E.Δ ≤ rho.horizon) :
    (∀ w ∈ rho.honest,
      Block.Preceq T.erase (voterHeadAt S rho w d)) ∧
      NamedHonestVotesCone S rho d
        (fun X => Block.Preceq T.erase X) := by
  have hbase := hseed.checkpointProtection_firstInterior_of_frame_named
    adm hbelow hfirst hframe hc0 ready hpostPrev hG1
  have hopenPost : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot a.round) :=
    ready.1.trans ((early_g2_lt_Γ_0 S a.round).le.trans
      (Proofs.HealingLemmas.Γ_0_lt_Γ_1 S.hc S.E.Δ_pos a.round).le)
  have hfold : ∀ n, S.hc.opening_slot a.round + 1 ≤ n → n ≤ d →
      (∀ w ∈ rho.honest,
        Block.Preceq T.erase (voterHeadAt S rho w n)) ∧
        NamedHonestVotesCone S rho n
          (fun X => Block.Preceq T.erase X) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => intro _; exact hbase
    | succ n hn ih =>
        intro hntop
        have hprevious := ih (Nat.le_of_succ_le hntop)
        have htime := vote_time_mono_slots S.E hntop
        have hnHor : Protocol.confirmation_time S.E n ≤ rho.horizon := by
          rw [← vote_time_succ_add_delta_eq_confirmation_time S.E n]
          exact (add_le_add htime (le_refl S.E.Δ)).trans hhor
        have hnext : Protocol.vote_time S.E (n + 1) ≤
            S.a (a.round + 1) := by
          have hle : n + 1 ≤ S.hc.opening_slot (a.round + 1) :=
            hntop.trans hdhi.le
          exact (vote_time_mono_slots S.E hle).trans
            (opening_vote_time_lt_action S (a.round + 1)).le
        have hnextOpening : Protocol.vote_time S.E (n + 1) ≤
            DecoupledConsensusModel.Protocol.opening S.E S.hc (a.round + 1) := by
          have hslot : n + 2 ≤ S.hc.opening_slot (a.round + 1) :=
            Nat.succ_le_iff.mpr (hntop.trans_lt hdhi)
          have hvoteNext : Protocol.vote_time S.E (n + 1) <
              Protocol.proposal_time S.E (n + 2) := by
            apply lt_trans ?_
              (support_cutoff_lt_proposal_time_succ S.E (n + 1))
            rw [← Proofs.Optimistic.vote_time_add_delta]
            exact Int.lt_add_of_pos_right _ S.E.Δ_pos
          exact hvoteNext.le.trans (by
            simpa only [DecoupledConsensusModel.Protocol.opening] using
              proposal_time_mono S.E hslot)
        have hsround : S.hc.round_of (n + 1) = a.round :=
          round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc
            (hn.trans (Nat.le_succ n)) (hntop.trans_lt hdhi)
        have hsettled : S.a a.round + S.E.Δ ≤
            Protocol.vote_time S.E (n + 1) := by
          apply action_add_delta_le_vote_of_lt S
          exact (action_lt_vote_time_two_after S a.round).trans_le
            (vote_time_mono_slots S.E (Nat.succ_le_succ hn))
        exact hseed.checkpointVoteStep_beforeNextAction_of_frame_run
          adm hcom hbelow hfirst hframe hc0 ready hpostPrev hG1 hpred
            hminimal ((Nat.succ_pos _).trans_le hn)
            (hopenPost.trans (vote_time_mono_slots S.E
              ((Nat.le_succ _).trans hn))) hnHor
            ((le_add_of_nonneg_right S.E.Δ_pos.le).trans hsettled)
            hnext hnextOpening hsround hsettled hprevious.2
  exact hfold d hdlo (le_refl _)

#print axioms
  PrefixFGSelectorConeAt.checkpointProtection_sourceRound_of_frame_run

private theorem PrefixFGSelectorConeAt.relativeCarrierWindow_source_beforeNextAction_run
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta
      Cfg T.erase)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    (hframe : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (hc0 : c0 ≤ a.round)
    (ready : GradeRoundReady S rho a.round)
    (hpostPrev : S.E.t_GST ≤ S.a (a.round - 1))
    (hG1 : ∀ w ∈ rho.honest, ∃ Q : Block V,
      namedG1At S rho w a.round Q)
    (hpred : NamedOldTargetRootBelowRun S rho first blocked T)
    (hminimal : ∀ (b : NamedAttestation V) (tb : Time),
      b.val_index ∈ rho.honest →
      NamedRun.emits S rho b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) →
      a.round ≤ b.round)
    (hsg : HonestSGEmissionsCompatibleAtRound S rho a.round T.erase)
    (hhor : Protocol.vote_time S.E
      (S.hc.opening_slot (a.round + 1)) + S.E.Δ ≤ rho.horizon) :
    RelativeCarrierWindowAt S rho a.round .g1 := by
  let core := adm.toNamedAdmissibleCore
  have hpost : S.E.t_GST ≤ S.a a.round :=
    ready.1.trans ((NamedOutageClosure.early_le_domain S a.round).trans
      (FrameForward.domain_le_a S a.round .g2))
  have hvoteHor : Protocol.vote_time S.E
      (S.hc.opening_slot (a.round + 1)) ≤ rho.horizon :=
    (le_add_of_nonneg_right S.E.Δ_pos.le).trans hhor
  have hsourceHor : S.a a.round ≤ rho.horizon :=
    (action_before_vote_of_round_lt S (by
      rw [round_of_opening_slot_eq_schedule S.hc (a.round + 1)]
      exact Nat.lt_succ_self a.round)).le.trans hvoteHor
  have hdomainHor : DecoupledConsensusModel.Protocol.domain S.E S.hc
      (a.round + 1) .g1 ≤ rho.horizon := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact (proposal_time_lt_vote_time S.E _).le.trans hvoteHor
  have hsourceDelay : S.a a.round + S.E.Δ ≤
      DecoupledConsensusModel.Protocol.domain S.E S.hc (a.round + 1) .g1 := by
    apply (NamedOutageClosure.action_delta_le_early
      S S.hc.R_ge_three (Nat.lt_succ_self a.round)).trans
    simp only [DecoupledConsensusModel.Protocol.early, DecoupledConsensusModel.Protocol.domain,
      DecoupledConsensusModel.Protocol.Phase.earlyOffset,
      DecoupledConsensusModel.Protocol.Phase.domainOffset]
    linarith [S.E.Δ_pos]
  intro w hw u hu
  have huHon : u ∈ rho.honest :=
    ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u a.round).mp hu).1
  obtain ⟨b, hbround, hbval, hemit⟩ :=
    NamedOutageClosure.honestRoundVoter_emits S rho hu
  obtain ⟨j, hj, _, Hb, hHb, hconfirmed⟩ :=
    Proofs.NamedOutageInputs.emitted_attestation_head S rho hemit
  have hcarrierMem : actionSGBlockAt S rho u a.round ∈
      (NamedRun.stateBeforeTime S rho (S.a a.round) u).st.core.T :=
    actionSGBlockAt_mem_storeBeforeTime S rho u a.round
  obtain ⟨D, hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
      S rho (S.a a.round) u hcarrierMem
  obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    core.toNamedScheduleWellFormed.sorted (S.a a.round)
  have hDprefix : D ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact hDbody
  have hHbSource : Hb ∈
      (NamedRun.stateBeforeTime S rho (S.a a.round) u).st.bodies := by
    have hstate := NamedActionSources.action_read_index S rho
      core.toNamedScheduleWellFormed j u b.round
        (by simpa only [hbround] using hj)
    change Hb ∈ (NamedRun.stateBefore S rho j u).st.bodies at hHb
    rw [← hbround, ← hstate]
    exact hHb
  have hHbPrefix : Hb ∈ (NamedRun.stateBefore S rho n u).st.bodies := by
    rw [← hn]
    exact hHbSource
  have hDrun : RunBlock S rho D :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S huHon hDprefix
  have hHbrun : RunBlock S rho Hb :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S huHon hHbPrefix
  have hbconfirmed := NamedOutageClosure.honest_emitted_round_confirmed
    S rho core u huHon a.round hsourceHor hbround hemit
  have hroot : D.root = Hb.root := by
    rw [← Proofs.NamedWire.erase_root D, hDerase]
    exact Option.some.inj (hbconfirmed.symm.trans hconfirmed)
  have hDH : D = Hb :=
    core.toNamedRootCollisionFree.root_injective D Hb hDrun hHbrun D Hb
      (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self Hb)) hroot
  have hHbErase : Hb.erase = actionSGBlockAt S rho u a.round := by
    rw [← hDH, hDerase]
  have hHbRoot : Hb.root = (actionSGBlockAt S rho u a.round).root := by
    rw [← Proofs.NamedWire.erase_root Hb, hHbErase]
  have hawake : (S.node u).awake a.round = true := by
    simpa only [hbround] using Proofs.Optimistic.emits_attest_awake S hemit
  have hemitAction := honest_emits_exact_actionAttestationAt_of_awake
    S core.toNamedScheduleWellFormed huHon a.round hawake hsourceHor
  have hcarrierT : Block.compatible Hb.erase T.erase = true := by
    rw [hHbErase]
    exact hsg u huHon hemitAction
  have hreadLo : S.a a.round ≤
      DecoupledConsensusModel.Protocol.domain S.E S.hc (a.round + 1) .g1 :=
    (le_add_of_nonneg_right S.E.Δ_pos.le).trans hsourceDelay
  have hrootT := hseed.fgRoot_preceq_before_nextAction_of_frame_run
    adm hcom hbelow hfirst hframe hc0 ready hpostPrev hG1 hpred hminimal
      hreadLo (FrameForward.domain_le_a S (a.round + 1) .g1) hw
  have hFT : Block.Preceq
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc (a.round + 1) .g1) w).st.core.F
      T.erase :=
    Block.preceq_trans (finalizedRoot_preceq_fgRoot S adm) hrootT
  have hk : a.round ∈
      Protocol.latest_window S.hc.η_SG (a.round + 1) := by
    apply NamedOutageClosure.mem_latest_window
    · simpa only [Nat.add_sub_cancel] using
        Nat.sub_le_sub_left S.hc.η_SG_ge_one (a.round + 1)
    · exact Nat.lt_succ_self a.round
  have hdeadline : max (S.a b.round) S.E.t_GST + S.E.Δ ≤
      DecoupledConsensusModel.Protocol.early S.E S.hc (a.round + 1) .g1 := by
    rw [hbround, max_eq_left hpost]
    apply (NamedOutageClosure.action_delta_le_early
      S S.hc.R_ge_three (Nat.lt_succ_self a.round)).trans
    simp only [DecoupledConsensusModel.Protocol.early,
      DecoupledConsensusModel.Protocol.Phase.earlyOffset]
    linarith [S.E.Δ_pos]
  have horder : DecoupledConsensusModel.Protocol.early S.E S.hc (a.round + 1) .g1 ≤
      DecoupledConsensusModel.Protocol.domain S.E S.hc (a.round + 1) .g1 := by
    simp only [DecoupledConsensusModel.Protocol.early, DecoupledConsensusModel.Protocol.domain,
      DecoupledConsensusModel.Protocol.Phase.earlyOffset,
      DecoupledConsensusModel.Protocol.Phase.domainOffset]
    linarith [S.E.Δ_pos]
  have hcut : DecoupledConsensusModel.Protocol.early S.E S.hc (a.round + 1) .g1 ≤
      rho.horizon := horder.trans hdomainHor
  have hhead : ∃ j : Nat,
      rho.events[j]? = some (.tick u (S.a a.round)) ∧
      Hb ∈ (NamedActionReads.actionReadFrom S
        (NamedRun.stateBefore S rho j u) b.round).st.bodies ∧
      b.confirmed = some Hb.root :=
    ⟨j, by simpa only [hbround] using hj, hHb, hconfirmed⟩
  change ∃ y ∈ DecoupledConsensusModel.Protocol.interpretedInputs
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc
          (a.round + 1) .g1) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc
          (a.round + 1) .g1) w).st.core.F
      S.hc.η_SG (a.round + 1)
        (DecoupledConsensusModel.Protocol.early S.E S.hc (a.round + 1) .g1) u,
    y.round = a.round ∧
      y.confirmed = some (actionSGBlockAt S rho u a.round).root ∧
      Block.find? (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc
          (a.round + 1) .g1) w).st.core.T
        (actionSGBlockAt S rho u a.round).root =
          some (actionSGBlockAt S rho u a.round)
  rcases (show Block.Preceq Hb.erase T.erase ∨
      Block.Preceq T.erase Hb.erase by
    simpa only [Block.compatible, Bool.or_eq_true] using hcarrierT) with
    hHbT | hTHb
  · simpa only [hbround, hHbErase, hHbRoot] using
      (interpretedInputs_exact_of_honest_window_vote_after_gst_common_upper
        S core .g1 hk huHon hw ⟨hbval, hbround, hemit⟩ hhead
          hHbT hFT (by simpa only [hbround] using hpost) hdeadline
            horder hcut)
  · simpa only [hbround, hHbErase, hHbRoot] using
      (interpretedInputs_exact_of_honest_window_vote_after_gst_common_upper
        S core .g1 hk huHon hw ⟨hbval, hbround, hemit⟩ hhead
          (Block.preceq_self Hb.erase) (Block.preceq_trans hFT hTHb)
            (by simpa only [hbround] using hpost) hdeadline horder hcut)

/-- The next-opening checkpoint cone with the run-scoped old-root
contract. -/
theorem PrefixFGSelectorConeAt.checkpointProtection_nextOpening_of_frame_run
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta
      Cfg T.erase)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    (hframe : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (hc0 : c0 ≤ a.round)
    (ready : GradeRoundReady S rho a.round)
    (hpostPrev : S.E.t_GST ≤ S.a (a.round - 1))
    (hG1 : ∀ w ∈ rho.honest, ∃ Q : Block V,
      namedG1At S rho w a.round Q)
    (hpred : NamedOldTargetRootBelowRun S rho first blocked T)
    (hminimal : ∀ (b : NamedAttestation V) (tb : Time),
      b.val_index ∈ rho.honest →
      NamedRun.emits S rho b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) →
      a.round ≤ b.round)
    (hhor : Protocol.vote_time S.E
      (S.hc.opening_slot (a.round + 1)) + S.E.Δ ≤ rho.horizon) :
    (∀ w ∈ rho.honest, Block.Preceq T.erase
      (voterHeadAt S rho w (S.hc.opening_slot (a.round + 1)))) ∧
      NamedHonestVotesCone S rho (S.hc.opening_slot (a.round + 1))
        (fun X => Block.Preceq T.erase X) := by
  let last := S.hc.opening_slot (a.round + 1) - 1
  have hb : S.hc.opening_slot a.round + 1 ≤ last ∧
      last < S.hc.opening_slot (a.round + 1) ∧ 0 < last ∧
      last + 1 = S.hc.opening_slot (a.round + 1) := by
    dsimp [last]
    rw [opening_slot_succ_eq]
    exact runHistory_sourceLastSlot_bounds _ _ S.hc.R_ge_two
  have hlastHor : Protocol.vote_time S.E last + S.E.Δ ≤ rho.horizon :=
    (add_le_add (vote_time_mono_slots S.E hb.2.1.le)
      (le_refl S.E.Δ)).trans hhor
  have hcone := hseed.checkpointProtection_sourceRound_of_frame_run
    adm hcom hbelow hfirst hframe hc0 ready hpostPrev hG1 hpred hminimal
      hb.1 hb.2.1 hlastHor
  have hsg := hseed.sgEmissionsCompatible_of_source_of_frame_named
    adm hcom hbelow hfirst hframe hc0 ready hpostPrev
  have hwindow := hseed.relativeCarrierWindow_source_beforeNextAction_run
    adm hcom hbelow hfirst hframe hc0 ready hpostPrev hG1 hpred hminimal
      hsg hhor
  have hvoteHor : Protocol.vote_time S.E
      (S.hc.opening_slot (a.round + 1)) ≤ rho.horizon :=
    (le_add_of_nonneg_right S.E.Δ_pos.le).trans hhor
  have hdomainG1Hor : DecoupledConsensusModel.Protocol.domain S.E S.hc
      (a.round + 1) .g1 ≤ rho.horizon := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact (proposal_time_lt_vote_time S.E _).le.trans hvoteHor
  have hdomainG2G1 : DecoupledConsensusModel.Protocol.domain S.E S.hc
      (a.round + 1) .g2 ≤
        DecoupledConsensusModel.Protocol.domain S.E S.hc (a.round + 1) .g1 := by
    simp only [DecoupledConsensusModel.Protocol.domain,
      DecoupledConsensusModel.Protocol.Phase.domainOffset]
    linarith [S.E.Δ_pos]
  have hmajority : Internal.NamedOutageEntry.GradeFormingMajority
      S rho (a.round + 1) :=
    gradeFormingMajority_of_admissible_belowOneThird S adm hbelow
      (Nat.succ_pos a.round) (hdomainG2G1.trans hdomainG1Hor)
      (by simpa only [Nat.add_sub_cancel] using
        hpostPrev.trans (Assembly.a_mono S (Nat.sub_le a.round 1)))
  have hpostOpen : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot a.round) :=
    ready.1.trans ((early_g2_lt_Γ_0 S a.round).le.trans
      (Proofs.HealingLemmas.Γ_0_lt_Γ_1 S.hc S.E.Δ_pos a.round).le)
  have hpost : S.E.t_GST ≤ Protocol.vote_time S.E last :=
    hpostOpen.trans
      (vote_time_mono_slots S.E ((Nat.le_succ _).trans hb.1))
  have hconfHor : Protocol.confirmation_time S.E last ≤ rho.horizon := by
    rwa [← vote_time_succ_add_delta_eq_confirmation_time, hb.2.2.2]
  have hread : S.a a.round ≤ Protocol.vote_time S.E (last + 1) := by
    rw [hb.2.2.2]
    exact (action_before_vote_of_round_lt S (by
      rw [round_of_opening_slot_eq_schedule S.hc (a.round + 1)]
      exact Nat.lt_succ_self a.round)).le
  have hnext : Protocol.vote_time S.E (last + 1) ≤
      S.a (a.round + 1) := by
    rw [hb.2.2.2]
    exact (opening_vote_time_lt_action S (a.round + 1)).le
  have hround : S.hc.round_of (last + 1) = a.round + 1 := by
    rw [hb.2.2.2]
    exact round_of_opening_slot_eq_schedule S.hc _
  have hroot : ∀ w ∈ rho.honest, Block.Preceq
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w
          (last + 1)).st.core.toHealing.toFG) T.erase := by
    intro w hw
    simpa only [Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
      Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using
      (hseed.fgRoot_preceq_before_nextAction_of_frame_run
        adm hcom hbelow hfirst hframe hc0 ready hpostPrev hG1 hpred
          hminimal hread hnext hw)
  have hanchors : ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w (last + 1)) T.erase = true := by
    intro w hw
    have hvoteHorLast : Protocol.vote_time S.E (last + 1) ≤
        rho.horizon := by
      simpa only [hb.2.2.2] using hvoteHor
    exact voterAnchorAt_compatible_of_previousRelativeCarrier
      S adm hround hvoteHorLast hwindow hmajority hsg hw (hroot w hw)
  obtain ⟨P, _, hPentry, hPheight0, _, hPrun⟩ :=
    action_named_checkpoint S adm hseed.signerHonest hseed.sourceMem
  have hPT : P.erase = T.erase :=
    hPentry.trans hseed.checkpointDerived.symm
  have hPheight : (Protocol.derive_named S.E S.cfg P).h =
      blocked + 1 := hPheight0.trans hseed.sourceDerivedHeight
  have hmajority' :=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow
  have hstep := WeakGoldfish.goldfishCone_succ_of_runFrontierWitnesses
    S adm.toNamedAdmissibleCore hcom hmajority' hb.2.2.1 hpost hconfHor
      hcone.2 (by
        intro w hw C hCerase hhigh hCrun b tb K hb' hemit ht hrow hW hKrun
        have hCP : C = P := by
          apply adm.toNamedRootCollisionFree.root_injective
            C P hCrun hPrun C P
              (Or.inl (Proofs.NamedAncestry.named_self C))
              (Or.inr (Proofs.NamedAncestry.named_self P))
          rw [← Proofs.NamedWire.erase_root C, hCerase, ← hPT,
            Proofs.NamedWire.erase_root]
        subst C
        have hupper := hseed.readFrontier_le_before_nextAction_run
          adm hmajority' hfirst hnext w
        have hband :
            (Internal.NamedRecoveryRead.voteDutyRead S rho w
              (last + 1)).st.core.h_max - 1 ≤ blocked + 1 := by
          apply Nat.sub_le_iff_le_add.mpr
          simpa only [Internal.NamedRecoveryRead.voteDutyRead,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom,
            Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
            Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hupper
        rw [hPheight] at hhigh
        exact False.elim ((Nat.not_lt_of_ge hband) hhigh))
      (by
        intro w hw
        simpa only [Block.compatible, Bool.or_eq_true] using
          Or.inl (hroot w hw)) hanchors
  simpa only [hb.2.2.2] using hstep

#print axioms
  PrefixFGSelectorConeAt.checkpointProtection_nextOpening_of_frame_run

/-- earlier's closed later action and slot history for the run-scoped named
regime. -/
theorem NamedHeightRegimeRun.laterHistory_main
    {S : Setup V} {rho : Run V} {r0 : Round} {blocked : Height}
    {first i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (h : NamedHeightRegimeRun S rho r0 blocked first i a ta
      Cfg T Tprev c0)
    {c : Round} (hc : a.round + 1 ≤ c) :
    (∀ s, S.hc.round_of s = c →
      Protocol.vote_time S.E s + S.E.Δ ≤ rho.horizon →
      (∀ w ∈ rho.honest,
        Block.Preceq T.erase (voterHeadAt S rho w s)) ∧
      NamedHonestVotesCone S rho s
        (fun X => Block.Preceq T.erase X)) ∧
    (S.a c ≤ rho.horizon →
      HonestSGEmissionsCompatibleAtRound S rho c T.erase ∧
      ∀ w ∈ rho.honest, ∀ W,
        fgConfirmationWitness S (actionStoreAt S rho w c) = some W →
        Block.compatible W T.erase = true) := by
  have hsourceOpenPost : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot a.round) := by
    rw [← Protocol.Γ_1_eq_vote_time]
    exact h.ready.1.trans ((early_g2_lt_Γ_0 S a.round).le.trans
      (Γ_0_lt_Γ_1 S.hc S.E.Δ_pos a.round).le)
  have hsourceActionPost :=
    hsourceOpenPost.trans (opening_vote_time_lt_action S a.round).le
  have hsourceSG := h.seed.sgEmissionsCompatible_of_source_of_frame_named
    adm hcom hbelow h.crossing h.frame h.c0le h.ready h.postPrev
  revert hc
  induction c using Nat.strong_induction_on with
  | h c ih =>
    intro hc
    have hcpos : 1 ≤ c :=
      (Nat.succ_le_succ (Nat.zero_le a.round)).trans hc
    have hp : c - 1 + 1 = c := Nat.sub_add_cancel hcpos
    have hpredlt : c - 1 < c :=
      Nat.sub_lt (Nat.zero_lt_of_lt hcpos) Nat.zero_lt_one
    have hsourcePred : a.round ≤ c - 1 :=
      Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hc)
    have hsourceLt : a.round < c := Nat.lt_of_succ_le hc
    have hopenRound := round_of_opening_slot_eq_schedule S.hc c
    have hsourceRead : S.a a.round ≤
        Protocol.vote_time S.E (S.hc.opening_slot c) :=
      (action_before_vote_of_round_lt S (by
        rw [hopenRound]
        exact hsourceLt)).le
    have hopenPost : S.E.t_GST ≤
        Protocol.vote_time S.E (S.hc.opening_slot c) :=
      hsourceOpenPost.trans (vote_time_mono_slots S.E
        (Nat.mul_le_mul_right S.hc.R hsourceLt.le))
    have hprevPost : S.E.t_GST ≤ S.a (c - 1) :=
      hsourceActionPost.trans (Assembly.a_mono S hsourcePred)
    have hprevSG : S.a (c - 1) ≤ rho.horizon →
        HonestSGEmissionsCompatibleAtRound S rho (c - 1) T.erase := by
      intro hhor
      by_cases heq : c - 1 = a.round
      · exact heq ▸ hsourceSG
      · exact ((ih (c - 1) hpredlt
          (Nat.succ_le_of_lt
            (lt_of_le_of_ne hsourcePred (Ne.symm heq)))).2 hhor).1
    have hpriorFG : ∀ read, read ≤ S.a c → read ≤ rho.horizon →
        ∀ r, a.round + 1 ≤ r → S.a r < read →
        ∀ w ∈ rho.honest, ∀ W,
          fgConfirmationWitness S (actionStoreAt S rho w r) = some W →
          Block.compatible W T.erase = true := by
      intro read hread hhor r hr ht w hw W hW
      have hrc : r < c := by
        by_contra hn
        exact (not_lt_of_ge
          (Assembly.a_mono S (Nat.le_of_not_gt hn)))
            (ht.trans_le hread)
      exact ((ih r hrc hr).2 (ht.le.trans hhor)).2 w hw W hW
    have hopening :
        Protocol.vote_time S.E (S.hc.opening_slot c) + S.E.Δ ≤
          rho.horizon →
        (∀ w ∈ rho.honest,
          Block.Preceq T.erase
            (voterHeadAt S rho w (S.hc.opening_slot c))) ∧
        NamedHonestVotesCone S rho (S.hc.opening_slot c)
          (fun X => Block.Preceq T.erase X) := by
      intro hhor
      by_cases heq : c = a.round + 1
      · subst c
        exact h.seed.checkpointProtection_nextOpening_of_frame_run
          adm hcom hbelow h.crossing h.frame h.c0le h.ready h.postPrev
            h.g1 h.pred h.minimal hhor
      have hprev : a.round + 1 ≤ c - 1 :=
        Nat.le_sub_one_of_lt (lt_of_le_of_ne hc (Ne.symm heq))
      let last := S.hc.opening_slot c - 1
      have hb : S.hc.opening_slot (c - 1) + 1 ≤ last ∧
          last < S.hc.opening_slot c ∧ 0 < last ∧
          last + 1 = S.hc.opening_slot c := by
        have hn := opening_slot_succ_eq S.hc (c - 1)
        rw [hp] at hn
        dsimp [last]
        rw [hn]
        exact runHistory_laterLastSlot_bounds _ _ S.hc.R_ge_two
      have hlastRound : S.hc.round_of last = c - 1 :=
        round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc
          hb.1 (hp ▸ hb.2.1)
      have hlastHor : Protocol.vote_time S.E last + S.E.Δ ≤
          rho.horizon :=
        (add_le_add (vote_time_mono_slots S.E hb.2.1.le)
          (le_refl S.E.Δ)).trans hhor
      have hcone := ((ih (c - 1) hpredlt hprev).1
        last hlastRound hlastHor).2
      have hreadHor : Protocol.vote_time S.E
          (S.hc.opening_slot c) ≤ rho.horizon :=
        (le_add_of_nonneg_right S.E.Δ_pos.le).trans hhor
      have hprevRead : S.a (c - 1) ≤
          Protocol.vote_time S.E (S.hc.opening_slot c) :=
        (action_before_vote_of_round_lt S (by
          rw [hopenRound]
          exact hpredlt)).le
      have hsg := hprevSG (hprevRead.trans hreadHor)
      have hlastPost : S.E.t_GST ≤ Protocol.vote_time S.E last :=
        hsourceOpenPost.trans (vote_time_mono_slots S.E
          ((Nat.mul_le_mul_right S.hc.R hsourcePred).trans
            ((Nat.le_succ _).trans hb.1)))
      have hconfHor : Protocol.confirmation_time S.E last ≤
          rho.horizon := by
        rwa [← vote_time_succ_add_delta_eq_confirmation_time,
          hb.2.2.2]
      have hnextRound : S.hc.round_of (last + 1) = c := by
        rwa [hb.2.2.2]
      have hstep :=
        h.seed.checkpointVoteStep_of_actionHistories_of_frame_run
          adm hcom hbelow h.crossing h.frame h.c0le h.ready h.postPrev
            h.g1 h.pred h.minimal hb.2.2.1 hlastPost hconfHor
            (by rwa [hb.2.2.2])
            (hnextRound ▸ hcpos)
            (by simpa only [hnextRound] using hsg)
            (by simpa only [hnextRound] using hprevPost)
            (by simpa only [hb.2.2.2] using
              hpriorFG _ (opening_vote_time_lt_action S c).le hreadHor)
            hcone
      simpa only [hb.2.2.2] using hstep
    have haction : S.a c ≤ rho.horizon →
        HonestSGEmissionsCompatibleAtRound S rho c T.erase ∧
        ∀ w ∈ rho.honest, ∀ W,
          fgConfirmationWitness S (actionStoreAt S rho w c) = some W →
          Block.compatible W T.erase = true := by
      intro hhor
      have hcone :=
        (hopening
          ((runHistory_openingVote_add_delta_le_action S c).trans hhor)).2
      have hsg := hprevSG ((Assembly.a_mono S hpredlt.le).trans hhor)
      have hroots : ∀ w ∈ rho.honest, Block.compatible
          (Protocol.get_fg_root
            (actionStoreAt S rho w c).st.core.toHealing.toFG)
          T.erase = true := by
        intro w hw
        rw [actionStoreAt_fgRoot_eq_storeBeforeTime]
        exact h.seed.fgRoot_compatible_of_recentWitnessHistory_of_frame_run
          adm hcom hbelow h.crossing h.frame h.c0le h.ready h.postPrev
            h.g1 h.pred h.minimal (Assembly.a_mono S hsourceLt.le)
              (hpriorFG _ (le_refl _) hhor) hw
      have hconfHor : Protocol.confirmation_time S.E
          (S.hc.opening_slot c) ≤ rho.horizon := by
        rwa [opening_confirmation_time_eq_action]
      constructor
      · have hout :=
          sgEmissionsCompatible_succ_of_previousSGHistory_and_openingVotes_named
            S adm hcom hbelow hsg (by simpa only [hp] using hcone)
              hprevPost (by simpa only [hp] using hhor)
                (by simpa only [hp] using hroots)
        simpa only [hp] using hout
      · intro w hw W hW
        exact fgConfirmationWitness_compatible_of_previousSGHistory_and_openingVotes_named
          S adm hcom hbelow hsg (by simpa only [hp] using hcone)
            hprevPost (by simpa only [hp] using hopenPost)
              (by simpa only [hp] using hconfHor) hw
                (by simpa only [hp] using hroots w hw)
                  (by simpa only [hp] using hW)
    refine ⟨?_, haction⟩
    intro s hround hhor
    have hslo : S.hc.opening_slot c ≤ s := by
      rw [← hround]
      exact Nat.div_mul_le_self s S.hc.R
    have hshi : s < S.hc.opening_slot (c + 1) := by
      apply (Nat.div_lt_iff_lt_mul
        (Nat.zero_lt_of_lt S.hc.R_ge_two)).mp
      change S.hc.round_of s < c + 1
      rw [hround]
      exact Nat.lt_succ_self _
    rcases eq_or_lt_of_le hslo with heq | hinterior
    · exact heq ▸ hopening (heq ▸ hhor)
    have hactionHor :=
      (runHistory_action_le_interiorVote_add_delta S hinterior).trans hhor
    have hcurrent := haction hactionHor
    have hsg := hprevSG
      ((Assembly.a_mono S hpredlt.le).trans hactionHor)
    have hreadHor : Protocol.vote_time S.E s ≤ rho.horizon :=
      (le_add_of_nonneg_right S.E.Δ_pos.le).trans hhor
    have hreadNext : Protocol.vote_time S.E s ≤ S.a (c + 1) :=
      (vote_time_mono_slots S.E hshi.le).trans
        (opening_vote_time_lt_action S _).le
    have hthroughFG : ∀ read, read ≤ Protocol.vote_time S.E s →
        ∀ r, a.round + 1 ≤ r → S.a r < read →
        ∀ w ∈ rho.honest, ∀ W,
          fgConfirmationWitness S (actionStoreAt S rho w r) = some W →
          Block.compatible W T.erase = true := by
      intro read hread r hr ht w hw W hW
      have hrc : r < c + 1 := by
        by_contra hn
        exact (not_lt_of_ge
          (Assembly.a_mono S (Nat.le_of_not_gt hn)))
            (ht.trans_le (hread.trans hreadNext))
      rcases eq_or_lt_of_le (Nat.le_of_lt_succ hrc) with heq | hlt
      · subst r
        exact hcurrent.2 w hw W hW
      · exact ((ih r hlt hr).2
          (ht.le.trans (hread.trans hreadHor))).2 w hw W hW
    have hopenPos : 0 < S.hc.opening_slot c :=
      Nat.mul_pos (Nat.zero_lt_of_lt hcpos)
        (Nat.zero_lt_of_lt S.hc.R_ge_two)
    have hfold : ∀ d, S.hc.opening_slot c ≤ d → d ≤ s →
        (∀ w ∈ rho.honest,
          Block.Preceq T.erase (voterHeadAt S rho w d)) ∧
        NamedHonestVotesCone S rho d
          (fun X => Block.Preceq T.erase X) := by
      intro d hd
      induction d, hd using Nat.le_induction with
      | base =>
        intro _
        exact hopening
          ((add_le_add (vote_time_mono_slots S.E hslo)
            (le_refl S.E.Δ)).trans hhor)
      | succ d hd ihSlot =>
        intro hds
        have hprev := ihSlot (Nat.le_of_succ_le hds)
        have hroundD := runHistory_round_of_between_openings S.hc
          (hd.trans (Nat.le_succ d)) (hds.trans_lt hshi)
        have htime := vote_time_mono_slots S.E hds
        have hconfHor : Protocol.confirmation_time S.E d ≤
            rho.horizon := by
          rw [← vote_time_succ_add_delta_eq_confirmation_time]
          exact (add_le_add htime (le_refl S.E.Δ)).trans hhor
        exact h.seed.checkpointVoteStep_of_actionHistories_of_frame_run
          adm hcom hbelow h.crossing h.frame h.c0le h.ready h.postPrev
            h.g1 h.pred h.minimal (hopenPos.trans_le hd)
            (hopenPost.trans (vote_time_mono_slots S.E hd)) hconfHor
            (hsourceRead.trans
              (vote_time_mono_slots S.E (hd.trans (Nat.le_succ d))))
            (hroundD ▸ hcpos) (by simpa only [hroundD] using hsg)
            (by simpa only [hroundD] using hprevPost)
            (hthroughFG _ htime) hprev.2
    exact hfold s hslo (le_refl s)


private theorem runHistory_actionBody_runBlock
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

/-- Exact named checkpoint recovery for every honest row at the source
height of a run-scoped regime. -/
theorem NamedHeightRegimeRun.witness_eq
    {S : Setup V} {rho : Run V} {r0 : Round} {blocked : Height}
    {first i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (h : NamedHeightRegimeRun S rho r0 blocked first i a ta
      Cfg T Tprev c0)
    {b : NamedAttestation V} {tb : Time}
    (hb : b.val_index ∈ rho.honest)
    (hemit : NamedRun.emits S rho b.val_index (Object.attest b) tb)
    (hrow : b.height_pair.erase.height? = some (blocked + 1)) :
    fgConfirmationWitness S (actionStoreAt S rho b.val_index b.round) =
      some T.erase := by
  rcases eq_or_lt_of_le (h.minimal b tb hb hemit hrow) with heq | hlt
  · exact h.seed.confirmationWitness_of_sameRound_honestHeightRow_of_frame_named
      adm hcom hbelow h.crossing h.frame h.ready hb hemit hrow heq
  · obtain ⟨D, K, hW, hDmem, _hsource, hDheight, hKmem,
        hKerase, hKheight, hKD, _hshape⟩ :=
      honestHeightRow_confirmationWitness S adm hb hemit hrow
    have hhor : S.a b.round ≤ rho.horizon := by
      have htime : tb = S.a b.round :=
        (Proofs.Optimistic.emits_attest_shape S hemit).2
      obtain ⟨k, hk, _⟩ := hemit
      have hin := (adm.in_horizon
        (Event.tick b.val_index tb) (List.mem_of_getElem? hk)).2
      simpa only [Event.time, htime] using hin
    have hDrun : RunBlock S rho D :=
      runHistory_actionBody_runBlock S adm hb hDmem
    have hKrun : RunBlock S rho K :=
      runHistory_actionBody_runBlock S adm hb hKmem
    have hKDnamed := Protocol.namedPreceq_of_runBlock_erase_preceq
      adm hKrun hDrun hKD
    have hKfixed :
        (Protocol.derive_named S.E S.cfg K).T_h = K.erase :=
      (Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hKDnamed
        (hKheight.trans hDheight.symm)).trans hKerase.symm
    have hW' : fgConfirmationWitness S
        (actionStoreAt S rho b.val_index b.round) =
          some (Protocol.derive_named S.E S.cfg D).T_h := by
      rw [hW, hKfixed, hKerase]
    have hcompat := ((h.laterHistory_main adm hcom hbelow hlt).2 hhor).2
      b.val_index hb (Protocol.derive_named S.E S.cfg D).T_h hW'
    obtain ⟨hTrun, hTheight⟩ := h.checkpoint_runBlock adm
    have heqTarget :=
      (h.seed.laterFGWitness_eq_or_extends_checkpoint_of_frameN
        adm hcom hbelow h.crossing h.frame h.c0le h.ready h.postPrev
        h.minimal h.checkpointPreceq hTrun h.checkpointErase hTheight
        hlt hhor hb hDmem hW' hcompat).1 hDheight
    rw [hW']
    exact congrArg some heqTarget


/-- Every later honest vote-duty head extends the checkpoint of a run-scoped
regime. -/
theorem NamedHeightRegimeRun.heads
    {S : Setup V} {rho : Run V} {r0 : Round} {blocked : Height}
    {first i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (h : NamedHeightRegimeRun S rho r0 blocked first i a ta
      Cfg T Tprev c0)
    {s : Slot} (hround : a.round + 1 ≤ S.hc.round_of s)
    (hhor : Protocol.vote_time S.E s + S.E.Δ ≤ rho.horizon) :
    ∀ w ∈ rho.honest,
      Block.Preceq T.erase (voterHeadAt S rho w s) :=
  ((h.laterHistory_main adm hcom hbelow hround).1 s rfl hhor).1


/-- Every honest vote-duty head from the first source-round interior slot
extends the checkpoint of a run-scoped regime. -/
theorem NamedHeightRegimeRun.heads_from_firstInterior
    {S : Setup V} {rho : Run V} {r0 : Round} {blocked : Height}
    {first i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (h : NamedHeightRegimeRun S rho r0 blocked first i a ta
      Cfg T Tprev c0)
    {d : Slot} (hdlo : S.hc.opening_slot a.round + 1 ≤ d)
    (hhor : Protocol.vote_time S.E d + S.E.Δ ≤ rho.horizon) :
    ∀ w ∈ rho.honest,
      Block.Preceq T.erase (voterHeadAt S rho w d) := by
  by_cases hdhi : d < S.hc.opening_slot (a.round + 1)
  · exact (h.seed.checkpointProtection_sourceRound_of_frame_run
      adm hcom hbelow h.crossing h.frame h.c0le h.ready h.postPrev
        h.g1 h.pred h.minimal hdlo hdhi hhor).1
  · have hR : 0 < S.hc.R :=
      lt_of_lt_of_le (by decide : 0 < 2) S.hc.R_ge_two
    have hround : a.round + 1 ≤ S.hc.round_of d := by
      unfold Protocol.HealConfig.round_of
      exact (Nat.le_div_iff_mul_le hR).mpr (Nat.le_of_not_lt hdhi)
    exact h.heads adm hcom hbelow hround hhor


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
