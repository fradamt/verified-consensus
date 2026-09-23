module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.HeightRegimeNamed
public import DecoupledConsensusProofs.Objects.AdmissibleCore
public import DecoupledConsensusProofs.Objects.RecoveryInitialSourceHistory
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryInitialSourceNamedHistory
public import DecoupledConsensusProofs.Objects.HeightRegimeStep
public import DecoupledConsensusProofs.Execution.HandoverLegacyFinality
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryRawVetoAnchor

@[expose] public section

/-!
# Named height-regime induction restatement ledger

This module is intentionally separate from `HeightRegimeInductionRun.lean`.
The prior module is red at its first `CombinedAttestation` application and
must remain byte-exact. The records used by the restatements are
`NamedHeightRegime` and `HeightRegimeFrameN`; raw block results erase named
blocks only at the specified raw boundary.

The 19 active declarations below are the named consumer surface. Producer 9
and producer 10 carry named heights and named checkpoints. Raw blocks occur
only at FG-witness and voter-head boundaries. The historical B2 Open records
remain at the end of this file as an audit trail for the replaced statements.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]











































/-- earlier's old-target-root bound over the fully named regime frame. -/
private theorem delayed_namedAncestorBodyMem {st : Protocol.NamedStore V}
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
theorem PrefixFGSelectorConeAt.oldTargetRoot_preceq_of_strictActionCut_of_frame_named
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
    (hpred : NamedOldTargetRootBelow S rho first blocked T)
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
    delayed_namedAncestorBodyMem hcoh.2.2.1 hC hKC
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
  · have hlow : (Protocol.derive_named S.E S.cfg C).h_j ≤ blocked :=
      Nat.le_of_lt_succ (lt_of_le_of_ne hupper heq)
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
          (hpred b tb hb hemit hbefore K heqB hpairB hR'
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

#print axioms PrefixFGSelectorConeAt.oldTargetRoot_preceq_of_strictActionCut_of_frame_named

/-- earlier's recent-witness FG-root bootstrap over the fully named frame. -/
theorem PrefixFGSelectorConeAt.fgRoot_compatible_of_recentWitnessHistory_of_frame_named
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
    (hpred : NamedOldTargetRootBelow S rho first blocked T)
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
    have hroot := hseed.oldTargetRoot_preceq_of_strictActionCut_of_frame_named
      adm hcom hbelow hfirst hframe hc0 ready hpostPrev hG1 hpred hminimal
        hcut hw hfrontier hC hb hemit hold hpair hJ hR
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr hroot

#print axioms PrefixFGSelectorConeAt.fgRoot_compatible_of_recentWitnessHistory_of_frame_named

/-- The named source body is present at every honest source action read. -/
theorem PrefixFGSelectorConeAt.sourceMem_at_action_of_frame_named
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hframe : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (ready : GradeRoundReady S rho a.round)
    {w : V} (hw : w ∈ rho.honest) :
    Cfg ∈ (actionStoreAt S rho w a.round).st.bodies := by
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
  rcases actionFGSource_genuineClear_or_selectedG2_named
      S rho a.val_index a.round hQ hseed.exactFGSource with
    hgenuine | hselected
  · obtain ⟨B, hgenuine, -, -, -, hCfgB⟩ := hgenuine
    have hvoteBody := ancestorGenuineConfirmation_body_at_nextVote_of_floor
      S adm ready hseed.signerHonest hgenuine hCfgB hseed.sourceMem
        hfloor hseed.sourceDerivedHeight (Proofs.NamedWire.erase_preceq hTprevCfg)
        hactionPrefix hactionHor hw
    let vote := Protocol.vote_time S.E (S.hc.opening_slot a.round + 1)
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
        hfloor hseed.sourceDerivedHeight (Proofs.NamedWire.erase_preceq hTprevCfg)
        hactionPrefix hw).1

#print axioms PrefixFGSelectorConeAt.sourceMem_at_action_of_frame_named

/-- The local frontier bound from the named source and frame. -/
theorem PrefixFGSelectorConeAt.localFrontier_ge_from_source_of_frame_named
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg Tprev : NamedBlock V} {T : Block V} {c0 : Round}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hframe : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (ready : GradeRoundReady S rho a.round)
    {read : Time} (hread : S.a a.round ≤ read)
    {w : V} (hw : w ∈ rho.honest) :
    blocked + 1 ≤ (rho.storeBeforeTime S w read).h_max := by
  have hsource := hseed.sourceMem_at_action_of_frame_named
    adm hframe ready hw
  have hsourcePre : Cfg ∈
      (NamedRun.stateBeforeTime S rho (S.a a.round) w).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hsource
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
  simpa only [hseed.sourceDerivedHeight] using hheight

#print axioms PrefixFGSelectorConeAt.localFrontier_ge_from_source_of_frame_named










































































end HealingSurface

end Proofs
end DecoupledConsensusModel

end
