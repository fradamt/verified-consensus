module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.FGSafetyRootNamed
public import DecoupledConsensusProofs.Objects.FGConfirmationHistory
public import DecoupledConsensusProofs.Generic.CanonicalRegimeFromChain
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Grades.HonestProposalRawLifecycleNamed

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# The round after a healed honest opening is not lost ( NL)

earlier's `notLost_nextRound_of_honestOpening_after_SG_healing`
(`NonLostAfterHonestOpeningRun.lean:24-158`) proves the same fact from the
moving-chain split boundary and the greatest-previous-head floor. Both are on a
red import path in the selection, so this leaf follows earlier's argument over the
clean named base instead.

earlier's route in two halves.

* Every honest round-`p` SG carrier equals the opening's proposal
  (`hSG`), so the carriers are above it. The clean named twin is
  `ActionCarriersCover`, which is the only direction the conclusion needs.
* Every honest FG root at the round-`(p+1)` read is below that proposal
  (`hroots`). earlier gets this by rebasing the moving history at the next
  opening. Here it is the named FG-root witness decomposition
  (`fgRoot_confirmationWitness_at_read`) run against the height regime, split
  on the emitting round:

  - an old root is below the regime's base checkpoint, which is below every
    honest head from the base's first interior slot on, hence below the head at
    the opening slot of `p`, which is the proposal;
  - a root explained by an honest row of a round STRICTLY below `p` is the
    regime checkpoint of that row's height, again below the same head;
  - a root explained by an honest row of round `p` itself is the target of that
    action's own FG source (`honestHeightRow_confirmationWitness`), and the
    healed lifecycle makes that source the proposal.

  The third case is exactly what earlier's `hnew` obtains from
  `rebaseAt_of_heightSourceBounds`'s last arm (`hlast`), where the source is
  rewritten to the live confirmation.

The three lifecycle facts at the honest opening are hypotheses of the `_of_`
form below and are discharged in the pin-free theorem at the end.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

/-- Verbatim copy of `openingSlot_add_two_le_openingSlot_of_lt`
(`MovingChainRowRun.lean:337`); that module is not on this leaf's import path. -/
private theorem w4OpeningSlotAddTwoLe
    (S : Setup V) {m r : Round} (h : m < r) :
    S.hc.opening_slot m + 2 ≤ S.hc.opening_slot r := by
  have hR : 2 ≤ S.hc.R := S.hc.R_ge_two
  have hstep : (m + 1) * S.hc.R ≤ r * S.hc.R := Nat.mul_le_mul_right _ h
  simp only [Protocol.HealConfig.opening_slot]
  calc
    m * S.hc.R + 2 ≤ m * S.hc.R + S.hc.R := Nat.add_le_add_left hR _
    _ = (m + 1) * S.hc.R := by ring
    _ ≤ r * S.hc.R := hstep

/-- Verbatim copy of the private helper `runBlock_of_mem_storeBeforeTime`
(`FGSafetyRootNamedRun.lean:21`); the original is `private`. -/
private theorem w4RunBlockOfMemStoreBeforeTime
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {t : Time} {D : NamedBlock V}
    (hD : D ∈ (rho.storeBeforeTime S w t).bodies) : RunBlock S rho D := by
  obtain ⟨n, hn, -⟩ :=
    Proofs.Bridges.stateBeforeTime_eq_stateBefore S adm.toNamedScheduleWellFormed t
  have hD' : D ∈ (rho.stateBefore S n w).st.bodies := by
    simpa only [Run.storeBeforeTime, hn] using hD
  exact Proofs.Bridges.runBlock_of_stateBefore_mem S hw hD'

/-- Verbatim copy of the private helper
`NamedHeightRegimeRun.fgRoot_compatible_after_source_run`
(`FGSafetyRootNamedRun.lean:47`); the original is `private`. -/
private theorem w4FgRootCompatibleAfterSourceRun
    {S : Setup V} {rho : Run V} {r0 : Round} {blocked : Height}
    {first i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (h : NamedHeightRegimeRun S rho r0 blocked first i a ta
      Cfg T Tprev c0)
    {read : Time} (hread : S.a a.round ≤ read)
    (hreadHor : read ≤ rho.horizon) {w : V} (hw : w ∈ rho.honest) :
    Block.compatible
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w read).toHealing.toFG) T.erase = true := by
  apply h.seed.fgRoot_compatible_of_recentWitnessHistory_of_frame_run
    adm hcom hbelow h.crossing h.frame h.c0le h.ready h.postPrev
      h.g1 h.pred h.minimal hread
  · intro r hr ht v hv W hW
    exact ((h.laterHistory_main adm hcom hbelow hr).2
      (ht.le.trans hreadHor)).2 v hv W hW
  · exact hw

/-- **earlier's `hroots` over the clean named base.**

Every honest FG root at the action read of the round after a healed honest
opening lies below that opening's named proposal. -/
theorem w4FgRoot_preceq_openingProposal_after_SG_healing
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {p : Round} {P : NamedBlock V}
    (hp : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ p)
    (hheads : ∀ v ∈ rho.honest,
      voteDutyHead S rho v (S.hc.opening_slot p) = P.erase)
    (hsource : ∀ w ∈ rho.honest, ∀ X : Block V,
      actionFGSource S (actionStoreAt S rho w p) = some X → X = P.erase)
    (hhor : S.a (p + 1) ≤ rho.horizon)
    {u : V} (hu : u ∈ rho.honest) :
    Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S u (S.a (p + 1))).toHealing.toFG) P.erase := by
  classical
  have hpD : fgSafetyProgressDeadline S rho rGST gap delayExtra < p :=
    lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 2)) hp
  have hread : S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) ≤
      S.a (p + 1) :=
    (action_strictMono S).monotone (hpD.le.trans (Nat.le_succ p))
  have hactionP : S.a p ≤ S.a (p + 1) :=
    (action_strictMono S).monotone (Nat.le_succ p)
  have hshor : Protocol.vote_time S.E (S.hc.opening_slot p) + S.E.Δ ≤
      rho.horizon := by
    rw [vote_time_add_delta]
    refine (support_cutoff_le_confirmation_time S.E (S.hc.opening_slot p)).trans ?_
    rw [opening_confirmation_time_eq_action]
    exact hactionP.trans hhor
  have hs : S.hc.opening_slot (fgSafetyProgressDeadline S rho rGST gap delayExtra)
      + 1 ≤ S.hc.opening_slot p :=
    (Nat.add_le_add_left (by decide : (1 : Nat) ≤ 2) _).trans
      (w4OpeningSlotAddTwoLe S hpD)
  obtain ⟨blocked, first, Tprev, hfirst, hbase⟩ :=
    exists_namedHeightRegimeBaseRun_before_fgSafetyProgressDeadline
      S adm hcom hbelow hrec hdelay hpost (hread.trans hhor)
  have hgst := gstLagged_le_Γ_neg1_of_gst_le_a S rGST hpost
  let R := Protocol.get_fg_root
    (rho.storeBeforeTime S u (S.a (p + 1))).toHealing.toFG
  change Block.Preceq R P.erase
  rcases fgRoot_confirmationWitness_at_read S adm.toNamedAdmissibleCore
      (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow)
      hu (S.a (p + 1)) with
    hgen | ⟨C, hC, hJ, b, tb, hb, hemit, hbt, hpair, hW⟩
  · rw [show R = Block.genesis from hgen]
    exact Protocol.preceq_genesis _
  · have hrowHeight : b.height_pair.erase.height? =
        some (Protocol.derive_named S.E S.cfg C).h_j := by
      rw [hpair]
      rfl
    by_cases hsmall :
        (Protocol.derive_named S.E S.cfg C).h_j ≤ blocked
    · obtain ⟨i, a, ta, Cfg, T, hreg, ha⟩ :=
        hbase.exists_regime_before_deadline adm hbelow hgst hfirst
      have hRT := w4FgRootCompatibleAfterSourceRun adm hcom hbelow hreg
        (((action_strictMono S).monotone ha).trans hread) hhor hu
      have hRTpre : Block.Preceq R T.erase := by
        by_cases hz : (Protocol.derive_named S.E S.cfg C).h_j = 0
        · have hgenJ :=
            NamedJustificationCertificates.justified_zero_is_genesis
              S.E S.cfg C hz
          have hRgen : R = Block.genesis := by
            dsimp only [R]
            exact hJ.symm.trans hgenJ
          rw [hRgen]
          exact Protocol.preceq_genesis _
        · obtain ⟨J, hJC, hJerase, hJheight⟩ :=
            (NamedCheckpointHeights.justified_ancestor_height
              S.E S.cfg C).resolve_left hz
          have hCrun : RunBlock S rho C :=
            w4RunBlockOfMemStoreBeforeTime S adm hu hC
          have hJrun : RunBlock S rho J :=
            Proofs.NamedRuntime.blockInRun_of_ancestor S rho hCrun hJC
          obtain ⟨hTrun, hTheight⟩ := hreg.checkpoint_runBlock adm
          rcases (show Block.Preceq R T.erase ∨ Block.Preceq T.erase R by
            simpa only [Block.compatible, Bool.or_eq_true] using hRT) with
            hRT | hTR
          · exact hRT
          · have hTJ : NamedBlock.Preceq T J :=
              Protocol.namedPreceq_of_runBlock_erase_preceq
                adm hTrun hJrun (by simpa only [hJ, hJerase] using hTR)
            have hmono := Proofs.NamedEntryHeight.derive_height_mono
              S.E S.cfg hTJ
            rw [hTheight, hJheight] at hmono
            exact False.elim
              (Nat.not_succ_le_self blocked (hmono.trans hsmall))
      have hopen : S.hc.opening_slot a.round + 1 ≤ S.hc.opening_slot p :=
        (Nat.add_le_add_right (Nat.mul_le_mul_right S.hc.R ha) 1).trans hs
      refine Block.preceq_trans hRTpre ?_
      rw [← hheads u hu]
      exact hreg.heads_from_firstInterior adm hcom hbelow hopen hshor u hu
    · have hactLt : S.a b.round < S.a (p + 1) := by
        simpa only [(Proofs.Optimistic.emits_attest_shape S hemit).2] using hbt
      have hbp : b.round ≤ p :=
        Nat.le_of_lt_succ ((action_strictMono S).lt_iff_lt.mp hactLt)
      rcases lt_or_eq_of_le hbp with hlt | hlast
      · let n := (Protocol.derive_named S.E S.cfg C).h_j - (blocked + 1)
        have heqn : blocked + n + 1 =
            (Protocol.derive_named S.E S.cfg C).h_j := by
          calc
            _ = n + (blocked + 1) := by ac_rfl
            _ = (Protocol.derive_named S.E S.cfg C).h_j :=
              Nat.sub_add_cancel (Nat.lt_of_not_ge hsmall)
        have hrow : b.height_pair.erase.height? = some (blocked + n + 1) := by
          rw [hrowHeight]
          exact congrArg some heqn.symm
        obtain ⟨first_n, i, a, ta, Cfg, T, Tprev', c0, hreg⟩ :=
          hbase.exists_regime_of_row_named adm hcom hbelow hgst n hb hemit hrow
        have hTR : T.erase = R := Option.some.inj
          ((hreg.witness_eq adm hcom hbelow hb hemit hrow).symm.trans hW)
        have hab : a.round ≤ b.round := hreg.minimal b tb hb hemit hrow
        have hopen : S.hc.opening_slot a.round + 1 ≤ S.hc.opening_slot p :=
          (Nat.add_le_add_left (by decide : (1 : Nat) ≤ 2) _).trans
            (w4OpeningSlotAddTwoLe S (lt_of_le_of_lt hab hlt))
        rw [← hTR, ← hheads u hu]
        exact hreg.heads_from_firstInterior adm hcom hbelow hopen hshor u hu
      · obtain ⟨Db, Kb, hfg, hDb, hsrc, hDbh, hKb, hKerase, hKh, hKD, -⟩ :=
          honestHeightRow_confirmationWitness S adm hb hemit hrowHeight
        have hRK : R = (Protocol.derive_named S.E S.cfg Kb).T_h :=
          Option.some.inj (hW.symm.trans hfg)
        have hDbP : Db.erase = P.erase :=
          hsource b.val_index hb Db.erase (by rw [← hlast]; exact hsrc)
        rw [hRK, ← hDbP]
        exact Block.preceq_trans
          (Proofs.Optimistic.derive_named_T_h_preceq S.E S.cfg Kb) hKD

/-- **earlier's `notLost_of_honestPredecessorOpening_after_SG_healing` over the
clean named base**, with the three healed-lifecycle facts at the honest opening
taken as hypotheses. -/
theorem notLost_of_honestPredecessorOpening_named_after_SG_healing_of_lifecycle
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    (_of_openingHeads : ∀ {m : Round} {P : NamedBlock V},
      fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m →
      S.E.proposer (S.hc.opening_slot m) ∈ rho.honest →
      proposedBlockAt S rho (S.hc.opening_slot m) = some P →
      Protocol.vote_time S.E (S.hc.opening_slot m) ≤ rho.horizon →
      ∀ v ∈ rho.honest, voterHeadAt S rho v (S.hc.opening_slot m) = P.erase)
    (_of_openingCover : ∀ {m : Round} {P : NamedBlock V},
      fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m →
      S.E.proposer (S.hc.opening_slot m) ∈ rho.honest →
      proposedBlockAt S rho (S.hc.opening_slot m) = some P →
      Protocol.confirmation_time S.E (S.hc.opening_slot m) ≤ rho.horizon →
      ActionCarriersCover S rho m P.erase)
    (_of_openingSource : ∀ {m : Round} {P : NamedBlock V},
      fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m →
      S.E.proposer (S.hc.opening_slot m) ∈ rho.honest →
      proposedBlockAt S rho (S.hc.opening_slot m) = some P →
      Protocol.confirmation_time S.E (S.hc.opening_slot m) ≤ rho.horizon →
      ∀ w ∈ rho.honest, ∀ X : Block V,
        actionFGSource S (actionStoreAt S rho w m) = some X → X = P.erase)
    {q : Round}
    (hq : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ q) :
    ∀ r : Round, q + 2 < r →
      S.E.proposer (S.hc.opening_slot (r - 1)) ∈ rho.honest →
      Protocol.confirmation_time S.E (S.hc.opening_slot r + 2) ≤ rho.horizon →
      ¬ LostRoundAt S rho r := by
  classical
  intro r hr hopen hhor
  have hrpos : 0 < r := (Nat.zero_le (q + 2)).trans_lt hr
  have hprev : r - 1 + 1 = r := Nat.sub_add_cancel hrpos
  have hArhor : S.a r ≤ rho.horizon := by
    have hmono : Protocol.confirmation_time S.E (S.hc.opening_slot r) ≤
        Protocol.confirmation_time S.E (S.hc.opening_slot r + 2) := by
      rw [Protocol.confirmation_time_eq_support_cutoff_succ,
        Protocol.confirmation_time_eq_support_cutoff_succ]
      exact support_cutoff_mono S.E (Nat.add_le_add_right (Nat.le_add_right _ 2) 1)
    simpa only [opening_confirmation_time_eq_action] using hmono.trans hhor
  have hqr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ r :=
    le_of_lt (lt_of_le_of_lt (hq.trans (Nat.le_add_right q 2)) hr)
  have hp : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ r - 1 :=
    Nat.le_sub_of_add_le hqr
  obtain ⟨P, hP⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot (r - 1))
  have hactionPrev : S.a (r - 1) ≤ rho.horizon := by
    refine ((action_strictMono S).monotone (Nat.sub_le r 1)).trans hArhor
  have hconfPrev : Protocol.confirmation_time S.E
      (S.hc.opening_slot (r - 1)) ≤ rho.horizon := by
    rw [opening_confirmation_time_eq_action]
    exact hactionPrev
  have hvotePrev : Protocol.vote_time S.E (S.hc.opening_slot (r - 1)) ≤
      rho.horizon :=
    (vote_time_le_confirmation_time S.E _).trans hconfPrev
  have hheads : ∀ v ∈ rho.honest,
      voteDutyHead S rho v (S.hc.opening_slot (r - 1)) = P.erase := by
    intro v hv
    simpa only [Protocol.voteDutyHead] using
      _of_openingHeads hp hopen hP hvotePrev v hv
  have hcover := _of_openingCover hp hopen hP hconfPrev
  have hsource := _of_openingSource hp hopen hP hconfPrev
  rintro ⟨u, hu, w, hw, hbad⟩
  apply hbad
  have hroot := w4FgRoot_preceq_openingProposal_after_SG_healing
    S adm hcom hbelow hrec hdelay hpost hp hheads hsource
      (by simpa only [hprev] using hArhor) hu
  change Block.Preceq
    (Protocol.get_fg_root
      (rho.storeBeforeTime S u (S.a r)).toHealing.toFG)
    (actionSGBlockAt S rho w (r - 1))
  exact Block.preceq_trans (by simpa only [hprev] using hroot) (hcover w hw)

#print axioms w4FgRoot_preceq_openingProposal_after_SG_healing
#print axioms notLost_of_honestPredecessorOpening_named_after_SG_healing_of_lifecycle

/-- Verbatim copy of `MovingChainRoundFloorFor.actionFGSource_some_eq_live`
(`CanonicalActionSourcesRun.lean:137`) with its dead `MovingChainRoundFloorFor`
binder dropped; that module is red. The body reads only the two prepared-frame
inputs, which the healed lifecycle supplies. -/
private theorem w4ActionFGSourceEqLive
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (hrpos : 0 < r) (hhor : S.a r ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest)
    (hanchorAt : Block.Preceq
      (PhaseGrades.nodeAnchor S (actionReadAt S rho v r) r)
      (actionStoreAt S rho v r).live_confirmed)
    (hclearAt : PhaseGrades.nodeClear S (actionReadAt S rho v r) r
      (actionStoreAt S rho v r).live_confirmed = true)
    {X : Block V}
    (hsource : actionFGSource S (actionReadAt S rho v r) = some X) :
    X = (actionStoreAt S rho v r).live_confirmed := by
  have hround : S.hc.round_of (actionReadAt S rho v r).st.core.toHealing.s = r := by
    simpa only [actionStoreAt, Protocol.Store.toHealing] using
      actionStoreAt_round S rho v r
  have hsource' : PhaseGrades.nodeFGSource S (actionReadAt S rho v r) r = some X := by
    simpa only [actionFGSource, PhaseGrades.nodeFGSource, hround] using hsource
  cases hA : PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r with
  | none =>
      have hQ2 : Protocol.grade2_block_with
          (NamedProfile.gradeContract (actionReadAt S rho v r).cache) S.E S.hc
          (actionReadAt S rho v r).st.core.toHealing r = none := hA
      rw [PhaseGrades.nodeFGSource, Protocol.fg_source_with.eq_def, hQ2] at hsource'
      simp only [reduceCtorEq] at hsource'
  | some A =>
      have hQ2 : Protocol.grade2_block_with
          (NamedProfile.gradeContract (actionReadAt S rho v r).cache) S.E S.hc
          (actionReadAt S rho v r).st.core.toHealing r = some A := hA
      have hAlive : Block.Preceq A (actionStoreAt S rho v r).live_confirmed :=
        Block.preceq_trans
          (actionQ2_preceq_actionAnchor S adm.toNamedAdmissibleCore hv hrpos hhor hA)
          hanchorAt
      have hwalk : Protocol.deepest_clear (some A)
          (actionReadAt S rho v r).st.core.toHealing.live_confirmed
          ((NamedProfile.gradeContract (actionReadAt S rho v r).cache).read S.E S.hc
            (actionReadAt S rho v r).st.core.toHealing r).clear =
          some (actionStoreAt S rho v r).live_confirmed :=
        deepest_clear_eq_tip (by simpa using hAlive) hclearAt
      rw [PhaseGrades.nodeFGSource, Protocol.fg_source_with.eq_def, hQ2] at hsource'
      simp only [hwalk, Option.some.injEq] at hsource'
      exact hsource'.symm


/-- **earlier's `notLost_of_honestPredecessorOpening_after_SG_healing`
(`NonLostAfterHonestOpeningRun.lean:163`) over the clean named base.**

This is the non-lostness conjunct of the corresponding branch's recovery-spine export. -/
theorem notLost_of_honestPredecessorOpening_named_after_SG_healing
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {q : Round}
    (hq : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ q) :
    ∀ r : Round, q + 2 < r →
      S.E.proposer (S.hc.opening_slot (r - 1)) ∈ rho.honest →
      Protocol.confirmation_time S.E (S.hc.opening_slot r + 2) ≤ rho.horizon →
      ¬ LostRoundAt S rho r := by
  refine notLost_of_honestPredecessorOpening_named_after_SG_healing_of_lifecycle
    S adm hcom hbelow hrec hdelay hpost ?_ ?_ ?_ hq
  · intro m P hm hopening hP hvoteHor
    exact honestProposal_voterHeadAt_eq_after_SG_healing_named_of_openingProposer
      S adm hcom hbelow hrec hdelay hpost hm hvoteHor hopening hP
  · intro m P hm hopening hP hconfHor v hv
    rw [(honestProposal_actionSelectors_after_SG_healing_named_of_openingProposer
      S adm hcom hbelow hrec hdelay hpost hm hopening hP hconfHor v hv).1]
    exact Block.preceq_self _
  · intro m P hm hopening hP hconfHor w hw X hX
    obtain ⟨-, hanchor, hclear⟩ :=
      honestProposal_actionSelectors_after_SG_healing_named_of_openingProposer
        S adm hcom hbelow hrec hdelay hpost hm hopening hP hconfHor w hw
    have hlive : (actionStoreAt S rho w m).live_confirmed = P.erase :=
      honestProposal_liveConfirmed_at_action_after_SG_healing_named_of_openingProposer
        S adm hcom hbelow hrec hdelay hpost hm hopening hP hconfHor w hw
    have hmPos : 0 < m :=
      lt_of_lt_of_le (by decide : 0 < 2)
        ((Nat.le_add_left 2 (fgSafetyProgressDeadline S rho rGST gap delayExtra)).trans hm)
    have hactionHor : S.a m ≤ rho.horizon := by
      simpa only [opening_confirmation_time_eq_action] using hconfHor
    have hres := w4ActionFGSourceEqLive S adm hmPos hactionHor hw
      (by rw [hlive]; exact hanchor) (by rw [hlive]; exact hclear) hX
    rw [hres, hlive]

#print axioms notLost_of_honestPredecessorOpening_named_after_SG_healing

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
