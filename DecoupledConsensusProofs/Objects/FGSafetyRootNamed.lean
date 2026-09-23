module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.FGSafetyRoot
public import DecoupledConsensusProofs.Protocol.ChainState.HeightRegimeNamedBaseDeadline
public import DecoupledConsensusProofs.Execution.HeightRegimeNamedRunAbove

@[expose] public section

/-!
# Named FG roots after the safety deadline

This is the run-scoped named proof of the post-deadline FG-root facts.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface
open Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

private theorem runBlock_of_mem_storeBeforeTime
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {t : Time} {D : NamedBlock V}
    (hD : D ∈ (rho.storeBeforeTime S w t).bodies) : RunBlock S rho D := by
  obtain ⟨n, hn, -⟩ :=
    Proofs.Bridges.stateBeforeTime_eq_stateBefore S adm.toNamedScheduleWellFormed t
  have hD' : D ∈ (rho.stateBefore S n w).st.bodies := by
    simpa only [Run.storeBeforeTime, hn] using hD
  exact Proofs.Bridges.runBlock_of_stateBefore_mem S hw hD'

private theorem NamedHeightRegimeRun.sgHistory_run
    {S : Setup V} {rho : Run V} {r0 : Round} {blocked : Height}
    {first i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (h : NamedHeightRegimeRun S rho r0 blocked first i a ta
      Cfg T Tprev c0)
    {c : Round} (hc : a.round ≤ c) (hhor : S.a c ≤ rho.horizon) :
    HonestSGEmissionsCompatibleAtRound S rho c T.erase := by
  rcases eq_or_lt_of_le hc with rfl | hlt
  · exact h.seed.sgEmissionsCompatible_of_source_of_frame_named
      adm hcom hbelow h.crossing h.frame h.c0le h.ready h.postPrev
  · exact ((h.laterHistory_main adm hcom hbelow
      (Nat.succ_le_of_lt hlt)).2 hhor).1

private theorem NamedHeightRegimeRun.fgRoot_compatible_after_source_run
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

namespace NamedHeightRegimeBaseRun

variable {S : Setup V} {rho : Run V} {r0 : Round} {blocked : Height}
  {first : Nat} {Tprev : NamedBlock V}

/-- The source of the base occurs no later than a deadline containing the
base crossing. -/
theorem exists_regime_before_deadline (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (h : NamedHeightRegimeBaseRun S rho r0 blocked first Tprev)
    {deadline : Round} (hdeadline : first ≤ inclusiveEventIndex rho (S.a deadline)) :
    ∃ (i : Nat) (a : NamedAttestation V) (ta : Time)
      (Cfg T : NamedBlock V),
      NamedHeightRegimeRun S rho r0 blocked first i a ta
        Cfg T Tprev a.round ∧ a.round ≤ deadline := by
  obtain ⟨i, a, ta, Cfg, T, hreg⟩ :=
    h.exists_regime_closed adm hbelow hgst
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
  apply (action_strictMono S).le_iff_le.mp
  simpa only [Event.time, hreg.seed.actionTime_eq, decide_eq_true_eq] using
    (List.mem_filter.mp hmem).2

/-- From the base deadline through the next action, an honest reader's
FG root is compatible with every honest SG vote of round `c`. -/
theorem fgRoot_compatible_actionSGBlock_at_read_after_deadline
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (h : NamedHeightRegimeBaseRun S rho r0 blocked first Tprev)
    {deadline : Round} (hdeadline : first ≤ inclusiveEventIndex rho (S.a deadline))
    {c : Round} (hc : deadline ≤ c) (hhor : S.a c ≤ rho.horizon)
    {read : Time} (hread : S.a deadline ≤ read)
    (hreadHor : read ≤ rho.horizon) (hnext : read ≤ S.a (c + 1))
    {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest) :
    Block.compatible
      (Protocol.get_fg_root
        (rho.storeBeforeTime S u read).toHealing.toFG)
      (actionSGBlockAt S rho v c) = true := by
  let R := Protocol.get_fg_root
    (rho.storeBeforeTime S u read).toHealing.toFG
  change Block.compatible R (actionSGBlockAt S rho v c) = true
  rcases fgRoot_confirmationWitness_at_read S adm.toNamedAdmissibleCore
      (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow)
      hu read with
    hgen | ⟨C, hC, hJ, b, tb, hb, hemit, hbt, hpair, hW⟩
  · rw [show R = Block.genesis from hgen]
    simp [Block.compatible, Protocol.preceq_genesis]
  · by_cases hsmall :
        (Protocol.derive_named S.E S.cfg C).h_j ≤ blocked
    · obtain ⟨i, a, ta, Cfg, T, hreg, ha⟩ :=
        h.exists_regime_before_deadline adm hbelow hgst hdeadline
      have hac : a.round ≤ c := ha.trans hc
      have hRT : Block.compatible R T.erase = true := by
        simpa only [R] using hreg.fgRoot_compatible_after_source_run
          adm hcom hbelow (((action_strictMono S).monotone ha).trans hread)
            hreadHor hu
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
            runBlock_of_mem_storeBeforeTime S adm hu hC
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
      have hSG := hreg.sgHistory_run adm hcom hbelow hac hhor
        v hv (honest_emits_exact_actionAttestationAt S adm hv c hhor
          (hreg.postPrev.trans (Assembly.a_mono S
            ((Nat.sub_le a.round 1).trans hac))))
      rcases (show Block.Preceq (actionSGBlockAt S rho v c) T.erase ∨
          Block.Preceq T.erase (actionSGBlockAt S rho v c) by
        simpa only [Block.compatible, Bool.or_eq_true] using hSG) with
        hBT | hTB
      · exact Block.compatible_of_preceq_common hRTpre hBT
      · simp only [Block.compatible, Bool.or_eq_true]
        exact Or.inl (Block.preceq_trans hRTpre hTB)
    · let n := (Protocol.derive_named S.E S.cfg C).h_j -
          (blocked + 1)
      have heq : blocked + n + 1 =
          (Protocol.derive_named S.E S.cfg C).h_j := by
        calc
          _ = n + (blocked + 1) := by ac_rfl
          _ = (Protocol.derive_named S.E S.cfg C).h_j :=
            Nat.sub_add_cancel (Nat.lt_of_not_ge hsmall)
      have hrow : b.height_pair.erase.height? =
          some (blocked + n + 1) := by
        rw [hpair]
        exact congrArg some heq.symm
      obtain ⟨first_n, i, a, ta, Cfg, T, Tprev', c0, hreg⟩ :=
        h.exists_regime_of_row_named adm hcom hbelow hgst n hb hemit hrow
      have hTR : T.erase = R := Option.some.inj
        ((hreg.witness_eq adm hcom hbelow hb hemit hrow).symm.trans hW)
      have hbc : b.round ≤ c := by
        have hact : S.a b.round < S.a (c + 1) := by
          simpa only [(Proofs.Optimistic.emits_attest_shape S hemit).2] using
            hbt.trans_le hnext
        exact Nat.le_of_lt_succ ((action_strictMono S).lt_iff_lt.mp hact)
      have hac : a.round ≤ c :=
        (hreg.minimal b tb hb hemit hrow).trans hbc
      have hSG := hreg.sgHistory_run adm hcom hbelow hac hhor
        v hv (honest_emits_exact_actionAttestationAt S adm hv c hhor
          (hreg.postPrev.trans (Assembly.a_mono S
            ((Nat.sub_le a.round 1).trans hac))))
      simpa only [hTR, Block.compatible, Bool.or_comm] using hSG

/-- After the base deadline, each honest reader's action FG root is
compatible with every honest SG vote of that round. -/
theorem fgRoot_compatible_actionSGBlock_after_deadline
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (h : NamedHeightRegimeBaseRun S rho r0 blocked first Tprev)
    {deadline : Round} (hdeadline : first ≤ inclusiveEventIndex rho (S.a deadline))
    {c : Round} (hc : deadline ≤ c) (hhor : S.a c ≤ rho.horizon)
    {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest) :
    Block.compatible
      (Protocol.get_fg_root (actionStoreAt S rho u c).toHealing.toFG)
      (actionSGBlockAt S rho v c) = true := by
  rw [actionStoreAt_fgRoot_eq_storeBeforeTime]
  exact h.fgRoot_compatible_actionSGBlock_at_read_after_deadline
    adm hcom hbelow hgst hdeadline hc hhor
      ((action_strictMono S).monotone hc) hhor
      ((action_strictMono S).monotone (Nat.le_succ c)) hu hv

/-- Through the strict confirmation read, the FG root is below each honest
head of the confirmed slot. -/
theorem fgRoot_preceq_previousHead_through_confirmation_after_deadline
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (h : NamedHeightRegimeBaseRun S rho r0 blocked first Tprev)
    {deadline : Round} (hdeadline : first ≤ inclusiveEventIndex rho (S.a deadline))
    {read : Time} (hread : S.a deadline ≤ read) (hhor : read ≤ rho.horizon)
    {s : Slot} (hs : S.hc.opening_slot deadline + 1 ≤ s)
    (hnext : read ≤ Protocol.confirmation_time S.E s)
    (hshor : Protocol.vote_time S.E s + S.E.Δ ≤ rho.horizon)
    {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest) :
    Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S u read).toHealing.toFG)
      (voteDutyHead S rho v s) := by
  let R := Protocol.get_fg_root
    (rho.storeBeforeTime S u read).toHealing.toFG
  change Block.Preceq R (voteDutyHead S rho v s)
  rcases fgRoot_confirmationWitness_at_read S adm.toNamedAdmissibleCore
      (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow)
      hu read with
    hgen | ⟨C, hC, hJ, b, tb, hb, hemit, hbt, hpair, hW⟩
  · rw [show R = Block.genesis from hgen]
    exact Protocol.preceq_genesis _
  · by_cases hsmall :
        (Protocol.derive_named S.E S.cfg C).h_j ≤ blocked
    · obtain ⟨i, a, ta, Cfg, T, hreg, ha⟩ :=
        h.exists_regime_before_deadline adm hbelow hgst hdeadline
      have hRT := hreg.fgRoot_compatible_after_source_run adm hcom hbelow
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
            runBlock_of_mem_storeBeforeTime S adm hu hC
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
      have hopen : S.hc.opening_slot a.round ≤
          S.hc.opening_slot deadline := Nat.mul_le_mul_right S.hc.R ha
      exact Block.preceq_trans hRTpre
        (hreg.heads_from_firstInterior adm hcom hbelow
          ((Nat.add_le_add_right hopen 1).trans hs) hshor v hv)
    · let n := (Protocol.derive_named S.E S.cfg C).h_j -
          (blocked + 1)
      have heq : blocked + n + 1 =
          (Protocol.derive_named S.E S.cfg C).h_j := by
        calc
          _ = n + (blocked + 1) := by ac_rfl
          _ = (Protocol.derive_named S.E S.cfg C).h_j :=
            Nat.sub_add_cancel (Nat.lt_of_not_ge hsmall)
      have hrow : b.height_pair.erase.height? =
          some (blocked + n + 1) := by
        rw [hpair]
        exact congrArg some heq.symm
      obtain ⟨first_n, i, a, ta, Cfg, T, Tprev', c0, hreg⟩ :=
        h.exists_regime_of_row_named adm hcom hbelow hgst n hb hemit hrow
      have hTR : T.erase = R := Option.some.inj
        ((hreg.witness_eq adm hcom hbelow hb hemit hrow).symm.trans hW)
      have hact : S.a b.round < read := by
        simpa only [(Proofs.Optimistic.emits_attest_shape S hemit).2] using hbt
      have hbs := firstInterior_le_of_action_lt_confirmation S
        (hact.trans_le hnext)
      have hab : a.round ≤ b.round := hreg.minimal b tb hb hemit hrow
      have hopen : S.hc.opening_slot a.round + 1 ≤ s :=
        (Nat.add_le_add_right
          (Nat.mul_le_mul_right S.hc.R hab) 1).trans hbs
      rw [← hTR]
      exact hreg.heads_from_firstInterior adm hcom hbelow
        hopen hshor v hv

/-- The earlier vote-bounded interface is unchanged. -/
theorem fgRoot_preceq_previousHead_after_deadline
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (h : NamedHeightRegimeBaseRun S rho r0 blocked first Tprev)
    {deadline : Round} (hdeadline : first ≤ inclusiveEventIndex rho (S.a deadline))
    {read : Time} (hread : S.a deadline ≤ read) (hhor : read ≤ rho.horizon)
    {s : Slot} (hs : S.hc.opening_slot deadline + 1 ≤ s)
    (hnext : read ≤ Protocol.vote_time S.E (s + 1))
    (hshor : Protocol.vote_time S.E s + S.E.Δ ≤ rho.horizon)
    {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest) :
    Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S u read).toHealing.toFG)
      (voteDutyHead S rho v s) := by
  have hbound : Protocol.vote_time S.E (s + 1) ≤
      Protocol.confirmation_time S.E s := by
    rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
    exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
  exact h.fgRoot_preceq_previousHead_through_confirmation_after_deadline
    adm hcom hbelow hgst hdeadline hread hhor hs
      (hnext.trans hbound) hshor hu hv

end NamedHeightRegimeBaseRun


/-- Every honest SG vote after the deadline is compatible with honest FG
roots at all reads through the next action. -/
theorem fgRoot_compatible_actionSGBlock_at_read_after_GST
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {c : Round} (hc : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ c)
    (hhor : S.a c ≤ rho.horizon)
    {read : Time} (hread : S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) ≤ read)
    (hreadHor : read ≤ rho.horizon) (hnext : read ≤ S.a (c + 1))
    {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest) :
    Block.compatible (Protocol.get_fg_root
      (rho.storeBeforeTime S u read).toHealing.toFG) (actionSGBlockAt S rho v c) = true := by
  obtain ⟨blocked, first, Tprev, hfirst, hbase⟩ :=
    exists_namedHeightRegimeBaseRun_before_fgSafetyProgressDeadline
      S adm hcom hbelow hrec hdelay hpost (hread.trans hreadHor)
  exact hbase.fgRoot_compatible_actionSGBlock_at_read_after_deadline
    adm hcom hbelow (gstLagged_le_Γ_neg1_of_gst_le_a S rGST hpost)
      hfirst hc hhor hread hreadHor hnext hu hv

/-- After the bounded bootstrap, an honest FG root at a read before the
next vote lies below every preceding honest Goldfish head. -/
theorem fgRoot_preceq_previousHead_after_GST
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {read : Time} (hread : S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) ≤ read)
    (hhor : read ≤ rho.horizon)
    {s : Slot} (hs : S.hc.opening_slot (fgSafetyProgressDeadline S rho rGST gap delayExtra) + 1 ≤ s)
    (hnext : read ≤ Protocol.vote_time S.E (s + 1))
    (hshor : Protocol.vote_time S.E s + S.E.Δ ≤ rho.horizon)
    {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest) :
    Block.Preceq (Protocol.get_fg_root (rho.storeBeforeTime S u read).toHealing.toFG)
      (voteDutyHead S rho v s) := by
  obtain ⟨blocked, first, Tprev, hfirst, hbase⟩ :=
    exists_namedHeightRegimeBaseRun_before_fgSafetyProgressDeadline
      S adm hcom hbelow hrec hdelay hpost (hread.trans hhor)
  exact hbase.fgRoot_preceq_previousHead_after_deadline
    adm hcom hbelow (gstLagged_le_Γ_neg1_of_gst_le_a S rGST hpost)
      hfirst hread hhor hs hnext hshor hu hv

/-- FG roots through the strict confirmation read remain below the earlier
honest vote heads. -/
theorem fgRoot_preceq_previousHead_through_confirmation_after_GST
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {read : Time} (hread : S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) ≤ read)
    (hhor : read ≤ rho.horizon)
    {s : Slot} (hs : S.hc.opening_slot (fgSafetyProgressDeadline S rho rGST gap delayExtra) + 1 ≤ s)
    (hnext : read ≤ Protocol.confirmation_time S.E s)
    (hshor : Protocol.vote_time S.E s + S.E.Δ ≤ rho.horizon)
    {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest) :
    Block.Preceq (Protocol.get_fg_root (rho.storeBeforeTime S u read).toHealing.toFG)
      (voteDutyHead S rho v s) := by
  obtain ⟨blocked, first, Tprev, hfirst, hbase⟩ :=
    exists_namedHeightRegimeBaseRun_before_fgSafetyProgressDeadline
      S adm hcom hbelow hrec hdelay hpost (hread.trans hhor)
  exact hbase.fgRoot_preceq_previousHead_through_confirmation_after_deadline
    adm hcom hbelow (gstLagged_le_Γ_neg1_of_gst_le_a S rGST hpost)
      hfirst hread hhor hs hnext hshor hu hv


#print axioms NamedHeightRegimeBaseRun.exists_regime_before_deadline
#print axioms NamedHeightRegimeBaseRun.fgRoot_compatible_actionSGBlock_at_read_after_deadline
#print axioms NamedHeightRegimeBaseRun.fgRoot_compatible_actionSGBlock_after_deadline
#print axioms NamedHeightRegimeBaseRun.fgRoot_preceq_previousHead_through_confirmation_after_deadline
#print axioms NamedHeightRegimeBaseRun.fgRoot_preceq_previousHead_after_deadline
#print axioms fgRoot_compatible_actionSGBlock_at_read_after_GST
#print axioms fgRoot_preceq_previousHead_after_GST
#print axioms fgRoot_preceq_previousHead_through_confirmation_after_GST

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
