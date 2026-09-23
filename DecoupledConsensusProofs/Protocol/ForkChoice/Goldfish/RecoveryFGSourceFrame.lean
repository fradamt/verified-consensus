module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.RecoveryFirstFGCone
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoverySelectedG2PrefixCone
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedEntryCanonical
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FGWitnessCandidate
public import DecoupledConsensusProofs.Protocol.Grades.GateOffWindowCone
public import DecoupledConsensusProofs.Objects.FGConfirmationHistory
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.WeakBootstrapJoin
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightRegimeFrame

@[expose] public section

/-!
# The common recovery frame from an actual FG source

Both FG source cases deliver the exact source block to every honest reader
before the action. Before the first global height crossing, its presence
forces each reader's frontier to the source height. The recovery condition
also gives the strict justification gap. The common-height frame used by
the SG safety window is therefore a conclusion, not an input.

This does not assert that the interval before the crossing lasts for a full
SG bootstrap window, or that the deeper FG witness is already protected.

The `RawExactHeightSeedRun` object is now present. The named source frame and
round-local relative-grade consumer chain are live. The pre-rewrite
declarations stay byte-exact in the comment below.

```text
error: Application type mismatch: The argument
  a
has type
  CombinedAttestation V
but is expected to have type
  NamedAttestation ?m
```
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.NamedRecoveryRead

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Named source frame -/

private theorem justification_gap_from_frontier_named {j H : Nat}
    (hlt : j < H + 1) (hne : j ≠ H) : j + 2 ≤ H + 1 := by
  omega

/-- K6 moves the exact named source body to every honest action read. -/
theorem PrefixFGSelectorConeAt.sourceMem_at_action
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {start stop : Nat} {blocked hF0 : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start stop blocked i a ta Cfg T)
    (hcap : HonestPrefixFinalityCap S rho stop hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (ready : GradeRoundReady S rho a.round)
    (hK6Q2 : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase →
      VoterAnchorSourceQ2Inputs S rho a.round a.val_index Cfg.erase)
    (hK6Clear : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round ≠ some Cfg.erase →
      VoterAnchorSourceClearInputs S rho a.round a.val_index Cfg.erase)
    {w : V} (hw : w ∈ rho.honest) :
    Cfg ∈ (actionStoreAt S rho w a.round).st.bodies := by
  by_cases hselected : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase
  · exact actionBody_at_action_of_openingVoteFiltered
      S adm hseed.signerHonest hseed.sourceMem hw
        ((hK6Q2 hselected).openingTarget w hw)
  · exact actionBody_at_action_of_nextVoteFiltered
      S adm hseed.signerHonest hseed.sourceMem hw
        ((hK6Clear hselected).nextTarget w hw)

/-- The exact named source body reaches every honest action read without K6.
The selected-Q2 arm uses its captured G2 source, and the genuine-clear arm
uses the delivered opening confirmation ancestor. -/
theorem PrefixFGSelectorConeAt.sourceMem_at_action_k6free
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {start stop : Nat} {blocked hF0 : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start stop blocked i a ta Cfg T)
    (hcap : HonestPrefixFinalityCap S rho stop hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (ready : GradeRoundReady S rho a.round)
    {w : V} (hw : w ∈ rho.honest) :
    Cfg ∈ (actionStoreAt S rho w a.round).st.bodies := by
  have hactionPrefix : strictEventIndex rho (S.a a.round) ≤ stop :=
    Nat.le_of_lt (hseed.actionPrefix_lt adm.toNamedScheduleWellFormed)
  have hactionHor : S.a a.round ≤ rho.horizon := hseed.actionHorizon adm
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
  · obtain ⟨C, hgenuine, -, -, -, hCfgC⟩ := hgenuine
    have hvoteBody := ancestorGenuineConfirmation_body_at_nextVote_of_floor
      S adm ready hseed.signerHonest hgenuine hCfgC hseed.sourceMem
        (finalityFloorAt_of_recovery S adm hbelow hcap hrec)
        hseed.sourceDerivedHeight (Protocol.preceq_genesis Cfg.erase)
        hactionPrefix hactionHor hw
    let vote := Protocol.vote_time S.E (S.hc.opening_slot a.round + 1)
    have hvotePre : Cfg ∈
        (NamedRun.stateBeforeTime S rho vote w).st.bodies := by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, Protocol.NamedStore.setClock,
        vote] using hvoteBody
    have heqVote := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedScheduleWellFormed vote) w
    have heqAction := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
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
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hactionPre
  · have hselectedCfg : PhaseGrades.nodeQ2
        S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase := by
      simpa only [hselected] using hQ
    exact (selectedQ2_body_at_action_and_openingVote_of_floor
      S adm ready hseed.signerHonest hselectedCfg hseed.sourceMem
        (finalityFloorAt_of_recovery S adm hbelow hcap hrec)
        hseed.sourceDerivedHeight (Protocol.preceq_genesis Cfg.erase)
        hactionPrefix hw).1

#print axioms PrefixFGSelectorConeAt.sourceMem_at_action_k6free

/-- Before the first crossing, every honest read has the exact recovery
frontier and the strict justification gap. -/
theorem PrefixFGSelectorConeAt.gateOff_at_read_beforeFirst
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked hF0 : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : FirstHeightProgressAt S rho (blocked + 1) first)
    (hcap : HonestPrefixFinalityCap S rho first hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (ready : GradeRoundReady S rho a.round)
    (hK6Q2 : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase →
      VoterAnchorSourceQ2Inputs S rho a.round a.val_index Cfg.erase)
    (hK6Clear : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round ≠ some Cfg.erase →
      VoterAnchorSourceClearInputs S rho a.round a.val_index Cfg.erase)
    {read : Time} (hread : S.a a.round ≤ read)
    (hbefore : strictEventIndex rho read < first)
    {w : V} (hw : w ∈ rho.honest) :
    (rho.storeBeforeTime S w read).core.h_j + 2 ≤ blocked + 1 ∧
      (rho.storeBeforeTime S w read).core.h_max = blocked + 1 := by
  have hsource := hseed.sourceMem_at_action
    adm hbelow hcap hrec ready hK6Q2 hK6Clear hw
  have hsourcePre : Cfg ∈
      (NamedRun.stateBeforeTime S rho (S.a a.round) w).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hsource
  have heqAction := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedScheduleWellFormed (S.a a.round)) w
  have heqRead := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedScheduleWellFormed read) w
  rw [heqAction] at hsourcePre
  have hbody : Cfg ∈
      (NamedRun.stateBefore S rho (strictEventIndex rho read) w).st.bodies :=
    NamedBodyRetention.stateBefore_bodies_mono S rho w
      (strictEventIndex_mono rho hread) hsourcePre
  have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho
    (strictEventIndex rho read) w).1.1.1
  have hraw : Cfg.erase ∈
      (rho.stateBefore S (strictEventIndex rho read) w).st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hbody
  have hstored :
      ((rho.stateBefore S (strictEventIndex rho read) w).st.core.σ
        Cfg.erase).h = blocked + 1 := by
    rw [Proofs.NamedStoreBridge.derivedView_stateBefore S rho
      (strictEventIndex rho read) w Cfg hbody,
      hseed.sourceDerivedHeight]
  have hfrontier : honestHMaxBeforeIndex S rho
      (strictEventIndex rho read) < blocked + 2 :=
    (hfirst.before _ hbefore).trans_lt
      (Nat.lt_succ_self (blocked + 1))
  have hmax := localHMax_eq_blocked_succ_of_rawMem_of_prefixFrontier
    S adm hfrontier hw (Nat.le_refl _) hraw hstored
  have hmaxCore :
      (rho.stateBefore S (strictEventIndex rho read) w).st.core.h_max =
        blocked + 1 := hmax
  have hcapRead := honestPrefixFinalityCap_of_le
    S adm.toNamedScheduleWellFormed (Nat.le_of_lt hbefore) hcap
  have huniverse := honestPrefixNJUniverse_of_finalityCap
    S adm.toNamedDeliveryWellFormed hcapRead hrec
  have hne :
      (rho.stateBefore S (strictEventIndex rho read) w).st.core.h_j ≠
        blocked := by
    obtain ⟨D, hD, -, hDhj⟩ :=
      Proofs.Bridges.storeJustificationOnChain_stateBefore
        S rho (strictEventIndex rho read) w
    have hneD := (huniverse w hw D hD).2
    intro heq
    apply hneD
    exact hDhj.trans heq
  have hjlt := NamedJustificationBound.justificationBelowMax_stateBefore
    S rho (strictEventIndex rho read) w
  have hjlt' :
      (rho.stateBefore S (strictEventIndex rho read) w).st.core.h_j <
        blocked + 1 := by
    change (rho.stateBefore S (strictEventIndex rho read) w).st.core.h_j <
      (rho.stateBefore S (strictEventIndex rho read) w).st.core.h_max at hjlt
    rw [hmaxCore] at hjlt
    exact hjlt
  have hgap :
      (rho.stateBefore S (strictEventIndex rho read) w).st.core.h_j + 2 ≤
        blocked + 1 :=
    justification_gap_from_frontier_named
      hjlt' hne
  change
    (NamedRun.stateBeforeTime S rho read w).st.core.h_j + 2 ≤
        blocked + 1 ∧
      (NamedRun.stateBeforeTime S rho read w).st.core.h_max = blocked + 1
  rw [heqRead]
  exact ⟨hgap, hmax⟩

/-- The finite named gate-off frame from the first-crossing prefix. -/
theorem PrefixFGSelectorConeAt.gateOffFrame_beforeFirst
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked hF0 : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : FirstHeightProgressAt S rho (blocked + 1) first)
    (hcap : HonestPrefixFinalityCap S rho first hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (ready : GradeRoundReady S rho a.round)
    (hK6Q2 : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase →
      VoterAnchorSourceQ2Inputs S rho a.round a.val_index Cfg.erase)
    (hK6Clear : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round ≠ some Cfg.erase →
      VoterAnchorSourceClearInputs S rho a.round a.val_index Cfg.erase)
    {lo hi : Round} (hlo : a.round ≤ lo)
    (hhi : strictEventIndex rho (S.a hi) < first) :
    NamedGateOffFrameAt S rho (blocked + 1) lo hi := by
  intro read hreadLo hreadHi w hw
  exact hseed.gateOff_at_read_beforeFirst
    adm hbelow hfirst hcap hrec ready hK6Q2 hK6Clear
      ((Assembly.a_mono S hlo).trans hreadLo)
      ((strictEventIndex_mono rho hreadHi).trans_lt hhi) hw

/-- The frame variant needs no erased `HeightRegimeFrame.sourceAbove`: K6
already carries the exact named source to every honest action read. -/
theorem PrefixFGSelectorConeAt.sourceMem_at_action_of_frame
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {start stop : Nat} {blocked : Height} {Tprev : Block V} {c0 : Round}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start stop blocked i a ta Cfg T)
    (hframe : HeightRegimeFrame S rho blocked (stop - 1) Tprev c0)
    (ready : GradeRoundReady S rho a.round)
    (hK6Q2 : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase →
      VoterAnchorSourceQ2Inputs S rho a.round a.val_index Cfg.erase)
    (hK6Clear : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round ≠ some Cfg.erase →
      VoterAnchorSourceClearInputs S rho a.round a.val_index Cfg.erase)
    {w : V} (hw : w ∈ rho.honest) :
    Cfg ∈ (actionStoreAt S rho w a.round).st.bodies := by
  by_cases hselected : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase
  · exact actionBody_at_action_of_openingVoteFiltered
      S adm hseed.signerHonest hseed.sourceMem hw
        ((hK6Q2 hselected).openingTarget w hw)
  · exact actionBody_at_action_of_nextVoteFiltered
      S adm hseed.signerHonest hseed.sourceMem hw
        ((hK6Clear hselected).nextTarget w hw)

/-- The named source clause of the regime frame applies directly to the
retained selector witness. No erased derivation is reconstructed. -/
theorem PrefixFGSelectorConeAt.prev_preceq_source_of_frame
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {start stop : Nat} {blocked : Height} {Tprev : Block V} {c0 : Round}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start stop blocked i a ta Cfg T)
    (hframe : HeightRegimeFrame S rho blocked (stop - 1) Tprev c0) :
    Block.Preceq Tprev Cfg.erase := by
  apply hframe.namedSourceAbove a.val_index hseed.signerHonest a.round
    (Nat.le_sub_one_of_lt (hseed.actionPrefix_lt adm.toNamedScheduleWellFormed))
    (hseed.actionHorizon adm) Cfg hseed.sourceMem hseed.exactFGSource
      hseed.sourceDerivedHeight

/-! The same source helpers over the additive named-predecessor frame. -/

/-- The named source body remains available at every honest action read from a
named-predecessor frame. -/
theorem PrefixFGSelectorConeAt.sourceMem_at_action_of_frameN
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {start stop : Nat} {blocked : Height} {Tprev : NamedBlock V} {c0 : Round}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start stop blocked i a ta Cfg T)
    (hframe : HeightRegimeFrameN S rho blocked (stop - 1) Tprev c0)
    (ready : GradeRoundReady S rho a.round)
    (hK6Q2 : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase →
      VoterAnchorSourceQ2Inputs S rho a.round a.val_index Cfg.erase)
    (hK6Clear : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round ≠ some Cfg.erase →
      VoterAnchorSourceClearInputs S rho a.round a.val_index Cfg.erase)
    {w : V} (hw : w ∈ rho.honest) :
    Cfg ∈ (actionStoreAt S rho w a.round).st.bodies := by
  by_cases hselected : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase
  · exact actionBody_at_action_of_openingVoteFiltered
      S adm hseed.signerHonest hseed.sourceMem hw
        ((hK6Q2 hselected).openingTarget w hw)
  · exact actionBody_at_action_of_nextVoteFiltered
      S adm hseed.signerHonest hseed.sourceMem hw
        ((hK6Clear hselected).nextTarget w hw)

/-- K6-free source delivery from the additive named-predecessor frame. -/
theorem PrefixFGSelectorConeAt.sourceMem_at_action_of_frameN_k6free
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {start stop : Nat} {blocked : Height}
    {Tprev : NamedBlock V} {c0 : Round}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start stop blocked i a ta Cfg T)
    (hframe : HeightRegimeFrameN S rho blocked (stop - 1) Tprev c0)
    (ready : GradeRoundReady S rho a.round)
    {w : V} (hw : w ∈ rho.honest) :
    Cfg ∈ (actionStoreAt S rho w a.round).st.bodies := by
  have hactionPrefix : strictEventIndex rho (S.a a.round) ≤ stop - 1 :=
    Nat.le_sub_one_of_lt
      (hseed.actionPrefix_lt adm.toNamedScheduleWellFormed)
  have hactionHor : S.a a.round ≤ rho.horizon := hseed.actionHorizon adm
  have hTprevCfg : Block.Preceq Tprev.erase Cfg.erase :=
    hframe.namedSourceAbove a.val_index hseed.signerHonest a.round
      hactionPrefix hactionHor Cfg hseed.sourceMem hseed.exactFGSource
        hseed.sourceDerivedHeight
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
  · obtain ⟨C, hgenuine, -, -, -, hCfgC⟩ := hgenuine
    have hvoteBody := ancestorGenuineConfirmation_body_at_nextVote_of_floor
      S adm ready hseed.signerHonest hgenuine hCfgC hseed.sourceMem
        hframe.floor hseed.sourceDerivedHeight
        hTprevCfg
        hactionPrefix hactionHor hw
    let vote := Protocol.vote_time S.E (S.hc.opening_slot a.round + 1)
    have hvotePre : Cfg ∈
        (NamedRun.stateBeforeTime S rho vote w).st.bodies := by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, Protocol.NamedStore.setClock,
        vote] using hvoteBody
    have heqVote := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedScheduleWellFormed vote) w
    have heqAction := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
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
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hactionPre
  · have hselectedCfg : PhaseGrades.nodeQ2
        S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase := by
      simpa only [hselected] using hQ
    exact (selectedQ2_body_at_action_and_openingVote_of_floor
      S adm ready hseed.signerHonest hselectedCfg hseed.sourceMem
        hframe.floor hseed.sourceDerivedHeight
        hTprevCfg
        hactionPrefix hw).1

#print axioms PrefixFGSelectorConeAt.sourceMem_at_action_of_frameN_k6free

/-- The named source clause of an additive frame orders the source body below
the retained predecessor. -/
theorem PrefixFGSelectorConeAt.prev_preceq_source_of_frameN
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {start stop : Nat} {blocked : Height} {Tprev : NamedBlock V} {c0 : Round}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start stop blocked i a ta Cfg T)
    (hframe : HeightRegimeFrameN S rho blocked (stop - 1) Tprev c0) :
    Block.Preceq Tprev.erase Cfg.erase := by
  apply hframe.namedSourceAbove a.val_index hseed.signerHonest a.round
    (Nat.le_sub_one_of_lt (hseed.actionPrefix_lt adm.toNamedScheduleWellFormed))
    (hseed.actionHorizon adm) Cfg hseed.sourceMem hseed.exactFGSource
      hseed.sourceDerivedHeight

#print axioms PrefixFGSelectorConeAt.sourceMem_at_action
#print axioms PrefixFGSelectorConeAt.gateOff_at_read_beforeFirst
#print axioms PrefixFGSelectorConeAt.gateOffFrame_beforeFirst
#print axioms PrefixFGSelectorConeAt.sourceMem_at_action_of_frame
#print axioms PrefixFGSelectorConeAt.prev_preceq_source_of_frame
#print axioms PrefixFGSelectorConeAt.sourceMem_at_action_of_frameN
#print axioms PrefixFGSelectorConeAt.prev_preceq_source_of_frameN


/-- The actual source tick supplies the action horizon, and its event-prefix
position supplies the post-GST round bound. open is not an extra input
when the seed starts at the chosen post-GST cutoff. -/
theorem PrefixFGSelectorConeAt.ready_of_postGSTStart
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {start stop : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time} {Cfg : NamedBlock V}
    {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start stop blocked i a ta Cfg T)
    {r0 : Round} (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (hstart : strictEventIndex rho (S.a r0) ≤ start) :
    GradeRoundReady S rho a.round := by
  have hhor : S.a a.round ≤ rho.horizon := by
    have hin := (adm.in_horizon (Event.tick a.val_index ta)
      (List.mem_of_getElem? hseed.exactTick)).2
    simpa only [Event.time, hseed.actionTime_eq] using hin
  have hround : r0 ≤ a.round := by
    by_contra hnot
    have htimeLt : ta < S.a r0 := by
      rw [hseed.actionTime_eq]
      exact action_strictMono S (Nat.lt_of_not_ge hnot)
    have htimeLe : S.a r0 ≤ ta :=
      Proofs.Optimistic.le_time_of_index_ge S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
        (hstart.trans hseed.startLeIndex) hseed.exactTick
    exact (not_le_of_gt htimeLt) htimeLe
  exact gradeRoundReady_of_action_horizon S hgst hround hhor

#print axioms PrefixFGSelectorConeAt.ready_of_postGSTStart

/-! ## Relative-grade SG safety -/

/-- Before the first height crossing, a selected Q2 with K6 gives the
round-`c` opening vote cone. Relative grades do not preserve the source Q2
through later rounds, so the previous later-round conclusion is not asserted. -/
theorem PrefixFGSelectorConeAt.sgVotesCone_beforeFirst
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked hF0 : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : FirstHeightProgressAt S rho (blocked + 1) first)
    (hcap : HonestPrefixFinalityCap S rho first hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (ready : GradeRoundReady S rho a.round)
    {c last : Round} (hc : a.round + 1 ≤ c)
    (hlast : c + 1 ≤ last)
    (hhor : S.a (last + 2) ≤ rho.horizon)
    (hbefore : strictEventIndex rho (S.a (last + 2)) < first) :
    ∀ v ∈ rho.honest, ∀ Q,
      PhaseGrades.nodeQ2 S (actionReadAt S rho v c) c = some Q →
      VoterAnchorSourceQ2Inputs S rho c v Q →
      NamedHonestVotesCone S rho (S.hc.opening_slot c)
        (fun X => Block.Preceq Q X) := by
  intro v hv Q hQ hK6
  have hround : a.round ≤ c :=
    (Nat.le_succ a.round).trans hc
  have hcLast : c ≤ last + 2 :=
    ((Nat.le_succ c).trans hlast).trans (Nat.le_add_right last 2)
  have hactionHor : S.a c ≤ rho.horizon :=
    (Assembly.a_mono S hcLast).trans hhor
  have hreadyC : GradeRoundReady S rho c := by
    constructor
    · apply ready.1.trans
      change DecoupledConsensusModel.Protocol.opening S.E S.hc a.round +
          (-5) * S.E.Δ ≤
        DecoupledConsensusModel.Protocol.opening S.E S.hc c + (-5) * S.E.Δ
      exact Int.add_le_add_right
        (Proofs.NamedOutageClosure.opening_mono S hround) _
    · rw [domain_g0_eq_Γ_1]
      exact (le_of_lt
        (Proofs.HealingLemmas.Γ_1_lt_Γ_2 S.hc S.E.Δ_pos c)).trans
          ((Γ_2_le_a S.hc S.E.Δ_pos c).trans hactionHor)
  exact selectedQ2_openingVotesCone
    S adm hbelow (Nat.lt_of_lt_of_le (Nat.succ_pos _) hc)
      hreadyC hv hQ hK6

/-- Either the finite window has crossed the next height, or every selected
Q2 at round `c` that satisfies K6 has the round-`c` opening vote cone. -/
theorem PrefixFGSelectorConeAt.sgVotesCone_or_heightProgress
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked hF0 : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : FirstHeightProgressAt S rho (blocked + 1) first)
    (hcap : HonestPrefixFinalityCap S rho first hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (ready : GradeRoundReady S rho a.round)
    {c last : Round} (hc : a.round + 1 ≤ c)
    (hlast : c + 1 ≤ last)
    (hhor : S.a (last + 2) ≤ rho.horizon) :
    blocked + 2 ≤ honestHMaxBeforeIndex S rho
        (strictEventIndex rho (S.a (last + 2))) ∨
      (∀ v ∈ rho.honest, ∀ Q,
        PhaseGrades.nodeQ2 S (actionReadAt S rho v c) c = some Q →
        VoterAnchorSourceQ2Inputs S rho c v Q →
        NamedHonestVotesCone S rho (S.hc.opening_slot c)
          (fun X => Block.Preceq Q X)) := by
  by_cases hcross : first ≤ strictEventIndex rho (S.a (last + 2))
  · left
    have hmono := honestHMaxBeforeIndex_mono S rho hcross
    rw [hfirst.frontier] at hmono
    exact hmono
  · right
    exact hseed.sgVotesCone_beforeFirst adm hcom hbelow hfirst hcap hrec
      ready hc hlast hhor (Nat.lt_of_not_ge hcross)


#print axioms PrefixFGSelectorConeAt.sgVotesCone_beforeFirst
#print axioms PrefixFGSelectorConeAt.sgVotesCone_or_heightProgress


private theorem named_ancestor_height
    (E : Env V) (cfg : Protocol.HeightConfig)
    {B : NamedBlock V} {H : Height} (hH : 1 ≤ H)
    (hHB : H ≤ (Protocol.derive_named E cfg B).h) :
    ∃ P : NamedBlock V, NamedBlock.Preceq P B ∧
      (Protocol.derive_named E cfg P).h = H := by
  induction B with
  | genesis =>
      have hHle : H ≤ 1 := by
        simpa only [Protocol.derive_named,
          Protocol.ChainState.initial] using hHB
      have hEq : H = 1 := Nat.le_antisymm hHle hH
      subst H
      exact ⟨NamedBlock.genesis, by simp [NamedBlock.Preceq, NamedBlock.preceq], rfl⟩
  | node parent slot root votes support rows proposer ih =>
      by_cases hparent : H ≤
          (Protocol.derive_named E cfg parent).h
      · obtain ⟨P, hPp, hPheight⟩ := ih hparent
        refine ⟨P, ?_, hPheight⟩
        simp only [NamedBlock.Preceq, NamedBlock.preceq,
          Bool.or_eq_true, decide_eq_true_eq]
        exact Or.inr hPp
      · have hparentLt :
            (Protocol.derive_named E cfg parent).h < H :=
          Nat.lt_of_not_ge hparent
        rcases Proofs.NamedEntryHeight.derive_node_height_cases E cfg parent slot root
            votes support rows proposer with hstay | hadvance
        · exfalso
          apply hparent
          rw [← hstay]
          exact hHB
        · have hchildUpper :
              (Protocol.derive_named E cfg
                (.node parent slot root votes support rows proposer)).h ≤ H := by
            rw [hadvance]
            exact Nat.succ_le_iff.mpr hparentLt
          have hchildEq :
              (Protocol.derive_named E cfg
                (.node parent slot root votes support rows proposer)).h = H :=
            Nat.le_antisymm hchildUpper hHB
          exact ⟨.node parent slot root votes support rows proposer,
            by simp [NamedBlock.Preceq, NamedBlock.preceq], hchildEq⟩

private theorem namedAncestorBodyMem {st : Protocol.NamedStore V}
    (hpc : NamedStore.NamedParentClosed st) {A B : NamedBlock V}
    (hB : B ∈ st.bodies) (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
      exact hAB ▸ hB
  | node parent slot root votes support rows proposer ih =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq,
        Bool.or_eq_true, decide_eq_true_eq] at hAB
      rcases hAB with rfl | hparent
      · exact hB
      · exact ih (hpc.2 _ hB) hparent

/-- The exact checkpoint remains in every honest named filtered tree from the
source action until the first crossing. The actual FG root is below it. -/
theorem PrefixFGSelectorConeAt.checkpointFiltered_at_read_beforeFirst
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked hF0 : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : FirstHeightProgressAt S rho (blocked + 1) first)
    (hcap : HonestPrefixFinalityCap S rho first hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (ready : GradeRoundReady S rho a.round)
    (hK6Q2 : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase →
      VoterAnchorSourceQ2Inputs S rho a.round a.val_index Cfg.erase)
    (hK6Clear : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round ≠ some Cfg.erase →
      VoterAnchorSourceClearInputs S rho a.round a.val_index Cfg.erase)
    {read : Time} (hread : S.a a.round ≤ read)
    (hbefore : strictEventIndex rho read < first)
    {w : V} (hw : w ∈ rho.honest) :
    (rho.storeBeforeTime S w read).core.h_max = blocked + 1 ∧
      Block.Preceq (Protocol.get_fg_root
        (rho.storeBeforeTime S w read).core.toHealing.toFG) T ∧
      T ∈ Protocol.get_filtered_block_tree
        (rho.storeBeforeTime S w read).core.toHealing.toFG := by
  have hsource := hseed.sourceMem_at_action
    adm hbelow hcap hrec ready hK6Q2 hK6Clear hw
  have hsourcePre : Cfg ∈
      (NamedRun.stateBeforeTime S rho (S.a a.round) w).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hsource
  have heqAction := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedScheduleWellFormed (S.a a.round)) w
  have heqRead := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedScheduleWellFormed read) w
  have hcohAction := (Proofs.NamedRuntime.stateBeforeTime_invariants
    S rho (S.a a.round) w).1.1.1
  obtain ⟨K, hKC, hKT, hKh⟩ :=
    Proofs.NamedEntryHeight.entry_ancestor_same_height S.E S.cfg Cfg
  have hKpre : K ∈
      (NamedRun.stateBeforeTime S rho (S.a a.round) w).st.bodies :=
    namedAncestorBodyMem hcohAction.2.2.1 hsourcePre hKC
  rw [heqAction] at hsourcePre hKpre
  have hbody : Cfg ∈
      (NamedRun.stateBefore S rho (strictEventIndex rho read) w).st.bodies :=
    NamedBodyRetention.stateBefore_bodies_mono S rho w
      (strictEventIndex_mono rho hread) hsourcePre
  have hKbody : K ∈
      (NamedRun.stateBefore S rho (strictEventIndex rho read) w).st.bodies :=
    NamedBodyRetention.stateBefore_bodies_mono S rho w
      (strictEventIndex_mono rho hread) hKpre
  have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho
    (strictEventIndex rho read) w).1.1.1
  have hKraw : K.erase ∈
      (rho.stateBefore S (strictEventIndex rho read) w).st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hKbody
  have hKheight :
      ((rho.stateBefore S (strictEventIndex rho read) w).st.core.σ
        K.erase).h = blocked + 1 := by
    rw [Proofs.NamedStoreBridge.derivedView_stateBefore S rho
      (strictEventIndex rho read) w K hKbody, hKh,
      hseed.sourceDerivedHeight]
  have hblocked : 1 ≤ blocked :=
    Nat.le_of_lt ((Nat.succ_le_succ (Nat.zero_le hF0)).trans_lt
      (NjGap.lt_of_recoveryHeight hrec))
  obtain ⟨P, hPK, hPheight⟩ := named_ancestor_height S.E S.cfg
    hblocked (by rw [hKh, hseed.sourceDerivedHeight]; exact Nat.le_succ blocked)
  have hPbody : P ∈
      (NamedRun.stateBefore S rho (strictEventIndex rho read) w).st.bodies :=
    namedAncestorBodyMem hcoh.2.2.1 hKbody hPK
  have hPheight' :
      ((rho.stateBefore S (strictEventIndex rho read) w).st.core.σ
        P.erase).h = blocked := by
    rw [Proofs.NamedStoreBridge.derivedView_stateBefore S rho
      (strictEventIndex rho read) w P hPbody, hPheight]
  have hfrontier : honestHMaxBeforeIndex S rho
      (strictEventIndex rho read) < blocked + 2 :=
    (hfirst.before _ hbefore).trans_lt
      (Nat.lt_succ_self (blocked + 1))
  have hfiltered :=
    (fgRoot_eq_F_and_filteredMem_of_prefixCap_named S adm hbelow
      (honestPrefixFinalityCap_of_le S
        adm.toNamedScheduleWellFormed (Nat.le_of_lt hbefore) hcap)
      hrec hfrontier hw (Nat.le_refl _) hKraw hKheight
      (Proofs.NamedWire.erase_preceq hPK) hPheight').2
  have hmax := localHMax_eq_blocked_succ_of_rawMem_of_prefixFrontier
    S adm hfrontier hw (Nat.le_refl _) hKraw hKheight
  have hKT' : K.erase = T := hKT.trans hseed.checkpointDerived.symm
  have hroot : Block.Preceq
      (Protocol.get_fg_root
        (rho.stateBefore S (strictEventIndex rho read) w).st.core.toHealing.toFG)
      K.erase := Proofs.Records.preceq_get_fg_root_of_mem_filtered hfiltered
  change (NamedRun.stateBeforeTime S rho read w).st.core.h_max = blocked + 1 ∧
    Block.Preceq (Protocol.get_fg_root
      (NamedRun.stateBeforeTime S rho read w).st.core.toHealing.toFG) T ∧
    T ∈ Protocol.get_filtered_block_tree
      (NamedRun.stateBeforeTime S rho read w).st.core.toHealing.toFG
  rw [heqRead]
  exact ⟨hmax, hKT' ▸ hroot, hKT' ▸ hfiltered⟩

#print axioms PrefixFGSelectorConeAt.checkpointFiltered_at_read_beforeFirst

/-- K6-free named twin of `checkpointFiltered_at_read_beforeFirst`. Both FG
source arms use the delivered exact source body. -/
theorem PrefixFGSelectorConeAt.checkpointFiltered_at_read_beforeFirst_k6free
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked hF0 : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : FirstHeightProgressAt S rho (blocked + 1) first)
    (hcap : HonestPrefixFinalityCap S rho first hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (ready : GradeRoundReady S rho a.round)
    {read : Time} (hread : S.a a.round ≤ read)
    (hbefore : strictEventIndex rho read < first)
    {w : V} (hw : w ∈ rho.honest) :
    (rho.storeBeforeTime S w read).core.h_max = blocked + 1 ∧
      Block.Preceq (Protocol.get_fg_root
        (rho.storeBeforeTime S w read).core.toHealing.toFG) T ∧
      T ∈ Protocol.get_filtered_block_tree
        (rho.storeBeforeTime S w read).core.toHealing.toFG := by
  have hsource := hseed.sourceMem_at_action_k6free
    adm hbelow hcap hrec ready hw
  have hsourcePre : Cfg ∈
      (NamedRun.stateBeforeTime S rho (S.a a.round) w).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hsource
  have heqAction := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedScheduleWellFormed (S.a a.round)) w
  have heqRead := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedScheduleWellFormed read) w
  have hcohAction := (Proofs.NamedRuntime.stateBeforeTime_invariants
    S rho (S.a a.round) w).1.1.1
  obtain ⟨K, hKC, hKT, hKh⟩ :=
    Proofs.NamedEntryHeight.entry_ancestor_same_height S.E S.cfg Cfg
  have hKpre : K ∈
      (NamedRun.stateBeforeTime S rho (S.a a.round) w).st.bodies :=
    namedAncestorBodyMem hcohAction.2.2.1 hsourcePre hKC
  rw [heqAction] at hsourcePre hKpre
  have hbody : Cfg ∈
      (NamedRun.stateBefore S rho (strictEventIndex rho read) w).st.bodies :=
    NamedBodyRetention.stateBefore_bodies_mono S rho w
      (strictEventIndex_mono rho hread) hsourcePre
  have hKbody : K ∈
      (NamedRun.stateBefore S rho (strictEventIndex rho read) w).st.bodies :=
    NamedBodyRetention.stateBefore_bodies_mono S rho w
      (strictEventIndex_mono rho hread) hKpre
  have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho
    (strictEventIndex rho read) w).1.1.1
  have hKraw : K.erase ∈
      (rho.stateBefore S (strictEventIndex rho read) w).st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hKbody
  have hKheight :
      ((rho.stateBefore S (strictEventIndex rho read) w).st.core.σ
        K.erase).h = blocked + 1 := by
    rw [Proofs.NamedStoreBridge.derivedView_stateBefore S rho
      (strictEventIndex rho read) w K hKbody, hKh,
      hseed.sourceDerivedHeight]
  have hblocked : 1 ≤ blocked :=
    Nat.le_of_lt ((Nat.succ_le_succ (Nat.zero_le hF0)).trans_lt
      (NjGap.lt_of_recoveryHeight hrec))
  obtain ⟨P, hPK, hPheight⟩ := named_ancestor_height S.E S.cfg
    hblocked (by rw [hKh, hseed.sourceDerivedHeight]; exact Nat.le_succ blocked)
  have hPbody : P ∈
      (NamedRun.stateBefore S rho (strictEventIndex rho read) w).st.bodies :=
    namedAncestorBodyMem hcoh.2.2.1 hKbody hPK
  have hPheight' :
      ((rho.stateBefore S (strictEventIndex rho read) w).st.core.σ
        P.erase).h = blocked := by
    rw [Proofs.NamedStoreBridge.derivedView_stateBefore S rho
      (strictEventIndex rho read) w P hPbody, hPheight]
  have hfrontier : honestHMaxBeforeIndex S rho
      (strictEventIndex rho read) < blocked + 2 :=
    (hfirst.before _ hbefore).trans_lt
      (Nat.lt_succ_self (blocked + 1))
  have hfiltered :=
    (fgRoot_eq_F_and_filteredMem_of_prefixCap_named S adm hbelow
      (honestPrefixFinalityCap_of_le S
        adm.toNamedScheduleWellFormed (Nat.le_of_lt hbefore) hcap)
      hrec hfrontier hw (Nat.le_refl _) hKraw hKheight
      (Proofs.NamedWire.erase_preceq hPK) hPheight').2
  have hmax := localHMax_eq_blocked_succ_of_rawMem_of_prefixFrontier
    S adm hfrontier hw (Nat.le_refl _) hKraw hKheight
  have hKT' : K.erase = T := hKT.trans hseed.checkpointDerived.symm
  have hroot : Block.Preceq
      (Protocol.get_fg_root
        (rho.stateBefore S (strictEventIndex rho read) w).st.core.toHealing.toFG)
      K.erase := Proofs.Records.preceq_get_fg_root_of_mem_filtered hfiltered
  change (NamedRun.stateBeforeTime S rho read w).st.core.h_max = blocked + 1 ∧
    Block.Preceq (Protocol.get_fg_root
      (NamedRun.stateBeforeTime S rho read w).st.core.toHealing.toFG) T ∧
    T ∈ Protocol.get_filtered_block_tree
      (NamedRun.stateBeforeTime S rho read w).st.core.toHealing.toFG
  rw [heqRead]
  exact ⟨hmax, hKT' ▸ hroot, hKT' ▸ hfiltered⟩

#print axioms PrefixFGSelectorConeAt.checkpointFiltered_at_read_beforeFirst_k6free

/-- Apply the named Goldfish canonicality step to the exact FG witness. -/
theorem PrefixFGSelectorConeAt.checkpointVoteStep_beforeFirst
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked hF0 : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : FirstHeightProgressAt S rho (blocked + 1) first)
    (hcap : HonestPrefixFinalityCap S rho first hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    (ready : GradeRoundReady S rho a.round)
    (hK6Q2 : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase →
      VoterAnchorSourceQ2Inputs S rho a.round a.val_index Cfg.erase)
    (hK6Clear : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round ≠ some Cfg.erase →
      VoterAnchorSourceClearInputs S rho a.round a.val_index Cfg.erase)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hread : S.a a.round ≤ Protocol.vote_time S.E (s + 1))
    (hbefore : strictEventIndex rho (Protocol.vote_time S.E (s + 1)) < first)
    (hvotes : NamedHonestVotesCone S rho s (fun X => Block.Preceq T X))
    (hanchors : ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w (s + 1)) T = true) :
    (∀ w ∈ rho.honest, Block.Preceq T (voterHeadAt S rho w (s + 1))) ∧
      NamedHonestVotesCone S rho (s + 1) (fun X => Block.Preceq T X) := by
  obtain ⟨K, _, hKT, hKh, _, hKrun⟩ :=
    action_named_checkpoint S adm hseed.signerHonest hseed.sourceMem
  have hKT' : K.erase = T := hKT.trans hseed.checkpointDerived.symm
  have hKheight :
      (Protocol.derive_named S.E S.cfg K).h = blocked + 1 :=
    hKh.trans hseed.sourceDerivedHeight
  have hreads := fun w hw => hseed.checkpointFiltered_at_read_beforeFirst
    adm hbelow hfirst hcap hrec ready hK6Q2 hK6Clear hread hbefore
      (w := w) hw
  have hheads : ∀ w ∈ rho.honest,
      Block.Preceq T (voterHeadAt S rho w (s + 1)) := by
    intro w hw
    let read := voteDutyRead S rho w (s + 1)
    have hmax : (voteDutyRead S rho w (s + 1)).st.core.h_max = blocked + 1 := by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using
        (hreads w hw).1
    have hroot : Block.Preceq
        (Protocol.get_fg_root
          (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) T := by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using
        (hreads w hw).2.1
    have hpositive : 0 < ((S.E.committee s) ∩ rho.honest).card := by
      have hc := hcom s
      omega
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hpositive
    have huCommittee : u ∈ S.E.committee s := (Finset.mem_inter.mp hu).1
    have huHonest : u ∈ rho.honest := (Finset.mem_inter.mp hu).2
    obtain ⟨X, hTX, hXrun, hXemit⟩ := hvotes u huHonest huCommittee
    have hXhead : Proofs.Optimistic.HonestHead S rho s X.erase :=
      ⟨u, huHonest, huCommittee, ⟨X, rfl, hXrun⟩, hXemit⟩
    have hrootDuty : Block.Preceq
        (Protocol.get_fg_root
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) T := by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hroot
    have hprocessed := honestHead_voterProcessed_at_nextDuty_of_postHealingCone
      S adm hpost hhor hvotes hXhead hw hrootDuty
    obtain ⟨K', hK'X, hK'erase⟩ :=
      Proofs.NamedAncestry.erased_ancestor_lift X hTX
    have hK'run : RunBlock S rho K' :=
      Proofs.NamedRuntime.blockInRun_of_ancestor S rho hXrun hK'X
    have hK'eq : K' = K := by
      apply adm.toNamedRootCollisionFree.root_injective
        K' K hK'run hKrun K' K
        (Or.inl (Proofs.NamedAncestry.named_self K'))
        (Or.inr (Proofs.NamedAncestry.named_self K))
      rw [← Proofs.NamedWire.erase_root K', hK'erase, ← hKT', Proofs.NamedWire.erase_root]
    have hKXheight :
        (Protocol.derive_named S.E S.cfg K).h ≤
          (Protocol.derive_named S.E S.cfg X).h := by
      rw [← hK'eq]
      exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hK'X
    have hXmem : X.erase ∈ (voteDutyRead S rho w (s + 1)).st.core.T := by
      have hmem := (Finset.mem_filter.mp hprocessed).1
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hmem
    have hstored := WeakJoint.storedHeight_of_runBlock_mem_voteDutyRead
      S adm hw hXrun hXmem
    have hband : (voteDutyRead S rho w (s + 1)).st.core.h_max - 1 ≤
        ((voteDutyRead S rho w (s + 1)).st.core.σ X.erase).h := by
      rw [hKheight] at hKXheight
      rw [hstored, hmax]
      exact (Nat.sub_le (blocked + 1) 1).trans hKXheight
    have hpath := WeakJoint.namedCandidatePath_of_processedBandDescendant
      S adm hw hTX hprocessed hband hroot
    apply goldfishCone_step' S adm hcom hs hpost hhor hvotes hw
    exact { rootSide := Or.inl ⟨hroot, hpath⟩, anchor := hanchors w hw }
  refine ⟨hheads, ?_⟩
  have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
    apply le_trans (le_of_lt ?_) hhor
    rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E s]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  intro w hw hcommittee
  obtain ⟨X, hXe, hXrun, hXemit⟩ :=
    named_voter_head_emits S adm hw (Nat.succ_pos s) hcommittee hvoteHor
  exact ⟨X, hXe ▸ hheads w hw, hXrun, hXemit⟩

#print axioms PrefixFGSelectorConeAt.checkpointVoteStep_beforeFirst

/-- The exact checkpoint remains in every honest named filtered tree from the
source action until the first crossing, from the additive named regime frame.
The retained named predecessor supplies the root-collision comparison. -/
theorem PrefixFGSelectorConeAt.checkpointFiltered_at_read_of_frame
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    {Tprev : NamedBlock V} {c0 : Round}
    (hframe : HeightRegimeFrameN S rho blocked (first - 1) Tprev c0)
    (ready : GradeRoundReady S rho a.round)
    (hK6Q2 : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase →
      VoterAnchorSourceQ2Inputs S rho a.round a.val_index Cfg.erase)
    (hK6Clear : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round ≠ some Cfg.erase →
      VoterAnchorSourceClearInputs S rho a.round a.val_index Cfg.erase)
    {read : Time} (hread : S.a a.round ≤ read)
    (hbefore : strictEventIndex rho read < first)
    {w : V} (hw : w ∈ rho.honest) :
    (rho.storeBeforeTime S w read).core.h_max = blocked + 1 ∧
      Block.Preceq (Protocol.get_fg_root
        (rho.storeBeforeTime S w read).core.toHealing.toFG) T ∧
      T ∈ Protocol.get_filtered_block_tree
        (rho.storeBeforeTime S w read).core.toHealing.toFG := by
  have hsource : Cfg ∈ (actionStoreAt S rho w a.round).st.bodies := by
    by_cases hselected : PhaseGrades.nodeQ2
        S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase
    · exact actionBody_at_action_of_openingVoteFiltered
        S adm hseed.signerHonest hseed.sourceMem hw
          ((hK6Q2 hselected).openingTarget w hw)
    · exact actionBody_at_action_of_nextVoteFiltered
        S adm hseed.signerHonest hseed.sourceMem hw
          ((hK6Clear hselected).nextTarget w hw)
  have hsourcePre : Cfg ∈
      (NamedRun.stateBeforeTime S rho (S.a a.round) w).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hsource
  have heqAction := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedScheduleWellFormed (S.a a.round)) w
  have heqRead := congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedScheduleWellFormed read) w
  have hcohAction := (Proofs.NamedRuntime.stateBeforeTime_invariants
    S rho (S.a a.round) w).1.1.1
  obtain ⟨K, hKC, hKT, hKh⟩ :=
    Proofs.NamedEntryHeight.entry_ancestor_same_height S.E S.cfg Cfg
  have hKpre : K ∈
      (NamedRun.stateBeforeTime S rho (S.a a.round) w).st.bodies :=
    namedAncestorBodyMem hcohAction.2.2.1 hsourcePre hKC
  rw [heqAction] at hsourcePre hKpre
  have hKbody : K ∈
      (NamedRun.stateBefore S rho (strictEventIndex rho read) w).st.bodies :=
    NamedBodyRetention.stateBefore_bodies_mono S rho w
      (strictEventIndex_mono rho hread) hKpre
  have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho
    (strictEventIndex rho read) w).1.1.1
  have hKraw : K.erase ∈
      (rho.stateBefore S (strictEventIndex rho read) w).st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hKbody
  have hKheight :
      ((rho.stateBefore S (strictEventIndex rho read) w).st.core.σ
        K.erase).h = blocked + 1 := by
    rw [Proofs.NamedStoreBridge.derivedView_stateBefore S rho
      (strictEventIndex rho read) w K hKbody, hKh,
      hseed.sourceDerivedHeight]
  have hKheightNamed :
      (Protocol.derive_named S.E S.cfg K).h = blocked + 1 :=
    hKh.trans hseed.sourceDerivedHeight
  have hfrontier : honestHMaxBeforeIndex S rho
      (strictEventIndex rho read) < blocked + 2 :=
    (hfirst.before _ hbefore).trans_lt
      (Nat.lt_succ_self (blocked + 1))
  have hKrun : RunBlock S rho K :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hw hKbody
  have hTprevCfg : Block.Preceq Tprev.erase Cfg.erase := by
    apply hframe.namedSourceAbove a.val_index hseed.signerHonest a.round
      (Nat.le_sub_one_of_lt
        (hseed.actionPrefix_lt adm.toNamedScheduleWellFormed))
      (hseed.actionHorizon adm) Cfg hseed.sourceMem hseed.exactFGSource
        hseed.sourceDerivedHeight
  have hTprevK : NamedBlock.Preceq Tprev K := by
    rcases Block.preceq_linear hTprevCfg
        (Proofs.NamedWire.erase_preceq hKC) with hprevK | hKprev
    · obtain ⟨P, hPK, hPerase⟩ :=
        Proofs.NamedAncestry.erased_ancestor_lift K hprevK
      have hPrun : RunBlock S rho P :=
        Proofs.NamedRuntime.blockInRun_of_ancestor S rho hKrun hPK
      have hPTprev : P = Tprev := by
        apply adm.toNamedRootCollisionFree.root_injective
          P Tprev hPrun hframe.prevRun P Tprev
          (Or.inl (Proofs.NamedAncestry.named_self P))
          (Or.inr (Proofs.NamedAncestry.named_self Tprev))
        rw [← Proofs.NamedWire.erase_root P, hPerase, Proofs.NamedWire.erase_root]
      rw [← hPTprev]
      exact hPK
    · obtain ⟨P, hPTprev, hPerase⟩ :=
        Proofs.NamedAncestry.erased_ancestor_lift Tprev hKprev
      have hPrun : RunBlock S rho P :=
        Proofs.NamedRuntime.blockInRun_of_ancestor S rho hframe.prevRun hPTprev
      have hPK : P = K := by
        apply adm.toNamedRootCollisionFree.root_injective
          P K hPrun hKrun P K
          (Or.inl (Proofs.NamedAncestry.named_self P))
          (Or.inr (Proofs.NamedAncestry.named_self K))
        rw [← Proofs.NamedWire.erase_root P, hPerase, Proofs.NamedWire.erase_root]
      have hKTprev : NamedBlock.Preceq K Tprev := by
        rw [← hPK]
        exact hPTprev
      have hmono := Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hKTprev
      rw [hKheightNamed] at hmono
      exact False.elim
        (Nat.not_succ_le_self blocked (hmono.trans hframe.prevHeight))
  have hn : strictEventIndex rho read ≤ first - 1 :=
    Nat.le_sub_one_of_lt hbefore
  have hroot : Block.Preceq
      (Protocol.get_fg_root
        (rho.stateBefore S (strictEventIndex rho read) w).st.core.toHealing.toFG)
      K.erase :=
    hframe.rootBelow w hw (strictEventIndex rho read) hn K.erase hKraw
      hKheight (Proofs.NamedWire.erase_preceq hTprevK)
  have hFK : Block.Preceq
      (rho.stateBefore S (strictEventIndex rho read) w).st.core.F K.erase :=
    hframe.floor w hw (strictEventIndex rho read) hn K hKrun
      (hKheightNamed ▸ Nat.le_succ blocked)
      (Proofs.NamedWire.erase_preceq hTprevK)
  have hmax := localHMax_eq_blocked_succ_of_rawMem_of_prefixFrontier
    S adm hfrontier hw (Nat.le_refl _) hKraw hKheight
  have hV : K.erase ∈ Protocol.V_tree
      (rho.stateBefore S (strictEventIndex rho read) w).st.core.toHealing.toFG := by
    simp only [Protocol.V_tree, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, Protocol.Store.toHealing, decide_eq_true_eq]
    refine ⟨⟨hKraw, hFK⟩, K.erase, hKraw, Block.preceq_self _, ?_⟩
    have hmaxCore :
        (rho.stateBefore S (strictEventIndex rho read) w).st.core.h_max = blocked + 1 := hmax
    rw [hmaxCore, hKheight]
    exact Nat.sub_le _ _
  have hfiltered : K.erase ∈ Protocol.get_filtered_block_tree
      (rho.stateBefore S (strictEventIndex rho read) w).st.core.toHealing.toFG :=
    Proofs.Records.mem_filtered_of_mem_V_tree hV hroot
  have hKT' : K.erase = T := hKT.trans hseed.checkpointDerived.symm
  change (NamedRun.stateBeforeTime S rho read w).st.core.h_max = blocked + 1 ∧
    Block.Preceq (Protocol.get_fg_root
      (NamedRun.stateBeforeTime S rho read w).st.core.toHealing.toFG) T ∧
    T ∈ Protocol.get_filtered_block_tree
      (NamedRun.stateBeforeTime S rho read w).st.core.toHealing.toFG
  rw [heqRead]
  exact ⟨hmax, hKT' ▸ hroot, hKT' ▸ hfiltered⟩

#print axioms PrefixFGSelectorConeAt.checkpointFiltered_at_read_of_frame

/-- Additive `HeightRegimeFrameN`-named spelling of
`checkpointFiltered_at_read_of_frame`. -/
theorem PrefixFGSelectorConeAt.checkpointFiltered_at_read_of_frameN
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    {Tprev : NamedBlock V} {c0 : Round}
    (hframe : HeightRegimeFrameN S rho blocked (first - 1) Tprev c0)
    (ready : GradeRoundReady S rho a.round)
    (hK6Q2 : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase →
      VoterAnchorSourceQ2Inputs S rho a.round a.val_index Cfg.erase)
    (hK6Clear : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round ≠ some Cfg.erase →
      VoterAnchorSourceClearInputs S rho a.round a.val_index Cfg.erase)
    {read : Time} (hread : S.a a.round ≤ read)
    (hbefore : strictEventIndex rho read < first)
    {w : V} (hw : w ∈ rho.honest) :
    (rho.storeBeforeTime S w read).core.h_max = blocked + 1 ∧
      Block.Preceq (Protocol.get_fg_root
        (rho.storeBeforeTime S w read).core.toHealing.toFG) T ∧
      T ∈ Protocol.get_filtered_block_tree
        (rho.storeBeforeTime S w read).core.toHealing.toFG :=
  hseed.checkpointFiltered_at_read_of_frame adm hfirst hframe ready
    hK6Q2 hK6Clear hread hbefore hw

#print axioms PrefixFGSelectorConeAt.checkpointFiltered_at_read_of_frameN

/-- The named Goldfish canonicality step for the checkpoint, from the
additive named regime frame. -/
theorem PrefixFGSelectorConeAt.checkpointVoteStep_of_frame
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    {Tprev : NamedBlock V} {c0 : Round}
    (hframe : HeightRegimeFrameN S rho blocked (first - 1) Tprev c0)
    (ready : GradeRoundReady S rho a.round)
    (hK6Q2 : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase →
      VoterAnchorSourceQ2Inputs S rho a.round a.val_index Cfg.erase)
    (hK6Clear : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round ≠ some Cfg.erase →
      VoterAnchorSourceClearInputs S rho a.round a.val_index Cfg.erase)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hread : S.a a.round ≤ Protocol.vote_time S.E (s + 1))
    (hbefore : strictEventIndex rho (Protocol.vote_time S.E (s + 1)) < first)
    (hvotes : NamedHonestVotesCone S rho s (fun X => Block.Preceq T X))
    (hanchors : ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w (s + 1)) T = true) :
    (∀ w ∈ rho.honest, Block.Preceq T (voterHeadAt S rho w (s + 1))) ∧
      NamedHonestVotesCone S rho (s + 1) (fun X => Block.Preceq T X) := by
  obtain ⟨K, _, hKT, hKh, _, hKrun⟩ :=
    action_named_checkpoint S adm hseed.signerHonest hseed.sourceMem
  have hKT' : K.erase = T := hKT.trans hseed.checkpointDerived.symm
  have hKheight :
      (Protocol.derive_named S.E S.cfg K).h = blocked + 1 :=
    hKh.trans hseed.sourceDerivedHeight
  have hreads := fun w hw => hseed.checkpointFiltered_at_read_of_frame
    adm hfirst hframe ready hK6Q2 hK6Clear hread hbefore (w := w) hw
  have hheads : ∀ w ∈ rho.honest,
      Block.Preceq T (voterHeadAt S rho w (s + 1)) := by
    intro w hw
    have hmax : (voteDutyRead S rho w (s + 1)).st.core.h_max = blocked + 1 := by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using
        (hreads w hw).1
    have hroot : Block.Preceq
        (Protocol.get_fg_root
          (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) T := by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using
        (hreads w hw).2.1
    have hpositive : 0 < ((S.E.committee s) ∩ rho.honest).card := by
      have hc := hcom s
      omega
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hpositive
    have huCommittee : u ∈ S.E.committee s := (Finset.mem_inter.mp hu).1
    have huHonest : u ∈ rho.honest := (Finset.mem_inter.mp hu).2
    obtain ⟨X, hTX, hXrun, hXemit⟩ := hvotes u huHonest huCommittee
    have hXhead : Proofs.Optimistic.HonestHead S rho s X.erase :=
      ⟨u, huHonest, huCommittee, ⟨X, rfl, hXrun⟩, hXemit⟩
    have hrootDuty : Block.Preceq
        (Protocol.get_fg_root
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) T := by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hroot
    have hprocessed := honestHead_voterProcessed_at_nextDuty_of_postHealingCone
      S adm hpost hhor hvotes hXhead hw hrootDuty
    obtain ⟨K', hK'X, hK'erase⟩ :=
      Proofs.NamedAncestry.erased_ancestor_lift X hTX
    have hK'run : RunBlock S rho K' :=
      Proofs.NamedRuntime.blockInRun_of_ancestor S rho hXrun hK'X
    have hK'eq : K' = K := by
      apply adm.toNamedRootCollisionFree.root_injective
        K' K hK'run hKrun K' K
        (Or.inl (Proofs.NamedAncestry.named_self K'))
        (Or.inr (Proofs.NamedAncestry.named_self K))
      rw [← Proofs.NamedWire.erase_root K', hK'erase, ← hKT', Proofs.NamedWire.erase_root]
    have hKXheight :
        (Protocol.derive_named S.E S.cfg K).h ≤
          (Protocol.derive_named S.E S.cfg X).h := by
      rw [← hK'eq]
      exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hK'X
    have hXmem : X.erase ∈ (voteDutyRead S rho w (s + 1)).st.core.T := by
      have hmem := (Finset.mem_filter.mp hprocessed).1
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hmem
    have hstored := WeakJoint.storedHeight_of_runBlock_mem_voteDutyRead
      S adm hw hXrun hXmem
    have hband : (voteDutyRead S rho w (s + 1)).st.core.h_max - 1 ≤
        ((voteDutyRead S rho w (s + 1)).st.core.σ X.erase).h := by
      rw [hKheight] at hKXheight
      rw [hstored, hmax]
      exact (Nat.sub_le (blocked + 1) 1).trans hKXheight
    have hpath := WeakJoint.namedCandidatePath_of_processedBandDescendant
      S adm hw hTX hprocessed hband hroot
    apply goldfishCone_step' S adm hcom hs hpost hhor hvotes hw
    exact { rootSide := Or.inl ⟨hroot, hpath⟩, anchor := hanchors w hw }
  refine ⟨hheads, ?_⟩
  have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
    apply le_trans (le_of_lt ?_) hhor
    rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E s]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  intro w hw hcommittee
  obtain ⟨X, hXe, hXrun, hXemit⟩ :=
    named_voter_head_emits S adm hw (Nat.succ_pos s) hcommittee hvoteHor
  exact ⟨X, hXe ▸ hheads w hw, hXrun, hXemit⟩

#print axioms PrefixFGSelectorConeAt.checkpointVoteStep_of_frame


/-
/-- The exact checkpoint remains in every honest named filtered tree from the
source action until the first crossing, from the regime frame. -/
theorem PrefixFGSelectorConeAt.checkpointFiltered_at_read_of_frame
    {S: Setup V} {rho: Run V} (adm: Admissible S rho)
    {start first: Nat} {blocked: Height}
    {i: Nat} {a: NamedAttestation V} {ta: Time}
    {Cfg: NamedBlock V} {T: Block V}
    (hseed: PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst: HeightWindowAt S rho (blocked + 1) first)
    {Tprev: NamedBlock V} {c0: Round}
    (hframe: NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (ready: GradeRoundReady S rho a.round)
    (hK6Q2: PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase →
      VoterAnchorSourceQ2Inputs S rho a.round a.val_index Cfg.erase)
    (hK6Clear: PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round ≠ some Cfg.erase →
      VoterAnchorSourceClearInputs S rho a.round a.val_index Cfg.erase)
    {read: Time} (hread: S.a a.round ≤ read)
    (hbefore: strictEventIndex rho read < first)
    {w: V} (hw: w ∈ rho.honest):
    (rho.storeBeforeTime S w read).core.h_max = blocked + 1 ∧
      Block.Preceq (Protocol.get_fg_root
        (rho.storeBeforeTime S w read).core.toHealing.toFG) T ∧
      T ∈ Protocol.get_filtered_block_tree
        (rho.storeBeforeTime S w read).core.toHealing.toFG:= by
  have hsource: Cfg ∈ (actionStoreAt S rho w a.round).st.bodies:= by
    by_cases hselected: PhaseGrades.nodeQ2
        S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase
    · exact actionBody_at_action_of_openingVoteFiltered
        S adm hseed.signerHonest hseed.sourceMem hw
          ((hK6Q2 hselected).openingTarget w hw)
    · exact actionBody_at_action_of_nextVoteFiltered
        S adm hseed.signerHonest hseed.sourceMem hw
          ((hK6Clear hselected).nextTarget w hw)
  have hsourcePre: Cfg ∈
      (NamedRun.stateBeforeTime S rho (S.a a.round) w).st.bodies:= by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hsource
  have heqAction:= congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedScheduleWellFormed (S.a a.round)) w
  have heqRead:= congrFun (stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedScheduleWellFormed read) w
  have hcohAction:= (Proofs.NamedRuntime.stateBeforeTime_invariants
    S rho (S.a a.round) w).1.1.1
  obtain ⟨K, hKC, hKT, hKh⟩:=
    Proofs.NamedEntryHeight.entry_ancestor_same_height S.E S.cfg Cfg
  have hKpre: K ∈
      (NamedRun.stateBeforeTime S rho (S.a a.round) w).st.bodies:=
    namedAncestorBodyMem hcohAction.2.2.1 hsourcePre hKC
  rw [heqAction] at hsourcePre hKpre
  have hKbody: K ∈
      (NamedRun.stateBefore S rho (strictEventIndex rho read) w).st.bodies:=
    NamedBodyRetention.stateBefore_bodies_mono S rho w
      (strictEventIndex_mono rho hread) hKpre
  have hcoh:= (Proofs.NamedRuntime.stateBefore_invariants S rho
    (strictEventIndex rho read) w).1.1.1
  have hKraw: K.erase ∈
      (rho.stateBefore S (strictEventIndex rho read) w).st.core.T:= by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hKbody
  have hKheight:
      ((rho.stateBefore S (strictEventIndex rho read) w).st.core.σ
        K.erase).h = blocked + 1:= by
    rw [Proofs.NamedStoreBridge.derivedView_stateBefore S rho
      (strictEventIndex rho read) w K hKbody, hKh,
      hseed.sourceDerivedHeight]
  have hKheightNamed:
      (Protocol.derive_named S.E S.cfg K).h = blocked + 1:=
    hKh.trans hseed.sourceDerivedHeight
  have hfrontier: honestHMaxBeforeIndex S rho
      (strictEventIndex rho read) < blocked + 2:=
    (hfirst.before _ hbefore).trans_lt
      (Nat.lt_succ_self (blocked + 1))
  have hKrun: RunBlock S rho K:=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hw hKbody
  have hTprevCfg: NamedBlock.Preceq Tprev Cfg:= by
    apply hframe.sourceAbove a.val_index hseed.signerHonest a.round
      (Nat.le_sub_one_of_lt
        (hseed.actionPrefix_lt adm.toNamedScheduleWellFormed))
      (hseed.actionHorizon adm) Cfg hseed.sourceMem hseed.exactFGSource
        hseed.sourceDerivedHeight
  have hTprevK: NamedBlock.Preceq Tprev K:= by
    rcases Block.preceq_linear (Proofs.NamedWire.erase_preceq hTprevCfg)
        (Proofs.NamedWire.erase_preceq hKC) with hprevK | hKprev
    · obtain ⟨P, hPK, hPerase⟩:=
        Proofs.NamedAncestry.erased_ancestor_lift K hprevK
      have hPrun: RunBlock S rho P:=
        Proofs.NamedRuntime.blockInRun_of_ancestor S rho hKrun hPK
      have hPTprev: P = Tprev:= by
        apply adm.toNamedRootCollisionFree.root_injective
          P Tprev hPrun hframe.prevRun P Tprev
          (Or.inl (Proofs.NamedAncestry.named_self P))
          (Or.inr (Proofs.NamedAncestry.named_self Tprev))
        rw [← Proofs.NamedWire.erase_root P, hPerase, Proofs.NamedWire.erase_root]
      rw [← hPTprev]
      exact hPK
    · obtain ⟨P, hPTprev, hPerase⟩:=
        Proofs.NamedAncestry.erased_ancestor_lift Tprev hKprev
      have hPrun: RunBlock S rho P:=
        Proofs.NamedRuntime.blockInRun_of_ancestor S rho hframe.prevRun hPTprev
      have hPK: P = K:= by
        apply adm.toNamedRootCollisionFree.root_injective
          P K hPrun hKrun P K
          (Or.inl (Proofs.NamedAncestry.named_self P))
          (Or.inr (Proofs.NamedAncestry.named_self K))
        rw [← Proofs.NamedWire.erase_root P, hPerase, Proofs.NamedWire.erase_root]
      have hKTprev: NamedBlock.Preceq K Tprev:= by
        rw [← hPK]
        exact hPTprev
      have hmono:= Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hKTprev
      rw [hKheightNamed] at hmono
      exact False.elim
        (Nat.not_succ_le_self blocked (hmono.trans hframe.prevHeight))
  have hn: strictEventIndex rho read ≤ first - 1:=
    Nat.le_sub_one_of_lt hbefore
  have hroot: Block.Preceq
      (Protocol.get_fg_root
        (rho.stateBefore S (strictEventIndex rho read) w).st.core.toHealing.toFG)
      K.erase:=
    hframe.rootBelow w hw (strictEventIndex rho read) hn K hKbody
      hKheightNamed hTprevK
  have hFK: Block.Preceq
      (rho.stateBefore S (strictEventIndex rho read) w).st.core.F K.erase:=
    hframe.floor w hw (strictEventIndex rho read) hn K hKrun
      (hKheightNamed ▸ Nat.le_succ blocked) hTprevK
  have hmax:= localHMax_eq_blocked_succ_of_rawMem_of_prefixFrontier
    S adm hfrontier hw (Nat.le_refl _) hKraw hKheight
  have hV: K.erase ∈ Protocol.V_tree
      (rho.stateBefore S (strictEventIndex rho read) w).st.core.toHealing.toFG:= by
    simp only [Protocol.V_tree, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, Protocol.Store.toHealing, decide_eq_true_eq]
    refine ⟨⟨hKraw, hFK⟩, K.erase, hKraw, Block.preceq_self _, ?_⟩
    rw [hmax, hKheight]
    exact Nat.sub_le _ _
  have hfiltered: K.erase ∈ Protocol.get_filtered_block_tree
      (rho.stateBefore S (strictEventIndex rho read) w).st.core.toHealing.toFG:=
    Proofs.Records.mem_filtered_of_mem_V_tree hV hroot
  have hKT': K.erase = T:= hKT.trans hseed.checkpointDerived.symm
  change (NamedRun.stateBeforeTime S rho read w).st.core.h_max = blocked + 1 ∧
    Block.Preceq (Protocol.get_fg_root
      (NamedRun.stateBeforeTime S rho read w).st.core.toHealing.toFG) T ∧
    T ∈ Protocol.get_filtered_block_tree
      (NamedRun.stateBeforeTime S rho read w).st.core.toHealing.toFG
  rw [heqRead]
  exact ⟨hmax, hKT' ▸ hroot, hKT' ▸ hfiltered⟩

/-- The named Goldfish canonicality step for the checkpoint, from the regime
frame. -/
theorem PrefixFGSelectorConeAt.checkpointVoteStep_of_frame
    {S: Setup V} {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest) (hbelow: BelowOneThird S rho.honest)
    {start first: Nat} {blocked: Height}
    {i: Nat} {a: NamedAttestation V} {ta: Time}
    {Cfg: NamedBlock V} {T: Block V}
    (hseed: PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst: HeightWindowAt S rho (blocked + 1) first)
    {Tprev: NamedBlock V} {c0: Round}
    (hframe: NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (ready: GradeRoundReady S rho a.round)
    (hK6Q2: PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase →
      VoterAnchorSourceQ2Inputs S rho a.round a.val_index Cfg.erase)
    (hK6Clear: PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round ≠ some Cfg.erase →
      VoterAnchorSourceClearInputs S rho a.round a.val_index Cfg.erase)
    {s: Slot} (hs: 0 < s)
    (hpost: S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor: Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hread: S.a a.round ≤ Protocol.vote_time S.E (s + 1))
    (hbefore: strictEventIndex rho (Protocol.vote_time S.E (s + 1)) < first)
    (hvotes: NamedHonestVotesCone S rho s (fun X => Block.Preceq T X))
    (hanchors: ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w (s + 1)) T = true):
    (∀ w ∈ rho.honest, Block.Preceq T (voterHeadAt S rho w (s + 1))) ∧
      NamedHonestVotesCone S rho (s + 1) (fun X => Block.Preceq T X):= by
  obtain ⟨K, _, hKT, hKh, _, hKrun⟩:=
    action_named_checkpoint S adm hseed.signerHonest hseed.sourceMem
  have hKT': K.erase = T:= hKT.trans hseed.checkpointDerived.symm
  have hKheight:
      (Protocol.derive_named S.E S.cfg K).h = blocked + 1:=
    hKh.trans hseed.sourceDerivedHeight
  have hreads:= fun w hw => hseed.checkpointFiltered_at_read_of_frame
    adm hfirst hframe ready hK6Q2 hK6Clear hread hbefore (w:= w) hw
  have hheads: ∀ w ∈ rho.honest,
      Block.Preceq T (voterHeadAt S rho w (s + 1)):= by
    intro w hw
    have hmax: (voteDutyRead S rho w (s + 1)).st.core.h_max = blocked + 1:= by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using
        (hreads w hw).1
    have hroot: Block.Preceq
        (Protocol.get_fg_root
          (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) T:= by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using
        (hreads w hw).2.1
    have hpositive: 0 < ((S.E.committee s) ∩ rho.honest).card:= by
      have hc:= hcom s
      omega
    obtain ⟨u, hu⟩:= Finset.card_pos.mp hpositive
    have huCommittee: u ∈ S.E.committee s:= (Finset.mem_inter.mp hu).1
    have huHonest: u ∈ rho.honest:= (Finset.mem_inter.mp hu).2
    obtain ⟨X, hTX, hXrun, hXemit⟩:= hvotes u huHonest huCommittee
    have hXhead: Proofs.Optimistic.HonestHead S rho s X.erase:=
      ⟨u, huHonest, huCommittee, ⟨X, rfl, hXrun⟩, hXemit⟩
    have hrootDuty: Block.Preceq
        (Protocol.get_fg_root
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) T:= by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hroot
    have hprocessed:= honestHead_voterProcessed_at_nextDuty_of_postHealingCone
      S adm hpost hhor hvotes hXhead hw hrootDuty
    obtain ⟨K', hK'X, hK'erase⟩:=
      Proofs.NamedAncestry.erased_ancestor_lift X hTX
    have hK'run: RunBlock S rho K':=
      Proofs.NamedRuntime.blockInRun_of_ancestor S rho hXrun hK'X
    have hK'eq: K' = K:= by
      apply adm.toNamedRootCollisionFree.root_injective
        K' K hK'run hKrun K' K
        (Or.inl (Proofs.NamedAncestry.named_self K'))
        (Or.inr (Proofs.NamedAncestry.named_self K))
      rw [← Proofs.NamedWire.erase_root K', hK'erase, ← hKT', Proofs.NamedWire.erase_root]
    have hKXheight:
        (Protocol.derive_named S.E S.cfg K).h ≤
          (Protocol.derive_named S.E S.cfg X).h:= by
      rw [← hK'eq]
      exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hK'X
    have hXmem: X.erase ∈ (voteDutyRead S rho w (s + 1)).st.core.T:= by
      have hmem:= (Finset.mem_filter.mp hprocessed).1
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hmem
    have hstored:= WeakJoint.storedHeight_of_runBlock_mem_voteDutyRead
      S adm hw hXrun hXmem
    have hband: (voteDutyRead S rho w (s + 1)).st.core.h_max - 1 ≤
        ((voteDutyRead S rho w (s + 1)).st.core.σ X.erase).h:= by
      rw [hKheight] at hKXheight
      rw [hstored, hmax]
      exact (Nat.sub_le (blocked + 1) 1).trans hKXheight
    have hpath:= WeakJoint.namedCandidatePath_of_processedBandDescendant
      S adm hw hTX hprocessed hband hroot
    apply goldfishCone_step' S adm hcom hs hpost hhor hvotes hw
    exact { rootSide:= Or.inl ⟨hroot, hpath⟩, anchor:= hanchors w hw }
  refine ⟨hheads, ?_⟩
  have hvoteHor: Protocol.vote_time S.E (s + 1) ≤ rho.horizon:= by
    apply le_trans (le_of_lt ?_) hhor
    rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E s]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  intro w hw hcommittee
  obtain ⟨X, hXe, hXrun, hXemit⟩:=
    named_voter_head_emits S adm hw (Nat.succ_pos s) hcommittee hvoteHor
  exact ⟨X, hXe ▸ hheads w hw, hXrun, hXemit⟩

#print axioms PrefixFGSelectorConeAt.checkpointFiltered_at_read_beforeFirst
#print axioms PrefixFGSelectorConeAt.checkpointVoteStep_beforeFirst
#print axioms PrefixFGSelectorConeAt.checkpointFiltered_at_read_of_frame
#print axioms PrefixFGSelectorConeAt.checkpointVoteStep_of_frame
-/





end HealingSurface
end Proofs
end DecoupledConsensusModel

end
