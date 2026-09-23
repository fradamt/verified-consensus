module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.TimeoutDelay
public import DecoupledConsensusProofs.Protocol.ChainState.CanonicalRegimeRound
public import DecoupledConsensusProofs.Generic.CanonicalSuffix
public import DecoupledConsensusProofs.Protocol.ChainState.CanonicalDensity
public import DecoupledConsensusProofs.Protocol.ChainState.CarrierAlignment
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Carrier timeout gate

This module isolates the Rule-A arithmetic at a carrier's slot-`+1` block.
When the current height was entered no earlier than the preceding round, the
two-round timeout delay is not mature at slot `opening_slot r + 1`. At a
justifiable height, `progReady` then agrees with `targetReady`, so the
progress-only arm of `CarrierPlusOneOutcomeAt` is impossible.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}










/-- If the carrier opening block itself entered its current height, the
current-height target was entered in the carrier round. This is the final
arithmetic step needed by a history argument that proves `T_h = P0`. -/
theorem carrierHeight_recentEntry_of_target_eq_opening
    (S : Setup V) (rho : Run V) {r : Round}
    (hself :
      (Protocol.derive_named S.E S.cfg
        (canonicalProposal S rho (S.hc.opening_slot r))).T_h =
          (canonicalProposal S rho (S.hc.opening_slot r)).erase) :
    r - 1 ≤ S.hc.round_of
      (Protocol.derive_named S.E S.cfg
        (canonicalProposal S rho (S.hc.opening_slot r))).T_h.slot := by
  have hslot : (canonicalProposal S rho (S.hc.opening_slot r)).slot =
      S.hc.opening_slot r :=
    proposedBlockAt_slot S rho (S.hc.opening_slot r)
      (canonicalProposal_spec S rho (S.hc.opening_slot r))
  have hround : S.hc.round_of
      (Protocol.derive_named S.E S.cfg
        (canonicalProposal S rho (S.hc.opening_slot r))).T_h.slot = r := by
    rw [hself, Proofs.NamedWire.erase_slot, hslot]
    exact round_of_opening_slot_eq S.hc r
  rw [hround]
  exact Nat.sub_le r 1


def CarrierRecentHeightEntryAt
    (S : Setup V) (rho : Run V) (r : Round) : Prop :=
  r - 1 ≤ S.hc.round_of
    (Protocol.derive_named S.E S.cfg
      (canonicalProposal S rho (S.hc.opening_slot r))).T_h.slot

/-- A carrier whose own opening proposal crossed has a recent height entry. -/
theorem carrierRecentHeightEntryAt_of_target_eq_opening
    (S : Setup V) (rho : Run V) {r : Round}
    (hself :
      (Protocol.derive_named S.E S.cfg
        (canonicalProposal S rho (S.hc.opening_slot r))).T_h =
          (canonicalProposal S rho (S.hc.opening_slot r)).erase) :
    CarrierRecentHeightEntryAt S rho r :=
  carrierHeight_recentEntry_of_target_eq_opening S rho hself



/-
/-- A same-height ancestor that entered the carrier's height no earlier than
The previous round's opening slot discharges the recent-entry condition.

This is the sound sufficient condition a producer can supply from an explicit
late crossing witness. -/
theorem carrierRecentHeightEntryAt_of_lateSameHeightAncestor
    (S: Setup V) (rho: Run V) {r: Round} {X: Block V}
    (hXP0: Block.Preceq X (proposedBlock S rho (S.hc.opening_slot r)))
    (hheight: (derived_state S.E S.cfg X).h =
      (derived_state S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot r))).h)
    (hself: (derived_state S.E S.cfg X).T_h = X)
    (hslot: S.hc.opening_slot (r - 1) ≤ X.slot):
    CarrierRecentHeightEntryAt S rho r:= by
  have htarget: (derived_state S.E S.cfg
      (proposedBlock S rho (S.hc.opening_slot r))).T_h = X:= by
    rw [derivedTarget_eq_of_preceq_same_height S.E S.cfg hXP0 hheight.symm]
    exact hself
  have hR: 0 < S.hc.R:= lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two
  have hmul: (r - 1) * S.hc.R ≤ X.slot:= by
    simpa only [Protocol.HealConfig.opening_slot] using hslot
  unfold CarrierRecentHeightEntryAt
  rw [htarget]
  exact (Nat.le_div_iff_mul_le hR).mpr hmul
-/





/-- A height entered in round `r - 1` or later cannot consume timeout rows at
slot `opening_slot r + 1` when the timeout delay is at least two full rounds. -/
theorem timeoutGate_closed_at_plusOne_of_enteredRoundPred_of_lowerBound
    (S : Setup V) {r : Round} {T : Block V}
    (hdelay : 2 * S.hc.R ≤ S.cfg.timeoutDelay)
    (hentered : r - 1 ≤ S.hc.round_of T.slot) :
    ¬ T.slot + S.cfg.timeoutDelay ≤ S.hc.opening_slot r + 1 := by
  suffices h : ¬ T.slot + 2 * S.hc.R ≤ S.hc.opening_slot r + 1 from
    fun hgate => h ((Nat.add_le_add_left hdelay
      T.slot).trans hgate)
  unfold Protocol.HealConfig.round_of at hentered
  have hR : 0 < S.hc.R :=
    lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two
  have hRtwo : 2 ≤ S.hc.R := S.hc.R_ge_two
  have hmul : (r - 1) * S.hc.R ≤ T.slot :=
    (Nat.le_div_iff_mul_le hR).mp hentered
  cases r with
  | zero =>
      simp only [Nat.zero_mul,
        Protocol.HealConfig.opening_slot, Nat.zero_mul]
      intro hmature
      have hstrict : 1 < 2 * S.hc.R := by omega
      have hlower : 2 * S.hc.R ≤ T.slot + 2 * S.hc.R :=
        Nat.le_add_left _ _
      exact (Nat.not_lt_of_ge (hlower.trans hmature)) hstrict
  | succ k =>
      simp only [Nat.succ_sub_one] at hmul
      unfold Protocol.HealConfig.opening_slot
      intro hmature
      have hopen : Nat.succ k * S.hc.R =
          k * S.hc.R + S.hc.R := Nat.succ_mul k S.hc.R
      rw [hopen] at hmature
      have hstrict :
          k * S.hc.R + S.hc.R + 1 < k * S.hc.R + 2 * S.hc.R := by
        omega
      have hlower : k * S.hc.R + 2 * S.hc.R ≤
          T.slot + 2 * S.hc.R := Nat.add_le_add_right hmul _
      exact (Nat.not_lt_of_ge (hlower.trans hmature)) hstrict

/-- The indexed delay family supplies the same two-round protection bound. -/
theorem timeoutGate_closed_at_plusOne_of_enteredRoundPred
    (S : Setup V) {r : Round} {T : Block V}
    (hdelay : TimeoutDelayBound S delayExtra)
    (hentered : r - 1 ≤ S.hc.round_of T.slot) :
    ¬ T.slot + S.cfg.timeoutDelay ≤ S.hc.opening_slot r + 1 :=
  timeoutGate_closed_at_plusOne_of_enteredRoundPred_of_lowerBound
    S (timeoutDelay_ge_twoRounds S hdelay) hentered




/-
/-- At a justifiable opening, `targetReady` is exactly the target-quorum test
in the slot-`+1` fold. -/
theorem plusOne_targetReady_eq_targetQuorum_of_nj_false
    (S: Setup V) (rho: Run V) {r: Round} {P0: Block V}
    (hnj: (derived_state S.E S.cfg P0).nj = false):
    let sigma:= Protocol.afterFin S.E (carrierPlusOneFold S rho r P0)
    Protocol.targetReady S.E sigma = sigma.targetQuorum S.E:= by
  dsimp only
  have hnjFold: (carrierPlusOneFold S rho r P0).nj = false:= by
    rw [carrierPlusOneFold_nj]
    exact hnj
  have hnjAfter:
      (Protocol.afterFin S.E (carrierPlusOneFold S rho r P0)).nj = false:= by
    rw [Protocol.afterFin_nj]
    exact hnjFold
  simp only [Protocol.targetReady, hnjAfter, Bool.not_false,
    Bool.true_and]

/-- Under the recent-entry timeout gate, the carrier's slot-`+1` block is
quiet or takes the target branch. The progress-only branch is impossible. -/
theorem plusOne_quiet_or_earlyTarget
    (S: Setup V) (rho: Run V) {r: Round} {P0: Block V}
    (hdelay: TimeoutDelayBound S delayExtra)
    (hentered: r - 1 ≤ S.hc.round_of
      (derived_state S.E S.cfg P0).T_h.slot)
    (hnj: (derived_state S.E S.cfg P0).nj = false):
    CarrierPlusOneNoHeightEventAt S rho r P0 ∨
      Protocol.targetReady S.E
        (Protocol.afterFin S.E (carrierPlusOneFold S rho r P0)) = true:= by
  have hprog:= plusOne_progReady_eq_targetQuorum
    S rho hdelay hentered
  have htarget:= plusOne_targetReady_eq_targetQuorum_of_nj_false
    S rho (r:= r) hnj
  cases carrierPlusOneOutcomeAt_exhaustive S rho r P0 with
  | quiet ht hp =>
      exact Or.inl { targetNotReady:= ht, progressNotReady:= hp }
  | earlyTarget ht =>
      exact Or.inr ht
  | earlyProgress ht hp =>
      have: False:= by
        rw [hprog, ← htarget, ht] at hp
        cases hp
      exact this.elim

/-- The target arm at slot `+1` is already a justification of the opening
height. -/
theorem plusOne_justifies_of_earlyTarget
    (S: Setup V) {rho: Run V} {r: Round} {P0: Block V}
    (hparent: Protocol.proposedParent S rho
      (S.hc.opening_slot r + 1) = P0)
    (htarget: Protocol.targetReady S.E
      (Protocol.afterFin S.E (carrierPlusOneFold S rho r P0)) = true):
    JustifiedAt S.E S.cfg
      (proposedBlock S rho (S.hc.opening_slot r + 1))
      (derived_state S.E S.cfg P0).T_h
      (derived_state S.E S.cfg P0).h:= by
  have hstate:= CarrierPlusOneOutcomeAt.earlyTarget_state
    (S:= S) (rho:= rho) hparent htarget
  exact by
    simpa only [JustifiedAt] using And.intro hstate.2.1 hstate.2.2.1

/-- Without a recent-entry premise, the slot-`+1` outcome is checkpoint-ready
or is already a numeric carrier advance. The progress-only arm is therefore
an escape success, not a failed finality phase. -/
theorem carrierPlusOne_checkpointReady_or_advance
    (S: Setup V) {rho: Run V} {r: Round}
    (hparent: Protocol.proposedParent S rho
      (S.hc.opening_slot r + 1) =
        proposedBlock S rho (S.hc.opening_slot r)):
    (JustifiedAt S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot r + 1))
        (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r))).T_h
        (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r))).h ∨
      ((derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r + 1))).h =
            (derived_state S.E S.cfg
              (proposedBlock S rho (S.hc.opening_slot r))).h ∧
        (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r + 1))).T_h =
            (derived_state S.E S.cfg
              (proposedBlock S rho (S.hc.opening_slot r))).T_h)) ∨
      CarrierAdvanceAt S rho r:= by
  cases carrierPlusOneOutcomeAt_exhaustive S rho r
      (proposedBlock S rho (S.hc.opening_slot r)) with
  | quiet ht hp =>
      exact Or.inl <| Or.inr <|
        plusOne_state_eq_of_parent_of_noHeightEvent S hparent
          { targetNotReady:= ht, progressNotReady:= hp }
  | earlyTarget ht =>
      exact Or.inl <| Or.inl <|
        plusOne_justifies_of_earlyTarget S hparent ht
  | earlyProgress ht hp =>
      have hstate:= CarrierPlusOneOutcomeAt.earlyProgress_state
        (S:= S) (rho:= rho) hparent ht hp
      apply Or.inr
      apply Or.inl
      unfold carrierOpeningHeight
      rw [hstate.1]
      exact Nat.lt_succ_self _
-/


/-
/-! ### The gate read at the entry's slot

`plusOne_noTimeoutConsumption` and everything above it only ever use the
recent-entry premise through `timeoutGate_closed_at_plusOne_of_enteredRoundPred`,
whose conclusion is a statement about the entry block's SLOT. Taking that
conclusion as the premise instead is strictly more general — the round form is
recovered by composing with that lemma — and it is what a caller with a slot
bound on the entry, rather than a round bound, can supply. -/

/-- The slot-keyed gate: the fold at the carrier's slot-`+1` block is before
timeout maturity whenever the entry's own slot is far enough back. -/
theorem plusOne_noTimeoutConsumption_of_gateShut
    (S: Setup V) (rho: Run V) {r: Round} {P0: Block V}
    (hgate: ¬ (derived_state S.E S.cfg P0).T_h.slot + S.cfg.timeoutDelay ≤
      S.hc.opening_slot r + 1):
    let sigma:= Protocol.afterFin S.E (carrierPlusOneFold S rho r P0)
    ¬ sigma.T_h.slot + S.cfg.timeoutDelay ≤ sigma.s:= by
  dsimp only
  intro hmature
  apply hgate
  simpa only [Protocol.afterFin_T_h, carrierPlusOneFold_T_h,
    afterFin_s, carrierPlusOneFold_s] using hmature

/-- With the slot-keyed gate shut, `progReady` reduces to the target quorum. -/
theorem plusOne_progReady_eq_targetQuorum_of_gateShut
    (S: Setup V) (rho: Run V) {r: Round} {P0: Block V}
    (hgate: ¬ (derived_state S.E S.cfg P0).T_h.slot + S.cfg.timeoutDelay ≤
      S.hc.opening_slot r + 1):
    let sigma:= Protocol.afterFin S.E (carrierPlusOneFold S rho r P0)
    Protocol.progReady S.E S.cfg sigma = sigma.targetQuorum S.E:= by
  dsimp only
  have hclosed:= plusOne_noTimeoutConsumption_of_gateShut S rho hgate
  have hmature: decide
      ((Protocol.afterFin S.E (carrierPlusOneFold S rho r P0)).T_h.slot +
          S.cfg.timeoutDelay ≤
        (Protocol.afterFin S.E (carrierPlusOneFold S rho r P0)).s) = false:= by
    simp only [decide_eq_false_iff_not]
    exact hclosed
  rw [Protocol.progReady, hmature]
  simp only [Bool.false_and, Bool.or_false]

/-- With the slot-keyed gate shut, the carrier's slot-`+1` block is quiet or
takes the target branch. -/
theorem plusOne_quiet_or_earlyTarget_of_gateShut
    (S: Setup V) (rho: Run V) {r: Round} {P0: Block V}
    (hgate: ¬ (derived_state S.E S.cfg P0).T_h.slot + S.cfg.timeoutDelay ≤
      S.hc.opening_slot r + 1)
    (hnj: (derived_state S.E S.cfg P0).nj = false):
    CarrierPlusOneNoHeightEventAt S rho r P0 ∨
      Protocol.targetReady S.E
        (Protocol.afterFin S.E (carrierPlusOneFold S rho r P0)) = true:= by
  have hprog:= plusOne_progReady_eq_targetQuorum_of_gateShut S rho hgate
  have htarget:= plusOne_targetReady_eq_targetQuorum_of_nj_false
    S rho (r:= r) hnj
  cases carrierPlusOneOutcomeAt_exhaustive S rho r P0 with
  | quiet ht hp =>
      exact Or.inl { targetNotReady:= ht, progressNotReady:= hp }
  | earlyTarget ht =>
      exact Or.inr ht
  | earlyProgress ht hp =>
      have hfalse: False:= by
        rw [hprog, ← htarget, ht] at hp
        cases hp
      exact hfalse.elim

/-- The carrier's checkpoint open from the slot-keyed gate. -/
theorem carrierPlusOne_checkpointReady_of_gateShut
    (S: Setup V) {rho: Run V} {r: Round} {P0: Block V}
    (hparent: Protocol.proposedParent S rho
      (S.hc.opening_slot r + 1) = P0)
    (hgate: ¬ (derived_state S.E S.cfg P0).T_h.slot + S.cfg.timeoutDelay ≤
      S.hc.opening_slot r + 1)
    (hnj: (derived_state S.E S.cfg P0).nj = false):
    JustifiedAt S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot r + 1))
        (derived_state S.E S.cfg P0).T_h
        (derived_state S.E S.cfg P0).h ∨
      ((derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r + 1))).h =
            (derived_state S.E S.cfg P0).h ∧
        (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r + 1))).T_h =
            (derived_state S.E S.cfg P0).T_h):= by
  rcases plusOne_quiet_or_earlyTarget_of_gateShut S rho hgate hnj with
      hquiet | hearly
  · exact Or.inr (plusOne_state_eq_of_parent_of_noHeightEvent S hparent hquiet)
  · exact Or.inl (plusOne_justifies_of_earlyTarget S hparent hearly)

/-- The carrier's slot-`+1` block either justifies the opening checkpoint or
preserves its height and target. This is the first-checkpoint input used by
the recurring-finality phase. -/
theorem carrierPlusOne_checkpointReady
    (S: Setup V) {rho: Run V} {r: Round} {P0: Block V}
    (hparent: Protocol.proposedParent S rho
      (S.hc.opening_slot r + 1) = P0)
    (hdelay: TimeoutDelayBound S delayExtra)
    (hentered: r - 1 ≤ S.hc.round_of
      (derived_state S.E S.cfg P0).T_h.slot)
    (hnj: (derived_state S.E S.cfg P0).nj = false):
    JustifiedAt S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot r + 1))
        (derived_state S.E S.cfg P0).T_h
        (derived_state S.E S.cfg P0).h ∨
      ((derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r + 1))).h =
            (derived_state S.E S.cfg P0).h ∧
        (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r + 1))).T_h =
            (derived_state S.E S.cfg P0).T_h):= by
  rcases plusOne_quiet_or_earlyTarget S rho hdelay hentered hnj with
      hquiet | hearly
  · exact Or.inr (plusOne_state_eq_of_parent_of_noHeightEvent
      S hparent hquiet)
  · exact Or.inl (plusOne_justifies_of_earlyTarget S hparent hearly)

-/




/-
/-- The unconditional slot-`+1` trichotomy, with the progress-only arm
carrying its own state. The new height entry is the `+1` block itself, whose
`round_of` is the carrier's own round. -/
theorem carrierPlusOne_checkpointReady_or_burn
    (S: Setup V) {rho: Run V} {r: Round}
    (hparent: Protocol.proposedParent S rho
      (S.hc.opening_slot r + 1) =
        proposedBlock S rho (S.hc.opening_slot r)):
    (JustifiedAt S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot r + 1))
        (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r))).T_h
        (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r))).h ∨
      ((derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r + 1))).h =
            (derived_state S.E S.cfg
              (proposedBlock S rho (S.hc.opening_slot r))).h ∧
        (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r + 1))).T_h =
            (derived_state S.E S.cfg
              (proposedBlock S rho (S.hc.opening_slot r))).T_h)) ∨
      CarrierBurnAt S rho r:= by
  cases carrierPlusOneOutcomeAt_exhaustive S rho r
      (proposedBlock S rho (S.hc.opening_slot r)) with
  | quiet ht hp =>
      exact Or.inl <| Or.inr <|
        plusOne_state_eq_of_parent_of_noHeightEvent S hparent
          { targetNotReady:= ht, progressNotReady:= hp }
  | earlyTarget ht =>
      exact Or.inl <| Or.inl <|
        plusOne_justifies_of_earlyTarget S hparent ht
  | earlyProgress ht hp =>
      have hstate:= CarrierPlusOneOutcomeAt.earlyProgress_state
        (S:= S) (rho:= rho) hparent ht hp
      exact Or.inr { height:= hstate.1, target:= hstate.2.2.2 }
-/



/-
/-- The canonical round record gives exact honest target rows once its
existing Rule B lock-alignment residual is supplied.

**Open (Rule B residual).** A record with an empty target can retain a
different compatible lock. `CanonicalRegimeRoundAt` does not contain lock
history, so its target and timeout histories cannot exclude that case. -/
theorem carrierRows_exactTargets
    (S: Setup V) {rho: Run V}
    (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hmajority: HonestWeightMajority S rho.honest)
    {q0 r: Round}
    (hexec: Protocol.CanonicalSuffixExecution S rho q0)
    (hround: CanonicalRegimeRoundAt S rho q0 r)
    (hactivity: CanonicalGradeFloorActivityResidualAt S rho r)
    (habove: honestHMaxAt S rho (S.a q0) <
      (derived_state S.E S.cfg
        (proposedBlock S rho (S.hc.opening_slot r))).h)
    (hnj: (derived_state S.E S.cfg
      (proposedBlock S rho (S.hc.opening_slot r))).nj = false)
    (hlockAligned: ∀ v ∈ rho.honest,
      SuccessorTargetLockAlignmentAt
        (rho.stateBeforeTime S (S.a r) v).Λ
        (actionAttestationAt S rho v r).finality_pair
        (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r))).h
        (derived_state S.E S.cfg
          (proposedBlock S rho (S.hc.opening_slot r))).T_h.root):
    ∃ C, GradeFormsAt S rho r C ∧
      ∀ v ∈ rho.honest,
        (actionAttestationAt S rho v r).height_pair =
          HeightPair.target
            (derived_state S.E S.cfg
              (proposedBlock S rho (S.hc.opening_slot r))).h
            (derived_state S.E S.cfg
              (proposedBlock S rho (S.hc.opening_slot r))).T_h.root:= by
  obtain ⟨C, hgrade, hbelow⟩:=
    hround.exists_gradeFloor hmajority hactivity
  have hres: CanonicalCarrierRegimeResidualAt S rho r C:=
    canonicalCarrierRegimeResidualAt_of_fresh_records S adm hgrade
      { gradeBelowOpening:= hbelow
        actionBatchAligned:= hround.actionBatchAligned }
      { successorRecord:= hround.successorTargetRecordAt habove hnj
        lockAlignment:= hlockAligned }
  have hreg: CanonicalCarrierRegimeAt S rho r C:=
    canonicalCarrierRegimeAt_of_residual S hres
  have hhor: S.a r ≤ rho.horizon:= by
    have htime: Protocol.confirmation_time S.E (S.hc.opening_slot r) ≤
        Protocol.confirmation_time S.E (S.hc.opening_slot r + 2):=
      confirmation_time_mono_timeoutGate S.E (Nat.le_add_right _ _)
    have ha: S.a r ≤
        Protocol.confirmation_time S.E (S.hc.opening_slot r + 2):= by
      simpa only [Setup.a, Protocol.a_eq_confirmation_time] using htime
    exact ha.trans hround.inHorizon
  exact ⟨C, hgrade, carrierRound_firstTargetRows S adm hcom hmajority
    hexec hround.afterBoundary hround.carrier hhor hreg hnj⟩
-/

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
