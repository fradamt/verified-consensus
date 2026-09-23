module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.W4StableWriteDuty
public import DecoupledConsensusProofs.Protocol.Grades.W4StableGrowthGSTZero
public import DecoupledConsensusInternal.Definitions.StableOutput

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel
namespace Proofs
namespace W4StableWrite

open Internal Execution
open Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Slot and time arithmetic of the pre-carrier opening -/

private theorem openingSlot_two_after_le (S : Setup V) {r q : Round}
    (h : r < q) : S.hc.opening_slot r + 2 ≤ S.hc.opening_slot q := by
  have hstep : S.hc.opening_slot r + 2 ≤ S.hc.opening_slot (r + 1) := by
    simp only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add_left S.hc.R_ge_two (r * S.hc.R)
  exact hstep.trans
    (by
      simpa only [Protocol.HealConfig.opening_slot] using
        Nat.mul_le_mul_right S.hc.R (Nat.succ_le_of_lt h))

private theorem action_lt_proposal (S : Setup V) {r q : Round} (h : r < q) :
    S.a r < Protocol.proposal_time S.E (S.hc.opening_slot q) :=
  lt_of_lt_of_le (Protocol.action_lt_proposal_time_two_after S r)
    (Protocol.proposal_time_mono S.E (openingSlot_two_after_le S h))

/-- The round-`q` action instant is at or before the round-`(q+1)` confirmation
duty: the next opening is at least two slots later, and the support cutoff is
monotone in the slot. -/
theorem action_le_nextDuty (S : Setup V) (q : Round) :
    S.a q ≤ dutyTime S (q + 1) := by
  have hstep : S.hc.opening_slot q + 1 ≤ S.hc.opening_slot (q + 1) := by
    simp only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add_left
      ((by decide : (1 : Nat) ≤ 2).trans S.hc.R_ge_two) (q * S.hc.R)
  rw [← opening_confirmation_time_eq_action S q,
    Protocol.confirmation_time_eq_support_cutoff_succ]
  exact Proofs.Optimistic.support_cutoff_mono S.E hstep

#print axioms action_le_nextDuty

/-- The round-`r` confirmation duty is at or before the round-`r` action
instant. -/
theorem dutyTime_le_action (S : Setup V) (r : Round) : dutyTime S r ≤ S.a r := by
  simp only [dutyTime, Protocol.support_cutoff, Setup.a,
    Protocol.HealConfig.a, Protocol.HealConfig.opening_slot, Env.t, slotStart]
  have hΔ : (0 : Time) < S.E.Δ := S.E.Δ_pos
  ring_nf
  nlinarith

#print axioms dutyTime_le_action

/-- The safety boundary of a start slot is at or before every later round's
action instant. -/
theorem confirmation_start_le_action (S : Setup V) {start : Slot} {r : Round}
    (hstart : start ≤ S.hc.opening_slot r) :
    Protocol.confirmation_time S.E start ≤ S.a r := by
  rw [← opening_confirmation_time_eq_action S r,
    Protocol.confirmation_time_eq_support_cutoff_succ,
    Protocol.confirmation_time_eq_support_cutoff_succ]
  exact Proofs.Optimistic.support_cutoff_mono S.E (Nat.succ_le_succ hstart)

#print axioms confirmation_start_le_action

/-! ## The two step lemmas, parametric in the safety boundary -/


/-- The strict clause of `StableRecordGrowthFrom`, from any boundary `t0`.
Record nesting puts the round-`r` stable record below the round-`r`
confirmation record, confirmation monotonicity puts that below the proposal,
and slot freshness separates them. The `t0 = 0` instance is w4-c1's
`w4_stable_prec_honestProposal`. -/
theorem stable_prec_honestProposal_from
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho) {t0 : Time}
    (hmono : ConfirmationMonotoneFrom S rho t0)
    {r q : Round} (hrq : r < q) (ht0 : t0 ≤ S.a r) {B : NamedBlock V}
    (hB : proposedBlockAt S rho (S.hc.opening_slot q) = some B)
    (hconf : ∀ v ∈ rho.honest,
      (rho.storeAt S v (S.a q)).latest_confirmed = B.erase)
    (hhor : S.a q ≤ rho.horizon) :
    ∀ v ∈ rho.honest,
      Block.Prec (rho.storeAt S v (S.a r)).latest_stable B.erase := by
  intro v hv
  have hslotB : B.erase.slot = S.hc.opening_slot q := by
    rw [Proofs.NamedWire.erase_slot]
    exact DecoupledConsensusModel.Proofs.Optimistic.proposedBlockAt_slot S rho (S.hc.opening_slot q) hB
  have hpos : 0 < S.hc.opening_slot q := by
    have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le r) hrq
    simpa only [Protocol.HealConfig.opening_slot] using
      Nat.mul_pos hq (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have harq : S.a r ≤ S.a q := Assembly.a_mono S (Nat.le_of_lt hrq)
  have hnest : Block.Preceq (rho.storeAt S v (S.a r)).latest_stable
      (rho.storeAt S v (S.a r)).latest_confirmed :=
    StableRecord.stableBelowConfirmed_storeAt S adm.toNamedScheduleWellFormed v (S.a r)
  have hstep : Block.Preceq (rho.storeAt S v (S.a r)).latest_confirmed
      (rho.storeAt S v (S.a q)).latest_confirmed :=
    hmono v hv (S.a r) (S.a q) ht0 harq hhor
  have hle : Block.Preceq (rho.storeAt S v (S.a r)).latest_stable B.erase := by
    rw [← hconf v hv]
    exact Block.preceq_trans hnest hstep
  have hmem : (rho.storeAt S v (S.a r)).latest_stable ∈ (rho.storeAt S v (S.a r)).T :=
    (Proofs.NamedRuntime.readAt_invariants S rho (S.a r) v).1.2.2.2
  have hslot : (rho.storeAt S v (S.a r)).latest_stable.slot < S.hc.opening_slot q :=
    w4_block_slot_lt_of_mem_storeAt S adm hpos (action_lt_proposal S hrq) hmem
  have hne : (rho.storeAt S v (S.a r)).latest_stable ≠ B.erase := by
    intro heq
    rw [heq, hslotB] at hslot
    exact (Nat.lt_irrefl _) hslot
  simp only [Block.Prec, Block.prec, hne, decide_false, Bool.not_false,
    Bool.true_and]
  exact hle

#print axioms stable_prec_honestProposal_from


/-- Retention of one duty write to every later read, and its exposure in
`stableOutputAt`, from any boundary `t0`. The `t0 = 0` instance is w4-c1's
`w4_stable_retained_of_duty`. -/
theorem stable_retained_of_duty_from
    (S : Setup V) {rho : Run V} {t0 : Time}
    (hcanon : StableRecordCanonicalFrom S rho t0)
    {P : Block V} {duty : Time} (hduty0 : t0 ≤ duty)
    (hwrite : ∀ v ∈ rho.honest,
      Block.Preceq P (rho.storeAt S v duty).latest_stable)
    {t : Time} (ht : duty ≤ t) (hthor : t ≤ rho.horizon) :
    ∀ v ∈ rho.honest,
      Block.Preceq P (rho.storeAt S v t).latest_stable ∧
        Block.Preceq P (stableOutputAt S rho v t) := by
  intro v hv
  have ht0 : t0 ≤ t := hduty0.trans ht
  have hlat : Block.Preceq P (rho.storeAt S v t).latest_stable :=
    Block.preceq_trans (hwrite v hv)
      (hcanon.monotone v hv duty t hduty0 ht hthor)
  refine ⟨hlat, ?_⟩
  have hfin : Block.compatible (rho.storeAt S v t).latest_stable
      (rho.storeAt S v t).F = true :=
    hcanon.finality v hv v hv t t ht0 ht0 hthor hthor
  exact NamedOutageClosure.preceq_get_stable (rho.storeAt S v t).core hlat
    (Protocol.compatible_of_preceq_of_compatible hlat hfin)

#print axioms stable_retained_of_duty_from





/-- The recurrence gap is at or below the widened deadline. -/
theorem le_widened_deadline (S : Setup V) (gap : Round) :
    gap ≤ gap + S.hc.η_SG - 1 := by
  have harith : ∀ a b : Nat, 1 ≤ b → a ≤ a + b - 1 := by
    intro a b hb
    omega
  exact harith gap S.hc.η_SG S.hc.η_SG_ge_one

#print axioms le_widened_deadline

/-! ## The growth field -/





/-- The proposal at the consuming read: in the reader's tree, viable there, and
compatible with the reader's FG root. earlier's counterpart is
`postGain_proposal_viable_at_consuming_read`. -/
def ProposalViableAtDuty (S : Setup V) (rho : Run V) (q : Round) (P : Block V)
    (v : V) : Prop :=
  P ∈ (NamedActionReads.confirmationReadAt S rho v (dutyTime S (q + 1))).st.core.T ∧
  Protocol.viable
      (NamedActionReads.confirmationReadAt S rho v (dutyTime S (q + 1))).st.core.σ
      (NamedActionReads.confirmationReadAt S rho v (dutyTime S (q + 1))).st.core.h_max
      (NamedActionReads.confirmationReadAt S rho v (dutyTime S (q + 1))).st.core.T P = true ∧
  Block.compatible P (Protocol.get_fg_root
    (NamedActionReads.confirmationReadAt S rho v
      (dutyTime S (q + 1))).st.core.toHealing.toFG) = true

/-- The reader's own frozen round-`(q+1)` G2 root covers the proposal, for the
readers that still hold it in their finality-filtered tree. earlier's counterpart
is `postGain_localFrameRoot_above_proposal`; that is where the round's
grade-forming participation is consumed (`WeakContinuationParticipation`). -/
def LocalG2CoverAtDuty (S : Setup V) (rho : Run V) (q : Round) (P : Block V)
    (v : V) : Prop :=
  P ∈ Protocol.get_filtered_block_tree
      (NamedActionReads.confirmationReadAt S rho v
        (dutyTime S (q + 1))).st.core.toHealing.toFG →
    ∃ raw : Block V,
      DecoupledConsensusModel.Protocol.freezeRoot S.E
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g2) v).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g2) v).st.core.F
        S.hc.η_SG (q + 1) (DecoupledConsensusModel.Protocol.early S.E S.hc (q + 1) .g2)
        (DecoupledConsensusModel.Protocol.late S.E S.hc (q + 1) .g2) = some raw ∧
      Block.Preceq P raw



/-- The reader's own G2 grade for the proposal at the round-`(q+1)` G2 domain
read gives `LocalG2CoverAtDuty`. This is the per-reader twin of
`dutyCoverAt_of_namedGradeFormsAt`: the freeze root of a graded block covers
it, and the duty-read membership the target assumes is not needed.

earlier produces the `storeGrade` premise from the relative carrier window, the
round's grade-forming majority and the action-carrier cover
(`postGain_storeGrade_g2_of_relativeCarrierWindow_and_cover`). -/
theorem localG2CoverAtDuty_of_storeGrade
    (S : Setup V) {rho : Run V} {q : Round} {P : Block V} {v : V}
    (hmem : P ∈ (Internal.PhaseGrades.readAt S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g2) v).st.core.T)
    (hgrade : Internal.PhaseGrades.storeGrade S.E S.hc
      (Internal.PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g2) v).st (q + 1) .g2 P = true) :
    LocalG2CoverAtDuty S rho q P v := by
  intro _
  apply NamedOutageClosure.q10_freeze_of_graded S.E
    (NamedRun.stateBeforeTime S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g2) v).st.core.toHealing.gradeView
    (NamedRun.stateBeforeTime S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + 1) .g2) v).st.core.F
    S.hc.η_SG (q + 1) (NamedOutageClosure.q10_early_le_late S (q + 1) .g2)
  · simpa only [Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hmem
  · simpa only [Internal.PhaseGrades.storeGrade, Internal.PhaseGrades.phaseGrade] using hgrade

#print axioms localG2CoverAtDuty_of_storeGrade



/-- `ProposalViableAtDuty` at an arbitrary duty round. -/
def ProposalViableAtDutyRound (S : Setup V) (rho : Run V) (d : Round)
    (P : Block V) (v : V) : Prop :=
  P ∈ (NamedActionReads.confirmationReadAt S rho v (dutyTime S d)).st.core.T ∧
  Protocol.viable
      (NamedActionReads.confirmationReadAt S rho v (dutyTime S d)).st.core.σ
      (NamedActionReads.confirmationReadAt S rho v (dutyTime S d)).st.core.h_max
      (NamedActionReads.confirmationReadAt S rho v (dutyTime S d)).st.core.T P = true ∧
  Block.compatible P (Protocol.get_fg_root
    (NamedActionReads.confirmationReadAt S rho v
      (dutyTime S d)).st.core.toHealing.toFG) = true

/-- `LocalG2CoverAtDuty` at an arbitrary duty round. -/
def LocalG2CoverAtDutyRound (S : Setup V) (rho : Run V) (d : Round)
    (P : Block V) (v : V) : Prop :=
  P ∈ Protocol.get_filtered_block_tree
      (NamedActionReads.confirmationReadAt S rho v
        (dutyTime S d)).st.core.toHealing.toFG →
    ∃ raw : Block V,
      DecoupledConsensusModel.Protocol.freezeRoot S.E
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) v).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2) v).st.core.F
        S.hc.η_SG d (DecoupledConsensusModel.Protocol.early S.E S.hc d .g2)
        (DecoupledConsensusModel.Protocol.late S.E S.hc d .g2) = some raw ∧
      Block.Preceq P raw



theorem localG2CoverAtDuty_eq_round (S : Setup V) (rho : Run V) (q : Round)
    (P : Block V) (v : V) :
    LocalG2CoverAtDuty S rho q P v = LocalG2CoverAtDutyRound S rho (q + 1) P v :=
  rfl

#print axioms localG2CoverAtDuty_eq_round

/-- **Per-reader duty cover at an arbitrary duty round.** Same split as
`w4FreezeCoverFrom_of_viable_and_localG2`: the FG arm is what the active arm's
failure means, so viability plus the reader's own grade is enough. -/
theorem dutyCoverAt_of_viable_and_localG2
    (S : Setup V) {rho : Run V} {d : Round} {P : Block V} {v : V}
    (hviable : ProposalViableAtDutyRound S rho d P v)
    (hgrade : LocalG2CoverAtDutyRound S rho d P v) :
    DutyCoverAt S rho d P v := by
  obtain ⟨hmem, hviab, hrootCompat⟩ := hviable
  set n := NamedActionReads.confirmationReadAt S rho v (dutyTime S d) with hn
  have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
    S rho (dutyTime S d) v
  have hFroot : Block.Preceq n.st.core.F
      (Protocol.get_fg_root n.st.core.toHealing.toFG) :=
    StoreFinality.finalized_preceq_fgRoot (by
      simpa only [hn, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using hFJ)
  rcases (show Block.Preceq P
      (Protocol.get_fg_root n.st.core.toHealing.toFG) ∨
      Block.Preceq (Protocol.get_fg_root n.st.core.toHealing.toFG) P by
    simpa only [Block.compatible, Bool.or_eq_true] using hrootCompat) with hPr | hrP
  · exact Or.inr hPr
  · have hfiltered : P ∈ Protocol.get_filtered_block_tree
        n.st.core.toHealing.toFG := by
      simp only [Protocol.get_filtered_block_tree,
        Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
        Protocol.finalized_descendants, Finset.mem_filter,
        Protocol.Store.toHealing]
      exact ⟨⟨⟨hmem, Block.preceq_trans hFroot hrP⟩, hviab⟩, hrP⟩
    exact Or.inl ⟨hfiltered, hgrade hfiltered⟩

#print axioms dutyCoverAt_of_viable_and_localG2

/-! ## Closing the reader's grade over the round's grade-forming majority -/





/-! ## Consuming the widened deadline: a write up to `η_SG` rounds later

The point of the user's constant (`Liveness.lean:46-54`) is that the stable
root may lag: under an awake-window majority the round's G2 root is formed from
votes over the expiry window, so the duty that first carries an opening
proposal into the stable record can be up to `η_SG` rounds after that opening,
not necessarily the very next one. `W4StableWriteFrom` fixes the duty at the
next round and therefore does not use the extra rounds; this additive variant
lets the duty range over `(q, q + η_SG]`, which is exactly what the widened
deadline pays for. -/

theorem dutyTime_mono (S : Setup V) {a b : Round} (h : a ≤ b) :
    dutyTime S a ≤ dutyTime S b := by
  simp only [dutyTime]
  exact Proofs.Optimistic.support_cutoff_mono S.E
    (Nat.mul_le_mul_right S.hc.R h)

#print axioms dutyTime_mono

/-- The lagged write obligation the widened deadline allows. -/
def W4StableWriteWithinFrom (S : Setup V) (rho : Run V) : Prop :=
  ∀ q : Round, 0 < q →
    S.E.proposer (S.hc.opening_slot q) ∈ rho.honest →
    ∀ P : NamedBlock V, proposedBlockAt S rho (S.hc.opening_slot q) = some P →
      S.a (q + S.hc.η_SG) ≤ rho.horizon →
      ∃ q' : Round, q < q' ∧ q' ≤ q + S.hc.η_SG ∧
        ∀ v ∈ rho.honest,
          Block.Preceq P.erase (rho.storeAt S v (dutyTime S q')).latest_stable

/-- **Stable-record growth at the widened public deadline, from a lagged
write.** Same witness selection as `stableRecordGrowthFrom_of_openingWrite`:
the honest opening before the recurrence carrier. The write may now be at any
duty within `η_SG` rounds of that opening. -/
theorem stableRecordGrowthFrom_of_openingWriteWithin
    (S : Setup V) {rho : Run V} (core : AdmissibleCore S rho)
    {start : Slot} {gap : Round} {t0 : Time}
    (ht0 : t0 ≤ Protocol.confirmation_time S.E start)
    (hrec : ProposerOpeningCarrierRecurrence S rho gap)
    (hmono : ConfirmationMonotoneFrom S rho t0)
    (hprops : UserProposalsConfirmedAfter S rho start)
    (hcanon : StableRecordCanonicalFrom S rho t0)
    (hwrite : W4StableWriteWithinFrom S rho) :
    StableRecordGrowthFrom S rho start (gap + S.hc.η_SG - 1) := by
  intro r hstart hhor
  classical
  obtain ⟨c, hclo, hchi, _hp2, hp1, _hcar⟩ := hrec r
  have hc2 : 2 ≤ c := le_trans (Nat.le_add_left 2 r) hclo
  have hc1 : 1 ≤ c := le_trans (by decide : (1 : Nat) ≤ 2) hc2
  obtain ⟨q, rfl⟩ : ∃ q : Round, c = q + 1 :=
    ⟨c - 1, (Nat.sub_add_cancel hc1).symm⟩
  have hrq : r < q := Nat.lt_of_succ_le (Nat.le_of_succ_le_succ hclo)
  have hqpos : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le r) hrq
  have harith : ∀ a b e k : Nat, 1 ≤ e → a + 1 ≤ b + k →
      a + e ≤ b + (k + e - 1) := by
    intro a b e k he hab
    omega
  have hlag : q + S.hc.η_SG ≤ r + (gap + S.hc.η_SG - 1) :=
    harith q r S.hc.η_SG gap S.hc.η_SG_ge_one hchi
  have hcgap : S.a (q + 1) ≤ S.a (r + (gap + S.hc.η_SG - 1)) :=
    Assembly.a_mono S
      (hchi.trans (Nat.add_le_add_left (le_widened_deadline S gap) r))
  have hchor : S.a (q + 1) ≤ rho.horizon := hcgap.trans hhor
  have hlagHor : S.a (q + S.hc.η_SG) ≤ rho.horizon :=
    (Assembly.a_mono S hlag).trans hhor
  have hqhor : S.a q ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_succ q)).trans hchor
  have hp1' : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest := by
    simpa only [Nat.add_sub_cancel] using hp1
  have hopen : S.hc.opening_slot r < S.hc.opening_slot q :=
    Nat.mul_lt_mul_of_pos_right hrq
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hstartq : start < S.hc.opening_slot q := lt_of_le_of_lt hstart hopen
  have hconfHor :
      Protocol.confirmation_time S.E (S.hc.opening_slot q) ≤ rho.horizon := by
    simpa only [opening_confirmation_time_eq_action S q] using hqhor
  obtain ⟨B, hB, hrecord, -⟩ :=
    hprops (S.hc.opening_slot q) hstartq hconfHor hp1'
  have hrecord' : ∀ v ∈ rho.honest,
      (rho.storeAt S v (S.a q)).latest_confirmed = B.erase := by
    intro v hv
    simpa only [opening_confirmation_time_eq_action S q] using hrecord v hv
  obtain ⟨q', hqq', hq'le, hwrite'⟩ := hwrite q hqpos hp1' B hB hlagHor
  have ht0r : t0 ≤ S.a r := ht0.trans (confirmation_start_le_action S hstart)
  have ht0duty : t0 ≤ dutyTime S q' :=
    ht0r.trans ((Assembly.a_mono S (Nat.le_of_lt hrq)).trans
      ((action_le_nextDuty S q).trans (dutyTime_mono S hqq')))
  refine ⟨B, ⟨S.hc.opening_slot q, hopen, hp1', hB⟩, ?_⟩
  intro v hv
  refine ⟨stable_prec_honestProposal_from S core hmono hrq ht0r hB hrecord' hqhor v hv,
    ?_⟩
  intro t ht hthor
  have hdutyle : dutyTime S q' ≤ t :=
    ((dutyTime_le_action S q').trans (Assembly.a_mono S hq'le)).trans
      ((Assembly.a_mono S hlag).trans ht)
  exact stable_retained_of_duty_from S hcanon ht0duty hwrite' hdutyle hthor v hv

#print axioms stableRecordGrowthFrom_of_openingWriteWithin

/-- **The lagged write above a start slot.** Same as `W4StableWriteWithinFrom`
but restricted to openings strictly after `start`, which is what the after-GST
branch has and what its viability step needs. -/
def W4StableWriteWithinFromAbove (S : Setup V) (rho : Run V) (start : Slot) : Prop :=
  ∀ q : Round, 0 < q →
    start < S.hc.opening_slot q →
    S.E.proposer (S.hc.opening_slot q) ∈ rho.honest →
    ∀ P : NamedBlock V, proposedBlockAt S rho (S.hc.opening_slot q) = some P →
      S.a (q + S.hc.η_SG) ≤ rho.horizon →
      ∃ q' : Round, q < q' ∧ q' ≤ q + S.hc.η_SG ∧
        ∀ v ∈ rho.honest,
          Block.Preceq P.erase (rho.storeAt S v (dutyTime S q')).latest_stable

/-- **Stable-record growth at the widened deadline from a lagged write above
the start.** The proof of `stableRecordGrowthFrom_of_openingWriteWithin`
already derives `start < S.hc.opening_slot q` for the selected opening; this
variant simply hands that fact to the write. -/
theorem stableRecordGrowthFrom_of_openingWriteWithinAbove
    (S : Setup V) {rho : Run V} (core : AdmissibleCore S rho)
    {start : Slot} {gap : Round} {t0 : Time}
    (ht0 : t0 ≤ Protocol.confirmation_time S.E start)
    (hrec : ProposerOpeningCarrierRecurrence S rho gap)
    (hmono : ConfirmationMonotoneFrom S rho t0)
    (hprops : UserProposalsConfirmedAfter S rho start)
    (hcanon : StableRecordCanonicalFrom S rho t0)
    (hwrite : W4StableWriteWithinFromAbove S rho start) :
    StableRecordGrowthFrom S rho start (gap + S.hc.η_SG - 1) := by
  intro r hstart hhor
  classical
  obtain ⟨c, hclo, hchi, _hp2, hp1, _hcar⟩ := hrec r
  have hc2 : 2 ≤ c := le_trans (Nat.le_add_left 2 r) hclo
  have hc1 : 1 ≤ c := le_trans (by decide : (1 : Nat) ≤ 2) hc2
  obtain ⟨q, rfl⟩ : ∃ q : Round, c = q + 1 :=
    ⟨c - 1, (Nat.sub_add_cancel hc1).symm⟩
  have hrq : r < q := Nat.lt_of_succ_le (Nat.le_of_succ_le_succ hclo)
  have hqpos : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le r) hrq
  have harith : ∀ a b e k : Nat, 1 ≤ e → a + 1 ≤ b + k →
      a + e ≤ b + (k + e - 1) := by
    intro a b e k he hab
    omega
  have hlag : q + S.hc.η_SG ≤ r + (gap + S.hc.η_SG - 1) :=
    harith q r S.hc.η_SG gap S.hc.η_SG_ge_one hchi
  have hcgap : S.a (q + 1) ≤ S.a (r + (gap + S.hc.η_SG - 1)) :=
    Assembly.a_mono S
      (hchi.trans (Nat.add_le_add_left (le_widened_deadline S gap) r))
  have hchor : S.a (q + 1) ≤ rho.horizon := hcgap.trans hhor
  have hlagHor : S.a (q + S.hc.η_SG) ≤ rho.horizon :=
    (Assembly.a_mono S hlag).trans hhor
  have hqhor : S.a q ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_succ q)).trans hchor
  have hp1' : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest := by
    simpa only [Nat.add_sub_cancel] using hp1
  have hopen : S.hc.opening_slot r < S.hc.opening_slot q :=
    Nat.mul_lt_mul_of_pos_right hrq
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hstartq : start < S.hc.opening_slot q := lt_of_le_of_lt hstart hopen
  have hconfHor :
      Protocol.confirmation_time S.E (S.hc.opening_slot q) ≤ rho.horizon := by
    simpa only [opening_confirmation_time_eq_action S q] using hqhor
  obtain ⟨B, hB, hrecord, -⟩ :=
    hprops (S.hc.opening_slot q) hstartq hconfHor hp1'
  have hrecord' : ∀ v ∈ rho.honest,
      (rho.storeAt S v (S.a q)).latest_confirmed = B.erase := by
    intro v hv
    simpa only [opening_confirmation_time_eq_action S q] using hrecord v hv
  obtain ⟨q', hqq', hq'le, hwrite'⟩ := hwrite q hqpos hstartq hp1' B hB hlagHor
  have ht0r : t0 ≤ S.a r := ht0.trans (confirmation_start_le_action S hstart)
  have ht0duty : t0 ≤ dutyTime S q' :=
    ht0r.trans ((Assembly.a_mono S (Nat.le_of_lt hrq)).trans
      ((action_le_nextDuty S q).trans (dutyTime_mono S hqq')))
  refine ⟨B, ⟨S.hc.opening_slot q, hopen, hp1', hB⟩, ?_⟩
  intro v hv
  refine ⟨stable_prec_honestProposal_from S core hmono hrq ht0r hB hrecord' hqhor v hv,
    ?_⟩
  intro t ht hthor
  have hdutyle : dutyTime S q' ≤ t :=
    ((dutyTime_le_action S q').trans (Assembly.a_mono S hq'le)).trans
      ((Assembly.a_mono S hlag).trans ht)
  exact stable_retained_of_duty_from S hcanon ht0duty hwrite' hdutyle hthor v hv

#print axioms stableRecordGrowthFrom_of_openingWriteWithinAbove

/-- **The lagged write above the start from a per-reader duty cover.** -/
theorem w4StableWriteWithinFromAbove_of_dutyCover
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    (sch : ScheduleWellFormed S rho) {start : Slot}
    (hchoice : ∀ q : Round, 0 < q →
      start < S.hc.opening_slot q →
      S.E.proposer (S.hc.opening_slot q) ∈ rho.honest →
      ∀ P : NamedBlock V, proposedBlockAt S rho (S.hc.opening_slot q) = some P →
        S.a (q + S.hc.η_SG) ≤ rho.horizon →
        ∃ d : Round, q < d ∧ d ≤ q + S.hc.η_SG ∧
          ∀ v ∈ rho.honest, DutyCoverAt S rho d P.erase v) :
    W4StableWriteWithinFromAbove S rho start := by
  intro q hq hstartq hprop P hP hhor
  obtain ⟨d, hqd, hdle, hnode⟩ := hchoice q hq hstartq hprop P hP hhor
  refine ⟨d, hqd, hdle, ?_⟩
  have hdpos : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le q) hqd
  have hdhor : dutyTime S d ≤ rho.horizon :=
    (dutyTime_le_action S d).trans ((Assembly.a_mono S hdle).trans hhor)
  exact stable_preceq_at_duty_of_dutyCover S core sch hdpos hnode hdhor

#print axioms w4StableWriteWithinFromAbove_of_dutyCover

/-- **The lagged write from a per-reader duty cover at a chosen later round.**
Together with `dutyCoverAt_of_viable_and_localG2` this reduces
`W4StableWriteWithinFrom` to: pick the duty round `d` within `η_SG` of the
opening, and supply viability and the reader's own G2 cover THERE. -/
theorem w4StableWriteWithinFrom_of_dutyCover
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    (sch : ScheduleWellFormed S rho)
    (hchoice : ∀ q : Round, 0 < q →
      S.E.proposer (S.hc.opening_slot q) ∈ rho.honest →
      ∀ P : NamedBlock V, proposedBlockAt S rho (S.hc.opening_slot q) = some P →
        S.a (q + S.hc.η_SG) ≤ rho.horizon →
        ∃ d : Round, q < d ∧ d ≤ q + S.hc.η_SG ∧
          ∀ v ∈ rho.honest, DutyCoverAt S rho d P.erase v) :
    W4StableWriteWithinFrom S rho := by
  intro q hq hprop P hP hhor
  obtain ⟨d, hqd, hdle, hnode⟩ := hchoice q hq hprop P hP hhor
  refine ⟨d, hqd, hdle, ?_⟩
  have hdpos : 0 < d := Nat.lt_of_le_of_lt (Nat.zero_le q) hqd
  have hdhor : dutyTime S d ≤ rho.horizon :=
    (dutyTime_le_action S d).trans ((Assembly.a_mono S hdle).trans hhor)
  exact stable_preceq_at_duty_of_dutyCover S core sch hdpos hnode hdhor

#print axioms w4StableWriteWithinFrom_of_dutyCover





/-! ## The write restricted to the rounds the branch actually uses
`W4StableWriteFrom` quantifies over every round, but the growth proof only ever
calls it at an opening at or after `start`. The prepared-V4 producers on the
continuation side are anchored at the handover slot and say nothing below it,
so the restricted obligation is the one that can actually be discharged. -/




end W4StableWrite
end Proofs
end DecoupledConsensusModel

end
