module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.StableRecordPreparedV4WindowPhase
public import DecoupledConsensusProofs.Execution.PreparedV4LatestFinalizedCompatibilityClosed
public import DecoupledConsensusProofs.Objects.HandoverPreparedV4Transfer
public import DecoupledConsensusProofs.Execution.PreparedV4ConfirmationReadBand
public import DecoupledConsensusProofs.Execution.RecoveryWindowClosure
public import DecoupledConsensusProofs.Generic.PreparedV4BoundedSafety
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.W4StableRecordGrowthFrom

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
#  C2 — the prepared-V4 record on the continuation side

The safety-after-recovery closure already produces the prepared-V4 bootstrap
record from `StrongRecoveryPrefix` alone and transfers it across the cut; the
continuation never has to assemble one. This leaf exposes that package at the
SAME bounded round `m` the stable-record growth branch uses, so the band
producer `SettledBootstrapPreparedV4.confirmationReadBand_le_voterHeadHeight_core`
can be instantiated at the branch's duty read.

The one input not exported by the closure is the continuation's awake-window
majority BELOW the cut, which `PreparedV4BoundedSafetyRun` derives privately
from the prefix's full participation. It is taken here as `PreparedV4AwakeWindows`.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace W4StableWrite

open Internal Execution Statements
open Proofs.HealingSurface Proofs.HealingSurface.Handover

variable {V : Type} [DecidableEq V] [Fintype V]

/-- PIN: the continuation's awake-window majority at EVERY positive round, not
only after the cut. Below the cut it comes from the prefix's full
participation, the honest-set inclusion and the agreement. The producer exists
as the private `preparedV4_awakeWindows_of_prefix`
(`PreparedV4BoundedSafetyRun.lean:61`); an additive public export of it
discharges this pin with no proof. -/
def PreparedV4AwakeWindows (S : Setup V) : Prop :=
  ∀ (source rho : Run V) (lastStrong : Round),
    Admissible S source → source.horizon = S.a lastStrong →
    rho.honest ⊆ source.honest → S.a lastStrong ≤ rho.horizon →
    (∀ r, lastStrong < r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r) →
    ∀ r, 0 < r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r

/-- **The continuation-side prepared-V4 package**, at the bounded round the
stable-record growth branch already selects. Everything is taken from the
closure's own selector at the cut `n + gap`. -/
theorem continuationV4Package (S : Setup V)
    (hawakePin : PreparedV4AwakeWindows S) :
    ∀ rho rGST gap extra n,
      StrongRecoveryPrefix S rho rGST gap extra n →
      ∃ m, n ≤ m ∧ m ≤ n + gap ∧
        ∀ rho', WeakContinuation S rho rho' (n + gap) →
          ∃ (fresh base : Round) (P : NamedBlock V) (cap : Height),
            PhaseShiftSafety S rho' (base + S.hc.η_SG)
              (S.hc.opening_slot m) P.erase ∧
            SettledBootstrapPreparedV4 S rho' fresh base
              (S.hc.opening_slot m) P cap ∧
            FinalizedRootsBelowAtRead S rho' cap P.erase ∧
            (∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho'.horizon →
              AwakeWindowMajority S.E (fun v => (S.node v).awake)
                rho'.honest S.hc.η_SG r) ∧
            Protocol.confirmation_time S.E
              (S.hc.opening_slot m) ≤ rho'.horizon ∧
            (∀ u ∈ rho'.honest, ∀ v ∈ rho'.honest, ∀ t t',
              Protocol.confirmation_time S.E (S.hc.opening_slot m) ≤ t →
              Protocol.confirmation_time S.E (S.hc.opening_slot m) ≤ t' →
              t ≤ rho'.horizon → t' ≤ rho'.horizon →
              Block.compatible (rho'.storeAt S u t).core.latest_confirmed
                (rho'.storeAt S v t').core.F = true) := by
  intro source rGST gap extra n hprefix
  obtain ⟨m, hmn, hmend, fresh, base, P, cap, hboot, hlatest, hfresh,
      hheight, hphase⟩ :=
    stableRecordPreparedV4_phase_of_window S (window_of_strongRecoveryPrefix S)
      source rGST gap extra n hprefix
  refine ⟨m, hmn, hmend, ?_⟩
  intro rho hcont
  have hseedCut : Protocol.confirmation_time S.E (S.hc.opening_slot m) ≤
      S.a (n + gap) := by
    rw [opening_confirmation_time_eq_action]
    exact Assembly.a_mono S hmend
  have hagreeSeed : AgreesUntil source rho
      (Protocol.confirmation_time S.E (S.hc.opening_slot m)) :=
    AgreesUntil.mono hcont.agrees hseedCut
  have hboot' := SettledBootstrapPreparedV4.transfer
    S hprefix.admissible.toNamedAdmissibleCore hcont.core hcont.committees
      hboot hfresh hagreeSeed
  have hfinality :=
    SettledBootstrapPreparedV4.finalizedRootsBelowAtRead_of_accountable
      S hcont.core hcont.accountable hboot' hheight
  have hcovered : S.a (n + gap) ≤ rho.horizon :=
    (a_le_healingBoundaryTime S (n + gap)).trans hcont.covered
  have hwindows := hawakePin source rho (n + gap) hprefix.admissible
    hprefix.horizon hcont.agrees.honest_subset hcovered hcont.windows
  have hcutPos : 0 < base + S.hc.η_SG :=
    Nat.zero_lt_of_lt (Nat.add_lt_add_left S.hc.η_SG_ge_one base)
  have hawake' : ∀ r, base + S.hc.η_SG ≤ r →
      S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r :=
    fun r hr => hwindows r (hcutPos.trans_le hr)
  have hstartHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot m) ≤ rho.horizon :=
    hseedCut.trans hcovered
  have hlatest' := SettledBootstrapPreparedV4.LatestSeed.transfer
    S hlatest hagreeSeed
  refine ⟨fresh, base, P, cap, hphase rho hcont, hboot', hfinality, hawake',
    hstartHor, ?_⟩
  intro u hu v hv t t' ht ht' htHor htHor'
  exact SettledBootstrapPreparedV4.latest_compatible_finalized_core
    S hcont.core hcont.committees hboot' hlatest' hawake' hfinality hstartHor
      hu hv ht ht' htHor htHor'

#print axioms continuationV4Package

/-! ## The frontier band at the branch's duty read
The branch's write duty is `dutyTime S (q+1) = support_cutoff (opening_slot (q+1))`,
which is one support-cutoff step BEFORE earlier's `confirmation_time (opening_slot (q+1))`.
It is nevertheless a `confirmationInputRead`: `confirmation_time s` is
`support_cutoff (s+1)`, so the duty read is `confirmationInputRead` at the slot
`opening_slot (q+1) - 1`. The prepared-V4 band producer therefore applies
directly, with no new timing argument. -/

private theorem openingSlot_succ_pos (S : Setup V) (q : Round) :
    0 < S.hc.opening_slot (q + 1) := by
  simpa only [Protocol.HealConfig.opening_slot] using
    Nat.mul_pos (Nat.succ_pos q) (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)

/-- The duty read of round `q+1` IS the prepared confirmation input read at the
slot one below that round's opening. -/
theorem confirmationInputRead_pred_eq_dutyRead (S : Setup V) (rho : Run V)
    (v : V) (q : Round) :
    Internal.NamedRecoveryRead.confirmationInputRead S rho v
        (S.hc.opening_slot (q + 1) - 1) =
      NamedActionReads.confirmationReadAt S rho v (dutyTime S (q + 1)) := by
  have hpos : 1 ≤ S.hc.opening_slot (q + 1) := openingSlot_succ_pos S q
  simp only [Internal.NamedRecoveryRead.confirmationInputRead, dutyTime,
    Protocol.confirmation_time_eq_support_cutoff_succ,
    Nat.sub_add_cancel hpos]

#print axioms confirmationInputRead_pred_eq_dutyRead

/-- **The frontier band at the branch's duty read**, from the transferred
prepared-V4 record. No participation premise beyond the record's own awake
windows. -/
theorem confirmationReadBand_at_dutyTime
    (S : Setup V) {rho : Run V} (core : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    {q : Round} (hs : start < S.hc.opening_slot (q + 1))
    (hhor : dutyTime S (q + 1) ≤ rho.horizon)
    (v : V) {x : V} (hx : x ∈ rho.honest)
    {X : NamedBlock V}
    (hX : X.erase = voterHeadAt S rho x (S.hc.opening_slot (q + 1) - 1))
    (hXrun : NamedRun.blockInRun S rho X) :
    (NamedActionReads.confirmationReadAt S rho v
        (dutyTime S (q + 1))).st.core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg X).h := by
  have hstart : start ≤ S.hc.opening_slot (q + 1) - 1 :=
    Nat.le_sub_one_of_lt hs
  have hreadHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot (q + 1) - 1) ≤ rho.horizon := by
    have hpos : 1 ≤ S.hc.opening_slot (q + 1) := openingSlot_succ_pos S q
    simpa only [Protocol.confirmation_time_eq_support_cutoff_succ,
      Nat.sub_add_cancel hpos, dutyTime] using hhor
  have h := SettledBootstrapPreparedV4.confirmationReadBand_le_voterHeadHeight_core
    S core hcom hboot hawake hfinality hstart hreadHor (v := v) hx hX hXrun
  simpa only [confirmationInputRead_pred_eq_dutyRead S rho v q] using h

#print axioms confirmationReadBand_at_dutyTime

/-! ## Viability at the duty read, reduced to the head witness

With the band in hand, `ProposalViableAtDuty` needs only the reader's own vote
head as a named body it actually holds. earlier's counterpart is the
`postGain_consuming_head_body` step. -/

/-- PIN: at the duty read the reader holds its own vote head of the slot below
the opening, as a named body of the run. -/
def DutyHeadWitness (S : Setup V) (rho : Run V) (q : Round) (v : V) : Prop :=
  ∃ X : NamedBlock V,
    X ∈ (NamedRun.stateBeforeTime S rho (dutyTime S (q + 1)) v).st.bodies ∧
      X.erase = voterHeadAt S rho v (S.hc.opening_slot (q + 1) - 1) ∧
      NamedRun.blockInRun S rho X

/-- **Viability of the proposal at the duty read.** The band gives the height,
the head witness gives the tree member that carries it, the read-safety field
puts the proposal below that head, and finality compatibility is the third
conjunct. -/
theorem proposalViableAtDuty_of_band_and_head
    (S : Setup V) {rho : Run V} {q : Round} {B : Block V} {v : V}
    (hhead : DutyHeadWitness S rho q v)
    (hband : ∀ X : NamedBlock V, NamedRun.blockInRun S rho X →
      X.erase = voterHeadAt S rho v (S.hc.opening_slot (q + 1) - 1) →
      (NamedActionReads.confirmationReadAt S rho v
          (dutyTime S (q + 1))).st.core.h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg X).h)
    (hbelow : Block.Preceq B
      (voterHeadAt S rho v (S.hc.opening_slot (q + 1) - 1)))
    (hfg : Block.compatible B (Protocol.get_fg_root
      (NamedActionReads.confirmationReadAt S rho v
        (dutyTime S (q + 1))).st.core.toHealing.toFG) = true) :
    ProposalViableAtDuty S rho q B v := by
  classical
  obtain ⟨X, hXbody, hXerase, hXrun⟩ := hhead
  have hTree : (NamedRun.stateBeforeTime S rho
      (dutyTime S (q + 1)) v).st.core.T =
      (NamedRun.stateBeforeTime S rho
        (dutyTime S (q + 1)) v).st.bodies.image NamedBlock.erase :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
      (dutyTime S (q + 1)) v).1.1.1.1
  have hXmem : X.erase ∈ (NamedActionReads.confirmationReadAt S rho v
      (dutyTime S (q + 1))).st.core.T := by
    have h : X.erase ∈ (NamedRun.stateBeforeTime S rho
        (dutyTime S (q + 1)) v).st.core.T := by
      rw [hTree]
      exact Finset.mem_image_of_mem NamedBlock.erase hXbody
    exact h
  have hsigma : (NamedActionReads.confirmationReadAt S rho v
      (dutyTime S (q + 1))).st.core.σ X.erase =
      Protocol.derive_named S.E S.cfg X := by
    have h := Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho
      (dutyTime S (q + 1)) v X hXbody
    exact h
  have hBX : Block.Preceq B X.erase := by
    rw [hXerase]; exact hbelow
  have hheight : (NamedActionReads.confirmationReadAt S rho v
      (dutyTime S (q + 1))).st.core.h_max - 1 ≤
      ((NamedActionReads.confirmationReadAt S rho v
        (dutyTime S (q + 1))).st.core.σ X.erase).h := by
    rw [hsigma]
    exact hband X hXrun hXerase
  have hpc := (parentClosed_iff (NamedActionReads.confirmationReadAt S rho v
    (dutyTime S (q + 1))).st.core).mp
    (Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
      (dutyTime S (q + 1)) v)
  refine ⟨Proofs.Records.mem_of_preceq hpc.2 B X.erase hXmem hBX, ?_, hfg⟩
  simp only [Protocol.viable, decide_eq_true_eq]
  exact ⟨X.erase, hXmem, hBX, hheight⟩

#print axioms proposalViableAtDuty_of_band_and_head

/-! ## Viability at the duty read, from the package plus one band head
With `proposalViableAtDutyRound_of_bandHead` the FG-root compatibility is no
longer a separate obligation, and the band comes from the transferred
prepared-V4 record. What is left is one head at the duty read with its two
order facts. -/





theorem supportCutoff_le_voteTime_succ (S : Setup V) (s : Slot) :
    Protocol.support_cutoff S.E s ≤ Protocol.vote_time S.E (s + 1) := by
  unfold Protocol.support_cutoff Protocol.vote_time Env.t slotStart
  push_cast
  nlinarith [S.E.Δ_pos]

#print axioms supportCutoff_le_voteTime_succ

theorem voteTime_le_supportCutoff_mono (S : Setup V) {s s' : Slot}
    (h : s ≤ s') :
    Protocol.vote_time S.E s ≤ Protocol.support_cutoff S.E s' := by
  have hcast : (s : Time) ≤ (s' : Time) := by exact_mod_cast h
  unfold Protocol.support_cutoff Protocol.vote_time Env.t slotStart
  nlinarith [S.E.Δ_pos, hcast]

#print axioms voteTime_le_supportCutoff_mono

/-- **The proposal is compatible with the reader's FG root at the duty read.** -/
theorem proposalFgRootCompat_at_dutyTime
    (S : Setup V) {rho : Run V} (core : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {Pseed : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start Pseed cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap Pseed.erase)
    {q : Round} (hd : start ≤ S.hc.opening_slot (q + 1))
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot (q + 1)) ≤ rho.horizon)
    {B : Block V} {v : V} (hv : v ∈ rho.honest)
    (hBH : Block.Preceq B
      (voterHeadAt S rho v (S.hc.opening_slot (q + 1)))) :
    Block.compatible B (Protocol.get_fg_root
      (NamedActionReads.confirmationReadAt S rho v
        (dutyTime S (q + 1))).st.core.toHealing.toFG) = true := by
  have hread : min (S.a (base + S.hc.η_SG))
      (Protocol.vote_time S.E start) ≤ dutyTime S (q + 1) := by
    exact (min_le_right _ _).trans (voteTime_le_supportCutoff_mono S hd)
  have ht : dutyTime S (q + 1) ≤
      Protocol.vote_time S.E (S.hc.opening_slot (q + 1) + 1) :=
    supportCutoff_le_voteTime_succ S (S.hc.opening_slot (q + 1))
  have hroot := SettledBootstrapPreparedV4.fgRootAtRead_preceq_voteDutyHead_core
    S core hcom hboot hawake hfinality
    (last := S.hc.opening_slot (q + 1)) hhor hd (Nat.le_succ _) hread ht hv hv
  exact Block.compatible_of_preceq_common hBH hroot

#print axioms proposalFgRootCompat_at_dutyTime


/-- **Viability at the duty read from the V4 record and one head witness.**
Both order facts are instances of `PhaseShiftSafety.honestProposalReads`, field
`vote`, at the two slots; the band and the FG-root compatibility both come from
the transferred record. The head witness is the corresponding branch's, which needs only
`AdmissibleCore` and honesty. -/
theorem proposalViableAtDuty_of_package_and_head
    (S : Setup V) {rho : Run V} (core : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {Pseed : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start Pseed cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap Pseed.erase)
    {q : Round} (hs : start < S.hc.opening_slot (q + 1))
    (hhorDuty : dutyTime S (q + 1) ≤ rho.horizon)
    (hhorOpen : Protocol.confirmation_time S.E
      (S.hc.opening_slot (q + 1)) ≤ rho.horizon)
    {B : Block V} {v : V} (hv : v ∈ rho.honest)
    (hhead : DutyHeadWitness S rho q v)
    (hbelowPrev : Block.Preceq B
      (voterHeadAt S rho v (S.hc.opening_slot (q + 1) - 1)))
    (hbelowOpen : Block.Preceq B
      (voterHeadAt S rho v (S.hc.opening_slot (q + 1)))) :
    ProposalViableAtDuty S rho q B v := by
  refine proposalViableAtDuty_of_band_and_head S hhead ?_ hbelowPrev
    (proposalFgRootCompat_at_dutyTime S core hcom hboot hawake hfinality
      (Nat.le_of_lt hs) hhorOpen hv hbelowOpen)
  intro Y hYrun hYerase
  exact confirmationReadBand_at_dutyTime S core hcom hboot hawake hfinality
    hs hhorDuty v hv hYerase hYrun

#print axioms proposalViableAtDuty_of_package_and_head

/-! ## Closing the awake-window pin, and the branch

`PreparedV4AwakeWindows` is now discharged from the safety closure's own
producer, exported additively as
`Handover.preparedV4_awakeWindows_of_prefix_core`. -/

theorem preparedV4AwakeWindows_closed (S : Setup V) : PreparedV4AwakeWindows S :=
  fun _source _rho _lastStrong adm hprefix hretain hcovered hawake =>
    Handover.preparedV4_awakeWindows_of_prefix_core S adm hprefix hretain
      hcovered hawake

#print axioms preparedV4AwakeWindows_closed


/-- PIN (the corresponding branch's `w4_dutyHeadWitness`, exact statement): at any positive
duty round each honest reader holds its own vote head of the slot below that
round's opening, as a named body of the run. Regime-free: `AdmissibleCore` and
honesty are the only premises. -/
def DutyHeadWitnessAll (S : Setup V) : Prop :=
  ∀ (rho : Run V), AdmissibleCore S rho → ∀ (r : Round), 0 < r →
    ∀ v ∈ rho.honest,
      ∃ X : NamedBlock V,
        X ∈ (NamedRun.stateBeforeTime S rho (dutyTime S r) v).st.bodies ∧
          X.erase = voterHeadAt S rho v (S.hc.opening_slot r - 1) ∧
          NamedRun.blockInRun S rho X

end W4StableWrite
end Proofs
end DecoupledConsensusModel

end
