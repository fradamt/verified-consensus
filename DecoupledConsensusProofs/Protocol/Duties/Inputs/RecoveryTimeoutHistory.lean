module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordFresh
public import DecoupledConsensusProofs.Objects.FGConfirmationHistory
public import DecoupledConsensusProofs.Execution.RecurringArithmeticCore
public import DecoupledConsensusProofs.Protocol.ChainState.NamedNjGap
public import DecoupledConsensusProofs.Generic.SuffixHistory
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.Actions
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.ValidatorClient.Record
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.Wire

@[expose] public section

/-!
# Target history behind recovery-successor timeouts

At the successor of a periodic height, every derived source has `nj = false`.
A timeout therefore reads an earlier timeout or a different recorded target.
Both entries come from earlier local emissions. Induction on the source round
traces each honest timeout to an earlier target at the same height.

The argument does not assume fresh records, aligned locks, a fault bound, or
agreement between FG witnesses from different rounds.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol (Record height_pair own_lock)
open Protocol (derive_named)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- With a clear `nj` input, a timeout must read an existing local record
entry. A conflicting lock instead produces an empty height pair. -/
theorem height_pair_timeout_of_nj_false_has_record
    (Lambda : Record) (fp : Option FinalityPair) {H : Height} {T : BlockId}
    (hpair : height_pair Lambda (some (H, T, false)) fp = HeightPair.timeout H) :
    Lambda.timeout H = true ∨ ∃ U, Lambda.target H = some U ∧ U ≠ T := by
  cases ht : Lambda.timeout H with
  | true => exact Or.inl rfl
  | false =>
      right
      cases hl : own_lock Lambda H fp with
      | some U =>
          by_cases hU : U = T <;> simp [height_pair, ht, hl, hU] at hpair
      | none =>
          cases hr : Lambda.target H with
          | none => simp [height_pair, ht, hl, hr] at hpair
          | some U =>
              refine ⟨U, rfl, ?_⟩
              intro hU
              simp [height_pair, ht, hl, hr, hU] at hpair

/-- An actual honest timeout at the successor of a periodic height reads an
earlier timeout or a target entry at that height. The result concerns the
record before the actual action, not an arbitrary selector call. -/
theorem recoverySuccessorTimeout_has_witness_record
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {blocked : Height} (hdvd : S.cfg.K ∣ blocked)
    {a : NamedAttestation V} {ta : Time}
    (ha : a.val_index ∈ rho.honest)
    (hemit : rho.emits S a.val_index (Object.attest a) ta)
    (hpair : a.erase.height_pair = HeightPair.timeout (blocked + 1)) :
    ∃ T : Block V,
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) = some T ∧
        ((rho.stateBeforeTime S ta a.val_index).Λ.legacy.timeout (blocked + 1) = true ∨
          ∃ U, (rho.stateBeforeTime S ta a.val_index).Λ.legacy.target (blocked + 1) =
            some U ∧ U ≠ T.root) := by
  have hrow : a.erase.height_pair.height? = some (blocked + 1) := hpair ▸ rfl
  obtain ⟨B, T, htime, haEq, hsource, hmem, hheight, hderived, hT, _⟩ :=
    honestEmittedHeightRow_exactFGSelectorWitness S adm ha hemit hrow
  let ast := actionStoreAt S rho a.val_index a.round
  let Lambda := (rho.stateBeforeTime S (S.a a.round) a.val_index).Λ.legacy
  let fp := (actionAttestationAt S rho a.val_index a.round).finality_pair
  have hBpre : B ∈
      (rho.stateBeforeTime S (S.a a.round) a.val_index).st.bodies := by
    simpa only [ast, actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hmem
  have hσ : ast.st.core.σ B.erase = derive_named S.E S.cfg B := by
    simpa only [ast, actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using
      (Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho
        (S.a a.round) a.val_index B hBpre)
  have hnj : (ast.st.core.σ B.erase).nj = false := by
    rw [hσ]
    obtain ⟨hF', -, hnj'⟩ := NjGap.njEntry_derive_named S.E S.cfg B
    rw [hnj', hderived]
    exact Proofs.Engine.nonjustifiable_succ_of_dvd S.cfg hdvd hF'
  have hLambda : ast.record.legacy = Lambda := by
    rfl
  have hshape : (actionAttestationAt S rho a.val_index a.round).erase.height_pair =
      Protocol.height_pair Lambda
        ((Protocol.fg_source_with (NamedProfile.gradeContract ast.cache)
          S.E S.hc ast.st.core.toHealing (S.hc.round_of ast.s)
          (Protocol.grade2_block_with (NamedProfile.gradeContract ast.cache)
            S.E S.hc ast.st.core.toHealing (S.hc.round_of ast.s))).map
            (fun X => ((ast.st.core.σ X).h, (ast.st.core.σ X).T_h.root,
              (ast.st.core.σ X).nj))) fp := by
    have hnamed := named_round_action_height_pair
      (NamedProfile.gradeContract ast.cache) S.E S.hc (S.node a.val_index)
      ast.st.core.toHealing ast.record
    have herase := congrArg NamedHeightPair.erase hnamed
    rw [NamedRecord.encode_height_erase] at herase
    simpa only [actionAttestationAt, ast, actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime, NamedAttestation.erase, NamedHeightPair.erase,
      actionSource] using herase
  have hsourceAst :
      Protocol.fg_source_with (NamedProfile.gradeContract ast.cache)
          S.E S.hc ast.st.core.toHealing (S.hc.round_of ast.s)
        (Protocol.grade2_block_with (NamedProfile.gradeContract ast.cache)
          S.E S.hc ast.st.core.toHealing (S.hc.round_of ast.s)) = some B.erase := by
    simpa only [actionFGSource, ast, actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hsource
  have hpure : height_pair Lambda
      (some (blocked + 1, (ast.st.core.σ B.erase).T_h.root, false)) fp =
        HeightPair.timeout (blocked + 1) := by
    have haction := haEq ▸ hpair
    rw [hshape] at haction
    simpa only [ast, hsourceAst, Option.map_some, hheight, hnj]
      using haction
  have hTstore : (ast.st.core.σ B.erase).T_h = T := by
    rw [hσ, hT]
  refine ⟨T, ?_, ?_⟩
  · simp only [fgConfirmationWitness, actionStoreAt_round, hsource, Option.map_some]
    exact congrArg some hTstore
  · rw [htime, hT]
    have hpure' : height_pair Lambda
        (some (blocked + 1, (derive_named S.E S.cfg B).T_h.root, false)) fp =
          HeightPair.timeout (blocked + 1) := by
      simpa only [hσ] using hpure
    exact height_pair_timeout_of_nj_false_has_record Lambda fp hpure'

/-- The weaker record-presence form does not need to expose the exact
confirmation witness or the recorded-target disagreement. -/
theorem recoverySuccessorTimeout_has_record
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {blocked : Height} (hdvd : S.cfg.K ∣ blocked)
    {a : NamedAttestation V} {ta : Time}
    (ha : a.val_index ∈ rho.honest)
    (hemit : rho.emits S a.val_index (Object.attest a) ta)
    (hpair : a.erase.height_pair = HeightPair.timeout (blocked + 1)) :
    (rho.stateBeforeTime S ta a.val_index).Λ.legacy.timeout (blocked + 1) = true ∨
      ∃ U, (rho.stateBeforeTime S ta a.val_index).Λ.legacy.target (blocked + 1) =
        some U := by
  obtain ⟨_, _, hrecord⟩ :=
    recoverySuccessorTimeout_has_witness_record S adm hdvd ha hemit hpair
  exact hrecord.imp id fun ⟨U, hU, _⟩ => ⟨U, hU⟩

/-- The record read by an honest recovery-successor timeout has a local
emission in a strictly earlier round. Keep both record-source cases so the
next theorem can trace repeated timeout entries back to a target. -/
theorem recoverySuccessorTimeout_has_earlier_heightRow
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {blocked : Height} (hdvd : S.cfg.K ∣ blocked)
    {a : NamedAttestation V} {ta : Time}
    (ha : a.val_index ∈ rho.honest)
    (hemit : rho.emits S a.val_index (Object.attest a) ta)
    (hpair : a.erase.height_pair = HeightPair.timeout (blocked + 1)) :
    ∃ (b : NamedAttestation V) (tb : Time),
      b.val_index = a.val_index ∧ b.round < a.round ∧ tb < ta ∧
        rho.emits S b.val_index (Object.attest b) tb ∧
        ((∃ U, b.erase.height_pair = HeightPair.target (blocked + 1) U) ∨
          b.erase.height_pair = HeightPair.timeout (blocked + 1)) := by
  obtain ⟨n, hn, hbefore⟩ :=
    Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed ta
  have hrecord := recoverySuccessorTimeout_has_record S adm hdvd ha hemit hpair
  rw [hn] at hrecord
  have hprior : ∃ (i : Nat), i < n ∧ ∃ (tb : Time) (b : NamedAttestation V),
      rho.events[i]? = some (Event.tick a.val_index tb) ∧
        Object.attest b ∈ (on_tick_emit S a.val_index
          (rho.stateBefore S i a.val_index) tb).2 ∧
        ((∃ U, b.erase.height_pair = HeightPair.target (blocked + 1) U) ∨
          b.erase.height_pair = HeightPair.timeout (blocked + 1)) := by
    rcases hrecord with ht | ⟨U, hU⟩
    · obtain ⟨i, hi, tb, b, hevent, hout, hrow⟩ :=
        recordTimeout_emission_before S rho a.val_index n ht
      exact ⟨i, hi, tb, b, hevent, hout, Or.inr hrow⟩
    · obtain ⟨i, hi, tb, b, hevent, hout, hrow⟩ :=
        Protocol.recordTarget_emission_before S rho a.val_index n hU
      exact ⟨i, hi, tb, b, hevent, hout, Or.inl ⟨U, hrow⟩⟩
  obtain ⟨i, hi, tb, b, hevent, hout, hrow⟩ := hprior
  have hbemit : rho.emits S a.val_index (Object.attest b) tb :=
    ⟨i, hevent, hout⟩
  obtain ⟨hbval, hbtime⟩ := Proofs.Optimistic.emits_attest_shape S hbemit
  have htime : tb < ta := hbefore i (Event.tick a.val_index tb) hi hevent
  have hround : b.round < a.round := by
    apply (action_strictMono S).lt_iff_lt.mp
    simpa only [(Proofs.Optimistic.emits_attest_shape S hemit).2, hbtime] using htime
  exact ⟨b, tb, hbval, hround, htime, hbval ▸ hbemit, hrow⟩

/-- Every honest timeout at the successor of a periodic height follows an
actual local target emission at that height. Repeated timeout records cannot
start a source history without a target. -/
theorem recoverySuccessorTimeout_has_earlier_target
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {blocked : Height} (hdvd : S.cfg.K ∣ blocked)
    {a : NamedAttestation V} {ta : Time}
    (ha : a.val_index ∈ rho.honest)
    (hemit : rho.emits S a.val_index (Object.attest a) ta)
    (hpair : a.erase.height_pair = HeightPair.timeout (blocked + 1)) :
    ∃ (b : NamedAttestation V) (tb : Time) (U : BlockId),
      b.val_index = a.val_index ∧ b.round < a.round ∧ tb < ta ∧
        rho.emits S b.val_index (Object.attest b) tb ∧
        b.erase.height_pair = HeightPair.target (blocked + 1) U := by
  suffices h : ∀ r : Round, ∀ (a : NamedAttestation V) (ta : Time),
      a.round = r → a.val_index ∈ rho.honest →
      rho.emits S a.val_index (Object.attest a) ta →
      a.erase.height_pair = HeightPair.timeout (blocked + 1) →
      ∃ (b : NamedAttestation V) (tb : Time) (U : BlockId),
        b.val_index = a.val_index ∧ b.round < a.round ∧ tb < ta ∧
          rho.emits S b.val_index (Object.attest b) tb ∧
          b.erase.height_pair = HeightPair.target (blocked + 1) U from
    h a.round a ta rfl ha hemit hpair
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
      intro a ta har ha hemit hpair
      obtain ⟨b, tb, hbval, hbr, hbt, hbemit, hbrow⟩ :=
        recoverySuccessorTimeout_has_earlier_heightRow S adm hdvd ha hemit hpair
      rcases hbrow with ⟨U, hbtarget⟩ | hbtimeout
      · exact ⟨b, tb, U, hbval, hbr, hbt, hbemit, hbtarget⟩
      · have hb : b.val_index ∈ rho.honest := hbval ▸ ha
        obtain ⟨c, tc, U, hcval, hcr, hct, hcemit, hctarget⟩ :=
          ih b.round (har ▸ hbr) b tb rfl hb hbemit hbtimeout
        exact ⟨c, tc, U, hcval.trans hbval, hcr.trans hbr, hct.trans hbt,
          hcemit, hctarget⟩

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
