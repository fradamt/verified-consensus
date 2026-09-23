module
public import DecoupledConsensusStatements.Instantiation
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Bridge.GenericExecution
public import DecoupledConsensusProofs.Bridge.GenericParticipation
public import DecoupledConsensusProofs.Bridge.GenericRecurrence

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

namespace DecoupledConsensusModel
namespace Proofs

open Internal Execution Statements
open Statements.Generic

variable {V : Type} [DecidableEq V] [Fintype V]


private theorem action_prev_eq (S : Setup V) {r : Round} (hr : 0 < r) :
    S.a r - (S.a 1 - S.a 0) = S.a (r - 1) := by
  have hprev : r - 1 + 1 = r := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hr)
  rw [← hprev, NamedOutageClosure.a_succ_roundLength]
  unfold Setup.a Protocol.HealConfig.a Protocol.HealConfig.opening_slot slotStart
  push_cast
  unfold Statements.Instantiation.roundLength
  ring_nf

theorem sleepyRegime_of_generic (S : Setup V) (rho : Run V) (t₀ : Time)
    (h : Generic.SleepyRegime (P S) (E S) (I S) (C S) rho t₀) :
    Statements.SleepyRegime S (Statements.«instance» S)
      (Statements.ourConstants S) rho t₀ := by
  refine {
    execution := executionValid_of_generic S rho h.execution
    synchrony := partialSynchrony_of_generic S rho h.partialSynchrony
    gst := h.gst
    committees := h.committees
    windows := ?_ }
  intro r hr htr hhor
  have htime : S.a r - (C S).participationLag = S.a (r - 1) := by
    simpa [C, Instantiation.constants] using action_prev_eq S hr
  have hlag : (C S).participationLag ≤ S.a r := by
    have hprev_nonneg := Proofs.HealingLemmas.a_nonneg S (r - 1)
    linarith [htime]
  apply windowMajority_of_generic S rho (S.hc.η_SG) r hr
    S.hc.η_SG_ge_one
  have hg := h.windows (S.a r) htr hlag (by simpa [htime] using hhor)
  simpa [C, Instantiation.constants] using hg

theorem bftRegime_of_generic (S : Setup V) (rho : Run V) (t₀ : Time)
    (h : Generic.BFTRegime (P S) (E S) (I S) rho t₀) :
    Statements.BFTRegime S (Statements.«instance» S) rho t₀ := by
  refine {
    execution := executionValid_of_generic S rho h.execution
    synchrony := partialSynchrony_of_generic S rho h.partialSynchrony
    gst := h.gst
    committees := h.committees
    belowThird := ?_
    allAwake := allAwake_of_generic S rho h.allAwake }
  simpa [E, Instantiation.env, Generic.BelowOneThird,
    Execution.BelowOneThird] using h.belowThird

theorem recoveryRegime_of_generic (S : Setup V) (rho : Run V) (t₀ : Time)
    (gap : Nat)
    (h : Generic.RecoveryRegime (P S) (E S) (I S) (C S) rho t₀ gap) :
    Statements.RecoveryRegime S (Statements.«instance» S)
      (Statements.ourConstants S) rho t₀ gap S.extraRounds := by
  refine {
    execution := executionValid_of_generic S rho h.execution
    synchrony := partialSynchrony_of_generic S rho h.partialSynchrony
    gst := h.gst
    committees := h.committees
    belowThird := ?_
    allAwake := allAwake_of_generic S rho h.allAwake
    recurrence := proposerRecurrence_of_generic S rho gap h.recurrence
    timeout := S.timeoutDelayBound
    horizon := ?_ }
  · simpa [E, Instantiation.env, Generic.BelowOneThird,
      Execution.BelowOneThird] using h.belowThird
  · simpa [C, Instantiation.constants, Statements.ourConstants] using h.horizon

theorem finalityRegime_of_generic (S : Setup V) (rho : Run V) (t₀ : Time)
    (gap : Nat)
    (h : Generic.FinalityRegime (P S) (E S) (I S) (C S) rho t₀ gap) :
    Statements.FinalityRegime S (Statements.«instance» S) rho t₀ gap S.extraRounds := by
  refine {
    execution := executionValid_of_generic S rho h.execution
    synchrony := partialSynchrony_of_generic S rho h.partialSynchrony
    gst := h.gst
    committees := h.committees
    belowThird := ?_
    allAwake := allAwake_of_generic S rho h.allAwake
    recurrence := openingCarrierRecurrence_of_generic S rho gap h.recurrence
    gapBound := ?_
    timeout := S.timeoutDelayBound }
  · simpa [E, Instantiation.env, Generic.BelowOneThird,
      Execution.BelowOneThird] using h.belowThird
  · simpa [C, Instantiation.constants] using h.gapBound

theorem recoveredBy_of_generic (S : Setup V) (rho : Run V)
    (t₀ : Time)
    (h : Generic.RecoveredBy (P S) (E S) (I S) (C S) rho t₀) :
    Statements.RecoveredBy S (Statements.«instance» S)
      (Statements.ourConstants S) rho t₀ := by
  induction h with
  | genesis => exact Statements.RecoveredBy.genesis
  | @recovered source t₀ gap hrec hcont hslash =>
      apply Statements.RecoveredBy.recovered
      · exact recoveryRegime_of_generic S source t₀ gap hrec
      · refine ⟨?_, hcont.covered⟩
        refine { honest_subset := hcont.agrees.honest_subset, events := ?_ }
        intro v hv
        have hprefix :
            (Statements.ourConstants S).prefixEnd t₀ gap
                (S.cfg.timeoutDelay / S.hc.R - 2) =
              (C S).prefixEnd t₀ gap := by
          simp [Setup.extraRounds, C, Instantiation.constants, Statements.ourConstants]
        rw [hprefix]
        have he := hcont.agrees.events v hv
        convert he using 1 <;> try rfl
        all_goals
          apply List.filter_congr
          intro e he
          cases e <;> rfl
      · exact slashableBound_of_generic S rho hslash

theorem outageRegime_of_generic (S : Setup V) (rho : Run V)
    (T b₀ b₁ : Time)
    (h : Generic.OutageRegime (P S) (E S) (I S) (C S) rho T b₀ b₁) :
    Statements.OutageRegime S (Statements.«instance» S)
      (Statements.ourConstants S) rho b₀ b₁ := by
  refine {
    execution := executionValid_of_generic S rho h.execution
    synchrony := partialSynchrony_of_generic S rho h.partialSynchrony
    gst := h.gst
    committees := h.committees
    healthy := healthy_of_generic S rho b₀ h.healthy
    interval := h.interval
    boundaryPublic := ?_
    participation := ?_ }
  · simpa [E, Instantiation.env, Generic.PublicTime,
      Execution.PublicTime] using h.boundaryPublic
  · apply awakeGradeMajorityThroughout_of_generic S rho
    intro t htlo hthi
    apply h.participation t
    · simpa [C, Instantiation.constants] using htlo
    · simpa [C, Instantiation.constants] using hthi

end Proofs
end DecoupledConsensusModel

end
