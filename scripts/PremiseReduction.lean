import DecoupledConsensusWitnesses.FinalityLiveness
import DecoupledConsensusWitnesses.WeakGenesis

/-! Regression checks for the newly admitted premise domain. -/
namespace DecoupledConsensusModel.PremiseReduction
open Execution Statements

/-- The base setup admits empty committees and the short outage parameter point. -/
def sparseSetup : Setup (Fin 2) :=
  { Witnesses.S with
    E := { Witnesses.E with committees := ⟨fun _ => ∅⟩ }
    hc := { Witnesses.hc with η_SG := 1, η_SG_ge_one := by decide } }

example : sparseSetup.E.committee 0 = ∅ := rfl
example : ¬ 4 ≤ sparseSetup.hc.R * sparseSetup.hc.η_SG := by decide

-- The removed setup bound is still genuinely needed by the constants field.
example : ¬ (Instantiation.constants sparseSetup).Valid := by
  intro h
  have hempty : ¬ (Instantiation.constants sparseSetup).outageStart 0 <
      (Instantiation.constants sparseSetup).expiry 0 := by decide
  exact hempty (h.outage_window_nonempty 0)

-- Sortedness alone suffices, even on a setup outside the old domain.
example (rho : Run (Fin 2))
    (h : Generic.SortedRun (P := Execution.spec sparseSetup) rho) :
    Generic.MonotoneFrom (Execution.spec sparseSetup) rho
      (Instantiation.interface sparseSetup).finalized 0 :=
  Proofs.accountable_finalizedMonotone sparseSetup rho h

def negativeRun : Run (Fin 2) :=
  { honest := {0}, events := [], horizon := -1 }

example : Generic.ScheduleWellFormed (P := Execution.spec sparseSetup)
    (Instantiation.env sparseSetup) negativeRun where
  sorted := List.Pairwise.nil
  nodup := List.Pairwise.nil
  in_horizon := by intro e he; cases he
  honest_only := by intro e he; cases he
  tick_public := by intro v t he; cases he
  tick_total := by
    intro v hv t ht hzero hhor
    change t ≤ (-1 : Time) at hhor
    dsimp [Time] at *
    omega

-- Participation and proposer triggers use distinct grids.
example : Generic.ActionTime (Instantiation.constants sparseSetup) (sparseSetup.a 0) :=
  Proofs.actionTime_a sparseSetup 0
example : Generic.OpeningTime (Instantiation.interface sparseSetup) 0 :=
  ⟨0, ⟨0, rfl⟩, rfl⟩
example : ¬ Generic.ActionTime (Instantiation.constants sparseSetup) 0 := by
  rintro ⟨r, hr⟩
  norm_num [Instantiation.constants, sparseSetup, Witnesses.S, Witnesses.E, Witnesses.hc,
    Setup.a, Protocol.HealConfig.a, Protocol.HealConfig.opening_slot, slotStart] at hr
  dsimp [Time] at *
  omega

/-- GST can fall inside a sleeping round; only the next action sample is needed. -/
def wakingSetup : Setup (Fin 2) :=
  { Witnesses.S with
    E := { Witnesses.E with t_GST := 7, t_GST_nonneg := by decide }
    node := fun v => { Witnesses.node v with awake := fun r => decide (1 ≤ r) } }

def wakingRun : Run (Fin 2) := { honest := {0}, events := [], horizon := 18 }

example : Generic.FullParticipation (P := Execution.spec wakingSetup)
    (Instantiation.env wakingSetup) (Instantiation.constants wakingSetup) wakingRun := by
  intro v _ t hsample hgst hhor
  obtain ⟨r, hr⟩ := hsample
  norm_num [Instantiation.constants, wakingSetup, Witnesses.S, Witnesses.E, Witnesses.hc,
    Setup.a, Protocol.HealConfig.a, Protocol.HealConfig.opening_slot, slotStart] at hr
  change (7 : Time) ≤ t at hgst
  change t ≤ (18 : Time) at hhor
  have hr1 : r = 1 := by
    dsimp [Time] at *
    omega
  subst r
  have ht : t = 18 := by
    dsimp [Time] at *
    omega
  subst t
  rfl

example : (Instantiation.env wakingSetup).awake 0 7 = false := rfl

example : Generic.StrongMultiProposerRecurrence
    (Instantiation.interface Witnesses.FinalityLiveness.S)
    (Instantiation.constants Witnesses.FinalityLiveness.S)
    Witnesses.FinalityLiveness.rho 0 2 :=
  Witnesses.FinalityLiveness.generic_opening_recurrence_gap_two

#print axioms Witnesses.FinalityLiveness.generic_opening_recurrence_gap_two
#print axioms Witnesses.FinalityLiveness.continuous_opening_recurrence_gap_two_impossible

end DecoupledConsensusModel.PremiseReduction
