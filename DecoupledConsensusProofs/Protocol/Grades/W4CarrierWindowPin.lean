module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.W4RecordPins
public import DecoupledConsensusProofs.Protocol.Grades.PreparedFrameAfterDeadline

@[expose] public section

/-!
# The selected-grade-2 step, discharged at the rounds that use it

, the corresponding branch. The last residual under the named height-source history is
`_of_selectedG2_preceq_honestPreviousCarrier`: a selected grade-2 block at a
node's round-`(k+1)` action read is below some honest node's round-`k` SG
carrier. the corresponding branch reduced it to two carrier-window facts
(`selectedG2_preceq_honestPreviousCarrier_of_carrierWindows`,
`W4RecordPinsRun.lean:237`): the relative carrier window at each round, and the
grade-2 domain of each round inside the horizon.

**The unguarded pair is not provable, and does not need to be.** Its second
fact, `∀ k, domain S.E S.hc (k + 1).g2 ≤ rho.horizon`, says every round of the
run lies inside the horizon. That is refuted outright below by
`w4uNot_domainG2_le_horizon_forall`: the horizon is one fixed time, while the
action schedule is strictly increasing and the round-`k` action is at or before
the round-`(k+1)` grade-2 domain read. Its first fact asks for the carrier
window at rounds BELOW the recovery deadline, where the honest action carriers
are exactly what the recovery is still establishing.

The guarded form is provable outright, with no pin, and it is the only form any
call site uses: the corresponding branch applies the step at `k:= r - 1` under
`fgSafetyProgressDeadline … + 3 ≤ r` (`W4HeightSourceHistoryRun.lean:216`), and
the record exports apply it at rounds inside the fold, which are after the same
deadline. At those rounds the window is already available material:
`relativeCarrierWindowAt_after_recovery_deadline`
(`PreparedFrameAfterDeadlineRun.lean:69`) needs exactly the regime the callers
carry, and the horizon guard is the caller's own.
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

/-- **The selected-grade-2 step at one round after the recovery deadline**,
with no pin. This is
`selectedG2_preceq_honestPreviousCarrier_of_carrierWindow` with its window
hypothesis discharged. -/
theorem w4uSelectedG2_preceq_honestPreviousCarrier_at
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {k : Round} (hk : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ k)
    (hhor : DecoupledConsensusModel.Protocol.domain S.E S.hc (k + 1) DecoupledConsensusModel.Protocol.Phase.g2 ≤
      rho.horizon) :
    ∀ v ∈ rho.honest, ∀ A : Block V,
      PhaseGrades.nodeQ2 S (actionReadAt S rho v (k + 1)) (k + 1) = some A →
      ∃ u ∈ rho.honest, Block.Preceq A (actionSGBlockAt S rho u k) :=
  selectedG2_preceq_honestPreviousCarrier_of_carrierWindow S adm hbelow
    (relativeCarrierWindowAt_after_recovery_deadline S adm hcom hbelow hrec
      hdelay hpost hk hhor)
    hhor
    (hpost.trans (Assembly.a_mono S (by
      have hGSTdead : rGST ≤
          fgSafetyProgressDeadline S rho rGST gap delayExtra := by
        unfold fgSafetyProgressDeadline
        exact (Nat.le_add_right rGST 1).trans
          (Nat.le_add_right (rGST + 1) _)
      exact hGSTdead.trans hk)))

#print axioms w4uSelectedG2_preceq_honestPreviousCarrier_at

/-- **The same step in the shape the callers' pin binder has**, indexed by the
round `r` of the action read rather than by its predecessor. A caller that
holds `fgSafetyProgressDeadline … + 1 ≤ r` and the round's own action horizon
discharges its pin by one application, with no arithmetic of its own. -/
theorem w4uSelectedG2_preceq_honestPreviousCarrier_atRound
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {r : Round}
    (hr : fgSafetyProgressDeadline S rho rGST gap delayExtra + 1 ≤ r)
    (hhor : DecoupledConsensusModel.Protocol.domain S.E S.hc r DecoupledConsensusModel.Protocol.Phase.g2 ≤
      rho.horizon) :
    ∀ v ∈ rho.honest, ∀ A : Block V,
      PhaseGrades.nodeQ2 S (actionReadAt S rho v r) r = some A →
      ∃ u ∈ rho.honest, Block.Preceq A (actionSGBlockAt S rho u (r - 1)) := by
  have hrpos : 1 ≤ r := (Nat.le_add_left 1 _).trans hr
  have hsucc : r - 1 + 1 = r := Nat.sub_add_cancel hrpos
  have hk : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ r - 1 :=
    Nat.le_sub_of_add_le hr
  have h := w4uSelectedG2_preceq_honestPreviousCarrier_at S adm hcom hbelow
    hrec hdelay hpost hk (by simpa only [hsucc] using hhor)
  simpa only [hsucc] using h

#print axioms w4uSelectedG2_preceq_honestPreviousCarrier_atRound

/-- **The second carrier-window fact, in its guarded form.** The round's
grade-2 domain read is inside the horizon as soon as the round's own ACTION is,
which every caller of the step already holds. Stated here so the step's two
inputs are named in one place. -/
theorem w4uDomainG2_le_horizon_of_action
    (S : Setup V) {rho : Run V} {r : Round}
    (hhor : S.a r ≤ rho.horizon) :
    DecoupledConsensusModel.Protocol.domain S.E S.hc r DecoupledConsensusModel.Protocol.Phase.g2 ≤ rho.horizon :=
  (FrameForward.domain_le_a S r DecoupledConsensusModel.Protocol.Phase.g2).trans hhor

#print axioms w4uDomainG2_le_horizon_of_action

/-! ## The unguarded pair is refutable

Not merely unproved: no setup and run satisfy the second carrier-window fact.
-/




end HealingSurface
end Proofs
end DecoupledConsensusModel

end
