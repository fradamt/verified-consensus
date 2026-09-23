module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.RelativeCarrierWindowGateOff

@[expose] public section

/-!
# Relative grade-one settlement in the seed window

This is the named counterpart of `LiveG1SettledAt` used by the original K3
proof. A relative grade has an honest previous-round carrier above it. The
gate-off frame makes that carrier quiet at every current action read, and
quietness passes to its ancestors. No carrier one-chain premise is needed.
-/

namespace DecoupledConsensusModel.Proofs.HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The current schedule has at least three slots per round. Its previous
action is already before the next G2 early cutoff, so no extra GST shift is
needed when that action is after GST. -/
theorem gradeRoundReady_of_previousAction
    (S : Setup V) {rho : Run V} {r : Round} (hr : 0 < r)
    (hpost : S.E.t_GST ≤ S.a (r - 1))
    (hhor : S.a r ≤ rho.horizon) : GradeRoundReady S rho r := by
  constructor
  · exact hpost.trans
      ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
        (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
          (Nat.sub_lt hr Nat.one_pos)))
  · exact (FrameForward.domain_le_a S r .g0).trans hhor

/-- Every named grade-one block is below the target FG root or active in the
target action tree. -/
def NamedLiveG1SettledAt (S : Setup V) (rho : Run V) (r : Round) : Prop :=
  ∀ u ∈ rho.honest, ∀ B, namedG1At S rho u r B →
    ∀ w ∈ rho.honest,
      FinalityFilterNoninterferenceAtRead S rho w (S.a r) B

/-- Relative G1 settlement follows from the preceding carriers' quietness. -/
theorem namedLiveG1SettledAt_of_previousActionCarriersQuiet
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (hr : 0 < r)
    (hwindow : RelativeCarrierWindowAt S rho (r - 1) .g1)
    (hmajority : Internal.NamedOutageEntry.GradeFormingMajority S rho r)
    (hquiet : PreviousActionCarriersQuietAt S rho r) :
    NamedLiveG1SettledAt S rho r := by
  intro u hu B hgrade w hw
  have hpred : r - 1 + 1 = r := Nat.sub_add_cancel hr
  have hgrade' : storeGrade S.E S.hc
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc (r - 1 + 1) .g1) u).st
      (r - 1 + 1) .g1 B = true := by
    simpa only [namedG1At, PhaseGrades.readAt, hpred] using hgrade
  obtain ⟨v, hv, hBcarrier⟩ := relativeGrade_has_roundCarrier
    S adm.toNamedAdmissibleCore hwindow
      (by simpa only [hpred] using hmajority) hu hgrade'
  have hvHon : v ∈ rho.honest :=
    ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho v (r - 1)).mp hv).1
  exact (hquiet v hvHon w hw).ancestor S adm hBcarrier

/-- Gate-off exact frontiers supply relative G1 settlement from the same
run and time premises as the original absolute-grade argument. -/
theorem namedLiveG1SettledAt_of_gateOff
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest) {r : Round} (hr : 0 < r)
    {M : Height} (hpost : S.E.t_GST ≤ S.a (r - 1))
    (hprev : ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (r - 1))).h_max = M)
    (hfrontier : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a r)).h_max = M)
    (hgateOff : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (S.a r)).h_j + 2 ≤ M)
    (hhor : S.a r ≤ rho.horizon) :
    NamedLiveG1SettledAt S rho r := by
  have hsb := slashableBound_of_admissible_belowOneThird S adm hfb
  have hquiet := previousActionCarriersQuietAt_of_gateOff S adm hsb hr hpost
    hprev hfrontier hgateOff hhor
  have hwindow : RelativeCarrierWindowAt S rho (r - 1) .g1 :=
    relativeCarrierWindowAt_of_gateOff S adm hfb hr hpost hprev hfrontier
      hgateOff ((FrameForward.domain_le_a S r .g1).trans hhor)
  have hmajority : Internal.NamedOutageEntry.GradeFormingMajority S rho r :=
    gradeFormingMajority_of_admissible_belowOneThird S adm hfb hr
      ((FrameForward.domain_le_a S r .g2).trans hhor)
  exact namedLiveG1SettledAt_of_previousActionCarriersQuiet
    S adm hr hwindow hmajority hquiet

end DecoupledConsensusModel.Proofs.HealingSurface

end
