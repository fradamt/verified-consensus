module
public import DecoupledConsensusStatements.Generic.Conditions
public import Mathlib.Tactic

@[expose] public section

namespace DecoupledConsensusModel.Proofs.Generic

open DecoupledConsensusModel
open DecoupledConsensusModel.Statements.Generic

variable {V : Type} {P : DecoupledConsensusModel.Generic.ProtocolSpec V}
  [DecidableEq V] [_root_.Fintype V]
variable {I : Interface P} {C : Constants}
  {rho : DecoupledConsensusModel.Generic.Run V P.Object} {g : Output P}
  {t₀ D : Time} {gap : Nat}

namespace StrongMultiProposerRecurrence

omit [DecidableEq V] [_root_.Fintype V] in
/-- Strong multi-proposer recurrence gives multi-proposer recurrence when the
period is positive. -/
theorem toMultiProposerRecurrence
    {I : Interface P} {C : Constants}
    {rho : DecoupledConsensusModel.Generic.Run V P.Object} {t₀ : Time} {gap : Nat}
    (h : DecoupledConsensusModel.Statements.Generic.StrongMultiProposerRecurrence
      I C rho t₀ gap) (hperiod : 0 < C.period) :
    DecoupledConsensusModel.Statements.Generic.MultiProposerRecurrence I C rho t₀ gap := by
  intro t ht hhor
  obtain ⟨s, hslo, hsupper, hcarrier, _hlookback⟩ := h t ht hhor
  have htwo : 0 < 2 * C.period := by
    exact mul_pos (by norm_num) hperiod
  exact ⟨s, lt_of_lt_of_le (lt_add_of_pos_right t htwo) hslo, hsupper, hcarrier⟩

end StrongMultiProposerRecurrence

namespace MultiProposerRecurrence

omit [DecidableEq V] [_root_.Fintype V] in
/-- Tier-2 multi-proposer recurrence gives tier-1 recurrence from `t₀` when
the proposer window is positive. -/
theorem toSingleProposerRecurrence
    {I : Interface P} {C : Constants}
    {rho : DecoupledConsensusModel.Generic.Run V P.Object} {t₀ : Time} {gap : Nat}
    (h : DecoupledConsensusModel.Statements.Generic.MultiProposerRecurrence
      I C rho t₀ gap) (ht₀ : 0 ≤ t₀) (hslots : 0 < C.proposerSlots) :
    DecoupledConsensusModel.Statements.Generic.SingleProposerRecurrence
      I C rho t₀ gap := by
  intro t ht hhor
  obtain ⟨s, hsAfter, hsupper, hwindow⟩ := h t ht hhor
  have hs_honest : I.proposer s ∈ rho.honest := by
    simpa using hwindow.2 0 hslots
  exact ⟨s, hsAfter, hsupper, hs_honest⟩

end MultiProposerRecurrence

omit [_root_.Fintype V] in
/-- Inclusion is the stronger property: with tier-1 recurrence within `gap`
periods, it yields liveness with delay `gap · period + D`. -/
theorem liveFrom_of_includedFrom
    (hmono : MonotoneFrom P rho g t₀)
    (hfuture : NoFutureRead P I rho g)
    (hincl : IncludedFrom P I rho g t₀ D)
    (hrec : SingleProposerRecurrence I C rho t₀ gap)
    (ht₀ : 0 ≤ t₀) (hD : 0 ≤ D)
    (hperiod : 0 < C.period)
    (hpreceqTrans : ∀ {A B C : Block V}, Block.Preceq A B → Block.Preceq B C →
      Block.Preceq A C)
    (hpreceqRefl : ∀ A : Block V, Block.Preceq A A)
    (hcompatibleOfCommon : ∀ {A B C : Block V}, Block.Preceq A C → Block.Preceq B C →
      Block.compatible A B = true) :
    LiveFrom P I rho g t₀ ((gap : Time) * C.period + D) := by
  intro t ht hdeadline
  have hgapDeadline : t + (gap : Time) * C.period ≤ rho.horizon := by
    have hbase : (gap : Time) * C.period ≤ (gap : Time) * C.period + D := by
      exact le_add_of_nonneg_right hD
    have hshift : t + (gap : Time) * C.period ≤
        t + ((gap : Time) * C.period + D) := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hbase t
    exact hshift.trans hdeadline
  obtain ⟨s, hsAfter, hsupper, hs_honest⟩ := hrec t ht hgapDeadline
  have htincl : t₀ < I.proposalTime s := ht.trans_lt hsAfter
  have hpropD : I.proposalTime s + D ≤ rho.horizon := by
    calc
      I.proposalTime s + D ≤ t + ((gap : Time) * C.period + D) := by
        simpa [add_assoc, add_comm, add_left_comm] using add_le_add_right hsupper D
      _ ≤ rho.horizon := hdeadline
  obtain ⟨B, hBprop, hBin⟩ := hincl s htincl hs_honest hpropD
  have hfinalle : I.proposalTime s + D ≤
      t + ((gap : Time) * C.period + D) := by
    simpa [add_assoc, add_comm, add_left_comm] using add_le_add_right hsupper D
  have ht0propD : t₀ ≤ I.proposalTime s + D := by
    exact (le_of_lt htincl).trans (le_add_of_nonneg_right hD)
  have hBfinal : ∀ v ∈ rho.honest,
      Block.Preceq B (readAt P rho g v
        (t + ((gap : Time) * C.period + D))) := by
    intro v hv
    exact hpreceqTrans (hBin v hv)
      (hmono v hv (I.proposalTime s + D)
        (t + ((gap : Time) * C.period + D))
        ht0propD hfinalle hdeadline)
  have hdelay : 0 ≤ (gap : Time) * C.period + D := by
    have hgap : (0 : Time) ≤ (gap : Time) := by
      exact_mod_cast Nat.zero_le gap
    exact add_nonneg (mul_nonneg hgap hperiod.le) hD
  have htfinal : t ≤ t + ((gap : Time) * C.period + D) := by
    nlinarith
  refine ⟨B, ?_, ?_, ?_⟩
  · exact ⟨s, hsAfter, hBprop⟩
  · intro v hv
    have hfuture := hfuture v hv t s B hBprop hsAfter
    have hmono_t := hmono v hv t
      (t + ((gap : Time) * C.period + D)) ht htfinal hdeadline
    have hcompat := hcompatibleOfCommon hmono_t (hBfinal v hv)
    simp only [Block.compatible, Bool.or_eq_true] at hcompat
    rcases hcompat with hTB | hBT
    · have hneq : readAt P rho g v t ≠ B := by
        intro heq
        apply hfuture
        rw [heq]
        exact hpreceqRefl _
      simp only [Block.Prec, Block.prec, hneq, decide_false, Bool.not_false,
        Bool.true_and]
      exact hTB
    · exact False.elim (hfuture hBT)
  · intro v hv
    exact hBfinal v hv

end DecoupledConsensusModel.Proofs.Generic

end
