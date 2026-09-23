module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.NamedJointOutage

@[expose] public section

/-!
# Interval induction for `RoundInvariant`

Generic scaffolding for the P1/P2 named-outage second half (addendum 34,
). `roundInvariant_all` lifts a per-round step lemma for
`RoundInvariant` to every included round above the base round ``, using
`roundIncluded_of_between` to certify inclusion at every intermediate round.
The step lemma itself is supplied by the caller; nothing here is specific
to its proof.
-/


namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open DecoupledConsensusModel.Protocol (HealConfig)
open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Internal.NamedJointOutage
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- `S.a` is monotone in the round: `a_r = t_{rR} + 6Δ` and `rR` is monotone
in `r` since `R: Nat` and `Δ ≥ 0`. -/
theorem a_mono (S : Setup V) {r r' : Round} (h : r ≤ r') : S.a r ≤ S.a r' := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  show S.hc.a S.E.Δ r ≤ S.hc.a S.E.Δ (r + k)
  have hadd : S.hc.a S.E.Δ (r + k) =
      S.hc.a S.E.Δ r + 4 * S.E.Δ * (S.hc.R * k : Nat) := by
    unfold HealConfig.a HealConfig.opening_slot slotStart
    push_cast
    ring
  rw [hadd]
  have hΔ : (0 : Time) ≤ 4 * S.E.Δ := by
    have key : ∀ d : Int, 0 < d → (0 : Int) ≤ 4 * d := by intro d hd; omega
    exact key S.E.Δ S.E.Δ_pos
  have hrk : (0 : Time) ≤ ((S.hc.R * k : Nat) : Time) := Int.natCast_nonneg _
  exact Int.le_add_of_nonneg_right (Int.mul_nonneg hΔ hrk)





end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
