module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Records
public import DecoupledConsensusProofs.ModelVocabulary.Execution.Setup

@[expose] public section

/-!
# The action time names its own round 

`round(slot(a_r)) = r`, at a level low enough for the §6 action lemmas.

`Proofs.HealingLemmas.Schedule` already proves this, and `NamedActionSources.action_timing`
repackages it for the named read, but both sit above `Bridges`, so the healing
surface cannot reach either. The three arithmetic steps below carry no runtime,
handler or admissibility content, so they are restated here.
-/



namespace DecoupledConsensusModel.Proofs.HealingLemmas.ActionRound

open Protocol (HealConfig)
open Execution (Setup)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A time inside slot `s`'s own window names slot `s`. -/
theorem slotOfTime_add (Δ : Time) (hΔ : 0 < Δ) (s : Slot) (r : Time)
    (hr0 : 0 ≤ r) (hr : r < 4 * Δ) : slotOfTime Δ (4 * Δ * (s : Time) + r) = s := by
  have hne : (4 : Time) * Δ ≠ 0 := by
    have h : ∀ d : Int, 0 < d → (4 : Int) * d ≠ 0 := by intro d hd; omega
    exact h Δ hΔ
  unfold slotOfTime
  have hrw : 4 * Δ * (s : Time) + r = r + (s : Time) * (4 * Δ) := by ring
  rw [hrw, Int.add_mul_fdiv_right _ _ hne, Int.fdiv_eq_zero_of_lt hr0 hr, zero_add]
  simp

/-- The slot-`s` evaluation happens in slot `s + 1`. -/
theorem slotOf_confirmation_time (E : Env V) (s : Slot) :
    E.slotOf (Protocol.confirmation_time E s) = s + 1 := by
  have h : ∀ d : Int, 0 < d → (0 : Int) ≤ 2 * d ∧ 2 * d < 4 * d := by intro d hd; omega
  obtain ⟨h0, h1⟩ := h E.Δ E.Δ_pos
  have hrw : Protocol.confirmation_time E s
      = 4 * E.Δ * ((s + 1 : Slot) : Time) + 2 * E.Δ := by
    unfold Protocol.confirmation_time Env.t slotStart
    push_cast
    ring
  rw [Env.slotOf, hrw]
  exact slotOfTime_add E.Δ E.Δ_pos (s + 1) (2 * E.Δ) h0 h1

/-- `round(rR + 1) = r`. The one explicit use of `HealConfig.R_ge_two`. -/
theorem round_of_opening_succ (hc : HealConfig) (r : Round) :
    hc.round_of (hc.opening_slot r + 1) = r := by
  have key : ∀ R n : Nat, 2 ≤ R → (n * R + 1) / R = n := by
    intro R n hR
    have hR0 : 0 < R := by omega
    have hcomm : n * R + 1 = 1 + R * n := by ring
    rw [hcomm, Nat.add_mul_div_left _ _ hR0, Nat.div_eq_of_lt (by omega), Nat.zero_add]
  simp only [Protocol.HealConfig.round_of, Protocol.HealConfig.opening_slot]
  exact key hc.R r hc.R_ge_two

/-- **The action time names its own round.** -/
theorem round_of_slotOf_a (S : Setup V) (r : Round) :
    S.hc.round_of (S.E.slotOf (S.a r)) = r := by
  have hslot : S.E.slotOf (S.a r) = S.hc.opening_slot r + 1 := by
    rw [Setup.a, Protocol.a_eq_confirmation_time]
    exact slotOf_confirmation_time S.E (S.hc.opening_slot r)
  rw [hslot, round_of_opening_succ]

end DecoupledConsensusModel.Proofs.HealingLemmas.ActionRound

end
