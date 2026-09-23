module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.PhaseGradeQueries
public import DecoupledConsensusInternal.Definitions.ActionSources
public import DecoupledConsensusProofs.Protocol.ValidatorClient.Engine

@[expose] public section

/-! # Row 31 (`Q31_actionSGBlock_tiers`, `actionSGBlockAt_tiers`)

The action's SG vote (`actionSGBlockAt`) recomputes the grade contract's own
`sgVote` selector (`Protocol.get_sg_vote_with`/`Protocol.currentSGVote`) at the
prepared action read, so its value is exactly one of `currentSGVote`'s four
arms: the veto-free walk between the anchor and `live_confirmed`, the active
G2 candidate, the FG root (raw G2 present but no active candidate), or the
anchor itself. This is a case split on that one definition, not a runtime
fact — no fault bound, delivery or provenance hypothesis is used.

The one non-cosmetic step is that `actionSGBlockAt` names its round from the
store's own slot (`S.hc.round_of st.s`) rather than taking the row's `r` as an
argument, so the proof first shows the two rounds agree
(`q31_round_of_slotOf_a`, `q31_action_round_eq`) — pure schedule arithmetic
on `Setup`, restated here because `Proofs.HealingLemmas.ActionRound`/`.Schedule`
sit above this row's import list ( already isolated the same
three steps for exactly this reason). -/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingLemmas
namespace Rows

open Internal Execution Internal.PhaseGrades Proofs.HealingSurface
variable {V : Type} [DecidableEq V] [Fintype V]

/-- A time inside slot `s`'s own window names slot `s`. -/
private theorem q31_slotOfTime_add (Δ : Time) (hΔ : 0 < Δ) (s : Slot) (r : Time)
    (hr0 : 0 ≤ r) (hr : r < 4 * Δ) : slotOfTime Δ (4 * Δ * (s : Time) + r) = s := by
  have hne : (4 : Time) * Δ ≠ 0 := by
    have h : ∀ d : Int, 0 < d → (4 : Int) * d ≠ 0 := by intro d hd; omega
    exact h Δ hΔ
  unfold slotOfTime
  have hrw : 4 * Δ * (s : Time) + r = r + (s : Time) * (4 * Δ) := by ring
  rw [hrw, Int.add_mul_fdiv_right _ _ hne, Int.fdiv_eq_zero_of_lt hr0 hr, zero_add]
  simp

/-- The slot-`s` evaluation happens in slot `s + 1`. -/
private theorem q31_slotOf_confirmation_time (E : Env V) (s : Slot) :
    E.slotOf (Protocol.confirmation_time E s) = s + 1 := by
  have h : ∀ d : Int, 0 < d → (0 : Int) ≤ 2 * d ∧ 2 * d < 4 * d := by intro d hd; omega
  obtain ⟨h0, h1⟩ := h E.Δ E.Δ_pos
  have hrw : Protocol.confirmation_time E s
      = 4 * E.Δ * ((s + 1 : Slot) : Time) + 2 * E.Δ := by
    unfold Protocol.confirmation_time Env.t slotStart
    push_cast
    ring
  rw [Env.slotOf, hrw]
  exact q31_slotOfTime_add E.Δ E.Δ_pos (s + 1) (2 * E.Δ) h0 h1

/-- `round(rR + 1) = r`. The one explicit use of `HealConfig.R_ge_two`. -/
private theorem q31_round_of_opening_succ (hc : Protocol.HealConfig) (r : Round) :
    hc.round_of (hc.opening_slot r + 1) = r := by
  have key : ∀ R n : Nat, 2 ≤ R → (n * R + 1) / R = n := by
    intro R n hR
    have hR0 : 0 < R := by omega
    have hcomm : n * R + 1 = 1 + R * n := by ring
    rw [hcomm, Nat.add_mul_div_left _ _ hR0, Nat.div_eq_of_lt (by omega), Nat.zero_add]
  simp only [Protocol.HealConfig.round_of, Protocol.HealConfig.opening_slot]
  exact key hc.R r hc.R_ge_two

/-- **The action time names its own round.** -/
private theorem q31_round_of_slotOf_a (S : Setup V) (r : Round) :
    S.hc.round_of (S.E.slotOf (S.a r)) = r := by
  have hslot : S.E.slotOf (S.a r) = S.hc.opening_slot r + 1 := by
    rw [Setup.a, Protocol.a_eq_confirmation_time]
    exact q31_slotOf_confirmation_time S.E (S.hc.opening_slot r)
  rw [hslot, q31_round_of_opening_succ]

/-- Clock staging and confirmation update both name the store's slot at the
action time; only `setClock` writes it. -/
private theorem q31_action_round_eq (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    S.hc.round_of (actionReadAt S rho v r).st.core.s = r := by
  have h : (actionReadAt S rho v r).st.core.s = S.E.slotOf (S.a r) := rfl
  rw [h]
  exact q31_round_of_slotOf_a S r

theorem q31_actionsgblock_tiers (S : Setup V) (rho : Run V) :
    Internal.PhaseGrades.Q31_actionSGBlock_tiers S rho := by
  intro v r n A
  set st := n.st.core.toHealing with hst_def
  set c := n.cache with hc_def
  have hk : S.hc.round_of st.s = r := q31_action_round_eq S rho v r
  set grades := DecoupledConsensusModel.Protocol.frameGradeRead c S.E S.hc st r with hgrades_def
  have heq : actionSGBlockAt S rho v r = Protocol.currentSGVote st grades := by
    show Protocol.get_sg_vote_with (NamedProfile.gradeContract c) S.E S.hc st
        (S.hc.round_of st.s)
        (Protocol.grade2_block_with (NamedProfile.gradeContract c) S.E S.hc st
          (S.hc.round_of st.s))
      = Protocol.currentSGVote st grades
    rw [hk]
    rfl
  rcases hdc : Protocol.deepest_clear (some grades.anchor) st.live_confirmed grades.clear
      with _ | B
  · rcases hq2 : grades.Q2 with _ | Q
    · by_cases hraw : grades.rawG2
      · have hval : Protocol.currentSGVote st grades = Protocol.get_fg_root st.toFG := by
          unfold Protocol.currentSGVote
          simp only [hdc, hq2, if_pos hraw]
        rw [heq, hval]
        exact Or.inr (Or.inr (Or.inl ⟨hq2, hraw, rfl⟩))
      · have hval : Protocol.currentSGVote st grades = grades.anchor := by
          unfold Protocol.currentSGVote
          simp only [hdc, hq2, if_neg hraw]
        rw [heq, hval]
        exact Or.inr (Or.inr (Or.inr ⟨hq2, hraw, rfl⟩))
    · have hval : Protocol.currentSGVote st grades = Q := by
        unfold Protocol.currentSGVote
        simp only [hdc, hq2]
      rw [heq, hval]
      exact Or.inr (Or.inl ⟨Q, hq2, rfl⟩)
  · have hval : Protocol.currentSGVote st grades = B := by
      unfold Protocol.currentSGVote
      simp only [hdc]
    rw [heq, hval]
    have hmem := Proofs.Engine.deepest?_mem hdc
    unfold Protocol.deepest_clear at hmem
    have hmem' := Finset.mem_filter.mp hmem
    refine Or.inl ⟨hmem'.2.1, Proofs.Engine.deepest_clear_preceq hdc, hmem'.2.2⟩

#print axioms q31_actionsgblock_tiers

end Rows
end HealingLemmas
end Proofs
end DecoupledConsensusModel

end
