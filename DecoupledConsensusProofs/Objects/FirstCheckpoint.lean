module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.IntrinsicEntry
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Data.Nat.Find

@[expose] public section

namespace DecoupledConsensusModel.Proofs.NamedFirstCheckpoint
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedJointOutage
variable {V : Type} [DecidableEq V] [Fintype V]

private theorem round_le_action (S : Setup V) (r : Round) : (r : Time) ≤ S.a r := by
  have hR : 0 < S.hc.R := by have := S.hc.R_ge_two; omega
  have hRcast : (0 : Time) < (S.hc.R : Time) := by exact_mod_cast hR
  have hscale : (1 : Time) ≤ 4 * S.E.Δ * (S.hc.R : Time) := by
    have hp := Int.mul_pos (Int.mul_pos (show (0 : Time) < 4 by norm_num) S.E.Δ_pos) hRcast
    exact Int.add_one_le_iff.mpr hp
  have hscaled : (r : Time) ≤ (4 * S.E.Δ * (S.hc.R : Time)) * (r : Time) := by
    simpa only [one_mul] using
      Int.mul_le_mul_of_nonneg_right hscale (Int.natCast_nonneg r)
  have hpad : (0 : Time) ≤ 6 * S.E.Δ :=
    Int.mul_nonneg (by norm_num) (le_of_lt S.E.Δ_pos)
  calc
    (r : Time) ≤ (4 * S.E.Δ * (S.hc.R : Time)) * (r : Time) := hscaled
    _ ≤ (4 * S.E.Δ * (S.hc.R : Time)) * (r : Time) + 6 * S.E.Δ :=
      le_add_of_nonneg_right hpad
    _ = S.a r := by
      unfold Setup.a Protocol.HealConfig.a Protocol.HealConfig.opening_slot slotStart
      push_cast
      ring

private theorem action_at_or_after_exists (S : Setup V) (b0 : Time) :
    ∃ r : Round, b0 ≤ S.a r := by
  obtain ⟨r, hr⟩ := exists_nat_gt b0
  exact ⟨r, hr.le.trans (round_le_action S r)⟩

private theorem formation_margin_action_deadline (S : Setup V) (s : Round) (b0 : Time)
    (hmargin : FormationMargin S s b0) : S.a s + S.E.Δ ≤ b0 := by
  have hfirst := Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt S
    (Nat.lt_succ_self s)
  have hnext : Protocol.proposal_time S.E (S.hc.opening_slot (s + 1)) ≤
      formationConfirmationTime S (s + 1) + S.E.Δ := by
    change Protocol.proposal_time S.E (S.hc.opening_slot (s + 1)) ≤
      Protocol.proposal_time S.E (S.hc.opening_slot (s + 1)) + 2 * S.E.Δ + S.E.Δ
    have hd : 0 ≤ S.E.Δ := le_of_lt S.E.Δ_pos
    have hnonneg : 0 ≤ 2 * S.E.Δ + S.E.Δ :=
      add_nonneg (Int.mul_nonneg (by norm_num) hd) hd
    calc
      _ ≤ Protocol.proposal_time S.E (S.hc.opening_slot (s + 1)) +
          (2 * S.E.Δ + S.E.Δ) := le_add_of_nonneg_right hnonneg
      _ = _ := by ring
  have hmargin' := old_margin_of_new S s b0 hmargin
  have hfirst' : S.a s + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot (s + 1)) := by
    simpa only [Nat.succ_eq_add_one] using hfirst
  exact hfirst'.trans (hnext.trans hmargin')

private theorem first_action_selection (S : Setup V) (b0 : Time) (s : Round)
    (hmargin : FormationMargin S s b0) :
    ∃ r : Round, 0 < r ∧ b0 ≤ S.a r ∧
      (∀ q : Round, 0 < q → b0 ≤ S.a q → r ≤ q) ∧
      S.a (r - 1) < b0 := by
  have hdeadline := formation_margin_action_deadline S s b0 hmargin
  have ha : S.a s < b0 :=
    (lt_add_of_pos_right (S.a s) S.E.Δ_pos).trans_le hdeadline
  have ha0 : S.a 0 < b0 := (Assembly.a_mono S (Nat.zero_le s)).trans_lt ha
  have hex := action_at_or_after_exists S b0
  let r := Nat.find hex
  have hbound : b0 ≤ S.a r := Nat.find_spec hex
  have hpos : 0 < r := by
    by_contra hnot
    have hz : r = 0 := by omega
    rw [hz] at hbound
    exact (not_le_of_gt ha0) hbound
  have hminimal : ∀ q : Round, 0 < q → b0 ≤ S.a q → r ≤ q := by
    intro q _ hq
    exact Nat.find_min' hex hq
  have hpred : r - 1 < r := by omega
  have hcut : S.a (r - 1) < b0 := lt_of_not_ge (Nat.find_min hex hpred)
  exact ⟨r, hpos, hbound, hminimal, hcut⟩

/-- Select the first post-boundary action independently of the finite
horizon. Initial high-entry history holds at that selected round even if
its checkpoint lies beyond the run; the latter case is exposed explicitly. -/
theorem first_checkpoint_history_cases
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s : Round)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (Pn : NamedBlock V) (hPn : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase) :
    ∃ r : Round, 0 < r ∧ b0 ≤ S.a r ∧
      (∀ q : Round, 0 < q → b0 ≤ S.a q → r ≤ q) ∧
      S.a (r - 1) < b0 ∧ IntrinsicHighEntryHistory S rho Pn r ∧
      (RoundIncluded S rho b0 r ∨
        (b0 ≤ rho.horizon ∧ rho.horizon < S.a r ∧
          (∀ q : Round, ¬ RoundIncluded S rho b0 q) ∧
          ∀ t : Time, b0 ≤ t → t ≤ rho.horizon →
            S.a (r - 1) < t ∧ t < S.a r)) := by
  obtain ⟨r, hpos, hbound, hminimal, hcut⟩ := first_action_selection S b0 s hmargin
  have hhistory := Proofs.NamedIntrinsicEntry.initial_intrinsic_history S rho b0 Pn r hPn hno hcut
  refine ⟨r, hpos, hbound, hminimal, hcut, hhistory, ?_⟩
  by_cases hwithin : S.a r ≤ rho.horizon
  · exact Or.inl ⟨hpos, hbound, hwithin⟩
  · have hshort : rho.horizon < S.a r := lt_of_not_ge hwithin
    refine Or.inr ⟨hexec.interval.2.1.trans hexec.interval.2.2, hshort, ?_, ?_⟩
    · intro q hq
      have hrq := hminimal q hq.1 hq.2.1
      have hle : S.a r ≤ rho.horizon := (Assembly.a_mono S hrq).trans hq.2.2
      exact (not_le_of_gt hshort) hle
    · intro t hlow hhigh
      exact ⟨hcut.trans_le hlow, hhigh.trans_lt hshort⟩

end DecoupledConsensusModel.Proofs.NamedFirstCheckpoint

end
