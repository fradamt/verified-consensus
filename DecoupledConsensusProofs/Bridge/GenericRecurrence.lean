module
public import DecoupledConsensusStatements.Instantiation
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Bridge.GenericParticipation
public import DecoupledConsensusProofs.Objects.AdmissibleCore

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

namespace DecoupledConsensusModel
namespace Proofs

open Internal Execution Statements
open Statements.Generic

variable {V : Type} [DecidableEq V] [Fintype V]


private theorem opening_time_formula (S : Setup V) (r : Round) :
    Protocol.proposal_time S.E (S.hc.opening_slot r) =
      4 * S.E.Δ * ((r : Time) * (S.hc.R : Time)) := by
  unfold Protocol.proposal_time Env.t slotStart Protocol.HealConfig.opening_slot
  push_cast
  ring

private theorem round_period_eq (S : Setup V) :
    S.a 1 - S.a 0 = 4 * S.E.Δ * (S.hc.R : Time) := by
  unfold Setup.a Protocol.HealConfig.a Protocol.HealConfig.opening_slot slotStart
  push_cast
  ring

theorem concretePeriod_pos (S : Setup V) : 0 < S.a 1 - S.a 0 := by
  rw [round_period_eq S]
  have hR : (0 : Time) < (S.hc.R : Time) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two
  nlinarith [S.E.Δ_pos]

theorem constants_valid (S : Setup V) :
    (Statements.Instantiation.constants S).Valid := by
  refine {
    period_pos := ?_
    participationWindow_nonneg := ?_
    participationLag_nonneg := ?_
    proposerSlots_pos := ?_
    maxGap_ge_two := ?_
    delays_nonneg := ?_
    prefixEnd_le_recoveryEnd := ?_
    outage_window_nonempty := ?_ }
  · simpa [Statements.Instantiation.constants] using concretePeriod_pos S
  · dsimp [Statements.Instantiation.constants]
    exact mul_nonneg (by positivity) (concretePeriod_pos S).le
  · simpa [Statements.Instantiation.constants] using (concretePeriod_pos S).le
  · simp [Statements.Instantiation.constants]
  · exact (by decide : (2 : Nat) ≤ 4).trans S.cfg.K_ge_four
  · intro gap
    have hΔ : (0 : Time) ≤ S.E.Δ := S.E.Δ_pos.le
    have hperiod : 0 < S.a 1 - S.a 0 := concretePeriod_pos S
    have hgap : (0 : Time) ≤ (gap : Time) := by positivity
    have hgapη : (0 : Time) ≤ (gap + S.hc.η_SG : Nat) := by positivity
    have hboundary_nonneg : ∀ k : Round,
        0 ≤ Statements.Instantiation.healingBoundaryTime S (k + 1) - S.a 0 := by
      intro k
      apply sub_nonneg.mpr
      exact (Assembly.a_mono S (Nat.zero_le _)).trans
        (a_le_healingBoundaryTime S _)
    have hstartup : 0 ≤
        Statements.Instantiation.healingBoundaryTime S
          (Statements.Instantiation.finalityStartup S gap
            (S.cfg.timeoutDelay / S.hc.R - 2) + 1) - S.a 0 :=
      hboundary_nonneg _
    have hdeadline : 0 ≤
        Statements.Instantiation.healingBoundaryTime S
          (Statements.Instantiation.finalityDeadline S gap
            (S.cfg.timeoutDelay / S.hc.R - 2) + 1) - S.a 0 :=
      hboundary_nonneg _
    dsimp [Statements.Instantiation.constants]
    exact ⟨by positivity,
      add_nonneg (mul_nonneg hgap hperiod.le) (by positivity),
      add_nonneg (mul_nonneg hgapη hperiod.le) (by positivity),
      add_nonneg (by positivity)
        (add_nonneg (mul_nonneg hgapη hperiod.le) (by positivity)),
      hstartup,
      add_nonneg hdeadline (by positivity)⟩
  · intro t₀ gap
    dsimp [Statements.Instantiation.constants]
    exact a_le_healingBoundaryTime S _
  · intro T
    have hround :
        S.hc.round_of (S.E.slotOf
          (Statements.Instantiation.nextAction S T)) =
          Statements.Instantiation.roundAfter S T := by
      simpa [Statements.Instantiation.nextAction] using
        Proofs.HealingLemmas.round_of_slotOf_a S
          (Statements.Instantiation.roundAfter S T)
    have hperiod : S.a 1 - S.a 0 = Statements.Instantiation.roundLength S := by
      rw [NamedOutageClosure.a_succ_roundLength S 0]
      exact add_sub_cancel_left _ _
    have ha :
        S.a (Statements.Instantiation.roundAfter S T + S.hc.η_SG + 1) =
          Statements.Instantiation.nextAction S T +
            ((S.hc.η_SG : Time) + 1) *
              Statements.Instantiation.roundLength S := by
      unfold Statements.Instantiation.nextAction
      rw [NamedOutageClosure.a_eq_roundLength,
        NamedOutageClosure.a_eq_roundLength]
      push_cast
      ring
    change Statements.Instantiation.nextAction S T +
        (S.a 1 - S.a 0) + S.E.Δ <
      Protocol.early S.E S.hc
        (S.hc.round_of (S.E.slotOf
          (Statements.Instantiation.nextAction S T)) + S.hc.η_SG + 1) .g2
    rw [hround, NamedOutageClosure.early_g2_eq, ha, hperiod]
    unfold Statements.Instantiation.roundLength
    have hbound :
        (4 : Time) ≤ (S.hc.R : Time) * (S.hc.η_SG : Time) := by
      exact_mod_cast S.outage_window
    nlinarith [S.E.Δ_pos, hbound]

theorem openingProposalTime_eq_period (S : Setup V) (r : Round) :
    Protocol.proposal_time S.E (S.hc.opening_slot r) =
      (r : Time) * (S.a 1 - S.a 0) := by
  rw [opening_time_formula S r, round_period_eq S]
  push_cast
  ring

private theorem opening_round_bounds (S : Setup V) {r r' gap : Round}
    (hlo : Protocol.proposal_time S.E (S.hc.opening_slot r) ≤
      Protocol.proposal_time S.E (S.hc.opening_slot r'))
    (hhi : Protocol.proposal_time S.E (S.hc.opening_slot r') ≤
      Protocol.proposal_time S.E (S.hc.opening_slot r) +
        (gap : Time) * (S.a 1 - S.a 0)) :
    r ≤ r' ∧ r' ≤ r + gap := by
  have hΔ : (0 : Time) < S.E.Δ := S.E.Δ_pos
  have hfactor : (0 : Time) < 4 * S.E.Δ := by nlinarith
  have hL : S.a 1 - S.a 0 = 4 * S.E.Δ * (S.hc.R : Time) := by
    unfold Setup.a Protocol.HealConfig.a Protocol.HealConfig.opening_slot slotStart
    push_cast
    ring
  rw [opening_time_formula S r, opening_time_formula S r'] at hlo
  rw [opening_time_formula S r, opening_time_formula S r'] at hhi
  rw [hL] at hhi
  have hlo' : (4 * S.E.Δ) * ((r : Time) * (S.hc.R : Time)) ≤
      (4 * S.E.Δ) * ((r' : Time) * (S.hc.R : Time)) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hlo
  have hhi' : (4 * S.E.Δ) * ((r' : Time) * (S.hc.R : Time)) ≤
      (4 * S.E.Δ) * (((r + gap : Nat) : Time) * (S.hc.R : Time)) := by
    simpa [Nat.cast_add, add_mul, mul_add, mul_assoc, mul_left_comm, mul_comm] using hhi
  have hlowR : (r : Time) * (S.hc.R : Time) ≤
      (r' : Time) * (S.hc.R : Time) :=
    Int.le_of_mul_le_mul_left hlo' hfactor
  have hhighR : (r' : Time) * (S.hc.R : Time) ≤
      ((r + gap : Nat) : Time) * (S.hc.R : Time) :=
    Int.le_of_mul_le_mul_left hhi' hfactor
  have hRpos : 0 < S.hc.R := Nat.lt_of_lt_of_le (by decide) S.hc.R_ge_two
  have hlowNat : r * S.hc.R ≤ r' * S.hc.R := by exact_mod_cast hlowR
  have hhighNat : r' * S.hc.R ≤ (r + gap) * S.hc.R := by exact_mod_cast hhighR
  exact ⟨Nat.le_of_mul_le_mul_right hlowNat hRpos,
    Nat.le_of_mul_le_mul_right hhighNat hRpos⟩

private theorem carrier_named_of_generic
    (S : Setup V) (rho : Run V) {s : Slot} {r' : Round}
    (hs : s = S.hc.opening_slot r')
    (h : Generic.MultiProposerAt (I S) (C S) rho.honest s) :
    Internal.ProposerCarrierAt S rho r' := by
  subst s
  change (∃ r : Round, S.hc.opening_slot r' = S.hc.opening_slot r) ∧
    (∀ k < 3, S.E.proposer (S.hc.opening_slot r' + k) ∈ rho.honest) at h
  have h0 := h.2 0 (by decide)
  have h1 := h.2 1 (by decide)
  have h2 := h.2 2 (by decide)
  exact ⟨by simpa using h0, by simpa using h1, by simpa using h2⟩

theorem proposerRecurrence_of_generic (S : Setup V) (rho : Run V)
    (t₀ : Time) (gap : Round)
    (h : Generic.MultiProposerRecurrence (I S) (C S) rho t₀ gap) :
    Internal.MultiProposerRecurrence S rho gap t₀ := by
  intro r hstart hhor
  obtain ⟨s, hlo, hhi, hcarrier⟩ :=
    h (Protocol.proposal_time S.E (S.hc.opening_slot r)) hstart
      (by simpa [C, Instantiation.constants] using hhor)
  change (∃ r' : Round, s = S.hc.opening_slot r') ∧
    (∀ k < 3, S.E.proposer (s + k) ∈ rho.honest) at hcarrier
  obtain ⟨r', hs⟩ := hcarrier.1
  rw [hs] at hlo hhi
  have hbounds := opening_round_bounds S (by simpa [I] using hlo.le)
    (by simpa [I, C] using hhi)
  refine ⟨r', hbounds.1, hbounds.2, ?_⟩
  exact carrier_named_of_generic S rho hs
    (by exact ⟨⟨r', hs⟩, hcarrier.2⟩)

private theorem earlier_opening_honest
    (S : Setup V) (rho : Run V) {r' k : Round}
    (h : ∀ s', (I S).opening s' →
      Protocol.proposal_time S.E (S.hc.opening_slot r') -
          2 * (S.a 1 - S.a 0) ≤ Protocol.proposal_time S.E s' →
      Protocol.proposal_time S.E s' <
        Protocol.proposal_time S.E (S.hc.opening_slot r') →
      S.E.proposer s' ∈ rho.honest)
    (hk : r' ≤ k + 2) (hupper : k < r') :
    S.E.proposer (S.hc.opening_slot k) ∈ rho.honest := by
  apply h (S.hc.opening_slot k)
  · exact ⟨k, rfl⟩
  · have hL := round_period_eq S
    rw [opening_time_formula S r', opening_time_formula S k, hL]
    have hkr : r' ≤ k + 2 := hk
    have hΔ : (0 : Time) ≤ 4 * S.E.Δ := by nlinarith [S.E.Δ_pos]
    have hmul : (r' : Time) * (S.hc.R : Time) ≤
        ((k + 2 : Nat) : Time) * (S.hc.R : Time) := by
      have hR : (0 : Time) ≤ (S.hc.R : Time) := by positivity
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hkr) hR
    have hmul' := Int.mul_le_mul_of_nonneg_left hmul hΔ
    push_cast at hmul' ⊢
    ring_nf at hmul' ⊢
    nlinarith [hmul']
  · have hslot : S.hc.opening_slot k < S.hc.opening_slot r' := by
      exact Nat.mul_lt_mul_of_pos_right hupper
        (Nat.lt_of_lt_of_le (by decide) S.hc.R_ge_two)
    rw [opening_time_formula S k, opening_time_formula S r']
    have hR : (0 : Time) < (S.hc.R : Time) := by
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two
    have hkr : (k : Time) * (S.hc.R : Time) <
        (r' : Time) * (S.hc.R : Time) := by
      exact mul_lt_mul_of_pos_right (by exact_mod_cast hupper) hR
    have hprod := mul_lt_mul_of_pos_left hkr (show (0 : Time) < 4 * S.E.Δ by
      nlinarith [S.E.Δ_pos])
    nlinarith

theorem openingCarrierRecurrence_of_generic (S : Setup V) (rho : Run V)
    (t₀ : Time) (gap : Round)
    (h : Generic.StrongMultiProposerRecurrence (I S) (C S) rho t₀ gap) :
    Internal.ProposerOpeningCarrierRecurrence S rho gap t₀ := by
  intro k hstart hhor
  obtain ⟨s, hlo, hhi, hcarrier, hopen⟩ :=
    h (Protocol.proposal_time S.E (S.hc.opening_slot k)) hstart
      (by simpa [C, Instantiation.constants] using hhor)
  change (∃ r' : Round, s = S.hc.opening_slot r') ∧
    (∀ j < 3, S.E.proposer (s + j) ∈ rho.honest) at hcarrier
  obtain ⟨r', hs⟩ := hcarrier.1
  rw [hs] at hlo hhi
  have hlo0 : Protocol.proposal_time S.E (S.hc.opening_slot k) ≤
      Protocol.proposal_time S.E (S.hc.opening_slot r') := by
    have hnonneg : (0 : Time) ≤ 2 * (C S).period := by
      have hperiod : 0 < (C S).period := by
        dsimp [C, Instantiation.constants]
        rw [round_period_eq S]
        exact NamedOutageClosure.roundLength_pos S
      exact mul_nonneg (by norm_num) hperiod.le
    exact (le_add_of_nonneg_right hnonneg).trans (by simpa [I] using hlo)
  have hbounds := opening_round_bounds S
    (by simpa [I] using hlo0) (by simpa [I, C] using hhi)
  have hcarrier' := carrier_named_of_generic S rho hs
    (by exact ⟨⟨r', hs⟩, hcarrier.2⟩)
  have hopen' : ∀ s', (I S).opening s' →
      Protocol.proposal_time S.E (S.hc.opening_slot r') -
          2 * (S.a 1 - S.a 0) ≤ Protocol.proposal_time S.E s' →
      Protocol.proposal_time S.E s' <
        Protocol.proposal_time S.E (S.hc.opening_slot r') →
      S.E.proposer s' ∈ rho.honest := by
    simpa [hs, I, C] using hopen
  have hk2 : k + 2 ≤ r' := by
    have htime := hlo
    change Protocol.proposal_time S.E (S.hc.opening_slot k) +
        2 * (C S).period ≤
      Protocol.proposal_time S.E (S.hc.opening_slot r') at htime
    have hperiod : (C S).period = S.a 1 - S.a 0 := rfl
    rw [hperiod, opening_time_formula S k, opening_time_formula S r'] at htime
    have hL := round_period_eq S
    rw [hL] at htime
    have hfac : (0 : Time) < 4 * S.E.Δ := by nlinarith [S.E.Δ_pos]
    have hR : (0 : Time) < (S.hc.R : Time) := by
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two
    have hmul : ((k + 2 : Nat) : Time) * (S.hc.R : Time) ≤
        (r' : Time) * (S.hc.R : Time) := by
      apply le_of_mul_le_mul_left (a := 4 * S.E.Δ)
      · push_cast
        ring_nf at htime ⊢
        exact htime
      · exact hfac
    have hmulNat : (k + 2) * S.hc.R ≤ r' * S.hc.R := by exact_mod_cast hmul
    exact Nat.le_of_mul_le_mul_right hmulNat (Nat.lt_of_lt_of_le (by decide) S.hc.R_ge_two)
  refine ⟨r', hk2, hbounds.2, ?_⟩
  refine ⟨?_, ?_, hcarrier'⟩
  · have hr2 : 2 ≤ r' := (Nat.le_add_left 2 k).trans hk2
    apply earlier_opening_honest S rho (r' := r') (k := r' - 2) hopen'
    · simpa [Nat.sub_add_cancel hr2]
    · have hupper2 : r' - 2 < r' :=
        Nat.sub_lt_of_pos_le (a := 2) (b := r') (by decide) hr2
      exact hupper2
  · have hr1 : 1 ≤ r' := by
      have hone : 1 ≤ k + 2 := by
        simpa [Nat.add_assoc] using Nat.succ_le_succ (Nat.zero_le (k + 1))
      exact hone.trans hk2
    apply earlier_opening_honest S rho (r' := r') (k := r' - 1) hopen'
    · calc
        r' = r' - 1 + 1 := (Nat.sub_add_cancel hr1).symm
        _ ≤ r' - 1 + 2 := by
          simpa [Nat.add_assoc] using (Nat.le_add_right (r' - 1 + 1) 1)
    · have hupper1 : r' - 1 < r' :=
        Nat.sub_lt_of_pos_le (a := 1) (b := r') (by decide) hr1
      exact hupper1

end Proofs
end DecoupledConsensusModel

end
