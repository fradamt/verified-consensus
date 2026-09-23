module
public import DecoupledConsensusStatements.Instantiation
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Bridge.GenericExecution
public import DecoupledConsensusProofs.Execution.HealthyLocalFacts
public import DecoupledConsensusProofs.Protocol.Grades.Inclusions
public import DecoupledConsensusProofs.Protocol.Handlers.StableOutputSeed

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

namespace DecoupledConsensusModel
namespace Proofs

open Internal Execution Statements
open Statements.Generic
open DecoupledConsensusModel.Protocol
open Proofs.NamedOutageClosure

variable {V : Type} [DecidableEq V] [Fintype V]

noncomputable abbrev C (S : Setup V) := Statements.Instantiation.constants S
abbrev L (S : Setup V) : Time := S.a 1 - S.a 0

private theorem round_length_eq (S : Setup V) :
    S.a 1 - S.a 0 = Statements.Instantiation.roundLength S := by
  rw [NamedOutageClosure.a_succ_roundLength S 0]
  exact add_sub_cancel_left _ _

private theorem L_pos (S : Setup V) : 0 < L S := by
  unfold L
  rw [round_length_eq S]
  exact NamedOutageClosure.roundLength_pos S

private theorem action_formula (S : Setup V) (r : Round) :
    S.a r = S.a 0 + (r : Time) * L S := by
  rw [NamedOutageClosure.a_eq_roundLength S r,
    NamedOutageClosure.a_eq_roundLength S 0]
  unfold L
  rw [round_length_eq S]
  push_cast
  ring

private theorem action_time_lt_of_lt (S : Setup V) {i j : Round} (hij : i < j) :
    S.a i < S.a j := by
  rw [action_formula S i, action_formula S j]
  have hdiff : 0 < (j : Time) - (i : Time) := by
    have hlt : (i : Time) < (j : Time) := by exact_mod_cast hij
    exact sub_pos.mpr hlt
  have hprod : 0 < ((j : Time) - (i : Time)) * L S :=
    mul_pos hdiff (L_pos S)
  nlinarith

private theorem action_window_lower (S : Setup V) {η r j : Nat}
    (hlo : r - η ≤ j) :
    S.a r - (η : Time) * L S ≤ S.a j := by
  rw [action_formula S r, action_formula S j]
  by_cases hη : η ≤ r
  · have hsub : ((r - η : Nat) : Time) = (r : Time) - (η : Time) :=
      Int.ofNat_sub hη
    have hcast : ((r - η : Nat) : Time) ≤ (j : Time) := by exact_mod_cast hlo
    have hcoef : (r : Time) - (η : Time) ≤ (j : Time) := by
      rw [← hsub]
      exact hcast
    have hmul := Int.mul_le_mul_of_nonneg_right hcoef (L_pos S).le
    nlinarith
  · have hlt : r < η := Nat.lt_of_not_ge hη
    have hle : (r : Time) ≤ (η : Time) := by exact_mod_cast (Nat.le_of_lt hlt)
    have hprod : ((r : Time) - (η : Time)) * L S ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hle) (L_pos S).le
    nlinarith

private theorem ediv_round_of_bounds (S : Setup V) {x : Time} {r : Round}
    (hL : 0 < L S) (hlo : (r : Time) * L S ≤ x)
    (hhi : x < ((r + 1 : Nat) : Time) * L S) :
    Int.toNat (x / L S) = r := by
  have hlow : (r : Time) ≤ x / L S := by
    apply (Int.le_ediv_iff_mul_le hL).2
    simpa [mul_comm] using hlo
  have hupp : x / L S < (r : Time) + 1 := by
    apply (Int.ediv_lt_iff_lt_mul hL).2
    simpa [Nat.cast_add, Nat.cast_one, add_mul] using hhi
  let q : Time := x / L S
  have hlow' : (r : Time) ≤ q := by simpa [q] using hlow
  have hupp' : q < (r : Time) + 1 := by simpa [q] using hupp
  have hq : q = (r : Time) := le_antisymm
    (Int.le_of_lt_add_one hupp') hlow'
  have hx : x / L S = (r : Time) := by simpa [q] using hq
  simp [hx]

private theorem actionRound_eq_of_formula_bounds (S : Setup V) {t : Time}
    {r : Round} (hlo : S.a r ≤ t) (hhi : t < S.a (r + 1)) :
    Instantiation.actionRound S t = r := by
  have hL : 0 < L S := L_pos S
  have h0 : ¬ t < S.a 0 := by
    intro ht
    have hle : S.a 0 ≤ S.a r := by
      rw [action_formula S r]
      exact le_add_of_nonneg_right (by
        have : (0 : Time) ≤ (r : Time) := by positivity
        exact mul_nonneg this hL.le)
    exact (not_lt_of_ge (hle.trans hlo)) ht
  simp only [Instantiation.actionRound, if_neg h0]
  apply ediv_round_of_bounds S hL
  · rw [action_formula S r] at hlo
    have hA0 : S.a 0 = 6 * S.E.Δ := by
      rw [NamedOutageClosure.a_eq_roundLength]
      simp
    rw [← hA0]
    apply (le_sub_iff_add_le).2
    simpa [add_comm] using hlo
  · rw [action_formula S (r + 1)] at hhi
    have hA0 : S.a 0 = 6 * S.E.Δ := by
      rw [NamedOutageClosure.a_eq_roundLength]
      simp
    rw [← hA0]
    apply (sub_lt_iff_lt_add).2
    simpa [add_comm] using hhi

theorem actionRound_a (S : Setup V) (r : Round) :
    Instantiation.actionRound S (S.a r) = r := by
  exact actionRound_eq_of_formula_bounds S le_rfl
    (by rw [NamedOutageClosure.a_succ_roundLength]
        exact lt_add_of_pos_right _ (by
          exact NamedOutageClosure.roundLength_pos S))

theorem actionRound_of_mem (S : Setup V) {r : Round} {t : Time}
    (hlo : S.a r ≤ t) (hhi : t < S.a (r + 1)) :
    Instantiation.actionRound S t = r :=
  actionRound_eq_of_formula_bounds S hlo hhi

theorem actionRound_lt (S : Setup V) {t : Time} (h : t < S.a 0) :
    Instantiation.actionRound S t = 0 := by
  simp [Instantiation.actionRound, h]

private theorem actionRound_bounds_of_ge (S : Setup V) {t : Time}
    (ht : S.a 0 ≤ t) :
    S.a (Instantiation.actionRound S t) ≤ t ∧
      t < S.a (Instantiation.actionRound S t + 1) := by
  have hL : 0 < L S := L_pos S
  have hA0 : S.a 0 = 6 * S.E.Δ := by
    rw [NamedOutageClosure.a_eq_roundLength]
    simp
  have hq0 : 0 ≤ (t - 6 * S.E.Δ) / (S.a 1 - S.a 0) := by
    apply Int.ediv_nonneg
    · rw [← hA0]
      exact sub_nonneg.mpr ht
    · exact hL.le
  have htoNat :
      ((Int.toNat ((t - 6 * S.E.Δ) / (S.a 1 - S.a 0)) : Nat) : Time) =
        (t - 6 * S.E.Δ) / (S.a 1 - S.a 0) := by
    exact Int.toNat_of_nonneg hq0
  have hlow :
      ((Int.toNat ((t - 6 * S.E.Δ) / (S.a 1 - S.a 0)) : Nat) : Time) *
          (S.a 1 - S.a 0) ≤ t - 6 * S.E.Δ := by
    rw [htoNat]
    exact Int.ediv_mul_le _ (ne_of_gt hL)
  have hupp :
      t - 6 * S.E.Δ <
        (((Int.toNat ((t - 6 * S.E.Δ) / (S.a 1 - S.a 0)) : Nat) : Time) + 1) *
          (S.a 1 - S.a 0) := by
    rw [htoNat]
    exact Int.lt_ediv_add_one_mul_self _ hL
  have hif : ¬ t < S.a 0 := not_lt_of_ge ht
  simp only [Instantiation.actionRound, if_neg hif]
  have hformula : S.a (Int.toNat ((t - 6 * S.E.Δ) / (S.a 1 - S.a 0))) =
      S.a 0 +
        ((Int.toNat ((t - 6 * S.E.Δ) / (S.a 1 - S.a 0)) : Nat) : Time) * L S := by
    rw [action_formula S]
  constructor
  · rw [hformula]
    have hlow' :
        ((Int.toNat ((t - 6 * S.E.Δ) / (S.a 1 - S.a 0)) : Nat) : Time) * L S ≤
          t - S.a 0 := by
      simpa [L, hA0] using hlow
    linarith
  ·
    have hformulaNext :
        S.a (Int.toNat ((t - 6 * S.E.Δ) / (S.a 1 - S.a 0)) + 1) =
          S.a 0 +
            (((Int.toNat ((t - 6 * S.E.Δ) / (S.a 1 - S.a 0)) : Nat) : Time) + 1) *
              L S := by
      rw [action_formula S]
      push_cast
      ring
    have hupp' : t - S.a 0 <
        (((Int.toNat ((t - 6 * S.E.Δ) / (S.a 1 - S.a 0)) : Nat) : Time) + 1) * L S := by
      simpa [L, hA0] using hupp
    rw [hformulaNext]
    linarith

theorem awakeIn_action_window (S : Setup V) (H : Finset V) (k r : Nat)
    (hr : 0 < r) (hk : 0 < k) :
    awakeIn (E S) H (S.a r - k * L S) (S.a r) =
      H.filter (fun v =>
        (Protocol.latest_window k r).any (fun j => (S.node v).awake j)) := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨hvH, u, hlu, huu, hawake⟩ := Finset.mem_filter.mp hv
    change (S.node v).awake (Instantiation.actionRound S u) = true at hawake
    apply Finset.mem_filter.mpr
    refine ⟨hvH, List.any_eq_true.mpr ?_⟩
    by_cases hu0 : u < S.a 0
    · have hkr : r ≤ k := by
        have hlow := hlu
        rw [action_formula S r] at hlow
        rw [action_formula S 0] at hu0
        have hL : 0 < L S := L_pos S
        have hrt : (0 : Time) ≤ r := by positivity
        have hkt : (0 : Time) ≤ k := by positivity
        by_contra hnot
        have hlt : k < r := Nat.lt_of_not_ge hnot
        have hdiff : 0 < (r : Time) - (k : Time) := by
          have hltT : (k : Time) < (r : Time) := by exact_mod_cast hlt
          exact sub_pos.mpr hltT
        have hprod : 0 < ((r : Time) - (k : Time)) * L S :=
          mul_pos hdiff hL
        ring_nf at hlow hu0
        nlinarith [hprod]
      have hrk : r - k = 0 := Nat.sub_eq_zero_of_le hkr
      have hmem : 0 ∈ Protocol.latest_window k r := by
        apply NamedOutageClosure.mem_latest_window
        · simpa [hrk]
        · exact hr
      refine ⟨0, hmem, ?_⟩
      exact (actionRound_lt S hu0 ▸ hawake)
    · have huge : S.a 0 ≤ u := le_of_not_gt hu0
      obtain ⟨huj, hujnext⟩ := actionRound_bounds_of_ge S huge
      let j := Instantiation.actionRound S u
      have hlowj : r - k ≤ j := by
        by_cases hrk : r < k
        · have hzero : r - k = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hrk)
          simp [hzero]
        · have hkr : k ≤ r := le_of_not_gt hrk
          have hlowj' : ((r - k : Nat) : Time) ≤ (j : Time) := by
            have hlow := hlu
            rw [action_formula S r, action_formula S 0] at hlow
            have hujnext' : u < S.a (j + 1) := by simpa [j] using hujnext
            rw [action_formula S (j + 1)] at hujnext'
            have hL : 0 < L S := L_pos S
            have hsub : ((r - k : Nat) : Time) = (r : Time) - (k : Time) :=
              Int.ofNat_sub hkr
            rw [hsub]
            have hlow_lt :
                S.a 0 + (r : Time) * L S - (k : Time) * L S <
                  S.a 0 + ((j : Time) + 1) * L S := by
              simp only [Nat.cast_zero, zero_mul, add_zero] at hlow
              push_cast at hujnext'
              exact lt_of_le_of_lt hlow hujnext'
            ring_nf at hlow_lt
            have hmul :
                ((r : Time) - (k : Time)) * L S <
                  ((j : Time) + 1) * L S := by
              linarith [hlow_lt]
            exact Int.le_of_lt_add_one ((Int.mul_lt_mul_right hL).mp hmul)
          exact_mod_cast hlowj'
      have hjr : j < r := by
        have hjr' : (j : Time) < (r : Time) := by
          have huj' : S.a j ≤ u := by simpa [j] using huj
          rw [action_formula S j] at huj'
          have huu0 := huu
          rw [action_formula S r] at huu
          have hL : 0 < L S := L_pos S
          by_contra hnot
          have hle : (r : Time) ≤ (j : Time) := le_of_not_gt hnot
          have hneq : (r : Time) ≠ (j : Time) := by
            intro heq
            have heqNat : r = j := by exact_mod_cast heq
            have heqAction : Instantiation.actionRound S u = r := by
              simpa [j] using heqNat.symm
            have huj0 := huj
            rw [heqAction] at huj0
            exact (not_lt_of_ge huj0) huu0
          have hlt : (r : Time) < (j : Time) := lt_of_le_of_ne hle hneq
          have hdiff : 0 < (j : Time) - (r : Time) := sub_pos.mpr hlt
          have hprod : 0 < ((j : Time) - (r : Time)) * L S := mul_pos hdiff hL
          ring_nf at huj' huu
          nlinarith [hprod]
        exact_mod_cast hjr'
      refine ⟨j, NamedOutageClosure.mem_latest_window hlowj hjr, ?_⟩
      exact hawake
  · intro hv
    obtain ⟨hvH, hvAny⟩ := Finset.mem_filter.mp hv
    apply Finset.mem_filter.mpr
    refine ⟨hvH, ?_⟩
    obtain ⟨j, hj, hawake⟩ := List.any_eq_true.mp hvAny
    have hjbounds := NamedOutageClosure.window_bounds hj
    refine ⟨S.a j, ?_, ?_, ?_⟩
    · rw [action_formula S r, action_formula S j]
      have hL : 0 < L S := L_pos S
      have hlow' : (r : Time) - (k : Time) ≤ (j : Time) := by
        by_cases hkr : k ≤ r
        · have hsub : ((r - k : Nat) : Time) = (r : Time) - (k : Time) :=
            Int.ofNat_sub hkr
          rw [← hsub]
          exact_mod_cast hjbounds.1
        · have hrk : r < k := Nat.lt_of_not_ge hkr
          have : (r : Time) - (k : Time) ≤ 0 :=
            sub_nonpos.mpr (by exact_mod_cast (Nat.le_of_lt hrk))
          exact this.trans (by positivity)
      nlinarith
    · rw [action_formula S j, action_formula S r]
      have hL : 0 < L S := L_pos S
      have hdiff : 0 < (r : Time) - (j : Time) := by
        have hlt : (j : Time) < (r : Time) := by
          exact_mod_cast hjbounds.2
        exact sub_pos.mpr hlt
      have hprod : 0 < ((r : Time) - (j : Time)) * L S :=
        mul_pos hdiff hL
      nlinarith
    · change (S.node v).awake (Instantiation.actionRound S (S.a j)) = true
      rw [actionRound_a S j]
      exact hawake

theorem windowMajority_of_generic (S : Setup V) (rho : Run V) (η r : Nat)
    (hr : 0 < r) (hη : 0 < η)
    (h : Generic.WindowMajority (E S) rho.honest (η * L S) (S.a r)) :
    AwakeWindowMajority S.E (fun v => (S.node v).awake)
      rho.honest η r := by
  have hw := awakeIn_action_window S rho.honest η r hr hη
  unfold Generic.WindowMajority at h
  unfold AwakeWindowMajority
  rw [hw] at h
  simpa [E, Instantiation.env, honestAwakeWindow] using h

theorem sleepy_windows_of_generic (S : Setup V) (rho : Run V) (t₀ : Time)
    (η : Nat) (hη : 0 < η)
    (h : ∀ t, t₀ ≤ t → t - L S ≤ rho.horizon →
      Generic.WindowMajority (E S) rho.honest (η * L S) t) :
    ∀ r, 0 < r → t₀ ≤ S.a r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake) rho.honest η r := by
  intro r hr htr hhor
  have hprev : r - 1 + 1 = r := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hr)
  have ha : S.a r - L S = S.a (r - 1) := by
    rw [← hprev, NamedOutageClosure.a_succ_roundLength]
    unfold L
    rw [round_length_eq S]
    exact add_sub_cancel_right _ _
  apply windowMajority_of_generic S rho η r hr hη
  exact h (S.a r) htr (by simpa [ha] using hhor)

theorem allAwake_of_generic (S : Setup V) (rho : Run V)
    (h : Generic.FullParticipation (P := DecoupledConsensusModel.Execution.spec S) (E S) rho) :
    ∀ v ∈ rho.honest, ∀ r, S.a r ≤ rho.horizon →
      (S.node v).awake r = true := by
  intro v hv r hhor
  have h' := h v hv (S.a r) (Proofs.HealingLemmas.a_nonneg S r) hhor
  simpa [E, Instantiation.env, actionRound_a S r] using h'

theorem awakeAt_action (S : Setup V) (rho : Run V) (r : Round) :
    awakeAt (E S) rho.honest (S.a r) =
      NamedOutageEntry.honestAwakeAt S rho r := by
  simp [awakeAt, NamedOutageEntry.honestAwakeAt, Instantiation.env,
    actionRound_a S r]

theorem staleAwake_eq (S : Setup V) (rho : Run V) {r : Round} (hr : 0 < r) :
    awakeIn (E S) rho.honest
        (S.a r - (S.hc.η_SG : Time) * L S) (S.a r - L S) \
      awakeAt (E S) rho.honest (S.a r - L S) =
    NamedOutageEntry.staleAwake S rho r := by
  classical
  have hη : 0 < S.hc.η_SG :=
    Nat.lt_of_lt_of_le Nat.zero_lt_one S.hc.η_SG_ge_one
  have ha : S.a r - L S = S.a (r - 1) := by
    have hprev : r - 1 + 1 = r := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hr)
    rw [← hprev, NamedOutageClosure.a_succ_roundLength]
    unfold L
    rw [round_length_eq S]
    exact add_sub_cancel_right _ _
  have hfull := awakeIn_action_window S rho.honest S.hc.η_SG r hr hη
  have hprevAwake := awakeAt_action S rho (r - 1)
  ext v
  unfold NamedOutageEntry.staleAwake
  constructor
  · intro hv
    rcases Finset.mem_sdiff.mp hv with ⟨hin, hnot⟩
    obtain ⟨hvH, u, hlu, huu, hawake⟩ := Finset.mem_filter.mp hin
    have hnotPrev : v ∉ NamedOutageEntry.honestAwakeAt S rho (r - 1) := by
      intro hvPrev
      apply hnot
      rw [ha, hprevAwake]
      exact hvPrev
    have hvFull : v ∈ awakeIn (E S) rho.honest
        (S.a r - (S.hc.η_SG : Time) * L S) (S.a r) := by
      apply Finset.mem_filter.mpr
      refine ⟨hvH, u, hlu, ?_, hawake⟩
      have hL : 0 ≤ L S := (L_pos S).le
      linarith
    have hvAny : v ∈ rho.honest.filter (fun v =>
        (Protocol.latest_window S.hc.η_SG r).any
          (fun j => (S.node v).awake j)) := by
      rw [← hfull]
      exact hvFull
    obtain ⟨_, hvAny⟩ := Finset.mem_filter.mp hvAny
    obtain ⟨j, hj, hawakej⟩ := List.any_eq_true.mp hvAny
    have hjbounds := NamedOutageClosure.window_bounds hj
    have hjlt : j + 1 < r := by
      by_contra hlt
      have hle1 : j + 1 ≤ r := Nat.succ_le_of_lt hjbounds.2
      have hle2 : r ≤ j + 1 := Nat.le_of_not_gt hlt
      have heqSucc : j + 1 = r := le_antisymm hle1 hle2
      have heq : j = r - 1 := by
        have hsub : r - 1 = j := by
          apply (Nat.sub_eq_iff_eq_add (Nat.succ_le_iff.mpr hr)).2
          simpa [Nat.add_comm] using heqSucc.symm
        exact hsub.symm
      apply hnotPrev
      apply Finset.mem_filter.mpr
      exact ⟨hvH, by simpa [heq] using hawakej⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, hnotPrev⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨j, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr hjbounds.2, ⟨hjbounds.1, hjlt⟩⟩
    · exact Finset.mem_filter.mpr ⟨hvH, hawakej⟩
  · intro hv
    rcases Finset.mem_sdiff.mp hv with ⟨hbi, hnot⟩
    obtain ⟨j, hj, hvj⟩ := Finset.mem_biUnion.mp hbi
    obtain ⟨_, hjcond⟩ := Finset.mem_filter.mp hj
    obtain ⟨hvH, hawakej⟩ := Finset.mem_filter.mp hvj
    have hjprev : j < r - 1 := Nat.lt_sub_iff_add_lt.mpr hjcond.2
    have hjwindow : j ∈ Protocol.latest_window S.hc.η_SG r :=
      NamedOutageClosure.mem_latest_window hjcond.1
        (Nat.lt_of_succ_lt hjcond.2)
    apply Finset.mem_sdiff.mpr
    refine ⟨?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨hvH, ?_⟩
      refine ⟨S.a j, action_window_lower S hjcond.1,
        (by simpa [ha] using action_time_lt_of_lt S hjprev), ?_⟩
      change (S.node v).awake (Instantiation.actionRound S (S.a j)) = true
      rw [actionRound_a S j]
      exact hawakej
    · intro hvAt
      have hvPrev : v ∈ NamedOutageEntry.honestAwakeAt S rho (r - 1) := by
        rw [← hprevAwake, ← ha]
        exact hvAt
      exact hnot hvPrev

theorem awakeGradeMajorityThroughout_of_generic
    (S : Setup V) (rho : Run V)
    (h : ∀ t, L S ≤ t → t ≤ rho.horizon + L S →
      Generic.FreshMajority (E S) rho.honest (C S) t) :
    NamedOutageEntry.AwakeGradeMajorityThroughout S rho := by
  intro r hr hcovered
  have hL : 0 < L S := L_pos S
  have hr1 : (1 : Time) ≤ (r : Time) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hr)
  have ha0 : (0 : Time) ≤ S.a 0 := Proofs.HealingLemmas.a_nonneg S 0
  have hlow : L S ≤ S.a r := by
    rw [action_formula S r]
    nlinarith
  have hhigh : S.a r ≤ rho.horizon + L S := by
    rcases hcovered with haction | ⟨p, hp0, hphor⟩
    · linarith
    · have hdom : S.a r - 7 * S.E.Δ ≤ DecoupledConsensusModel.Protocol.domain S.E S.hc r p := by
        unfold DecoupledConsensusModel.Protocol.domain DecoupledConsensusModel.Protocol.opening
          Protocol.proposal_time Env.t slotStart Setup.a
          Protocol.HealConfig.a Protocol.HealConfig.opening_slot
        cases p <;> simp only [DecoupledConsensusModel.Protocol.Phase.domainOffset] <;>
          unfold slotStart <;> push_cast <;> ring_nf <;>
          nlinarith [S.E.Δ_pos]
      have hLbig : 7 * S.E.Δ ≤ L S := by
        unfold L
        rw [round_length_eq S]
        unfold Statements.Instantiation.roundLength
        have hR : (3 : Time) ≤ (S.hc.R : Time) := by
          exact_mod_cast S.hc.R_ge_three
        have h4 : (0 : Time) ≤ 4 * S.E.Δ := by nlinarith [S.E.Δ_pos]
        have hmul := Int.mul_le_mul_of_nonneg_left hR h4
        nlinarith [S.E.Δ_pos]
      linarith
  have hs := h (S.a r) hlow hhigh
  unfold Generic.FreshMajority at hs
  unfold NamedOutageEntry.AwakeGradeMajority
  have hstale := staleAwake_eq S rho hr
  have ha : S.a r - L S = S.a (r - 1) := by
    have hprevRound : r - 1 + 1 = r :=
      Nat.sub_add_cancel (Nat.succ_le_iff.mpr hr)
    rw [← hprevRound, NamedOutageClosure.a_succ_roundLength]
    unfold L
    rw [round_length_eq S]
    exact add_sub_cancel_right _ _
  have hprev := awakeAt_action S rho (r - 1)
  have hs' :
      (E S).electorate.weightOf ((Finset.univ \ rho.honest) ∪
        (awakeIn (E S) rho.honest
            (S.a r - (S.hc.η_SG : Time) * L S) (S.a r - L S) \
          awakeAt (E S) rho.honest (S.a r - L S))) <
        (E S).electorate.weightOf (awakeAt (E S) rho.honest (S.a r - L S)) := by
    simpa [C, Instantiation.constants] using hs
  rw [hstale, ha, hprev] at hs'
  simpa [E, Instantiation.env] using hs'

end Proofs
end DecoupledConsensusModel

end
