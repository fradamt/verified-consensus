module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.ModelVocabulary.Execution.Setup
public import DecoupledConsensusProofs.ModelVocabulary.Protocol.Handlers
public import DecoupledConsensusProofs.Protocol.Handlers.TickBridges

@[expose] public section

/-! Existing local schedule, stamp and pool-projection theorems.
No run-level or round-uniformity premise is introduced. -/

namespace DecoupledConsensusModel.Execution
open Protocol (ChainState HeightConfig)
variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Execution

namespace DecoupledConsensusModel.Protocol
open Protocol (HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Protocol

namespace DecoupledConsensusModel.Protocol
open Protocol (ChainState HeightConfig)
open Protocol (Record)
open Protocol (HealConfig)
open Internal
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

end DecoupledConsensusModel.Protocol

namespace DecoupledConsensusModel.Protocol
open Internal
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The preceding round belongs to every nonempty relative-SG window. -/
theorem pred_mem_latest_window (etaSG r : Round) (heta : 1 ≤ etaSG)
    (hr : 0 < r) : r - 1 ∈ Protocol.latest_window etaSG r := by
  simp only [Protocol.latest_window, List.mem_range']
  refine ⟨r - 1 - (r - etaSG), ?_, ?_⟩
  · have key : ∀ (e n : Nat), 1 ≤ e → 0 < n →
        n - 1 - (n - e) < min n e := by
      intro e n he hn
      omega
    exact key etaSG r heta hr
  · have key : ∀ (e n : Nat), 1 ≤ e → 0 < n →
        n - 1 = n - e + 1 * (n - 1 - (n - e)) := by
      intro e n he hn
      omega
    exact key etaSG r heta hr

#print axioms pred_mem_latest_window
end DecoupledConsensusModel.Protocol

namespace DecoupledConsensusModel.Proofs.HealingLemmas
open Protocol (HealConfig)
open Internal
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The slot of an instant of `[t_s + 2Δ, t_s + 3Δ)` is `s`
(PROTOCOL.md#the-complete-protocol). `Proofs.Optimistic.slotOf_of_between` with the offset shifted
by one `Δ`; the two together cover the second half of a slot. -/
theorem slotOf_of_between' (E : Env V) (s : Slot) {p : Time}
    (hlo : Protocol.support_cutoff E s ≤ p) (hhi : p < Protocol.view_freeze E s) :
    E.slotOf p = s := by
  have hbounds : ∀ a d q : Int, 0 < d → a + 2 * d ≤ q → q < a + 3 * d →
      0 ≤ q - a ∧ q - a < 4 * d := by
    intro a d q hd h1 h2; omega
  obtain ⟨h0, h1⟩ := hbounds (E.t s) E.Δ p E.Δ_pos hlo hhi
  have hrw : p = 4 * E.Δ * (s : Time) + (p - E.t s) := by
    unfold Env.t slotStart
    ring
  rw [Env.slotOf, hrw]
  exact DecoupledConsensusModel.Proofs.Optimistic.slotOfTime_add E.Δ E.Δ_pos s _ h0 h1

/-- **`round(rR + 1) = r`** (PROTOCOL.md#the-complete-protocol). The one explicit use of
`HealConfig.R_ge_two`: with `R = 1` the slot after the opening slot is the
opening slot of round `r + 1` and the action would fire in the next round.

Stated over `Nat` rather than at `Slot`/`Round`, for the reason row H2.1 records:
`omega` matches the syntactic type and does not reduce the abbreviation. -/
theorem round_of_opening_succ (hc : HealConfig) (r : Round) :
    hc.round_of (hc.opening_slot r + 1) = r := by
  have key : ∀ R n : Nat, 2 ≤ R → (n * R + 1) / R = n := by
    intro R n hR
    have hR0 : 0 < R := by omega
    have hcomm : n * R + 1 = 1 + R * n := by ring
    rw [hcomm, Nat.add_mul_div_left _ _ hR0, Nat.div_eq_of_lt (by omega), Nat.zero_add]
  simp only [Protocol.HealConfig.round_of, Protocol.HealConfig.opening_slot]
  exact key hc.R r hc.R_ge_two


/-- **The action time names its own round** (PROTOCOL.md#the-complete-protocol). This is
row OC.'s missing arithmetic: `round(slot(a_r)) = r`. -/
theorem round_of_slotOf_a (S : Setup V) (r : Round) :
    S.hc.round_of (S.E.slotOf (S.a r)) = r := by
  have hslot : S.E.slotOf (S.a r) = S.hc.opening_slot r + 1 := by
    rw [Setup.a, Protocol.a_eq_confirmation_time]
    exact DecoupledConsensusModel.Proofs.Optimistic.slotOf_confirmation_time
      S.E (S.hc.opening_slot r)
  rw [hslot, round_of_opening_succ]

/-- `a_r` is a public time (PROTOCOL.md#the-complete-protocol): `a_r = Δ(4rR + 6)`. -/
theorem publicTime_a (S : Setup V) (r : Round) : PublicTime S (S.a r) := by
  refine ⟨4 * (S.hc.opening_slot r) + 6, ?_⟩
  unfold Setup.a HealConfig.a slotStart
  push_cast
  ring

/-- `a_r` is not negative (PROTOCOL.md#the-complete-protocol). -/
theorem a_nonneg (S : Setup V) (r : Round) : (0 : Time) ≤ S.a r := by
  have h : ∀ d n : Int, 0 < d → 0 ≤ n → 0 ≤ 4 * d * n + 6 * d := by
    intro d n hd hn
    have h4 : (0 : Int) ≤ 4 * d := by omega
    have := Int.mul_nonneg h4 hn
    omega
  unfold Setup.a HealConfig.a slotStart
  exact h S.E.Δ _ S.E.Δ_pos (Int.natCast_nonneg _)

/-- `a_r + Δ` is the view freeze of `a_r`'s own slot (PROTOCOL.md#the-complete-protocol,
114–115). The bracket's right endpoint. -/
theorem a_add_delta_eq_view_freeze (S : Setup V) (r : Round) :
    S.a r + S.E.Δ = Protocol.view_freeze S.E (S.hc.opening_slot r + 1) := by
  rw [Setup.a, Protocol.a_eq_support_cutoff_succ]
  unfold Protocol.support_cutoff Protocol.view_freeze
  have h : ∀ a d : Int, a + 2 * d + d = a + 3 * d := by intro a d; ring
  exact h _ _

/-- **The slot of a store whose clock is in `[a_r, a_r + Δ)`** — `rR + 1`
(PROTOCOL.md#the-complete-protocol). -/
theorem slotOf_of_between_a (S : Setup V) (r : Round) {p : Time}
    (hlo : S.a r ≤ p) (hhi : p < S.a r + S.E.Δ) :
    S.E.slotOf p = S.hc.opening_slot r + 1 := by
  refine slotOf_of_between' S.E _ ?_ ?_
  · rw [← Protocol.a_eq_support_cutoff_succ]; exact hlo
  · rw [← a_add_delta_eq_view_freeze]; exact hhi

/-- **`a_{r+k} = a_r + 4Δ·R·k`** (PROTOCOL.md#the-complete-protocol). The round
schedule is arithmetic, so a bound in rounds is a bound in `Time`. -/
theorem a_add_rounds (S : Setup V) (r k : Round) :
    S.a (r + k) = S.a r + 4 * S.E.Δ * (S.hc.R * k : Nat) := by
  unfold Setup.a HealConfig.a HealConfig.opening_slot slotStart
  push_cast
  ring

/-- The bound is not negative, which is `Internal.HealingReachesAlignedRound`'s
first conjunct. -/
theorem bound_nonneg (S : Setup V) (n : Round) :
    (0 : Time) ≤ 4 * S.E.Δ * (S.hc.R * n : Nat) := by
  have hΔ : (0 : Time) ≤ 4 * S.E.Δ := by
    have h : ∀ d : Int, 0 < d → (0 : Int) ≤ 4 * d := by intro d hd; omega
    exact h S.E.Δ S.E.Δ_pos
  exact Int.mul_nonneg hΔ (Int.natCast_nonneg _)

/-- One complete round boundary leaves a full network delay between an action
and every later opening proposal. -/
theorem action_add_delta_le_openingProposal_of_round_lt
    (S : Setup V) {r q : Round} (hrq : r < q) :
    S.a r + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q) := by
  have hslots :
      S.hc.opening_slot r + 2 ≤ S.hc.opening_slot q := by
    unfold HealConfig.opening_slot
    calc
      r * S.hc.R + 2 ≤ r * S.hc.R + S.hc.R :=
        Nat.add_le_add_left S.hc.R_ge_two (r * S.hc.R)
      _ = (r + 1) * S.hc.R := by ring
      _ ≤ q * S.hc.R :=
        Nat.mul_le_mul_right S.hc.R (Nat.succ_le_iff.mpr hrq)
  have key : ∀ x y : Nat, ∀ d : Int, 0 < d → x + 2 ≤ y →
      4 * d * (x : Int) + 6 * d + d ≤ 4 * d * (y : Int) := by
    intro x y d hd hxyNat
    have hseven : 6 * d + d ≤ 4 * d * 2 := by omega
    have hxy : (x : Int) + 2 ≤ (y : Int) := by
      exact_mod_cast hxyNat
    have hfactor : (0 : Int) ≤ 4 * d := by omega
    calc
      4 * d * (x : Int) + 6 * d + d ≤
          4 * d * (x : Int) + 4 * d * 2 := by
        simpa only [add_assoc] using
          (Int.add_le_add_left hseven (4 * d * (x : Int)))
      _ = 4 * d * ((x : Int) + 2) := by ring
      _ ≤ 4 * d * (y : Int) :=
        Int.mul_le_mul_of_nonneg_left hxy hfactor
  unfold Setup.a HealConfig.a Protocol.proposal_time Env.t slotStart
  exact key _ _ S.E.Δ S.E.Δ_pos hslots

/-- A recurrence window ending at the action time of its last round is inside
the run whenever that action time is inside the run. -/
theorem openingProposal_window_le_action (S : Setup V) (r gap : Round) :
    Protocol.proposal_time S.E (S.hc.opening_slot r) +
      gap * (S.a 1 - S.a 0) ≤ S.a (r + gap) := by
  have hperiod : S.a 1 - S.a 0 = 4 * S.E.Δ * (S.hc.R : Time) := by
    unfold Setup.a Protocol.HealConfig.a Protocol.HealConfig.opening_slot slotStart
    push_cast
    ring
  have haction : S.a r =
      Protocol.proposal_time S.E (S.hc.opening_slot r) + 6 * S.E.Δ := rfl
  rw [a_add_rounds, hperiod, haction]
  push_cast
  nlinarith [S.E.Δ_pos]

#print axioms slotOf_of_between'
#print axioms round_of_opening_succ
#print axioms round_of_slotOf_a
#print axioms publicTime_a
#print axioms a_nonneg
#print axioms a_add_delta_eq_view_freeze
#print axioms slotOf_of_between_a
#print axioms a_add_rounds
#print axioms bound_nonneg
#print axioms action_add_delta_le_openingProposal_of_round_lt
end DecoupledConsensusModel.Proofs.HealingLemmas

namespace DecoupledConsensusModel.Proofs.Assembly
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-- `a_r ≤ a_{r'}` for `r ≤ r'` (PROTOCOL.md#the-complete-protocol). -/
theorem a_mono (S : Setup V) {r r' : Round} (h : r ≤ r') : S.a r ≤ S.a r' := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Proofs.HealingLemmas.a_add_rounds]
  have hadd : ∀ x p : Int, 0 ≤ p → x ≤ x + p := by intro x p hp; omega
  exact hadd _ _ (Proofs.HealingLemmas.bound_nonneg S k)

#print axioms a_mono
end DecoupledConsensusModel.Proofs.Assembly

namespace DecoupledConsensusModel.Protocol
open Internal
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The start of `slotOf(t)` is at or before every nonnegative `t`. -/
theorem proposal_time_slotOf_le (E : Env V) {t : Time} (ht : 0 ≤ t) :
    Protocol.proposal_time E (E.slotOf t) ≤ t := by
  unfold Protocol.proposal_time Env.t slotStart Env.slotOf slotOfTime
  have hd : 0 < 4 * E.Δ := Int.mul_pos (by norm_num) E.Δ_pos
  have hq : 0 ≤ Int.fdiv t (4 * E.Δ) :=
    Int.fdiv_nonneg ht (le_of_lt hd)
  rw [Int.toNat_of_nonneg hq]
  rw [Int.fdiv_eq_ediv_of_nonneg _ (le_of_lt hd), Int.mul_comm]
  exact Int.ediv_mul_le t (ne_of_gt hd)

/-- Once the proposal instant of slot `s` has passed, `slotOf` is at least
`s`. -/
theorem slot_le_slotOf_of_proposal_time_le (E : Env V) {s : Slot} {t : Time}
    (h : Protocol.proposal_time E s ≤ t) : s ≤ E.slotOf t := by
  have ht0 : 0 ≤ t :=
    le_trans (DecoupledConsensusModel.Proofs.Optimistic.proposal_time_nonneg E s) h
  have hd : 0 < 4 * E.Δ := Int.mul_pos (by norm_num) E.Δ_pos
  have hmul : (s : Int) * (4 * E.Δ) ≤ t := by
    unfold Protocol.proposal_time Env.t slotStart at h
    calc
      (s : Int) * (4 * E.Δ) = 4 * E.Δ * (s : Int) := by ring
      _ ≤ t := h
  have hdiv : (s : Int) ≤ t / (4 * E.Δ) :=
    (Int.le_ediv_iff_mul_le hd).2 hmul
  have hq0 : 0 ≤ t / (4 * E.Δ) :=
    Int.ediv_nonneg ht0 (le_of_lt hd)
  unfold Env.slotOf slotOfTime
  rw [Int.fdiv_eq_ediv_of_nonneg _ (le_of_lt hd)]
  exact (Int.le_toNat hq0).2 hdiv

/-- Slot starts are monotone in their slot number. -/
theorem proposal_time_mono (E : Env V) {s s' : Slot} (h : s ≤ s') :
    Protocol.proposal_time E s ≤ Protocol.proposal_time E s' := by
  unfold Protocol.proposal_time Env.t slotStart
  have hc : (0 : Int) ≤ 4 * E.Δ :=
    Int.mul_nonneg (by norm_num) (le_of_lt E.Δ_pos)
  exact Int.mul_le_mul_of_nonneg_left (by exact_mod_cast h) hc

#print axioms proposal_time_slotOf_le
#print axioms slot_le_slotOf_of_proposal_time_le
#print axioms proposal_time_mono
end DecoupledConsensusModel.Protocol

end
