module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.MovingChainCeiling
public import DecoupledConsensusProofs.Execution.MovingChainIterate
public import DecoupledConsensusProofs.Protocol.Grades.MovingChainHandoffBase
public import DecoupledConsensusProofs.Protocol.Schedule.GSTZeroActionHead

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.NamedRecoveryRead
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Schedule arithmetic, reproduced from `MovingChainExecutionRun` -/



/-- The six helpers below are PUBLIC on purpose (the corresponding branch's request): both
this leaf's case split and `completeState_of_handoff` in `W4BaseFoldRun` need
the same ones, and the originals are private inside
`MovingChainExecutionRun`'s Open block, so exporting them here is the only way
to avoid a second copy. Origin for every declaration in this section:
`DecoupledConsensusProofs/HealingSurface/MovingChainExecutionRun.lean`,
reproduced unchanged. No protocol content. -/
private theorem nat_pred_add_one {n : Nat} (hn : 0 < n) : n - 1 + 1 = n :=
  Nat.sub_add_cancel hn

private theorem nat_pred_eq_of_pos_eq_succ {a b : Nat}
    (ha : 0 < a) (h : a = b + 1) : a - 1 = b := by
  omega

private theorem int_add_le_add_right {a b d : Int}
    (hab : a ≤ b) : a + d ≤ b + d :=
  by simpa only [Int.add_comm] using add_le_add_left hab d

private theorem int_add_lt_add_right {a b d : Int}
    (hab : a < b) : a + d < b + d :=
  by simpa only [Int.add_comm] using add_lt_add_left hab d

private theorem int_mul_le_mul_pos {a b d : Int}
    (hab : a ≤ b) (hd : 0 < d) : a * d ≤ b * d :=
  Int.mul_le_mul_of_nonneg_right hab (le_of_lt hd)

private theorem int_mul_lt_mul_pos {a b d : Int}
    (hab : a < b) (hd : 0 < d) : a * d < b * d :=
  Int.mul_lt_mul_of_pos_right hab hd

private theorem proposal_time_normal (E : Env V) (s : Slot) :
    Protocol.proposal_time E s = (4 * (s : Time)) * E.Δ := by
  unfold Protocol.proposal_time Env.t slotStart
  ring

private theorem vote_time_normal (E : Env V) (s : Slot) :
    Protocol.vote_time E s = (4 * (s : Time) + 1) * E.Δ := by
  unfold Protocol.vote_time Env.t slotStart
  ring

private theorem support_cutoff_normal (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s = (4 * (s : Time) + 2) * E.Δ := by
  unfold Protocol.support_cutoff Env.t slotStart
  ring

private theorem confirmation_time_normal (E : Env V) (s : Slot) :
    Protocol.confirmation_time E s = (4 * (s : Time) + 6) * E.Δ := by
  unfold Protocol.confirmation_time Env.t slotStart
  ring

private theorem action_time_normal (S : Setup V) (r : Round) :
    S.a r = (4 * ((S.hc.opening_slot r : Slot) : Time) + 6) * S.E.Δ := by
  unfold Setup.a Protocol.HealConfig.a slotStart
  ring

private theorem gammaNegOne_normal (S : Setup V) (r : Round) :
    S.hc.Γ_neg1 S.E.Δ r =
      (4 * ((S.hc.opening_slot r : Slot) : Time) - 1) * S.E.Δ := by
  unfold Protocol.HealConfig.Γ_neg1 slotStart
  ring

private theorem proposal_time_mono' (E : Env V) {a b : Slot} (hab : a ≤ b) :
    Protocol.proposal_time E a ≤ Protocol.proposal_time E b := by
  rw [proposal_time_normal, proposal_time_normal]
  apply int_mul_le_mul_pos _ E.Δ_pos
  exact_mod_cast Nat.mul_le_mul_left 4 hab

private theorem action_time_mono' (S : Setup V) {a b : Round} (hab : a ≤ b) :
    S.a a ≤ S.a b := by
  rw [action_time_normal, action_time_normal]
  apply int_mul_le_mul_pos _ S.E.Δ_pos
  have hopen : S.hc.opening_slot a ≤ S.hc.opening_slot b := by
    exact Nat.mul_le_mul_right S.hc.R hab
  exact int_add_le_add_right (by exact_mod_cast Nat.mul_le_mul_left 4 hopen)

private theorem round_of_opening_add_three_le_succ
    (hc : Protocol.HealConfig) (q : Round) :
    hc.round_of (hc.opening_slot q + 3) ≤ q + 1 := by
  have hRpos : 0 < hc.R := lt_of_lt_of_le Nat.zero_lt_two hc.R_ge_two
  simp only [Protocol.HealConfig.round_of, Protocol.HealConfig.opening_slot]
  rw [show q * hc.R + 3 = 3 + hc.R * q by ring,
    Nat.add_mul_div_left _ _ hRpos]
  have hdiv : 3 / hc.R ≤ 1 := by
    have hlt : 3 / hc.R < 2 := by
      rw [Nat.div_lt_iff_lt_mul hRpos]
      exact lt_of_lt_of_le (by decide : 3 < 4)
        (by simpa only [Nat.mul_comm] using
          Nat.mul_le_mul_left 2 hc.R_ge_two)
    exact Nat.le_of_lt_succ hlt
  simpa only [Nat.add_comm] using Nat.add_le_add_left hdiv q

private theorem opening_slot_round_of_le
    (hc : Protocol.HealConfig) (s : Slot) :
    hc.opening_slot (hc.round_of s) ≤ s := by
  have hRpos : 0 < hc.R := lt_of_lt_of_le Nat.zero_lt_two hc.R_ge_two
  simp only [Protocol.HealConfig.round_of, Protocol.HealConfig.opening_slot]
  simpa only [Nat.mul_comm] using Nat.div_mul_le_self s hc.R

private theorem round_of_mono'
    (hc : Protocol.HealConfig) {a b : Slot} (hab : a ≤ b) :
    hc.round_of a ≤ hc.round_of b :=
  Nat.div_le_div_right hab

private theorem gammaNegOne_round_of_succ_le_confirmation
    (S : Setup V) (s : Slot) :
    S.hc.Γ_neg1 S.E.Δ (S.hc.round_of (s + 1)) ≤
      Protocol.confirmation_time S.E s := by
  rw [gammaNegOne_normal, confirmation_time_normal]
  apply int_mul_le_mul_pos _ S.E.Δ_pos
  have hopen := opening_slot_round_of_le S.hc (s + 1)
  have hcast : ((S.hc.opening_slot (S.hc.round_of (s + 1)) : Slot) : Time) ≤
      ((s + 1 : Slot) : Time) := by exact_mod_cast hopen
  have hmul : 4 * ((S.hc.opening_slot (S.hc.round_of (s + 1)) : Slot) : Time) ≤
      4 * ((s + 1 : Slot) : Time) :=
    Int.mul_le_mul_of_nonneg_left hcast (by norm_num)
  have hright : 4 * ((s + 1 : Slot) : Time) - 1 ≤ 4 * (s : Time) + 6 := by
    have hsCast : (((s + 1 : Nat) : Int)) = (s : Int) + 1 := by
      push_cast
      rfl
    rw [hsCast]
    ring_nf
    exact int_add_le_add_right (by decide : (3 : Int) ≤ 6)
  exact (sub_le_sub_right hmul 1).trans hright

private theorem gammaNegOne_le_action (S : Setup V) (r : Round) :
    S.hc.Γ_neg1 S.E.Δ r ≤ S.a r := by
  rw [gammaNegOne_normal, action_time_normal]
  apply int_mul_le_mul_pos _ S.E.Δ_pos
  exact (sub_le_self _ (by norm_num)).trans
    (le_add_of_nonneg_right (by norm_num))

private theorem action_le_proposal_plus_two
    (S : Setup V) (q : Round) :
    S.a q ≤ Protocol.proposal_time S.E (S.hc.opening_slot q + 2) := by
  rw [action_time_normal, proposal_time_normal]
  apply int_mul_le_mul_pos _ S.E.Δ_pos
  push_cast
  omega

private theorem boundary_cutoff_le_next_action
    (S : Setup V) (q : Round) :
    Protocol.support_cutoff S.E (S.hc.opening_slot q + 2) ≤ S.a (q + 1) := by
  rw [support_cutoff_normal, action_time_normal]
  apply int_mul_le_mul_pos _ S.E.Δ_pos
  have hopen : S.hc.opening_slot q + S.hc.R =
      S.hc.opening_slot (q + 1) := by
    simp only [Protocol.HealConfig.opening_slot]
    ring
  have hslots : S.hc.opening_slot q + 2 ≤ S.hc.opening_slot (q + 1) := by
    rw [← hopen]
    exact Nat.add_le_add_left S.hc.R_ge_two _
  have hcast : ((S.hc.opening_slot q + 2 : Slot) : Time) ≤
      ((S.hc.opening_slot (q + 1) : Slot) : Time) := by exact_mod_cast hslots
  have hmul := Int.mul_le_mul_of_nonneg_left hcast (by norm_num : (0 : Int) ≤ 4)
  calc
    4 * (((S.hc.opening_slot q + 2 : Slot) : Time)) + 2 ≤
        4 * ((S.hc.opening_slot (q + 1) : Slot) : Time) + 2 :=
      int_add_le_add_right hmul
    _ ≤ 4 * ((S.hc.opening_slot (q + 1) : Slot) : Time) + 6 :=
      by simpa only [Int.add_comm] using
        (int_add_le_add_right (d :=
          4 * ((S.hc.opening_slot (q + 1) : Slot) : Time))
          (by decide : (2 : Int) ≤ 6))

private theorem previous_action_lt_opening_proposal
    (S : Setup V) {r : Round} (hr : 0 < r) :
    S.a (r - 1) < Protocol.proposal_time S.E (S.hc.opening_slot r) := by
  rw [action_time_normal, proposal_time_normal]
  apply int_mul_lt_mul_pos _ S.E.Δ_pos
  have hrpred : r - 1 + 1 = r := nat_pred_add_one hr
  have hopen : S.hc.opening_slot (r - 1) + S.hc.R =
      S.hc.opening_slot r := by
    have := opening_slot_succ_eq S.hc (r - 1)
    rw [hrpred] at this
    exact this.symm
  have hslots : S.hc.opening_slot (r - 1) + 2 ≤ S.hc.opening_slot r := by
    rw [← hopen]
    exact Nat.add_le_add_left S.hc.R_ge_two _
  have hcast : ((S.hc.opening_slot (r - 1) + 2 : Slot) : Time) ≤
      ((S.hc.opening_slot r : Slot) : Time) := by exact_mod_cast hslots
  have hmul := Int.mul_le_mul_of_nonneg_left hcast (by norm_num : (0 : Int) ≤ 4)
  have hlt : 4 * ((S.hc.opening_slot (r - 1) : Slot) : Time) + 6 <
      4 * (((S.hc.opening_slot (r - 1) + 2 : Slot) : Time)) := by
    have hopenCast : (((S.hc.opening_slot (r - 1) + 2 : Slot) : Time)) =
        ((S.hc.opening_slot (r - 1) : Slot) : Time) + 2 := by
      push_cast
      rfl
    rw [hopenCast]
    ring_nf
    exact int_add_lt_add_right (by decide : (6 : Int) < 8)
  exact hlt.trans_le hmul

private theorem opening_slot_eq_of_action_eq_confirmation
    (S : Setup V) {r : Round} {s : Slot}
    (h : S.a r = Protocol.confirmation_time S.E s) :
    S.hc.opening_slot r = s := by
  have hslot := congrArg S.E.slotOf
    ((Protocol.a_eq_confirmation_time S.hc S.E r).symm.trans h)
  rw [Proofs.Optimistic.slotOf_confirmation_time,
    Proofs.Optimistic.slotOf_confirmation_time] at hslot
  exact Nat.add_right_cancel hslot

private theorem proposal_le_vote (E : Env V) (s : Slot) :
    Protocol.proposal_time E s ≤ Protocol.vote_time E s := by
  rw [proposal_time_normal, vote_time_normal]
  apply int_mul_le_mul_pos _ E.Δ_pos
  omega

private theorem proposal_lt_succ (E : Env V) (s : Slot) :
    Protocol.proposal_time E s < Protocol.proposal_time E (s + 1) := by
  rw [proposal_time_normal, proposal_time_normal]
  apply int_mul_lt_mul_pos _ E.Δ_pos
  have hcast : (((s + 1 : Nat) : Int)) = (s : Int) + 1 := by
    push_cast
    rfl
  rw [hcast]
  omega

private theorem proposal_succ_le_confirmation
    (E : Env V) (s : Slot) :
    Protocol.proposal_time E (s + 1) ≤ Protocol.confirmation_time E s := by
  rw [proposal_time_normal, confirmation_time_normal]
  apply int_mul_le_mul_pos _ E.Δ_pos
  push_cast
  omega

private theorem round_of_lt_of_lt_opening
    (hc : Protocol.HealConfig) {s : Slot} {r : Round}
    (h : s < hc.opening_slot r) : hc.round_of s < r := by
  have hRpos : 0 < hc.R := lt_of_lt_of_le Nat.zero_lt_two hc.R_ge_two
  simp only [Protocol.HealConfig.round_of]
  rw [Nat.div_lt_iff_lt_mul hRpos]
  simpa only [Nat.mul_comm] using h

private theorem nat_pred_le_pred {a b : Nat} (h : a ≤ b) : a - 1 ≤ b - 1 :=
  Nat.sub_le_sub_right h 1

private theorem nat_pred_le_of_pos_le_succ {a b : Nat}
    (ha : 0 < a) (h : a ≤ b + 1) : a - 1 ≤ b := by
  exact Nat.lt_succ_iff.mp ((Nat.sub_lt ha (by decide : 0 < 1)).trans_le h)

private theorem nat_add_three_le_succ_of_add_two_le {a c : Nat}
    (h : a + 2 ≤ c) : a + 3 ≤ c + 1 := by omega

private theorem nat_eq_succ_of_nested_bounds_ne {q a b : Nat}
    (hqa : q ≤ a) (hab : a ≤ b) (hb : b ≤ q + 1) (hne : b ≠ a) :
    b = q + 1 := by omega

private theorem nat_eq_succ_of_between {q r : Nat}
    (hlo : q < r) (hhi : r < q + 2) : r = q + 1 := by omega

private theorem nat_pred_ge_of_succ_le {q r : Nat}
    (h : q + 2 ≤ r) : q + 1 ≤ r - 1 := by omega

private theorem nat_le_pred_of_succ_le {a c : Nat}
    (h : a + 1 ≤ c + 1) : a ≤ c := by omega

private theorem nat_false_of_crossed_gap {a c : Nat}
    (hlo : a ≤ c + 1) (hhi : c + 2 ≤ a) : False := by omega


theorem inclusiveEventIndex_le_strictEventIndex_of_lt
    (rho : Run V) {t0 t1 : Time} (hlt : t0 < t1) :
    inclusiveEventIndex rho t0 ≤ strictEventIndex rho t1 := by
  unfold inclusiveEventIndex strictEventIndex
  exact (List.monotone_filter_right rho.events (fun e he => by
    simp only [decide_eq_true_eq] at he ⊢
    exact lt_of_le_of_lt he hlt)).length_le

private theorem nat_add_two_le_pred_of_add_three_le {a c : Nat}
    (h : a + 3 ≤ c) : a + 2 ≤ c - 1 := by omega


private theorem nat_pred_succ {n : Nat} (hn : 0 < n) : n - 1 + 1 = n := by
  omega


theorem events_length_eq_inclusive_horizon
    (S : Setup V) {rho : Run V} (adm : Admissible S rho) :
    rho.events.length = inclusiveEventIndex rho rho.horizon := by
  unfold inclusiveEventIndex
  apply congrArg List.length
  symm
  apply List.filter_eq_self.mpr
  intro e he
  simp only [decide_eq_true_eq]
  exact (adm.in_horizon e he).2



/-! ## The four window-data helpers of the hybrid's case split -/

theorem ceilingWindowData
    (S : Setup V) {rho : Run V}
    {q : Round} {D Prev : Block V} {M0 : Height} {c : Slot}
    (hR0pos : 0 < S.hc.round_of (S.hc.opening_slot q + 3))
    (hpostBase : S.E.t_GST ≤
      S.a (S.hc.round_of (S.hc.opening_slot q + 3) - 1))
    (hcarrierCeiling : ∀ r : Round,
      S.hc.round_of (S.hc.opening_slot q + 3) = r + 1 →
      ∀ u ∈ rho.honest,
        Block.Preceq (actionSGBlockAt S rho u r) D)
    (hcarrierQ : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u q) D)
    (hDPrev : Block.Preceq D Prev)
    (hlower : S.hc.opening_slot q + 2 ≤ c)
    (hupper : c + 1 < S.hc.opening_slot (q + 2))
    (hslotHor : Protocol.confirmation_time S.E c ≤ rho.horizon) :
    MovingSlotWindowDataC S rho M0 c Prev := by
  let R0 := S.hc.round_of (S.hc.opening_slot q + 3)
  let Rc := S.hc.round_of (c + 1)
  let r := Rc - 1
  have hopenLower : S.hc.opening_slot q + 3 ≤ c + 1 :=
    nat_add_three_le_succ_of_add_two_le hlower
  have hR0Rc : R0 ≤ Rc := by
    exact round_of_mono' S.hc hopenLower
  have hqR0 : q ≤ R0 := by
    rw [← round_of_opening_slot_eq_schedule S.hc q]
    exact round_of_mono' S.hc (Nat.le_add_right _ _)
  have hRcUpper : Rc ≤ q + 1 := by
    exact Nat.le_of_lt_succ
      (round_of_lt_of_lt_opening S.hc hupper)
  have hRcpos : 0 < Rc := hR0pos.trans_le hR0Rc
  have hround : S.hc.round_of (c + 1) = r + 1 := by
    simpa only [Rc, r] using (nat_pred_add_one hRcpos).symm
  have hr0r : R0 - 1 ≤ r := by
    simpa only [r] using nat_pred_le_pred hR0Rc
  have hrq : r ≤ q := by
    exact nat_pred_le_of_pos_le_succ hRcpos hRcUpper
  have hcarrier : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) D := by
    by_cases heq : Rc = R0
    · apply hcarrierCeiling r
      rw [← hround]
      exact heq.symm
    · have hRc : Rc = q + 1 :=
        nat_eq_succ_of_nested_bounds_ne hqR0 hR0Rc hRcUpper heq
      have hr : r = q := nat_pred_eq_of_pos_eq_succ hRcpos hRc
      simpa only [hr] using hcarrierQ
  have hpostAction : S.E.t_GST ≤ S.a r :=
    hpostBase.trans (action_time_mono' S hr0r)
  have hpostAtBase : S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q + 2) :=
    hpostBase.trans
      ((action_time_mono' S (nat_pred_le_of_pos_le_succ hR0pos
          (round_of_opening_add_three_le_succ S.hc q))).trans
        (action_le_proposal_plus_two S q))
  have hpostProp : S.E.t_GST ≤ Protocol.proposal_time S.E c :=
    hpostAtBase.trans (proposal_time_mono' S.E hlower)
  refine
    { pos := lt_of_lt_of_le (Nat.zero_lt_succ _) hlower
      round := ⟨r, hround, hpostAction,
        (by rw [← hround]
            exact (gammaNegOne_round_of_succ_le_confirmation S c).trans hslotHor),
        fun u hu => Block.preceq_trans
          (hcarrier u hu) hDPrev⟩
      postVote := hpostProp.trans (proposal_le_vote S.E c)
      postProp := hpostProp
      slotHor := hslotHor }

theorem ceilingActionTiming
    (S : Setup V) {rho : Run V}
    {q : Round} {D Prev : Block V} {c : Slot}
    (hpostQ : S.E.t_GST ≤ S.a q)
    (hcarrierQ : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u q) D)
    (hDPrev : Block.Preceq D Prev)
    (hlower : S.hc.opening_slot q + 2 ≤ c)
    (hupper : c + 1 < S.hc.opening_slot (q + 2))
    (hslotHor : Protocol.confirmation_time S.E c ≤ rho.horizon) :
    MovingSlotActionCeiling S rho c Prev := by
  intro r hr
  have hopen : S.hc.opening_slot r = c :=
    opening_slot_eq_of_action_eq_confirmation S hr
  have hqr : q < r := by
    have hopenLt : S.hc.opening_slot q < S.hc.opening_slot r := by
      rw [hopen]
      exact lt_of_lt_of_le
        (Nat.lt_add_of_pos_right (by decide : 0 < 2)) hlower
    simp only [Protocol.HealConfig.opening_slot] at hopenLt
    exact Nat.lt_of_mul_lt_mul_right hopenLt
  have hrUpper : r < q + 2 := by
    have hopenLt : S.hc.opening_slot r < S.hc.opening_slot (q + 2) := by
      rw [hopen]
      exact (Nat.lt_succ_self c).trans hupper
    simp only [Protocol.HealConfig.opening_slot] at hopenLt
    exact Nat.lt_of_mul_lt_mul_right hopenLt
  have hre : r = q + 1 := nat_eq_succ_of_between hqr hrUpper
  have hrpos : 0 < r := Nat.zero_lt_of_lt hqr
  have hrpred : r - 1 = q := nat_pred_eq_of_pos_eq_succ hrpos hre
  refine ⟨hrpos, ?_, ?_, ?_⟩
  · simpa only [hrpred] using hpostQ
  · exact (gammaNegOne_le_action S r).trans (hr.le.trans hslotHor)
  · simpa only [hrpred] using fun u hu =>
      Block.preceq_trans (hcarrierQ u hu) hDPrev

theorem ordinaryWindowData
    (S : Setup V) {rho : Run V}
    {q : Round} {M0 : Height} {c : Slot}
    (hR0pos : 0 < S.hc.round_of (S.hc.opening_slot q + 3))
    (hpostBase : S.E.t_GST ≤
      S.a (S.hc.round_of (S.hc.opening_slot q + 3) - 1))
    (hlower : S.hc.opening_slot (q + 2) ≤ c + 1)
    (hslotHor : Protocol.confirmation_time S.E c ≤ rho.horizon) :
    MovingSlotWindowData S rho
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0 c := by
  let Rc := S.hc.round_of (c + 1)
  let r := Rc - 1
  have hqRc : q + 2 ≤ Rc := by
    rw [← round_of_opening_slot_eq_schedule S.hc (q + 2)]
    exact round_of_mono' S.hc hlower
  have hRcpos : 0 < Rc :=
    (Nat.zero_lt_succ (q + 1)).trans_le hqRc
  have hround : S.hc.round_of (c + 1) = r + 1 := by
    simpa only [Rc, r] using (nat_pred_add_one hRcpos).symm
  have hq1r : q + 1 ≤ r := by
    dsimp only [r]
    exact nat_pred_ge_of_succ_le hqRc
  have hR0q : S.hc.round_of (S.hc.opening_slot q + 3) - 1 ≤ q :=
    nat_pred_le_of_pos_le_succ hR0pos
      (round_of_opening_add_three_le_succ S.hc q)
  have hR0q1 : S.hc.round_of (S.hc.opening_slot q + 3) - 1 ≤ q + 1 :=
    hR0q.trans (Nat.le_succ q)
  have hpostAction : S.E.t_GST ≤ S.a r :=
    hpostBase.trans (action_time_mono' S (hR0q1.trans hq1r))
  have ht1 : Protocol.support_cutoff S.E (S.hc.opening_slot q + 2) ≤ S.a r :=
    (boundary_cutoff_le_next_action S q).trans (action_time_mono' S hq1r)
  have hbaseLower : S.hc.opening_slot q + 2 ≤ c := by
    have hopen : S.hc.opening_slot q + 4 ≤
        S.hc.opening_slot (q + 2) := by
      have hfour : 4 ≤ 2 * S.hc.R := by
        simpa only [Nat.mul_comm] using Nat.mul_le_mul_left 2 S.hc.R_ge_two
      simp only [Protocol.HealConfig.opening_slot]
      calc
        q * S.hc.R + 4 ≤ q * S.hc.R + 2 * S.hc.R :=
          Nat.add_le_add_left hfour _
        _ = (q + 2) * S.hc.R := by ring
    have hsucc : S.hc.opening_slot q + 3 ≤ c :=
      nat_le_pred_of_succ_le (hopen.trans hlower)
    exact (Nat.add_le_add_left (by decide : 2 ≤ 3) _).trans hsucc
  have hpostAtBase : S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q + 2) :=
    hpostBase.trans
      ((action_time_mono' S hR0q).trans
        (action_le_proposal_plus_two S q))
  have hpostProp : S.E.t_GST ≤ Protocol.proposal_time S.E c :=
    hpostAtBase.trans (proposal_time_mono' S.E hbaseLower)
  refine
    { pos := lt_of_lt_of_le (Nat.zero_lt_succ _) hbaseLower
      round := ⟨r, hround, ht1, hpostAction,
        (by rw [← hround]
            exact (gammaNegOne_round_of_succ_le_confirmation S c).trans hslotHor)⟩
      postVote := hpostProp.trans (proposal_le_vote S.E c)
      postProp := hpostProp
      slotHor := hslotHor }

theorem ordinaryActionTiming
    (S : Setup V) {rho : Run V}
    {q : Round} {c : Slot}
    (hpostQ1 : S.E.t_GST ≤ S.a (q + 1))
    (hlower : S.hc.opening_slot (q + 2) ≤ c + 1)
    (hslotHor : Protocol.confirmation_time S.E c ≤ rho.horizon) :
    MovingSlotActionTiming S rho
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) c := by
  intro r hr
  have hopen : S.hc.opening_slot r = c :=
    opening_slot_eq_of_action_eq_confirmation S hr
  have hq2r : q + 2 ≤ r := by
    by_contra hnot
    have hrle : r ≤ q + 1 := Nat.le_of_lt_succ (Nat.lt_of_not_ge hnot)
    have hopenLe : S.hc.opening_slot r ≤ S.hc.opening_slot (q + 1) := by
      exact Nat.mul_le_mul_right S.hc.R hrle
    have hnext : S.hc.opening_slot (q + 2) =
        S.hc.opening_slot (q + 1) + S.hc.R :=
      opening_slot_succ_eq S.hc (q + 1)
    have hgap : S.hc.opening_slot r + 2 ≤ S.hc.opening_slot (q + 2) := by
      rw [hnext]
      exact (Nat.add_le_add_right hopenLe 2).trans
        (Nat.add_le_add_left S.hc.R_ge_two _)
    rw [hopen] at hgap
    exact nat_false_of_crossed_gap hlower hgap
  have hrpos : 0 < r := (Nat.zero_lt_succ (q + 1)).trans_le hq2r
  have hq1pred : q + 1 ≤ r - 1 := nat_pred_ge_of_succ_le hq2r
  have hpostPrev : S.E.t_GST ≤ S.a (r - 1) :=
    hpostQ1.trans (action_time_mono' S hq1pred)
  have ht1Prev : Protocol.support_cutoff S.E (S.hc.opening_slot q + 2) ≤
      S.a (r - 1) :=
    (boundary_cutoff_le_next_action S q).trans (action_time_mono' S hq1pred)
  have hbefore : S.a (r - 1) < Protocol.proposal_time S.E (c + 1) := by
    have hown := previous_action_lt_opening_proposal S hrpos
    rw [hopen] at hown
    exact hown.trans (proposal_lt_succ S.E c)
  have hprevHor : S.a (r - 1) ≤ rho.horizon :=
    (le_of_lt hbefore).trans
      ((proposal_succ_le_confirmation S.E c).trans hslotHor)
  exact ⟨hrpos, hpostPrev,
    (gammaNegOne_le_action S r).trans (hr.le.trans hslotHor),
    ht1Prev, hprevHor, hbefore⟩

/-! ## The horizon-sensitive hybrid iteration -/

/-! ## The window-facts hybrid and the window step, named -/

theorem MovingSlotFoldAtN.windowFacts_hybrid
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {q : Round} {D : Block V} {M0 : Height}
    (hR0pos : 0 < S.hc.round_of (S.hc.opening_slot q + 3))
    (hpostBase : S.E.t_GST ≤
      S.a (S.hc.round_of (S.hc.opening_slot q + 3) - 1))
    (hcarrierBase : ∀ r : Round,
      S.hc.round_of (S.hc.opening_slot q + 3) = r + 1 →
      ∀ u ∈ rho.honest,
        Block.Preceq (actionSGBlockAt S rho u r) D)
    (hcarrierQ : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u q) D)
    {s : Slot} {F : Slot → Block V} {End : Block V}
    (hfold : MovingSlotFoldAtN S rho
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
      (S.hc.opening_slot q + 3) s F End)
    (hsBase : S.hc.opening_slot q + 3 ≤ s)
    (hbaseEq : F (S.hc.opening_slot q + 3) = D)
    (hcutHor : Protocol.support_cutoff S.E s ≤ rho.horizon) :
    ∃ Next : Block V,
      MovingSlotFrontierAt S rho (s - 1) End Next ∧
      NamedMovingSlotWindowFacts S rho s End Next ∧
      NamedHonestVotesCone S rho s
        (fun X => Block.Preceq Next X) := by
  have hsPos : 0 < s := lt_of_lt_of_le (Nat.zero_lt_succ _) hsBase
  have hcSucc : s - 1 + 1 = s := nat_pred_succ hsPos
  have hcBase : S.hc.opening_slot q + 2 ≤ s - 1 := by
    exact nat_add_two_le_pred_of_add_three_le hsBase
  have hslotHor : Protocol.confirmation_time S.E (s - 1) ≤
      rho.horizon := by
    rw [← support_cutoff_eq_confirmation_time_pred S.E hsPos]
    exact hcutHor
  have hDPrev : Block.Preceq D (F s) := by
    rw [← hbaseEq]
    exact hfold.mono _ _ (Nat.le_refl _) hsBase (Nat.le_refl _)
  have hDPrev' : Block.Preceq D (F (s - 1 + 1)) := by
    rw [hcSucc]
    exact hDPrev
  have hentry : MovingSlotEntryStateN S rho
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
      (s - 1 + 1) (F (s - 1 + 1)) End := by
    simpa only [hcSucc] using hfold.entry
  have hR0q : S.hc.round_of (S.hc.opening_slot q + 3) - 1 ≤ q :=
    nat_pred_le_of_pos_le_succ hR0pos
      (round_of_opening_add_three_le_succ S.hc q)
  have hpostQ : S.E.t_GST ≤ S.a q :=
    hpostBase.trans (action_time_mono' S hR0q)
  have hpostQ1 : S.E.t_GST ≤ S.a (q + 1) :=
    hpostQ.trans (action_time_mono' S (Nat.le_succ q))
  by_cases hceiling : s < S.hc.opening_slot (q + 2)
  · have hdata := ceilingWindowData (M0 := M0) S hR0pos hpostBase
      hcarrierBase hcarrierQ hDPrev' hcBase (by simpa only [hcSucc] using hceiling)
      hslotHor
    have htiming := ceilingActionTiming S hpostQ hcarrierQ hDPrev' hcBase
      (by simpa only [hcSucc] using hceiling) hslotHor
    obtain ⟨Next, hfrontier, hfacts⟩ :=
      hentry.windowFacts_of_ceiling S adm hcom hfb hdata.pos
        hdata.round.choose_spec.1 hdata.round.choose_spec.2.2.2
        hdata.round.choose_spec.2.1 hdata.round.choose_spec.2.2.1
        hdata.postVote hdata.postProp hdata.slotHor htiming
    have hcone := hentry.windowVotesCone_of_ceiling S adm hcom hfb hdata.pos
      hdata.round.choose_spec.1 hdata.round.choose_spec.2.2.2
      hdata.round.choose_spec.2.1 hdata.round.choose_spec.2.2.1
      hdata.postVote hdata.postProp hdata.slotHor hfrontier
    exact ⟨Next, by simpa only [hcSucc] using hfrontier,
      by simpa only [hcSucc] using hfacts,
      by simpa only [hcSucc] using hcone⟩
  · have htake : S.hc.opening_slot (q + 2) ≤ s :=
      Nat.le_of_not_gt hceiling
    have hdata := ordinaryWindowData (M0 := M0) S hR0pos hpostBase
      (by simpa only [hcSucc] using htake) hslotHor
    have htiming := ordinaryActionTiming S hpostQ1
      (by simpa only [hcSucc] using htake) hslotHor
    obtain ⟨r, hround, ht1, hpostAction, hcut⟩ := hdata.round
    obtain ⟨Next, hfrontier, hfacts⟩ := hentry.windowFacts S adm hcom hfb
      hdata.pos hround ht1 hpostAction hcut hdata.postVote hdata.postProp
      hdata.slotHor htiming
    have hcone := hentry.windowVotesCone S adm hcom hfb hdata.pos hround ht1
      hpostAction hcut hdata.postVote hdata.postProp hdata.slotHor hfrontier
    exact ⟨Next, by simpa only [hcSucc] using hfrontier,
      by simpa only [hcSucc] using hfacts,
      by simpa only [hcSucc] using hcone⟩


theorem MovingSlotFoldAtN.complete_through_window
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {t1 : Time} {M0 : Height} {s0 s : Slot}
    {F : Slot → Block V} {End Next : Block V}
    (hfold : MovingSlotFoldAtN S rho t1 M0 s0 s F End)
    (hs : 0 < s)
    (hfrontier : MovingSlotFrontierAt S rho (s - 1) End Next)
    (hfacts : NamedMovingSlotWindowFacts S rho s End Next)
    {v : V} (hv : v ∈ rho.honest)
    (hcutHor : Protocol.support_cutoff S.E s ≤ rho.horizon)
    (hfuture : rho.horizon < Protocol.proposal_time S.E (s + 1)) :
    ∃ End' : Nat → Block V,
      MovingFrontierChainStateN S rho t1 M0
        (strictEventIndex rho t1) rho.events.length End' := by
  obtain ⟨End0, hstate0, _hprev, hEnd0⟩ := hfold.entry.prevEndpoint
  have hrunE : ∃ E : NamedBlock V, E.erase = End ∧ RunBlock S rho E := by
    rw [← hEnd0]
    exact hstate0.endpointRun _ hstate0.start_le (Nat.le_refl _)
  have hrunN : ∃ E : NamedBlock V, E.erase = Next ∧ RunBlock S rho E :=
    hfrontier.runBlock S adm hrunE
  obtain ⟨End1, _hlow1, hval1, hstate1⟩ :=
    through_slotWindowPrefix_named S adm hs hstate0 hEnd0 hrunE hrunN hfacts
      hv hcutHor
  have hcfLen : inclusiveEventIndex rho (Protocol.view_freeze S.E s) ≤
      rho.events.length := by
    dsimp only [inclusiveEventIndex]
    exact List.length_filter_le _ _
  have hlenFuture : rho.events.length ≤
      strictEventIndex rho (Protocol.proposal_time S.E (s + 1)) := by
    rw [events_length_eq_inclusive_horizon S adm]
    exact inclusiveEventIndex_le_strictEventIndex_of_lt rho hfuture
  obtain ⟨End2, _hlow2, _hhigh2, hstate2⟩ :=
    hstate1.through_constantEndpoint_named_public S
      (by rw [hval1]; exact Block.preceq_self Next) hrunN hcfLen (by
        intro j hj hjlen
        refine movingSlotWindowTail_eventFacts_named_public S adm
          (Block.preceq_self Next) ?_ hj ?_
        · intro u _hu hevent _heq
          have hmem := List.mem_of_getElem? hevent
          have hhor := (adm.in_horizon _ hmem).2
          simp only [Event.time] at hhor
          exact absurd hhor (not_le_of_gt hfuture)
        · exact hjlen.trans_le
            (hlenFuture.trans (strictEventIndex_le_inclusiveEventIndex rho _)))
  exact ⟨End2, hstate2⟩

#print axioms MovingSlotFoldAtN.windowFacts_hybrid
#print axioms MovingSlotFoldAtN.complete_through_window

#print axioms inclusiveEventIndex_le_strictEventIndex_of_lt
#print axioms events_length_eq_inclusive_horizon
#print axioms ceilingWindowData
#print axioms ceilingActionTiming
#print axioms ordinaryWindowData
#print axioms ordinaryActionTiming

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
