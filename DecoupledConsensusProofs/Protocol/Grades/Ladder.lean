module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.Grades
public import DecoupledConsensusInternal.HealingSurface
public import DecoupledConsensusProofs.Protocol.ValidatorClient.HeightPairCases
public import DecoupledConsensusProofs.Objects.ActionRound
public import Mathlib.Tactic.Linarith

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol (GradeView HealConfig)
open Internal
open Execution
open Internal.HealingSurface (HonestGradeDelivery GradeRoundReady
  gradeViewAt healStoreAt gstLagged readyLag readyLag_pos)
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. The cutoff arithmetic of one Δ hop (PROTOCOL.md#the-complete-protocol)

Four instants around one slot start, so each identity is `Δ` added to or taken
from `slotStart`. Stated as three lemmas rather than inlined, for the same
reason `Γ_neg1_lt_Γ_0` and its siblings are: they would fail loudly if a cutoff
were ever edited. -/

/-- `a − d + d = a` on the nose. The `∀ a d: Int` shape is
`Proofs.HealingLemmas.Grades`'s own idiom for the cutoff arithmetic: `omega` is handed
an explicit `Int` statement rather than a `Time`-typed goal. -/
theorem int_sub_add (a d : Int) : a - d + d = a := by omega

/-- `Γ_r^{−1} + Δ = Γ_r^0`. -/
theorem Γ_neg1_add_Δ (hc : HealConfig) (Δ : Time) (r : Round) :
    hc.Γ_neg1 Δ r + Δ = hc.Γ_0 Δ r :=
  int_sub_add (slotStart Δ (hc.opening_slot r)) Δ

/-- `Γ_r^0 + Δ = Γ_r^1`. -/
theorem Γ_0_add_Δ (hc : HealConfig) (Δ : Time) (r : Round) :
    hc.Γ_0 Δ r + Δ = hc.Γ_1 Δ r := rfl

/-- `Γ_r^1 + Δ = Γ_r^2`. -/
theorem Γ_1_add_Δ (hc : HealConfig) (Δ : Time) (r : Round) :
    hc.Γ_1 Δ r + Δ = hc.Γ_2 Δ r := by
  have key : ∀ a d : Int, a + d + d = a + 2 * d := by intro a d; omega
  exact key (slotStart Δ (hc.opening_slot r)) Δ




/-- `Γ_r^2` precedes the round action at `a_r`. -/
theorem Γ_2_le_a (hc : HealConfig) {Δ : Time} (hΔ : 0 < Δ) (r : Round) :
    hc.Γ_2 Δ r ≤ hc.a Δ r := by
  have key : ∀ a d : Int, 0 < d → a + 2 * d ≤ a + 6 * d := by
    intro a d hd
    omega
  exact key (slotStart Δ (hc.opening_slot r)) Δ hΔ

/-- Advancing by `k` rounds advances `Γ^{−1}` by `4ΔRk`. -/
theorem Γ_neg1_add_rounds (hc : HealConfig) (Δ : Time) (r k : Round) :
    hc.Γ_neg1 Δ (r + k) =
      hc.Γ_neg1 Δ r + 4 * Δ * (hc.R * k : Nat) := by
  unfold HealConfig.Γ_neg1 HealConfig.opening_slot slotStart
  push_cast
  ring

/-- The earliest grade cutoff is monotone in the round. -/
theorem Γ_neg1_mono (hc : HealConfig) {Δ : Time} (hΔ : 0 < Δ)
    {r r' : Round} (h : r ≤ r') : hc.Γ_neg1 Δ r ≤ hc.Γ_neg1 Δ r' := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Γ_neg1_add_rounds]
  have hfour : (0 : Time) ≤ 4 * Δ := by
    have key : ∀ d : Int, 0 < d → (0 : Int) ≤ 4 * d := by
      intro d hd
      omega
    exact key Δ hΔ
  have hrounds : (0 : Time) ≤ (hc.R * k : Nat) := Int.natCast_nonneg _
  exact Int.le_add_of_nonneg_right (Int.mul_nonneg hfour hrounds)

/-- The action of round `r` precedes the earliest grade cutoff of round
`r + 1`. The bound uses the protocol condition `R ≥ 2`. -/
theorem a_le_Γ_neg1_succ (hc : HealConfig) {Δ : Time} (hΔ : 0 < Δ)
    (r : Round) : hc.a Δ r ≤ hc.Γ_neg1 Δ (r + 1) := by
  have hR : (2 : Time) ≤ (hc.R : Nat) := by
    exact_mod_cast hc.R_ge_two
  unfold HealConfig.a HealConfig.Γ_neg1 HealConfig.opening_slot slotStart
  push_cast
  have hfactor : (0 : Time) ≤ 4 * (hc.R : Nat) - 7 := by
    have key : ∀ R : Int, 2 ≤ R → (0 : Int) ≤ 4 * R - 7 := by
      intro R hR'
      omega
    exact key (hc.R : Nat) hR
  have hprod : (0 : Time) ≤ Δ * (4 * (hc.R : Nat) - 7) :=
    Int.mul_nonneg (le_of_lt hΔ) hfactor
  calc
    4 * Δ * (r * hc.R) + 6 * Δ ≤
        4 * Δ * (r * hc.R) + 6 * Δ + Δ * (4 * hc.R - 7) :=
      Int.le_add_of_nonneg_right hprod
    _ = 4 * Δ * ((r + 1) * hc.R) - Δ := by ring

/-- If round `r` acts after GST, round `r + 1` starts its grade delivery window
after GST. This is the schedule bridge used when healing starts at `ref + 1`.
Retained for any consumer still stated on bare `t_GST`; new consumers of the
open producer below should reach for `gstLagged_le_Γ_neg1_succ`. -/
theorem gst_le_Γ_neg1_succ (S : Setup V) (r : Round)
    (hgst : S.E.t_GST ≤ S.a r) :
    S.E.t_GST ≤ S.hc.Γ_neg1 S.E.Δ (r + 1) :=
  le_trans hgst (a_le_Γ_neg1_succ S.hc S.E.Δ_pos r)


/-- `gstLagged` is `t_GST` plus a nonnegative shift, so any fact stated on
`gstLagged` implies the corresponding `t_GST` fact. Ports of a "round `r₀` is
after GST" premise from `t_GST` to `gstLagged` stay usable by
old consumers of the weaker `t_GST`-stated fact through this one lemma. -/
theorem t_GST_le_gstLagged (S : Setup V) : S.E.t_GST ≤ gstLagged S := by
  have h1 : (0 : Time) ≤ S.E.Δ := le_of_lt S.E.Δ_pos
  have h2 : (0 : Time) ≤ (S.hc.R * readyLag : Nat) := Int.natCast_nonneg _
  have h3 : (0 : Time) ≤ 4 * S.E.Δ * (S.hc.R * readyLag : Nat) :=
    mul_nonneg (mul_nonneg (by norm_num) h1) h2
  unfold gstLagged
  linarith


/-- `gstLagged`-flavored twin of `gst_le_Γ_neg1_succ`: if round
`r`'s action is at or after the lagged GST, round `r + 1`'s earliest grade
cutoff is too. -/
theorem gstLagged_le_Γ_neg1_succ (S : Setup V) (r : Round)
    (hgst : gstLagged S ≤ S.a r) :
    gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ (r + 1) :=
  le_trans hgst (a_le_Γ_neg1_succ S.hc S.E.Δ_pos r)


/-- The lagged GST from the **public** GST premise. The public claims
state "round `r₀` acts at or after GST" on bare `t_GST`; every graded transport
wants the `readyLag`-shifted `gstLagged`. Two rounds of schedule close the gap:
the first carries `a_r` past `Γ_{r+1}^{−1}` (`a_le_Γ_neg1_succ`), the second pays
the `4ΔR` lag itself (`Γ_neg1_add_rounds`, `readyLag = 1`). The constant `2` is
the smallest that works: `a_r = Γ_{r+1}^{−1} − (4ΔR − 7Δ)` sits `7Δ` short of
one round's worth of slack, so a single round cannot also pay a full `4ΔR`. -/
theorem gstLagged_le_Γ_neg1_of_gst_le_a (S : Setup V) (r : Round)
    (hgst : S.E.t_GST ≤ S.a r) :
    gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ (r + 2) := by
  have hstep : S.a r ≤ S.hc.Γ_neg1 S.E.Δ (r + 1) :=
    a_le_Γ_neg1_succ S.hc S.E.Δ_pos r
  have hlag : gstLagged S = S.E.t_GST + 4 * S.E.Δ * (S.hc.R : Nat) := by
    simp [gstLagged, readyLag]
  have hcast : ((S.hc.R * 1 : Nat) : Time) = ((S.hc.R : Nat) : Time) := by
    push_cast
    ring
  have hsplit : S.hc.Γ_neg1 S.E.Δ (r + 2)
      = S.hc.Γ_neg1 S.E.Δ (r + 1) + 4 * S.E.Δ * (S.hc.R : Nat) := by
    rw [← hcast]
    exact Γ_neg1_add_rounds S.hc S.E.Δ (r + 1) 1
  rw [hlag, hsplit]
  linarith


/-- `DecoupledConsensusModel.Protocol.early` at `.g2` is `Γ_r^{−1}` pulled back by `4Δ`
: `early(r,.g2) = Γ_0(r) − 5Δ = Γ_neg1(r) − 4Δ`. -/
theorem early_g2_eq_Γ_neg1_sub (S : Setup V) (r : Round) :
    DecoupledConsensusModel.Protocol.early S.E S.hc r .g2 = S.hc.Γ_neg1 S.E.Δ r - 4 * S.E.Δ := by
  have hopen : DecoupledConsensusModel.Protocol.opening S.E S.hc r = S.hc.Γ_0 S.E.Δ r :=
    (Protocol.Γ_0_eq_proposal_time S.hc S.E r).symm
  have hΓ : S.hc.Γ_neg1 S.E.Δ r = S.hc.Γ_0 S.E.Δ r - S.E.Δ :=
    eq_sub_of_add_eq (Γ_neg1_add_Δ S.hc S.E.Δ r)
  unfold DecoupledConsensusModel.Protocol.early DecoupledConsensusModel.Protocol.Phase.earlyOffset
  rw [hopen, hΓ]
  ring

/-- `DecoupledConsensusModel.Protocol.domain` at `.g0` is exactly `Γ_r^1`. -/
theorem domain_g0_eq_Γ_1 (S : Setup V) (r : Round) :
    DecoupledConsensusModel.Protocol.domain S.E S.hc r .g0 = S.hc.Γ_1 S.E.Δ r := by
  have hopen : DecoupledConsensusModel.Protocol.opening S.E S.hc r = S.hc.Γ_0 S.E.Δ r :=
    (Protocol.Γ_0_eq_proposal_time S.hc S.E r).symm
  unfold DecoupledConsensusModel.Protocol.domain DecoupledConsensusModel.Protocol.Phase.domainOffset
  rw [hopen, one_mul]
  exact Γ_0_add_Δ S.hc S.E.Δ r


/-- A `gstLagged`-post start cutoff and an in-horizon action make every later
in-horizon round ready for the three fixed transports. The
`readyLag` rounds of slack absorb the `4Δ` gap between the prior `Γ_r^{−1}`
cutoff and `GradeRoundReady`'s `early(r,.g2)` window. -/
theorem gradeRoundReady_of_action_horizon (S : Setup V) {ρ : Run V}
    {r₀ r : Round}
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r₀)
    (hround : r₀ ≤ r) (ha : S.a r ≤ ρ.horizon) :
    GradeRoundReady S ρ r := by
  constructor
  · have hmono : S.hc.Γ_neg1 S.E.Δ r₀ ≤ S.hc.Γ_neg1 S.E.Δ r :=
      Γ_neg1_mono S.hc S.E.Δ_pos hround
    have hlag : gstLagged S = S.E.t_GST + 4 * S.E.Δ * (S.hc.R : Nat) := by
      simp [gstLagged, readyLag]
    have hR1 : 1 ≤ S.hc.R := le_trans (by norm_num) S.hc.R_ge_two
    have hR : (1 : Time) ≤ (S.hc.R : Nat) := by exact_mod_cast hR1
    have hΔnn : (0 : Time) ≤ 4 * S.E.Δ := by linarith [S.E.Δ_pos]
    have hshift : 4 * S.E.Δ ≤ 4 * S.E.Δ * (S.hc.R : Nat) := by
      calc 4 * S.E.Δ = 4 * S.E.Δ * 1 := by ring
        _ ≤ 4 * S.E.Δ * (S.hc.R : Nat) := mul_le_mul_of_nonneg_left hR hΔnn
    have hchain : S.E.t_GST + 4 * S.E.Δ * (S.hc.R : Nat) ≤ S.hc.Γ_neg1 S.E.Δ r :=
      hlag ▸ le_trans hgst hmono
    rw [early_g2_eq_Γ_neg1_sub]
    linarith
  · rw [domain_g0_eq_Γ_1]
    have hΓ12 : S.hc.Γ_1 S.E.Δ r ≤ S.hc.Γ_2 S.E.Δ r := by
      have := Γ_1_add_Δ S.hc S.E.Δ r
      linarith [S.E.Δ_pos]
    exact le_trans hΓ12 (le_trans (Γ_2_le_a S.hc S.E.Δ_pos r) ha)


/-- The public-premise open producer. A round `r₀` whose action is
at or after GST makes every in-horizon round from `r₀ + 2` on ready for the three
fixed transports. This is the shape the public claims quote: their GST premise
is on bare `t_GST`, and the two rounds of slack pay both the `6Δ` action offset
and the `readyLag` shift of `gstLagged`. -/
theorem gradeRoundReady_of_gst_le_a (S : Setup V) {ρ : Run V} {r₀ r : Round}
    (hgst : S.E.t_GST ≤ S.a r₀) (hround : r₀ + 2 ≤ r)
    (ha : S.a r ≤ ρ.horizon) :
    GradeRoundReady S ρ r :=
  gradeRoundReady_of_action_horizon S
    (gstLagged_le_Γ_neg1_of_gst_le_a S r₀ hgst) hround ha

/-! ## 2. The hop moves support (`the design` §9 L1) -/





/-! ## 3. L3 — never vetoed (`the design` §9 L3)

The grade-2 supporters are delivered to the far store with heads by `Γ_r^0`
and cleanliness through `Γ_r^1`. The latter is stronger than grade 1, whose
equivocation cutoff is `Γ_r^0`, and is exactly L8a's boundary. -/

/-! ## 4. L2's across-store half, for the pairs the ladder reaches
(`the design` §9 L2) -/

/-! ## 5. L5 — abstention exclusivity (`the design` §9 L5)

Two halves, and they meet at the store. The grade half is L1's first step
contraposed and is about the run; the FG half is one unfold of `height_pair` at
`⊥` and is about the model alone. -/

omit [Fintype V] in
/-- "Deepest" over an empty range is `⊥` (PROTOCOL.md#the-complete-protocol). The twin of
`Proofs.HealingLemmas.Grades.find?_empty`, and what turns "no block holds `G2`" into
`grade2_block = ⊥`. -/
theorem deepest?_empty : Block.deepest? (∅ : Finset (Block V)) = none := by
  unfold Block.deepest? pickUnique?
  rw [dif_neg]
  rintro ⟨a, ⟨ha, -⟩, -⟩
  simp at ha





end HealingSurface
end Proofs
end DecoupledConsensusModel

end
