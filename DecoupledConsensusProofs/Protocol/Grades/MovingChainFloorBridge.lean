module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainRoundRead

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# The fold's slot facts in the floor record's guarded shape

`MovingChainRoundFloorFor` states its three slot-indexed fields under two
schedule guards: the slot is strictly after the healing boundary,
`healingBoundaryTime S q0 < proposal_time d`, and it is inside the horizon,
`confirmation_time d ≤ rho.horizon`. Those guards are what makes the fields
true at all: without a lower one, two consecutive honest-proposer slots before
GST would force the second proposer to build on the first proposal, which the
adversary can prevent by delaying delivery.

The fold proves the same three facts on the range `[s0, s]` it has actually
walked. This module converts the two time guards into that range, and hands
back the fields in the record's shape.

The conversion is exact on the lower side: `healingBoundaryTime S q0` is the
slot-`(opening_slot q0 + 2)` vote instant, so a proposal instant strictly after
it belongs to slot `opening_slot q0 + 3` or later — the fold's own base slot.
On the upper side the caller supplies the range fact `hrange`, which says the
fold walked strictly past every slot inside the horizon; walking one slot past
is what the step already needs, since entering slot `c + 2` consumes the window
data of slots `c` and `c + 1`.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem vote_time_normal''' (E : Env V) (s : Slot) :
    Protocol.vote_time E s = (4 * (s : Time) + 1) * E.Δ := by
  unfold Protocol.vote_time Env.t slotStart
  ring

private theorem confirmation_time_mono_slots''' (E : Env V) {s t : Slot}
    (hst : s ≤ t) :
    Protocol.confirmation_time E s ≤ Protocol.confirmation_time E t := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ,
    Protocol.confirmation_time_eq_support_cutoff_succ]
  exact Proofs.Optimistic.support_cutoff_mono E (Nat.add_le_add_right hst 1)

private theorem proposal_time_normal''' (E : Env V) (s : Slot) :
    Protocol.proposal_time E s = (4 * (s : Time) + 0) * E.Δ := by
  unfold Protocol.proposal_time Env.t slotStart
  ring

/-- **The healing boundary, read as a slot bound.**

The boundary is the slot-`(opening_slot q0 + 2)` vote instant, one quarter of a
slot into that slot's window, so the first proposal instant strictly after it
is the one of slot `opening_slot q0 + 3`. -/
theorem openingSlot_three_le_of_healingBoundary_lt_proposal
    (S : Setup V) {q0 : Round} {d : Slot}
    (hguard : healingBoundaryTime S q0 < Protocol.proposal_time S.E d) :
    S.hc.opening_slot q0 + 3 ≤ d := by
  rw [healingBoundaryTime, vote_time_normal''' S.E _,
    proposal_time_normal''' S.E d] at hguard
  have hnum : 4 * ((S.hc.opening_slot q0 + 2 : Slot) : Int) + 1 <
      4 * ((d : Slot) : Int) + 0 := by
    by_contra hnot
    exact absurd hguard (not_lt_of_ge
      (Int.mul_le_mul_of_nonneg_right (le_of_not_gt hnot)
        (le_of_lt S.E.Δ_pos)))
  have hcast : ((S.hc.opening_slot q0 : Slot) : Int) + 3 ≤ ((d : Slot) : Int) := by
    push_cast at hnum ⊢
    omega
  exact_mod_cast hcast

/-- The fold walked a range that covers every slot the floor record's guards
allow: it starts at or below the boundary slot and it goes strictly past every
slot inside the horizon. -/
structure MovingSlotFoldCovers
    (S : Setup V) (rho : Run V) (q0 : Round) (s0 s : Slot) : Prop where
  /-- The fold starts at or below the first slot after the boundary. -/
  base : s0 ≤ S.hc.opening_slot q0 + 3
  /-- The fold ends strictly past every in-horizon slot. Entering slot
  `c + 2` already consumes the window data of slot `c + 1`, so a fold that
  consumed the last in-horizon slot's data ends one slot beyond it. -/
  reach : ∀ e : Slot, Protocol.confirmation_time S.E e ≤ rho.horizon → e < s
/-- The guarded round's opening lies in the fold's range. Its action is
that opening slot's confirmation, so ordinary slot coverage supplies the
upper bound. A later confirmation need not be in the run. -/
theorem MovingSlotFoldCovers.mem_range_round
    {S : Setup V} {rho : Run V} {q0 : Round} {s0 s : Slot}
    (hcov : MovingSlotFoldCovers S rho q0 s0 s)
    {r : Round} (hround : q0 + 1 < r) (hhor : S.a r ≤ rho.horizon) :
    s0 ≤ S.hc.opening_slot r ∧ S.hc.opening_slot r < s := by
  have hreach := hcov.reach (S.hc.opening_slot r)
    (by simpa only [Setup.a, Protocol.a_eq_confirmation_time] using hhor)
  refine ⟨?_, hreach⟩
  have hR : 2 ≤ S.hc.R := S.hc.R_ge_two
  have hstep : (q0 + 2) * S.hc.R ≤ r * S.hc.R :=
    Nat.mul_le_mul_right _ hround
  have hlow : S.hc.opening_slot q0 + 3 ≤ S.hc.opening_slot r := by
    simp only [Protocol.HealConfig.opening_slot]
    calc
      q0 * S.hc.R + 3 ≤ q0 * S.hc.R + 2 * S.hc.R := by
        have : 3 ≤ 2 * S.hc.R := by omega
        exact Nat.add_le_add_left this _
      _ = (q0 + 2) * S.hc.R := by ring
      _ ≤ r * S.hc.R := hstep
  exact hcov.base.trans hlow

/-- The guarded slot lies in the range the fold walked. -/
theorem MovingSlotFoldCovers.mem_range
    {S : Setup V} {rho : Run V} {q0 : Round} {s0 s : Slot}
    (hcov : MovingSlotFoldCovers S rho q0 s0 s)
    {d : Slot}
    (hboundary : healingBoundaryTime S q0 < Protocol.proposal_time S.E d)
    (hhor : Protocol.confirmation_time S.E d ≤ rho.horizon) :
    s0 ≤ d ∧ d < s :=
  ⟨hcov.base.trans
    (openingSlot_three_le_of_healingBoundary_lt_proposal S hboundary),
    hcov.reach d hhor⟩





-- fold invariant, whose seven shared fields this body reads.
theorem MovingSlotFoldAtN.endpointMonotone_guarded
    (S : Setup V) {rho : Run V}
    {t1 : Time} {M0 : Height} {s0 s : Slot} {F : Slot → Block V}
    {End : Block V} {q0 : Round}
    (hfold : MovingSlotFoldAtN S rho t1 M0 s0 s F End)
    (hcov : MovingSlotFoldCovers S rho q0 s0 s) :
    ∀ d e : Slot,
      healingBoundaryTime S q0 < Protocol.proposal_time S.E d →
      Protocol.confirmation_time S.E e ≤ rho.horizon →
      d ≤ e → Block.Preceq (F d) (F e) := by
  intro d e hboundary hhor hde
  have hboundaryE : healingBoundaryTime S q0 <
      Protocol.proposal_time S.E e :=
    lt_of_lt_of_le hboundary (Protocol.proposal_time_mono S.E hde)
  obtain ⟨hd, -⟩ := hcov.mem_range hboundary
    ((confirmation_time_mono_slots''' S.E hde).trans hhor)
  obtain ⟨-, he⟩ := hcov.mem_range hboundaryE hhor
  exact hfold.mono d e hd hde (le_of_lt he)

/-- **`endpointBelowHonestParent` in the floor record's shape.** -/


-- fold invariant, whose seven shared fields this body reads.
theorem MovingSlotFoldAtN.endpointBelowHonestParent_guarded
    (S : Setup V) {rho : Run V}
    {t1 : Time} {M0 : Height} {s0 s : Slot} {F : Slot → Block V}
    {End : Block V} {q0 : Round}
    (hfold : MovingSlotFoldAtN S rho t1 M0 s0 s F End)
    (hcov : MovingSlotFoldCovers S rho q0 s0 s) :
    ∀ d : Slot,
      healingBoundaryTime S q0 < Protocol.proposal_time S.E d →
      Protocol.confirmation_time S.E d ≤ rho.horizon →
      S.E.proposer d ∈ rho.honest →
      Block.Preceq (F d) (proposedParent S rho d) := by
  intro d hboundary hhor hprop
  obtain ⟨hd, hdlt⟩ := hcov.mem_range hboundary hhor
  exact hfold.parent d hd (le_of_lt hdlt) hprop

/-- **`honestProposalAbsorbed` in the floor record's shape.**

The parent premise of the record's field is not used: the fold proves the
absorption from the entry endpoint being the proposal, and the parent fact is
its own field. -/


-- fold invariant, whose seven shared fields this body reads.
theorem MovingSlotFoldAtN.honestProposalAbsorbed_guarded
    (S : Setup V) {rho : Run V}
    {t1 : Time} {M0 : Height} {s0 s : Slot} {F : Slot → Block V}
    {End : Block V} {q0 : Round}
    (hfold : MovingSlotFoldAtN S rho t1 M0 s0 s F End)
    (hcov : MovingSlotFoldCovers S rho q0 s0 s) :
    ∀ d : Slot,
      healingBoundaryTime S q0 < Protocol.proposal_time S.E d →
      Protocol.confirmation_time S.E d ≤ rho.horizon →
      S.E.proposer d ∈ rho.honest →
      Block.Preceq (F d) (proposedParent S rho d) →
      ∀ P : NamedBlock V, proposedBlockAt S rho d = some P →
        Block.Preceq P.erase (F (d + 1)) := by
  intro d hboundary hhor hprop _hparent P hP
  obtain ⟨hd, hdlt⟩ := hcov.mem_range hboundary hhor
  obtain ⟨P', hP', hpre⟩ := hfold.absorbed d hd hdlt hprop
  rw [hP] at hP'
  cases hP'
  exact hpre

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
