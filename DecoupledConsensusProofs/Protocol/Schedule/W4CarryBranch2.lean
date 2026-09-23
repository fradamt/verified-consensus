module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.MovingChainHandoffBase
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainRoundRead
public import DecoupledConsensusProofs.Objects.MovingChainStep
public import DecoupledConsensusProofs.Protocol.Schedule.GSTZeroActionHead
public import DecoupledConsensusProofs.Protocol.Schedule.W4MovingParent
public import DecoupledConsensusProofs.Protocol.Schedule.W4CarryWindow

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



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

/-! ## Schedule helpers, copied without the dead binders -/

private theorem w4_int_le_add_two_c2 {x d : Int} (hd : 0 < d) :
    x ≤ x + 2 * d := by omega

private theorem w4_proposalSucc_le_confirmation_c2 (E : Env V) (s : Slot) :
    Protocol.proposal_time E (s + 1) ≤ Protocol.confirmation_time E s := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ]
  simp only [Protocol.proposal_time, Protocol.support_cutoff]
  exact w4_int_le_add_two_c2 E.Δ_pos

/-! ## The honest parent at the entered slot, mixed

The N form of the erased `MovingSlotEntryState.honestParent_mixed`
(`MovingChainExecutionRun.lean:624`). Its erased body calls the parked
`MovingFrontierChainState.endpoint_preceq_proposedParent`; this one calls the
available N twin over the supplied carrier bound, and derives that bound from the
entered slot's reach-back. -/
theorem MovingSlotEntryStateN.honestParent_mixed_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End Next : Block V}
    (hentry : MovingSlotEntryStateN S rho t1 M0 (c + 1) Prev End)
    (hdata : MovingSlotWindowDataC S rho M0 c Prev)
    (hdata' : MovingSlotWindowData S rho t1 M0 (c + 1))
    (hfrontier : MovingSlotFrontierAt S rho c End Next)
    (hfacts : NamedMovingSlotWindowFacts S rho (c + 1) End Next)
    (hprop : S.E.proposer (c + 1 + 1) ∈ rho.honest)
    {v : V} (hv : v ∈ rho.honest) :
    Block.Preceq Next (proposedParent S rho (c + 1 + 1)) := by
  obtain ⟨r, hround, hpostAction, hcut, hupper⟩ := hdata.round
  obtain ⟨r', hround', ht1', hpostAction', hcut'⟩ := hdata'.round
  have hhorSC : Protocol.support_cutoff S.E (c + 1) ≤ rho.horizon :=
    (support_cutoff_le_confirmation_time S.E (c + 1)).trans hdata'.slotHor
  have hhorProp : Protocol.proposal_time S.E (c + 1 + 1) ≤ rho.horizon :=
    (w4_proposalSucc_le_confirmation_c2 S.E (c + 1)).trans hdata'.slotHor
  have hcone := hentry.windowVotesCone_of_ceiling S adm hcom hfb hdata.pos
    hround hupper hpostAction hcut hdata.postVote hdata.postProp
    hdata.slotHor hfrontier
  obtain ⟨p, EndAt, _hpevent, hsnp, hEndAtp, hstate⟩ :=
    hentry.historyAtHonestProposalEvent S adm hfrontier hfacts hprop
      hhorProp hhorSC hv
  have hcone' : NamedHonestVotesCone S rho (c + 1)
      (fun X => Block.Preceq (EndAt p) X) := by
    rw [hEndAtp]
    exact hcone
  -- the entered slot's reach-back becomes the ceiling family's carrier bound
  have hactionHor : S.a r' ≤ rho.horizon :=
    (le_of_lt (Int.lt_add_of_pos_right (S.a r') S.E.Δ_pos)).trans
      ((action_add_delta_le_next_Γ_neg1 S r').trans hcut')
  have hroundPos : 0 < S.hc.round_of (c + 1 + 1) := by
    rw [hround']
    exact Nat.succ_pos r'
  have hbefore : S.a r' < Protocol.proposal_time S.E (c + 1 + 1) := by
    have hdelay := Protocol.previous_action_add_delta_le_proposal S hroundPos
    have hdelay' : S.a r' + S.E.Δ ≤ Protocol.proposal_time S.E (c + 1 + 1) := by
      simpa only [hround', Nat.add_sub_cancel] using hdelay
    exact (Int.lt_add_of_pos_right (S.a r') S.E.Δ_pos).trans_le hdelay'
  have hupperK := hstate.previousActionCarriersPreceqAtRead S adm ht1'
    hactionHor hbefore hsnp
  have hparent := hstate.endpoint_preceq_proposedParent_of_ceiling_named
    S adm hcom hfb (Nat.succ_pos c) hround' hupperK hpostAction' hcut'
    hdata'.postVote hhorSC hhorProp hsnp hprop hcone'
    (hentry.startTime.trans
      (Protocol.proposal_time_mono S.E (Nat.le_succ (c + 1))))
  rw [hEndAtp] at hparent
  exact hparent

#print axioms MovingSlotEntryStateN.honestParent_mixed_named

/-! ## The entered slot's ceiling record, from the ordinary one

The mixed family's only structural difference from the ceiling family is the
entered slot's record. In the honest-proposer branch that difference
disappears: the history through the proposer's own tick turns the ordinary
record's reach-back into the ceiling record's carrier bound, at the very
endpoint the entered slot enters with. So every ceiling producer serves the
mixed branch unchanged, and the mixed members are one-line consumers rather
than second copies of the argument. -/
theorem MovingSlotEntryStateN.enteredCeilingData_mixed
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End Next : Block V}
    (hentry : MovingSlotEntryStateN S rho t1 M0 (c + 1) Prev End)
    (hdata' : MovingSlotWindowData S rho t1 M0 (c + 1))
    (hfrontier : MovingSlotFrontierAt S rho c End Next)
    (hfacts : NamedMovingSlotWindowFacts S rho (c + 1) End Next)
    (hprop : S.E.proposer (c + 1 + 1) ∈ rho.honest)
    {v : V} (hv : v ∈ rho.honest) :
    MovingSlotWindowDataC S rho M0 (c + 1) Next := by
  obtain ⟨r', hround', ht1', hpostAction', hcut'⟩ := hdata'.round
  have hhorSC : Protocol.support_cutoff S.E (c + 1) ≤ rho.horizon :=
    (support_cutoff_le_confirmation_time S.E (c + 1)).trans hdata'.slotHor
  have hhorProp : Protocol.proposal_time S.E (c + 1 + 1) ≤ rho.horizon :=
    (w4_proposalSucc_le_confirmation_c2 S.E (c + 1)).trans hdata'.slotHor
  obtain ⟨p, EndAt, _hpevent, hsnp, hEndAtp, hstate⟩ :=
    hentry.historyAtHonestProposalEvent S adm hfrontier hfacts hprop
      hhorProp hhorSC hv
  have hactionHor : S.a r' ≤ rho.horizon :=
    (le_of_lt (Int.lt_add_of_pos_right (S.a r') S.E.Δ_pos)).trans
      ((action_add_delta_le_next_Γ_neg1 S r').trans hcut')
  have hroundPos : 0 < S.hc.round_of (c + 1 + 1) := by
    rw [hround']
    exact Nat.succ_pos r'
  have hbefore : S.a r' < Protocol.proposal_time S.E (c + 1 + 1) := by
    have hdelay := Protocol.previous_action_add_delta_le_proposal S hroundPos
    have hdelay' : S.a r' + S.E.Δ ≤ Protocol.proposal_time S.E (c + 1 + 1) := by
      simpa only [hround', Nat.add_sub_cancel] using hdelay
    exact (Int.lt_add_of_pos_right (S.a r') S.E.Δ_pos).trans_le hdelay'
  have hupperK := hstate.previousActionCarriersPreceqAtRead S adm ht1'
    hactionHor hbefore hsnp
  exact
    { pos := Nat.succ_pos c
      round := ⟨r', hround', hpostAction', hcut', by
        intro u hu
        simpa only [hEndAtp] using hupperK u hu⟩
      postVote := hdata'.postVote
      postProp := hdata'.postProp
      slotHor := hdata'.slotHor }

#print axioms MovingSlotEntryStateN.enteredCeilingData_mixed

/-- The N honest pre-entry of the next slot, mixed. The erased original is
`MovingSlotEntryState.nextPreEntryHonest_mixed`
(`MovingChainExecutionRun.lean:590`). -/
theorem MovingSlotEntryStateN.nextPreEntry_honest_mixed_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End Next : Block V}
    (hentry : MovingSlotEntryStateN S rho t1 M0 (c + 1) Prev End)
    (hdata : MovingSlotWindowDataC S rho M0 c Prev)
    (hdata' : MovingSlotWindowData S rho t1 M0 (c + 1))
    (hfrontier : MovingSlotFrontierAt S rho c End Next)
    (hfacts : NamedMovingSlotWindowFacts S rho (c + 1) End Next)
    (hprop : S.E.proposer (c + 1 + 1) ∈ rho.honest)
    (hparent : Block.Preceq Next (proposedParent S rho (c + 1 + 1)))
    {v : V} (hv : v ∈ rho.honest) :
    ∃ P : NamedBlock V, proposedBlockAt S rho (c + 1 + 1) = some P ∧
      MovingSlotPreEntryN S rho t1 M0 (c + 1 + 1) Next P.erase :=
  hentry.nextPreEntry_honest_of_ceiling S adm hcom hfb hdata
    (hentry.enteredCeilingData_mixed S adm hdata' hfrontier hfacts hprop hv)
    hfrontier hfacts hprop hparent hv

#print axioms MovingSlotEntryStateN.nextPreEntry_honest_mixed_named

/-- The N Byzantine pre-entry of the next slot, mixed. The erased original is
`MovingSlotEntryState.nextPreEntryByzantine_mixed`
(`MovingChainExecutionRun.lean:552`). No bridge is needed on this branch: the
ceiling producer already takes the entered slot's support-cutoff horizon
directly rather than a window record. -/
theorem MovingSlotEntryStateN.nextPreEntry_byzantine_mixed_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End Next : Block V}
    (hentry : MovingSlotEntryStateN S rho t1 M0 (c + 1) Prev End)
    (hdata : MovingSlotWindowDataC S rho M0 c Prev)
    (hdata' : MovingSlotWindowData S rho t1 M0 (c + 1))
    (hfrontier : MovingSlotFrontierAt S rho c End Next)
    (hfacts : NamedMovingSlotWindowFacts S rho (c + 1) End Next)
    (hbyz : S.E.proposer (c + 2) ∉ rho.honest)
    {v : V} (hv : v ∈ rho.honest) :
    MovingSlotPreEntryN S rho t1 M0 (c + 2) Next Next := by
  obtain ⟨r, hround, hpostAction, hcut, hupper⟩ := hdata.round
  exact hentry.nextPreEntry_byzantine_of_ceiling S adm hcom hfb hdata.pos
    hround hupper hpostAction hcut hdata.postVote hdata.postProp
    hdata.slotHor hfrontier hfacts hbyz hv
    ((support_cutoff_le_confirmation_time S.E (c + 1)).trans hdata'.slotHor)

#print axioms MovingSlotEntryStateN.nextPreEntry_byzantine_mixed_named

/-- **The N Byzantine entry step, mixed.** The erased original is
`MovingSlotEntryState.stepByzantine_mixed` (`MovingChainExecutionRun.lean:756`).

The entered slot's ordinary record is what the two pre-entry producers want
here, so this branch needs no bridge at all: `MovingSlotPreEntryN.votesCone_prev`
and `MovingSlotPreEntryN.confCompatible_byzantine` both take the reach-back
`t1 ≤ S.a r` directly. -/
theorem MovingSlotEntryStateN.stepByzantine_mixed_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End Next : Block V}
    (hentry : MovingSlotEntryStateN S rho t1 M0 (c + 1) Prev End)
    (hdata : MovingSlotWindowDataC S rho M0 c Prev)
    (hdata' : MovingSlotWindowData S rho t1 M0 (c + 1))
    (hfrontier : MovingSlotFrontierAt S rho c End Next)
    (hfacts : NamedMovingSlotWindowFacts S rho (c + 1) End Next)
    (hbyz : S.E.proposer (c + 2) ∉ rho.honest)
    {v : V} (hv : v ∈ rho.honest) :
    MovingSlotEntryStateN S rho t1 M0 (c + 2) Next Next := by
  obtain ⟨r, hround, hpostAction, hcut, hupper⟩ := hdata.round
  obtain ⟨r', hround', ht1', hpostAction', hcut'⟩ := hdata'.round
  have hhorSC : Protocol.support_cutoff S.E (c + 1) ≤ rho.horizon :=
    (support_cutoff_le_confirmation_time S.E (c + 1)).trans hdata'.slotHor
  obtain ⟨EndAt, hhistory, _hprev, hEndAt⟩ := hentry.prevEndpoint
  have hrunE : ∃ E : NamedBlock V, E.erase = End ∧ RunBlock S rho E := by
    rw [← hEndAt]
    exact hhistory.endpointRun _ hhistory.start_le (Nat.le_refl _)
  have hrunN : ∃ N : NamedBlock V, N.erase = Next ∧ RunBlock S rho N :=
    hfrontier.runBlock S adm hrunE
  have hcone := hentry.windowVotesCone_of_ceiling S adm hcom hfb hdata.pos
    hround hupper hpostAction hcut hdata.postVote hdata.postProp
    hdata.slotHor hfrontier
  have hnext := hentry.nextPreEntry_byzantine_mixed_named S adm hcom hfb hdata
    hdata' hfrontier hfacts hbyz hv
  exact hentry.step_byzantineProposer_named S adm (Nat.succ_pos c) hrunN
    hfacts hbyz hv hhorSC hcone
    (hnext.votesCone_prev S adm hcom hfb hdata'.pos hround' ht1'
      hpostAction' hcut' hdata'.postVote hdata'.slotHor)
    (hnext.confCompatible_byzantine S adm hcom hfb hdata'.pos hround' ht1'
      hpostAction' hcut' hdata'.postVote hdata'.slotHor)

#print axioms MovingSlotEntryStateN.stepByzantine_mixed_named



private theorem w4c2_nat_pred_add_one {n : Nat} (hn : 0 < n) : n - 1 + 1 = n :=
  Nat.sub_add_cancel hn

private theorem w4c2_nat_pred_eq_of_pos_eq_succ {a b : Nat}
    (ha : 0 < a) (h : a = b + 1) : a - 1 = b := by
  omega

private theorem w4c2_int_add_le_add_right {a b d : Int}
    (hab : a ≤ b) : a + d ≤ b + d :=
  by simpa only [Int.add_comm] using add_le_add_left hab d


private theorem w4c2_int_mul_le_mul_pos {a b d : Int}
    (hab : a ≤ b) (hd : 0 < d) : a * d ≤ b * d :=
  Int.mul_le_mul_of_nonneg_right hab (le_of_lt hd)

private theorem w4c2_int_mul_lt_mul_pos {a b d : Int}
    (hab : a < b) (hd : 0 < d) : a * d < b * d :=
  Int.mul_lt_mul_of_pos_right hab hd

private theorem w4c2_proposal_time_normal (E : Env V) (s : Slot) :
    Protocol.proposal_time E s = (4 * (s : Time)) * E.Δ := by
  unfold Protocol.proposal_time Env.t slotStart
  ring

private theorem w4c2_vote_time_normal (E : Env V) (s : Slot) :
    Protocol.vote_time E s = (4 * (s : Time) + 1) * E.Δ := by
  unfold Protocol.vote_time Env.t slotStart
  ring

private theorem w4c2_support_cutoff_normal (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s = (4 * (s : Time) + 2) * E.Δ := by
  unfold Protocol.support_cutoff Env.t slotStart
  ring

private theorem w4c2_confirmation_time_normal (E : Env V) (s : Slot) :
    Protocol.confirmation_time E s = (4 * (s : Time) + 6) * E.Δ := by
  unfold Protocol.confirmation_time Env.t slotStart
  ring

private theorem w4c2_action_time_normal (S : Setup V) (r : Round) :
    S.a r = (4 * ((S.hc.opening_slot r : Slot) : Time) + 6) * S.E.Δ := by
  unfold Setup.a Protocol.HealConfig.a slotStart
  ring

private theorem w4c2_gammaNegOne_normal (S : Setup V) (r : Round) :
    S.hc.Γ_neg1 S.E.Δ r =
      (4 * ((S.hc.opening_slot r : Slot) : Time) - 1) * S.E.Δ := by
  unfold Protocol.HealConfig.Γ_neg1 slotStart
  ring

private theorem w4c2_proposal_time_mono' (E : Env V) {a b : Slot} (hab : a ≤ b) :
    Protocol.proposal_time E a ≤ Protocol.proposal_time E b := by
  rw [w4c2_proposal_time_normal, w4c2_proposal_time_normal]
  apply w4c2_int_mul_le_mul_pos _ E.Δ_pos
  exact_mod_cast Nat.mul_le_mul_left 4 hab

private theorem w4c2_action_time_mono' (S : Setup V) {a b : Round} (hab : a ≤ b) :
    S.a a ≤ S.a b := by
  rw [w4c2_action_time_normal, w4c2_action_time_normal]
  apply w4c2_int_mul_le_mul_pos _ S.E.Δ_pos
  have hopen : S.hc.opening_slot a ≤ S.hc.opening_slot b := by
    exact Nat.mul_le_mul_right S.hc.R hab
  exact w4c2_int_add_le_add_right (by exact_mod_cast Nat.mul_le_mul_left 4 hopen)

private theorem w4c2_round_of_opening_add_three_le_succ
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

private theorem w4c2_opening_slot_round_of_le
    (hc : Protocol.HealConfig) (s : Slot) :
    hc.opening_slot (hc.round_of s) ≤ s := by
  have hRpos : 0 < hc.R := lt_of_lt_of_le Nat.zero_lt_two hc.R_ge_two
  simp only [Protocol.HealConfig.round_of, Protocol.HealConfig.opening_slot]
  simpa only [Nat.mul_comm] using Nat.div_mul_le_self s hc.R

private theorem w4c2_round_of_mono'
    (hc : Protocol.HealConfig) {a b : Slot} (hab : a ≤ b) :
    hc.round_of a ≤ hc.round_of b :=
  Nat.div_le_div_right hab



private theorem w4c2_action_le_proposal_plus_two
    (S : Setup V) (q : Round) :
    S.a q ≤ Protocol.proposal_time S.E (S.hc.opening_slot q + 2) := by
  rw [w4c2_action_time_normal, w4c2_proposal_time_normal]
  apply w4c2_int_mul_le_mul_pos _ S.E.Δ_pos
  push_cast
  omega

private theorem w4c2_boundary_cutoff_le_next_action
    (S : Setup V) (q : Round) :
    Protocol.support_cutoff S.E (S.hc.opening_slot q + 2) ≤ S.a (q + 1) := by
  rw [w4c2_support_cutoff_normal, w4c2_action_time_normal]
  apply w4c2_int_mul_le_mul_pos _ S.E.Δ_pos
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
      w4c2_int_add_le_add_right hmul
    _ ≤ 4 * ((S.hc.opening_slot (q + 1) : Slot) : Time) + 6 :=
      by simpa only [Int.add_comm] using
        (w4c2_int_add_le_add_right (d :=
          4 * ((S.hc.opening_slot (q + 1) : Slot) : Time))
          (by decide : (2 : Int) ≤ 6))



private theorem w4c2_proposal_le_vote (E : Env V) (s : Slot) :
    Protocol.proposal_time E s ≤ Protocol.vote_time E s := by
  rw [w4c2_proposal_time_normal, w4c2_vote_time_normal]
  apply w4c2_int_mul_le_mul_pos _ E.Δ_pos
  omega



private theorem w4c2_round_of_lt_of_lt_opening
    (hc : Protocol.HealConfig) {s : Slot} {r : Round}
    (h : s < hc.opening_slot r) : hc.round_of s < r := by
  have hRpos : 0 < hc.R := lt_of_lt_of_le Nat.zero_lt_two hc.R_ge_two
  simp only [Protocol.HealConfig.round_of]
  rw [Nat.div_lt_iff_lt_mul hRpos]
  simpa only [Nat.mul_comm] using h

private theorem w4c2_nat_pred_le_pred {a b : Nat} (h : a ≤ b) : a - 1 ≤ b - 1 :=
  Nat.sub_le_sub_right h 1

private theorem w4c2_nat_pred_le_of_pos_le_succ {a b : Nat}
    (ha : 0 < a) (h : a ≤ b + 1) : a - 1 ≤ b := by
  exact Nat.lt_succ_iff.mp ((Nat.sub_lt ha (by decide : 0 < 1)).trans_le h)


private theorem w4c2_nat_eq_succ_of_nested_bounds_ne {q a b : Nat}
    (hqa : q ≤ a) (hab : a ≤ b) (hb : b ≤ q + 1) (hne : b ≠ a) :
    b = q + 1 := by omega


private theorem w4c2_nat_pred_ge_of_succ_le {q r : Nat}
    (h : q + 2 ≤ r) : q + 1 ≤ r - 1 := by omega




private theorem w4c2_gammaNegOne_round_of_le_proposal
    (S : Setup V) (s : Slot) :
    S.hc.Γ_neg1 S.E.Δ (S.hc.round_of s) ≤
      Protocol.proposal_time S.E s := by
  rw [w4c2_gammaNegOne_normal, w4c2_proposal_time_normal]
  apply w4c2_int_mul_le_mul_pos _ S.E.Δ_pos
  have hopen := w4c2_opening_slot_round_of_le S.hc s
  have hcast : ((S.hc.opening_slot (S.hc.round_of s) : Slot) : Time) ≤
      (s : Time) := by
    exact_mod_cast hopen
  have hmul : 4 * ((S.hc.opening_slot (S.hc.round_of s) : Slot) : Time) ≤
      4 * (s : Time) := Int.mul_le_mul_of_nonneg_left hcast (by norm_num)
  exact (sub_le_self _ (by norm_num)).trans hmul

/-- **Schedule of the carry's second branch.** Pure schedule; the erased
original is `proposalSchedule_hybrid` (`MovingChainExecutionRun.lean:2105`) and
nothing in it touches the N structures, so the argument is unchanged. -/
theorem w4_proposalSchedule_hybrid
    (S : Setup V) {rho : Run V}
    {q : Round} {D Next : Block V} {s : Slot}
    (hR0pos : 0 < S.hc.round_of (S.hc.opening_slot q + 3))
    (hpostBase : S.E.t_GST ≤
      S.a (S.hc.round_of (S.hc.opening_slot q + 3) - 1))
    (hcarrierBase : ∀ r : Round,
      S.hc.round_of (S.hc.opening_slot q + 3) = r + 1 →
      ∀ u ∈ rho.honest,
        Block.Preceq (actionSGBlockAt S rho u r) D)
    (hcarrierQ : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u q) D)
    (hDNext : Block.Preceq D Next)
    (hsBase : S.hc.opening_slot q + 3 ≤ s)
    (hproposalHor : Protocol.proposal_time S.E s ≤ rho.horizon) :
    ∃ r : Round,
      S.hc.round_of s = r + 1 ∧
      S.E.t_GST ≤ S.a r ∧
      S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon ∧
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2) ≤ S.a r ∨
        ∀ u ∈ rho.honest,
          Block.Preceq (actionSGBlockAt S rho u r) Next) := by
  let R0 := S.hc.round_of (S.hc.opening_slot q + 3)
  let Rs := S.hc.round_of s
  let r := Rs - 1
  have hR0Rs : R0 ≤ Rs := w4c2_round_of_mono' S.hc hsBase
  have hRsPos : 0 < Rs := hR0pos.trans_le hR0Rs
  have hround : S.hc.round_of s = r + 1 := by
    simpa only [Rs, r] using (w4c2_nat_pred_add_one hRsPos).symm
  have hr0r : R0 - 1 ≤ r := by
    simpa only [r] using w4c2_nat_pred_le_pred hR0Rs
  have hpost : S.E.t_GST ≤ S.a r :=
    hpostBase.trans (w4c2_action_time_mono' S hr0r)
  have hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon := by
    rw [← hround]
    exact (w4c2_gammaNegOne_round_of_le_proposal S s).trans hproposalHor
  refine ⟨r, hround, hpost, hcut, ?_⟩
  by_cases hordinary : S.hc.opening_slot (q + 2) ≤ s
  · left
    have hq2Rs : q + 2 ≤ Rs := by
      rw [← round_of_opening_slot_eq_schedule S.hc (q + 2)]
      exact w4c2_round_of_mono' S.hc hordinary
    have hq1r : q + 1 ≤ r := by
      dsimp only [r]
      exact w4c2_nat_pred_ge_of_succ_le hq2Rs
    exact (w4c2_boundary_cutoff_le_next_action S q).trans
      (w4c2_action_time_mono' S hq1r)
  · right
    have hqR0 : q ≤ R0 := by
      rw [← round_of_opening_slot_eq_schedule S.hc q]
      exact w4c2_round_of_mono' S.hc (Nat.le_add_right _ _)
    have hRsUpper : Rs ≤ q + 1 := by
      exact Nat.le_of_lt_succ (w4c2_round_of_lt_of_lt_opening S.hc
        (lt_of_not_ge hordinary))
    have hcarrier : ∀ u ∈ rho.honest,
        Block.Preceq (actionSGBlockAt S rho u r) D := by
      by_cases heq : Rs = R0
      · apply hcarrierBase r
        rw [← hround]
        exact heq.symm
      · have hRs : Rs = q + 1 :=
          w4c2_nat_eq_succ_of_nested_bounds_ne hqR0 hR0Rs hRsUpper heq
        have hr : r = q := w4c2_nat_pred_eq_of_pos_eq_succ hRsPos hRs
        simpa only [hr] using hcarrierQ
    intro u hu
    exact Block.preceq_trans (hcarrier u hu) hDNext

#print axioms w4_proposalSchedule_hybrid

private theorem w4c2_nat_pred_add_two_eq_succ {n : Nat} (hn : 0 < n) :
    n - 1 + 1 + 1 = n + 1 := by omega

/-- **The next slot's honest parent on the carry's second branch.**

The erased original is `MovingSlotFoldAt.nextParent_hybrid`
(`MovingChainExecutionRun.lean:2300`). Its proof splits on the schedule
disjunction and calls a different parent read in each arm: the reach-back arm
uses `MovingFrontierChainState.endpoint_preceq_proposedParent`, the ceiling arm
uses `…_of_ceiling`. Over the N structures the two arms merge, because
`MovingFrontierChainStateN.previousActionCarriersPreceqAtRead` turns the
reach-back into the ceiling arm's carrier bound at the same cursor, so a single
named parent read serves both. -/
theorem MovingSlotFoldAtN.nextParent_hybrid
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
    {s : Slot} {F : Slot → Block V} {End Next : Block V}
    (hfold : MovingSlotFoldAtN S rho
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
      (S.hc.opening_slot q + 3) s F End)
    (hsBase : S.hc.opening_slot q + 3 ≤ s)
    (hbaseEq : F (S.hc.opening_slot q + 3) = D)
    (hfrontier : MovingSlotFrontierAt S rho (s - 1) End Next)
    (hfacts : NamedMovingSlotWindowFacts S rho s End Next)
    (hcone : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq Next X))
    (hcutHor : Protocol.support_cutoff S.E s ≤ rho.horizon)
    (hproposalHor : Protocol.proposal_time S.E (s + 1) ≤ rho.horizon)
    (hprop : S.E.proposer (s + 1) ∈ rho.honest)
    {v : V} (hv : v ∈ rho.honest) :
    Block.Preceq Next (proposedParent S rho (s + 1)) := by
  have hsPos : 0 < s := lt_of_lt_of_le (Nat.zero_lt_succ _) hsBase
  have hcSucc : s - 1 + 1 = s := w4c2_nat_pred_add_one hsPos
  have hcTwo : s - 1 + 1 + 1 = s + 1 := w4c2_nat_pred_add_two_eq_succ hsPos
  have hDNext : Block.Preceq D Next := by
    have hDPrev : Block.Preceq D (F s) := by
      rw [← hbaseEq]
      exact hfold.mono _ _ (Nat.le_refl _) hsBase (Nat.le_refl _)
    exact Block.preceq_trans hDPrev
      (Block.preceq_trans hfold.entry.prevLe hfrontier.oldPreceq)
  have hsBaseNext : S.hc.opening_slot q + 3 ≤ s + 1 :=
    hsBase.trans (Nat.le_succ s)
  obtain ⟨r, hround, hpostAction, hcut, hmode⟩ :=
    w4_proposalSchedule_hybrid S hR0pos hpostBase hcarrierBase hcarrierQ
      hDNext hsBaseNext hproposalHor
  have hR0q : S.hc.round_of (S.hc.opening_slot q + 3) - 1 ≤ q :=
    w4c2_nat_pred_le_of_pos_le_succ hR0pos
      (w4c2_round_of_opening_add_three_le_succ S.hc q)
  have hpostAtBase : S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q + 2) :=
    hpostBase.trans
      ((w4c2_action_time_mono' S hR0q).trans
        (w4c2_action_le_proposal_plus_two S q))
  have hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E s :=
    hpostAtBase.trans
      ((w4c2_proposal_time_mono' S.E
        ((Nat.le_succ (S.hc.opening_slot q + 2)).trans hsBase)).trans
          (w4c2_proposal_le_vote S.E s))
  have hstart : Protocol.support_cutoff S.E
      (S.hc.opening_slot q + 2) ≤
      Protocol.proposal_time S.E (s + 1) :=
    (le_of_lt (Protocol.support_cutoff_lt_proposal_time_succ S.E
      (S.hc.opening_slot q + 2))).trans
      (w4c2_proposal_time_mono' S.E (hsBase.trans (Nat.le_succ s)))
  have hentry : MovingSlotEntryStateN S rho
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
      (s - 1 + 1) (F (s - 1 + 1)) End := by
    simpa only [hcSucc] using hfold.entry
  have hfacts' : NamedMovingSlotWindowFacts S rho (s - 1 + 1) End Next := by
    simpa only [hcSucc] using hfacts
  obtain ⟨p, EndAt, _hpevent, hcursor, hEndAt, hstate⟩ :=
    hentry.historyAtHonestProposalEvent S adm hfrontier hfacts'
      (by simpa only [hcTwo] using hprop)
      (by simpa only [hcTwo] using hproposalHor)
      (by simpa only [hcSucc] using hcutHor) hv
  have hcursor' : strictEventIndex rho
      (Protocol.proposal_time S.E (s + 1)) ≤ p := by
    simpa only [hcTwo] using hcursor
  have hcone' : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq (EndAt p) X) := by
    rw [hEndAt]
    exact hcone
  -- both schedule arms give the same carrier bound at the cursor
  have hupper' : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) (EndAt p) := by
    rcases hmode with ht1 | hupper
    · have hactionHor : S.a r ≤ rho.horizon :=
        (le_of_lt (Int.lt_add_of_pos_right (S.a r) S.E.Δ_pos)).trans
          ((action_add_delta_le_next_Γ_neg1 S r).trans hcut)
      have hroundPos : 0 < S.hc.round_of (s + 1) := by
        rw [hround]
        exact Nat.succ_pos r
      have hbefore : S.a r < Protocol.proposal_time S.E (s + 1) := by
        have hdelay :=
          Protocol.previous_action_add_delta_le_proposal S hroundPos
        have hdelay' : S.a r + S.E.Δ ≤ Protocol.proposal_time S.E (s + 1) := by
          simpa only [hround, Nat.add_sub_cancel] using hdelay
        exact (Int.lt_add_of_pos_right (S.a r) S.E.Δ_pos).trans_le hdelay'
      exact hstate.previousActionCarriersPreceqAtRead S adm ht1 hactionHor
        hbefore hcursor'
    · rw [hEndAt]
      exact hupper
  have hparent := hstate.endpoint_preceq_proposedParent_of_ceiling_named
    S adm hcom hfb hsPos hround hupper' hpostAction hcut hpostVote hcutHor
    hproposalHor hcursor' hprop hcone' hstart
  rwa [hEndAt] at hparent

#print axioms MovingSlotFoldAtN.nextParent_hybrid

/-! ### Further private helpers for the completion statements

`view_freeze` arithmetic, the event-time bound, and the named no-tick event
facts, all verbatim from `MovingChainExecutionRun` and `MovingChainFoldRun`
where they are `private`, under the same `w4c2_` prefix. -/

private theorem w4c2_view_freeze_normal (E : Env V) (s : Slot) :
    Protocol.view_freeze E s = (4 * (s : Time) + 3) * E.Δ := by
  unfold Protocol.view_freeze Env.t slotStart
  ring

private theorem w4c2_vote_time_lt_support_cutoff_local (E : Env V) (s : Slot) :
    Protocol.vote_time E s < Protocol.support_cutoff E s := by
  rw [w4c2_vote_time_normal, w4c2_support_cutoff_normal]
  apply w4c2_int_mul_lt_mul_pos _ E.Δ_pos
  omega

private theorem w4c2_support_cutoff_le_view_freeze_local (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s ≤ Protocol.view_freeze E s := by
  rw [w4c2_support_cutoff_normal, w4c2_view_freeze_normal]
  apply w4c2_int_mul_le_mul_pos _ E.Δ_pos
  omega

private theorem w4c2_view_freeze_lt_proposal_succ (E : Env V) (s : Slot) :
    Protocol.view_freeze E s < Protocol.proposal_time E (s + 1) := by
  rw [w4c2_view_freeze_normal, w4c2_proposal_time_normal]
  apply w4c2_int_mul_lt_mul_pos _ E.Δ_pos
  have hcast : (((s + 1 : Nat) : Int)) = (s : Int) + 1 := by
    push_cast
    rfl
  rw [hcast]
  omega

private theorem w4c2_eventTime_gt_of_inclusive_le
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {t0 : Time} {j : Nat} {e : Event V}
    (hj : inclusiveEventIndex rho t0 ≤ j)
    (hget : rho.events[j]? = some e) :
    t0 < e.time := by
  have hfalse := Proofs.Optimistic.filter_false_of_index_ge S sch _
    (Proofs.Optimistic.downward_le t0)
    (by simpa only [inclusiveEventIndex] using hj) hget
  simpa only [decide_eq_false_iff_not, not_le] using hfalse

private theorem w4c2_movingEventFacts_of_no_tick_named
    (S : Setup V) (rho : Run V) {i : Nat} (Next : Block V)
    (hno : ∀ (w : V) (t : Time),
      rho.events[i]? ≠ some (Event.tick w t)) :
    ProposalChainObservationsSandwichedAtIndex S rho i Next Next ∧
      NamedGenuineConfirmationsPreceqAtIndex S rho i Next ∧
      HonestActionSGCarriersPreceqAtIndex S rho i Next ∧
      HonestAttestationOutputPreceqAtIndex S rho i Next ∧
      NamedReadAnchorsAtIndex S rho i Next := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro stage B hstage hobs
    cases hobs with
    | proposalParent _ hevent _ => exact absurd hevent (hno _ _)
    | proposedBlock _ hevent _ => exact absurd hevent (hno _ _)
    | voteHead _ hevent _ _ _ => exact absurd hevent (hno _ _)
    | confirmationOutput _ hevent _ => exact absurd hevent (hno _ _)
    | actionHead _ hevent _ => exact absurd hevent (hno _ _)
  · intro v _hv C hC
    obtain ⟨s, hevent, _⟩ := hC
    exact absurd hevent (hno _ _)
  · intro v q a _hv hevent _ha
    exact absurd hevent (hno _ _)
  · refine Protocol.honestAttestationOutputPreceqAtIndex_of_no_emission
      S rho ?_
    rintro ⟨v, time, a, _hv, hevent, _ha⟩
    exact absurd hevent (hno _ _)
  · refine { voteCompatible := ?_, confirmationCompatible := ?_ }
    · intro v s _hv hevent
      exact absurd hevent (hno _ _)
    · intro v s _hv hevent
      exact absurd hevent (hno _ _)


/-- **The N moving history runs to the end of the run, before the vote.**

The erased original is `MovingFrontierChainState.complete_before_vote`
(`MovingChainExecutionRun.lean:3293`). The run block becomes a named witness
 and the constant-endpoint extension is the N one. -/
theorem MovingFrontierChainStateN.complete_before_vote
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {t1 : Time} {M0 : Height} {n0 : Nat} {s : Slot}
    {EndAt : Nat → Block V} {End : Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0
      (inclusiveEventIndex rho (Protocol.proposal_time S.E s)) EndAt)
    (hEnd : EndAt (inclusiveEventIndex rho
      (Protocol.proposal_time S.E s)) = End)
    (hrun : ∃ E : NamedBlock V, E.erase = End ∧ RunBlock S rho E)
    (hproposalHor : Protocol.proposal_time S.E s ≤ rho.horizon)
    (hvoteFuture : rho.horizon < Protocol.vote_time S.E s)
    (hcutFuture : rho.horizon < Protocol.support_cutoff S.E s)
    (hnextFuture : rho.horizon < Protocol.proposal_time S.E (s + 1)) :
    ∃ End' : Nat → Block V,
      MovingFrontierChainStateN S rho t1 M0 n0 rho.events.length End' := by
  have hstartLen : inclusiveEventIndex rho
      (Protocol.proposal_time S.E s) ≤ rho.events.length := by
    rw [events_length_eq_inclusive_horizon S adm]
    exact inclusiveEventIndex_mono rho hproposalHor
  obtain ⟨End', _hlow, _hhigh, hstate⟩ :=
    h.through_constantEndpoint_named_public S
      (by rw [hEnd]; exact Block.preceq_self End) hrun hstartLen (by
      intro j hj hjlen
      refine w4c2_movingEventFacts_of_no_tick_named S rho End ?_
      intro u t htick
      have hmem : Event.tick u t ∈ rho.events := List.mem_of_getElem? htick
      have hpub : PublicTime S t := adm.tick_public u t hmem
      have hgt : Protocol.proposal_time S.E s < t :=
        w4c2_eventTime_gt_of_inclusive_le S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hj htick
      have htHor : t ≤ rho.horizon := (adm.in_horizon _ hmem).2
      have hltVote : t < Protocol.vote_time S.E s := htHor.trans_lt hvoteFuture
      have hleNext : t ≤ Protocol.proposal_time S.E (s + 1) :=
        htHor.trans (le_of_lt hnextFuture)
      rcases publicTime_slotWindow_cases S hpub hgt hleNext
        with ht | ht | ht | ht
      · exact absurd (ht ▸ hltVote) (lt_irrefl _)
      · exact absurd hltVote (not_lt_of_ge (by
          rw [ht]
          exact le_of_lt (w4c2_vote_time_lt_support_cutoff_local S.E s)))
      · exact absurd hltVote (not_lt_of_ge (by
          rw [ht]
          exact (le_of_lt (w4c2_vote_time_lt_support_cutoff_local S.E s)).trans
            (w4c2_support_cutoff_le_view_freeze_local S.E s)))
      · exact absurd hltVote (not_lt_of_ge (by
          rw [ht]
          exact (le_of_lt (w4c2_vote_time_lt_support_cutoff_local S.E s)).trans
            ((w4c2_support_cutoff_le_view_freeze_local S.E s).trans
              (le_of_lt (w4c2_view_freeze_lt_proposal_succ S.E s))))))
  exact ⟨End', hstate⟩

#print axioms MovingFrontierChainStateN.complete_before_vote

private theorem w4c2_slotInstant_ne (E : Env V) (a b : Slot) (m n : Int)
    (hmod : ∀ x y : Int, 4 * x + m ≠ 4 * y + n) :
    (4 * (a : Time) + m) * E.Δ ≠ (4 * (b : Time) + n) * E.Δ := by
  intro heq
  exact hmod (a : Time) (b : Time)
    (mul_right_cancel₀ (ne_of_gt E.Δ_pos) heq)

private theorem w4c2_tick_node_time_eq_of_same_index
    {rho : Run V} {i : Nat} {v w : V} {t u : Time}
    (h₁ : rho.events[i]? = some (Event.tick v t))
    (h₂ : rho.events[i]? = some (Event.tick w u)) : v = w ∧ t = u := by
  simpa using Option.some.inj (h₁.symm.trans h₂)


private theorem w4c2_movingEventFacts_vote_at_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {i : Nat} {w : V} {s : Slot}
    (hevent : rho.events[i]? = some
      (Event.tick w (Protocol.vote_time S.E s)))
    {Next : Block V}
    (hhead : S.E.proposer s ∈ rho.honest →
      Block.Preceq Next (voteDutyHead S rho w s) ∧
        Block.Preceq (voteDutyHead S rho w s) Next)
    (hanchor : Block.compatible (voterAnchorAt S rho w s) Next = true) :
    ProposalChainObservationsSandwichedAtIndex S rho i Next Next ∧
      NamedGenuineConfirmationsPreceqAtIndex S rho i Next ∧
      HonestActionSGCarriersPreceqAtIndex S rho i Next ∧
      HonestAttestationOutputPreceqAtIndex S rho i Next ∧
      NamedReadAnchorsAtIndex S rho i Next := by
  have hslotEq : S.E.slotOf (Protocol.vote_time S.E s) = s :=
    Proofs.Optimistic.slotOf_vote_time S.E s
  have htickPair : ∀ {u : V} {t : Time},
      rho.events[i]? = some (Event.tick u t) →
        u = w ∧ t = Protocol.vote_time S.E s := by
    intro u t hu
    exact w4c2_tick_node_time_eq_of_same_index hu hevent
  have hproposalNe : ∀ s' : Slot,
      Protocol.vote_time S.E s ≠ Protocol.proposal_time S.E s' := by
    intro s'
    rw [w4c2_vote_time_normal, w4c2_proposal_time_normal]
    exact w4c2_slotInstant_ne S.E s s' 1 0 (by intro x y; omega)
  have hconfNe : ∀ s' : Slot,
      Protocol.confirmation_time S.E s' ≠ Protocol.vote_time S.E s := by
    intro s'
    rw [w4c2_vote_time_normal, w4c2_confirmation_time_normal]
    exact w4c2_slotInstant_ne S.E s' s 6 1 (by intro x y; omega)
  have hactionNe : ∀ q : Round,
      S.a q ≠ Protocol.vote_time S.E s := by
    intro q
    rw [w4c2_vote_time_normal, w4c2_action_time_normal]
    exact w4c2_slotInstant_ne S.E (S.hc.opening_slot q) s 6 1 (by intro x y; omega)
  have hproposal : ProposalChainObservationsSandwichedAtIndex
      S rho i Next Next := by
    intro stage B hstage hobs
    cases hobs with
    | proposalParent _ hevt hactive =>
        obtain ⟨rfl, rfl⟩ := htickPair hevt
        exact absurd hactive.2.1 (hproposalNe _)
    | proposedBlock _ hevt hactive =>
        obtain ⟨rfl, rfl⟩ := htickPair hevt
        exact absurd hactive.2.1 (hproposalNe _)
    | voteHead _ hevt hactive hproposerHonest _ =>
        obtain ⟨rfl, rfl⟩ := htickPair hevt
        have hproposerSlot : S.E.proposer s ∈ rho.honest := by
          simpa only [hslotEq] using hproposerHonest
        rw [voteStageHeadAtIndex_eq_voteDutyHead S adm hevt hactive, hslotEq]
        exact hhead hproposerSlot
    | confirmationOutput =>
        simp only [ProposalChainStage] at hstage
        omega
    | actionHead =>
        simp only [ProposalChainStage] at hstage
        omega
  have hconfirmations : NamedGenuineConfirmationsPreceqAtIndex
      S rho i Next := by
    intro u _hu C hC
    obtain ⟨s', hevt, _hgenuine⟩ := hC
    exact absurd (htickPair hevt).2 (hconfNe s')
  have hsg : HonestActionSGCarriersPreceqAtIndex S rho i Next := by
    intro u q a _hu hevt _ha
    exact absurd (htickPair hevt).2 (hactionNe q)
  have hnoEmission : ¬ HonestAttestationEmissionAtIndex S rho i := by
    rintro ⟨u, time, a, _hu, hevt, ha⟩
    have hemits : rho.emits S u (Object.attest a) time := ⟨i, hevt, ha⟩
    have hshape := Proofs.Optimistic.emits_attest_shape S hemits
    exact hactionNe a.round (hshape.2.symm.trans (htickPair hevt).2)
  have hout : HonestAttestationOutputPreceqAtIndex S rho i Next :=
    honestAttestationOutputPreceqAtIndex_of_no_emission S rho hnoEmission
  have hanchors : NamedReadAnchorsAtIndex S rho i Next := by
    refine { voteCompatible := ?_, confirmationCompatible := ?_ }
    · intro u s' _hu hevt
      obtain ⟨rfl, hteq⟩ := htickPair hevt
      have hs' : s' = s := by
        have hcongr := congrArg S.E.slotOf hteq
        rwa [Proofs.Optimistic.slotOf_vote_time, Proofs.Optimistic.slotOf_vote_time]
          at hcongr
      subst hs'
      exact hanchor
    · intro u s' _hu hevt
      exact absurd (htickPair hevt).2 (hconfNe s')
  exact ⟨hproposal, hconfirmations, hsg, hout, hanchors⟩
/-- The named vote-phase event facts at every index of the phase. The erased
original is `votePhaseEventFacts` (`MovingChainExecutionRun.lean:3233`). -/
private theorem w4c2_votePhaseEventFacts
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} {End : Block V}
    (hhead : S.E.proposer s ∈ rho.honest → ∀ w ∈ rho.honest,
      voteDutyHead S rho w s = End)
    (hanchor : ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w s) End = true)
    {j : Nat}
    (hlow : inclusiveEventIndex rho (Protocol.proposal_time S.E s) ≤ j)
    (hhigh : j < strictEventIndex rho (Protocol.support_cutoff S.E s)) :
    ProposalChainObservationsSandwichedAtIndex S rho j End End ∧
      NamedGenuineConfirmationsPreceqAtIndex S rho j End ∧
      HonestActionSGCarriersPreceqAtIndex S rho j End ∧
      HonestAttestationOutputPreceqAtIndex S rho j End ∧
      NamedReadAnchorsAtIndex S rho j End := by
  cases hev : rho.events[j]? with
  | none =>
      refine w4c2_movingEventFacts_of_no_tick_named S rho End ?_
      intro w t htick
      rw [hev] at htick
      simp only [reduceCtorEq] at htick
  | some e =>
      cases e with
      | deliver v o t =>
          refine w4c2_movingEventFacts_of_no_tick_named S rho End ?_
          intro w t' htick
          rw [hev] at htick
          simp only [Option.some.injEq, reduceCtorEq] at htick
      | tick u t =>
          have hmem : Event.tick u t ∈ rho.events := List.mem_of_getElem? hev
          have hpub : PublicTime S t := adm.tick_public u t hmem
          have hgt : Protocol.proposal_time S.E s < t :=
            w4c2_eventTime_gt_of_inclusive_le S
              adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hlow hev
          have hlt : t < Protocol.support_cutoff S.E s := by
            have htrue := Proofs.Optimistic.filter_true_of_index_lt
              S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed _
              (Proofs.Optimistic.downward_lt (Protocol.support_cutoff S.E s))
              (by simpa only [strictEventIndex] using hhigh) hev
            simpa only [decide_eq_true_eq, Event.time] using htrue
          have hhonest : u ∈ rho.honest := by
            simpa only [Event.node] using adm.honest_only _ hmem
          rcases publicTime_slotWindow_cases S hpub hgt
            (le_of_lt (lt_of_lt_of_le hlt
              ((w4c2_support_cutoff_le_view_freeze_local S.E s).trans
                (le_of_lt (w4c2_view_freeze_lt_proposal_succ S.E s)))))
            with ht | ht | ht | ht
          · subst ht
            refine w4c2_movingEventFacts_vote_at_named S adm hev ?_
              (hanchor u hhonest)
            intro hp
            rw [hhead hp u hhonest]
            exact ⟨Block.preceq_self _, Block.preceq_self _⟩
          · exact absurd (ht ▸ hlt) (lt_irrefl _)
          · exact absurd (ht ▸ hlt)
              (not_lt_of_ge (w4c2_support_cutoff_le_view_freeze_local S.E s))
          · exact absurd (ht ▸ hlt) (not_lt_of_ge
              (le_of_lt (lt_of_le_of_lt
                (w4c2_support_cutoff_le_view_freeze_local S.E s)
                (w4c2_view_freeze_lt_proposal_succ S.E s))))

/-- **The N moving history runs to the end of the run, before the cutoff.**

The erased original is `MovingFrontierChainState.complete_before_cutoff`
(`MovingChainExecutionRun.lean:3347`), with the run block a named witness and
the head and anchor hypotheses at the named reads. -/
theorem MovingFrontierChainStateN.complete_before_cutoff
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {t1 : Time} {M0 : Height} {n0 : Nat} {s : Slot}
    {EndAt : Nat → Block V} {End : Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0
      (inclusiveEventIndex rho (Protocol.proposal_time S.E s)) EndAt)
    (hEnd : EndAt (inclusiveEventIndex rho
      (Protocol.proposal_time S.E s)) = End)
    (hrun : ∃ E : NamedBlock V, E.erase = End ∧ RunBlock S rho E)
    (hproposalHor : Protocol.proposal_time S.E s ≤ rho.horizon)
    (hcutFuture : rho.horizon < Protocol.support_cutoff S.E s)
    (hhead : S.E.proposer s ∈ rho.honest → ∀ w ∈ rho.honest,
      voteDutyHead S rho w s = End)
    (hanchor : ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w s) End = true) :
    ∃ End' : Nat → Block V,
      MovingFrontierChainStateN S rho t1 M0 n0 rho.events.length End' := by
  have hstartLen : inclusiveEventIndex rho
      (Protocol.proposal_time S.E s) ≤ rho.events.length := by
    rw [events_length_eq_inclusive_horizon S adm]
    exact inclusiveEventIndex_mono rho hproposalHor
  have hlenCut : rho.events.length ≤
      strictEventIndex rho (Protocol.support_cutoff S.E s) := by
    rw [events_length_eq_inclusive_horizon S adm]
    exact inclusiveEventIndex_le_strictEventIndex_of_lt rho hcutFuture
  obtain ⟨End', _hlow, _hhigh, hstate⟩ :=
    h.through_constantEndpoint_named_public S
      (by rw [hEnd]; exact Block.preceq_self End) hrun hstartLen (by
      intro j hj hjlen
      exact w4c2_votePhaseEventFacts S adm hhead hanchor hj
        (hjlen.trans_le hlenCut))
  exact ⟨End', hstate⟩

#print axioms MovingFrontierChainStateN.complete_before_cutoff


theorem MovingSlotEntryStateN.stepHonest_mixed_of_supply
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End Next : Block V}
    (hentry : MovingSlotEntryStateN S rho t1 M0 (c + 1) Prev End)
    (hdata : MovingSlotWindowDataC S rho M0 c Prev)
    (hdata' : MovingSlotWindowData S rho t1 M0 (c + 1))
    (hfrontier : MovingSlotFrontierAt S rho c End Next)
    (hfacts : NamedMovingSlotWindowFacts S rho (c + 1) End Next)
    (hprop : S.E.proposer (c + 1 + 1) ∈ rho.honest)
    {v : V} (hv : v ∈ rho.honest)
    (hadopt : MovingSlotAdoptionSupplyAt S rho c End) :
    ∃ P : NamedBlock V, proposedBlockAt S rho (c + 1 + 1) = some P ∧
      MovingSlotEntryStateN S rho t1 M0 (c + 1 + 1) Next P.erase := by
  classical
  obtain ⟨r, hround, hpostAction, hcut, hupper⟩ := hdata.round
  have hhorSC : Protocol.support_cutoff S.E (c + 1) ≤ rho.horizon :=
    (support_cutoff_le_confirmation_time S.E (c + 1)).trans hdata'.slotHor
  have hhorProp : Protocol.proposal_time S.E (c + 1 + 1) ≤ rho.horizon :=
    (w4_proposalSucc_le_confirmation_c2 S.E (c + 1)).trans hdata'.slotHor
  obtain ⟨P, hP⟩ := proposedBlockAt_isSome S rho (c + 1 + 1)
  obtain ⟨hparent, hvotes, hheadEq, hconf⟩ := hadopt Next hfrontier hprop P hP
  have hcone := hentry.windowVotesCone_of_ceiling S adm hcom hfb hdata.pos
    hround hupper hpostAction hcut hdata.postVote hdata.postProp
    hdata.slotHor hfrontier
  obtain ⟨EndAt, hhistory, _hprev, hEndAt⟩ := hentry.prevEndpoint
  have hrunE : ∃ E : NamedBlock V, E.erase = End ∧ RunBlock S rho E := by
    rw [← hEndAt]
    exact hhistory.endpointRun _ hhistory.start_le (Nat.le_refl _)
  have hrunN : ∃ N : NamedBlock V, N.erase = Next ∧ RunBlock S rho N :=
    hfrontier.runBlock S adm hrunE
  exact ⟨P, hP, hentry.step_honestProposer_named S adm (Nat.succ_pos c)
    hrunN hfacts hprop hhorProp hhorSC hparent hv hP hcone hvotes hheadEq
    hconf⟩

#print axioms MovingSlotEntryStateN.stepHonest_mixed_of_supply

private theorem w4c2_frontier_unique
    {S : Setup V} {rho : Run V} {s : Slot} {A B End : Block V}
    (hA : MovingSlotFrontierAt S rho s End A)
    (hB : MovingSlotFrontierAt S rho s End B) : A = B :=
  Option.some.inj (hA.selected.symm.trans hB.selected)


theorem movingSlotAdoptionParent_of_ordinary
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hentry : MovingSlotEntryStateN S rho t1 M0 (c + 1) Prev End)
    (hdata : MovingSlotWindowDataC S rho M0 c Prev)
    (htiming : MovingSlotActionCeiling S rho c Prev)
    (hdata' : MovingSlotWindowData S rho t1 M0 (c + 1))
    {v : V} (hv : v ∈ rho.honest) :
    ∀ Next : Block V,
      MovingSlotFrontierAt S rho c End Next →
      S.E.proposer (c + 1 + 1) ∈ rho.honest →
      ∀ P : NamedBlock V, proposedBlockAt S rho (c + 1 + 1) = some P →
        Block.Preceq Next (proposedParent S rho (c + 1 + 1)) := by
  intro Next hfrontier hprop _P _hP
  obtain ⟨r, hround, hpostAction, hcut, hupper⟩ := hdata.round
  obtain ⟨Next0, hfrontier0, hfacts0⟩ :=
    hentry.windowFacts_of_ceiling S adm hcom hfb hdata.pos hround hupper
      hpostAction hcut hdata.postVote hdata.postProp hdata.slotHor htiming
  have hNext : Next = Next0 := w4c2_frontier_unique hfrontier hfrontier0
  subst hNext
  exact hentry.honestParent_of_ceiling S adm hcom hfb hdata
    (hentry.enteredCeilingData_mixed S adm hdata' hfrontier0 hfacts0 hprop hv)
    hfrontier0 hfacts0 hprop hv

#print axioms movingSlotAdoptionParent_of_ordinary

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
