module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.W4CarrierFinalityField
public import DecoupledConsensusProofs.Execution.W4RecoverySpine
public import DecoupledConsensusProofs.Protocol.Schedule.W4D2SourceCallsite

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Carrier export from the named moving fold
This leaf is additive. It consumes the prepared named fold directly and keeps
The previous `MovingChainAtCarrierFrom` result as the public carrier interface.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.NamedRecoveryRead
open Protocol Proofs.HealingLemmas
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

private theorem w4cat_action_lt_openingProposal0
    (S : Setup V) {p r : Round} (hpr : p < r) :
    S.a p < Protocol.proposal_time S.E (S.hc.opening_slot r) := by
  have hslot : S.hc.opening_slot p + 2 ≤ S.hc.opening_slot r := by
    simp only [Protocol.HealConfig.opening_slot]
    have hstep : (p + 1) * S.hc.R ≤ r * S.hc.R :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hpr)
    calc
      p * S.hc.R + 2 ≤ p * S.hc.R + S.hc.R :=
        Nat.add_le_add_left S.hc.R_ge_two _
      _ = (p + 1) * S.hc.R := by ring
      _ ≤ r * S.hc.R := hstep
  have hbase : Protocol.confirmation_time S.E (S.hc.opening_slot p) <
      Protocol.proposal_time S.E (S.hc.opening_slot r) := by
    have hlt : Protocol.confirmation_time S.E (S.hc.opening_slot p) <
        Protocol.proposal_time S.E (S.hc.opening_slot p + 2) := by
      unfold Protocol.confirmation_time Protocol.proposal_time Env.t slotStart
      push_cast
      have h68 : 6 * S.E.Δ < 8 * S.E.Δ :=
        Int.mul_lt_mul_of_pos_right (by decide : (6 : Time) < 8) S.E.Δ_pos
      calc
        4 * S.E.Δ * ((S.hc.opening_slot p : Time)) + 6 * S.E.Δ <
            4 * S.E.Δ * ((S.hc.opening_slot p : Time)) + 8 * S.E.Δ :=
          Int.add_lt_add_left h68 _
        _ = 4 * S.E.Δ * (((S.hc.opening_slot p : Time)) + 2) := by ring
    exact lt_of_lt_of_le hlt (Protocol.proposal_time_mono S.E hslot)
  simpa only [Setup.a, Protocol.a_eq_confirmation_time] using hbase

private theorem w4cat_proposal_succ_le_confirmation (E : Env V) (s : Slot) :
    Protocol.proposal_time E (s + 1) ≤ Protocol.confirmation_time E s := by
  rw [show Protocol.proposal_time E (s + 1) =
      (4 * ((s + 1 : Slot) : Time) + 0) * E.Δ by
        unfold Protocol.proposal_time Env.t slotStart
        ring]
  rw [show Protocol.confirmation_time E s =
      (4 * ((s : Slot) : Time) + 6) * E.Δ by
        unfold Protocol.confirmation_time Env.t slotStart
        ring]
  refine Int.mul_le_mul_of_nonneg_right ?_ (le_of_lt E.Δ_pos)
  push_cast
  omega

private theorem w4cat_confirmation_pred_pred_lt_proposal
    (E : Env V) {s : Slot} (hs : 2 ≤ s) :
    Protocol.confirmation_time E (s - 1 - 1) <
      Protocol.proposal_time E s := by
  rw [show Protocol.confirmation_time E (s - 1 - 1) =
      (4 * ((s - 1 - 1 : Slot) : Time) + 6) * E.Δ by
        unfold Protocol.confirmation_time Env.t slotStart
        ring]
  rw [show Protocol.proposal_time E s =
      (4 * ((s : Slot) : Time) + 0) * E.Δ by
        unfold Protocol.proposal_time Env.t slotStart
        ring]
  refine Int.mul_lt_mul_of_pos_right ?_ E.Δ_pos
  have hnat : (s - 1 - 1) + 2 = s := by
    simpa only [Nat.sub_sub, Nat.reduceAdd] using
      (Nat.sub_add_cancel hs)
  have hcast : ((s - 1 - 1 : Nat) : Int) = (s : Int) - 2 := by
    have hcastNat := congrArg (fun n : Nat => (n : Int)) hnat
    push_cast at hcastNat
    omega
  rw [hcast]
  omega

private theorem w4cat_nat_le_pred_of_succ_le {a b : Nat}
    (h : a + 1 ≤ b) : a ≤ b - 1 := by omega

private theorem w4cat_nat_lt_pred_of_succ_lt {a b : Nat}
    (h : a + 1 < b) : a < b - 1 := by omega

private theorem w4cat_nat_zero_lt_add_three (n : Nat) :
    0 < n + 3 := by omega

private theorem w4cat_nat_two_le_add_three_add_one (n : Nat) :
    2 ≤ n + 3 + 1 := by omega


private theorem w4cat_confirmation_mono
    (E : Env V) {a b : Slot} (hab : a ≤ b) :
    Protocol.confirmation_time E a ≤ Protocol.confirmation_time E b := by
  exact Int.add_le_add_right (Protocol.proposal_time_mono E hab) _

private theorem w4cat_boundary_predecessor_eq
    {a d o : Nat} (hbase : a + 3 ≤ o) (hd : d + 1 = o)
    (hlow : ¬ a + 3 ≤ d) :
      d = a + 2 ∧ o = a + 3 := by
  constructor <;> omega

private theorem w4cat_boundary_le_predecessor
    {a d o : Nat} (hbase : a + 3 ≤ o) (hd : d + 1 = o) :
    a + 2 ≤ d := by
  omega

private theorem w4cat_round_lt_of_opening_three
    (S : Setup V) {q r : Round}
    (h : S.hc.opening_slot q + 3 ≤ S.hc.opening_slot r) : q < r := by
  by_contra hnot
  have hle : r ≤ q := Nat.le_of_not_gt hnot
  have hslots : S.hc.opening_slot r ≤ S.hc.opening_slot q := by
    simpa only [Protocol.HealConfig.opening_slot] using
      Nat.mul_le_mul_right S.hc.R hle
  have hbad : S.hc.opening_slot q + 3 ≤ S.hc.opening_slot q :=
    h.trans hslots
  exact (Nat.not_le_of_gt
    (Nat.lt_add_of_pos_right (by decide : 0 < 3))) hbad

private theorem w4cat_foldCoverN
    (S : Setup V) {rho : Run V}
    {q : Round} {D : NamedBlock V} {M0 : Height}
    (hbaseTiming :
      0 < S.hc.round_of (S.hc.opening_slot q + 3) ∧
      S.E.t_GST ≤ S.a
        (S.hc.round_of (S.hc.opening_slot q + 3) - 1) ∧
      Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤ rho.horizon)
    (hfoldAt : ∀ {s : Slot}, S.hc.opening_slot q + 3 ≤ s →
      Protocol.confirmation_time S.E (s - 1) ≤ rho.horizon →
      ∃ F : Slot → Block V, ∃ End : Block V,
        MovingSlotFoldAtN S rho
          (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
          (S.hc.opening_slot q + 3) s F End ∧
        F (S.hc.opening_slot q + 3) = D.erase) :
    ∃ (s : Slot) (F : Slot → Block V) (End : Block V),
      MovingSlotFoldAtN S rho
          (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
          (S.hc.opening_slot q + 3) s F End ∧
        F (S.hc.opening_slot q + 3) = D.erase ∧
        MovingSlotFoldCovers S rho q (S.hc.opening_slot q + 3) s := by
  let base := S.hc.opening_slot q + 3
  let z := S.E.slotOf rho.horizon
  let s := if Protocol.support_cutoff S.E z ≤ rho.horizon then z else z - 1
  have hproposalBaseSuccHor : Protocol.proposal_time S.E (base + 1) ≤
      rho.horizon :=
    (w4cat_proposal_succ_le_confirmation S.E base).trans hbaseTiming.2.2
  have hbaseSuccZ : base + 1 ≤ z := by
    dsimp only [z]
    exact Protocol.slot_le_slotOf_of_proposal_time_le S.E
      hproposalBaseSuccHor
  have hbaseZ : base ≤ z := (Nat.le_succ base).trans hbaseSuccZ
  have hzPos : 0 < z :=
    (w4cat_nat_zero_lt_add_three (S.hc.opening_slot q)).trans_le hbaseZ
  have hzTwo : 2 ≤ z :=
    (w4cat_nat_two_le_add_three_add_one (S.hc.opening_slot q)).trans hbaseSuccZ
  have hhorNonneg : 0 ≤ rho.horizon :=
    (Proofs.Optimistic.proposal_time_nonneg S.E (base + 1)).trans
      hproposalBaseSuccHor
  have hproposalZ : Protocol.proposal_time S.E z ≤ rho.horizon := by
    dsimp only [z]
    exact Protocol.proposal_time_slotOf_le S.E hhorNonneg
  have hsBase : base ≤ s := by
    dsimp only [s]
    split_ifs with hcutZ
    · exact hbaseZ
    · exact w4cat_nat_le_pred_of_succ_le hbaseSuccZ
  have hconfPred : Protocol.confirmation_time S.E (s - 1) ≤
      rho.horizon := by
    dsimp only [s]
    split_ifs with hcutZ
    · rw [← support_cutoff_eq_confirmation_time_pred S.E hzPos]
      exact hcutZ
    · exact le_of_lt (calc
        Protocol.confirmation_time S.E (z - 1 - 1) <
            Protocol.proposal_time S.E z :=
          w4cat_confirmation_pred_pred_lt_proposal S.E hzTwo
        _ ≤ rho.horizon := hproposalZ)
  have hreach : ∀ e : Slot,
      Protocol.confirmation_time S.E e ≤ rho.horizon → e < s := by
    intro e he
    have hez : e + 1 ≤ z := by
      dsimp only [z]
      exact Protocol.slot_le_slotOf_of_proposal_time_le S.E
        ((w4cat_proposal_succ_le_confirmation S.E e).trans he)
    dsimp only [s]
    split_ifs with hcutZ
    · exact Nat.lt_of_succ_le hez
    · have hne : e + 1 ≠ z := by
        intro heq
        apply hcutZ
        rw [← heq, ← Protocol.confirmation_time_eq_support_cutoff_succ]
        exact he
      exact w4cat_nat_lt_pred_of_succ_lt (lt_of_le_of_ne hez hne)
  have hcov : MovingSlotFoldCovers S rho q base s :=
    { base := Nat.le_refl _
      reach := hreach }
  obtain ⟨F, End, hfold, hbaseEq⟩ := hfoldAt
    (by simpa only [base] using hsBase) hconfPred
  exact ⟨s, F, End, hfold, hbaseEq, by simpa only [base] using hcov⟩

private theorem w4cat_endpointMemAt
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {q : Round} {D : NamedBlock V} {carrier : V} {M0 : Height}
    (hhandoff : HealedTwoSlotHandoffPrepared S rho q D.erase carrier)
    {s : Slot} {F : Slot → Block V} {FoldEnd : Block V}
    (hfold : MovingSlotFoldAtN S rho
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
      (S.hc.opening_slot q + 3) s F FoldEnd)
    (hbaseEq : F (S.hc.opening_slot q + 3) = D.erase)
    (hcov : MovingSlotFoldCovers S rho q
      (S.hc.opening_slot q + 3) s)
    {r : Round}
    (hboundary : healingBoundaryTime S q <
      Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    (hpostQ : S.E.t_GST ≤ S.a q) :
    ∀ v ∈ rho.honest,
      HonestHeadsAvailableBefore S rho (S.hc.opening_slot r - 1) v
        (Protocol.support_cutoff S.E (S.hc.opening_slot r - 1)) ∧
      F (S.hc.opening_slot r) ∈
        (rho.storeBeforeTime S v (S.a r)).T := by
  intro v hv
  have hArhor := w4cr_actionHorizon S hhor
  have hhorOpen : Protocol.confirmation_time S.E
      (S.hc.opening_slot r) ≤ rho.horizon := by
    simpa only [opening_confirmation_time_eq_action S r] using hArhor
  obtain ⟨hlowR, hhighR⟩ := hcov.mem_range hboundary hhorOpen
  have hbaseOpen : S.hc.opening_slot q + 3 ≤
      S.hc.opening_slot r := by
    exact openingSlot_three_le_of_healingBoundary_lt_proposal S hboundary
  have hqr : q < r := by
    by_contra hnot
    have hle : r ≤ q := Nat.le_of_not_gt hnot
    have hslots : S.hc.opening_slot r ≤ S.hc.opening_slot q := by
      simpa only [Protocol.HealConfig.opening_slot] using
        Nat.mul_le_mul_right S.hc.R hle
    have : S.hc.opening_slot q + 3 ≤ S.hc.opening_slot q :=
      hbaseOpen.trans hslots
    exact (Nat.not_le_of_gt
      (Nat.lt_add_of_pos_right (by decide : 0 < 3))) this
  have hslotQ : S.hc.opening_slot q + 2 ≤
      S.hc.opening_slot r := by
    exact (Nat.le_succ _).trans hbaseOpen
  have ht1 : Protocol.support_cutoff S.E
      (S.hc.opening_slot q + 2) ≤ S.a r := by
    exact (support_cutoff_le_confirmation_time S.E
      (S.hc.opening_slot q + 2)).trans
      ((w4cat_confirmation_mono S.E hslotQ).trans_eq
        (opening_confirmation_time_eq_action S r).symm)
  let d := S.hc.opening_slot r - 1
  have hdSucc : d + 1 = S.hc.opening_slot r := by
    dsimp only [d]
    exact Nat.succ_pred_eq_of_pos
      (Nat.mul_pos (Nat.zero_lt_of_lt hqr)
        (Nat.zero_lt_of_lt S.hc.R_ge_two))
  have hdLow : S.hc.opening_slot q + 2 ≤ d := by
    have hslot : S.hc.opening_slot q + 3 ≤ d + 1 := by
      simpa only [hdSucc] using hbaseOpen
    exact w4cat_boundary_le_predecessor hslot rfl
  have hdHigh : d < s := by
    calc
      d < d + 1 := Nat.lt_succ_self d
      _ = S.hc.opening_slot r := hdSucc
      _ < s := hhighR
  have hcone : NamedHonestVotesCone S rho d
      (fun X => Block.Preceq (F (S.hc.opening_slot r)) X) := by
    by_cases hbaseD : S.hc.opening_slot q + 3 ≤ d
    · have hcone0 := hfold.windowCone d hbaseD hdHigh
      simpa only [hdSucc] using hcone0
    · obtain ⟨hdEq, hopenEq⟩ :=
        w4cat_boundary_predecessor_eq hbaseOpen hdSucc hbaseD
      simpa only [hdEq, hopenEq, hbaseEq] using
        hhandoff.honestVotesCone_two_after adm
          ((vote_time_le_confirmation_time S.E
            (S.hc.opening_slot q + 2)).trans
            ((w4cat_confirmation_mono S.E hslotQ).trans
              hhorOpen))
  have hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E d := by
    have hslot : S.hc.opening_slot q + 2 ≤ d := hdLow
    exact hpostQ.trans
      ((by
        have hqAction : S.a q ≤
            Protocol.proposal_time S.E (S.hc.opening_slot q + 2) :=
          (action_lt_proposal_time_two_after S q).le
        exact hqAction.trans
          ((Protocol.proposal_time_mono S.E hslot).trans
            (le_of_lt (proposal_time_lt_vote_time S.E d)))) )
  have hcut : Protocol.support_cutoff S.E d ≤ S.a r := by
    have hds : d ≤ S.hc.opening_slot r := by
      rw [← hdSucc]
      exact Nat.le_succ _
    exact (support_cutoff_le_confirmation_time S.E d).trans
      ((w4cat_confirmation_mono S.E hds).trans_eq
        (opening_confirmation_time_eq_action S r).symm)
  have hcutHor : Protocol.support_cutoff S.E d ≤ rho.horizon :=
    hcut.trans hArhor
  have hroot : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v (S.a r)).core.toHealing.toFG)
      (F (S.hc.opening_slot r)) := by
    obtain ⟨EndAt, hstate, hval⟩ := hfold.historyAt
      (S.hc.opening_slot r) hlowR (le_of_lt hhighR)
    obtain ⟨E, hE, hErun⟩ :=
      hstate.endpointRun _ hstate.start_le (Nat.le_refl _)
    have hroot' := hstate.readRoot_preceq_endpointAtCursor_named S adm hfb
      (fun _q hq =>
        w4cat_action_lt_openingProposal0 S
          ((action_strictMono S).lt_iff_lt.mp hq))
      (Nat.le_refl _) hv ht1 hE hErun
    rw [hE.trans hval] at hroot'
    exact hroot'
  have havailable := honestHeadsAvailableBefore_of_postHealingCone_at
    S adm.toNamedAdmissibleCore hv hpostVote hcutHor hcut hroot hcone
  exact ⟨havailable, (storeBeforeTime_mem_stamp_of_cone S adm hcom
    havailable hcut hcone (Block.preceq_self _)).1⟩

private theorem w4cat_action_lt_openingProposal
    (S : Setup V) {p r : Round} (hpr : p < r) :
    S.a p < Protocol.proposal_time S.E (S.hc.opening_slot r) := by
  have hslot : S.hc.opening_slot p + 2 ≤ S.hc.opening_slot r := by
    simp only [Protocol.HealConfig.opening_slot]
    have hstep : (p + 1) * S.hc.R ≤ r * S.hc.R :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hpr)
    calc
      p * S.hc.R + 2 ≤ p * S.hc.R + S.hc.R :=
        Nat.add_le_add_left S.hc.R_ge_two _
      _ = (p + 1) * S.hc.R := by ring
      _ ≤ r * S.hc.R := hstep
  have hbase : Protocol.confirmation_time S.E (S.hc.opening_slot p) <
      Protocol.proposal_time S.E (S.hc.opening_slot r) := by
    have hlt : Protocol.confirmation_time S.E (S.hc.opening_slot p) <
        Protocol.proposal_time S.E (S.hc.opening_slot p + 2) := by
      unfold Protocol.confirmation_time Protocol.proposal_time Env.t slotStart
      push_cast
      have h68 : 6 * S.E.Δ < 8 * S.E.Δ :=
        Int.mul_lt_mul_of_pos_right (by decide : (6 : Time) < 8) S.E.Δ_pos
      calc
        4 * S.E.Δ * ((S.hc.opening_slot p : Time)) + 6 * S.E.Δ <
            4 * S.E.Δ * ((S.hc.opening_slot p : Time)) + 8 * S.E.Δ :=
          Int.add_lt_add_left h68 _
        _ = 4 * S.E.Δ * (((S.hc.opening_slot p : Time)) + 2) := by ring
    exact lt_of_lt_of_le hlt (Protocol.proposal_time_mono S.E hslot)
  simpa only [Setup.a, Protocol.a_eq_confirmation_time] using hbase

private theorem w4cat_endpointRunAt
    (S : Setup V) {rho : Run V}
    {t1 : Time} {M0 : Height} {s0 s : Slot} {F : Slot → Block V}
    {End : Block V}
    (hfold : MovingSlotFoldAtN S rho t1 M0 s0 s F End)
    {d : Slot} (hlow : s0 ≤ d) (hhigh : d ≤ s) :
    ∃ E : NamedBlock V, E.erase = F d ∧ RunBlock S rho E := by
  obtain ⟨EndAt, hstate, hval⟩ := hfold.historyAt d hlow hhigh
  obtain ⟨E, hE, hErun⟩ :=
    hstate.endpointRun _ hstate.start_le (Nat.le_refl _)
  exact ⟨E, hE.trans hval, hErun⟩


private theorem w4cat_frontierAt
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {s0 s : Slot} {F : Slot → Block V}
    {End : Block V}
    (hfold : MovingSlotFoldAtN S rho t1 M0 s0 s F End)
    {r : Round}
    (hlow : s0 ≤ S.hc.opening_slot r)
    (hhigh : S.hc.opening_slot r ≤ s)
    {v : V} (hv : v ∈ rho.honest)
    {E : NamedBlock V} (hE : E.erase = F (S.hc.opening_slot r))
    (hErun : RunBlock S rho E) :
    (rho.storeBeforeTime S v (S.a r)).core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg E).h := by
  obtain ⟨EndAt, hstate, hval⟩ := hfold.historyAt
    (S.hc.opening_slot r) hlow hhigh
  have hsep : ∀ _q : Round, S.a _q < S.a r →
      S.a _q < Protocol.proposal_time S.E (S.hc.opening_slot r) := by
    intro p hp
    exact w4cat_action_lt_openingProposal S
      ((action_strictMono S).lt_iff_lt.mp hp)
  have hEraw : E.erase = EndAt
      (strictEventIndex rho (Protocol.proposal_time S.E
        (S.hc.opening_slot r))) := hE.trans hval.symm
  exact hstate.readFrontier_sub_one_le_endpointAtCursor_named S adm hbelow
    hsep
    (Nat.le_refl _) hv hEraw hErun

private theorem w4cat_actionCarriersAt
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {t1 : Time} {M0 : Height} {s0 s : Slot} {F : Slot → Block V}
    {End : Block V}
    (hfold : MovingSlotFoldAtN S rho t1 M0 s0 s F End)
    {r : Round}
    (hlow : s0 ≤ S.hc.opening_slot (r + 1))
    (hhigh : S.hc.opening_slot (r + 1) ≤ s)
    (ht1 : t1 ≤ S.a r) (hhor : S.a r ≤ rho.horizon) :
    ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r)
        (F (S.hc.opening_slot (r + 1))) := by
  obtain ⟨EndAt, hstate, hval⟩ := hfold.historyAt
    (S.hc.opening_slot (r + 1)) hlow hhigh
  have hbefore := w4cat_action_lt_openingProposal S (Nat.lt_succ_self r)
  rw [← hval]
  exact hstate.previousActionCarriersPreceqAtRead S adm ht1 hhor
    hbefore
    (Nat.le_refl _)

private theorem w4cat_frontierAtTimeN
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {s0 s : Slot} {F : Slot → Block V}
    {End : Block V}
    (hfold : MovingSlotFoldAtN S rho t1 M0 s0 s F End)
    {d : Slot} {read : Time}
    (hlow : s0 ≤ d) (hhigh : d ≤ s)
    (hsep : ∀ q : Round, S.a q < read →
      S.a q < Protocol.proposal_time S.E d)
    {v : V} (hv : v ∈ rho.honest)
    {E : NamedBlock V} (hE : E.erase = F d)
    (hErun : RunBlock S rho E) :
    (rho.storeBeforeTime S v read).core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg E).h := by
  obtain ⟨EndAt, hstate, hval⟩ := hfold.historyAt d hlow hhigh
  have hEraw : E.erase = EndAt
      (strictEventIndex rho (Protocol.proposal_time S.E d)) :=
    hE.trans hval.symm
  exact hstate.readFrontier_sub_one_le_endpointAtCursor_named S adm hfb
    hsep (Nat.le_refl _) hv hEraw hErun

private theorem w4cat_bandAtProposalN
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {s0 s : Slot} {F : Slot → Block V}
    {End : Block V}
    (hfold : MovingSlotFoldAtN S rho t1 M0 s0 s F End)
    {d : Slot} {read : Time} {P : NamedBlock V}
    (hlow : s0 ≤ d) (hhigh : d ≤ s)
    (hprop : S.E.proposer d ∈ rho.honest)
    (hP : proposedBlockAt S rho d = some P)
    (hPrun : RunBlock S rho P)
    (hsep : ∀ q : Round, S.a q < read →
      S.a q < Protocol.proposal_time S.E d) :
    ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v read).core.h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg P).h := by
  have hparent : Block.Preceq (F d) (proposedParent S rho d) :=
    hfold.parent d hlow hhigh hprop
  have hparentP := proposedParent_preceq_proposedBlockAt S rho d hP
  obtain ⟨E, hE, hErun⟩ := w4cat_endpointRunAt S hfold hlow hhigh
  have hEP : Block.Preceq E.erase P.erase := by
    rw [hE]
    exact Block.preceq_trans hparent hparentP
  have hEnamedP : NamedBlock.Preceq E P :=
    namedPreceq_of_runBlock_erase_preceq adm hErun hPrun hEP
  have hheight := Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hEnamedP
  intro v hv
  exact (w4cat_frontierAtTimeN S adm hfb hfold hlow hhigh hsep hv hE hErun).trans
    hheight

private theorem w4cat_roundFloor_mem_filtered_at_plusTwoProposalN
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {q0 : Round} {F : Slot → Block V}
    {t1 : Time} {M0 : Height} {s0 s : Slot} {FoldEnd : Block V}
    (hfold : MovingSlotFoldAtN S rho t1 M0 s0 s F FoldEnd)
    (hcov : MovingSlotFoldCovers S rho q0 s0 s)
    {r : Round} {C : Block V}
    (hboundary : healingBoundaryTime S q0 <
      Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    (hcarriers : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u (r - 1))
        (F (S.hc.opening_slot r)))
    (hfields : RoundFloorFieldsAt S rho r C)
    (hrootC : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S
          (S.E.proposer (S.hc.opening_slot r + 2))
          (Protocol.proposal_time S.E
            (S.hc.opening_slot r + 2))).toHealing.toFG) C) :
    C ∈ Protocol.get_filtered_block_tree
      (Protocol.proposerDutyStore S rho
        (S.hc.opening_slot r + 2)).toHealing.toFG := by
  let d := S.hc.opening_slot r + 2
  let w := S.E.proposer d
  let T2 := Protocol.proposal_time S.E d
  let pre := (rho.storeBeforeTime S w T2).core
  have hd : S.hc.opening_slot r ≤ d := by
    simpa only [d] using Nat.le_add_right (S.hc.opening_slot r) 2
  have hw : w ∈ rho.honest := by
    simpa only [w, d] using hcarrier.2.2
  have hboundary2 : healingBoundaryTime S q0 <
      Protocol.proposal_time S.E d :=
    lt_of_lt_of_le hboundary (Protocol.proposal_time_mono S.E hd)
  obtain ⟨hlow2, hhigh2⟩ := hcov.mem_range hboundary2 hhor
  have hlow : s0 ≤ S.hc.opening_slot r :=
    hcov.base.trans
      (openingSlot_three_le_of_healingBoundary_lt_proposal S hboundary)
  obtain ⟨EndAt, hstate, hval⟩ := hfold.historyAt d hlow2
    (le_of_lt hhigh2)
  obtain ⟨E, hEAt, hErun⟩ :=
    hstate.endpointRun _ hstate.start_le (Nat.le_refl _)
  have hbandRaw :=
    hstate.readFrontier_sub_one_le_endpointAtCursor_named S adm hfb
      (t := T2) (s := d) (fun _q hq => hq) (Nat.le_refl _) hw hEAt hErun
  have hband : pre.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg E).h := by
    simpa only [pre, w, T2] using hbandRaw
  have hpc : ParentClosed pre := by
    simpa only [pre, Run.storeBeforeTime] using
      Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho T2 w
  have hFJ : Block.Preceq pre.F pre.J := by
    simpa only [pre, Run.storeBeforeTime] using
      Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho T2 w
  have hparent : Block.Preceq (F d) (proposedParent S rho d) :=
    hfold.parent d hlow2 (le_of_lt hhigh2)
      (by simpa only [w, d] using hw)
  have hparentPre : proposedParent S rho d ∈ pre.T := by
    simpa only [pre, w, T2, d, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      (proposedParent_mem S rho d)
  have hFmem : F d ∈ pre.T :=
    Proofs.Records.mem_of_preceq ((parentClosed_iff pre).mp hpc).2
      (F d) (proposedParent S rho d) hparentPre hparent
  have hEerase : E.erase = F d := hEAt.trans hval
  have hFmem' : F d ∈
      (rho.stateBeforeTime S T2 w).st.core.T := by
    simpa only [pre, Run.storeBeforeTime] using hFmem
  obtain ⟨E', hE'body, hE'erase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho T2 w hFmem'
  obtain ⟨m, hm, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed T2
  have hE'run : RunBlock S rho E' := by
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw (i := m)
    simpa only [hm] using hE'body
  have hEE' : E = E' := by
    apply adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      E E' hErun hE'run E E'
    · exact Or.inl (Proofs.NamedAncestry.named_self E)
    · exact Or.inr (Proofs.NamedAncestry.named_self E')
    · rw [← Proofs.NamedWire.erase_root E, ← Proofs.NamedWire.erase_root E', hEerase,
        hE'erase]
  have hderive : pre.σ (F d) =
      Protocol.derive_named S.E S.cfg E := by
    calc
      pre.σ (F d) = Protocol.derive_named S.E S.cfg E' := by
        simpa only [pre, Run.storeBeforeTime, hE'erase] using
          (Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho T2 w E' hE'body)
      _ = Protocol.derive_named S.E S.cfg E := by rw [hEE']
  have hbandStore : pre.h_max - 1 ≤ (pre.σ (F d)).h := by
    rw [hderive]
    exact hband
  have hCbase : Block.Preceq C (F (S.hc.opening_slot r)) :=
    Block.preceq_trans (hfields.floorBelowCarriers w hw)
      (hcarriers w hw)
  have hCF : Block.Preceq C (F d) :=
    Block.preceq_trans hCbase
      (hfold.mono _ _ hlow hd (le_of_lt hhigh2))
  have hrootPre : Block.Preceq
      (Protocol.get_fg_root pre.toHealing.toFG) C := by
    simpa only [pre, w, T2, d] using hrootC
  have hfiltered := canonicalConeSegment_mem_filtered_of_root_preceq
    hpc hFJ (P := Protocol.get_fg_root pre.toHealing.toFG)
      (W := F d) (D := C) (Block.preceq_self _) hFmem hbandStore
      hrootPre hCF
  simpa only [Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
    pre, w, T2] using hfiltered

private theorem w4cat_roundFloor_mem_filtered_or_prec_rootN
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {q0 : Round} {F : Slot → Block V}
    {t1 : Time} {M0 : Height} {s0 s : Slot} {FoldEnd : Block V}
    (hfold : MovingSlotFoldAtN S rho t1 M0 s0 s F FoldEnd)
    (hcov : MovingSlotFoldCovers S rho q0 s0 s)
    {r : Round} {C : Block V}
    (hboundary : healingBoundaryTime S q0 <
      Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    (hcarriers : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u (r - 1))
        (F (S.hc.opening_slot r)))
    (hfields : RoundFloorFieldsAt S rho r C)
    {M : Height}
    (hgate : (rho.storeBeforeTime S
        (S.E.proposer (S.hc.opening_slot r + 2))
        (Protocol.proposal_time S.E
          (S.hc.opening_slot r + 2))).h_j + 2 ≤ M)
    (hmax : (rho.storeBeforeTime S
        (S.E.proposer (S.hc.opening_slot r + 2))
        (Protocol.proposal_time S.E
          (S.hc.opening_slot r + 2))).h_max = M) :
    C ∈ Protocol.get_filtered_block_tree
        (Protocol.proposerDutyStore S rho
          (S.hc.opening_slot r + 2)).toHealing.toFG ∨
      Block.Prec C
        (Protocol.get_fg_root
          (rho.storeBeforeTime S
            (S.E.proposer (S.hc.opening_slot r + 2))
            (Protocol.proposal_time S.E
              (S.hc.opening_slot r + 2))).toHealing.toFG) := by
  let d := S.hc.opening_slot r + 2
  let w := S.E.proposer d
  let T2 := Protocol.proposal_time S.E d
  let pre := (rho.storeBeforeTime S w T2).core
  have hd : S.hc.opening_slot r ≤ d := by
    simpa only [d] using Nat.le_add_right (S.hc.opening_slot r) 2
  have hw : w ∈ rho.honest := by
    simpa only [w, d] using hcarrier.2.2
  have hboundary2 : healingBoundaryTime S q0 <
      Protocol.proposal_time S.E d :=
    lt_of_lt_of_le hboundary (Protocol.proposal_time_mono S.E hd)
  obtain ⟨hlow2, hhigh2⟩ := hcov.mem_range hboundary2 hhor
  have hlow : s0 ≤ S.hc.opening_slot r :=
    hcov.base.trans
      (openingSlot_three_le_of_healingBoundary_lt_proposal S hboundary)
  obtain ⟨EndAt, hstate, hval⟩ := hfold.historyAt d hlow2
    (le_of_lt hhigh2)
  obtain ⟨E, hEAt, hErun⟩ :=
    hstate.endpointRun _ hstate.start_le (Nat.le_refl _)
  have hbandRaw :=
    hstate.readFrontier_sub_one_le_endpointAtCursor_named S adm hfb
      (t := T2) (s := d) (fun _q hq => hq) (Nat.le_refl _) hw hEAt hErun
  have hband : M - 1 ≤
      (Protocol.derive_named S.E S.cfg E).h := by
    have hbandPre : pre.h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg E).h := by
      simpa only [pre, w, T2] using hbandRaw
    have hmaxPre : pre.h_max = M := by
      simpa only [pre, w, T2, d] using hmax
    rw [hmaxPre] at hbandPre
    exact hbandPre
  have hCbase : Block.Preceq C (F (S.hc.opening_slot r)) :=
    Block.preceq_trans (hfields.floorBelowCarriers w hw)
      (hcarriers w hw)
  have hCF : Block.Preceq C (F d) :=
    Block.preceq_trans hCbase
      (hfold.mono _ _ hlow hd (le_of_lt hhigh2))
  have hgatePre : pre.h_j + 2 ≤ M := by
    simpa only [pre, w, T2, d] using hgate
  have hmaxPre : pre.h_max = M := by
    simpa only [pre, w, T2, d] using hmax
  have hCFNamed : Block.Preceq C E.erase := by
    simpa only [hEAt, hval] using hCF
  rcases fgRoot_comparable_of_bandWitness S adm hfb hw hgatePre hmaxPre
      hErun hCFNamed hband with hrootC | hCroot
  · exact Or.inl
      (w4cat_roundFloor_mem_filtered_at_plusTwoProposalN
        S adm hfb hfold hcov hboundary hcarrier hhor hcarriers hfields
        (by simpa only [pre, w, T2, d] using hrootC))
  · by_cases heq : C = Protocol.get_fg_root
      (rho.storeBeforeTime S
        (S.E.proposer (S.hc.opening_slot r + 2))
        (Protocol.proposal_time S.E
          (S.hc.opening_slot r + 2))).toHealing.toFG
    · apply Or.inl
      apply w4cat_roundFloor_mem_filtered_at_plusTwoProposalN
        S adm hfb hfold hcov hboundary hcarrier hhor hcarriers hfields
      rw [heq]
      exact Block.preceq_self _
    · apply Or.inr
      change (!decide (C = Protocol.get_fg_root
          (rho.storeBeforeTime S
            (S.E.proposer (S.hc.opening_slot r + 2))
            (Protocol.proposal_time S.E
              (S.hc.opening_slot r + 2))).toHealing.toFG) &&
        Block.preceq C
          (Protocol.get_fg_root
            (rho.storeBeforeTime S
              (S.E.proposer (S.hc.opening_slot r + 2))
              (Protocol.proposal_time S.E
                (S.hc.opening_slot r + 2))).toHealing.toFG)) = true
      rw [Bool.and_eq_true]
      exact ⟨by simp only [heq, decide_false, Bool.not_false],
        by simpa only [pre, w, T2, d] using hCroot⟩

set_option maxHeartbeats 1200000 in
private theorem w4cat_roundFloor_mem_filtered_or_prec_rootN_of_bandCover
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {q0 : Round} {F : Slot → Block V}
    {t1 : Time} {M0 : Height} {s0 s : Slot} {FoldEnd : Block V}
    (hfold : MovingSlotFoldAtN S rho t1 M0 s0 s F FoldEnd)
    (hcov : MovingSlotFoldCovers S rho q0 s0 s)
    {r : Round} {C : Block V}
    (hboundary : healingBoundaryTime S q0 <
      Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    (hcarriers : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u (r - 1))
        (F (S.hc.opening_slot r)))
    (hfields : RoundFloorFieldsAt S rho r C) :
    C ∈ Protocol.get_filtered_block_tree
        (Protocol.proposerDutyStore S rho
          (S.hc.opening_slot r + 2)).toHealing.toFG ∨
      Block.Prec C
        (Protocol.get_fg_root
          (rho.storeBeforeTime S
            (S.E.proposer (S.hc.opening_slot r + 2))
            (Protocol.proposal_time S.E
              (S.hc.opening_slot r + 2))).toHealing.toFG) := by
  let d := S.hc.opening_slot r + 2
  let w := S.E.proposer d
  let T2 := Protocol.proposal_time S.E d
  let pre := (rho.storeBeforeTime S w T2).core
  by_cases hgate : pre.h_j + 2 ≤ pre.h_max
  · exact w4cat_roundFloor_mem_filtered_or_prec_rootN S adm hfb hfold hcov
      hboundary hcarrier hhor hcarriers hfields hgate rfl
  · have hd : S.hc.opening_slot r ≤ d := by
      simpa only [d] using Nat.le_add_right (S.hc.opening_slot r) 2
    have hw : w ∈ rho.honest := by
      simpa only [w, d] using hcarrier.2.2
    have hboundary2 : healingBoundaryTime S q0 <
        Protocol.proposal_time S.E d :=
      lt_of_lt_of_le hboundary (Protocol.proposal_time_mono S.E hd)
    obtain ⟨hlow2, hhigh2⟩ := hcov.mem_range hboundary2 hhor
    have hlow : s0 ≤ S.hc.opening_slot r :=
      hcov.base.trans
        (openingSlot_three_le_of_healingBoundary_lt_proposal S hboundary)
    have hparent : Block.Preceq (F d) (proposedParent S rho d) :=
      hfold.parent d hlow2 (le_of_lt hhigh2)
        (by simpa only [w, d] using hw)
    have hCbase : Block.Preceq C (F (S.hc.opening_slot r)) :=
      Block.preceq_trans (hfields.floorBelowCarriers w hw)
        (hcarriers w hw)
    have hCF : Block.Preceq C (F d) :=
      Block.preceq_trans hCbase
        (hfold.mono _ _ hlow hd (le_of_lt hhigh2))
    have hCparent : Block.Preceq C (proposedParent S rho d) :=
      Block.preceq_trans hCF hparent
    have hrootParentDuty : Block.Preceq
        (Protocol.get_fg_root
          (Internal.NamedRecoveryRead.proposalDutyRead S rho
            d).st.core.toHealing.toFG)
        (proposedParent S rho d) :=
      fgRoot_preceq_proposedParent S rho d
    rcases Block.preceq_linear hrootParentDuty hCparent with hrootC | hCroot
    · exact Or.inl
        (w4cat_roundFloor_mem_filtered_at_plusTwoProposalN
          S adm hfb hfold hcov hboundary hcarrier hhor hcarriers hfields
          (by simpa only [pre, w, T2, d] using hrootC))
    · have hCroot' : Block.Preceq C
          (Protocol.get_fg_root
            (rho.storeBeforeTime S
              (S.E.proposer (S.hc.opening_slot r + 2))
              (Protocol.proposal_time S.E
                (S.hc.opening_slot r + 2))).toHealing.toFG) := by
        simpa only [Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
          pre, w, T2, d] using hCroot
      by_cases heq : C = Protocol.get_fg_root
          (rho.storeBeforeTime S
            (S.E.proposer (S.hc.opening_slot r + 2))
            (Protocol.proposal_time S.E
              (S.hc.opening_slot r + 2))).toHealing.toFG
      · exact Or.inl
          (w4cat_roundFloor_mem_filtered_at_plusTwoProposalN
            S adm hfb hfold hcov hboundary hcarrier hhor hcarriers hfields
            (by rw [heq]; exact Block.preceq_self _))
      · exact Or.inr
          (by
            unfold Block.Prec Block.prec
            rw [Bool.and_eq_true]
            exact ⟨by simp only [heq, decide_false, Bool.not_false], hCroot'⟩)

set_option maxHeartbeats 800000 in
private theorem w4cat_carrierBelowAt
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {q : Round} {D : NamedBlock V} {carrier : V} {M0 : Height}
    (hhandoff : HealedTwoSlotHandoffPrepared S rho q D.erase carrier)
    {s : Slot} {F : Slot → Block V} {FoldEnd : Block V}
    (hfold : MovingSlotFoldAtN S rho
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
      (S.hc.opening_slot q + 3) s F FoldEnd)
    (hbaseEq : F (S.hc.opening_slot q + 3) = D.erase)
    (hcov : MovingSlotFoldCovers S rho q
      (S.hc.opening_slot q + 3) s)
    (hboundaryCore : W4NamedHandoffBoundaryCore S rho q
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0 D)
    {r : Round}
    (hboundary : healingBoundaryTime S q <
      Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    (hbaseTiming :
      0 < S.hc.round_of (S.hc.opening_slot q + 3) ∧
      S.E.t_GST ≤ S.a
        (S.hc.round_of (S.hc.opening_slot q + 3) - 1) ∧
      Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤ rho.horizon)
    (hpostQ : S.E.t_GST ≤ S.a q) :
    ∀ w ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho w (r - 1))
        (F (S.hc.opening_slot r)) := by
  have hArhor := w4cr_actionHorizon S hhor
  have hhorOpen : Protocol.confirmation_time S.E
      (S.hc.opening_slot r) ≤ rho.horizon := by
    simpa only [opening_confirmation_time_eq_action S r] using hArhor
  have hbaseOpen : S.hc.opening_slot q + 3 ≤
      S.hc.opening_slot r :=
    openingSlot_three_le_of_healingBoundary_lt_proposal S hboundary
  have hqr : q < r := w4cat_round_lt_of_opening_three S hbaseOpen
  have hrpos : 0 < r :=
    (Nat.zero_lt_succ q).trans_le (Nat.succ_le_of_lt hqr)
  have hqPrev : q ≤ r - 1 := by
    exact Nat.le_sub_of_add_le (Nat.succ_le_iff.mpr hqr)
  have hpostPrev : S.E.t_GST ≤ S.a (r - 1) :=
    hpostQ.trans (Assembly.a_mono S hqPrev)
  have hhorPrev : S.a (r - 1) ≤ rho.horizon :=
    ((action_strictMono S).monotone (Nat.sub_le r 1)).trans hArhor
  have hlowR : S.hc.opening_slot q + 3 ≤
      S.hc.opening_slot r := hbaseOpen
  have hhighR : S.hc.opening_slot r < s :=
    (hcov.mem_range hboundary hhorOpen).2
  by_cases hqPrev' : q < r - 1
  · have hroundPrev : q + 1 ≤ r - 1 :=
      Nat.succ_le_iff.mpr hqPrev'
    have hslotQ2Prev : S.hc.opening_slot q + 2 ≤
        S.hc.opening_slot (r - 1) := by
      have hslotQ1 : S.hc.opening_slot q + 2 ≤
          S.hc.opening_slot (q + 1) := by
        simpa only [Protocol.HealConfig.opening_slot, Nat.add_mul,
          Nat.one_mul] using
          Nat.add_le_add_left S.hc.R_ge_two (q * S.hc.R)
      exact hslotQ1.trans
        (by simpa only [Protocol.HealConfig.opening_slot] using
          Nat.mul_le_mul_right S.hc.R hroundPrev)
    have hstartPrev : Protocol.support_cutoff S.E
        (S.hc.opening_slot q + 2) ≤ S.a (r - 1) := by
      exact (support_cutoff_le_confirmation_time S.E
        (S.hc.opening_slot q + 2)).trans
        ((w4cat_confirmation_mono S.E hslotQ2Prev).trans_eq
          (opening_confirmation_time_eq_action S (r - 1)).symm)
    have hcarrierFold := w4cat_actionCarriersAt S adm hfold
      (r := r - 1)
      (by simpa only [Nat.sub_add_cancel hrpos] using
        (hcov.mem_range hboundary hhorOpen).1)
      (by simpa only [Nat.sub_add_cancel hrpos] using
        (hcov.mem_range hboundary hhorOpen).2.le)
      hstartPrev hhorPrev
    simpa only [Nat.sub_add_cancel hrpos] using hcarrierFold
  · have hle : r - 1 ≤ q := Nat.le_of_not_gt hqPrev'
    have hqle : q ≤ r - 1 :=
      Nat.le_sub_of_add_le (Nat.succ_le_iff.mpr hqr)
    have hrEq : r = q + 1 := by
      have hpred : r - 1 = q := Nat.le_antisymm hle hqle
      calc
        r = (r - 1) + 1 := (Nat.sub_add_cancel hrpos).symm
        _ = q + 1 := by rw [hpred]
    have hbaseToOpening : Block.Preceq (F (S.hc.opening_slot q + 3))
        (F (S.hc.opening_slot r)) := by
      apply hfold.mono
        (S.hc.opening_slot q + 3) (S.hc.opening_slot r)
        (Nat.le_refl _) hbaseOpen (le_of_lt hhighR)
    have hcarrierQpin : ∀ u ∈ rho.honest,
        Block.Preceq (actionSGBlockAt S rho u q) D.erase := by
      exact (w4CarrierCeilingAtQPin_of_prepared S adm hfb)
        q D carrier hhandoff hbaseTiming hboundaryCore.carrierCeiling
    have hDopen : Block.Preceq D.erase (F (S.hc.opening_slot r)) := by
      rw [← hbaseEq]
      exact hbaseToOpening
    intro w hw
    simpa only [hrEq] using
      (Block.preceq_trans (hcarrierQpin w hw) hDopen)

set_option maxHeartbeats 800000 in
private theorem w4cat_batchInputs
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {q : Round} {D : NamedBlock V} {carrier : V} {M0 : Height}
    (hhandoff : HealedTwoSlotHandoffPrepared S rho q D.erase carrier)
    {s : Slot} {F : Slot → Block V} {FoldEnd : Block V}
    (hfold : MovingSlotFoldAtN S rho
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
      (S.hc.opening_slot q + 3) s F FoldEnd)
    (hbaseEq : F (S.hc.opening_slot q + 3) = D.erase)
    (hcov : MovingSlotFoldCovers S rho q
      (S.hc.opening_slot q + 3) s)
    (hboundaryCore : W4NamedHandoffBoundaryCore S rho q
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0 D)
    {r : Round}
    (hboundary : healingBoundaryTime S q <
      Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    (hbaseTiming :
      0 < S.hc.round_of (S.hc.opening_slot q + 3) ∧
      S.E.t_GST ≤ S.a
        (S.hc.round_of (S.hc.opening_slot q + 3) - 1) ∧
      Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤ rho.horizon)
    (hpostQ : S.E.t_GST ≤ S.a q) :
    ∃ d : Slot,
      d + 1 = S.hc.opening_slot r ∧ d < s ∧
      (∀ w ∈ rho.honest,
        NamedHonestVotesCone S rho d
          (fun X => Block.Preceq (actionSGBlockAt S rho w (r - 1)) X)) ∧
      (∀ v ∈ rho.honest,
        HonestHeadsAvailableBefore S rho d v
          (Protocol.support_cutoff S.E d)) := by
  have hArhor := w4cr_actionHorizon S hhor
  have hhorOpen : Protocol.confirmation_time S.E
      (S.hc.opening_slot r) ≤ rho.horizon := by
    simpa only [opening_confirmation_time_eq_action S r] using hArhor
  have hbaseOpen : S.hc.opening_slot q + 3 ≤
      S.hc.opening_slot r :=
    openingSlot_three_le_of_healingBoundary_lt_proposal S hboundary
  have hqr : q < r := w4cat_round_lt_of_opening_three S hbaseOpen
  have hrpos : 0 < r :=
    (Nat.zero_lt_succ q).trans_le (Nat.succ_le_of_lt hqr)
  have hqPrev : q ≤ r - 1 := by
    exact Nat.le_sub_of_add_le (Nat.succ_le_iff.mpr hqr)
  have hpostPrev : S.E.t_GST ≤ S.a (r - 1) :=
    hpostQ.trans (Assembly.a_mono S hqPrev)
  have hhorPrev : S.a (r - 1) ≤ rho.horizon :=
    ((action_strictMono S).monotone (Nat.sub_le r 1)).trans hArhor
  let d := S.hc.opening_slot r - 1
  have hdSucc : d + 1 = S.hc.opening_slot r := by
    dsimp only [d]
    exact Nat.succ_pred_eq_of_pos
      (Nat.mul_pos hrpos (Nat.zero_lt_of_lt S.hc.R_ge_two))
  have hdLow : S.hc.opening_slot q + 2 ≤ d := by
    have hslot : S.hc.opening_slot q + 3 ≤ d + 1 := by
      simpa only [hdSucc] using hbaseOpen
    exact w4cat_boundary_le_predecessor hslot rfl
  have hdHigh : d < s := by
    calc
      d < d + 1 := Nat.lt_succ_self d
      _ = S.hc.opening_slot r := hdSucc
      _ < s := (hcov.mem_range hboundary hhorOpen).2
  have hconeEnd : NamedHonestVotesCone S rho d
      (fun X => Block.Preceq (F (S.hc.opening_slot r)) X) := by
    by_cases hbaseD : S.hc.opening_slot q + 3 ≤ d
    · have hcone0 := hfold.windowCone d hbaseD hdHigh
      simpa only [hdSucc] using hcone0
    · obtain ⟨hdEq, hopenEq⟩ :=
        w4cat_boundary_predecessor_eq hbaseOpen hdSucc hbaseD
      have hq2Hor : Protocol.confirmation_time S.E
          (S.hc.opening_slot q + 2) ≤ rho.horizon := by
        rw [hopenEq] at hhorOpen
        exact (w4cat_confirmation_mono S.E (Nat.le_succ _)).trans hhorOpen
      simpa only [hdEq, hopenEq, hbaseEq] using
        hhandoff.honestVotesCone_two_after adm
          ((vote_time_le_confirmation_time S.E
            (S.hc.opening_slot q + 2)).trans hq2Hor)
  have hcarrierF := w4cat_carrierBelowAt S adm hfb hhandoff hfold hbaseEq
    hcov hboundaryCore hboundary hcarrier hhor hbaseTiming hpostQ
  have hcone : ∀ w ∈ rho.honest,
      NamedHonestVotesCone S rho d
        (fun X => Block.Preceq (actionSGBlockAt S rho w (r - 1)) X) := by
    intro w hw x hx hxc
    obtain ⟨X, hFX, hXrun, hXemit⟩ := hconeEnd x hx hxc
    exact ⟨X, Block.preceq_trans (hcarrierF w hw) hFX, hXrun, hXemit⟩
  have hdata := w4cat_endpointMemAt S adm hcom hfb hhandoff hfold hbaseEq hcov
    hboundary hcarrier hhor hpostQ
  refine ⟨d, hdSucc, hdHigh, hcone, ?_⟩
  intro v hv
  exact (hdata v hv).1



set_option maxHeartbeats 4000000 in
private theorem w4cat_batchComplete_of_inputs
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {r : Round} (hrpos : 0 < r)
    (hpost : S.E.t_GST ≤ S.a (r - 1))
    (hcut : S.hc.Γ_neg1 S.E.Δ r ≤ rho.horizon)
    (hcone : ∀ w ∈ rho.honest,
      NamedHonestVotesCone S rho (S.hc.opening_slot r - 1)
        (fun X => Block.Preceq (actionSGBlockAt S rho w (r - 1)) X))
    (havail : ∀ v ∈ rho.honest,
      HonestHeadsAvailableBefore S rho (S.hc.opening_slot r - 1) v
        (Protocol.support_cutoff S.E (S.hc.opening_slot r - 1))) :
    ∀ v ∈ rho.honest, ∀ w ∈ rho.honest,
      CanonicalBatchVoteAt S rho r
        (actionStoreAt S rho v r).toHealing.gradeView w := by
  exact w4cr_batchComplete_field_of_cone S adm hcom hrpos hpost hcut
    hcone havail

set_option maxHeartbeats 4000000 in
private theorem w4cat_batchAt
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {q : Round} {D : NamedBlock V} {carrier : V} {M0 : Height}
    (hhandoff : HealedTwoSlotHandoffPrepared S rho q D.erase carrier)
    {s : Slot} {F : Slot → Block V} {FoldEnd : Block V}
    (hfold : MovingSlotFoldAtN S rho
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
      (S.hc.opening_slot q + 3) s F FoldEnd)
    (hbaseEq : F (S.hc.opening_slot q + 3) = D.erase)
    (hcov : MovingSlotFoldCovers S rho q
      (S.hc.opening_slot q + 3) s)
    (hboundaryCore : W4NamedHandoffBoundaryCore S rho q
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0 D)
    {r : Round}
    (hboundary : healingBoundaryTime S q <
      Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon)
    (hbaseTiming :
      0 < S.hc.round_of (S.hc.opening_slot q + 3) ∧
      S.E.t_GST ≤ S.a
        (S.hc.round_of (S.hc.opening_slot q + 3) - 1) ∧
      Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤ rho.horizon)
    (hpostQ : S.E.t_GST ≤ S.a q) :
    ∀ v ∈ rho.honest, ∀ w ∈ rho.honest,
      CanonicalBatchVoteAt S rho r
        (actionStoreAt S rho v r).toHealing.gradeView w := by
  have hinputs : ∃ d : Slot,
      d + 1 = S.hc.opening_slot r ∧ d < s ∧
      (∀ w ∈ rho.honest,
        NamedHonestVotesCone S rho d
          (fun X => Block.Preceq (actionSGBlockAt S rho w (r - 1)) X)) ∧
      (∀ v ∈ rho.honest,
        HonestHeadsAvailableBefore S rho d v
          (Protocol.support_cutoff S.E d)) :=
    w4cat_batchInputs (S := S) (rho := rho) (q := q) (D := D)
      (carrier := carrier) (M0 := M0) (s := s) (F := F)
      (FoldEnd := FoldEnd) (r := r) adm hcom hfb hhandoff hfold hbaseEq hcov
      hboundaryCore hboundary hcarrier hhor hbaseTiming hpostQ
  obtain ⟨d, hdSucc, hdHigh, hcone, havail⟩ := hinputs
  have hArhor := w4cr_actionHorizon S hhor
  have hhorOpen : Protocol.confirmation_time S.E
      (S.hc.opening_slot r) ≤ rho.horizon := by
    simpa only [opening_confirmation_time_eq_action S r] using hArhor
  have hbaseOpen : S.hc.opening_slot q + 3 ≤
      S.hc.opening_slot r :=
    openingSlot_three_le_of_healingBoundary_lt_proposal S hboundary
  have hqr : q < r := w4cat_round_lt_of_opening_three S hbaseOpen
  have hrpos : 0 < r :=
    (Nat.zero_lt_succ q).trans_le (Nat.succ_le_of_lt hqr)
  have hqPrev : q ≤ r - 1 :=
    Nat.le_sub_of_add_le (Nat.succ_le_iff.mpr hqr)
  have hpostPrev : S.E.t_GST ≤ S.a (r - 1) :=
    hpostQ.trans (Assembly.a_mono S hqPrev)
  have hcut : S.hc.Γ_neg1 S.E.Δ r ≤ rho.horizon := by
    have hstep : S.hc.Γ_neg1 S.E.Δ (r - 1 + 1) ≤ rho.horizon :=
      (next_Γ_neg1_lt_action S (r - 1)).le.trans
        (by simpa only [Nat.sub_add_cancel hrpos] using hArhor)
    simpa only [Nat.sub_add_cancel hrpos] using hstep
  have hdeq : d = S.hc.opening_slot r - 1 := by
    have hopenPos : 0 < S.hc.opening_slot r := by
      exact Nat.mul_pos
        hrpos
        (Nat.zero_lt_of_lt S.hc.R_ge_two)
    apply Nat.succ.inj
    exact hdSucc.trans (Nat.sub_add_cancel hopenPos).symm
  exact w4cat_batchComplete_of_inputs S adm hcom hrpos hpostPrev hcut
    (by simpa only [hdeq] using hcone)
    (by simpa only [hdeq] using havail)

private theorem w4cat_proposedParent_mem_filtered
    (S : Setup V) {rho : Run V} (adm : Admissible S rho) (d : Slot) :
    Protocol.proposedParent S rho d ∈
      Protocol.get_filtered_block_tree
        (Protocol.proposerDutyStore S rho d).toHealing.toFG := by
  let p := S.E.proposer d
  let t := Protocol.proposal_time S.E d
  let pre := rho.storeBeforeTime S p t
  let duty := Protocol.proposerDutyStore S rho d
  have hrootPre : Protocol.get_fg_root pre.toHealing.toFG ∈
      Protocol.get_filtered_block_tree pre.toHealing.toFG := by
    simpa only [pre, Protocol.NamedStore.toHealing] using
      named_fgRoot_mem_filtered_stateBeforeTime S rho t p
  have hrootDuty : Protocol.get_fg_root duty.toHealing.toFG ∈
      Protocol.get_filtered_block_tree duty.toHealing.toFG := by
    simpa only [duty, Protocol.proposerDutyStore,
      Proofs.Optimistic.tickStore, pre, t, p] using hrootPre
  let votes := Protocol.proposer_view duty.toHealing.toFG.toSG.toGoldfishStore duty.s
  let support := Protocol.proposer_support_view duty.toHealing.toFG.toSG.toGoldfishStore duty.s
  have hhead := getHead_mem_filtered_of_fgRoot_mem
    S.E S.hc duty.toHealing votes.toFinset support.toFinset
      (duty.s - 1) hrootDuty
  simpa only [Protocol.proposedParent, duty, votes, support] using hhead

/-! ## Public carrier export -/

set_option maxHeartbeats 1200000 in
theorem w4_carrierAtField_of_namedFold
    (S : Setup V) {rho : Run V}
    {rGST gap q : Round} {D : NamedBlock V}
    {carrier : V} {M0 : Height}
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    (hqlo : rGST ≤ q)
    (_hqhi : q ≤ rGST + w4UniformHandoffLag S gap delayExtra)
    (hlate : fgSafetyProgressDeadline S rho rGST gap
      delayExtra + 3 ≤ q)
    (hhandoff : HealedTwoSlotHandoffPrepared S rho q D.erase carrier)
    (hboundary : W4NamedHandoffBoundaryCore S rho q
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0 D)
    (hbaseTiming :
      0 < S.hc.round_of (S.hc.opening_slot q + 3) ∧
      S.E.t_GST ≤ S.a
        (S.hc.round_of (S.hc.opening_slot q + 3) - 1) ∧
      Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤ rho.horizon)
    (hfoldAt : W4SelectedNamedFoldAtEverySlot S rho q M0 D) :
    MovingChainAtCarrierFrom S rho q := by
  have hpostQ : S.E.t_GST ≤ S.a q :=
    hpost.trans (Assembly.a_mono S hqlo)
  obtain ⟨s, F, FoldEnd, hfold, hbaseEq, hcov⟩ :=
    w4cat_foldCoverN (S := S) (rho := rho) (q := q) (D := D) (M0 := M0)
      hbaseTiming hfoldAt
  intro r hafter hcarrier hhor
  have hbaseOpen : S.hc.opening_slot q + 3 ≤
      S.hc.opening_slot r :=
    openingSlot_three_le_of_healingBoundary_lt_proposal S hafter
  have hqr : q < r := w4cat_round_lt_of_opening_three S hbaseOpen
  have hrpos : 0 < r :=
    (Nat.zero_lt_succ q).trans_le (Nat.succ_le_of_lt hqr)
  have hrLate : fgSafetyProgressDeadline S rho rGST gap
      delayExtra + 3 ≤ r :=
    hlate.trans hqr.le
  have hArhor := w4cr_actionHorizon S hhor
  have hhorOpen : Protocol.confirmation_time S.E
      (S.hc.opening_slot r) ≤ rho.horizon := by
    simpa only [opening_confirmation_time_eq_action S r] using hArhor
  obtain ⟨hlowR, hhighR⟩ := hcov.mem_range hafter hhorOpen
  have hP : ∃ P : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r) = some P :=
    proposedBlockAt_isSome S rho (S.hc.opening_slot r)
  obtain ⟨P, hP⟩ := hP
  have hPrun : RunBlock S rho P :=
    w4cr_openingProposal_runBlock S adm hrpos hcarrier hhor hP
  have hsepP : ∀ k : Round, S.a k < S.a r →
      S.a k < Protocol.proposal_time S.E (S.hc.opening_slot r) := by
    intro k hk
    exact w4cat_action_lt_openingProposal S
      ((action_strictMono S).lt_iff_lt.mp hk)
  have hbandP : ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v (S.a r)).core.h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg P).h := by
    exact w4cat_bandAtProposalN S adm hbelow hfold hlowR
      (le_of_lt hhighR) hcarrier.1 hP hPrun hsepP
  obtain ⟨P1, hP1⟩ :=
    proposedBlockAt_isSome S rho (S.hc.opening_slot r + 1)
  have hhor1 : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 1) ≤ rho.horizon := by
    exact (w4cat_confirmation_mono S.E (Nat.le_succ _)).trans hhor
  have hboundary1 : healingBoundaryTime S q <
      Protocol.proposal_time S.E (S.hc.opening_slot r + 1) :=
    hafter.trans_le (Protocol.proposal_time_mono S.E (Nat.le_succ _))
  obtain ⟨hlow1, hhigh1⟩ := hcov.mem_range hboundary1 hhor1
  have hP1run : RunBlock S rho P1 :=
    proposedBlock_runBlock S adm (Nat.succ_pos _) hcarrier.2.1
      ((w4cr_proposalSucc_le_action S r).trans hArhor) hP1
  have hsepP1 : ∀ k : Round, S.a k < S.a r →
      S.a k < Protocol.proposal_time S.E (S.hc.opening_slot r + 1) := by
    intro k hk
    have hkr : k < r := (action_strictMono S).lt_iff_lt.mp hk
    exact (w4cat_action_lt_openingProposal S hkr).trans_le
      (Protocol.proposal_time_mono S.E (Nat.le_succ _))
  have hbandP1 : ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v (S.a r)).core.h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg P1).h := by
    exact w4cat_bandAtProposalN S adm hbelow hfold hlow1
      (le_of_lt hhigh1) hcarrier.2.1 hP1 hP1run hsepP1
  have hcarriersF := w4cat_carrierBelowAt S adm hbelow hhandoff hfold
    hbaseEq hcov hboundary hafter hcarrier hhor hbaseTiming hpostQ
  have hbatch := w4cat_batchAt S adm hcom hbelow hhandoff hfold hbaseEq hcov
    hboundary hafter hcarrier hhor hbaseTiming hpostQ
  have hdata := w4cat_endpointMemAt S adm hcom hbelow hhandoff hfold
    hbaseEq hcov hafter hcarrier hhor hpostQ
  have hendpoint := w4cat_endpointRunAt S hfold hlowR (le_of_lt hhighR)
  obtain ⟨E, hE, hErun⟩ := hendpoint
  have hbandE : ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v (S.a r)).core.h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg E).h := by
    intro v hv
    exact w4cat_frontierAt S adm hbelow hfold hlowR
      (le_of_lt hhighR) hv hE hErun
  have hmemE : ∀ v ∈ rho.honest,
      E ∈ (rho.storeBeforeTime S v (S.a r)).bodies := by
    intro v hv
    apply w4cr_mem_bodies_of_mem_T S adm hv hErun
    simpa only [hE] using (hdata v hv).2
  have hcase := movingChainRoundFloor_or_lost_of_carrierCeiling S adm hcom
    (fun v hv => hcarriersF v hv)
    (fun v hv => ⟨E, hmemE v hv, by
      rw [hE]
      exact Block.preceq_self _, hbandE v hv⟩)
  have hcarriersP := w4cr_carriersBelowEndpoint S adm hcom hbelow hrec
    hdelay hpost hrLate hcarrier hhor hP
  have hanchorsP := w4cr_anchorsBelowEndpoint S adm hcom hbelow hrec
    hdelay hpost hrLate hcarrier hhor hP
  have hanchorsCurrentP := w4cr_anchorsBelowEndpoint_current S adm hcom hbelow hrec
    hdelay hpost hrLate hcarrier hhor hP
  have hheightP := w4cr_heightHistory_of_pins S adm hcom hbelow hrec hdelay
    hpost hlate hrLate hcarrier hhor hP
  have htargetP := w4cr_targetHistory_of_heightHistory S adm hheightP
  have htimeoutP := w4cr_timeoutHistory_of_heightHistory S adm hheightP
  have hplusOneP := w4cr_plusOneCandidate_of_band S adm hcom hbelow hrec
    hdelay hpost hrLate hcarrier hhor
    (fun P1' hP1' => by
      have hEq : P1' = P1 := Option.some.inj (hP1'.symm.trans hP1)
      simpa only [hEq] using hbandP1)
  have hopeningP : ∀ P' : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r) = some P' →
      Block.Preceq P.erase P'.erase := by
    intro P' hP'
    have hEq : P' = P := Option.some.inj (hP'.symm.trans hP)
    subst P'
    exact Block.preceq_self _
  rcases hcase with hlost | ⟨C, hfields⟩
  · have hparentFiltered := w4cat_proposedParent_mem_filtered S adm
        (S.hc.opening_slot r + 2)
    refine ⟨Protocol.proposedParent S rho
      (S.hc.opening_slot r + 2), P.erase, ?_⟩
    refine
      { endpointBelowOpening := hopeningP
        carriersBelowEndpoint := hcarriersP
        batchComplete := hbatch
        roundFloor := Or.inl hlost
        anchorsBelowEndpoint := hanchorsCurrentP
        namedAnchorsBelowEndpoint := hanchorsP
        floorActiveAtPlusTwoProposal := Or.inl hparentFiltered
        plusOneCandidate := hplusOneP
        heightHistory := ?_
        targetHistory := ?_
        timeoutHistory := ?_ }
    · intro P' hP'
      have hEq : P' = P := Option.some.inj (hP'.symm.trans hP)
      simpa only [hEq] using hheightP
    · intro P' hP'
      have hEq : P' = P := Option.some.inj (hP'.symm.trans hP)
      simpa only [hEq] using htargetP
    · intro P' hP'
      have hEq : P' = P := Option.some.inj (hP'.symm.trans hP)
      simpa only [hEq] using htimeoutP
  · have hactive :=
      w4cat_roundFloor_mem_filtered_or_prec_rootN_of_bandCover
        S adm hbelow hfold hcov hafter hcarrier hhor hcarriersF hfields
    refine ⟨C, P.erase, ?_⟩
    refine
      { endpointBelowOpening := hopeningP
        carriersBelowEndpoint := hcarriersP
        batchComplete := hbatch
        roundFloor := Or.inr hfields
        anchorsBelowEndpoint := hanchorsCurrentP
        namedAnchorsBelowEndpoint := hanchorsP
        floorActiveAtPlusTwoProposal := hactive
        plusOneCandidate := hplusOneP
        heightHistory := ?_
        targetHistory := ?_
        timeoutHistory := ?_ }
    · intro P' hP'
      have hEq : P' = P := Option.some.inj (hP'.symm.trans hP)
      simpa only [hEq] using hheightP
    · intro P' hP'
      have hEq : P' = P := Option.some.inj (hP'.symm.trans hP)
      simpa only [hEq] using htargetP
    · intro P' hP'
      have hEq : P' = P := Option.some.inj (hP'.symm.trans hP)
      simpa only [hEq] using htimeoutP

#print axioms w4_carrierAtField_of_namedFold

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
