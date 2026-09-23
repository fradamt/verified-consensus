module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainNextEntry
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.MovingChainCeiling

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
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Additive lower-layer shape of `W4ByzantineVoteAnchorPin`
(`W4BaseFoldRun.lean`). The duplicate shape keeps this leaf below the
dispatcher; the two definitions reduce to the same proposition at the
consumer, without importing the owning module back into this leaf. -/
def w4cx_ByzantineVoteAnchorPin (S : Setup V) (rho : Run V) : Prop :=
  ∀ {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V} {r : Round},
    MovingSlotPreEntryN S rho t1 M0 (c + 1) Prev End →
    S.hc.round_of (c + 1) = r + 1 →
    (t1 ≤ S.a r ∨ ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) Prev) →
    S.E.t_GST ≤ S.a r →
    S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon →
    S.E.t_GST ≤ Protocol.vote_time S.E c →
    Protocol.support_cutoff S.E c ≤ rho.horizon →
    Protocol.vote_time S.E (c + 1) ≤ rho.horizon →
    ∀ w ∈ rho.honest,
      Block.Preceq (voterAnchorAt S rho w (c + 1)) Prev

/-! The two anchor twins below are additive. The first copies the core body
with the only use of the false confirmation-time premise removed. The second
uses the vote-time fact already present in the cutoff branch, then applies the
prepared previous-carrier anchor lemma. -/

/-- Named twin of
 `movingSlotPreEntryN_voterAnchorAt_preceq_prev_core`
 (`MovingChainSupporterRun.lean`). The original uses
 `confirmation_time c ≤ horizon` only to derive
 `vote_time (c + 1) ≤ horizon`; branch 2 already supplies the latter.
-/
theorem w4cx_movingSlotPreEntryN_voterAnchorAt_preceq_prev_of_voteHorizon
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hstartTime : t1 ≤ Protocol.proposal_time S.E (c + 1))
    (hprevEndpoint : ∃ EndAt : Nat → Block V,
      MovingFrontierChainStateN S rho t1 M0 (strictEventIndex rho t1)
          (inclusiveEventIndex rho
            (Protocol.proposal_time S.E (c + 1))) EndAt ∧
        EndAt (strictEventIndex rho
          (Protocol.proposal_time S.E (c + 1))) = Prev ∧
        EndAt (inclusiveEventIndex rho
          (Protocol.proposal_time S.E (c + 1))) = End)
    {r : Round}
    (hround : S.hc.round_of (c + 1) = r + 1)
    (ht1 : t1 ≤ S.a r)
    (hpostAction : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hvoteHor : Protocol.vote_time S.E (c + 1) ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) :
    Block.Preceq (voterAnchorAt S rho w (c + 1)) Prev := by
  obtain ⟨EndAt, hhistory, hprev, _hEnd⟩ := hprevEndpoint
  set k := strictEventIndex rho (Protocol.proposal_time S.E (c + 1)) with hk
  have hpre : MovingFrontierChainStateN S rho t1 M0
      (strictEventIndex rho t1) k EndAt :=
    hhistory.prefix (strictEventIndex_mono rho hstartTime)
      (strictEventIndex_le_inclusiveEventIndex rho _)
  obtain ⟨E, hE, hErun⟩ := hpre.endpointRun k hpre.start_le (Nat.le_refl k)
  have hrootRaw : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w
          (Protocol.vote_time S.E (c + 1))).toHealing.toFG) (EndAt k) := by
    rw [← hE]
    exact hpre.voteRoot_preceq_endpointAtCursor_named S adm hfb
      (Nat.le_refl k) hw hstartTime hE hErun
  have hroot : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (c + 1)).toHealing.toFG)
      (EndAt k) := by
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hrootRaw
  have hread : S.hc.Γ_0 S.E.Δ (r + 1) ≤ Protocol.vote_time S.E (c + 1) :=
    Γ_0_le_vote_time_of_round_eq S hround
  have hbefore : S.a r < Protocol.vote_time S.E (c + 1) :=
    (Int.lt_add_of_pos_right (S.a r) S.E.Δ_pos).trans_le
      ((action_add_delta_le_next_Γ_neg1 S r).trans
        ((le_of_lt (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos (r + 1))).trans hread))
  have hactionHor : S.a r ≤ rho.horizon :=
    (le_of_lt (Int.lt_add_of_pos_right (S.a r) S.E.Δ_pos)).trans
      ((action_add_delta_le_next_Γ_neg1 S r).trans hcut)
  have hupper := hpre.previousActionCarriersPreceqAtRead S adm ht1 hactionHor hpostAction
    (Protocol.action_time_lt_proposal_of_lt_vote S hbefore)
    (Nat.le_refl k)
  rw [← hprev]
  exact voterAnchorAt_preceq_of_previousCarriers S adm hfb hround hpostAction
    hcut hvoteHor (by simpa only [hE] using hupper) hw (by simpa only [hE] using hroot)

#print axioms w4cx_movingSlotPreEntryN_voterAnchorAt_preceq_prev_of_voteHorizon

/-- Named-anchor twin of the ceiling-side pre-entry read. The branch already
 carries the entered vote horizon, so the prepared previous-carrier theorem
 is the exact named replacement for the default ceiling read.
-/
theorem w4cx_movingSlotPreEntryN_voterAnchorAt_preceq_prev_of_ceiling
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hentry : MovingSlotPreEntryN S rho t1 M0 (c + 1) Prev End)
    {r : Round}
    (hround : S.hc.round_of (c + 1) = r + 1)
    (hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) Prev)
    (hpostAction : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hslotHor : Protocol.support_cutoff S.E c ≤ rho.horizon)
    (hvoteHor : Protocol.vote_time S.E (c + 1) ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) :
    Block.Preceq (voterAnchorAt S rho w (c + 1)) Prev := by
  obtain ⟨EndAt, hhistory, hprev, _hEnd⟩ := hentry.prevEndpoint
  set k := strictEventIndex rho (Protocol.proposal_time S.E (c + 1)) with hk
  have hpre : MovingFrontierChainStateN S rho t1 M0
      (strictEventIndex rho t1) k EndAt :=
    hhistory.prefix (strictEventIndex_mono rho hentry.startTime)
      (strictEventIndex_le_inclusiveEventIndex rho _)
  obtain ⟨E0, hE0, hE0run⟩ :=
    hpre.endpointRun k hpre.start_le (Nat.le_refl k)
  have hrootRaw : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w
          (Protocol.vote_time S.E (c + 1))).core.toHealing.toFG) E0.erase :=
    hpre.voteRoot_preceq_endpointAtCursor_named S adm hfb
      (Nat.le_refl k) hw hentry.startTime hE0 hE0run
  have hroot : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (c + 1)).toHealing.toFG)
      E0.erase := by
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hrootRaw
  have hupperK : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) E0.erase := by
    intro u hu
    simpa only [hE0, hprev] using hupper u hu
  have hanchor : Block.Preceq
      (voterAnchorAt S rho w (c + 1)) E0.erase :=
    voterAnchorAt_preceq_of_previousCarriers S adm hfb hround
      hpostAction hcut hvoteHor hupperK hw hroot
  have hanchorPrev : Block.Preceq
      (voterAnchorAt S rho w (c + 1)) Prev := by
    refine Block.preceq_trans hanchor ?_
    simpa only [hE0, hprev] using (Block.preceq_self Prev)
  exact hanchorPrev

#print axioms w4cx_movingSlotPreEntryN_voterAnchorAt_preceq_prev_of_ceiling

/-! The branch-2 Byzantine pin follows by a schedule split over the two
anchor twins. The schedule disjunction itself remains the exact output shape
of `w4_proposalSchedule_hybrid`; no default-contract object is introduced. -/

theorem w4cx_byzantineVoteAnchorPin_of_preentry
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest) :
    w4cx_ByzantineVoteAnchorPin S rho := by
  intro t1 M0 c Prev End r hpre hround hmode hpostAction hcut hpostVote
    hslotHor hvoteHor w hw
  rcases hmode with ht1 | hupper
  · exact w4cx_movingSlotPreEntryN_voterAnchorAt_preceq_prev_of_voteHorizon
      S adm hfb hpre.startTime hpre.prevEndpoint hround ht1 hpostAction hcut
      hvoteHor hw
  · exact w4cx_movingSlotPreEntryN_voterAnchorAt_preceq_prev_of_ceiling
      S adm hcom hfb hpre hround hupper hpostAction hcut hpostVote hslotHor
      hvoteHor hw

#print axioms w4cx_byzantineVoteAnchorPin_of_preentry

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
