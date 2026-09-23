module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.W4NamedCeilingStep
public import DecoupledConsensusProofs.Protocol.Schedule.W4NamedHonestBoundaryFold

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# The honest named boundary fold from stage-0 data

The older honest boundary theorem leaves the parent and the confirmation
compatibility as call-site facts. At the selected boundary these facts are
already available before an entered moving-slot state exists. This leaf
copies the boundary parent route: keep the named endpoint through the strict
proposal cursor, then use the named ceiling parent theorem. The prepared
confirmation compatibility is read from the resulting pre-entry.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.NamedRecoveryRead
open Protocol Proofs.HealingLemmas
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

private theorem w4nbs_proposal_parent_preceq_proposedBlockAt
    (S : Setup V) (rho : Run V) (s : Slot) {P : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P) :
    Block.Preceq (proposedParent S rho s) P.erase := by
  obtain ⟨p, hp, hparent⟩ := proposedBlockAt_parent S rho s hP
  rw [← hparent]
  cases P with
  | genesis => simp only [NamedBlock.parent?, reduceCtorEq] at hp
  | node parent slot root votes support rows proposer =>
      simp only [NamedBlock.parent?, Option.some.injEq] at hp
      subst hp
      apply Protocol.preceq_of_parent?
      rfl


private theorem w4nbs_action_time_mono
    (S : Setup V) {a b : Round} (hab : a ≤ b) :
    S.a a ≤ S.a b := by
  have hopen : S.hc.opening_slot a ≤ S.hc.opening_slot b :=
    Nat.mul_le_mul_right S.hc.R hab
  have hnormal (r : Round) : S.a r =
      (4 * ((S.hc.opening_slot r : Slot) : Time) + 6) * S.E.Δ := by
    unfold Setup.a Protocol.HealConfig.a slotStart
    ring
  rw [hnormal, hnormal]
  apply Int.mul_le_mul_of_nonneg_right _ S.E.Δ_pos.le
  exact Int.add_le_add_right (by exact_mod_cast Nat.mul_le_mul_left 4 hopen) 6

private theorem w4nbs_action_le_proposal_plus_two (S : Setup V) (q : Round) :
    S.a q ≤ Protocol.proposal_time S.E (S.hc.opening_slot q + 2) := by
  have haction : S.a q =
      (4 * ((S.hc.opening_slot q : Slot) : Time) + 6) * S.E.Δ := by
    unfold Setup.a Protocol.HealConfig.a slotStart
    ring
  have hproposal : Protocol.proposal_time S.E (S.hc.opening_slot q + 2) =
      (4 * ((S.hc.opening_slot q + 2 : Slot) : Time) + 0) * S.E.Δ := by
    unfold Protocol.proposal_time Env.t slotStart
    ring
  rw [haction, hproposal]
  apply Int.mul_le_mul_of_nonneg_right _ S.E.Δ_pos.le
  push_cast
  omega

private theorem w4nbs_confirmation_time_mono
    (E : Env V) {a b : Slot} (hab : a ≤ b) :
    Protocol.confirmation_time E a ≤ Protocol.confirmation_time E b :=
  Int.add_le_add_right (Protocol.proposal_time_mono E hab) _

private theorem w4nbs_inclusive_le_strict_of_lt
    (rho : Run V) {t0 t1 : Time} (hlt : t0 < t1) :
    inclusiveEventIndex rho t0 ≤ strictEventIndex rho t1 := by
  unfold inclusiveEventIndex strictEventIndex
  exact (List.monotone_filter_right rho.events (fun e he => by
    simp only [decide_eq_true_eq] at he ⊢
    exact lt_of_le_of_lt he hlt)).length_le

private theorem w4nbs_eventIndex_unique
    {rho : Run V} (hnodup : rho.events.Nodup) {i j : Nat} {e : Event V}
    (hi : rho.events[i]? = some e) (hj : rho.events[j]? = some e) :
    i = j := by
  obtain ⟨hiLen, hie⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjLen, hje⟩ := List.getElem?_eq_some_iff.mp hj
  have hfin : (⟨i, hiLen⟩ : Fin rho.events.length) =
      ⟨j, hjLen⟩ :=
    (List.nodup_iff_injective_getElem.mp hnodup) (by simp only [hie, hje])
  simpa using congrArg Fin.val hfin

private theorem w4nbs_round_of_opening_add_three_le_succ
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

private theorem w4nbs_parent_of_boundary
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {q : Round} {D : NamedBlock V} {carrier : V} {M0 : Height}
    (hhandoff : HealedTwoSlotHandoffPrepared S rho q D.erase carrier)
    (hboundary : W4NamedHandoffBoundaryCore S rho q
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0 D)
    (hbaseTiming :
      0 < S.hc.round_of (S.hc.opening_slot q + 3) ∧
      S.E.t_GST ≤ S.a
        (S.hc.round_of (S.hc.opening_slot q + 3) - 1) ∧
      Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤
        rho.horizon)
    (hprop : S.E.proposer (S.hc.opening_slot q + 3) ∈ rho.honest) :
    Block.Preceq D.erase
      (proposedParent S rho (S.hc.opening_slot q + 3)) := by
  let o := S.hc.opening_slot q
  let R0 := S.hc.round_of (o + 3)
  let r0 := R0 - 1
  have hR0pos : 0 < R0 := by
    simpa only [R0, o] using hbaseTiming.1
  have hround : S.hc.round_of (o + 3) = r0 + 1 := by
    simpa only [R0, r0] using
      (Nat.sub_add_cancel hR0pos).symm
  have hconfHor : Protocol.confirmation_time S.E (o + 1) ≤ rho.horizon := by
    have hslots : o + 1 ≤ o + 3 := by
      exact Nat.add_le_add_left (by decide : (1 : Nat) ≤ 3) o
    exact (Int.add_le_add_right
      (Protocol.proposal_time_mono S.E hslots) _).trans
      (by simpa only [o] using hbaseTiming.2.2)
  obtain ⟨EndAt, hstate, hconstAll⟩ :=
    w4NamedBoundaryHistoryN_toFreeze S adm hhandoff hboundary hconfHor
  have hconst : EndAt
      (inclusiveEventIndex rho (Protocol.view_freeze S.E (o + 2))) =
        D.erase := by
    exact hconstAll _ (Nat.le_refl _)
  have hfreezeStrict :
      inclusiveEventIndex rho (Protocol.view_freeze S.E (o + 2)) ≤
        strictEventIndex rho (Protocol.proposal_time S.E (o + 3)) := by
    apply w4nbs_inclusive_le_strict_of_lt
    have hfreeze : Protocol.view_freeze S.E (o + 2) =
        (4 * ((o + 2 : Slot) : Time) + 3) * S.E.Δ := by
      unfold Protocol.view_freeze Env.t slotStart
      ring
    have hproposal : Protocol.proposal_time S.E (o + 3) =
        (4 * ((o + 3 : Slot) : Time) + 0) * S.E.Δ := by
      unfold Protocol.proposal_time Env.t slotStart
      ring
    rw [hfreeze, hproposal]
    apply Int.mul_lt_mul_of_pos_right _ S.E.Δ_pos
    push_cast
    omega
  have hproposal : ∃ P : NamedBlock V,
      proposedBlockAt S rho (o + 3) = some P :=
    proposedBlockAt_isSome S rho (o + 3)
  obtain ⟨P, hP⟩ := hproposal
  have hPRun : RunBlock S rho P :=
    proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
      (o + 3) (Nat.succ_pos _) hprop
      ((Protocol.proposal_time_lt_vote_time S.E _).le.trans
        ((Protocol.vote_time_le_confirmation_time S.E _).trans
          (by simpa only [o] using hbaseTiming.2.2))) hP
  obtain ⟨_hBslot, hpemit⟩ := Proofs.Optimistic.proposalTick S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (o + 3)
      (Nat.succ_pos _) hprop
      ((Protocol.proposal_time_lt_vote_time S.E _).le.trans
        ((Protocol.vote_time_le_confirmation_time S.E _).trans
          (by simpa only [o] using hbaseTiming.2.2))) hP
  obtain ⟨p, hpevent, _⟩ := hpemit
  have hstateStrict :
      ∃ EndAt' : Nat → Block V,
        (∀ j, j ≤ inclusiveEventIndex rho
            (Protocol.view_freeze S.E (o + 2)) → EndAt' j = EndAt j) ∧
        (∀ j, inclusiveEventIndex rho
            (Protocol.view_freeze S.E (o + 2)) < j →
          EndAt' j = D.erase) ∧
        MovingFrontierChainStateN S rho
          (Protocol.support_cutoff S.E (o + 2)) M0
          (strictEventIndex rho (Protocol.support_cutoff S.E (o + 2)))
          (strictEventIndex rho (Protocol.proposal_time S.E (o + 3))) EndAt' := by
    refine MovingFrontierChainStateN.through_constantEndpoint_named_public S
      hstate (by rw [hconst]; exact Block.preceq_self _) 
      ⟨D, rfl, hboundary.run⟩ hfreezeStrict ?_
    intro j hj hjm
    refine movingSlotWindowTail_eventFacts_named_public S adm
      (Block.preceq_self D.erase) ?_ hj
      (hjm.trans_le (strictEventIndex_le_inclusiveEventIndex rho _))
    intro u hu hev heq
    obtain hstrict : strictEventIndex rho
        (Protocol.proposal_time S.E (o + 3)) ≤ p := by
      by_contra hnot
      have htrue := Proofs.Optimistic.filter_true_of_index_lt S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed _
        (Proofs.Optimistic.downward_lt (Protocol.proposal_time S.E (o + 3)))
        (by simpa only [strictEventIndex] using Nat.lt_of_not_ge hnot) hpevent
      simp only [decide_eq_true_eq, Event.time] at htrue
      exact lt_irrefl _ htrue
    have hjp : j < p := lt_of_lt_of_le hjm hstrict
    have heq' : S.E.proposer (o + 3) = (S.node u).val_index := by
      simpa only [o, Nat.add_assoc] using heq
    have hev' : rho.events[j]? = some
        (Event.tick (S.E.proposer (o + 3))
          (Protocol.proposal_time S.E (o + 3))) := by
      simpa only [heq', S.node_val_index u, o, Nat.add_assoc] using hev
    exact absurd (w4nbs_eventIndex_unique adm.nodup hev' hpevent)
      (Nat.ne_of_lt hjp)
  obtain ⟨EndAt', _hlow, hhigh, hstate'⟩ := hstateStrict
  have hEndStrict :
      EndAt' (strictEventIndex rho (Protocol.proposal_time S.E (o + 3))) =
        D.erase := by
    rcases Nat.eq_or_lt_of_le hfreezeStrict with heq | hlt
    · rw [← heq, _hlow _ (Nat.le_refl _), hconst]
    · exact hhigh _ hlt
  have hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r0) D.erase := by
    intro u hu
    simpa only [o, R0, r0] using hboundary.carrierCeiling r0 hround u hu
  have hgammaConf : S.hc.Γ_neg1 S.E.Δ R0 ≤
      Protocol.confirmation_time S.E (o + 3) := by
    have hgamma : S.hc.Γ_neg1 S.E.Δ R0 =
        (4 * ((S.hc.opening_slot R0 : Slot) : Time) - 1) * S.E.Δ := by
      unfold Protocol.HealConfig.Γ_neg1 slotStart
      ring
    have hconf : Protocol.confirmation_time S.E (o + 3) =
        (4 * ((o + 3 : Slot) : Time) + 6) * S.E.Δ := by
      unfold Protocol.confirmation_time Env.t slotStart
      ring
    rw [hgamma, hconf]
    apply Int.mul_le_mul_of_nonneg_right _ S.E.Δ_pos.le
    have hopen : S.hc.opening_slot R0 ≤ o + 3 := by
      dsimp only [R0]
      simp only [Protocol.HealConfig.opening_slot,
        Protocol.HealConfig.round_of]
      exact Nat.div_mul_le_self (o + 3) S.hc.R
    have hcast : ((S.hc.opening_slot R0 : Slot) : Time) ≤
        ((o + 3 : Slot) : Time) := by
      exact_mod_cast hopen
    push_cast at hcast ⊢
    linarith
  have hcut : S.hc.Γ_neg1 S.E.Δ (r0 + 1) ≤ rho.horizon := by
    have hr0 : r0 + 1 = R0 := Nat.sub_add_cancel hR0pos
    simpa only [hr0] using
      hgammaConf.trans (by simpa only [o] using hbaseTiming.2.2)
  have hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E (o + 2) := by
    have hrq : r0 ≤ q := by
      have hle : R0 ≤ q + 1 := by
        simpa only [R0, o] using
          w4nbs_round_of_opening_add_three_le_succ S.hc q
      exact Nat.lt_succ_iff.mp
        ((Nat.sub_lt hR0pos (by decide : 0 < 1)).trans_le hle)
    have hproposalPost : S.E.t_GST ≤
        Protocol.proposal_time S.E (o + 2) :=
      hbaseTiming.2.1.trans
        ((w4nbs_action_time_mono S hrq).trans
          (w4nbs_action_le_proposal_plus_two S q))
    exact hproposalPost.trans
      (le_of_lt (Protocol.proposal_time_lt_vote_time S.E _))
  have hcutHor : Protocol.support_cutoff S.E (o + 2) ≤ rho.horizon := by
    have hslots : o + 2 ≤ o + 3 := by
      show o + 2 ≤ o + 3
      exact Nat.le_succ _
    exact (Protocol.support_cutoff_le_confirmation_time S.E _).trans
      ((w4nbs_confirmation_time_mono S.E hslots).trans
        (by simpa only [o] using hbaseTiming.2.2))
  have hproposalHor : Protocol.proposal_time S.E (o + 3) ≤ rho.horizon := by
    exact (Protocol.proposal_time_lt_vote_time S.E (o + 3)).le.trans
      ((Protocol.vote_time_le_confirmation_time S.E (o + 3)).trans
        (by simpa only [o] using hbaseTiming.2.2))
  have hstart : Protocol.support_cutoff S.E (o + 2) ≤
      Protocol.proposal_time S.E (o + 3) := by
    exact (Protocol.support_cutoff_lt_proposal_time_succ S.E (o + 2)).le
  have hcone : NamedHonestVotesCone S rho (o + 2)
      (fun X => Block.Preceq D.erase X) := by
    have hvoteHor : Protocol.vote_time S.E (o + 2) ≤ rho.horizon :=
      (Protocol.vote_time_mono_slots S.E (by
        show o + 2 ≤ o + 3
        exact Nat.le_succ _)).trans
        ((Protocol.vote_time_le_confirmation_time S.E _).trans
          (by simpa only [o] using hbaseTiming.2.2))
    exact hhandoff.honestVotesCone_two_after adm hvoteHor
  have hroundC : S.hc.round_of ((o + 2) + 1) = r0 + 1 := by
    simpa only [Nat.add_assoc] using hround
  have hcone' : NamedHonestVotesCone S rho (o + 2)
      (fun X => Block.Preceq
        (EndAt' (strictEventIndex rho (Protocol.proposal_time S.E (o + 3)))) X) := by
    simpa only [hEndStrict] using hcone
  have hupper' : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r0)
        (EndAt' (strictEventIndex rho (Protocol.proposal_time S.E (o + 3)))) := by
    simpa only [hEndStrict] using hupper
  have hparent :=
    MovingFrontierChainStateN.endpoint_preceq_proposedParent_of_ceiling_named
      (c := o + 2) S adm hcom hfb hstate'
        (Nat.zero_lt_succ (o + 1))
        hroundC hupper'
      hbaseTiming.2.1 hcut hpostVote hcutHor hproposalHor
      (Nat.le_refl _) hprop hcone' hstart
  rw [hEndStrict] at hparent
  exact hparent

/-- The honest initial named fold from the selected stage-0 boundary. -/
theorem w4MovingSlotFoldAtN_boundary_honest_stage0
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {rGST gap q : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    (hqLate : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ q)
    {D : NamedBlock V} {carrier : V} {M0 : Height}
    (hhandoff : HealedTwoSlotHandoffPrepared S rho q D.erase carrier)
    (hboundary : W4NamedHandoffBoundaryCore S rho q
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0 D)
    (hbaseTiming :
      0 < S.hc.round_of (S.hc.opening_slot q + 3) ∧
      S.E.t_GST ≤ S.a
        (S.hc.round_of (S.hc.opening_slot q + 3) - 1) ∧
      Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤
        rho.horizon)
    (hprop : S.E.proposer (S.hc.opening_slot q + 3) ∈ rho.honest) :
    ∃ F : Slot → Block V, ∃ End : Block V,
      MovingSlotFoldAtN S rho
        (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
        (S.hc.opening_slot q + 3) (S.hc.opening_slot q + 3) F End ∧
      F (S.hc.opening_slot q + 3) = D.erase := by
  let o := S.hc.opening_slot q
  have hparent := w4nbs_parent_of_boundary S adm hcom hfb
    hhandoff hboundary hbaseTiming hprop
  obtain ⟨P, hP⟩ := proposedBlockAt_isSome S rho (o + 3)
  have hdeadline : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ q :=
    (Nat.le_succ _).trans hqLate
  have hdeadlineSlot : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤ o + 3 := by
    exact (Nat.mul_le_mul_right S.hc.R hdeadline).trans
      (Nat.le_add_right o 3)
  have hvoteHor : Protocol.vote_time S.E (o + 3) ≤ rho.horizon :=
    (Protocol.vote_time_le_confirmation_time S.E _).trans
      (by simpa only [o] using hbaseTiming.2.2)
  have hheadEq : ∀ w ∈ rho.honest,
      voteDutyHead S rho w (o + 3) = P.erase := by
    have h := honestProposal_voterHeadAt_eq_after_SG_healing_named_slot
      S adm hcom hfb hrec hdelay hpost (s := o + 2) (P := P)
        hdeadlineSlot hvoteHor hprop hP
    simpa only [Protocol.voteDutyHead] using h
  have hprevVotes : NamedHonestVotesCone S rho (o + 3)
      (fun X => Block.Preceq D.erase X) := by
    have hprevVotesP := honestProposal_slotVoteCone_after_SG_healing_named
      S adm hcom hfb hrec hdelay hpost (s := o + 2) (P := P)
        hdeadlineSlot hvoteHor hprop hP
    have hDP : Block.Preceq D.erase P.erase :=
      Block.preceq_trans hparent
        (w4nbs_proposal_parent_preceq_proposedBlockAt S rho (o + 3) hP)
    intro w hw hcommittee
    obtain ⟨X, hXP, hXrun, hXemit⟩ :=
      hprevVotesP w hw hcommittee
    exact ⟨X, Block.preceq_trans hDP hXP, hXrun, hXemit⟩
  have hconf : ∀ w ∈ rho.honest, ∀ C : Block V,
      GenuineConfirmationWith
        (NamedProfile.gradeContract
          (confirmationInputRead S rho w (o + 2)).cache)
        S.E S.hc
        (Proofs.Optimistic.confStore S rho w (o + 2)) (o + 2) C →
      Block.compatible C P.erase = true := by
    have hround : S.hc.round_of (o + 3) =
        S.hc.round_of (o + 3) - 1 + 1 := by
      exact (Nat.sub_add_cancel hbaseTiming.1).symm
    have hupper : ∀ u ∈ rho.honest,
        Block.Preceq (actionSGBlockAt S rho u
          (S.hc.round_of (o + 3) - 1)) D.erase := by
      intro u hu
      exact hboundary.carrierCeiling _ hround u hu
    have hroundC : S.hc.round_of ((o + 2) + 1) =
        S.hc.round_of (o + 3) - 1 + 1 := by
      simpa only [Nat.add_assoc] using hround
    have hpre := movingBoundaryPreEntryN_honest_of_prevEndpoint S
      (by
        have hslots : o + 1 ≤ o + 3 := by
          show o + 1 ≤ o + 3
          exact Nat.add_le_add_left (by decide : (1 : Nat) ≤ 3) o
        obtain ⟨EndAt, hstate, hconst⟩ :=
          w4NamedBoundaryHistoryN_toFreeze S adm hhandoff hboundary
            (by
              exact (Int.add_le_add_right
                (Protocol.proposal_time_mono S.E
                  hslots) _).trans
                (by simpa only [o] using hbaseTiming.2.2))
        obtain ⟨P0, hP0, EndAt', hstate', hstrict, hincl⟩ :=
          movingBoundaryHistoryN_toProposal_honest (c := o + 1) S adm hstate
            (hconst _ (Nat.le_refl _)) ⟨D, rfl, hboundary.run⟩ hprop
            ((Protocol.proposal_time_lt_vote_time S.E _).le.trans
              ((Protocol.vote_time_le_confirmation_time S.E _).trans
                (by simpa only [o] using hbaseTiming.2.2))) hparent
        have hP0eq : P0 = P := proposedBlockAt_unique S rho
            (o + 3) hP0 hP
        subst P0
        exact ⟨EndAt', hstate', hstrict, hincl⟩)
      (hhandoff.honestVotesCone_two_after adm
        ((Protocol.vote_time_mono_slots S.E (by
          show o + 2 ≤ o + 3
          exact Nat.le_succ _)).trans
          ((Protocol.vote_time_le_confirmation_time S.E _).trans
            (by simpa only [o] using hbaseTiming.2.2))))
    intro w hw C hC
    have hpostAction : S.E.t_GST ≤
        S.a (S.hc.round_of (o + 3) - 1) := hbaseTiming.2.1
    have hcut : S.hc.Γ_neg1 S.E.Δ
        (S.hc.round_of (o + 3)) ≤ rho.horizon := by
      have hR0' : S.hc.round_of (o + 3) =
          S.hc.round_of (o + 3) - 1 + 1 :=
        (Nat.sub_add_cancel hbaseTiming.1).symm
      have hgammaConf : S.hc.Γ_neg1 S.E.Δ
          (S.hc.round_of (o + 3)) ≤
          Protocol.confirmation_time S.E (o + 3) := by
        have hgamma : S.hc.Γ_neg1 S.E.Δ (S.hc.round_of (o + 3)) =
            (4 * ((S.hc.opening_slot (S.hc.round_of (o + 3)) : Slot) : Time) - 1) * S.E.Δ := by
          unfold Protocol.HealConfig.Γ_neg1 slotStart
          ring
        have hconf : Protocol.confirmation_time S.E (o + 3) =
            (4 * ((o + 3 : Slot) : Time) + 6) * S.E.Δ := by
          unfold Protocol.confirmation_time Env.t slotStart
          ring
        rw [hgamma, hconf]
        apply Int.mul_le_mul_of_nonneg_right _ S.E.Δ_pos.le
        have hopen : S.hc.opening_slot (S.hc.round_of (o + 3)) ≤ o + 3 := by
          simp only [Protocol.HealConfig.opening_slot,
            Protocol.HealConfig.round_of]
          exact Nat.div_mul_le_self (o + 3) S.hc.R
        have hcast : ((S.hc.opening_slot (S.hc.round_of (o + 3)) : Slot) : Time) ≤
            ((o + 3 : Slot) : Time) := by exact_mod_cast hopen
        push_cast at hcast ⊢
        linarith
      exact hgammaConf.trans (by simpa only [o] using hbaseTiming.2.2)
    have hpostProp : S.E.t_GST ≤ Protocol.proposal_time S.E (o + 2) := by
      have hrq : S.hc.round_of (o + 3) - 1 ≤ q := by
        have hle := w4nbs_round_of_opening_add_three_le_succ S.hc q
        exact Nat.lt_succ_iff.mp
          ((Nat.sub_lt hbaseTiming.1 (by decide : 0 < 1)).trans_le hle)
      exact hpostAction.trans
        ((w4nbs_action_time_mono S hrq).trans
          (w4nbs_action_le_proposal_plus_two S q))
    have hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E (o + 2) :=
      hpostProp.trans (le_of_lt (Protocol.proposal_time_lt_vote_time S.E _))
    have hslotHor : Protocol.confirmation_time S.E (o + 2) ≤ rho.horizon :=
      (w4nbs_confirmation_time_mono S.E (by
        show o + 2 ≤ o + 3
        exact Nat.le_succ _)).trans
        (by simpa only [o] using hbaseTiming.2.2)
    have hpre' : MovingSlotPreEntryN S rho
        (Protocol.support_cutoff S.E (o + 2)) M0 (o + 3)
        D.erase P.erase := by
      simpa only [o, Nat.add_assoc] using hpre
    have hcutC : S.hc.Γ_neg1 S.E.Δ
        (S.hc.round_of (o + 3) - 1 + 1) ≤ rho.horizon := by
      have heq : S.hc.round_of (o + 3) - 1 + 1 =
          S.hc.round_of (o + 3) := Nat.sub_add_cancel hbaseTiming.1
      simpa only [heq] using hcut
    have hDhead :=
      MovingSlotPreEntryN.genuineConfirmation_preceq_voteDutyHead_of_ceiling_named
        S adm hcom hfb (c := o + 2) (hentry := hpre')
        (Nat.zero_lt_succ (o + 1)) hroundC hupper hpostAction hcutC
        hpostVote hpostProp hslotHor hw hC hw
    have hDhead' : Block.Preceq C (voteDutyHead S rho w (o + 3)) := hDhead
    rw [hheadEq w hw] at hDhead'
    exact Block.compatible_of_preceq_common hDhead'
      (Block.preceq_self P.erase)
  exact w4MovingSlotFoldAtN_boundary_honest_named S adm hhandoff hboundary
    hbaseTiming hP hprop hparent hprevVotes hheadEq hconf

#print axioms w4MovingSlotFoldAtN_boundary_honest_stage0

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
