module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.W4NamedBoundaryCore
public import DecoupledConsensusProofs.Protocol.Grades.MovingChainHandoffBase
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainFold

@[expose] public section

/-!
# Prepared confirmation facts for the named handoff boundary

The base freeze interval reads the previous slot's confirmations. It does
not read the current slot's vote head, vote anchor, or endpoint order.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.NamedRecoveryRead
open Protocol Proofs.HealingLemmas
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The four fields read by a named confirmation interval. -/
structure W4NamedBoundaryConfirmationFacts
    (S : Setup V) (rho : Run V) (s : Slot) (Next : Block V) : Prop where
  confirmed : ∀ w ∈ rho.honest, ∀ C : Block V,
    GenuineConfirmationWith
      (NamedProfile.gradeContract
        (confirmationInputRead S rho w (s - 1)).cache)
      S.E S.hc (Proofs.Optimistic.confStore S rho w (s - 1)) (s - 1) C →
      Block.Preceq C Next
  carrier : ∀ w ∈ rho.honest, ∀ q : Round,
    S.a q = Protocol.confirmation_time S.E (s - 1) →
      Block.Preceq (actionSGBlockAt S rho w q) Next
  outputs : ∀ (j : Nat) (w : V), w ∈ rho.honest →
    rho.events[j]? = some
      (Event.tick w (Protocol.confirmation_time S.E (s - 1))) →
      HonestAttestationOutputPreceqAtIndex S rho j Next
  confAnchorCompatible : ∀ w ∈ rho.honest,
    Block.compatible
      (confirmationAnchorAt S rho w (s - 1)) Next = true

/-- Copy of the prepared anchor order used by the confirmation event. -/
private theorem w4nb_confAnchorWith_preceq_of_genuine
    (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V)
    (s : Slot) (B : Block V)
    (h : GenuineConfirmationWith contract E hc st s B) :
    Block.Preceq (confAnchorWith contract E hc st) B := by
  have hwalk : confWalkWith contract E hc st s = B := by
    have hsel := h.selected
    rw [update_confirmation_with_live_confirmed, if_pos h.genuine] at hsel
    exact hsel
  have hfloor : Block.Preceq (confAnchorWith contract E hc st)
      (confWalkWith contract E hc st s) :=
    ghost_preceq (confAnchorWith contract E hc st) (confTree st)
      (confScore E st s) (confEligible E st s)
  rwa [hwalk] at hfloor

/-- The prepared handoff supplies all four confirmation-side fields. -/
theorem w4NamedBoundaryConfirmationFacts_of_handoff
    (S : Setup V) {rho : Run V} {q : Round}
    {D : Block V} {carrier : V}
    (h : HealedTwoSlotHandoffPrepared S rho q D carrier)
    (hhor : Protocol.confirmation_time S.E (S.hc.opening_slot q + 1) ≤
      rho.horizon) :
    W4NamedBoundaryConfirmationFacts S rho
      (S.hc.opening_slot q + 2) D where
  confirmed := by
    intro w hw C hC
    obtain ⟨_hgen, hpre⟩ :=
      h.boundary_outputs (S.hc.opening_slot q + 1) (Or.inr rfl) w hw hhor
    have hCeq : C = movingSlotConfirmationOutput S rho
        (S.hc.opening_slot q + 1) w := hC.selected.symm
    rw [hCeq]
    exact hpre
  carrier := by
    intro _w _hw q' hq'
    exact absurd hq' (no_action_at_openingSucc_confirmation S q q')
  outputs := by
    intro j w _hw hev
    refine honestAttestationOutputPreceqAtIndex_of_no_emission S rho ?_
    rintro ⟨u, time, a, _hu, hevu, ha⟩
    have hteq : time =
        Protocol.confirmation_time S.E (S.hc.opening_slot q + 1) :=
      (NamedEvent.tick.inj (Option.some.inj (hevu.symm.trans hev))).2
    have hemits : rho.emits S u (Object.attest a) time :=
      ⟨j, hevu, ha⟩
    have hshape := Proofs.Optimistic.emits_attest_shape S hemits
    exact no_action_at_openingSucc_confirmation S q a.round
      (hshape.2.symm.trans hteq)
  confAnchorCompatible := by
    intro w hw
    obtain ⟨hgen, hpre⟩ :=
      h.boundary_outputs (S.hc.opening_slot q + 1) (Or.inr rfl) w hw hhor
    have hanchor : Block.Preceq
        (confirmationAnchorAt S rho w (S.hc.opening_slot q + 1))
        (movingSlotConfirmationOutput S rho (S.hc.opening_slot q + 1) w) := by
      simpa only [confirmationAnchorAt, namedConfirmationAnchor,
        Protocol.confAnchorWith,
        Proofs.Optimistic.confStore_eq_confirmationInputRead] using
        (w4nb_confAnchorWith_preceq_of_genuine
          (NamedProfile.gradeContract
            (confirmationInputRead S rho w (S.hc.opening_slot q + 1)).cache)
          S.E S.hc
          (Proofs.Optimistic.confStore S rho w (S.hc.opening_slot q + 1))
          (S.hc.opening_slot q + 1)
          (movingSlotConfirmationOutput S rho (S.hc.opening_slot q + 1) w)
          hgen)
    exact Block.compatible_of_preceq_common
      (Block.preceq_trans hanchor hpre) (Block.preceq_self D)

private theorem w4nb_slotInstant_ne (E : Env V) (a b : Slot) (m n : Int)
    (hmod : ∀ x y : Int, 4 * x + m ≠ 4 * y + n) :
    (4 * (a : Time) + m) * E.Δ ≠
      (4 * (b : Time) + n) * E.Δ := by
  intro heq
  exact hmod (a : Time) (b : Time)
    (mul_right_cancel₀ (ne_of_gt E.Δ_pos) heq)

/-- No-tick event facts, copied from MovingChainFoldRun. -/
private theorem w4nb_eventFacts_of_no_tick
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
  · refine honestAttestationOutputPreceqAtIndex_of_no_emission S rho ?_
    rintro ⟨v, time, a, _hv, hevent, _ha⟩
    exact absurd hevent (hno _ _)
  · refine { voteCompatible := ?_, confirmationCompatible := ?_ }
    · intro v s _hv hevent
      exact absurd hevent (hno _ _)
    · intro v s _hv hevent
      exact absurd hevent (hno _ _)

/-- View-freeze event facts, copied from MovingChainFoldRun. -/
private theorem w4nb_eventFacts_viewFreeze
    (S : Setup V) {rho : Run V} {i : Nat} {Next : Block V}
    {w : V} {s : Slot}
    (hevent : rho.events[i]? = some
      (Event.tick w (Protocol.view_freeze S.E s))) :
    ProposalChainObservationsSandwichedAtIndex S rho i Next Next ∧
      NamedGenuineConfirmationsPreceqAtIndex S rho i Next ∧
      HonestActionSGCarriersPreceqAtIndex S rho i Next ∧
      HonestAttestationOutputPreceqAtIndex S rho i Next ∧
      NamedReadAnchorsAtIndex S rho i Next := by
  obtain ⟨hproposal, _hconfirmations, hsg, hout, _hanchors⟩ :=
    movingEventFacts_viewFreeze S hevent
  have htickTime : ∀ {u : V} {t : Time},
      rho.events[i]? = some (Event.tick u t) →
        t = Protocol.view_freeze S.E s := by
    intro u t hu
    have heq : u = w ∧ t = Protocol.view_freeze S.E s := by
      simpa using Option.some.inj (hu.symm.trans hevent)
    exact heq.2
  have hfreezeNormal (a : Slot) :
      Protocol.view_freeze S.E a = (4 * (a : Time) + 3) * S.E.Δ := by
    unfold Protocol.view_freeze Env.t slotStart
    ring
  have hvoteNormal (a : Slot) :
      Protocol.vote_time S.E a = (4 * (a : Time) + 1) * S.E.Δ := by
    unfold Protocol.vote_time Env.t slotStart
    ring
  have hconfNormal (a : Slot) :
      Protocol.confirmation_time S.E a = (4 * (a : Time) + 6) * S.E.Δ := by
    unfold Protocol.confirmation_time Env.t slotStart
    ring
  have hvoteNe : ∀ s' : Slot,
      Protocol.view_freeze S.E s ≠ Protocol.vote_time S.E s' := by
    intro s'
    rw [hfreezeNormal, hvoteNormal]
    exact w4nb_slotInstant_ne S.E s s' 3 1 (by intro x y; omega)
  have hconfNe : ∀ s' : Slot,
      Protocol.confirmation_time S.E s' ≠
        Protocol.view_freeze S.E s := by
    intro s'
    rw [hfreezeNormal, hconfNormal]
    exact w4nb_slotInstant_ne S.E s' s 6 3 (by intro x y; omega)
  have hconfirmations : NamedGenuineConfirmationsPreceqAtIndex
      S rho i Next := by
    intro u _hu C hC
    obtain ⟨s', hevt, _hgen⟩ := hC
    exact absurd (htickTime hevt) (hconfNe s')
  have hanchors : NamedReadAnchorsAtIndex S rho i Next := by
    refine { voteCompatible := ?_, confirmationCompatible := ?_ }
    · intro u s' _hu hevt
      exact absurd (htickTime hevt) (fun heq => hvoteNe s' heq.symm)
    · intro u s' _hu hevt
      exact absurd (htickTime hevt) (hconfNe s')
  exact ⟨hproposal, hconfirmations, hsg, hout, hanchors⟩

/-- Prepared event facts for one honest confirmation tick. -/
private theorem w4nb_eventFacts_confirmationAt
    (S : Setup V) {rho : Run V} {i : Nat} {w : V} {s : Slot}
    (hevent : rho.events[i]? = some
      (Event.tick w (Protocol.confirmation_time S.E s)))
    {Next : Block V}
    (hgenuine : ∀ C : Block V,
      GenuineConfirmationWith
        (NamedProfile.gradeContract
          (confirmationInputRead S rho w s).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho w s) s C →
        Block.Preceq C Next)
    (hcarrier : ∀ q : Round,
      S.a q = Protocol.confirmation_time S.E s →
        Block.Preceq (actionSGBlockAt S rho w q) Next)
    (hout : HonestAttestationOutputPreceqAtIndex S rho i Next)
    (hanchor : Block.compatible
      (confirmationAnchorAt S rho w s) Next = true) :
    ProposalChainObservationsSandwichedAtIndex S rho i Next Next ∧
      NamedGenuineConfirmationsPreceqAtIndex S rho i Next ∧
      HonestActionSGCarriersPreceqAtIndex S rho i Next ∧
      HonestAttestationOutputPreceqAtIndex S rho i Next ∧
      NamedReadAnchorsAtIndex S rho i Next := by
  have htickPair : ∀ {u : V} {t : Time},
      rho.events[i]? = some (Event.tick u t) →
        u = w ∧ t = Protocol.confirmation_time S.E s := by
    intro u t hu
    simpa using Option.some.inj (hu.symm.trans hevent)
  have hslotEq : ∀ s' : Slot,
      Protocol.confirmation_time S.E s' =
        Protocol.confirmation_time S.E s → s' = s := by
    intro s' heq
    have hcongr := congrArg S.E.slotOf heq
    rw [Proofs.Optimistic.slotOf_confirmation_time,
      Proofs.Optimistic.slotOf_confirmation_time] at hcongr
    exact Nat.add_right_cancel hcongr
  have hproposalNormal (a : Slot) :
      Protocol.proposal_time S.E a = (4 * (a : Time) + 0) * S.E.Δ := by
    unfold Protocol.proposal_time Env.t slotStart
    ring
  have hvoteNormal (a : Slot) :
      Protocol.vote_time S.E a = (4 * (a : Time) + 1) * S.E.Δ := by
    unfold Protocol.vote_time Env.t slotStart
    ring
  have hconfNormal (a : Slot) :
      Protocol.confirmation_time S.E a = (4 * (a : Time) + 6) * S.E.Δ := by
    unfold Protocol.confirmation_time Env.t slotStart
    ring
  have hproposalNe : ∀ s' : Slot,
      Protocol.confirmation_time S.E s ≠
        Protocol.proposal_time S.E s' := by
    intro s'
    rw [hconfNormal, hproposalNormal]
    exact w4nb_slotInstant_ne S.E s s' 6 0 (by intro x y; omega)
  have hvoteNe : ∀ s' : Slot,
      Protocol.confirmation_time S.E s ≠ Protocol.vote_time S.E s' := by
    intro s'
    rw [hconfNormal, hvoteNormal]
    exact w4nb_slotInstant_ne S.E s s' 6 1 (by intro x y; omega)
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
    | voteHead _ hevt hactive _ _ =>
        obtain ⟨rfl, rfl⟩ := htickPair hevt
        exact absurd hactive.2 (hvoteNe _)
    | confirmationOutput =>
        simp only [ProposalChainStage] at hstage
        omega
    | actionHead =>
        simp only [ProposalChainStage] at hstage
        omega
  have hconfirmations : NamedGenuineConfirmationsPreceqAtIndex
      S rho i Next := by
    intro u _hu C hC
    obtain ⟨s', hevt, hgen⟩ := hC
    obtain ⟨rfl, hteq⟩ := htickPair hevt
    have hss : s' = s := hslotEq s' hteq
    subst hss
    exact hgenuine C hgen
  have hsg : HonestActionSGCarriersPreceqAtIndex S rho i Next := by
    intro u q a _hu hevt _ha
    obtain ⟨rfl, hteq⟩ := htickPair hevt
    exact hcarrier q hteq
  have hanchors : NamedReadAnchorsAtIndex S rho i Next := by
    refine { voteCompatible := ?_, confirmationCompatible := ?_ }
    · intro u s' _hu hevt
      exact absurd (htickPair hevt).2 (fun heq => hvoteNe s' heq.symm)
    · intro u s' _hu hevt
      obtain ⟨rfl, hteq⟩ := htickPair hevt
      have hss : s' = s := hslotEq s' hteq
      subst hss
      exact hanchor
  exact ⟨hproposal, hconfirmations, hsg, hout, hanchors⟩

/-- The confirmation interval reads only the four prepared fields. -/
theorem w4NamedBoundaryConfirmationFacts.eventFacts
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hs : 0 < s) {Next : Block V}
    (hfacts : W4NamedBoundaryConfirmationFacts S rho s Next)
    {j : Nat}
    (hlow : strictEventIndex rho (Protocol.support_cutoff S.E s) ≤ j)
    (hhigh : j < inclusiveEventIndex rho (Protocol.view_freeze S.E s)) :
    ProposalChainObservationsSandwichedAtIndex S rho j Next Next ∧
      NamedGenuineConfirmationsPreceqAtIndex S rho j Next ∧
      HonestActionSGCarriersPreceqAtIndex S rho j Next ∧
      HonestAttestationOutputPreceqAtIndex S rho j Next ∧
      NamedReadAnchorsAtIndex S rho j Next := by
  have hproposalNormal (a : Slot) :
      Protocol.proposal_time S.E a = (4 * (a : Time) + 0) * S.E.Δ := by
    unfold Protocol.proposal_time Env.t slotStart
    ring
  have hvoteNormal (a : Slot) :
      Protocol.vote_time S.E a = (4 * (a : Time) + 1) * S.E.Δ := by
    unfold Protocol.vote_time Env.t slotStart
    ring
  have hsupportNormal (a : Slot) :
      Protocol.support_cutoff S.E a = (4 * (a : Time) + 2) * S.E.Δ := by
    unfold Protocol.support_cutoff Env.t slotStart
    ring
  have hfreezeNormal (a : Slot) :
      Protocol.view_freeze S.E a = (4 * (a : Time) + 3) * S.E.Δ := by
    unfold Protocol.view_freeze Env.t slotStart
    ring
  have hpropCut : Protocol.proposal_time S.E s <
      Protocol.support_cutoff S.E s := by
    rw [hproposalNormal, hsupportNormal]
    exact Int.mul_lt_mul_of_pos_right (by omega) S.E.Δ_pos
  have hvoteCut : Protocol.vote_time S.E s <
      Protocol.support_cutoff S.E s := by
    rw [hvoteNormal, hsupportNormal]
    exact Int.mul_lt_mul_of_pos_right (by omega) S.E.Δ_pos
  have hcutFreeze : Protocol.support_cutoff S.E s ≤
      Protocol.view_freeze S.E s := by
    rw [hsupportNormal, hfreezeNormal]
    exact Int.mul_le_mul_of_nonneg_right (by omega) (le_of_lt S.E.Δ_pos)
  have hfreezeSucc : Protocol.view_freeze S.E s <
      Protocol.proposal_time S.E (s + 1) := by
    rw [hfreezeNormal, hproposalNormal]
    refine Int.mul_lt_mul_of_pos_right ?_ S.E.Δ_pos
    have hcast : ((s + 1 : Nat) : Int) = (s : Int) + 1 := by
      push_cast
      ring
    rw [hcast]
    omega
  have hcut : Protocol.support_cutoff S.E s =
      Protocol.confirmation_time S.E (s - 1) :=
    support_cutoff_eq_confirmation_time_pred S.E hs
  cases hev : rho.events[j]? with
  | none =>
      refine w4nb_eventFacts_of_no_tick S rho Next ?_
      intro w t htick
      rw [hev] at htick
      simp only [reduceCtorEq] at htick
  | some e =>
      cases e with
      | deliver v o t =>
          refine w4nb_eventFacts_of_no_tick S rho Next ?_
          intro w t' htick
          rw [hev] at htick
          simp only [Option.some.injEq, reduceCtorEq] at htick
      | tick u t =>
          have hmem : Event.tick u t ∈ rho.events :=
            List.mem_of_getElem? hev
          have hpub : PublicTime S t := adm.tick_public u t hmem
          have hge : Protocol.support_cutoff S.E s ≤ t := by
            have hres := Proofs.Optimistic.le_time_of_index_ge
              S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
              (by simpa only [strictEventIndex] using hlow) hev
            simpa only [Event.time] using hres
          have hle : t ≤ Protocol.view_freeze S.E s := by
            have htrue := Proofs.Optimistic.filter_true_of_index_lt S
              adm.toNamedAdmissibleCore.toNamedScheduleWellFormed _
              (Proofs.Optimistic.downward_le (Protocol.view_freeze S.E s))
              (by simpa only [inclusiveEventIndex] using hhigh) hev
            simpa only [decide_eq_true_eq, Event.time] using htrue
          have hhonest : u ∈ rho.honest := by
            simpa only [Event.node] using adm.honest_only _ hmem
          have hgt : Protocol.proposal_time S.E s < t :=
            lt_of_lt_of_le hpropCut hge
          rcases publicTime_slotWindow_cases S hpub hgt
            (hle.trans (le_of_lt hfreezeSucc)) with ht | ht | ht | ht
          · exact absurd (ht ▸ hge) (not_le_of_gt hvoteCut)
          · rw [hcut] at ht
            subst ht
            exact w4nb_eventFacts_confirmationAt S hev
              (hfacts.confirmed u hhonest)
              (fun q hq => hfacts.carrier u hhonest q hq)
              (hfacts.outputs j u hhonest hev)
              (hfacts.confAnchorCompatible u hhonest)
          · subst ht
            exact w4nb_eventFacts_viewFreeze S hev
          · exact absurd (ht ▸ hle)
              (not_le_of_gt hfreezeSucc)

/-- The named boundary history through the first view freeze. -/
theorem w4NamedBoundaryHistoryN_toFreeze
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} {D : NamedBlock V} {carrier : V} {M0 : Height}
    (hhandoff : HealedTwoSlotHandoffPrepared S rho q D.erase carrier)
    (hboundary : W4NamedHandoffBoundaryCore S rho q
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0 D)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot q + 1) ≤ rho.horizon) :
    ∃ EndAt : Nat → Block V,
      MovingFrontierChainStateN S rho
          (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
          (strictEventIndex rho
            (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)))
          (inclusiveEventIndex rho
            (Protocol.view_freeze S.E (S.hc.opening_slot q + 2))) EndAt ∧
        ∀ j, j ≤ inclusiveEventIndex rho
          (Protocol.view_freeze S.E (S.hc.opening_slot q + 2)) →
          EndAt j = D.erase := by
  have hbootN := hboundary.bootstrapAtN S adm
  have hcm : strictEventIndex rho
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) ≤
      inclusiveEventIndex rho
        (Protocol.view_freeze S.E (S.hc.opening_slot q + 2)) :=
    (strictEventIndex_mono rho
      (le_of_lt (Proofs.Optimistic.support_cutoff_lt_view_freeze S.E
        (S.hc.opening_slot q + 2)))).trans
      (strictEventIndex_le_inclusiveEventIndex rho _)
  have hfacts :
      W4NamedBoundaryConfirmationFacts S rho
        (S.hc.opening_slot q + 2) D.erase :=
    w4NamedBoundaryConfirmationFacts_of_handoff S hhandoff hhor
  obtain ⟨EndAt, hlow, hhigh, hstate⟩ :=
    hbootN.through_constantEndpoint_named_public S
      (Block.preceq_self D.erase) ⟨D, rfl, hboundary.run⟩ hcm
      (fun j hj hjlt =>
        w4NamedBoundaryConfirmationFacts.eventFacts S adm
          (Nat.succ_pos (S.hc.opening_slot q + 1)) hfacts hj hjlt)
  refine ⟨EndAt, hstate, ?_⟩
  intro j hj
  rcases Nat.lt_or_ge
    (strictEventIndex rho
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2))) j with
    hlt | hge
  · exact hhigh j hlt
  · exact hlow j hge

#check w4NamedBoundaryConfirmationFacts_of_handoff
#check w4NamedBoundaryHistoryN_toFreeze

#print axioms w4NamedBoundaryConfirmationFacts_of_handoff
#print axioms w4NamedBoundaryHistoryN_toFreeze

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
