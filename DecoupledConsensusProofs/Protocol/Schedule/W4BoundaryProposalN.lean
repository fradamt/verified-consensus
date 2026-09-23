module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.MovingChainCeiling
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# W4 branches b: the named boundary history through the honest proposal

The named twin of `movingBoundaryHistory_toProposal_honest`
(`MovingChainBoundaryRun.lean:289`): the boundary history advances from the
view-freeze cursor of slot `c + 1` to the proposal cursor of slot `c + 2`, with
the endpoint staying at `E` up to the proposer's own tick, which installs the
proposal, and at the proposal for the rest of that instant.

earlier's body, on the named history. The two constant-endpoint stretches use the
public named forms `MovingFrontierChainStateN.through_constantEndpoint_named_public`
and `movingSlotWindowTail_eventFacts_named_public`, which already carry the two
contract-bearing fields (`NamedGenuineConfirmationsPreceqAtIndex`,
`NamedReadAnchorsAtIndex`) as per-index facts.

The one step with no public named form is the proposal instant itself,
`MovingFrontierChainStateN.succ_proposalInstant_named`
(`MovingChainFoldRun.lean:1678`), which is `private` there. `MovingChainFoldRun`
sits under the whole moving-chain tree, so a source change there freezes every
olean above it for every branches; the lead therefore COPY rather than export
. The step and the six further private lemmas it reaches are copied below
as `w4b_`-prefixed twins, each cited at its origin, so this theorem is
PIN-FREE.

A clean leaf, not an edit of `MovingChainBoundaryRun`: that module is
unallocated, and adding imports to an existing module can break declarations
already in it by changing name resolution, which neither `check-cycle.py` nor
`check-below.py` sees.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem w4b_view_freeze_normal (E : Env V) (s : Slot) :
    Protocol.view_freeze E s = (4 * (s : Time) + 3) * E.Δ := by
  unfold Protocol.view_freeze Env.t slotStart
  ring

private theorem w4b_proposal_time_normal (E : Env V) (s : Slot) :
    Protocol.proposal_time E s = (4 * (s : Time)) * E.Δ := by
  unfold Protocol.proposal_time Env.t slotStart
  ring

private theorem w4b_view_freeze_lt_proposal_time_succ (E : Env V) (s : Slot) :
    Protocol.view_freeze E s < Protocol.proposal_time E (s + 1) := by
  rw [w4b_view_freeze_normal, w4b_proposal_time_normal]
  refine Int.mul_lt_mul_of_pos_right ?_ E.Δ_pos
  have hcast : ((s + 1 : Nat) : Int) = (s : Int) + 1 := by push_cast; ring
  rw [hcast]
  omega

private theorem w4b_inclusive_le_strict_of_lt
    (rho : Run V) {t0 t1 : Time} (hlt : t0 < t1) :
    inclusiveEventIndex rho t0 ≤ strictEventIndex rho t1 := by
  unfold inclusiveEventIndex strictEventIndex
  exact (List.monotone_filter_right rho.events (fun e he => by
    simp only [decide_eq_true_eq] at he ⊢
    exact lt_of_le_of_lt he hlt)).length_le

omit [DecidableEq V] [Fintype V] in
private theorem w4b_eventIndex_unique
    {rho : Run V} (hnodup : rho.events.Nodup) {i j : Nat} {e : Event V}
    (hi : rho.events[i]? = some e) (hj : rho.events[j]? = some e) :
    i = j := by
  obtain ⟨hiLen, hie⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjLen, hje⟩ := List.getElem?_eq_some_iff.mp hj
  have hfin : (⟨i, hiLen⟩ : Fin rho.events.length) = ⟨j, hjLen⟩ :=
    (List.nodup_iff_injective_getElem.mp hnodup) (by simp only [hie, hje])
  simpa using congrArg Fin.val hfin

private theorem w4b_eventTime_gt_of_inclusive_le
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {t0 : Time} {j : Nat} {e : Event V}
    (hj : inclusiveEventIndex rho t0 ≤ j)
    (hget : rho.events[j]? = some e) :
    t0 < e.time := by
  have hfalse := Proofs.Optimistic.filter_false_of_index_ge S sch _
    (Proofs.Optimistic.downward_le t0)
    (by simpa only [inclusiveEventIndex] using hj) hget
  simpa only [decide_eq_false_iff_not, not_le] using hfalse

private theorem w4b_proposedParent_preceq_proposedBlockAt
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

/-- Copies of four further `private` helpers the three above call, cited at
their origin: `proposal_time_lt_support_cutoff`,
`confirmation_time_ne_proposal_time` and `vote_time_ne_proposal_time`
(`MovingChainFoldRun.lean:57,69,83`), and `tick_node_time_eq_of_same_index`
(`Availability/CanonicalObservationRun.lean:231`). -/
private theorem w4b_proposal_time_lt_support_cutoff (E : Env V) (s : Slot) :
    Protocol.proposal_time E s < Protocol.support_cutoff E s := by
  have hvote : Protocol.proposal_time E s < Protocol.vote_time E s :=
    Protocol.proposal_time_lt_vote_time E s
  have hcut : Protocol.vote_time E s < Protocol.support_cutoff E s := by
    rw [← Proofs.Optimistic.vote_time_add_delta]
    exact Int.lt_add_of_pos_right _ E.Δ_pos
  exact hvote.trans hcut

private theorem w4b_confirmation_time_ne_proposal_time (E : Env V) (s' s : Slot)
    (heq : Protocol.confirmation_time E s' = Protocol.proposal_time E s) :
    False := by
  have hslot : s' + 1 = s := by
    have hcongr := congrArg E.slotOf heq
    rwa [Proofs.Optimistic.slotOf_confirmation_time,
      Proofs.Optimistic.slotOf_proposal_time] at hcongr
  have hcut : Protocol.support_cutoff E (s' + 1) =
      Protocol.proposal_time E (s' + 1) := by
    rw [← Protocol.confirmation_time_eq_support_cutoff_succ, hslot]
    exact heq
  exact absurd hcut.symm (ne_of_lt (w4b_proposal_time_lt_support_cutoff E (s' + 1)))

private theorem w4b_vote_time_ne_proposal_time (E : Env V) (s' s : Slot)
    (heq : Protocol.vote_time E s' = Protocol.proposal_time E s) :
    False := by
  have hslot : s' = s := by
    have hcongr := congrArg E.slotOf heq
    rwa [Proofs.Optimistic.slotOf_vote_time, Proofs.Optimistic.slotOf_proposal_time] at hcongr
  subst hslot
  exact absurd heq.symm (ne_of_lt (Protocol.proposal_time_lt_vote_time E s'))

omit [DecidableEq V] [Fintype V] in
private theorem w4b_tick_node_time_eq_of_same_index
    {rho : Run V} {i : Nat} {v w : V} {t u : Time}
    (h₁ : rho.events[i]? = some (Event.tick v t))
    (h₂ : rho.events[i]? = some (Event.tick w u)) : v = w ∧ t = u := by
  have h := Option.some.inj (h₁.symm.trans h₂)
  simpa using h



private theorem w4b_movingEventFacts_proposalInstant_at_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {i : Nat} {u : V} {s : Slot}
    (hevent : rho.events[i]? = some
      (Event.tick u (Protocol.proposal_time S.E s)))
    {Before Next : Block V}
    (hproposer : S.E.proposer s = (S.node u).val_index →
      Block.Preceq Before (proposedParent S rho s) ∧
        ∃ P : NamedBlock V, proposedBlockAt S rho s = some P ∧
          Block.Preceq P.erase Next) :
    ProposalChainObservationsSandwichedAtIndex S rho i Before Next ∧
      NamedGenuineConfirmationsPreceqAtIndex S rho i Next ∧
      HonestActionSGCarriersPreceqAtIndex S rho i Next ∧
      HonestAttestationOutputPreceqAtIndex S rho i Next ∧
      NamedReadAnchorsAtIndex S rho i Next := by
  obtain ⟨hproposal, _hconfirmations, hsg, hout, _hanchors⟩ :=
    movingEventFacts_proposalInstant S adm hevent hproposer
  have htickTime : ∀ {v : V} {t : Time},
      rho.events[i]? = some (Event.tick v t) →
        t = Protocol.proposal_time S.E s := by
    intro v t hevent'
    exact (w4b_tick_node_time_eq_of_same_index hevent' hevent).2
  have hconfirmations : NamedGenuineConfirmationsPreceqAtIndex
      S rho i Next := by
    intro v _hv C hC
    obtain ⟨s', hevent', _hgen⟩ := hC
    have htime := htickTime hevent'
    exact (w4b_confirmation_time_ne_proposal_time S.E s' s htime).elim
  have hanchors : NamedReadAnchorsAtIndex S rho i Next := by
    refine { voteCompatible := ?_, confirmationCompatible := ?_ }
    · intro v s' _hv hevent'
      have htime := htickTime hevent'
      exact (w4b_vote_time_ne_proposal_time S.E s' s htime).elim
    · intro v s' _hv hevent'
      have htime := htickTime hevent'
      exact (w4b_confirmation_time_ne_proposal_time S.E s' s htime).elim
  exact ⟨hproposal, hconfirmations, hsg, hout, hanchors⟩

private theorem w4b_succ_of_eventFacts_named
    {S : Setup V} {rho : Run V} {t1 : Time} {M0 : Height}
    {n0 i : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 i End)
    (Next : Block V)
    (hEndNext : Block.Preceq (End i) Next)
    (hNextRun : ∃ E : NamedBlock V, E.erase = Next ∧ RunBlock S rho E)
    (hproposal : ProposalChainObservationsSandwichedAtIndex
      S rho i (End i) Next)
    (hconfirmations : NamedGenuineConfirmationsPreceqAtIndex S rho i Next)
    (hsg : HonestActionSGCarriersPreceqAtIndex S rho i Next)
    (hout : HonestAttestationOutputPreceqAtIndex S rho i Next)
    (hanchors : NamedReadAnchorsAtIndex S rho i Next) :
    ∃ End' : Nat → Block V,
      (∀ j, j ≤ i → End' j = End j) ∧
      End' (i + 1) = Next ∧
      MovingFrontierChainStateN S rho t1 M0 n0 (i + 1) End' := by
  let End' : Nat → Block V := fun j =>
    if j = i + 1 then Next else End j
  refine ⟨End', ?_, ?_, ?_⟩
  · intro j hji
    have hjne : j ≠ i + 1 := by omega
    simp only [End', if_neg hjne]
  · simp only [End', if_pos rfl]
  · refine
      { historyStart := h.historyStart
        start_le := h.start_le.trans (Nat.le_succ i)
        endpointRun := ?_
        endpointMono := ?_
        proposalChain := ?_
        genuineConfirmations := ?_
        sgCarriers := ?_
        outputs := ?_
        anchors := ?_
        oldRows_named := by
          have hn0ne : n0 ≠ i + 1 :=
            Nat.ne_of_lt (h.start_le.trans_lt (Nat.lt_succ_self i))
          intro j a time ha hevent hemit hj hh hrow E hE hErun
          have hE' : E.erase = End n0 := by
            simpa only [End', if_neg hn0ne] using hE
          simpa only [End', if_neg hn0ne] using
            h.oldRows_named ha hevent hemit hj hh hrow E hE' hErun
        frontierFloor := h.frontierFloor
        boundaryTargets := by
          have hn0ne : n0 ≠ i + 1 := by
            have hn0le : n0 ≤ i := h.start_le
            omega
          simpa only [End', if_neg hn0ne] using h.boundaryTargets }
    · intro j hj hjupper
      by_cases hji : j = i + 1
      · subst j
        simpa only [End', if_pos rfl] using hNextRun
      · have hjold : j ≤ i := by omega
        simpa only [End', if_neg hji] using h.endpointRun j hj hjold
    · intro j hj hjupper
      by_cases hji : j = i
      · subst j
        have hine : i ≠ i + 1 := by omega
        simp only [End', if_neg hine, if_pos rfl]
        exact hEndNext
      · have hjold : j < i := by omega
        have hjne : j ≠ i + 1 := by omega
        have hjsne : j + 1 ≠ i + 1 := by omega
        simpa only [End', if_neg hjne, if_neg hjsne] using
          h.endpointMono j hj hjold
    · intro j hj hjupper
      by_cases hji : j = i
      · subst j
        have hine : i ≠ i + 1 := by omega
        simpa only [End', if_neg hine, if_pos rfl] using hproposal
      · have hjold : j < i := by omega
        have hjne : j ≠ i + 1 := by omega
        have hjsne : j + 1 ≠ i + 1 := by omega
        simpa only [End', if_neg hjne, if_neg hjsne] using
          h.proposalChain j hj hjold
    · intro j hj hjupper
      by_cases hji : j = i
      · subst j
        simpa only [End', if_pos rfl] using hconfirmations
      · have hjold : j < i := by omega
        have hjsne : j + 1 ≠ i + 1 := by omega
        simpa only [End', if_neg hjsne] using
          h.genuineConfirmations j hj hjold
    · intro j hj hjupper
      by_cases hji : j = i
      · subst j
        simpa only [End', if_pos rfl] using hsg
      · have hjold : j < i := by omega
        have hjsne : j + 1 ≠ i + 1 := by omega
        simpa only [End', if_neg hjsne] using h.sgCarriers j hj hjold
    · intro j hj hjupper
      by_cases hji : j = i
      · subst j
        simpa only [End', if_pos rfl] using hout
      · have hjold : j < i := by omega
        have hjsne : j + 1 ≠ i + 1 := by omega
        simpa only [End', if_neg hjsne] using h.outputs j hj hjold
    · intro j hj hjupper
      by_cases hji : j = i
      · subst j
        simpa only [End', if_pos rfl] using hanchors
      · have hjold : j < i := by omega
        have hjsne : j + 1 ≠ i + 1 := by omega
        simpa only [End', if_neg hjsne] using h.anchors j hj hjold

private theorem w4b_succ_proposalInstant_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {t1 : Time} {M0 : Height} {n0 i : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 i End)
    {u : V} {s : Slot}
    (hevent : rho.events[i]? = some
      (Event.tick u (Protocol.proposal_time S.E s)))
    {Next : Block V}
    (hEndNext : Block.Preceq (End i) Next)
    (hNextRun : ∃ E : NamedBlock V, E.erase = Next ∧ RunBlock S rho E)
    (hproposer : S.E.proposer s = (S.node u).val_index →
      Block.Preceq (End i) (proposedParent S rho s) ∧
        ∃ P : NamedBlock V, proposedBlockAt S rho s = some P ∧
          Block.Preceq P.erase Next) :
    ∃ End' : Nat → Block V,
      (∀ j, j ≤ i → End' j = End j) ∧
      End' (i + 1) = Next ∧
      MovingFrontierChainStateN S rho t1 M0 n0 (i + 1) End' := by
  obtain ⟨hproposal, hconfirmations, hsg, hout, hanchors⟩ :=
    w4b_movingEventFacts_proposalInstant_at_named S adm hevent hproposer
  exact w4b_succ_of_eventFacts_named h Next hEndNext hNextRun
    hproposal hconfirmations hsg hout hanchors

/-- **The named boundary history through the honest slot-`(c + 2)` proposal.**
earlier's `movingBoundaryHistory_toProposal_honest` on the named history. -/
theorem movingBoundaryHistoryN_toProposal_honest
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {M0 : Height} {c : Slot} {E : Block V} {n0 : Nat}
    {EndAt : Nat → Block V}
    (hstate : MovingFrontierChainStateN S rho
      (Protocol.support_cutoff S.E (c + 1)) M0 n0
      (inclusiveEventIndex rho (Protocol.view_freeze S.E (c + 1))) EndAt)
    (hconst : EndAt
      (inclusiveEventIndex rho (Protocol.view_freeze S.E (c + 1))) = E)
    (hrun : ∃ D : NamedBlock V, D.erase = E ∧ RunBlock S rho D)
    (hprop : S.E.proposer (c + 1 + 1) ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E (c + 1 + 1) ≤ rho.horizon)
    (hparent : Block.Preceq E (proposedParent S rho (c + 1 + 1))) :
    ∃ P : NamedBlock V, proposedBlockAt S rho (c + 1 + 1) = some P ∧
      ∃ EndAt' : Nat → Block V,
        MovingFrontierChainStateN S rho
            (Protocol.support_cutoff S.E (c + 1)) M0 n0
            (inclusiveEventIndex rho
              (Protocol.proposal_time S.E (c + 1 + 1))) EndAt' ∧
          EndAt'
              (strictEventIndex rho
                (Protocol.proposal_time S.E (c + 1 + 1))) = E ∧
            EndAt'
              (inclusiveEventIndex rho
                (Protocol.proposal_time S.E (c + 1 + 1))) = P.erase := by
  classical
  set cf := inclusiveEventIndex rho (Protocol.view_freeze S.E (c + 1)) with hcf
  set sn := strictEventIndex rho
    (Protocol.proposal_time S.E (c + 1 + 1)) with hsn
  set cn := inclusiveEventIndex rho
    (Protocol.proposal_time S.E (c + 1 + 1)) with hcn
  obtain ⟨P, hP⟩ := proposedBlockAt_isSome S rho (c + 1 + 1)
  have hPrun : RunBlock S rho P :=
    proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
      (c + 1 + 1) (Nat.succ_pos _) hprop hhor hP
  have hNextP : Block.Preceq E P.erase :=
    Block.preceq_trans hparent
      (w4b_proposedParent_preceq_proposedBlockAt S rho (c + 1 + 1) hP)
  obtain ⟨_hBslot, hpemit⟩ :=
    Proofs.Optimistic.proposalTick S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (c + 1 + 1) (Nat.succ_pos _) hprop hhor hP
  obtain ⟨p, hpevent, _hpblock⟩ := hpemit
  have hcfsn : cf ≤ sn :=
    w4b_inclusive_le_strict_of_lt rho
      (w4b_view_freeze_lt_proposal_time_succ S.E (c + 1))
  have hsnp : sn ≤ p := by
    by_contra hnot
    have htrue := Proofs.Optimistic.filter_true_of_index_lt
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed _
      (Proofs.Optimistic.downward_lt (Protocol.proposal_time S.E (c + 1 + 1)))
      (by simpa only [strictEventIndex] using Nat.lt_of_not_ge hnot) hpevent
    simp only [decide_eq_true_eq, Event.time] at htrue
    exact lt_irrefl _ htrue
  have hcfp : cf ≤ p := hcfsn.trans hsnp
  have hpcn : p < cn := by
    by_contra hnot
    have hgt := w4b_eventTime_gt_of_inclusive_le S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (Nat.le_of_not_gt hnot) hpevent
    simp only [Event.time] at hgt
    exact lt_irrefl _ hgt
  have hpUnique : ∀ (j : Nat) (u : V), u ∈ rho.honest →
      rho.events[j]? = some
        (Event.tick u (Protocol.proposal_time S.E (c + 1 + 1))) →
      S.E.proposer (c + 1 + 1) = (S.node u).val_index → j = p := by
    intro j u _hu hev heq
    rw [S.node_val_index u] at heq
    subst heq
    exact w4b_eventIndex_unique adm.nodup hev hpevent
  obtain ⟨End2, hlow2, hhigh2, hstate2⟩ :=
    MovingFrontierChainStateN.through_constantEndpoint_named_public S hstate
      (by rw [hconst]; exact Block.preceq_self _) hrun hcfp (by
      intro j hj hjp
      refine movingSlotWindowTail_eventFacts_named_public S adm
        (Block.preceq_self E) ?_ hj (hjp.trans hpcn)
      intro u hu hev heq
      exact absurd (hpUnique j u hu hev heq) (Nat.ne_of_lt hjp))
  have hEnd2p : End2 p = E := by
    rcases Nat.eq_or_lt_of_le hcfp with heq | hlt
    · rw [← heq, hlow2 _ (Nat.le_refl _), hconst]
    · exact hhigh2 p hlt
  obtain ⟨End3, hlow3, hval3, hstate3⟩ :=
    w4b_succ_proposalInstant_named S adm hstate2 hpevent
      (by rw [hEnd2p]; exact hNextP) ⟨P, rfl, hPrun⟩ (fun _ =>
        ⟨by rw [hEnd2p]; exact hparent, P, hP, Block.preceq_self _⟩)
  obtain ⟨End4, hlow4, hhigh4, hstate4⟩ :=
    MovingFrontierChainStateN.through_constantEndpoint_named_public S hstate3
      (by rw [hval3]; exact Block.preceq_self _) ⟨P, rfl, hPrun⟩
      (Nat.succ_le_of_lt hpcn) (by
      intro j hj hjn
      refine movingSlotWindowTail_eventFacts_named_public S adm
        (Block.preceq_self P.erase) ?_ (hcfp.trans (Nat.le_of_succ_le hj)) hjn
      intro u hu hev heq
      exact absurd (hpUnique j u hu hev heq) (by omega))
  refine ⟨P, hP, End4, hstate4, ?_, ?_⟩
  · rw [hlow4 sn (hsnp.trans (Nat.le_succ p)), hlow3 sn hsnp]
    rcases Nat.eq_or_lt_of_le hcfsn with heq | hlt
    · rw [← heq, hlow2 _ (Nat.le_refl _), hconst]
    · exact hhigh2 sn hlt
  · by_cases hcase : p + 1 < cn
    · rw [hhigh4 cn hcase]
    · have hcneq : cn = p + 1 := by omega
      rw [hcneq, hlow4 (p + 1) (Nat.le_refl _), hval3]

#print axioms movingBoundaryHistoryN_toProposal_honest

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
