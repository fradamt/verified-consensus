module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.MovingChainHandoffBase
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainRoundRead
public import DecoupledConsensusProofs.Objects.MovingChainStep
public import DecoupledConsensusProofs.Protocol.Schedule.GSTZeroActionHead
public import DecoupledConsensusProofs.Execution.W4HandoffStructures
public import DecoupledConsensusProofs.Protocol.Schedule.ActionStoreHeadsResolve
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalAdoptionNamedClosed
public import DecoupledConsensusProofs.Protocol.ChainState.RecurringFinality
public import DecoupledConsensusProofs.Protocol.Grades.LifecycleActionSource
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.RecoverySourceProgress
public import DecoupledConsensusProofs.Generic.CanonicalSuffix
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionConfirmationCore
public import DecoupledConsensusProofs.Protocol.Schedule.PostHealingContinuation
public import DecoupledConsensusProofs.Protocol.Grades.GoldfishConePersistence
public import DecoupledConsensusProofs.Protocol.ChainState.CarrierAlignment
public import DecoupledConsensusProofs.Protocol.Store.WeakSGHistory
public import DecoupledConsensusProofs.Protocol.ChainState.CanonicalDensity

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 0. Timing helpers

Copied verbatim from `MovingChainExecutionRun.lean:56-64, 66-85, 363-385`
(all `private` there). -/

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

private theorem int_add_le_add_right {a b d : Int}
    (hab : a ≤ b) : a + d ≤ b + d :=
  by simpa only [Int.add_comm] using add_le_add_left hab d

/-- Copied from `MovingChainExecutionRun.lean:103` (`private` there). -/
private theorem confirmation_time_mono_exec (E : Env V) {a b : Slot}
    (hab : a ≤ b) :
    Protocol.confirmation_time E a ≤ Protocol.confirmation_time E b := by
  rw [confirmation_time_normal, confirmation_time_normal]
  apply int_mul_le_mul_pos _ E.Δ_pos
  exact int_add_le_add_right (by exact_mod_cast Nat.mul_le_mul_left 4 hab)

private theorem view_freeze_normal (E : Env V) (s : Slot) :
    Protocol.view_freeze E s = (4 * (s : Time) + 3) * E.Δ := by
  unfold Protocol.view_freeze Env.t slotStart
  ring

private theorem vote_time_lt_support_cutoff_local
    (E : Env V) (s : Slot) :
    Protocol.vote_time E s < Protocol.support_cutoff E s := by
  rw [vote_time_normal, support_cutoff_normal]
  apply int_mul_lt_mul_pos _ E.Δ_pos
  omega

private theorem view_freeze_lt_proposal_succ
    (E : Env V) (s : Slot) :
    Protocol.view_freeze E s < Protocol.proposal_time E (s + 1) := by
  rw [view_freeze_normal, proposal_time_normal]
  apply int_mul_lt_mul_pos _ E.Δ_pos
  have hcast : (((s + 1 : Nat) : Int)) = (s : Int) + 1 := by
    push_cast
    rfl
  rw [hcast]
  omega

private theorem support_cutoff_le_view_freeze_local
    (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s ≤ Protocol.view_freeze E s := by
  rw [support_cutoff_normal, view_freeze_normal]
  apply int_mul_le_mul_pos _ E.Δ_pos
  omega



/-- The public suffix cursor is at or before the moving history's start. -/
theorem lastSuffixStart_le_movingStart
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} {nB : Nat}
    (hstart : SuffixStartsAfterBoundaryVote S rho
      (healingBoundaryTime S q) nB) :
    nB ≤ strictEventIndex rho
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) := by
  rcases hstart with
    ⟨v, s, i, _hv, _hcommittee, _hs, htime, hevent, rfl⟩
  have hi : i < strictEventIndex rho
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) := by
    by_contra hnot
    have hfalse := Proofs.Optimistic.filter_false_of_index_ge
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed _
      (Proofs.Optimistic.downward_lt
        (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)))
      (by simpa only [strictEventIndex] using Nat.le_of_not_gt hnot) hevent
    have hbefore : healingBoundaryTime S q <
        Protocol.support_cutoff S.E (S.hc.opening_slot q + 2) := by
      exact vote_time_lt_support_cutoff_local S.E
        (S.hc.opening_slot q + 2)
    simp only [decide_eq_false_iff_not, Event.time] at hfalse
    exact hfalse (by simpa only [htime] using hbefore)
  exact Nat.succ_le_iff.mpr hi

/-- Every tick between the public cursor and the moving history's start is at
the boundary vote instant itself. -/
theorem boundaryPrefix_tick_time_eq
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} {nB j : Nat} {u : V} {t : Time}
    (hstart : SuffixStartsAfterBoundaryVote S rho
      (healingBoundaryTime S q) nB)
    (hj : nB ≤ j)
    (hhigh : j < strictEventIndex rho
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)))
    (hevent : rho.events[j]? = some (Event.tick u t)) :
    t = healingBoundaryTime S q := by
  let s0 := S.hc.opening_slot q + 2
  have hmem : Event.tick u t ∈ rho.events := List.mem_of_getElem? hevent
  have hpub : PublicTime S t := adm.tick_public u t hmem
  have hlow : healingBoundaryTime S q ≤ t :=
    SuffixStartsAfterBoundaryVote.time_le_of_index
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hstart hj hevent
  have hupper : t < Protocol.support_cutoff S.E s0 := by
    simpa only [s0, Event.time] using
      time_lt_of_index_lt_strictEventIndex S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hhigh hevent
  have hgt : Protocol.proposal_time S.E s0 < t :=
    (Protocol.proposal_time_lt_vote_time S.E s0).trans_le (by
      simpa only [healingBoundaryTime, s0] using hlow)
  have hleNext : t ≤ Protocol.proposal_time S.E (s0 + 1) :=
    (le_of_lt hupper).trans
      ((support_cutoff_le_view_freeze_local S.E s0).trans
        (le_of_lt (view_freeze_lt_proposal_succ S.E s0)))
  rcases publicTime_slotWindow_cases S hpub hgt hleNext
    with ht | ht | ht | ht
  · simpa only [healingBoundaryTime, s0] using ht
  · exact absurd (ht ▸ hupper) (lt_irrefl _)
  · exact absurd hupper (not_lt_of_ge (by
      rw [ht]
      exact support_cutoff_le_view_freeze_local S.E s0))
  · exact absurd hupper (not_lt_of_ge (by
      rw [ht]
      exact (support_cutoff_le_view_freeze_local S.E s0).trans
        (le_of_lt (view_freeze_lt_proposal_succ S.E s0))))

/-- No proposal-chain observation happens strictly inside the boundary prefix. -/
theorem boundaryPrefix_noProposalChainObservation
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} {nB j stage : Nat} {B : Block V}
    (hstart : SuffixStartsAfterBoundaryVote S rho
      (healingBoundaryTime S q) nB)
    (hlast : ∀ j v,
      v ∈ rho.honest →
      v ∈ S.E.committee (S.hc.opening_slot q + 2) →
      rho.events[j]? = some
        (Event.tick v (healingBoundaryTime S q)) →
      j < nB)
    (hj : nB ≤ j)
    (hhigh : j < strictEventIndex rho
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)))
    (hstage : ProposalChainStage stage)
    (hobs : HonestCanonicalObservationAtIndex S rho j stage B) : False := by
  let s0 := S.hc.opening_slot q + 2
  cases hobs with
  | @proposalParent v t hv hevent hactive =>
      have ht := boundaryPrefix_tick_time_eq S adm hstart hj hhigh hevent
      have hbad : Protocol.vote_time S.E s0 =
          Protocol.proposal_time S.E s0 := by
        simpa only [ht, healingBoundaryTime, s0,
          Proofs.Optimistic.slotOf_vote_time] using hactive.2.1
      exact (Proofs.Optimistic.vote_time_ne_proposal_time S.E s0 hbad).elim
  | @proposedBlock v t P hv hevent hactive _hcomputed =>
      have ht := boundaryPrefix_tick_time_eq S adm hstart hj hhigh hevent
      have hbad : Protocol.vote_time S.E s0 =
          Protocol.proposal_time S.E s0 := by
        simpa only [ht, healingBoundaryTime, s0,
          Proofs.Optimistic.slotOf_vote_time] using hactive.2.1
      exact (Proofs.Optimistic.vote_time_ne_proposal_time S.E s0 hbad).elim
  | @voteHead v t u hv hevent hactive _hprop hcommittee _hcomputed =>
      have ht := boundaryPrefix_tick_time_eq S adm hstart hj hhigh hevent
      have hslot : S.E.slotOf t = s0 := by
        rw [ht, healingBoundaryTime, Proofs.Optimistic.slotOf_vote_time]
      have hcommittee' : v ∈ S.E.committee
          (S.hc.opening_slot q + 2) := by
        simpa only [S.node_val_index, hslot, s0] using hcommittee
      have hevent' : rho.events[j]? = some
          (Event.tick v (healingBoundaryTime S q)) := by
        simpa only [ht] using hevent
      exact (Nat.not_lt_of_ge hj) (hlast j v hv hcommittee' hevent')
  | confirmationOutput =>
      simp only [ProposalChainStage] at hstage
      omega
  | actionHead =>
      simp only [ProposalChainStage] at hstage
      omega

/-- No honest attestation is emitted strictly inside the boundary prefix. -/
theorem boundaryPrefix_noHonestAttestationEmission
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} {nB j : Nat}
    (hstart : SuffixStartsAfterBoundaryVote S rho
      (healingBoundaryTime S q) nB)
    (hj : nB ≤ j)
    (hhigh : j < strictEventIndex rho
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2))) :
    ¬ HonestAttestationEmissionAtIndex S rho j := by
  rintro ⟨v, time, a, _hv, hevent, ha⟩
  have ht := boundaryPrefix_tick_time_eq S adm hstart hj hhigh hevent
  have hemit := Protocol.emits_of_emittedAt_tick S hevent ha
  obtain ⟨r, haction⟩ := Proofs.Optimistic.a_of_attest_mem S hemit
  apply Proofs.Optimistic.a_ne_vote_time S haction
  rw [ht, healingBoundaryTime, Proofs.Optimistic.slotOf_vote_time]




#print axioms lastSuffixStart_le_movingStart
#print axioms boundaryPrefix_tick_time_eq
#print axioms boundaryPrefix_noProposalChainObservation
#print axioms boundaryPrefix_noHonestAttestationEmission




theorem canonicalSuffixAndActionHistory_of_completeN
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} {M0 : Height} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
      (strictEventIndex rho
        (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)))
      rho.events.length End)
    {nB : Nat}
    (hstart : SuffixStartsAfterBoundaryVote S rho
      (healingBoundaryTime S q) nB)
    (hlast : ∀ j v,
      v ∈ rho.honest →
      v ∈ S.E.committee (S.hc.opening_slot q + 2) →
      rho.events[j]? = some
        (Event.tick v (healingBoundaryTime S q)) →
      j < nB)
    (_hnBM : nB ≤ strictEventIndex rho
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2))) :
    CanonicalSuffixFrom S rho (healingBoundaryTime S q) ∧
      Nonempty (CanonicalSuffixActionHistory S rho q) := by
  classical
  let nM := strictEventIndex rho
    (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2))
  let nC := rho.events.length
  let End' : Nat → Block V := fun j =>
    if j < nM then End nM else End (min j nC)
  have hstartComplete : nM ≤ nC := by
    simpa only [nM, nC] using h.start_le
  have hrunEx : ∀ j : Nat, nB ≤ j →
      ∃ E : NamedBlock V, E.erase = End' j ∧ RunBlock S rho E := by
    intro j _hj
    by_cases hjM : j < nM
    · rw [show End' j = End nM by simp only [End', if_pos hjM]]
      exact h.endpointRun nM (by simpa only [nM] using Nat.le_refl nM)
        (by simpa only [nM, nC] using hstartComplete)
    · have hnMj : nM ≤ j := Nat.le_of_not_gt hjM
      have hminLower : nM ≤ min j nC := le_min hnMj hstartComplete
      rw [show End' j = End (min j nC) by simp only [End', if_neg hjM]]
      exact h.endpointRun (min j nC)
        (by simpa only [nM] using hminLower)
        (by simpa only [nC] using min_le_right j nC)
  have hchoice : ∀ j : Nat, ∃ E : NamedBlock V,
      nB ≤ j → (E.erase = End' j ∧ RunBlock S rho E) := by
    intro j
    by_cases hj : nB ≤ j
    · obtain ⟨E, he, hr⟩ := hrunEx j hj
      exact ⟨E, fun _ => ⟨he, hr⟩⟩
    · exact ⟨NamedBlock.genesis, fun hcon => absurd hcon hj⟩
  choose EndN hEndN using hchoice
  have hmono : ∀ j k : Nat, nB ≤ j → j ≤ k →
      Block.Preceq (End' j) (End' k) := by
    intro j k hj hjk
    by_cases hjM : j < nM
    · by_cases hkM : k < nM
      · simp only [End', if_pos hjM, if_pos hkM]
        exact Block.preceq_self _
      · have hnMk : nM ≤ k := Nat.le_of_not_gt hkM
        have hminLower : nM ≤ min k nC := le_min hnMk hstartComplete
        simp only [End', if_pos hjM, if_neg hkM]
        exact h.endpoint_mono
          (by simpa only [nM] using Nat.le_refl nM)
          (by simpa only [nM] using hminLower)
          (by simpa only [nC] using min_le_right k nC)
    · have hnMj : nM ≤ j := Nat.le_of_not_gt hjM
      have hkM : ¬ k < nM := Nat.not_lt_of_ge (hnMj.trans hjk)
      have hminLower : nM ≤ min j nC := le_min hnMj hstartComplete
      have hminMono : min j nC ≤ min k nC := min_le_min_right nC hjk
      simp only [End', if_neg hjM, if_neg hkM]
      exact h.endpoint_mono
        (by simpa only [nM] using hminLower) hminMono
        (by simpa only [nC] using min_le_right k nC)
  have hsandwich : ∀ j stage : Nat, ∀ B : Block V,
      nB ≤ j → ProposalChainStage stage →
      HonestCanonicalObservationAtIndex S rho j stage B →
      Block.Preceq (End' j) B ∧ Block.Preceq B (End' (j + 1)) := by
    intro j stage B hj hstage hobs
    by_cases hjM : j < nM
    · exact False.elim (boundaryPrefix_noProposalChainObservation
        S adm hstart hlast hj (by simpa only [nM] using hjM) hstage hobs)
    · have hnMj : nM ≤ j := Nat.le_of_not_gt hjM
      by_cases hjC : j < nC
      · have hjmin : min j nC = j := min_eq_left (Nat.le_of_lt hjC)
        have hjsC : j + 1 ≤ nC := Nat.succ_le_iff.mpr hjC
        have hjsmin : min (j + 1) nC = j + 1 := min_eq_left hjsC
        have hjsM : ¬ j + 1 < nM :=
          Nat.not_lt_of_ge (hnMj.trans (Nat.le_succ j))
        simpa only [End', if_neg hjM, if_neg hjsM, hjmin, hjsmin] using
          h.proposalChain j (by simpa only [nM] using hnMj)
            (by simpa only [nC] using hjC) stage B hstage hobs
      · have hlength : rho.events.length ≤ j := by
          simpa only [nC] using Nat.le_of_not_gt hjC
        cases hobs with
        | proposalParent _ hevent _ =>
            rw [List.getElem?_eq_none hlength] at hevent
            cases hevent
        | proposedBlock _ hevent _ _ =>
            rw [List.getElem?_eq_none hlength] at hevent
            cases hevent
        | voteHead _ hevent _ _ _ _ =>
            rw [List.getElem?_eq_none hlength] at hevent
            cases hevent
        | confirmationOutput _ hevent _ =>
            rw [List.getElem?_eq_none hlength] at hevent
            cases hevent
        | actionHead _ hevent _ =>
            rw [List.getElem?_eq_none hlength] at hevent
            cases hevent
  have hsuffix : CanonicalSuffixFrom S rho (healingBoundaryTime S q) := by
    refine canonicalSuffixFrom_of_sandwich S (End := EndN) hstart
      (fun i hi => (hEndN i hi).2) ?_ ?_
    · intro i j hi hij
      rw [(hEndN i hi).1, (hEndN j (hi.trans hij)).1]
      exact hmono i j hi hij
    · intro j stage B hj hstage hobs
      rw [(hEndN j hj).1, (hEndN (j + 1) (hj.trans (Nat.le_succ j))).1]
      exact hsandwich j stage B hj hstage hobs
  let haction : CanonicalSuffixActionHistory S rho q :=
    { n0 := nB
      endpoint := End'
      starts := hstart
      endpointNamed := fun i hi => ⟨EndN i, (hEndN i hi).1, (hEndN i hi).2⟩
      endpointMono := fun j hj => hmono j (j + 1) hj (Nat.le_succ j)
      actionOutput := by
        intro j hj
        by_cases hjM : j < nM
        · exact honestAttestationOutputPreceqAtIndex_of_no_emission S rho
            (boundaryPrefix_noHonestAttestationEmission S adm hstart hj
              (by simpa only [nM] using hjM))
        · have hnMj : nM ≤ j := Nat.le_of_not_gt hjM
          by_cases hjC : j < nC
          · have hjsC : j + 1 ≤ nC := Nat.succ_le_iff.mpr hjC
            have hjsmin : min (j + 1) nC = j + 1 := min_eq_left hjsC
            have hjsM : ¬ j + 1 < nM :=
              Nat.not_lt_of_ge (hnMj.trans (Nat.le_succ j))
            simpa only [End', if_neg hjsM, hjsmin] using
              h.outputs j (by simpa only [nM] using hnMj)
                (by simpa only [nC] using hjC)
          · have hlength : rho.events.length ≤ j := by
              simpa only [nC] using Nat.le_of_not_gt hjC
            refine honestAttestationOutputPreceqAtIndex_of_no_emission S rho ?_
            rintro ⟨v, time, a, _hv, hevent, _ha⟩
            rw [List.getElem?_eq_none hlength] at hevent
            cases hevent }
  exact ⟨hsuffix, ⟨haction⟩⟩

#print axioms lastSuffixStart_le_movingStart
#print axioms boundaryPrefix_tick_time_eq
#print axioms boundaryPrefix_noProposalChainObservation
#print axioms boundaryPrefix_noHonestAttestationEmission

#print axioms canonicalSuffixAndActionHistory_of_completeN











/-- `names` from the head equality. Every honest committee member's emitted
Goldfish vote names its own vote-duty head, so a head equality at the slot is
already the named vote-name fact. This is the step the corresponding branch runs inside its
deliverable 2, isolated. -/
theorem namedHonestVotesName_of_voteDutyHead_eq
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hs : 0 < s)
    (hhor : Protocol.vote_time S.E s ≤ rho.horizon)
    {B : NamedBlock V}
    (hheads : ∀ v ∈ rho.honest, voteDutyHead S rho v s = B.erase) :
    NamedHonestVotesName S rho s B.erase := by
  intro w hw hcommittee
  obtain ⟨X, hXhead, _hXrun, hXemit⟩ :=
    voteDutyHead_runBlock_and_emits S adm hs hhor hw hcommittee
  have hXB : X.erase = B.erase := hXhead.trans (hheads w hw)
  simpa only [hXB] using hXemit

#print axioms namedHonestVotesName_of_voteDutyHead_eq


/-- Pin: the general-slot head equality at every strictly post-boundary honest
proposal (the corresponding branch / w4-gs1,
`W4GeneralSlotAdoptionRun.honestProposal_voterHeadAt_eq_after_SG_healing_named_slot`,
whose one premise `_of_sourceAnchor` the corresponding branch is closing in
`FixedHeightRootOpeningParentRun`).

Stated boundary-relative rather than deadline-relative, because that is the
shape the `duty` field quantifies over. The spine supplies the bridge: its own
`fgSafetyProgressDeadline S rho (fixedPostGSTRound S) gap extra + 3 ≤ q`
(`W4RecoverySpinePin`) puts every slot after `healingBoundaryTime S q` past the
deadline gs1's theorem needs. -/
def W4SlotHeadEqualityPin (S : Setup V) (rho : Run V) (q : Round) : Prop :=
  ∀ s : Slot, 0 < s →
    healingBoundaryTime S q < Protocol.proposal_time S.E s →
    S.E.proposer s ∈ rho.honest →
    Protocol.confirmation_time S.E s ≤ rho.horizon →
    ∀ B : NamedBlock V, proposedBlockAt S rho s = some B →
      ∀ v ∈ rho.honest, voteDutyHead S rho v s = B.erase


/-- Pin: the four general-slot confirmation-read facts (the corresponding branch), in the
exact shapes `Protocol.CanonicalSuffixProposalStoreFacts` asks for. -/
def W4SlotConfirmationReadPin (S : Setup V) (rho : Run V) (q : Round) : Prop :=
  ∀ s : Slot, 0 < s →
    healingBoundaryTime S q < Protocol.proposal_time S.E s →
    S.E.proposer s ∈ rho.honest →
    Protocol.confirmation_time S.E s ≤ rho.horizon →
    ∀ B : NamedBlock V, proposedBlockAt S rho s = some B →
      (∀ v ∈ rho.honest,
        Protocol.VoteSetValid S.E s
          (confLate S.E (Proofs.Optimistic.confStore S rho v s) s)) ∧
      (∀ v ∈ rho.honest,
        Block.Preceq
          (Internal.namedConfirmationAnchor S
            (Internal.NamedRecoveryRead.confirmationInputRead S rho v s))
          B.erase) ∧
      (∀ v ∈ rho.honest,
        B.erase ∈ Protocol.confTree (Proofs.Optimistic.confStore S rho v s)) ∧
      (∀ v ∈ rho.honest,
        Proofs.Optimistic.HeadsResolveIn S rho s
          (Proofs.Optimistic.confStore S rho v s).T
          (Proofs.Optimistic.confStore S rho v s).timestamp_block)

/-- The per-slot store-fact record, from the two slot pins. -/
theorem canonicalSuffixProposalStoreFacts_of_slotPins
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round}
    (hheadEq : W4SlotHeadEqualityPin S rho q)
    (hreads : W4SlotConfirmationReadPin S rho q)
    {s : Slot} (hs : 0 < s)
    (hafter : healingBoundaryTime S q < Protocol.proposal_time S.E s)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B) :
    Protocol.CanonicalSuffixProposalStoreFacts S rho s B := by
  obtain ⟨hvalidLate, hanchor, hcandidate, hresolve⟩ :=
    hreads s hs hafter hprop hhor B hB
  have hvoteHor : Protocol.vote_time S.E s ≤ rho.horizon :=
    (Protocol.vote_time_le_confirmation_time S.E s).trans hhor
  exact
    { run := Protocol.proposedBlock_runBlock S adm hs hprop
        ((Protocol.proposal_time_le_confirmation_time S.E s).trans hhor) hB
      names := namedHonestVotesName_of_voteDutyHead_eq S adm hs hvoteHor
        (hheadEq s hs hafter hprop hhor B hB)
      validLate := hvalidLate
      anchor := hanchor
      candidate := hcandidate
      resolve := hresolve }

#print axioms canonicalSuffixProposalStoreFacts_of_slotPins

/-- Route D's `duty` field: `CanonicalProposalDutyAt` at every strictly
post-boundary honest proposal, from the two slot pins and post-GST. -/
theorem canonicalProposalDutyAt_of_slotPins
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round}
    (hheadEq : W4SlotHeadEqualityPin S rho q)
    (hreads : W4SlotConfirmationReadPin S rho q)
    (hpostGST : ∀ s : Slot,
      healingBoundaryTime S q < Protocol.proposal_time S.E s →
      S.E.t_GST ≤ Protocol.vote_time S.E s)
    {s : Slot} (hs : 0 < s)
    (hafter : healingBoundaryTime S q < Protocol.proposal_time S.E s)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B) :
    Protocol.CanonicalProposalDutyAt S rho s B :=
  Protocol.CanonicalSuffixProposalStoreFacts.duty adm hs
    (hpostGST s hafter) hhor
    (canonicalSuffixProposalStoreFacts_of_slotPins S adm hheadEq hreads hs
      hafter hprop hhor hB)

#print axioms canonicalProposalDutyAt_of_slotPins














/-- The deadline bridge, shared by §7 and §9. A slot strictly after the
boundary of a round that is itself at least three past the SG-healing deadline
is at or after the deadline-plus-two opening slot. -/
private theorem openingSlotDeadline_le_of_boundary
    (S : Setup V) {rho : Run V} {rGST gap : Round} {delayExtra : Nat}
    {q : Round} {t : Slot}
    (hq : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ q)
    (hafter : healingBoundaryTime S q <
      Protocol.proposal_time S.E (t + 1)) :
    S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤ t := by
  have hslotGt : S.hc.opening_slot q + 2 < t + 1 := by
    by_contra hnot
    have hle : t + 1 ≤ S.hc.opening_slot q + 2 := Nat.le_of_not_gt hnot
    have hmono : Protocol.proposal_time S.E (t + 1) ≤
        Protocol.proposal_time S.E (S.hc.opening_slot q + 2) :=
      Protocol.proposal_time_mono S.E hle
    have hlt : Protocol.proposal_time S.E (S.hc.opening_slot q + 2) <
        Protocol.proposal_time S.E (t + 1) := by
      refine lt_of_lt_of_le ?_ (le_of_lt hafter)
      simpa only [healingBoundaryTime] using
        Protocol.proposal_time_lt_vote_time S.E
          (S.hc.opening_slot q + 2)
    exact absurd (hmono.trans_lt hlt) (lt_irrefl _)
  have hdq : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ q :=
    (Nat.le_succ _).trans hq
  have hopenMono : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤
      S.hc.opening_slot q := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_le_mul_right S.hc.R hdq
  exact hopenMono.trans
    ((Nat.le_add_right _ 2).trans (Nat.lt_succ_iff.mp hslotGt))


/-- The boundary-relative head equality, from the corresponding branch's deadline-relative
one and the spine's deadline bound. -/
theorem w4SlotHeadEqualityPin_of_adoption
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} {delayExtra : Nat}
    (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {q : Round}
    (hq : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ q) :
    W4SlotHeadEqualityPin S rho q := by
  intro s hs hafter hprop hhor B hB
  obtain ⟨t, rfl⟩ : ∃ t : Slot, s = t + 1 :=
    ⟨s - 1, (Nat.succ_pred_eq_of_pos hs).symm⟩
  have hround2 : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤ t + 1 :=
    (openingSlotDeadline_le_of_boundary S hq hafter).trans (Nat.le_succ t)
  have hvoteHor : Protocol.vote_time S.E (t + 1) ≤ rho.horizon :=
    (Protocol.vote_time_le_confirmation_time S.E (t + 1)).trans hhor
  exact honestProposal_voterHeadAt_eq_after_SG_healing_named_slot S adm hcom
    hbelow hrec hdelay hpost hround2 hvoteHor hprop hB

#print axioms w4SlotHeadEqualityPin_of_adoption



/-- Prepared twin of `Protocol.CanonicalSuffixExecution`: the same record
with the opening-proposal head bound read at the prepared read's own contract.
Additive; there is no conversion either way. -/
structure CanonicalSuffixExecutionPrepared
    (S : Setup V) (rho : Run V) (q : Round) : Prop where
  canonicalSuffixFrom :
    CanonicalSuffixFrom S rho (healingBoundaryTime S q)
  actionHistory : Nonempty (CanonicalSuffixActionHistory S rho q)
  duty : ∀ s : Slot, 0 < s →
    healingBoundaryTime S q < Protocol.proposal_time S.E s →
    S.E.proposer s ∈ rho.honest →
    Protocol.confirmation_time S.E s ≤ rho.horizon →
    ∀ B : NamedBlock V, proposedBlockAt S rho s = some B →
      Protocol.CanonicalProposalDutyAt S rho s B
  openingProposalPreceqActionHeadAt : ∀ {r : Round},
    0 < S.hc.opening_slot r →
    healingBoundaryTime S q <
      Protocol.proposal_time S.E (S.hc.opening_slot r) →
    S.E.proposer (S.hc.opening_slot r) ∈ rho.honest →
    S.a r ≤ rho.horizon →
    ∀ B : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r) = some B →
      ∀ v ∈ rho.honest,
        Block.Preceq B.erase (actionHeadAt S rho v r)



/-- The field's single consumer, restated over the prepared twin.

`canonicalOpeningLifecycleAt_of_execution`
(`CanonicalCarrierRegimeRun.lean:79`) is the only place in the tree that reads
`openingProposalPreceqActionHead` (the judgment's projection count: 1). Its
first conjunct reads `duty`, which the twin shares, so only the second conjunct
moves to `actionHeadAt`. The original is left in place; this is an additive
twin. -/
theorem canonicalOpeningLifecycleAt_of_executionPrepared
    (S : Setup V) {rho : Run V}
    (hcom : HonestCommittees S rho.honest)
    {q r : Round} (hexec : CanonicalSuffixExecutionPrepared S rho q)
    (hafter : healingBoundaryTime S q <
      Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hprop : S.E.proposer (S.hc.opening_slot r) ∈ rho.honest)
    (hhor : S.a r ≤ rho.horizon) :
    ∀ P : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r) = some P →
      ∀ v ∈ rho.honest,
        (actionStoreAt S rho v r).st.core.live_confirmed = P.erase ∧
          Block.Preceq P.erase (actionHeadAt S rho v r) := by
  have hopen : 0 < S.hc.opening_slot r := by
    by_contra hnot
    have heq : S.hc.opening_slot r = 0 := Nat.eq_zero_of_not_pos hnot
    have hproposalBoundary :
        Protocol.proposal_time S.E (S.hc.opening_slot r) <
          healingBoundaryTime S q := by
      rw [heq]
      unfold healingBoundaryTime
      exact lt_of_lt_of_le (Protocol.proposal_time_lt_vote_time S.E 0)
        (vote_time_mono_slots S.E (Nat.zero_le _))
    exact (lt_asymm hafter) hproposalBoundary
  have hconfirmHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r) ≤ rho.horizon := by
    simpa only [Setup.a, Protocol.a_eq_confirmation_time] using hhor
  have hduty := hexec.duty (S.hc.opening_slot r) hopen hafter
    hprop hconfirmHor
  intro P hP v hv
  have hwrite :=
    Protocol.updateConfirmation_eq_proposedBlock_of_dutyExecution
      S hcom (hduty P hP) hv
  refine ⟨?_, hexec.openingProposalPreceqActionHeadAt
    hopen hafter hprop hhor P hP v hv⟩
  change (actionStoreAt S rho v r).st.core.live_confirmed = P.erase
  rw [actionStoreAt_eq_update_confirmation_openingConfStore S rho v r]
  simpa only [Proofs.Optimistic.confStore_eq_confirmationInputRead] using hwrite

#print axioms canonicalOpeningLifecycleAt_of_executionPrepared




/-- Pin: the two confirmation-store facts the corresponding branch's read pair does not
give. Same quantification as `W4SlotConfirmationReadPin`. -/
def W4SlotLateResolvePin (S : Setup V) (rho : Run V) (q : Round) : Prop :=
  ∀ s : Slot, 0 < s →
    healingBoundaryTime S q < Protocol.proposal_time S.E s →
    S.E.proposer s ∈ rho.honest →
    Protocol.confirmation_time S.E s ≤ rho.horizon →
    ∀ B : NamedBlock V, proposedBlockAt S rho s = some B →
      (∀ v ∈ rho.honest,
        Protocol.VoteSetValid S.E s
          (confLate S.E (Proofs.Optimistic.confStore S rho v s) s)) ∧
      (∀ v ∈ rho.honest,
        Proofs.Optimistic.HeadsResolveIn S rho s
          (Proofs.Optimistic.confStore S rho v s).T
          (Proofs.Optimistic.confStore S rho v s).timestamp_block)


/-- `W4SlotConfirmationReadPin` from the corresponding branch's read pair and the two facts
it does not cover. -/
theorem w4SlotConfirmationReadPin_of_adoption
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} {delayExtra : Nat}
    (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {q : Round}
    (hq : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ q)
    (hlateResolve : W4SlotLateResolvePin S rho q) :
    W4SlotConfirmationReadPin S rho q := by
  intro s hs hafter hprop hhor B hB
  obtain ⟨hvalidLate, hresolve⟩ := hlateResolve s hs hafter hprop hhor B hB
  obtain ⟨t, rfl⟩ : ∃ t : Slot, s = t + 1 :=
    ⟨s - 1, (Nat.succ_pred_eq_of_pos hs).symm⟩
  have hd : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤ t :=
    openingSlotDeadline_le_of_boundary S hq hafter
  have hpair := honestProposal_confirmationReadFacts_after_SG_healing_named_slot
    S adm hcom hbelow hrec hdelay hpost hd hhor hprop hB
  refine ⟨hvalidLate, fun v hv => (hpair v hv).1, fun v hv => ?_, hresolve⟩
  simpa only [Proofs.Optimistic.confStore_eq_confirmationInputRead] using (hpair v hv).2

#print axioms w4SlotConfirmationReadPin_of_adoption



/-- Copied from `Availability/PostHealingProposalLifecycleRun.lean:24`
(`private` there). -/
private theorem tickIndex_lt_of_time_lt_suffix
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {i j : Nat} {v w : V} {t u : Time}
    (hi : rho.events[i]? = some (Event.tick v t))
    (hj : rho.events[j]? = some (Event.tick w u))
    (htu : t < u) :
    i < j := by
  by_contra hnot
  have hji : j ≤ i := Nat.le_of_not_gt hnot
  rcases lt_or_eq_of_le hji with hji | hji
  · have hkey := Proofs.Optimistic.key_le_of_index_lt S sch hji hj hi
    have htime := Proofs.Bridges.time_le_of_key_le hkey
    simp only [Event.time] at htime
    exact (not_le_of_gt htu) htime
  · subst j
    have hevent : Event.tick v t = Event.tick w u :=
      Option.some.inj (hi.symm.trans hj)
    have htime : t = u := by
      simpa only [Event.time] using congrArg Event.time hevent
    exact (ne_of_lt htu) htime

/-- Field-level restatement of
`Protocol.proposedBlock_preceq_of_canonicalSuffixExecution`: it reads only
`canonicalSuffixFrom`, so stating it over that field serves both records and no
twin is needed. -/
theorem proposedBlock_preceq_of_canonicalSuffixFrom
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round}
    (hsuffix : CanonicalSuffixFrom S rho (healingBoundaryTime S q))
    {s u : Slot} (hs : 0 < s) (hu : 0 < u)
    (hafter : healingBoundaryTime S q < Protocol.proposal_time S.E s)
    (hpropS : S.E.proposer s ∈ rho.honest)
    (hpropU : S.E.proposer u ∈ rho.honest)
    {P Q : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P)
    (hQ : proposedBlockAt S rho u = some Q)
    (hemitS : rho.emits S (S.E.proposer s) (Object.block P)
      (Protocol.proposal_time S.E s))
    (hemitU : rho.emits S (S.E.proposer u) (Object.block Q)
      (Protocol.proposal_time S.E u))
    (htime : Protocol.proposal_time S.E s ≤
      Protocol.proposal_time S.E u) :
    Block.Preceq P.erase Q.erase := by
  by_cases heq : Protocol.proposal_time S.E s =
      Protocol.proposal_time S.E u
  · have hsu : s = u := by
      have hslot := congrArg S.E.slotOf heq
      simpa only [Proofs.Optimistic.slotOf_proposal_time] using hslot
    subst hsu
    have hPQ : P = Q := Option.some.inj (hP.symm.trans hQ)
    subst hPQ
    exact Block.preceq_self _
  · have htimeLt : Protocol.proposal_time S.E s <
        Protocol.proposal_time S.E u :=
      lt_of_le_of_ne htime heq
    rcases hsuffix with ⟨n0, End, hstart, hchain⟩
    obtain ⟨i, hi, -⟩ := hemitS
    obtain ⟨j, hj, -⟩ := hemitU
    have hobsS : HonestCanonicalObservationAtIndex S rho i 1 P.erase :=
      Protocol.proposedBlock_observationAtIndex S adm hs hpropS hi hP
    have hobsU : HonestCanonicalObservationAtIndex S rho j 1 Q.erase :=
      Protocol.proposedBlock_observationAtIndex S adm hu hpropU hj hQ
    have hstartData := hstart
    obtain ⟨_, _, k, _, _, _, _, hk, hn0⟩ := hstartData
    have hki : k < i := tickIndex_lt_of_time_lt_suffix
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hk hi hafter
    have hni : n0 ≤ i := by
      rw [hn0]
      exact Nat.succ_le_of_lt hki
    have hij : i < j := tickIndex_lt_of_time_lt_suffix
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hi hj htimeLt
    exact hchain.ordered i 1 P.erase
      j 1 Q.erase
      hni (hni.trans (Nat.le_of_lt hij))
      (by simp [ProposalChainStage]) (by simp [ProposalChainStage])
      hobsS hobsU (Or.inl hij)

#print axioms proposedBlock_preceq_of_canonicalSuffixFrom

/-! ## 11. The carrier-regime readers over the prepared record
Three additive twins of `CanonicalCarrierRegimeRun`'s readers, for the spine's
D2 side. Only the first carries the head; the other two need the prepared form
solely because they make a call whose result they discard, which is why their
bodies are one line each. `canonicalCarrierActionOutput_of_execution` needs no
twin at all: it takes the record and never projects it. -/

/-- Prepared twin of `canonicalCarrierOpeningLifecycleAt_of_execution`
(`CanonicalCarrierRegimeRun.lean:123`). -/
theorem canonicalCarrierOpeningLifecycleAt_of_executionPrepared
    (S : Setup V) {rho : Run V}
    (hcom : HonestCommittees S rho.honest)
    {q r : Round} (hexec : CanonicalSuffixExecutionPrepared S rho q)
    (hafter : healingBoundaryTime S q <
      Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : S.a r ≤ rho.horizon) :
    ∀ P : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r) = some P →
      ∀ v ∈ rho.honest,
        (actionStoreAt S rho v r).st.core.live_confirmed = P.erase ∧
          Block.Preceq P.erase (actionHeadAt S rho v r) :=
  canonicalOpeningLifecycleAt_of_executionPrepared S hcom hexec hafter
    hcarrier.1 hhor

#print axioms canonicalCarrierOpeningLifecycleAt_of_executionPrepared







/-- Copied from `WeakProposalConfirmationCoreRun.lean:26` (`private` there). -/
private theorem contractAnchor_mem_filtered_slot
    (S : Setup V) (n : NamedNodeState V) (r : Round)
    (hroot : Protocol.get_fg_root n.st.core.toHealing.toFG ∈
      Protocol.get_filtered_block_tree n.st.core.toHealing.toFG) :
    Protocol.get_sg_root_with (NamedProfile.gradeContract n.cache) S.E S.hc
        n.st.core.toHealing r ∈
      Protocol.get_filtered_block_tree n.st.core.toHealing.toFG := by
  change DecoupledConsensusModel.Protocol.anchor S.E S.hc n.st.core.toHealing r
    (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g1 ∈
      Protocol.get_filtered_block_tree n.st.core.toHealing.toFG
  cases hframe :
      (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g1 with
  | none => exact hroot
  | some opt =>
      cases opt with
      | none => exact hroot
      | some root =>
          cases hactive : DecoupledConsensusModel.Protocol.activePrefix
              (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG)
              root with
          | none =>
              simpa only [DecoupledConsensusModel.Protocol.anchor, hactive,
                Option.getD_none] using hroot
          | some B =>
              simpa only [DecoupledConsensusModel.Protocol.anchor, hactive,
                Option.getD_some] using
                NamedProposalParent.activePrefix_mem _ root B hactive


/-- Copied from `WeakProposalConfirmationCoreRun.lean:56` (`private` there).
The confirmation read's FG root precedes its own contract anchor; design note, the
anchor is the prepared contract's, never the absolute `confAnchor`. -/
private theorem confRoot_preceq_namedConfirmationAnchor_slot
    (S : Setup V) (rho : Run V) (v : V) (s : Slot) :
    Block.Preceq
      (Protocol.get_fg_root (Proofs.Optimistic.confStore S rho v s).toHealing.toFG)
      (Internal.namedConfirmationAnchor S
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v s)) := by
  have hroot : Protocol.get_fg_root
      (Internal.NamedRecoveryRead.confirmationInputRead S rho v
        s).st.core.toHealing.toFG ∈
      Protocol.get_filtered_block_tree
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v
          s).st.core.toHealing.toFG := by
    simpa only [Internal.NamedRecoveryRead.confirmationInputRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using
      named_fgRoot_mem_filtered_stateBeforeTime S rho
        (Protocol.confirmation_time S.E s) v
  exact Proofs.Records.preceq_get_fg_root_of_mem_filtered
    (contractAnchor_mem_filtered_slot S
      (Internal.NamedRecoveryRead.confirmationInputRead S rho v s)
      (S.hc.round_of (Internal.NamedRecoveryRead.confirmationInputRead S rho v
        s).st.core.s) hroot)

/-- `W4SlotLateResolvePin` from the available general-slot family. -/
theorem w4SlotLateResolvePin_of_adoption
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} {delayExtra : Nat}
    (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {q : Round}
    (hq : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ q)
    (hpostGST : ∀ s : Slot,
      healingBoundaryTime S q < Protocol.proposal_time S.E s →
      S.E.t_GST ≤ Protocol.vote_time S.E s) :
    W4SlotLateResolvePin S rho q := by
  intro s hs hafter hprop hhor B hB
  obtain ⟨t, rfl⟩ : ∃ t : Slot, s = t + 1 :=
    ⟨s - 1, (Nat.succ_pred_eq_of_pos hs).symm⟩
  have hd : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤ t :=
    openingSlotDeadline_le_of_boundary S hq hafter
  have hvoteHor : Protocol.vote_time S.E (t + 1) ≤ rho.horizon :=
    (Protocol.vote_time_le_confirmation_time S.E (t + 1)).trans hhor
  have hcut : Protocol.support_cutoff S.E (t + 1) ≤ rho.horizon :=
    (Protocol.support_cutoff_le_confirmation_time S.E (t + 1)).trans hhor
  have hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E (t + 1) :=
    hpostGST (t + 1) hafter
  have hanchor := honestProposal_confirmationReadFacts_after_SG_healing_named_slot
    S adm hcom hbelow hrec hdelay hpost hd hhor hprop hB
  have hcone := honestProposal_slotVoteCone_after_SG_healing_named
    S adm hcom hbelow hrec hdelay hpost (hd.trans (Nat.le_succ t)) hvoteHor
    hprop hB
  refine ⟨fun v _hv => ?_, fun v hv => ?_⟩
  · simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using
      Protocol.voteSetValid_confLate_stateBeforeTime S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v
        (Protocol.confirmation_time S.E (t + 1)) (t + 1)
  · exact Protocol.headsResolveIn_confStore_of_postHealingCone S adm hv
      hpostVote hcut
      (Block.preceq_trans
        (confRoot_preceq_namedConfirmationAnchor_slot S rho v (t + 1))
        (hanchor v hv).1)
      hcone

#print axioms w4SlotLateResolvePin_of_adoption


/-- The `duty` field of the execution record with NO pin: the six-field
per-slot record is assembled entirely from the corresponding branch and w4-gs2's available
general-slot family and the unconditional store facts. The premises below are
the spine's own (recurrence, timeout bound, post-GST at `rGST`, and the
deadline bound `… + 3 ≤ q` that `W4RecoverySpinePin` supplies). -/
theorem canonicalProposalDutyAt_of_adoption
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} {delayExtra : Nat}
    (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {q : Round}
    (hq : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ q)
    (hpostGST : ∀ s : Slot,
      healingBoundaryTime S q < Protocol.proposal_time S.E s →
      S.E.t_GST ≤ Protocol.vote_time S.E s)
    {s : Slot} (hs : 0 < s)
    (hafter : healingBoundaryTime S q < Protocol.proposal_time S.E s)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B) :
    Protocol.CanonicalProposalDutyAt S rho s B :=
  canonicalProposalDutyAt_of_slotPins S adm
    (w4SlotHeadEqualityPin_of_adoption S adm hcom hbelow hrec hdelay hpost hq)
    (w4SlotConfirmationReadPin_of_adoption S adm hcom hbelow hrec hdelay hpost
      hq (w4SlotLateResolvePin_of_adoption S adm hcom hbelow hrec hdelay hpost
        hq hpostGST))
    hpostGST hs hafter hprop hhor hB

#print axioms canonicalProposalDutyAt_of_adoption



/-- Copied from `CanonicalCarrierConeRun.lean:113` (`private` there), with the
record premise replaced by the one field it reaches. -/
private theorem adjacentProposal_parentCone_of_canonicalSuffixFrom
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round}
    (hsuffix : CanonicalSuffixFrom S rho (healingBoundaryTime S q))
    {s : Slot} (hs : 0 < s)
    (hafter : healingBoundaryTime S q < Protocol.proposal_time S.E s)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hpropNext : S.E.proposer (s + 1) ∈ rho.honest)
    (hhor : Protocol.confirmation_time S.E (s + 1) ≤ rho.horizon)
    {P Q : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P)
    (hQ : proposedBlockAt S rho (s + 1) = some Q) :
    Block.Preceq P.erase (proposedParent S rho (s + 1)) := by
  have hsNext : 0 < s + 1 := Nat.zero_lt_succ s
  have hproposalNextHor : Protocol.proposal_time S.E (s + 1) ≤
      rho.horizon :=
    (Protocol.proposal_time_le_confirmation_time S.E (s + 1)).trans hhor
  have hproposalHor : Protocol.proposal_time S.E s ≤ rho.horizon :=
    (Protocol.proposal_time_mono S.E (Nat.le_succ s)).trans
      hproposalNextHor
  have hemit := Protocol.proposedBlock_emitted_of_admissible
    S adm hs hprop hproposalHor hP
  have hemitNext := Protocol.proposedBlock_emitted_of_admissible
    S adm hsNext hpropNext hproposalNextHor hQ
  have hblocks : Block.Preceq P.erase Q.erase :=
    proposedBlock_preceq_of_canonicalSuffixFrom
      S adm hsuffix hs hsNext hafter hprop hpropNext hP hQ hemit hemitNext
        (Protocol.proposal_time_mono S.E (Nat.le_succ s))
  have hne : P.erase ≠ Q.erase := by
    intro heq
    have hslots := congrArg Block.slot heq
    rw [Proofs.NamedWire.erase_slot, Proofs.NamedWire.erase_slot,
      proposedBlockAt_slot S rho s hP,
      proposedBlockAt_slot S rho (s + 1) hQ] at hslots
    exact (Nat.ne_of_lt (Nat.lt_succ_self s)) hslots
  have hparent : Q.erase.parent? = some (proposedParent S rho (s + 1)) := by
    obtain ⟨p, hp, hpe⟩ := proposedBlockAt_parent S rho (s + 1) hQ
    simpa only [Proofs.NamedWire.erase_parent_optional, hp, Option.map, hpe]
  exact Proofs.Optimistic.preceq_parent_of_ne hparent hblocks hne

/-- Copied from `CanonicalCarrierConeRun.lean:38` (`private` there); the record
premise is dropped because that proof binds it to `_hexec`. -/
private theorem openingSlot_pos_of_after_boundary_suffix
    (S : Setup V) {q r : Round}
    (hafter : healingBoundaryTime S q <
      Protocol.proposal_time S.E (S.hc.opening_slot r)) :
    0 < S.hc.opening_slot r := by
  by_contra hnot
  have heq : S.hc.opening_slot r = 0 := Nat.eq_zero_of_not_pos hnot
  have hproposalBoundary :
      Protocol.proposal_time S.E (S.hc.opening_slot r) <
        healingBoundaryTime S q := by
    rw [heq]
    unfold healingBoundaryTime
    exact lt_of_lt_of_le (Protocol.proposal_time_lt_vote_time S.E 0)
      (Protocol.vote_time_mono_slots S.E (Nat.zero_le _))
  exact (lt_asymm hafter) hproposalBoundary

/-- Copied from `CanonicalCarrierConeRun.lean:87` (`private` there). -/
private theorem namedProposedParent_eq_previousSlotBlock_of_preceq_suffix
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} {B : Block V} (hslot : B.slot = s)
    (hpre : Block.Preceq B (proposedParent S rho (s + 1))) :
    proposedParent S rho (s + 1) = B := by
  let H := proposedParent S rho (s + 1)
  have hH : H ∈ (rho.storeBeforeTime S (S.E.proposer (s + 1))
      (Protocol.proposal_time S.E (s + 1))).core.T := by
    simpa only [H, proposerReadAt, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using
      proposedParent_mem S rho (s + 1)
  by_contra hne
  have hne' : B ≠ H := fun h => hne h.symm
  have hlt : B.slot < H.slot :=
    Proofs.NamedSlotFreshness.slot_lt_of_preceq_ne_of_mem_storeBeforeTime S
      adm.toNamedAdmissibleCore hH hpre hne'
  have hHlt : H.slot < s + 1 :=
    Proofs.NamedSlotFreshness.block_slot_lt_of_mem_before_proposal S
      adm.toNamedAdmissibleCore (Nat.zero_lt_succ s) hH
  have hsucc : s + 1 ≤ H.slot := by
    rw [← hslot]
    exact Nat.succ_le_iff.mpr hlt
  exact (Nat.not_lt_of_ge hsucc) hHlt

/-- Field-level twin of `canonicalCarrierParentConesAt_of_execution`
(`CanonicalCarrierConeRun.lean:154`). -/
theorem canonicalCarrierParentConesAt_of_canonicalSuffixFrom
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q r : Round}
    (hsuffix : CanonicalSuffixFrom S rho (healingBoundaryTime S q))
    (hafter : healingBoundaryTime S q <
      Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon) :
    ∀ B0 : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r) = some B0 →
      CarrierParentConesAt S rho r B0 := by
  intro B0 hB0
  have hs0 : 0 < S.hc.opening_slot r :=
    openingSlot_pos_of_after_boundary_suffix S hafter
  have hconf1 : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 1) ≤ rho.horizon :=
    (confirmation_time_mono_exec S.E
      (Nat.le_succ (S.hc.opening_slot r + 1))).trans hhor
  have hafter1 : healingBoundaryTime S q <
      Protocol.proposal_time S.E (S.hc.opening_slot r + 1) :=
    hafter.trans_le
      (Protocol.proposal_time_mono S.E (Nat.le_succ _))
  obtain ⟨P1, hP1⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot r + 1)
  refine { plusOneCone := ?_, plusTwoCone := ?_ }
  · exact adjacentProposal_parentCone_of_canonicalSuffixFrom
      S adm hsuffix hs0 hafter hcarrier.1 hcarrier.2.1 hconf1 hB0 hP1
  · intro P1' hP1'
    have hs1 : 0 < S.hc.opening_slot r + 1 := Nat.zero_lt_succ _
    obtain ⟨P2, hP2⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot r + 2)
    simpa only [Nat.add_assoc] using
      adjacentProposal_parentCone_of_canonicalSuffixFrom
        S adm hsuffix hs1 hafter1 hcarrier.2.1 hcarrier.2.2
          (by simpa only [Nat.add_assoc] using hhor) hP1' hP2

#print axioms canonicalCarrierParentConesAt_of_canonicalSuffixFrom

/-- Field-level twin of `canonicalCarrierParentEqualities_of_execution`
(`CanonicalCarrierConeRun.lean:195`). Stated over `CanonicalSuffixFrom`, so a
closer over either record is `hexec.canonicalSuffixFrom` and one application. -/
theorem canonicalCarrierParentEqualities_of_canonicalSuffixFrom
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q r : Round}
    (hsuffix : CanonicalSuffixFrom S rho (healingBoundaryTime S q))
    (hafter : healingBoundaryTime S q <
      Protocol.proposal_time S.E (S.hc.opening_slot r))
    (hcarrier : ProposerCarrierAt S rho r)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot r + 2) ≤ rho.horizon) :
    ∀ B0 P1 : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot r) = some B0 →
      proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P1 →
      proposedParent S rho (S.hc.opening_slot r + 1) = B0.erase ∧
        proposedParent S rho (S.hc.opening_slot r + 2) = P1.erase := by
  intro B0 P1 hB0 hP1
  have hcones := canonicalCarrierParentConesAt_of_canonicalSuffixFrom
    S adm hsuffix hafter hcarrier hhor B0 hB0
  constructor
  · have hslot : B0.erase.slot = S.hc.opening_slot r := by
      rw [Proofs.NamedWire.erase_slot]
      exact proposedBlockAt_slot S rho (S.hc.opening_slot r) hB0
    exact namedProposedParent_eq_previousSlotBlock_of_preceq_suffix S adm
      (s := S.hc.opening_slot r) (B := B0.erase) hslot hcones.plusOneCone
  · have hslot : P1.erase.slot = S.hc.opening_slot r + 1 := by
      rw [Proofs.NamedWire.erase_slot]
      exact proposedBlockAt_slot S rho (S.hc.opening_slot r + 1) hP1
    simpa only [Nat.add_assoc] using
      namedProposedParent_eq_previousSlotBlock_of_preceq_suffix S adm
        (s := S.hc.opening_slot r + 1) (B := P1.erase) hslot
          (hcones.plusTwoCone P1 hP1)

#print axioms canonicalCarrierParentEqualities_of_canonicalSuffixFrom
















/-! ## 17. The carrier-selection family, over the suffix field

The density record's `execution` field reaches the carrier selection through one
lemma and one field. Read down the chain rather than assumed:

```text
exists_justifiableCarrierPair_afterTwoProgress_with_property
      (OpeningCarrierSelectionRun:187, passes hdensity.execution)
  → exists_strictHeightCarrierPair_with_property (CanonicalDensityRun:594)
      → carrierOpeningHeight_mono (CanonicalDensityRun:316)
          → proposedBlock_preceq_of_canonicalSuffixExecution
                                      reads `canonicalSuffixFrom`, nothing else
```

`exists_strictHeightCarrierPair_with_property` touches the record exactly once,
and `carrierOpeningHeight_mono` exactly once, so the whole family is field-level
over `canonicalSuffixFrom`. The bottom lemma is twinned here; every theorem
above it then differs from its original by that one call. -/

/-- Opening slots are monotone in the round; `opening_slot r = r * R`. -/
private theorem w4_openingSlot_mono (hc : Protocol.HealConfig) {p q : Round}
    (h : p ≤ q) : hc.opening_slot p ≤ hc.opening_slot q := by
  unfold Protocol.HealConfig.opening_slot
  exact Nat.mul_le_mul_right hc.R h

/-- Field-level twin of `CanonicalDensityRun.carrierOpeningHeight_mono`
(`:316`): stated over `CanonicalSuffixFrom`, so it serves the plain and the
prepared density record alike. Body is the original's with the one record call
routed through §13's field-level suffix ordering. -/
theorem carrierOpeningHeight_mono_of_canonicalSuffixFrom
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q0 c1 c2 : Round}
    (hsuffix : CanonicalSuffixFrom S rho (healingBoundaryTime S q0))
    (hafter : healingBoundaryTime S q0 <
      Protocol.proposal_time S.E (S.hc.opening_slot c1))
    (hc1 : ProposerCarrierAt S rho c1)
    (hc2 : ProposerCarrierAt S rho c2)
    (hc12 : c1 ≤ c2)
    (hc2Hor : Protocol.proposal_time S.E (S.hc.opening_slot c2) ≤
      rho.horizon) :
    carrierOpeningHeight S rho c1 ≤ carrierOpeningHeight S rho c2 := by
  rcases Nat.eq_or_lt_of_le hc12 with rfl | hlt
  · exact Nat.le_refl _
  · have hs0 : 0 < S.hc.opening_slot c1 :=
      openingSlot_pos_of_after_boundary_suffix S hafter
    have hslot : S.hc.opening_slot c1 ≤ S.hc.opening_slot c2 :=
      w4_openingSlot_mono S.hc hc12
    have hsTarget : 0 < S.hc.opening_slot c2 := hs0.trans_le hslot
    have htime := Protocol.proposal_time_mono S.E hslot
    have hP1 : proposedBlockAt S rho (S.hc.opening_slot c1) = some
        (canonicalProposal S rho (S.hc.opening_slot c1)) :=
      canonicalProposal_spec S rho (S.hc.opening_slot c1)
    have hP2 : proposedBlockAt S rho (S.hc.opening_slot c2) = some
        (canonicalProposal S rho (S.hc.opening_slot c2)) :=
      canonicalProposal_spec S rho (S.hc.opening_slot c2)
    have hemit1 := Protocol.proposedBlock_emitted_of_admissible
      S adm hs0 hc1.1 (htime.trans hc2Hor) hP1
    have hemit2 := Protocol.proposedBlock_emitted_of_admissible
      S adm hsTarget hc2.1 hc2Hor hP2
    have hpre := proposedBlock_preceq_of_canonicalSuffixFrom
      S adm hsuffix hs0 hsTarget hafter hc1.1 hc2.1 hP1 hP2 hemit1 hemit2 htime
    have hrun1 := proposedBlockAt_blockInRun_of_admissible S
      adm.toNamedAdmissibleCore (S.hc.opening_slot c1) hs0 hc1.1
      (htime.trans hc2Hor) hP1
    have hrun2 := proposedBlockAt_blockInRun_of_admissible S
      adm.toNamedAdmissibleCore (S.hc.opening_slot c2) hsTarget hc2.1 hc2Hor hP2
    have hnamed := Protocol.namedPreceq_of_runBlock_erase_preceq adm
      hrun1 hrun2 hpre
    exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hnamed

#print axioms carrierOpeningHeight_mono_of_canonicalSuffixFrom

/-! Four arithmetic helpers copied from `CanonicalDensityRun.lean:104-118`
(`private` there); all `omega`. -/

private theorem w4_nat_not_lt_of_sub_le_zero
    {a z : Nat} (h : z - a ≤ 0) : ¬ a < z := by omega

private theorem w4_nat_near_of_next_window
    {a b gap : Nat} (h : b ≤ a + 1 + gap) : b ≤ a + gap + 1 := by omega

private theorem w4_nat_bound_of_near
    {a b z gap : Nat} (h : b ≤ a + gap + 1) (haz : a < z) :
    b ≤ z + gap := by omega

private theorem w4_nat_sub_le_of_step
    {a b z n : Nat} (h : z - a ≤ n + 1) (hab : a < b) : z - b ≤ n := by omega

/-- Field-level twin of
`CanonicalDensityRun.exists_strictHeightCarrierPair_with_property` (`:594`).
Body is the original's induction with its single `carrierOpeningHeight_mono`
call routed through the field-level twin above, so this serves the plain and
the prepared density record alike. -/
theorem exists_strictHeightCarrierPair_with_property_of_canonicalSuffixFrom
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q0 gap : Round}
    (hsuffix : CanonicalSuffixFrom S rho (healingBoundaryTime S q0))
    (hpost : S.E.t_GST ≤ S.a q0)
    {P : Round → Prop}
    (hrec : ∀ k : Round,
      S.E.t_GST ≤ Protocol.proposal_time S.E (S.hc.opening_slot k) →
      Protocol.proposal_time S.E (S.hc.opening_slot k) +
        gap * (S.a 1 - S.a 0) ≤ rho.horizon →
      ∃ r : Round, k ≤ r ∧ r ≤ k + gap ∧
      ProposerCarrierAt S rho r ∧ P r) :
    ∀ n a z : Round, z - a ≤ n → q0 ≤ a →
      healingBoundaryTime S q0 <
          Protocol.proposal_time S.E (S.hc.opening_slot a) →
      ProposerCarrierAt S rho a → P a → ProposerCarrierAt S rho z → a < z →
      carrierOpeningHeight S rho a < carrierOpeningHeight S rho z →
      S.a (z + gap) ≤ rho.horizon →
      ∃ c1 c2 : Round, a ≤ c1 ∧ c1 < z ∧ c1 < c2 ∧ c2 ≤ c1 + gap + 1 ∧
        ProposerCarrierAt S rho c1 ∧ ProposerCarrierAt S rho c2 ∧
        carrierOpeningHeight S rho c1 < carrierOpeningHeight S rho c2 ∧
        P c1 ∧ P c2 := by
  intro n
  induction n with
  | zero =>
      intro a z hn _ _ _ _ _ haz _ _
      exact absurd haz (w4_nat_not_lt_of_sub_le_zero hn)
  | succ n ih =>
      intro a z hn hq0 hafter ha haP hz haz hstrict hhor
      have hGSTwindow : S.E.t_GST ≤
          Protocol.proposal_time S.E (S.hc.opening_slot (a + 1)) :=
        hpost.trans ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
          (action_add_delta_le_openingProposal_of_round_lt S
            (lt_of_le_of_lt hq0 (Nat.lt_succ_self a))))
      have hwindowRound : a + 1 + gap ≤ z + gap :=
        Nat.add_le_add_right (Nat.succ_le_of_lt haz) gap
      have hhorWindow := (openingProposal_window_le_action S (a + 1) gap).trans
        ((Assembly.a_mono S hwindowRound).trans hhor)
      obtain ⟨b, hbLo, hbHi, hb, hbP⟩ := hrec (a + 1) hGSTwindow hhorWindow
      have hab : a < b := (Nat.lt_succ_self a).trans_le hbLo
      have hbNear : b ≤ a + gap + 1 := w4_nat_near_of_next_window hbHi
      have hbBound : b ≤ z + gap := w4_nat_bound_of_near hbNear haz
      have hafterB : healingBoundaryTime S q0 <
          Protocol.proposal_time S.E (S.hc.opening_slot b) :=
        hafter.trans_le
          (Protocol.proposal_time_mono S.E
            (w4_openingSlot_mono S.hc (Nat.le_of_lt hab)))
      have hafterZ : healingBoundaryTime S q0 <
          Protocol.proposal_time S.E (S.hc.opening_slot z) :=
        hafter.trans_le
          (Protocol.proposal_time_mono S.E
            (w4_openingSlot_mono S.hc (Nat.le_of_lt haz)))
      have hbHor : Protocol.proposal_time S.E (S.hc.opening_slot b) ≤
          rho.horizon :=
        (proposal_time_le_confirmation_time S.E _).trans
          (by simpa only [opening_confirmation_time_eq_action] using
            (Assembly.a_mono S hbBound).trans hhor)
      by_cases hgrow :
          carrierOpeningHeight S rho a < carrierOpeningHeight S rho b
      · exact ⟨a, b, Nat.le_refl a, haz, hab, hbNear, ha, hb, hgrow, haP, hbP⟩
      · have hba : carrierOpeningHeight S rho b ≤
            carrierOpeningHeight S rho a := Nat.le_of_not_lt hgrow
        have hbz : b < z := by
          by_contra hnot
          have hzb : z ≤ b := Nat.le_of_not_gt hnot
          have hmono := carrierOpeningHeight_mono_of_canonicalSuffixFrom
            S adm hsuffix hafterZ hz hb hzb hbHor
          exact absurd (hmono.trans hba) (Nat.not_le_of_gt hstrict)
        have hstrictB : carrierOpeningHeight S rho b <
            carrierOpeningHeight S rho z := lt_of_le_of_lt hba hstrict
        obtain ⟨c1, c2, hc1Lo, hc1z, hc12, hnear, hc1, hc2, hgrowPair,
          hc1P, hc2P⟩ :=
          ih b z (w4_nat_sub_le_of_step hn hab)
            (hq0.trans (Nat.le_of_lt hab)) hafterB hb hbP hz
            hbz hstrictB hhor
        exact ⟨c1, c2, (Nat.le_of_lt hab).trans hc1Lo, hc1z, hc12, hnear,
          hc1, hc2, hgrowPair, hc1P, hc2P⟩

#print axioms exists_strictHeightCarrierPair_with_property_of_canonicalSuffixFrom

/-! The two selection variants the density discharge actually calls
(`CanonicalDensityDischargeRun:1064` and `:1229`). Each touches the record
exactly once, at the same `carrierOpeningHeight_mono`, so each is the identical
one-call swap. Bodies copied from `CanonicalDensityRun.lean:535` and `:656`. -/








/-- The seven fields of `CanonicalRegimeRoundExecutionCoreAt` that are actually
read, with the same names. Contract-free, so one record serves the plain and
the prepared execution record alike. -/
structure CanonicalRegimeRoundExecutionFactsAt
    (S : Setup V) (rho : Run V) (q0 r : Round) : Prop where
  carrier : ProposerCarrierAt S rho r
  afterBoundary : healingBoundaryTime S q0 <
    Protocol.proposal_time S.E (S.hc.opening_slot r)
  inHorizon : Protocol.confirmation_time S.E
    (S.hc.opening_slot r + 2) ≤ rho.horizon
  batchSole : ∀ v ∈ rho.honest, ∀ w ∈ rho.honest,
    (Protocol.sg_votes_by
      (Protocol.round_batch
        (actionStoreAt S rho v r).toHealing.gradeView r) w).card ≤ 1
  openingLive : ∀ v ∈ rho.honest, ∀ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P →
    (actionStoreAt S rho v r).st.core.live_confirmed = P.erase
  plusOneCone : ∀ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P →
    Block.Preceq P.erase
      (proposedParent S rho (S.hc.opening_slot r + 1))
  plusTwoCone : ∀ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r + 1) = some P →
    Block.Preceq P.erase
      (proposedParent S rho (S.hc.opening_slot r + 2))




/-- the corresponding branch's `W4ExecutionCoreAtPin` shape, from the prepared execution
record, concluding the seven read facts. This is §15's body with the head field
dropped, so nothing here mentions a grade contract. -/
theorem w4ExecutionCoreFactsAt_of_executionPrepared
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {q0 : Round} (hexec : CanonicalSuffixExecutionPrepared S rho q0) :
    ∀ r : Round,
      healingBoundaryTime S q0 <
        Protocol.proposal_time S.E (S.hc.opening_slot r) →
      ProposerCarrierAt S rho r →
      Protocol.confirmation_time S.E
        (S.hc.opening_slot r + 2) ≤ rho.horizon →
      CanonicalRegimeRoundExecutionFactsAt S rho q0 r := by
  intro r hafter hcarrier hhor
  have hconf0 : Protocol.confirmation_time S.E
      (S.hc.opening_slot r) ≤ rho.horizon :=
    (confirmation_time_mono_exec S.E
      (Nat.le_add_right (S.hc.opening_slot r) 2)).trans hhor
  have hactionHor : S.a r ≤ rho.horizon := by
    simpa only [Setup.a, Protocol.a_eq_confirmation_time] using hconf0
  obtain ⟨P, hP⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot r)
  have hlifecycle := canonicalCarrierOpeningLifecycleAt_of_executionPrepared
    S hcom hexec hafter hcarrier hactionHor
  have hcones := canonicalCarrierParentConesAt_of_canonicalSuffixFrom
    S adm hexec.canonicalSuffixFrom hafter hcarrier hhor P hP
  refine
    { carrier := hcarrier
      afterBoundary := hafter
      inHorizon := hhor
      batchSole := ?_
      openingLive := ?_
      plusOneCone := ?_
      plusTwoCone := ?_ }
  · intro v hv w hw
    rw [Protocol.actionStoreAt_gradeView_eq_storeBeforeTime S rho v r]
    exact roundBatch_card_le_one_stateBeforeTime S adm hw
  · intro v hv P' hP'
    exact (hlifecycle P' hP' v hv).1
  · intro P' hP'
    exact (canonicalCarrierParentConesAt_of_canonicalSuffixFrom
      S adm hexec.canonicalSuffixFrom hafter hcarrier hhor P' hP').plusOneCone
  · intro P' hP'
    exact hcones.plusTwoCone P' hP'

#print axioms w4ExecutionCoreFactsAt_of_executionPrepared

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
