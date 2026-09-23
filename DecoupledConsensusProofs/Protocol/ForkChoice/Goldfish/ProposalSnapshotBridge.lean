module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.PostGSTCarrierAdmissionCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.ProposalCore
public import DecoupledConsensusProofs.Protocol.Schedule.ProposalSnapshot
public import DecoupledConsensusProofs.Protocol.Handlers.AdoptionConstructor
public import DecoupledConsensusProofs.Generic.PostGSTCarrierAdmission
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Proposal snapshot identities -/


/-- The named proposal carries the raw vote list from its prepared proposal
input. This is the  witness form of the retired field identity. -/
theorem proposedBlock_gf_votes
    (S : Setup V) (rho : Run V) (s : Slot) {B : NamedBlock V}
    (hB : Statements.Instantiation.proposedBlockAt S rho s = some B) :
    B.gf_votes = (Proofs.HealingSurface.proposalInputAt S rho s).gf_votes := by
  have hpay := Proofs.NamedActions.proposal_payload
    (NamedProfile.gradeContract (Statements.Instantiation.proposerReadAt S rho s).cache)
    .poolAndCarried S.E S.hc (S.node (S.E.proposer s))
    (Statements.Instantiation.proposerReadAt S rho s).st B hB
  simpa only [Proofs.HealingSurface.proposalInputAt] using hpay.2.2.2.2.1


/-- The named proposal carries the support subset from its prepared proposal
input. This is the  witness form of the retired field identity. -/
theorem proposedBlock_gf_support_votes
    (S : Setup V) (rho : Run V) (s : Slot) {B : NamedBlock V}
    (hB : Statements.Instantiation.proposedBlockAt S rho s = some B) :
    B.gf_support_votes =
      (Proofs.HealingSurface.proposalInputAt S rho s).gf_support_votes := by
  have hpay := Proofs.NamedActions.proposal_payload
    (NamedProfile.gradeContract (Statements.Instantiation.proposerReadAt S rho s).cache)
    .poolAndCarried S.E S.hc (S.node (S.E.proposer s))
    (Statements.Instantiation.proposerReadAt S rho s).st B hB
  simpa only [Proofs.HealingSurface.proposalInputAt] using hpay.2.2.2.2.2.1

/-- The named proposal's raw list is the previous-slot pool of its prepared
proposal read. -/
theorem proposedBlock_raw_eq_proposer_pool
    (S : Setup V) (rho : Run V) (s : Slot) {B : NamedBlock V}
    (hB : Statements.Instantiation.proposedBlockAt S rho s = some B) :
    B.gf_votes.toFinset =
      (Statements.Instantiation.proposerReadAt S rho s).st.core.pool
        ((Statements.Instantiation.proposerReadAt S rho s).st.core.s - 1) := by
  have hgf := Proofs.Optimistic.proposal_with_gf_votes
    (NamedProfile.gradeContract (Statements.Instantiation.proposerReadAt S rho s).cache)
    .poolAndCarried S.E S.hc (S.node (S.E.proposer s))
    (Statements.Instantiation.proposerReadAt S rho s).st (B := B) hB
  rw [hgf]
  rfl

/-- A vote already processed at an earlier proposer prefix remains in the
proposer's pool at the proposal read. -/
theorem gfVote_processed_after_event_at_proposerDuty_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {i : Nat} {e : Event V} {u : GoldfishVote V} {s : Slot}
    (he : rho.events[i]? = some e) (hus : u.slot = s)
    (hprocessed : Object.processed
      (rho.stateBefore S (i + 1) (S.E.proposer (s + 1))).st
      (Object.gfVote u) = true)
    (hearly : e.time < Protocol.proposal_time S.E (s + 1)) :
    u ∈ (proposerDutyStore S rho (s + 1)).pool s := by
  have hmem : u ∈ (rho.stateBefore S (i + 1)
      (S.E.proposer (s + 1))).st.core.gf_votes s := by
    have hprocessed' := hprocessed
    simp only [Object.processed, NamedReceipt.processed,
      decide_eq_true_eq, Protocol.Store.pool, List.mem_toFinset] at hprocessed'
    rw [hus] at hprocessed'
    exact hprocessed'
  let Gamma := Protocol.proposal_time S.E (s + 1)
  let N := (rho.events.filter (fun x => decide (x.time < Gamma))).length
  have hiN : i < N := by
    by_contra hnot
    have hNle : N ≤ i := Nat.le_of_not_gt hnot
    have hGammae : Gamma ≤ e.time :=
      Proofs.Optimistic.le_time_of_index_ge S adm.toNamedScheduleWellFormed
        (t := Gamma) (j := i) (e := e) (by simpa [N] using hNle) he
    exact (not_le_of_gt (by simpa only [Gamma] using hearly)) hGammae
  have hcarry : PoolCarry
      (rho.stateBefore S (i + 1) (S.E.proposer (s + 1))).st.core
      (rho.stateBefore S N (S.E.proposer (s + 1))).st.core :=
    pool_carry S adm.toNamedScheduleWellFormed (S.E.proposer (s + 1)) N
      (Nat.succ_le_of_lt hiN)
  have hstore : proposerDutyStore S rho (s + 1) =
      Proofs.Optimistic.tickStore S
        (rho.stateBefore S N (S.E.proposer (s + 1))).st.core Gamma := by
    change Proofs.Optimistic.tickStore S
        (rho.stateBeforeTime S Gamma (S.E.proposer (s + 1))).st.core Gamma = _
    rw [Proofs.Optimistic.stateBeforeTime_eq_take S adm.toNamedScheduleWellFormed Gamma]
  rw [hstore, Protocol.Store.pool]
  simpa only [Proofs.Optimistic.tickStore, List.mem_toFinset] using
    hcarry.mem s u hmem


#print axioms gfVote_processed_after_event_at_proposerDuty_core

/-- A correctly slotted carried set is included in the raw voter view as soon
as its carrier is in the tree. -/
theorem carried_raw_subset_voter_view
    (E : Env V) (st : Protocol.GoldfishStore V) {s : Slot} {B : Block V}
    (hB : B ∈ st.T) (hBslot : B.slot = s)
    (hslots : ∀ u ∈ B.gf_votes, u.slot + 1 = B.slot) :
    B.gf_votes.toFinset ⊆ Protocol.voter_view E st s := by
  intro u hu
  rw [Protocol.voter_view, Finset.mem_union]
  apply Or.inr
  rw [Finset.mem_biUnion]
  refine ⟨B, ?_, ?_⟩
  · rw [Finset.mem_filter]
    exact ⟨hB, hBslot⟩
  · rw [Finset.mem_filter]
    refine ⟨hu, ?_⟩
    have hslot := hslots u (List.mem_toFinset.mp hu)
    rw [hBslot] at hslot
    exact Nat.eq_sub_of_add_eq hslot

/-- Candidate-local view transport. Unlike global support-set inclusion, this
interface mentions only support votes that can affect the score of `C`.

The two raw fields preserve participation and equivocation. The directional
fields preserve a vote that targets `C`, or establish that its validator is
already score-invisible on the receiving side. -/
structure CandidateScorePreservingViewExtension
    (sourceTree targetTree : Finset (Block V))
    (sourceRaw sourceSupport targetRaw targetSupport :
      Finset (GoldfishVote V)) (C : Block V) : Prop where
  raw_subset : sourceRaw ⊆ targetRaw
  raw_extra_equiv : ∀ u ∈ targetRaw, u ∉ sourceRaw →
    Protocol.equivocates sourceRaw u.val_index = true
  forward : ∀ u ∈ sourceSupport,
    Protocol.targets_under sourceTree C u = true →
      (u ∈ targetSupport ∧
        Protocol.targets_under targetTree C u = true) ∨
      Protocol.equivocates targetRaw u.val_index = true
  backward : ∀ u ∈ targetSupport,
    Protocol.targets_under targetTree C u = true →
      (u ∈ sourceSupport ∧
        Protocol.targets_under sourceTree C u = true) ∨
      Protocol.equivocates sourceRaw u.val_index = true

namespace CandidateScorePreservingViewExtension

variable {sourceTree targetTree : Finset (Block V)}
  {sourceRaw sourceSupport targetRaw targetSupport :
    Finset (GoldfishVote V)} {C : Block V}

/-- Forgetting support yields the ordinary raw-view extension. -/
def rawExtension
    (h : CandidateScorePreservingViewExtension sourceTree targetTree
      sourceRaw sourceSupport targetRaw targetSupport C) :
    ScorePreservingViewExtension sourceRaw ∅ targetRaw ∅ :=
  { raw_subset := h.raw_subset
    support_subset := by simp
    raw_extra_equiv := h.raw_extra_equiv
    support_extra_equiv := by simp }

/-- Candidate-local transport preserves exactly the supporter set counted for
that candidate, even when the two trees and full support sets differ. -/
theorem supporters_eq
    (h : CandidateScorePreservingViewExtension sourceTree targetTree
      sourceRaw sourceSupport targetRaw targetSupport C)
    (E : Env V) (s : Slot) :
    Protocol.goldfishSupporters E sourceTree sourceRaw sourceSupport s C =
      Protocol.goldfishSupporters E targetTree targetRaw targetSupport s C := by
  apply Finset.ext
  intro x
  rw [mem_supporters_iff, mem_supporters_iff]
  have heq := h.rawExtension.equivocates_eq x
  constructor
  · rintro ⟨hclean, u, hu, hus, htarget⟩
    rw [Protocol.votes_by, Finset.mem_filter] at hu
    rcases h.forward u hu.1 htarget with hreach | hequiv
    · refine ⟨?_, u, ?_, hus, hreach.2⟩
      · rwa [← heq]
      · rw [Protocol.votes_by, Finset.mem_filter]
        exact ⟨hreach.1, hu.2⟩
    · have hcleanTarget : Protocol.equivocates targetRaw x = false := by
        rwa [← heq]
      rw [hu.2, hcleanTarget] at hequiv
      contradiction
  · rintro ⟨hclean, u, hu, hus, htarget⟩
    rw [Protocol.votes_by, Finset.mem_filter] at hu
    rcases h.backward u hu.1 htarget with hreach | hequiv
    · refine ⟨?_, u, ?_, hus, hreach.2⟩
      · rwa [heq]
      · rw [Protocol.votes_by, Finset.mem_filter]
        exact ⟨hreach.1, hu.2⟩
    · have hcleanSource : Protocol.equivocates sourceRaw x = false := by
        rwa [heq]
      rw [hu.2, hcleanSource] at hequiv
      contradiction

/-- Candidate-local transport preserves the candidate's Goldfish score. -/
theorem goldfish_score_eq
    (h : CandidateScorePreservingViewExtension sourceTree targetTree
      sourceRaw sourceSupport targetRaw targetSupport C)
    (E : Env V) (s : Slot) :
    Protocol.goldfish_score E sourceTree sourceRaw sourceSupport s C =
      Protocol.goldfish_score E targetTree targetRaw targetSupport s C := by
  simp only [Protocol.goldfish_score, Protocol.raw_goldfish_score]
  rw [h.rawExtension.raw_equivocators_eq]
  have hsupp :
      Protocol.raw_supporters sourceTree sourceRaw sourceSupport s C =
        Protocol.raw_supporters targetTree targetRaw targetSupport s C :=
    h.supporters_eq E s
  rw [hsupp]

/-- Candidate-local transport also preserves the Goldfish denominator. -/
theorem voters_count_eq
    (h : CandidateScorePreservingViewExtension sourceTree targetTree
      sourceRaw sourceSupport targetRaw targetSupport C)
    (E : Env V) (s : Slot) :
    Protocol.voters_count E sourceRaw s =
      Protocol.voters_count E targetRaw s :=
  h.rawExtension.voters_count_eq E s

end CandidateScorePreservingViewExtension

/-! ## Candidate-cone resolution transport -/



/-- One proposal-carried support vote enters the receiver's support view as
soon as its head resolves locally. It does not need a local vote receipt. -/
theorem mem_voter_support_view_of_carried
    (E : Env V) (st : Protocol.GoldfishStore V) {s : Slot} {B : Block V}
    {u : GoldfishVote V}
    (hB : B ∈ st.T) (hBslot : B.slot = s)
    (hu : u ∈ B.gf_support_votes)
    (hresolved : Protocol.resolved st.T u = true)
    (huslot : u.slot + 1 = B.slot) :
    u ∈ Protocol.voter_support_view E st s := by
  rw [Protocol.voter_support_view, Finset.mem_union]
  apply Or.inr
  rw [Finset.mem_biUnion]
  refine ⟨B, ?_, ?_⟩
  · rw [Finset.mem_filter]
    exact ⟨hB, hBslot⟩
  · rw [Finset.mem_filter]
    refine ⟨List.mem_toFinset.mpr hu, hresolved, ?_⟩
    rw [hBslot] at huslot
    exact Nat.eq_sub_of_add_eq huslot

/-- One slot's view freeze plus one network delay is the next proposal time. -/
theorem view_freeze_add_delta_eq_proposal_time_succ
    (E : Env V) (s : Slot) :
    Protocol.view_freeze E s + E.Δ = Protocol.proposal_time E (s + 1) := by
  unfold Protocol.view_freeze Protocol.proposal_time Env.t slotStart
  push_cast
  ring



#print axioms carried_raw_subset_voter_view
#print axioms proposedBlock_gf_votes
#print axioms proposedBlock_gf_support_votes
#print axioms proposedBlock_raw_eq_proposer_pool
#print axioms CandidateScorePreservingViewExtension.goldfish_score_eq
#print axioms CandidateScorePreservingViewExtension.voters_count_eq
#print axioms mem_voter_support_view_of_carried
#print axioms view_freeze_add_delta_eq_proposal_time_succ

end Protocol
end DecoupledConsensusModel

end
