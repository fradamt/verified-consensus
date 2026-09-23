module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import Mathlib.Data.Finset.Max
public import DecoupledConsensusInternal.RecoveryPrefix
public import DecoupledConsensusProofs.Protocol.Grades.HonestMajority
public import DecoupledConsensusProofs.Protocol.Schedule.Action
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionHistory
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.AdoptionRun
public import DecoupledConsensusProofs.Protocol.ValidatorClient.FinalityPairCore
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Protocol.Grades.ProposalLifecycleCore
public import DecoupledConsensusProofs.Generic.SuffixHistory
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.CanonicalObservation
public import DecoupledConsensusProofs.Protocol.Schedule.CanonicalSuffixPostGSTCore

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Event-indexed canonical suffix after healing

The checked two-slot handoff starts an event-indexed, moving proposal-chain
suffix. The internal execution record also keeps the exact local facts used by
an honest proposal's later confirmation read. The public projection hides all
store state and exposes only `Internal.CanonicalSuffixFrom`.

**Named-runtime proof (design note).**  quantifies the
proposal at every site: each proposal-facing clause reads
`∀ B, Statements.Instantiation.proposedBlockAt S rho s = some B → …` and takes its fields
on the named body, with `B.erase` in geometric positions and `derive_named` for
its chain state. Height pairs use the named constructor, so a target is
`NamedHeightPair.vote H T false` and a timeout `.vote H T true`. The common
grade is `Proofs.HealingSurface.NamedGradeFormsAt`. Run-scope fields name the full
body behind an erased endpoint, because `RunBlock` is `NamedRun.blockInRun`
over `NamedBlock V`. The action read is a `NamedNodeState V`, so its
store is `.st.core`.

The sixteen suffix-fold declarations are restated below. Post-GST vote counting
uses `canonicalSuffixHonestVoteCounted`; vote-stage facts use the prepared
named read and a named tree witness. Proposal reads are bound with
`proposedBlockAt = some B` under.
-/



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution
open Internal.NamedRecoveryRead

variable {V : Type} [DecidableEq V] [Fintype V]





/-- The event-indexed action-output part of a canonical suffix.

`endpoint (i + 1)` is the canonical endpoint selected after event `i`. Thus
each honest target, confirmed root, and height-gate source emitted at that
event has a concrete run block on the same monotone endpoint chain above it.
This record intentionally does not assert that a height is unused: records at
one height may be reused by later actions. It also contains no common SG grade,
carrier, or action-batch fact; those require the separate carrier-round leaf. -/
structure CanonicalSuffixActionHistory
    (S : Setup V) (rho : Run V) (q : Round) where
  n0 : Nat
  endpoint : Nat → Block V
  starts : SuffixStartsAfterBoundaryVote S rho (healingBoundaryTime S q) n0
  endpointNamed : ∀ i : Nat, n0 ≤ i →
    ∃ C : NamedBlock V, C.erase = endpoint i ∧ RunBlock S rho C
  endpointMono : ∀ i : Nat, n0 ≤ i →
    Block.Preceq (endpoint i) (endpoint (i + 1))
  actionOutput : ∀ i : Nat, n0 ≤ i →
    HonestAttestationOutputPreceqAtIndex S rho i (endpoint (i + 1))







/-! ## Post-GST vote counting -/

/-- Exact vote names and receiver-side resolution discharge the confirmation
counting field at a post-GST proposal. The block witness is named. -/
theorem canonicalProposalCounted_of_exactNames_afterGST
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {B : NamedBlock V} (hrun : RunBlock S rho B)
    (hnames : Proofs.HealingSurface.NamedHonestVotesName S rho s B.erase)
    (hresolve : ∀ v ∈ rho.honest,
      Proofs.Optimistic.HeadsResolveIn S rho s
        (Proofs.Optimistic.confStore S rho v s).T
        (Proofs.Optimistic.confStore S rho v s).timestamp_block) :
    ∀ v ∈ rho.honest, ∀ u : GoldfishVote V,
      u.slot = s →
      u.val_index ∈ rho.honest →
      u.val_index ∈ S.E.committee s →
      rho.emits S u.val_index (Object.gfVote u)
        (Protocol.vote_time S.E s) →
      u ∈ confVotes S.E (Proofs.Optimistic.confStore S rho v s) s := by
  intro v hv u hus huHon huCommittee huEmit
  have hnamed := hnames u.val_index huHon huCommittee
  have hueq : u = ⟨u.val_index, s, B.erase.root⟩ :=
    Proofs.Optimistic.emits_gfVote_unique S adm.toNamedScheduleWellFormed
      huEmit hnamed (by simpa only using hus)
  have harr : Proofs.Optimistic.HeadArrivesBefore
      (Proofs.Optimistic.confStore S rho v s).T
      (Proofs.Optimistic.confStore S rho v s).timestamp_block
      (Protocol.support_cutoff S.E s) u := by
    obtain ⟨hfind, hstamp⟩ :=
      hresolve v hv B.erase
        ⟨u.val_index, huHon, huCommittee, ⟨B, rfl, hrun⟩, hnamed⟩
    refine ⟨B.erase, ?_, hstamp⟩
    rw [hueq]
    simpa only using hfind
  exact canonicalSuffixHonestVoteCounted
    S adm hs hpost hhor v hv u hus huHon huEmit harr



/-- Exact local store facts produced for one honest named proposal. -/
structure CanonicalSuffixProposalStoreFacts
    (S : Setup V) (rho : Run V) (s : Slot) (B : NamedBlock V) : Prop where
  run : RunBlock S rho B
  names : Proofs.HealingSurface.NamedHonestVotesName S rho s B.erase
  validLate : ∀ v ∈ rho.honest,
    Protocol.VoteSetValid S.E s
      (confLate S.E (Proofs.Optimistic.confStore S rho v s) s)
  anchor : ∀ v ∈ rho.honest,
    Block.Preceq
      (namedConfirmationAnchor S (confirmationInputRead S rho v s)) B.erase
  candidate : ∀ v ∈ rho.honest,
    B.erase ∈ confTree (Proofs.Optimistic.confStore S rho v s)
  resolve : ∀ v ∈ rho.honest,
    Proofs.Optimistic.HeadsResolveIn S rho s
      (Proofs.Optimistic.confStore S rho v s).T
      (Proofs.Optimistic.confStore S rho v s).timestamp_block

/-- Post-GST counting and the candidate path complete the proposal duty. -/
theorem CanonicalSuffixProposalStoreFacts.duty
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {B : NamedBlock V} (h : CanonicalSuffixProposalStoreFacts S rho s B) :
    CanonicalProposalDutyAt S rho s B := by
  apply CanonicalProposalDutyAt.ofLocalFacts
    S rho s B h.run h.names h.validLate h.anchor
  · intro v hv C hanchorC hCne hCB
    exact confPath_of_candidate S (h.candidate v hv)
      C hanchorC hCne hCB
  · exact h.resolve
  · exact canonicalProposalCounted_of_exactNames_afterGST
      S adm hs hpost hhor h.run h.names h.resolve












/-- Consecutive endpoint sandwiches imply the public named suffix. -/
theorem canonicalSuffixAtIndex_of_sandwich
    (S : Setup V) {rho : Run V}
    {n0 : Nat} {End : Nat → NamedBlock V}
    (hrun : ∀ i : Nat, n0 ≤ i → RunBlock S rho (End i))
    (hmono : ∀ i j : Nat, n0 ≤ i → i ≤ j →
      Block.Preceq (End i).erase (End j).erase)
    (hsandwich : ∀ i stage : Nat, ∀ B : Block V,
      n0 ≤ i → ProposalChainStage stage →
      HonestCanonicalObservationAtIndex S rho i stage B →
      Block.Preceq (End i).erase B ∧ Block.Preceq B (End (i + 1)).erase) :
    CanonicalSuffixAtIndex S rho n0 End := by
  refine
    { endpointRun := hrun
      endpointMono := fun i hi => hmono i (i + 1) hi (Nat.le_succ i)
      sandwich := hsandwich
      ordered := ?_ }
  intro i stage B j laterStage C hi hj hstage hlater hB hC horder
  rcases horder with hij | ⟨rfl, hle⟩
  · have hBnext := (hsandwich i stage B hi hstage hB).2
    have hnextj : Block.Preceq (End (i + 1)).erase (End j).erase :=
      hmono (i + 1) j
        (le_trans hi (Nat.le_succ i)) (Nat.succ_le_iff.mpr hij)
    have hjC := (hsandwich j laterStage C hj hlater hC).1
    exact Block.preceq_trans hBnext (Block.preceq_trans hnextj hjC)
  · exact proposalChainObservation_preceq_of_sameIndex
      S hstage hlater hB hC hle

/-- Package a checked boundary cursor and the named suffix closure. -/
theorem canonicalSuffixFrom_of_sandwich
    (S : Setup V) {rho : Run V} {t0 : Time}
    {n0 : Nat} {End : Nat → NamedBlock V}
    (hstart : SuffixStartsAfterBoundaryVote S rho t0 n0)
    (hrun : ∀ i : Nat, n0 ≤ i → RunBlock S rho (End i))
    (hmono : ∀ i j : Nat, n0 ≤ i → i ≤ j →
      Block.Preceq (End i).erase (End j).erase)
    (hsandwich : ∀ i stage : Nat, ∀ B : Block V,
      n0 ≤ i → ProposalChainStage stage →
      HonestCanonicalObservationAtIndex S rho i stage B →
      Block.Preceq (End i).erase B ∧ Block.Preceq B (End (i + 1)).erase) :
    CanonicalSuffixFrom S rho t0 :=
  ⟨n0, End, hstart,
    canonicalSuffixAtIndex_of_sandwich S hrun hmono hsandwich⟩




/-- Indices of honest committee ticks at one vote duty. This finite set lets
the suffix cursor choose the last honest boundary vote, so no later
proposal-chain observation remains at the boundary instant. -/
private noncomputable def honestVoteTickIndices
    (S : Setup V) (rho : Run V) (s : Slot) : Finset Nat := by
  classical
  exact (Finset.range rho.events.length).filter (fun i =>
    ∃ v : V, v ∈ rho.honest ∧ v ∈ S.E.committee s ∧
      rho.events[i]? = some (Event.tick v (Protocol.vote_time S.E s)))

/-- The public cursor can be chosen after the last honest committee tick at
the boundary duty, not merely after an arbitrary one. -/
theorem exists_lastCanonicalSuffixStart
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) {q : Round}
    (hboundary : healingBoundaryTime S q ≤ rho.horizon) :
    ∃ n0 : Nat,
      SuffixStartsAfterBoundaryVote S rho (healingBoundaryTime S q) n0 ∧
      ∀ j v,
        v ∈ rho.honest →
        v ∈ S.E.committee (S.hc.opening_slot q + 2) →
        rho.events[j]? = some
          (Event.tick v (healingBoundaryTime S q)) →
        j < n0 := by
  classical
  let s0 := S.hc.opening_slot q + 2
  let I := honestVoteTickIndices S rho s0
  have hcard : 0 < ((S.E.committee s0) ∩ rho.honest).card := by
    have hmajority := hcom s0
    omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hcard
  have hvCommittee : v ∈ S.E.committee s0 := (Finset.mem_inter.mp hv).1
  have hvHonest : v ∈ rho.honest := (Finset.mem_inter.mp hv).2
  have htick : Event.tick v (healingBoundaryTime S q) ∈ rho.events := by
    apply adm.tick_total v hvHonest (healingBoundaryTime S q)
    · simpa only [healingBoundaryTime, s0] using
        (Proofs.Optimistic.publicTime_vote_time S s0)
    · simpa only [healingBoundaryTime, s0] using
        (Proofs.Optimistic.vote_time_nonneg S.E s0)
    · exact hboundary
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp htick
  have hiI : i ∈ I := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr
      (List.getElem?_eq_some_iff.mp hi).1, ?_⟩
    exact ⟨v, hvHonest, hvCommittee, by
      simpa only [healingBoundaryTime, s0] using hi⟩
  have hI : I.Nonempty := ⟨i, hiI⟩
  let last := I.max' hI
  have hlastI : last ∈ I := Finset.max'_mem I hI
  obtain ⟨_, ⟨vlast, hvlastHonest, hvlastCommittee, hvlastEvent⟩⟩ :=
    Finset.mem_filter.mp hlastI
  refine ⟨last + 1, ?_, ?_⟩
  · refine ⟨vlast, s0, last, hvlastHonest, ?_, ?_, ?_,
      ?_, rfl⟩
    · simpa only [S.node_val_index] using hvlastCommittee
    · exact Nat.zero_lt_succ (S.hc.opening_slot q + 1)
    · simp only [healingBoundaryTime, s0]
    · simpa only [healingBoundaryTime, s0] using hvlastEvent
  · intro j w hwHonest hwCommittee hj
    have hjI : j ∈ I := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr
        (List.getElem?_eq_some_iff.mp hj).1, ?_⟩
      exact ⟨w, hwHonest, by simpa only [s0] using hwCommittee,
        by simpa only [healingBoundaryTime, s0] using hj⟩
    exact Nat.lt_succ_of_le (Finset.le_max' I j hjI)

/-- Every event at or after a checked suffix cursor is at or after the boundary
time. This converts the event-index fold back to suffix-local time histories. -/
theorem SuffixStartsAfterBoundaryVote.time_le_of_index
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {t0 : Time} {n0 j : Nat} {e : Event V}
    (hstart : SuffixStartsAfterBoundaryVote S rho t0 n0)
    (hj : n0 ≤ j) (hget : rho.events[j]? = some e) :
    t0 ≤ e.time := by
  rcases hstart with
    ⟨v, s, i, hv, hcommittee, hs, ht0, hi, rfl⟩
  have hprefix :
      (rho.events.filter (fun e => decide (e.time < t0))).length ≤ i := by
    by_contra hnot
    have hlt :
        i < (rho.events.filter (fun e => decide (e.time < t0))).length :=
      Nat.lt_of_not_ge hnot
    have hmem : Event.tick v t0 ∈
        rho.events.filter (fun e => decide (e.time < t0)) := by
      rw [Proofs.Optimistic.filter_eq_take S sch _
        (Proofs.Optimistic.downward_lt t0)]
      exact List.mem_of_getElem? (by
        rw [List.getElem?_take_of_lt hlt]
        exact hi)
    have htime := (List.mem_filter.mp hmem).2
    simp only [decide_eq_true_eq, Event.time] at htime
    exact lt_irrefl t0 htime
  apply Proofs.Optimistic.le_time_of_index_ge S sch
    (le_trans hprefix (le_trans (Nat.le_succ i) hj)) hget

#print axioms canonicalProposalCounted_of_exactNames_afterGST
#print axioms CanonicalSuffixProposalStoreFacts.duty
#print axioms canonicalSuffixAtIndex_of_sandwich
#print axioms canonicalSuffixFrom_of_sandwich
#print axioms exists_lastCanonicalSuffixStart
#print axioms SuffixStartsAfterBoundaryVote.time_le_of_index

end Protocol
end DecoupledConsensusModel

end
