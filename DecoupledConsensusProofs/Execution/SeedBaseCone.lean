module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ExcludesRefute
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryHandoffCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightProgressSeedRegime
public import DecoupledConsensusProofs.Protocol.ChainState.SlashableBoundBridge
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGTargetCanonicality
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainSupporter
public import DecoupledConsensusProofs.Protocol.Schedule.SlotInduction

@[expose] public section

/-!
# The base cone at the slot after a carrier round's opening

A genuine confirmation below an honest vote-duty head supplies the strict
source score for a protected ancestor. Post-GST relay places that head in
each next-slot duty, where the gate-off frontier keeps the protected ancestor
in the frozen candidate tree. Compatible healing anchors then give the
next-slot honest vote cone.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]


/-! ## The prepared vote-duty head in its own read -/

set_option linter.unusedVariables false in

/-- A vote-duty head remains in the tree from which it was selected.
This also holds for nodes outside the slot's committee.

: the head is the prepared `voterHeadAt` observation, so its membership is
read off the prepared vote-duty read's own retained tree. The erased tick
store of the vote duty carries exactly that block set, so the public statement
is unchanged; only the route is. The retired `DepReachableStore` bridge is
replaced by the named confirmation-membership invariant of the read. The
admissibility argument is kept in the signature for the erased route's
callers; the named route reads the invariant off the run's own state. -/
theorem voteDutyHead_mem_voteDutyStore
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (v : V) (s : Slot) :
    voteDutyHead S rho v s ∈ (Proofs.Optimistic.voteDutyStore S rho v s).T := by
  let read := Internal.NamedRecoveryRead.voteDutyRead S rho v s
  let st := read.st.core
  have hinvPre : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (rho.stateBeforeTime S (Protocol.vote_time S.E s) v).st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
      (Protocol.vote_time S.E s) v).1
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg read.st := by
    simpa only [read, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt] using
      Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ _ hinvPre
  have hroot : Protocol.get_fg_root st.toHealing.toFG ∈ st.T :=
    Proofs.NamedStoreRoots.fg_root_mem read.st hinv.1.2
  have hanchor : voterAnchorAt S rho v s ∈ st.T :=
    Proofs.NamedConfirmationMembership.runtime_anchor_mem read.cache
      S.E S.hc st.toHealing (S.hc.round_of st.s) hroot
  have htree : voterCandidateTreeAt S rho v s ⊆ st.T := by
    intro D hD
    have hprocessed := Proofs.Records.get_filtered_block_tree_from_subset
      st.toHealing.toFG
      (Protocol.voter_processed_block_tree S.E st.toHealing.toFG.toSG.toGoldfishStore st.s) hD
    exact (Finset.mem_filter.mp hprocessed).1
  have hHmem : voterHeadAt S rho v s ∈ st.T := by
    rw [show voterHeadAt S rho v s = Protocol.ghost (voterAnchorAt S rho v s)
        (voterCandidateTreeAt S rho v s)
        (Protocol.goldfish_score S.E st.T
          (Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (st.s - 1))
        (Protocol.goldfish_eligible S.E st.σ st.h_max st.T st.s
          (Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (st.s - 1)) from rfl]
    exact Proofs.Records.ghost_mem_of _ _ hanchor htree
  have hHpre : voterHeadAt S rho v s ∈
      (rho.stateBeforeTime S (Protocol.vote_time S.E s) v).st.core.T := by
    simpa only [read, st, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hHmem
  simpa only [voteDutyHead, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
    Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hHpre

/-! ## The post-GST relay of a slot-`s` head into the next duty -/

/-- Local twin of the named delivery-time finalized bound. Every module that
holds this fact declares it `private`, so the route over the same public
helpers is repeated here rather than re-derived. -/
private theorem finalized_preceq_at_delivery_local
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} {v : V} {B : Block V} {X : NamedBlock V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho v (s + 1)).toHealing.toFG) B)
    {i : Nat} {t : Time}
    (hi : rho.events[i]? = some (Event.deliver v (Object.block X) t))
    (hlt : t < Protocol.view_freeze S.E s) :
    Block.Preceq (rho.stateBefore S i v).st.F B := by
  let Gamma := Protocol.vote_time S.E (s + 1)
  let n := (rho.events.filter (fun e => decide (e.time < Gamma))).length
  have hiN : i < n := by
    by_contra hnot
    have hni : n ≤ i := Nat.le_of_not_gt hnot
    have hGamma : Gamma ≤ t :=
      Proofs.Optimistic.le_time_of_index_ge S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
        (t := Gamma) (j := i) (e := Event.deliver v (Object.block X) t)
        (by simpa only [n] using hni) hi
    exact (not_le_of_gt
      (lt_trans hlt (Protocol.view_freeze_lt_vote_time_succ S.E s))) hGamma
  let pre := rho.storeBeforeTime S v Gamma
  have hmono : Block.Preceq (rho.stateBefore S i v).st.F pre.F := by
    have hprefix := stateBefore_F_mono S rho v (Nat.le_of_lt hiN)
    have hstore : pre = (rho.stateBefore S n v).st :=
      congrArg NamedNodeState.st
        (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed Gamma) v)
    simpa only [hstore] using hprefix
  have hFJ : Block.Preceq pre.F pre.J :=
    Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho Gamma v
  have hFroot : Block.Preceq pre.F
      (Protocol.get_fg_root pre.toHealing.toFG) :=
    Proofs.Records.preceq_get_fg_root_of_F (st := pre.toHealing.toFG) hFJ
  have hroot' : Block.Preceq
      (Protocol.get_fg_root pre.toHealing.toFG) B := by
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, pre, Gamma] using hroot
  exact Block.preceq_trans hmono (Block.preceq_trans hFroot hroot')

/-- An honest slot-`s` vote head above the next duty's own fork-choice root is
visible, and stamped in time, at that duty's read. -/
private theorem voteHeadVisible_at_nextDuty
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {u w : V} (hu : u ∈ rho.honest) (hw : w ∈ rho.honest)
    {s : Slot} (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.confirmation_time S.E (s + 1) ≤ rho.horizon)
    {B : Block V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) B)
    (hBhead : Block.Preceq B (voteDutyHead S rho u s)) :
    voteDutyHead S rho u s ∈
        (rho.storeBeforeTime S w (Protocol.vote_time S.E (s + 1))).T ∧
      stampedBefore
        (rho.storeBeforeTime S w
          (Protocol.vote_time S.E (s + 1))).timestamp_block
        (Protocol.view_freeze S.E s) (voteDutyHead S rho u s) = true := by
  have hHVpreU : voteDutyHead S rho u s ∈
      (rho.storeBeforeTime S u (Protocol.vote_time S.E s)).T := by
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using voteDutyHead_mem_voteDutyStore S adm u s
  rcases block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTime S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed u
      (Protocol.vote_time S.E s) hHVpreU with
    hgen | ⟨D, i, t, hDeq, hacc, ht⟩
  · simpa only [hgen] using
      (Protocol.genesis_mem_and_stamp_storeBeforeTime S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed w
        (Protocol.vote_time S.E (s + 1)) (Protocol.view_freeze S.E s))
  · have hDpos : 0 < D.slot := by
      rw [← Proofs.NamedWire.erase_slot D]
      exact Nat.zero_lt_of_lt
        (Protocol.parent_slot_lt_of_acceptsAt_block S hacc)
    have hBD : Block.Preceq B D.erase := by
      simpa only [hDeq] using hBhead
    have htSupport : t < Protocol.support_cutoff S.E s :=
      lt_trans ht (by
        rw [← Proofs.Optimistic.vote_time_add_delta]
        exact Int.lt_add_of_pos_right _ S.E.Δ_pos)
    have hgstCut : S.E.t_GST ≤ Protocol.support_cutoff S.E s := by
      apply le_trans hpost
      unfold Protocol.proposal_time Protocol.support_cutoff
      exact le_add_of_nonneg_right
        (Int.mul_nonneg (by norm_num) (le_of_lt S.E.Δ_pos))
    have hfreezeHor : Protocol.view_freeze S.E s ≤ rho.horizon :=
      (le_of_lt (Protocol.view_freeze_lt_vote_time_succ S.E s)).trans
        ((Protocol.vote_time_le_confirmation_time S.E (s + 1)).trans hhor)
    have hadmit : AdmittedBefore S rho w D.erase
        (Protocol.view_freeze S.E s) := by
      apply Protocol.block_admittedBefore_of_accepted_after_cutoff
        S adm hu hw hDpos hacc htSupport hgstCut
          (Protocol.support_cutoff_add_delta_eq_view_freeze S.E s)
          hfreezeHor
      intro j hj
      have hjVote := hj.trans (strict_filter_length_mono rho
        (le_of_lt (Protocol.view_freeze_lt_vote_time_succ S.E s)))
      have hroot' : Block.Preceq
          (Protocol.get_fg_root
            (rho.storeBeforeTime S w (Protocol.vote_time S.E (s + 1))).toHealing.toFG)
            B := by
        simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore] using hroot
      exact Block.preceq_trans
        (finalized_preceq_at_prefix_of_storeBeforeRoot_preceq
          S rho adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted
          hroot' hjVote) hBD
    have hvis := Protocol.admittedBefore_mem_and_stamp_at S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hadmit
      (le_of_lt (Protocol.view_freeze_lt_vote_time_succ S.E s))
    simpa only [hDeq] using hvis

/-! ## The next-vote adoption of a protected ancestor -/


/-- Compatible anchors suffice for the post-GST next-vote adoption handoff.

design note: the duty anchor is the prepared `voterAnchorAt`, which is exactly the
anchor field of the prepared adoption interface. When the target is already
at or below that anchor no adoption is needed — the duty's composed head
descends its own anchor — so the compatible premise splits into the two arms
below. -/
private theorem nextVoteAdoption_of_recovery_after_gst_compatible
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {s : Slot} (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {B : Block V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) B)
    (hanchor : Block.compatible (voterAnchorAt S rho w (s + 1)) B = true)
    (hcandidate : B ∈ Proofs.Optimistic.voter_candidate_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing) :
    Block.Preceq B (voterAnchorAt S rho w (s + 1)) ∨
      Protocol.NamedNextVoteAdoption S rho
        (Proofs.Optimistic.confStore S rho v s) s B w := by
  simp only [Block.compatible, Bool.or_eq_true] at hanchor
  rcases hanchor with habove | hbelow
  · exact Or.inr (nextVoteAdoption_of_recovery_after_gst
      S adm hv hw hpost hhor hroot habove hcandidate)
  · exact Or.inl hbelow


/-- The single-committee-member vote witness
`honestVotesCone_succ_of_ancestorGenuineConfirmation` extracts from ONE
`NamedNextVoteAdoption` fact, exposed on its own. A caller that only has
`NamedNextVoteAdoption` at some (not necessarily every) slot-`(s + 1)`
committee member — e.g. because a different member takes a different route to
the cone entirely — can still produce the vote witness at exactly the members
it has it for.

design note: the witness is the named run block behind the prepared head, and the
emission is the named vote of that duty. -/
private theorem honestVoteWitness_of_nextVoteAdoption
    (S : Setup V) (rho : Run V) (source : Protocol.Store V)
    (s : Slot) (T : Block V)
    (heligible : Protocol.voters_count S.E (confLate S.E source s) s <
      2 * Protocol.goldfish_score S.E source.T
        (confVotes S.E source s) (confVotes S.E source s) s T)
    {w : V} (_hw : w ∈ rho.honest) (hwcommittee : w ∈ S.E.committee (s + 1))
    (hd : Protocol.NamedNextVoteAdoption S rho source s T w) :
    ∃ X : NamedBlock V, Block.Preceq T X.erase ∧ RunBlock S rho X ∧
      NamedRun.emits S rho w (Object.gfVote ⟨w, s + 1, X.erase.root⟩)
        (Protocol.vote_time S.E (s + 1)) := by
  let read := Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)
  let st := read.st.core
  let tree := voterCandidateTreeAt S rho w (s + 1)
  let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  have hslot : st.s = s + 1 := by
    simpa only [st, read] using
      Proofs.Optimistic.voteDutyRead_slot S rho w (s + 1)
  have hprev : st.s - 1 = s := by
    rw [hslot]
    simp
  have hhead : Block.Preceq T (voterHeadAt S rho w (s + 1)) := by
    change Block.Preceq T
      (Protocol.get_head_in_tree_with_layer
        (NamedProfile.gradeContract read.cache) S.E S.hc st.toHealing
        tree votes support (st.s - 1))
    rw [Proofs.Optimistic.get_head_in_tree_split_with, hprev]
    simpa only [Protocol.Store.toHealing, read, st] using
      (Protocol.goldfish_fork_choice_captures_of_confirmation
        S.E st.σ st.h_max source.T st.T tree st.s
        (confEarly S.E source s) (confLate S.E source s)
        (confVotes S.E source s) votes support s
        (confNumerator S.E source s) hd.transport heligible
        hd.support_subset hd.anchor hd.path)
  obtain ⟨X, hXerase, hXrun⟩ := hd.run
  have hXhead : X.erase = voterHeadAt S rho w (s + 1) := hXerase
  have hout :
      (Protocol.NamedDuties.goldfish_vote_with
        (NamedProfile.gradeContract read.cache)
        S.E S.hc (S.node w) read.st).2 =
          some ⟨(S.node w).val_index, st.s,
            (voterHeadAt S rho w (s + 1)).root⟩ := by
    simp only [Protocol.NamedDuties.goldfish_vote_with,
      Protocol.goldfish_vote_with]
    rw [if_pos]
    · rfl
    · rw [S.node_val_index, hslot]
      exact hwcommittee
  have hem := hd.emit _ hout
  rw [S.node_val_index, hslot] at hem
  exact ⟨X, by rw [hXhead]; exact hhead, hXrun, by
    simpa only [hXhead] using hem⟩

/-- Confirmation instants are monotone in their slot number. -/
private theorem confirmation_time_mono_local
    (E : Env V) {a b : Slot} (hab : a ≤ b) :
    Protocol.confirmation_time E a ≤ Protocol.confirmation_time E b := by
  unfold Protocol.confirmation_time
  exact Int.add_le_add_right (Protocol.proposal_time_mono E hab) _


/-! ## The base cone at the slot after a genuine confirmation -/

/-- The per-member vote witness of the base cone.

One honest slot-`s` vote head at the band carries the protected ancestor into
the next duty's frozen candidate tree; the duty's own prepared anchor then
decides which of the two closures applies. Both
`baseCone_succ_of_genuineSupporter` and its root-comparable relaxation call
this at each slot-`(s + 1)` committee member. -/
private theorem baseConeVoteWitness_of_supporter
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {s : Slot} {v u w : V}
    (hv : v ∈ rho.honest) (hu : u ∈ rho.honest) (hw : w ∈ rho.honest)
    (hwcommittee : w ∈ S.E.committee (s + 1))
    {T C : Block V} {Hn : NamedBlock V}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.confirmation_time S.E (s + 1) ≤ rho.horizon)
    (heligible : Protocol.voters_count S.E
        (confLate S.E (Proofs.Optimistic.confStore S rho v s) s) s <
      2 * Protocol.goldfish_score S.E (Proofs.Optimistic.confStore S rho v s).T
        (confVotes S.E (Proofs.Optimistic.confStore S rho v s) s)
        (confVotes S.E (Proofs.Optimistic.confStore S rho v s) s) s T)
    (hTC : Block.Preceq T C)
    (hHerase : Hn.erase = voteDutyHead S rho u s)
    (hHrun : RunBlock S rho Hn)
    (hCH : Block.Preceq C Hn.erase)
    (hHthin : M - 1 ≤ (Protocol.derive_named S.E S.cfg Hn).h)
    (hfrontier : (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).h_max = M)
    (hgate : (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).h_j + 2 ≤ M)
    (hrootT : Block.Preceq (Protocol.get_fg_root
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) T)
    (hanchor : Block.compatible (voterAnchorAt S rho w (s + 1)) T = true) :
    ∃ X : NamedBlock V, Block.Preceq T X.erase ∧ RunBlock S rho X ∧
      NamedRun.emits S rho w (Object.gfVote ⟨w, s + 1, X.erase.root⟩)
        (Protocol.vote_time S.E (s + 1)) := by
  have hread : Protocol.vote_time S.E (s + 1) ≤ rho.horizon :=
    (Protocol.vote_time_le_confirmation_time S.E (s + 1)).trans hhor
  have hTH : Block.Preceq T Hn.erase := Block.preceq_trans hTC hCH
  have hTHead : Block.Preceq T (voteDutyHead S rho u s) := by
    rw [← hHerase]
    exact hTH
  have hvisible := voteHeadVisible_at_nextDuty S adm hu hw hpost hhor hrootT
    hTHead
  have hslot : (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s = s + 1 := by
    simpa only [Proofs.Optimistic.toHealing_slot] using
      Proofs.Optimistic.voteDutyStore_slot S rho w (s + 1)
  have hHprocessed : Hn.erase ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s := by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    rw [hslot, Nat.add_sub_cancel]
    refine ⟨?_, Or.inl ?_⟩
    · simpa only [hHerase, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hvisible.1
    · simpa only [hHerase, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hvisible.2
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hM : 1 ≤ M :=
    (Nat.succ_le_succ (Nat.zero_le 1)).trans
      ((Nat.le_add_left 2
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).h_j).trans hgate)
  have hTfilteredPre : T ∈ Protocol.get_filtered_block_tree
      (rho.storeBeforeTime S w
        (Protocol.vote_time S.E (s + 1))).toHealing.toFG := by
    refine frontierAncestor_filtered_of_gateOff S adm hsb hw hread
      hvisible.1 hHerase hHrun hTHead hHthin hM ?_ ?_ ?_
    · simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore] using hfrontier
    · simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore] using hgate
    · simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore] using hrootT
  have hTfiltered : T ∈ Protocol.get_filtered_block_tree
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG := by
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using hTfilteredPre
  have hmax : (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).h_max ≤
      (Protocol.derive_named S.E S.cfg Hn).h + 1 := by
    rw [hfrontier]
    exact Nat.sub_le_iff_le_add.mp hHthin
  have hcandidate : T ∈ Proofs.Optimistic.voter_candidate_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing :=
    namedAncestorCandidate_of_processedDescendant_and_hMax S adm hw
      hHprocessed hHrun hTH hTfiltered hmax
  have hhor' : Protocol.confirmation_time S.E s ≤ rho.horizon :=
    (confirmation_time_mono_local S.E (Nat.le_succ s)).trans hhor
  rcases nextVoteAdoption_of_recovery_after_gst_compatible S adm hv hw hpost
    hhor' hrootT hanchor hcandidate with hbelow | hd
  · obtain ⟨X, hXerase, hXrun⟩ := seedVoteDutyHead_runBlock S adm hw (s + 1)
    refine ⟨X, ?_, hXrun, ?_⟩
    · rw [hXerase]
      exact Block.preceq_trans hbelow
        (voterAnchorAt_preceq_voterHeadAt S rho w (s + 1))
    · simpa only [hXerase] using
        seedVoteDutyHead_emits S adm hw (Nat.succ_pos s) hwcommittee hread
  · exact honestVoteWitness_of_nextVoteAdoption S rho
      (Proofs.Optimistic.confStore S rho v s) s T heligible hw hwcommittee hd



set_option linter.unusedVariables false in
/-- The `baseCone_succ_of_genuineSupporter` root floor, relaxed to mere
comparability with `T` at each duty. When the duty's own FG root is below
`T` this is the earlier proof, unchanged. When `T` is below the duty's own
FG root instead, no relay of the supporter's head is needed at all: the
prepared head always descends the read's FG root
(`fgRoot_preceq_voterHeadAt`), so it already descends `T`, and the vote
witness is that duty's own head. -/
theorem baseCone_succ_of_genuineSupporter_rootComparable (S : Setup V) {rho : Run V}
    (adm : Admissible S rho) (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {s : Slot} {v : V} (hv : v ∈ rho.honest) {T C : Block V}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.confirmation_time S.E (s + 1) ≤ rho.horizon)
    (hC : GenuineConfirmationWith
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).cache)
      S.E S.hc (Proofs.Optimistic.confStore S rho v s) s C)
    (hTC : Block.Preceq T C)
    (hTrun : ∃ Tn : NamedBlock V, Tn.erase = T ∧ RunBlock S rho Tn)
    (hframe : ∀ w ∈ rho.honest,
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).h_max = M ∧
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).h_j + 2 ≤ M ∧
      (Block.Preceq (Protocol.get_fg_root
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) T ∨
        Block.Preceq T (Protocol.get_fg_root
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG)))
    (hsupp : ∃ u ∈ rho.honest, ∃ Hn : NamedBlock V,
      Hn.erase = voteDutyHead S rho u s ∧ RunBlock S rho Hn ∧
        Block.Preceq C Hn.erase ∧
        M - 1 ≤ (Protocol.derive_named S.E S.cfg Hn).h)
    (hanchor : ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w (s + 1)) T = true) :
    NamedHonestVotesCone S rho (s + 1) (fun X => Block.Preceq T X) := by
  obtain ⟨u, hu, Hn, hHerase, hHrun, hCH, hHthin⟩ := hsupp
  intro w hw hwcommittee
  have hread : Protocol.vote_time S.E (s + 1) ≤ rho.horizon :=
    (Protocol.vote_time_le_confirmation_time S.E (s + 1)).trans hhor
  rcases (hframe w hw).2.2 with hcase1 | hcase2
  · exact baseConeVoteWitness_of_supporter S adm hfb hv hu hw hwcommittee hpost
      hhor (ancestorConfirmation_eligible_of_preceq S.E S.hc
        (Proofs.Optimistic.confStore S rho v s) s hTC hC)
      hTC hHerase hHrun hCH hHthin (hframe w hw).1 (hframe w hw).2.1
      hcase1 (hanchor w hw)
  · have hTX : Block.Preceq T (voteDutyHead S rho w (s + 1)) := by
      refine Block.preceq_trans ?_ (fgRoot_preceq_voterHeadAt S rho w (s + 1))
      simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock, Run.storeBeforeTime] using hcase2
    obtain ⟨X, hXerase, hXrun⟩ := seedVoteDutyHead_runBlock S adm hw (s + 1)
    refine ⟨X, ?_, hXrun, ?_⟩
    · rw [hXerase]
      exact hTX
    · simpa only [hXerase] using
        seedVoteDutyHead_emits S adm hw (Nat.succ_pos s) hwcommittee hread


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
