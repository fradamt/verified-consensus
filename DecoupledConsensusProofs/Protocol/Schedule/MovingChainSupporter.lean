module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.MovingChainSlotStep

@[expose] public section

/-!
# The absorbed confirmation reaches the next slot's vote cone

`MovingChainSlotStepRun` refutes the statement that every honest slot-`c` vote
misses a genuine slot-`c` confirmation. This module turns that refutation into
the fact the slot step consumes.

The chain has three links.

1. **A supporter exists.** Negating the refuted cone at one honest committee
   member's own vote-duty head yields a member whose slot-`c` head is at or
   above the confirmation. The head is an `Proofs.Optimistic.HonestHead` of slot `c`,
   because an honest committee member's scheduled tick emits exactly the block
   its duty computed.
2. **The supporter's head is available, so the confirmation is.** The
   slot-`c` heads are admitted at every honest node before `t_c + 2Δ`, one
   network delay after the vote instant; ancestors of an admitted block are
   present and stamped no later, so the confirmation is inside the frozen
   processed view read by the slot-`(c+1)` vote duty at `t_c + 5Δ`.
3. **The capture lemma applies.** With the confirmation visible, below the
   endpoint and inside the local frontier band, the slot-`(c+1)` walk cannot
   leave it: `genuineConfirmation_preceq_nextVoteDutyHead_of_endpointBand`
   puts every honest slot-`(c+1)` head at or above it.

The result is the slot-`(c+1)` vote cone above the WINDOW endpoint, which is
the one input the next entry state's three obligations all reduce to.
-/

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

/-- `Time` is a reducible abbreviation of `Int`, so every numeric step goes
through a helper with bare `Int` binders. -/
private theorem int_add_le_add_six {x d : Int} (hd : 0 < d) :
    x + d ≤ x + 6 * d := by omega

private theorem int_add_le_add_two {x d : Int} (hd : 0 < d) :
    x + d ≤ x + 2 * d := by omega

private theorem voteTime_le_confirmationTime (E : Env V) (s : Slot) :
    Protocol.vote_time E s ≤ Protocol.confirmation_time E s := by
  simp only [Protocol.vote_time, Protocol.confirmation_time]
  exact int_add_le_add_six E.Δ_pos

/-- `t_{s+1} + Δ ≤ t_s + 6Δ`: the next slot's vote read precedes this slot's
confirmation evaluation. -/
private theorem voteTimeSucc_le_confirmationTime (E : Env V) (s : Slot) :
    Protocol.vote_time E (s + 1) ≤ Protocol.confirmation_time E s := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ]
  simp only [Protocol.vote_time, Protocol.support_cutoff]
  exact int_add_le_add_two E.Δ_pos

/-! ## 1. An honest committee member's tick emits its own duty head -/

/-- **An honest committee member's scheduled slot-`s` tick emits a Goldfish
vote naming exactly the block its own vote duty computed.**

The head stays the prepared `voteDutyHead` (`Internal.voterHeadAt`) throughout: it
is shown to be a member of the vote duty read's own retained tree and lifted
from there to a named run block, so no bare/prepared head agreement is used.
The named block is existential because `RunBlock` ranges over `NamedBlock`. -/
theorem voteDutyHead_runBlock_and_emits
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hs : 0 < s)
    (hhor : Protocol.vote_time S.E s ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) (hcommittee : w ∈ S.E.committee s) :
    ∃ X : NamedBlock V, X.erase = voteDutyHead S rho w s ∧
      RunBlock S rho X ∧
      NamedRun.emits S rho w (Object.gfVote ⟨w, s, X.erase.root⟩)
        (Protocol.vote_time S.E s) := by
  let t := Protocol.vote_time S.E s
  let pre := NamedRun.stateBeforeTime S rho t w
  let n := NamedActionReads.confirmationReadFrom S pre t
  let gc := NamedProfile.gradeContract n.cache
  let tree := Protocol.voter_filtered_block_tree S.E n.st.core n.st.core.s
  let votes := Protocol.voter_view S.E n.st.core.toHealing.toFG.toSG.toGoldfishStore n.st.core.s
  let support :=
    Protocol.voter_support_view S.E n.st.core.toHealing.toFG.toSG.toGoldfishStore n.st.core.s
  let head := Protocol.get_head_in_tree_with_layer gc S.E S.hc n.st.core.toHealing
    tree votes support (n.st.core.s - 1)
  have hslot : n.st.core.s = s := Proofs.Optimistic.voteDutyRead_slot S rho w s
  have hcommittee' : (S.node w).val_index ∈ S.E.committee n.st.core.s := by
    rw [S.node_val_index, hslot]
    exact hcommittee
  have hinvPre : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg pre.st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t w).1
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg n.st :=
    Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg pre.st t hinvPre
  have hroot : Protocol.get_fg_root n.st.core.toHealing.toFG ∈ n.st.core.T :=
    Proofs.NamedStoreRoots.fg_root_mem n.st hinv.1.2
  have htree : tree ⊆ n.st.core.T := by
    dsimp only [tree]
    rw [← Proofs.Optimistic.voter_candidate_tree_eq_protocol_voter_filtered_block_tree]
    intro C hC
    simp only [Proofs.Optimistic.voter_candidate_tree,
      Protocol.get_filtered_block_tree_from,
      Protocol.viable_tree, Protocol.finalized_descendants,
      Protocol.voter_processed_block_tree, Finset.mem_filter] at hC
    exact hC.1.1.1.1
  have hanchor : Protocol.get_sg_root_with gc S.E S.hc n.st.core.toHealing
      (S.hc.round_of n.st.core.s) ∈ n.st.core.T :=
    Proofs.NamedConfirmationMembership.runtime_anchor_mem n.cache
      S.E S.hc n.st.core.toHealing (S.hc.round_of n.st.core.s) hroot
  have hhead : head ∈ n.st.core.T := by
    dsimp only [head]
    rw [Proofs.Optimistic.get_head_in_tree_split_with]
    exact Proofs.Records.ghost_mem_of _ _ hanchor htree
  have hheadPre : head ∈ pre.st.core.T := hhead
  obtain ⟨X, hXe, hXrun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hw t hheadPre
  have hu : (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc (S.node w) n.st).2 =
      some ⟨(S.node w).val_index, n.st.core.s, head.root⟩ := by
    simp only [Protocol.NamedDuties.goldfish_vote_with,
      Protocol.goldfish_vote_with]
    rw [if_pos hcommittee']
    rfl
  have ho : Object.gfVote ⟨(S.node w).val_index, n.st.core.s, head.root⟩ ∈
      (on_tick_emit S w pre t).2 :=
    Proofs.Optimistic.on_tick_emit_vote_mem S w pre s hs hu
  have hemit := Proofs.Optimistic.emits_of_on_tick_emit S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hw
    (Proofs.Optimistic.publicTime_vote_time S s) (Proofs.Optimistic.vote_time_nonneg S.E s)
    hhor ho
  refine ⟨X, hXe, hXrun, ?_⟩
  simpa only [hXe, S.node_val_index, hslot] using hemit

/-- The duty head of an honest committee member is an honest slot head.
`Proofs.Optimistic.HonestHead` already carries its run block as a named witness under
the erasure, which is exactly what the producer above returns. -/
theorem honestHead_voteDutyHead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hs : 0 < s)
    (hhor : Protocol.vote_time S.E s ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) (hcommittee : w ∈ S.E.committee s) :
    Proofs.Optimistic.HonestHead S rho s (voteDutyHead S rho w s) := by
  obtain ⟨X, hXe, hXrun, hemit⟩ :=
    voteDutyHead_runBlock_and_emits S adm hs hhor hw hcommittee
  exact ⟨w, hw, hcommittee, ⟨X, hXe, hXrun⟩,
    by simpa only [hXe] using hemit⟩

/-! ## 2. The supporter -/



/-- The contract-carrying twin of `genuineConfirmation_exists_honestSupporter`
(the corresponding branch). Same statement and same proof with the confirmation taken
at an arbitrary grade contract, which is what every confirmation on the named
route carries; the default-contract form above is unchanged. the corresponding branch's
`MovingSlotPreEntryN.genuineConfirmation_preceq_voteDutyHead` consumes this. -/
theorem genuineConfirmation_exists_honestSupporter_with
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (contract : Protocol.GradeContract V)
    {c : Slot} (hc : 0 < c)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hhor : Protocol.confirmation_time S.E c ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest)
    (hres : Proofs.Optimistic.HeadsResolveIn S rho c
      (Proofs.Optimistic.confStore S rho v c).T
      (Proofs.Optimistic.confStore S rho v c).timestamp_block)
    {D : Block V}
    (hgenuine : GenuineConfirmationWith contract S.E S.hc
      (Proofs.Optimistic.confStore S rho v c) c D) :
    ∃ x ∈ rho.honest, x ∈ S.E.committee c ∧
      Block.Preceq D (voteDutyHead S rho x c) := by
  have hvoteHor : Protocol.vote_time S.E c ≤ rho.horizon :=
    (voteTime_le_confirmationTime S.E c).trans hhor
  by_contra hno
  refine genuineConfirmation_not_allHonestVotesOff_with S adm hcom contract hc
    hpost hhor hv hres hgenuine ?_
  intro x hx hxc
  obtain ⟨X, hXe, hXrun, hemit⟩ :=
    voteDutyHead_runBlock_and_emits S adm hc hvoteHor hx hxc
  exact ⟨X, fun hpre => hno ⟨x, hx, hxc, hXe ▸ hpre⟩, hXrun, hemit⟩

#print axioms genuineConfirmation_exists_honestSupporter_with

/-! ## 3. Visibility -/

/-- An ancestor of an available honest slot-`s` head is inside the frozen
processed view of the slot-`(s+1)` vote duty.

This is `voterProcessedConeEndpoint_of_availableBefore` with the cone premise
replaced by one named head, which is what a single supporter supplies. -/
theorem voterProcessed_of_availableBefore_of_honestHead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} {B X : Block V} {w : V}
    (havailable : HonestHeadsAvailableBefore S rho s w
      (Protocol.support_cutoff S.E s))
    (hhead : Proofs.Optimistic.HonestHead S rho s X)
    (hBX : Block.Preceq B X) :
    B ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s := by
  let duty := Proofs.Optimistic.voteDutyStore S rho w (s + 1)
  rcases havailable X hhead with hXgen | hXadmit
  · have hBgen : B = Block.genesis :=
      Block.preceq_antisymm (hXgen ▸ hBX) (Protocol.preceq_genesis B)
    subst B
    have hgenesis := genesis_mem_and_stamp_storeBeforeTime S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed w
        (Protocol.vote_time S.E (s + 1))
      (Protocol.view_freeze S.E s)
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    exact ⟨by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Proofs.Optimistic.slotOf_vote_time,
        Protocol.Store.toHealing, Nat.add_sub_cancel] using hgenesis.1,
      Or.inl (by
        simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, Proofs.Optimistic.slotOf_vote_time,
          Protocol.Store.toHealing, Nat.add_sub_cancel] using hgenesis.2)⟩
  · have hvisibleB := Proofs.Optimistic.admittedBefore_ancestor_mem_and_stamp_at
      S adm hXadmit hBX
      (le_trans
        (le_of_lt (Proofs.Optimistic.support_cutoff_lt_view_freeze S.E s))
        (le_of_lt (view_freeze_lt_vote_time_succ S.E s)))
    have hBstampCut : stampedBefore duty.toHealing.toFG.toSG.toGoldfishStore.timestamp_block
        (Protocol.support_cutoff S.E s) B = true := by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Proofs.Optimistic.slotOf_vote_time,
        Protocol.Store.toHealing, Nat.add_sub_cancel] using hvisibleB.2
    have hBstampFreeze : stampedBefore duty.toHealing.toFG.toSG.toGoldfishStore.timestamp_block
        (Protocol.view_freeze S.E s) B = true := by
      rw [stampedBefore_eq_occurrenceBefore] at hBstampCut ⊢
      exact occurrenceBefore_mono
        (le_of_lt (Proofs.Optimistic.support_cutoff_lt_view_freeze S.E s))
        hBstampCut
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    exact ⟨by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Proofs.Optimistic.slotOf_vote_time,
        Protocol.Store.toHealing, Nat.add_sub_cancel] using hvisibleB.1,
      Or.inl (by
        simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, Proofs.Optimistic.slotOf_vote_time,
          Protocol.Store.toHealing, Nat.add_sub_cancel] using hBstampFreeze)⟩


/-! ## 4. The pre-entry state

`MovingSlotEntryState` carries three forward-looking fields — the slot's own
vote cone, the transferred head equality and the compatibility of the previous
slot's confirmations — and those are exactly the three obligations the slot
step has to discharge. Everything the discharge itself reads is the OTHER
half of the record: the moving history through the inclusive proposal cursor,
its two endpoint values, and the previous slot's vote cone.

That half is named here, so the same read lemmas serve the current entry state
and the next one, which does not exist yet while its obligations are being
proved. -/





/-! ## 5. The three reads of the slot-`(c+1)` window, against `Prev` -/




















/-- An available honest slot-`c` head above `P` puts `P` in every honest store
read at or after the slot-`c` support cutoff. Membership half of
`storeBeforeTime_mem_stamp_of_cone`. -/
private theorem w4_mem_of_cone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {c : Slot} {P : Block V} {w : V} {Gamma : Time}
    (havailable : HonestHeadsAvailableBefore S rho c w
      (Protocol.support_cutoff S.E c))
    (hcut : Protocol.support_cutoff S.E c ≤ Gamma)
    (hvotes : NamedHonestVotesCone S rho c (fun X => Block.Preceq P X)) :
    P ∈ (rho.storeBeforeTime S w Gamma).T := by
  have hpositive : 0 < ((S.E.committee c) ∩ rho.honest).card := by
    have hcc := hcom c
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpositive
  have hxCommittee : x ∈ S.E.committee c := (Finset.mem_inter.mp hx).1
  have hxHonest : x ∈ rho.honest := (Finset.mem_inter.mp hx).2
  obtain ⟨X, hPX, hXrun, hXemit⟩ := hvotes x hxHonest hxCommittee
  rcases havailable X.erase
      ⟨x, hxHonest, hxCommittee, ⟨X, rfl, hXrun⟩, hXemit⟩ with
    hXgen | hXadmit
  · have hPgen : P = Block.genesis :=
      Block.preceq_antisymm (hXgen ▸ hPX) (Protocol.preceq_genesis P)
    rw [hPgen]
    exact (genesis_mem_and_stamp_storeBeforeTime S
      adm.toNamedScheduleWellFormed w Gamma
      (Protocol.support_cutoff S.E c)).1
  · exact (Proofs.Optimistic.admittedBefore_ancestor_mem_and_stamp_at
      S adm hXadmit hPX hcut).1


/-- Public form of the membership half of the cone argument: an available
honest slot-`c` head above `P` puts `P` in every honest store read at or after
the slot-`c` support cutoff. The packaged `storeBeforeTime_mem_stamp_of_cone`
is in `MovingChainBatchRun`, which imports this module, so consumers below it
need this form (the corresponding branch). -/
theorem mem_storeBeforeTime_of_cone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {c : Slot} {P : Block V} {w : V} {Gamma : Time}
    (havailable : HonestHeadsAvailableBefore S rho c w
      (Protocol.support_cutoff S.E c))
    (hcut : Protocol.support_cutoff S.E c ≤ Gamma)
    (hvotes : NamedHonestVotesCone S rho c (fun X => Block.Preceq P X)) :
    P ∈ (rho.storeBeforeTime S w Gamma).T :=
  w4_mem_of_cone S adm hcom havailable hcut hvotes

/-- A run block whose erasure an honest reader holds is one of that reader's
named bodies. -/
theorem mem_bodies_of_mem_T
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {t : Time} {B : NamedBlock V}
    (hBrun : RunBlock S rho B)
    (hmem : B.erase ∈ (rho.storeBeforeTime S v t).core.T) :
    B ∈ (rho.storeBeforeTime S v t).bodies := by
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedScheduleWellFormed t
  have hmemN : B.erase ∈ (rho.stateBefore S n v).st.core.T := by
    simpa only [Run.storeBeforeTime, hn] using hmem
  obtain ⟨D, hDmem, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n v hmemN
  have hDrun : RunBlock S rho D := Proofs.Bridges.runBlock_of_stateBefore_mem S hv hDmem
  have hDB : D = B :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      D B hDrun hBrun D B
      (Or.inl (Proofs.NamedAncestry.named_self D)) (Or.inr (Proofs.NamedAncestry.named_self B))
      (by rw [← Proofs.NamedWire.erase_root D, ← Proofs.NamedWire.erase_root B, hDerase])
  have hBmem : B ∈ (rho.stateBefore S n v).st.bodies := hDB ▸ hDmem
  simpa only [Run.storeBeforeTime, hn] using hBmem

#print axioms mem_storeBeforeTime_of_cone
#print axioms mem_bodies_of_mem_T

/-! ### The named vote anchor -/
theorem movingSlotPreEntryN_prevRunAt_core
    (S : Setup V) {rho : Run V}
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hstartTime : t1 ≤ Protocol.proposal_time S.E (c + 1))
    (hprevEndpoint : ∃ EndAt : Nat → Block V,
      MovingFrontierChainStateN S rho t1 M0 (strictEventIndex rho t1)
          (inclusiveEventIndex rho
            (Protocol.proposal_time S.E (c + 1))) EndAt ∧
        EndAt (strictEventIndex rho
          (Protocol.proposal_time S.E (c + 1))) = Prev ∧
        EndAt (inclusiveEventIndex rho
          (Protocol.proposal_time S.E (c + 1))) = End) :
    ∃ E : NamedBlock V, E.erase = Prev ∧ RunBlock S rho E := by
  obtain ⟨EndAt, hhistory, hprev, _hEnd⟩ := hprevEndpoint
  set k := strictEventIndex rho (Protocol.proposal_time S.E (c + 1)) with hk
  have hpre : MovingFrontierChainStateN S rho t1 M0
      (strictEventIndex rho t1) k EndAt :=
    hhistory.prefix (strictEventIndex_mono rho hstartTime)
      (strictEventIndex_le_inclusiveEventIndex rho _)
  obtain ⟨E, hE, hErun⟩ := hpre.endpointRun k hpre.start_le (Nat.le_refl k)
  exact ⟨E, by rw [hE, hprev], hErun⟩

/-- The FG root at the slot-`(c+1)` vote read is on the previous endpoint's
chain, N history. -/
theorem movingSlotPreEntryN_voteRoot_preceq_prev_core
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
    {w : V} (hw : w ∈ rho.honest) :
    Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w
          (Protocol.vote_time S.E (c + 1))).toHealing.toFG) Prev := by
  obtain ⟨EndAt, hhistory, hprev, _hEnd⟩ := hprevEndpoint
  set k := strictEventIndex rho (Protocol.proposal_time S.E (c + 1)) with hk
  have hpre : MovingFrontierChainStateN S rho t1 M0
      (strictEventIndex rho t1) k EndAt :=
    hhistory.prefix (strictEventIndex_mono rho hstartTime)
      (strictEventIndex_le_inclusiveEventIndex rho _)
  obtain ⟨E, hE, hErun⟩ := hpre.endpointRun k hpre.start_le (Nat.le_refl k)
  rw [← hprev, ← hE]
  exact hpre.voteRoot_preceq_endpointAtCursor_named S adm hfb (Nat.le_refl k)
    hw hstartTime hE hErun

/-- The selected FG root at the slot-`c` confirmation read is on the previous
endpoint's chain, N history. -/
theorem movingSlotPreEntryN_confRoot_preceq_prev_core
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
    {w : V} (hw : w ∈ rho.honest) :
    Block.Preceq (confRoot (Proofs.Optimistic.confStore S rho w c)) Prev := by
  obtain ⟨EndAt, hhistory, hprev, _hEnd⟩ := hprevEndpoint
  set k := strictEventIndex rho (Protocol.proposal_time S.E (c + 1)) with hk
  have hpre : MovingFrontierChainStateN S rho t1 M0
      (strictEventIndex rho t1) k EndAt :=
    hhistory.prefix (strictEventIndex_mono rho hstartTime)
      (strictEventIndex_le_inclusiveEventIndex rho _)
  obtain ⟨E, hE, hErun⟩ := hpre.endpointRun k hpre.start_le (Nat.le_refl k)
  have hrootRaw :=
    hpre.confRoot_preceq_endpointAtCursor_named S adm hfb (Nat.le_refl k) hw
      hstartTime hE hErun
  rw [← hprev, ← hE]
  simpa only [confRoot, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
    Run.storeBeforeTime] using hrootRaw

/-- The frontier band at the slot-`(c+1)` vote read, N history, on the named
derivation of the endpoint witness. -/
theorem movingSlotPreEntryN_voteFrontier_sub_one_le_prevHeight_named_core
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
    {w : V} (hw : w ∈ rho.honest)
    {E : NamedBlock V} (hE : E.erase = Prev) (hErun : RunBlock S rho E) :
    (rho.storeBeforeTime S w
        (Protocol.vote_time S.E (c + 1))).core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg E).h := by
  obtain ⟨EndAt, hhistory, hprev, _hEnd⟩ := hprevEndpoint
  set k := strictEventIndex rho (Protocol.proposal_time S.E (c + 1)) with hk
  have hpre : MovingFrontierChainStateN S rho t1 M0
      (strictEventIndex rho t1) k EndAt :=
    hhistory.prefix (strictEventIndex_mono rho hstartTime)
      (strictEventIndex_le_inclusiveEventIndex rho _)
  exact hpre.readFrontier_sub_one_le_endpointAtCursor_named S adm hfb
    (fun _q hq => Protocol.action_time_lt_proposal_of_lt_vote S hq)
    (Nat.le_refl k) hw (by rw [hE, hprev]) hErun


/-- The same band on the reader's own chain-state map, N history. -/
theorem movingSlotPreEntryN_voteFrontier_sub_one_le_prevHeightSigma_core
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
    {w : V} (hw : w ∈ rho.honest)
    (hmem : Prev ∈
      (rho.storeBeforeTime S w (Protocol.vote_time S.E (c + 1))).core.T) :
    (rho.storeBeforeTime S w
        (Protocol.vote_time S.E (c + 1))).core.h_max - 1 ≤
      ((rho.storeBeforeTime S w
        (Protocol.vote_time S.E (c + 1))).core.σ Prev).h := by
  obtain ⟨E, hE, hErun⟩ :=
    movingSlotPreEntryN_prevRunAt_core S hstartTime hprevEndpoint
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedScheduleWellFormed (Protocol.vote_time S.E (c + 1))
  have hmemN : E.erase ∈ (rho.stateBefore S n w).st.core.T := by
    simpa only [Run.storeBeforeTime, hn, hE] using hmem
  obtain ⟨D, hDmem, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n w hmemN
  have hDrun : RunBlock S rho D := Proofs.Bridges.runBlock_of_stateBefore_mem S hw hDmem
  have hDE : D = E :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      D E hDrun hErun D E
      (Or.inl (Proofs.NamedAncestry.named_self D)) (Or.inr (Proofs.NamedAncestry.named_self E))
      (by rw [← Proofs.NamedWire.erase_root D, ← Proofs.NamedWire.erase_root E, hDerase])
  have hbodies : E ∈ (rho.storeBeforeTime S w
      (Protocol.vote_time S.E (c + 1))).bodies := by
    simpa only [Run.storeBeforeTime, hn] using (hDE ▸ hDmem)
  have hview : (rho.storeBeforeTime S w
      (Protocol.vote_time S.E (c + 1))).core.σ E.erase =
      Protocol.derive_named S.E S.cfg E := by
    simpa only [Run.storeBeforeTime] using
      Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho
        (Protocol.vote_time S.E (c + 1)) w E
        (by simpa only [Run.storeBeforeTime] using hbodies)
  rw [← hE, hview]
  exact movingSlotPreEntryN_voteFrontier_sub_one_le_prevHeight_named_core
    S adm hfb hstartTime hprevEndpoint hw hE hErun

#print axioms movingSlotPreEntryN_prevRunAt_core
#print axioms movingSlotPreEntryN_voteRoot_preceq_prev_core
#print axioms movingSlotPreEntryN_confRoot_preceq_prev_core
#print axioms movingSlotPreEntryN_voteFrontier_sub_one_le_prevHeight_named_core
#print axioms movingSlotPreEntryN_voteFrontier_sub_one_le_prevHeightSigma_core


/-- The PREPARED slot-`(c+1)` vote anchor is on the previous endpoint's chain,
N history. `GoldfishConeVoteInputs'` reads `voterAnchorAt`, the contract's
anchor at the vote-duty read, not `healAnchor` on the erased duty store, so the
default-anchor core above does not serve it (the corresponding branch). -/
theorem movingSlotPreEntryN_voterAnchorAt_preceq_prev_core
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
    (hslotHor : Protocol.confirmation_time S.E c ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) :
    Block.Preceq (voterAnchorAt S rho w (c + 1)) Prev := by
  obtain ⟨EndAt, hhistory, hprev, _hEnd⟩ := hprevEndpoint
  set k := strictEventIndex rho (Protocol.proposal_time S.E (c + 1)) with hk
  have hpre : MovingFrontierChainStateN S rho t1 M0
      (strictEventIndex rho t1) k EndAt :=
    hhistory.prefix (strictEventIndex_mono rho hstartTime)
      (strictEventIndex_le_inclusiveEventIndex rho _)
  obtain ⟨E, hE, hErun⟩ := hpre.endpointRun k hpre.start_le (Nat.le_refl k)
  have hvoteHor : Protocol.vote_time S.E (c + 1) ≤ rho.horizon :=
    (voteTimeSucc_le_confirmationTime S.E c).trans hslotHor
  have hrootRaw : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w
          (Protocol.vote_time S.E (c + 1))).toHealing.toFG) (EndAt k) := by
    rw [← hE]
    exact hpre.voteRoot_preceq_endpointAtCursor_named S adm hfb (Nat.le_refl k)
      hw hstartTime hE hErun
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
        ((le_of_lt (Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos (r + 1))).trans hread))
  have hactionHor : S.a r ≤ rho.horizon :=
    (le_of_lt (Int.lt_add_of_pos_right (S.a r) S.E.Δ_pos)).trans
      ((action_add_delta_le_next_Γ_neg1 S r).trans hcut)
  have hupper := hpre.previousActionCarriersPreceqAtRead S adm ht1 hactionHor
    (Protocol.action_time_lt_proposal_of_lt_vote S hbefore)
    (Nat.le_refl k)
  rw [← hprev]
  exact voterAnchorAt_preceq_of_previousCarriers S adm hfb hround hpostAction
    hcut hvoteHor hupper hw hroot

#print axioms movingSlotPreEntryN_voterAnchorAt_preceq_prev_core

/-! ## 6. The window cone -/

/-- **The slot-`(c+1)` named vote cone above the WINDOW endpoint.**

This is the N-history twin of `MovingSlotEntryState.windowVotesCone`. The
endpoint-band capture is applied to the prepared confirmation output, while
the cursor and local height bridges use the named moving history. -/
theorem MovingSlotEntryStateN.windowVotesCone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hentry : MovingSlotEntryStateN S rho t1 M0 (c + 1) Prev End)
    (hc : 0 < c)
    {r : Round}
    (hround : S.hc.round_of (c + 1) = r + 1)
    (ht1 : t1 ≤ S.a r)
    (hpostAction : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hpostProp : S.E.t_GST ≤ Protocol.proposal_time S.E c)
    (hslotHor : Protocol.confirmation_time S.E c ≤ rho.horizon)
    {Next : Block V}
    (hfrontier : MovingSlotFrontierAt S rho c End Next) :
    NamedHonestVotesCone S rho (c + 1)
      (fun X => Block.Preceq Next X) := by
  rcases hfrontier.source with rfl | ⟨v, hv, hgenuine⟩
  · exact hentry.votes
  obtain ⟨EndAt, hhistory, hprev, _hEnd⟩ := hentry.prevEndpoint
  set k := strictEventIndex rho (Protocol.proposal_time S.E (c + 1)) with hk
  have hpre : MovingFrontierChainStateN S rho t1 M0
      (strictEventIndex rho t1) k EndAt :=
    hhistory.prefix (strictEventIndex_mono rho hentry.startTime)
      (strictEventIndex_le_inclusiveEventIndex rho _)
  obtain ⟨E0, hE0, hE0run⟩ :=
    hpre.endpointRun k hpre.start_le (Nat.le_refl k)
  have hprevVotes : NamedHonestVotesCone S rho c
      (fun X => Block.Preceq (EndAt k) X) := by
    rw [hprev]
    simpa only [Nat.add_sub_cancel] using hentry.prevVotes
  have hPrevNext : Block.Preceq Prev Next :=
    Block.preceq_trans hentry.prevLe hfrontier.oldPreceq
  intro w hw hwcommittee
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
  have hrootNext : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (c + 1)).toHealing.toFG) Next := by
    exact Block.preceq_trans hroot (by
      simpa only [hE0, hprev] using hPrevNext)
  have hgenuine' : GenuineConfirmation (contract :=
      NamedProfile.gradeContract (confirmationInputRead S rho v c).cache)
      S.E S.hc (Proofs.Optimistic.confStore S rho v c) c Next := by
    exact ⟨hgenuine.selected, hgenuine.genuine⟩
  have hprocessedOld :=
    Protocol.voterProcessedTarget_of_genuineConfirmation_after_gst
      S adm hv hw hpostProp hslotHor hgenuine' hrootNext
  have hprocessed : Next ∈
      Protocol.voter_processed_block_tree S.E
        (voteDutyRead S rho w (c + 1)).st.core.toHealing.toFG.toSG.toGoldfishStore
        (voteDutyRead S rho w (c + 1)).st.core.s := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using hprocessedOld
  have htime : Protocol.vote_time S.E (c + 1) ≤
      Protocol.confirmation_time S.E c := by
    rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E c]
    exact Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)
  have hmax := storeBeforeTime_hMax_mono S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed w htime
  have hconfBand := hpre.confFrontier_sub_one_le_endpointAtCursor_named
    S adm hfb (c := c) (Nat.le_refl k) hw hE0 hE0run
  have hendpointMono : ∀ {a b : Nat},
      strictEventIndex rho t1 ≤ a → a ≤ b → b ≤ k →
      Block.Preceq (EndAt a) (EndAt b) := by
    intro a b ha hab hb
    induction hab with
    | refl => exact Block.preceq_self _
    | @step b hab ih =>
        exact Block.preceq_trans (ih (Nat.le_trans (Nat.le_succ b) hb))
          (hpre.endpointMono b (ha.trans hab) (Nat.lt_of_succ_le hb))
  have hNextCore : Next ∈
      (voteDutyRead S rho w (c + 1)).st.core.T := by
    have hdata := hprocessed
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter] at hdata
    simpa only [Protocol.Store.toHealing] using hdata.1
  have hNextPre : Next ∈
      (rho.stateBeforeTime S (Protocol.vote_time S.E (c + 1)) w).st.core.T := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      hNextCore
  obtain ⟨N, hNbody, hNerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (Protocol.vote_time S.E (c + 1)) w hNextPre
  have hNrun : RunBlock S rho N := by
    obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (Protocol.vote_time S.E (c + 1))
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw
    simpa only [Run.storeBeforeTime, hn] using hNbody
  have hE0N : NamedBlock.Preceq E0 N :=
    Protocol.namedPreceq_of_runBlock_erase_preceq adm hE0run hNrun (by
      simpa only [hE0, hprev, hNerase] using hPrevNext)
  have hsigma :
      (voteDutyRead S rho w (c + 1)).st.core.σ Next =
        Protocol.derive_named S.E S.cfg N := by
    rw [← hNerase]
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho
        (Protocol.vote_time S.E (c + 1)) w N hNbody
  have hband :
      (voteDutyRead S rho w (c + 1)).st.core.h_max - 1 ≤
        ((voteDutyRead S rho w (c + 1)).st.core.σ Next).h := by
    rw [hsigma]
    have hmaxSub :
        (voteDutyRead S rho w (c + 1)).st.core.h_max - 1 ≤
          (rho.storeBeforeTime S w
            (Protocol.confirmation_time S.E c)).core.h_max - 1 := by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Run.storeBeforeTime] using Nat.sub_le_sub_right hmax 1
    exact hmaxSub.trans (hconfBand.trans
      (Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hE0N))
  have hanchor : Block.Preceq
      (voterAnchorAt S rho w (c + 1)) E0.erase := by
    have hread : S.hc.Γ_0 S.E.Δ (r + 1) ≤
        Protocol.vote_time S.E (c + 1) :=
      Γ_0_le_vote_time_of_round_eq S hround
    have hbefore : S.a r < Protocol.vote_time S.E (c + 1) :=
      (Int.lt_add_of_pos_right (S.a r) S.E.Δ_pos).trans_le
        ((action_add_delta_le_next_Γ_neg1 S r).trans
          ((le_of_lt (Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos (r + 1))).trans hread))
    have hactionHor : S.a r ≤ rho.horizon :=
      (le_of_lt (Int.lt_add_of_pos_right (S.a r) S.E.Δ_pos)).trans
        ((action_add_delta_le_next_Γ_neg1 S r).trans hcut)
    have hupper : ∀ u ∈ rho.honest,
        Block.Preceq (actionSGBlockAt S rho u r) E0.erase := by
      intro u hu
      obtain ⟨j, hj, hout⟩ :=
        honest_emits_exact_actionAttestationAt S adm hu r hactionHor
      have hji : j < k :=
        (emission_index_lt_beforeTime_prefix S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hj
          (action_time_lt_proposal_of_lt_vote S hbefore)).trans_le
          (Nat.le_refl k)
      have hn0j : strictEventIndex rho t1 ≤ j :=
        filterBefore_length_le_tickIndex S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hj ht1
      exact Block.preceq_trans ((hpre.sgCarriers j hn0j hji) hu hj hout)
        (by
          simpa only [hE0] using
            (hendpointMono (a := j + 1) (b := k)
              (hn0j.trans (Nat.le_succ j))
              (Nat.succ_le_iff.mpr hji) (Nat.le_refl k)))
    have hvoteHor : Protocol.vote_time S.E (c + 1) ≤ rho.horizon :=
      htime.trans hslotHor
    exact voterAnchorAt_preceq_of_previousCarriers S adm hfb hround
      hpostAction hcut hvoteHor hupper hw hroot
  have hanchorEnd : Block.Preceq
      (voterAnchorAt S rho w (c + 1)) End :=
    Block.preceq_trans hanchor (by
      simpa only [hE0, hprev] using hentry.prevLe)
  have hbandN :
      (voteDutyRead S rho w (c + 1)).st.core.h_max - 1 ≤
        ((voteDutyRead S rho w (c + 1)).st.core.σ N.erase).h := by
    simpa only [← hNerase] using hband
  have hcapture := genuineConfirmation_preceq_nextVoteDutyHead_of_endpointBand
    S adm hv hw hpostProp hslotHor (B := N)
    (by simpa only [← hNerase] using hgenuine)
    (by simpa only [← hNerase] using hfrontier.oldPreceq)
      hanchorEnd (by simpa only [← hNerase] using hprocessed) hbandN
  obtain ⟨X, hXerase, hXrun, hXemit⟩ :=
    voteDutyHead_runBlock_and_emits S adm (Nat.succ_pos c)
      ((voteTimeSucc_le_confirmationTime S.E c).trans hslotHor)
      hw hwcommittee
  have hcapture' : Block.Preceq Next (voteDutyHead S rho w (c + 1)) := by
    simpa only [voteDutyHead, hNerase] using hcapture
  exact ⟨X, by simpa only [hXerase] using hcapture', hXrun, hXemit⟩

#print axioms MovingSlotEntryStateN.windowVotesCone

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
