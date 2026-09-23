module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.W4HandoffStructures
public import DecoupledConsensusProofs.Execution.MovingChainIterate
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainNextEntry
public import DecoupledConsensusProofs.Protocol.Schedule.W4HandoffBoundary
public import DecoupledConsensusProofs.Protocol.Schedule.W4BoundaryProposalN
public import DecoupledConsensusProofs.Protocol.Schedule.W4CarryBranch2
public import DecoupledConsensusProofs.Protocol.Schedule.W4ExecSuffix
public import DecoupledConsensusProofs.Protocol.Schedule.W4CarryWindow

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# The named base fold from the row-cap handoff boundary ( D1)

Route D needs one thing from the slot fold: the event-indexed moving endpoint,
`W4CompleteStatePin` (`W4ExecSuffixRun.lean:444`) with the NAMED frontier state.
Everything above it, `canonicalSuffixFrom` and `actionHistory`, is branches
w4-fk-proj's available code.

The named state is required rather than the erased one because the two differ
on contract-bearing fields: `MovingFrontierChainState.genuineConfirmations` is
`GenuineConfirmationsPreceqAtIndex` where `MovingFrontierChainStateN`'s is
`NamedGenuineConfirmationsPreceqAtIndex`, and `anchors` likewise; that is the
default-versus-prepared contract line of design note, so no conversion is
written in either direction.

This file starts the chain at its base. Every field on which the two states
differ is quantified `∀ j, n0 ≤ j → j < i → …` and is therefore vacuous at
`i = n0`, and the erased `oldRows` field that the plain record carries is
simply absent from the named one. So the named bootstrap needs no conversion
and no extra input: it is the corresponding branch's `bootstrapAt`
(`W4HandoffStructuresRun.lean:91`) with one field dropped.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.NamedRecoveryRead
open Protocol
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]



/-- **The named one-slot base of the moving fold.**

Named twin of `movingSlotFoldAt_of_entry` (`MovingChainBaseRun.lean:580`). The
same free-at-the-base argument applies: `confAbsorbed` and the two cone fields
are vacuous when the fold has not left its starting slot, and `entry` and
`historyAt` are the named entry state's own, so no conversion appears. This is
the piece that connects any named entry state to the named iteration
`MovingSlotFoldAtN.iterate_of_supply` (`MovingChainIterateRun.lean:778`). -/
theorem movingSlotFoldAtN_of_entry
    (S : Setup V) {rho : Run V}
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hentry : MovingSlotEntryStateN S rho t1 M0 (c + 1) Prev End)
    (hproposal : S.E.proposer (c + 1) ∈ rho.honest →
      ∃ P : NamedBlock V, proposedBlockAt S rho (c + 1) = some P ∧
        End = P.erase)
    (hparent : S.E.proposer (c + 1) ∈ rho.honest →
      Block.Preceq Prev (proposedParent S rho (c + 1))) :
    MovingSlotFoldAtN S rho t1 M0 (c + 1) (c + 1) (fun _ => Prev) End where
  base := Nat.le_refl _
  entry := hentry
  endpointProposal := hproposal
  mono := fun _ _ _ _ _ => Block.preceq_self _
  parent := by
    intro d hd hdle hdprop
    have hdeq : d = c + 1 := Nat.le_antisymm hdle hd
    subst hdeq
    exact hparent hdprop
  absorbed := fun d hd hdlt => absurd (hd.trans_lt hdlt) (lt_irrefl _)
  confAbsorbed := fun d hd hdlt =>
    absurd (hd.trans_lt (Nat.lt_of_succ_lt hdlt)) (lt_irrefl _)
  confAbove := fun d hd hdlt =>
    absurd (hd.trans_lt (Nat.lt_of_succ_lt hdlt)) (lt_irrefl _)
  windowCone := fun d hd hdlt => absurd (hd.trans_lt hdlt) (lt_irrefl _)
  historyAt := by
    intro d hd hdle
    have hdeq : d = c + 1 := Nat.le_antisymm hdle hd
    subst hdeq
    obtain ⟨EndAt, hhistory, hprev, _hEnd⟩ := hentry.prevEndpoint
    exact ⟨EndAt, hhistory.prefix
      (strictEventIndex_mono rho hentry.startTime)
      (strictEventIndex_le_inclusiveEventIndex rho _), hprev⟩

#print axioms movingSlotFoldAtN_of_entry


/-- Copy of the private `baseCoreVoterHeadRunBlock`
(`MovingChainBaseRun.lean:44`), byte-for-byte in its body. Copied rather than
exported: `MovingChainBaseRun` sits under the whole moving-chain tree, so a
source change there invalidates every olean above it for every branches until the
next CI pass. -/
theorem w4d1_baseCoreVoterHeadRunBlock
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) (d : Slot) :
    ∃ H : NamedBlock V, H.erase = voterHeadAt S rho w d ∧
      H.erase ∈ (voteDutyRead S rho w d).st.core.T ∧
      NamedRun.blockInRun S rho H := by
  let read := voteDutyRead S rho w d
  let st := read.st.core
  let tree := voterCandidateTreeAt S rho w d
  let H := voterHeadAt S rho w d
  have hinvPre : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E d) w).st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
      (Protocol.vote_time S.E d) w).1
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg read.st := by
    simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt] using
      Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ _ hinvPre
  have hroot : Protocol.get_fg_root st.toHealing.toFG ∈ st.T :=
    Proofs.NamedStoreRoots.fg_root_mem read.st hinv.1.2
  have hanchor : voterAnchorAt S rho w d ∈ st.T :=
    Proofs.NamedConfirmationMembership.runtime_anchor_mem read.cache
      S.E S.hc st.toHealing (S.hc.round_of st.s) hroot
  have htree : tree ⊆ st.T := by
    intro D hD
    have hp := Proofs.Records.get_filtered_block_tree_from_subset
      st.toHealing.toFG
      (Protocol.voter_processed_block_tree S.E
        st.toHealing.toFG.toSG.toGoldfishStore st.s) hD
    exact (Finset.mem_filter.mp hp).1
  have hHmem : H ∈ st.T := by
    rw [show H = Protocol.ghost (voterAnchorAt S rho w d) tree
        (Protocol.goldfish_score S.E st.T
          (Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (st.s - 1))
        (Protocol.goldfish_eligible S.E st.σ st.h_max st.T st.s
          (Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (st.s - 1)) by rfl]
    exact Proofs.Records.ghost_mem_of _ _ hanchor htree
  have hHpre : H ∈ (NamedRun.stateBeforeTime S rho
      (Protocol.vote_time S.E d) w).st.core.T := by
    simpa only [read, st, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using hHmem
  obtain ⟨H', hH'erase, hHrun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
      adm.toNamedScheduleWellFormed hw (Protocol.vote_time S.E d) hHpre
  refine ⟨H', hH'erase, ?_, hHrun⟩
  simpa only [hH'erase, read, st] using hHmem

/-- Copy of the private `baseCoreVoterHeadEmits` (`MovingChainBaseRun.lean:95`),
byte-for-byte in its body. This is the witness `MovingSlotPreEntryN.toEntryN`
takes as `_of_voterHeadEmits`. -/
theorem w4d1_baseCoreVoterHeadEmits
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot}
    (hs : 0 < s) (hcommittee : w ∈ S.E.committee s)
    (hhor : Protocol.vote_time S.E s ≤ rho.horizon) :
    ∃ C : NamedBlock V, C.erase = voterHeadAt S rho w s ∧
      NamedRun.blockInRun S rho C ∧
      NamedRun.emits S rho w
        (Object.gfVote ⟨w, s, C.erase.root⟩)
        (Protocol.vote_time S.E s) := by
  obtain ⟨C, hChead, -, hCrun⟩ := w4d1_baseCoreVoterHeadRunBlock S adm hw s
  let read := voteDutyRead S rho w s
  have hslot : read.st.core.s = s := Proofs.Optimistic.voteDutyRead_slot S rho w s
  have hcommittee' :
      (S.node w).val_index ∈ S.E.committee read.st.core.s := by
    rw [S.node_val_index, hslot]
    exact hcommittee
  have hout :
      (Protocol.NamedDuties.goldfish_vote_with
        (NamedProfile.gradeContract read.cache)
        S.E S.hc (S.node w) read.st).2 =
        some ⟨(S.node w).val_index, read.st.core.s,
          (voterHeadAt S rho w s).root⟩ := by
    simp only [Protocol.NamedDuties.goldfish_vote_with,
      Protocol.goldfish_vote_with]
    rw [if_pos]
    · rfl
    · exact hcommittee'
  have ho : Object.gfVote
      ⟨(S.node w).val_index, read.st.core.s,
        (voterHeadAt S rho w s).root⟩ ∈
      (on_tick_emit S w
        (NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E s) w)
        (Protocol.vote_time S.E s)).2 := by
    exact Proofs.Optimistic.on_tick_emit_vote_mem S w
      (NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E s) w)
      s hs hout
  have hem := Proofs.Optimistic.emits_of_on_tick_emit S adm.toNamedScheduleWellFormed hw
    (Proofs.Optimistic.publicTime_vote_time S s) (Proofs.Optimistic.vote_time_nonneg S.E s) hhor ho
  refine ⟨C, hChead, hCrun, ?_⟩
  simpa only [S.node_val_index, hslot, hChead] using hem

#print axioms w4d1_baseCoreVoterHeadEmits


/-- **The named pre-entry becomes the named entry state.**

Named twin of `MovingSlotPreEntry.toEntry_of_confCompatible`
(`MovingChainBaseRun.lean:391`), which the corresponding branch's boundary fold uses and
which has no named form. The three fields `MovingSlotPreEntryN` already carries
pass straight through; `votes` is built here exactly as the plain proof builds
it, from the head equality in an honest-proposer slot and from the previous
cone otherwise, and `confCompatible` is the caller's callback.

Nothing in the argument is contract-specific: the named and plain records
differ only in which confirmation contract `confCompatible` names, and that is
the caller's hypothesis in both. -/
theorem MovingSlotPreEntryN.toEntryN
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hpre : MovingSlotPreEntryN S rho t1 M0 (c + 1) Prev End)
    (hdata' : MovingSlotWindowData S rho t1 M0 (c + 1))
    (hheadEq : S.E.proposer (c + 1) ∈ rho.honest → ∀ w ∈ rho.honest,
      voteDutyHead S rho w (c + 1) = End)
    (hbyz : S.E.proposer (c + 1) ∉ rho.honest → End = Prev)
    (hprevVotes : NamedHonestVotesCone S rho (c + 1)
      (fun X => Block.Preceq Prev X))
    (hconf : ∀ w ∈ rho.honest, ∀ D : Block V,
      GenuineConfirmationWith
        (NamedProfile.gradeContract
          (Internal.NamedRecoveryRead.confirmationInputRead S rho w c).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho w c) c D →
      Block.compatible D End = true)
    :
    MovingSlotEntryStateN S rho t1 M0 (c + 1) Prev End := by
  have hvoteHor : Protocol.vote_time S.E (c + 1) ≤ rho.horizon := by
    refine le_trans ?_ hdata'.slotHor
    simp only [Protocol.vote_time, Protocol.confirmation_time]
    have h : ∀ x d : Int, 0 < d → x + d ≤ x + 6 * d := by
      intro x d hd
      omega
    exact h _ _ S.E.Δ_pos
  have hvotes : NamedHonestVotesCone S rho (c + 1)
      (fun X => Block.Preceq End X) := by
    by_cases hprop : S.E.proposer (c + 1) ∈ rho.honest
    · intro u hu huc
      obtain ⟨C, hC, hCrun, hCemit⟩ :=
        w4d1_baseCoreVoterHeadEmits S adm.toNamedAdmissibleCore hu
          (s := c + 1) (Nat.succ_pos c) huc hvoteHor
      have hCEnd : C.erase = End := hC.trans (by
        simpa only [voteDutyHead] using (hheadEq hprop u hu))
      exact ⟨C, by rw [hCEnd]; exact Block.preceq_self _, hCrun, hCemit⟩
    · rw [hbyz hprop]
      exact hprevVotes
  refine
    { startTime := hpre.startTime
      prevEndpoint := hpre.prevEndpoint
      prevVotes := hpre.prevVotes
      votes := hvotes
      headEq := hheadEq
      confCompatible := ?_ }
  · intro w hw D hD
    simpa only [Nat.add_sub_cancel] using hconf w hw D hD

#print axioms MovingSlotPreEntryN.toEntryN


/-- The support cutoff of a slot is at or before the next slot's proposal. -/
theorem w4d1_support_cutoff_le_proposal_time_two (E : Env V) (c : Slot) :
    Protocol.support_cutoff E (c + 1) ≤ Protocol.proposal_time E (c + 1 + 1) := by
  have hsc : Protocol.support_cutoff E (c + 1) =
      (4 * ((c + 1 : Slot) : Time) + 2) * E.Δ := by
    unfold Protocol.support_cutoff Env.t slotStart
    ring
  have hp : Protocol.proposal_time E (c + 1 + 1) =
      (4 * ((c + 1 + 1 : Slot) : Time) + 0) * E.Δ := by
    unfold Protocol.proposal_time Env.t slotStart
    ring
  rw [hsc, hp]
  have hcast : ((c + 1 : Slot) : Time) + 1 = ((c + 1 + 1 : Slot) : Time) := by
    push_cast
    ring
  have hle : (4 * ((c + 1 : Slot) : Time) + 2) ≤ (4 * ((c + 1 + 1 : Slot) : Time) + 0) := by
    rw [← hcast]
    linarith
  exact Int.mul_le_mul_of_nonneg_right hle E.Δ_pos.le


/-- **The named pre-entry of the boundary's successor slot, over its history.**

Named twin of the corresponding branch's `movingBoundaryPreEntry_honest_of_rowCap`
(`W4HandoffBoundaryRun.lean:804`), reduced to the one field that distinguishes
the named pre-entry from the plain one. `MovingSlotPreEntryN` has three fields:
`startTime` is schedule arithmetic, `prevVotes` is the caller's cone, and
`prevEndpoint` is the named moving history through the successor's proposal
event, which is `hprev` here.

`hprev` is what the two missing named history steps produce: the named twins of
`movingBoundaryHistory_toFreeze_of_rowCapFields` (`W4HandoffBoundaryRun:754`)
and `movingBoundaryHistory_toProposal_honest` (`MovingChainBoundaryRun:289`),
composed exactly as h1's plain proof composes them. Neither advances at a base
index, so neither is free and both are real ports; this theorem is stated over
their joint output so that the closure is one application when they land. -/
theorem movingBoundaryPreEntryN_honest_of_prevEndpoint
    (S : Setup V) {rho : Run V}
    {M0 : Height} {c : Slot} {E : Block V} {P : NamedBlock V}
    (hprev : ∃ EndAt : Nat → Block V,
      MovingFrontierChainStateN S rho
          (Protocol.support_cutoff S.E (c + 1)) M0
          (strictEventIndex rho (Protocol.support_cutoff S.E (c + 1)))
          (inclusiveEventIndex rho
            (Protocol.proposal_time S.E (c + 1 + 1))) EndAt ∧
        EndAt (strictEventIndex rho
          (Protocol.proposal_time S.E (c + 1 + 1))) = E ∧
        EndAt (inclusiveEventIndex rho
          (Protocol.proposal_time S.E (c + 1 + 1))) = P.erase)
    (hcone : NamedHonestVotesCone S rho (c + 1)
      (fun X => Block.Preceq E X)) :
    MovingSlotPreEntryN S rho (Protocol.support_cutoff S.E (c + 1)) M0
      (c + 1 + 1) E P.erase where
  startTime := w4d1_support_cutoff_le_proposal_time_two S.E c
  prevEndpoint := hprev
  prevVotes := by simpa only [Nat.add_sub_cancel] using hcone

#print axioms movingBoundaryPreEntryN_honest_of_prevEndpoint




/-- **The named complete moving-frontier state at a last in-horizon slot.**

The first branch of earlier's `completeState_of_handoff`
(`MovingChainExecutionRun.lean:3381`), reproduced over the named family: at a
slot `z` whose support cutoff is still inside the horizon and whose successor's
proposal is past it, the corresponding branch's `MovingSlotFoldAtN.windowFacts_hybrid` and
`.complete_through_window` (`W4CarryWindowRun.lean`, c5b7283d) carry the named
state to the end of the event list. The erased block is never unparked.

`z` and its three schedule properties are parameters rather than computed here,
so that the caller chooses the slot; for the intended caller `z` is
`S.E.slotOf rho.horizon`. earlier's other branch, where `z`'s own support cutoff
is already past the horizon, is a separate and much larger argument and is not
covered here.

The fold is the hypothesis `_of_foldN`, which the chain `bootstrapAtN` →
w4-h1's named boundary history → the named `toProposal` step → `toEntryN` →
`movingSlotFoldAtN_of_entry` → `iterate_of_supply` produces once the corresponding branch's
step lands. -/
theorem w4CompleteStateN_of_foldN_at_lastSlot
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {q : Round} {D : NamedBlock V} {M0 : Height}
    (hbaseTiming :
      0 < S.hc.round_of (S.hc.opening_slot q + 3) ∧
      S.E.t_GST ≤ S.a
        (S.hc.round_of (S.hc.opening_slot q + 3) - 1) ∧
      Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤
        rho.horizon)
    (hcarrierBase : ∀ r : Round,
      S.hc.round_of (S.hc.opening_slot q + 3) = r + 1 →
      ∀ u ∈ rho.honest,
        Block.Preceq (actionSGBlockAt S rho u r) D.erase)
    (hcarrierQ : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u q) D.erase)
    {z : Slot}
    (hbaseZ : S.hc.opening_slot q + 3 ≤ z)
    (hcutZ : Protocol.support_cutoff S.E z ≤ rho.horizon)
    (hnextFuture : rho.horizon < Protocol.proposal_time S.E (z + 1))
    (_of_foldN : ∀ {s : Slot},
      S.hc.opening_slot q + 3 ≤ s →
      Protocol.confirmation_time S.E (s - 1) ≤ rho.horizon →
      ∃ (F : Slot → Block V) (End : Block V),
        MovingSlotFoldAtN S rho
          (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
          (S.hc.opening_slot q + 3) s F End ∧
        F (S.hc.opening_slot q + 3) = D.erase) :
    ∃ EndAt : Nat → Block V,
      MovingFrontierChainStateN S rho
        (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
        (strictEventIndex rho
          (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)))
        rho.events.length EndAt := by
  classical
  have hzPos : 0 < z := Nat.lt_of_lt_of_le (Nat.succ_pos _) hbaseZ
  obtain ⟨v, hv⟩ := honest_nonempty_of_honestCommittees hcom
  have hconfPred : Protocol.confirmation_time S.E (z - 1) ≤ rho.horizon := by
    rw [← support_cutoff_eq_confirmation_time_pred S.E hzPos]
    exact hcutZ
  obtain ⟨F, End, hfold, hbaseEq⟩ := _of_foldN hbaseZ hconfPred
  obtain ⟨Next, hfrontier, hfacts, _hcone⟩ :=
    hfold.windowFacts_hybrid S adm hcom hfb hbaseTiming.1
      hbaseTiming.2.1 hcarrierBase hcarrierQ hbaseZ hbaseEq hcutZ
  exact hfold.complete_through_window S adm hzPos hfrontier hfacts hv
    hcutZ hnextFuture

#print axioms w4CompleteStateN_of_foldN_at_lastSlot


/-! ## Shared schedule normals

The slot instants in closed form, and the two integer monotonicity steps the
normals are used with. Copies of the private helpers of `W4CarryWindowRun` and
`MovingChainHandoffExportsRun`, each cited where it is used below. -/

private theorem w4d1_view_freeze_normal (E : Env V) (s : Slot) :
    Protocol.view_freeze E s = (4 * (s : Time) + 3) * E.Δ := by
  unfold Protocol.view_freeze Env.t slotStart
  ring

private theorem w4d1_proposal_time_normal (E : Env V) (s : Slot) :
    Protocol.proposal_time E s = (4 * (s : Time)) * E.Δ := by
  unfold Protocol.proposal_time Env.t slotStart
  ring

private theorem w4d1_int_mul_lt_mul_pos {a b d : Int}
    (h : a < b) (hd : 0 < d) : a * d < b * d :=
  Int.mul_lt_mul_of_pos_right h hd

private theorem w4d1_confirmation_time_normal (E : Env V) (s : Slot) :
    Protocol.confirmation_time E s = (4 * (s : Time) + 6) * E.Δ := by
  unfold Protocol.confirmation_time Env.t slotStart
  ring

private theorem w4d1_int_mul_le_mul_pos {a b d : Int}
    (h : a ≤ b) (hd : 0 < d) : a * d ≤ b * d :=
  Int.mul_le_mul_of_nonneg_right h (le_of_lt hd)

private theorem w4d1_action_time_normal (S : Setup V) (r : Round) :
    S.a r = (4 * ((S.hc.opening_slot r : Slot) : Time) + 6) * S.E.Δ := by
  unfold Setup.a Protocol.HealConfig.a slotStart
  ring

private theorem w4d1_gammaNegOne_normal (S : Setup V) (r : Round) :
    S.hc.Γ_neg1 S.E.Δ r =
      (4 * ((S.hc.opening_slot r : Slot) : Time) - 1) * S.E.Δ := by
  unfold Protocol.HealConfig.Γ_neg1 slotStart
  ring

private theorem w4d1_vote_time_normal (E : Env V) (s : Slot) :
    Protocol.vote_time E s = (4 * (s : Time) + 1) * E.Δ := by
  unfold Protocol.vote_time Env.t slotStart
  ring

private theorem w4d1_int_add_le_add_right {a b d : Int}
    (h : a ≤ b) : a + d ≤ b + d :=
  Int.add_le_add_right h d

/-- Copy of the private `proposal_time_mono'` (`W4CarryWindowRun.lean:98`). -/
private theorem w4d1_proposal_time_mono' (E : Env V) {a b : Slot} (hab : a ≤ b) :
    Protocol.proposal_time E a ≤ Protocol.proposal_time E b := by
  rw [w4d1_proposal_time_normal, w4d1_proposal_time_normal]
  apply w4d1_int_mul_le_mul_pos _ E.Δ_pos
  exact_mod_cast Nat.mul_le_mul_left 4 hab

/-- Copy of the private `action_time_mono'` (`W4CarryWindowRun.lean:104`). -/
private theorem w4d1_action_time_mono' (S : Setup V) {a b : Round} (hab : a ≤ b) :
    S.a a ≤ S.a b := by
  rw [w4d1_action_time_normal, w4d1_action_time_normal]
  apply w4d1_int_mul_le_mul_pos _ S.E.Δ_pos
  have hopen : S.hc.opening_slot a ≤ S.hc.opening_slot b :=
    Nat.mul_le_mul_right S.hc.R hab
  exact w4d1_int_add_le_add_right
    (by exact_mod_cast Nat.mul_le_mul_left 4 hopen)

/-- Copy of the private `action_le_proposal_plus_two`
(`W4CarryWindowRun.lean:168`). -/
private theorem w4d1_action_le_proposal_plus_two (S : Setup V) (q : Round) :
    S.a q ≤ Protocol.proposal_time S.E (S.hc.opening_slot q + 2) := by
  rw [w4d1_action_time_normal, w4d1_proposal_time_normal]
  apply w4d1_int_mul_le_mul_pos _ S.E.Δ_pos
  push_cast
  omega

/-- Copy of the private `proposal_le_vote` (`W4CarryWindowRun.lean:239`). -/
private theorem w4d1_proposal_le_vote (E : Env V) (s : Slot) :
    Protocol.proposal_time E s ≤ Protocol.vote_time E s := by
  rw [w4d1_proposal_time_normal, w4d1_vote_time_normal]
  apply w4d1_int_mul_le_mul_pos _ E.Δ_pos
  omega

/-- Copy of the private `nat_pred_le_of_pos_le_succ`
(`W4CarryWindowRun.lean:274`). -/
private theorem w4d1_nat_pred_le_of_pos_le_succ {a b : Nat}
    (ha : 0 < a) (h : a ≤ b + 1) : a - 1 ≤ b :=
  Nat.lt_succ_iff.mp ((Nat.sub_lt ha (by decide : 0 < 1)).trans_le h)

/-- Copy of `round_of_opening_add_three_le_succ_handoffExport`
(`MovingChainHandoffExportsRun.lean:137`). -/
private theorem w4d1_round_of_opening_add_three_le_succ
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

/-- Copy of `round_of_mono_handoffExport`
(`MovingChainHandoffExportsRun.lean:276`). -/
private theorem w4d1_round_of_mono
    (hc : Protocol.HealConfig) {a b : Slot} (hab : a ≤ b) :
    hc.round_of a ≤ hc.round_of b := by
  simpa only [Protocol.HealConfig.round_of] using Nat.div_le_div_right hab



/-- Copy of the private `view_freeze_lt_proposal_time_succ`
(`MovingChainFoldRun.lean:1101`). -/
private theorem w4d1_view_freeze_lt_proposal_succ (E : Env V) (s : Slot) :
    Protocol.view_freeze E s < Protocol.proposal_time E (s + 1) := by
  rw [w4d1_view_freeze_normal, w4d1_proposal_time_normal]
  apply w4d1_int_mul_lt_mul_pos _ E.Δ_pos
  have hcast : (((s + 1 : Nat) : Int)) = (s : Int) + 1 := by
    push_cast
    rfl
  rw [hcast]
  omega


/-- **The named complete moving-frontier state when the last slot's cutoff is
past the horizon.**

The second branch of earlier's `completeState_of_handoff`. For the intended caller
`z` is `S.E.slotOf rho.horizon` and the three schedule facts about it are the
ones earlier derives there; they are parameters so the caller chooses the slot.

the corresponding branch's four items have all available (`W4CarryBranch2Run.lean`,
`d1d20034`, `abfbc9f8`, `8926c953`, `09765782`), so they are called directly
rather than pinned: `MovingSlotFoldAtN.nextParent_hybrid` for the next slot's
honest parent, and `MovingFrontierChainStateN.complete_before_vote` /
`.complete_before_cutoff` for the four ways the run can end inside the window.

Three hypotheses remain:

* `_of_foldN` is the fold at `z - 1`, from this file's own chain.
* `_of_honestVoteReads` and `_of_byzantineVoteAnchor` are the two obligations
  this branch exposes that earlier discharges through four private hybrids of the
  parked Execution block (`voteInputsAtProposal_hybrid` `:2472`,
  `frozenProposalSuffixCoreInputs_hybrid` `:3052`,
  `proposalWalkTransferred_of_sourceFloor_of_cutoff` `:2822` and
  `MovingSlotPreEntry.voteAnchor_preceq_prev_hybrid` `:2394`). Pinning the two
  vote-phase reads they produce, rather than the four hybrids, keeps the proof
  to what the branch actually consumes: in an honest slot every honest voter's
  head is the slot proposal and its anchor is compatible with it; in a
  Byzantine slot the anchor is compatible with the window endpoint. -/
theorem w4CompleteStateN_of_foldN_at_cutoffPastHorizon
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {q : Round} {D : NamedBlock V} {M0 : Height}
    (hbaseTiming :
      0 < S.hc.round_of (S.hc.opening_slot q + 3) ∧
      S.E.t_GST ≤ S.a
        (S.hc.round_of (S.hc.opening_slot q + 3) - 1) ∧
      Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤
        rho.horizon)
    (hcarrierBase : ∀ r : Round,
      S.hc.round_of (S.hc.opening_slot q + 3) = r + 1 →
      ∀ u ∈ rho.honest,
        Block.Preceq (actionSGBlockAt S rho u r) D.erase)
    (hcarrierQ : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u q) D.erase)
    {z : Slot}
    (hbaseSuccZ : S.hc.opening_slot q + 3 + 1 ≤ z)
    (hproposalZ : Protocol.proposal_time S.E z ≤ rho.horizon)
    (hcutFuture : rho.horizon < Protocol.support_cutoff S.E z)
    (hnextFuture : rho.horizon < Protocol.proposal_time S.E (z + 1))
    (_of_foldN : ∀ {s : Slot},
      S.hc.opening_slot q + 3 ≤ s →
      Protocol.confirmation_time S.E (s - 1) ≤ rho.horizon →
      ∃ (F : Slot → Block V) (End : Block V),
        MovingSlotFoldAtN S rho
          (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
          (S.hc.opening_slot q + 3) s F End ∧
        F (S.hc.opening_slot q + 3) = D.erase)
    (_of_honestVoteReads : ∀ {s : Slot} {F : Slot → Block V}
        {End Next : Block V} {P : NamedBlock V},
      MovingSlotFoldAtN S rho
        (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
        (S.hc.opening_slot q + 3) s F End →
      S.hc.opening_slot q + 3 ≤ s →
      F (S.hc.opening_slot q + 3) = D.erase →
      MovingSlotFrontierAt S rho (s - 1) End Next →
      NamedMovingSlotWindowFacts S rho s End Next →
      NamedHonestVotesCone S rho s (fun X => Block.Preceq Next X) →
      Protocol.support_cutoff S.E s ≤ rho.horizon →
      Protocol.proposal_time S.E (s + 1) ≤ rho.horizon →
      Protocol.vote_time S.E (s + 1) ≤ rho.horizon →
      S.E.proposer (s + 1) ∈ rho.honest →
      proposedBlockAt S rho (s + 1) = some P →
        (∀ w ∈ rho.honest, voteDutyHead S rho w (s + 1) = P.erase) ∧
          (∀ w ∈ rho.honest,
            Block.compatible (voterAnchorAt S rho w (s + 1)) P.erase = true))
    (_of_byzantineVoteAnchor : ∀ {t1 : Time} {c : Slot}
        {Prev End' : Block V} {r : Round},
      MovingSlotPreEntryN S rho t1 M0 (c + 1) Prev End' →
      S.hc.round_of (c + 1) = r + 1 →
      (t1 ≤ S.a r ∨ ∀ u ∈ rho.honest,
        Block.Preceq (actionSGBlockAt S rho u r) Prev) →
      S.E.t_GST ≤ S.a r →
      S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon →
      S.E.t_GST ≤ Protocol.vote_time S.E c →
      Protocol.support_cutoff S.E c ≤ rho.horizon →
      Protocol.vote_time S.E (c + 1) ≤ rho.horizon →
      ∀ w ∈ rho.honest,
        Block.Preceq (voterAnchorAt S rho w (c + 1)) Prev) :
    ∃ EndAt : Nat → Block V,
      MovingFrontierChainStateN S rho
        (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
        (strictEventIndex rho
          (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)))
        rho.events.length EndAt := by
  classical
  obtain ⟨v, hv⟩ := honest_nonempty_of_honestCommittees hcom
  have hzPos : 0 < z :=
    Nat.lt_of_lt_of_le (Nat.succ_pos _) hbaseSuccZ
  obtain ⟨s, hsSucc⟩ : ∃ s : Slot, s + 1 = z :=
    ⟨z - 1, Nat.succ_pred_eq_of_pos hzPos⟩
  have hbaseSuccS : S.hc.opening_slot q + 3 + 1 ≤ s + 1 := by
    rw [hsSucc]; exact hbaseSuccZ
  have hsBase : S.hc.opening_slot q + 3 ≤ s :=
    Nat.le_of_succ_le_succ hbaseSuccS
  have hsPos : 0 < s :=
    Nat.lt_of_lt_of_le (Nat.succ_pos _) hsBase
  have hcutS : Protocol.support_cutoff S.E s ≤ rho.horizon :=
    le_of_lt (lt_of_lt_of_le
      (Protocol.support_cutoff_lt_proposal_time_succ S.E s)
      (by rw [hsSucc]; exact hproposalZ))
  have hconfFold : Protocol.confirmation_time S.E (s - 1) ≤ rho.horizon := by
    rw [← support_cutoff_eq_confirmation_time_pred S.E hsPos]
    exact hcutS
  obtain ⟨F, End, hfold, hbaseEq⟩ := _of_foldN hsBase hconfFold
  obtain ⟨Next, hfrontier, hfacts, hcone⟩ :=
    hfold.windowFacts_hybrid S adm hcom hfb hbaseTiming.1 hbaseTiming.2.1
      hcarrierBase hcarrierQ hsBase hbaseEq hcutS
  obtain ⟨End0, hstate0, _hprev0, hEnd0⟩ := hfold.entry.prevEndpoint
  have hrunEnd : ∃ E : NamedBlock V, E.erase = End ∧ RunBlock S rho E := by
    rw [← hEnd0]
    exact hstate0.endpointRun _ hstate0.start_le (Nat.le_refl _)
  have hrunNext : ∃ E : NamedBlock V, E.erase = Next ∧ RunBlock S rho E :=
    hfrontier.runBlock S adm hrunEnd
  have hproposalS : Protocol.proposal_time S.E (s + 1) ≤ rho.horizon := by
    rw [hsSucc]; exact hproposalZ
  have hcutFutureS : rho.horizon < Protocol.support_cutoff S.E (s + 1) := by
    rw [hsSucc]; exact hcutFuture
  have hnextFutureS : rho.horizon <
      Protocol.proposal_time S.E (s + 1 + 1) := by
    rw [hsSucc]; exact hnextFuture
  by_cases hpropZ : S.E.proposer (s + 1) ∈ rho.honest
  · have hparent : Block.Preceq Next (proposedParent S rho (s + 1)) :=
      hfold.nextParent_hybrid S adm hcom hfb hbaseTiming.1 hbaseTiming.2.1
        hcarrierBase hcarrierQ hsBase hbaseEq hfrontier hfacts hcone hcutS
        hproposalS hpropZ hv
    obtain ⟨P, hP, EndZ, _hlowZ, _hstrictZ, hEndZ, hstateZ⟩ :=
      MovingFrontierChainStateN.through_slotWindow_honestProposer_named
        S adm hsPos hstate0 hEnd0 hrunEnd hrunNext hfacts hpropZ
        hproposalS hparent hv hcutS
    have hrunP : ∃ E : NamedBlock V, E.erase = P.erase ∧ RunBlock S rho E :=
      ⟨P, rfl, proposedBlockAt_blockInRun_of_admissible S
        adm.toNamedAdmissibleCore (s + 1) (Nat.succ_pos s) hpropZ
        hproposalS hP⟩
    by_cases hvoteZ : Protocol.vote_time S.E (s + 1) ≤ rho.horizon
    · obtain ⟨hhead, hanchor⟩ :=
        _of_honestVoteReads hfold hsBase hbaseEq hfrontier hfacts hcone
          hcutS hproposalS hvoteZ hpropZ hP
      exact hstateZ.complete_before_cutoff S adm hEndZ hrunP hproposalS
        hcutFutureS (fun _hp => hhead) hanchor
    · exact hstateZ.complete_before_vote S adm hEndZ hrunP hproposalS
        (lt_of_not_ge hvoteZ) hcutFutureS hnextFutureS
  · obtain ⟨EndZ, _hlowZ, hhighZ, hstateZ⟩ :=
      MovingFrontierChainStateN.through_slotWindow_byzantineProposer_named
        S adm hsPos hstate0 hEnd0 hrunEnd hrunNext hfacts hpropZ hv hcutS
    have hEndZ : EndZ
        (inclusiveEventIndex rho
          (Protocol.proposal_time S.E (s + 1))) = Next :=
      hhighZ _ (inclusiveEventIndex_mono rho
        (le_of_lt (w4d1_view_freeze_lt_proposal_succ S.E s)))
    by_cases hvoteZ : Protocol.vote_time S.E (s + 1) ≤ rho.horizon
    · have hEndStrict : EndZ
          (strictEventIndex rho
            (Protocol.proposal_time S.E (s + 1))) = Next :=
        hhighZ _ (inclusiveEventIndex_le_strictEventIndex_of_lt rho
          (w4d1_view_freeze_lt_proposal_succ S.E s))
      have hsBaseSucc : S.hc.opening_slot q + 3 ≤ s + 1 :=
        hsBase.trans (Nat.le_succ s)
      have hstart : Protocol.support_cutoff S.E (S.hc.opening_slot q + 2) ≤
          Protocol.proposal_time S.E (s + 1) :=
        (le_of_lt (Protocol.support_cutoff_lt_proposal_time_succ S.E
          (S.hc.opening_slot q + 2))).trans
          (w4d1_proposal_time_mono' S.E hsBaseSucc)
      have hpre : MovingSlotPreEntryN S rho
          (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
          (s + 1) Next Next :=
        { startTime := hstart
          prevEndpoint := ⟨EndZ, hstateZ, hEndStrict, hEndZ⟩
          prevVotes := by simpa only [Nat.add_sub_cancel] using hcone }
      have hDPrev : Block.Preceq D.erase (F s) := by
        rw [← hbaseEq]
        exact hfold.mono _ _ (Nat.le_refl _) hsBase (Nat.le_refl _)
      have hDNext : Block.Preceq D.erase Next :=
        Block.preceq_trans hDPrev
          (Block.preceq_trans hfold.entry.prevLe hfrontier.oldPreceq)
      obtain ⟨r, hround, hpostAction, hcut, hmode⟩ :=
        w4_proposalSchedule_hybrid S hbaseTiming.1 hbaseTiming.2.1
          hcarrierBase hcarrierQ hDNext hsBaseSucc hproposalS
      have hR0q : S.hc.round_of (S.hc.opening_slot q + 3) - 1 ≤ q :=
        w4d1_nat_pred_le_of_pos_le_succ hbaseTiming.1
          (w4d1_round_of_opening_add_three_le_succ S.hc q)
      have hpostAtBase : S.E.t_GST ≤
          Protocol.proposal_time S.E (S.hc.opening_slot q + 2) :=
        hbaseTiming.2.1.trans
          ((w4d1_action_time_mono' S hR0q).trans
            (w4d1_action_le_proposal_plus_two S q))
      have hpostVoteS : S.E.t_GST ≤ Protocol.vote_time S.E s :=
        (hpostAtBase.trans (w4d1_proposal_time_mono' S.E
          ((Nat.le_succ (S.hc.opening_slot q + 2)).trans hsBase))).trans
          (w4d1_proposal_le_vote S.E s)
      have hanchor : ∀ w ∈ rho.honest,
          Block.compatible (voterAnchorAt S rho w (s + 1)) Next = true :=
        fun w hw => Block.compatible_of_preceq_common
          (_of_byzantineVoteAnchor hpre hround hmode hpostAction hcut
            hpostVoteS hcutS hvoteZ w hw)
          (Block.preceq_self Next)
      exact hstateZ.complete_before_cutoff S adm hEndZ hrunNext hproposalS
        hcutFutureS (fun hp => absurd hp hpropZ) hanchor
    · exact hstateZ.complete_before_vote S adm hEndZ hrunNext hproposalS
        (lt_of_not_ge hvoteZ) hcutFutureS hnextFutureS

#print axioms w4CompleteStateN_of_foldN_at_cutoffPastHorizon





/-- **Obligation.** The carrier ceiling transported from the base round to `q`
itself. earlier's private `carrierCeiling_q_of_handoff`
(`MovingChainExecutionRun.lean:273`); `MovingChainHandoffExportsRun.lean:292`
has the same argument in selection vocabulary, over one further pin for the
prepared boundary output. -/
def W4CarrierCeilingAtQPin (S : Setup V) (rho : Run V) : Prop :=
  ∀ (q : Round) (D : NamedBlock V) (carrier : V),
    HealedTwoSlotHandoffPrepared S rho q D.erase carrier →
    (0 < S.hc.round_of (S.hc.opening_slot q + 3) ∧
      S.E.t_GST ≤ S.a
        (S.hc.round_of (S.hc.opening_slot q + 3) - 1) ∧
      Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤
        rho.horizon) →
    (∀ r : Round, S.hc.round_of (S.hc.opening_slot q + 3) = r + 1 →
      ∀ u ∈ rho.honest,
        Block.Preceq (actionSGBlockAt S rho u r) D.erase) →
    ∀ u ∈ rho.honest, Block.Preceq (actionSGBlockAt S rho u q) D.erase



/-- **Obligation.** The named-anchor twin of earlier's
`MovingSlotPreEntry.voteAnchor_preceq_prev_hybrid`
(`MovingChainExecutionRun.lean:2394`): at a named pre-entry, every honest
voter's anchor at the entered slot lies below the previous endpoint. Branch 2's
Byzantine arm turns it into compatibility with one application of
`Block.compatible_of_preceq_common`.

It is stated here in earlier's own shape, over the pre-entry and the schedule,
rather than over the fold, because that is the shape the existing lemmas
produce and the shape a producer can take without redoing the Byzantine
slot-window step.

Half of it is already live. `MovingSlotPreEntryN.voterAnchorAt_preceq_prev`
(`MovingChainNextEntryRun.lean:1534`) has exactly this conclusion for the left
disjunct, but takes the horizon as `Protocol.confirmation_time S.E c ≤
rho.horizon` where earlier takes the strictly weaker
`Protocol.support_cutoff S.E c ≤ rho.horizon`. The gap is a full slot, four
deltas, and branch 2 is the branch where the horizon falls inside it, so that
form can never be supplied here. In the core
(`MovingChainSupporterRun.lean:925`) that hypothesis is used exactly once, at
`:954`, and only to reach `Protocol.vote_time S.E (c + 1) ≤ rho.horizon`, which
IS available here: the arm that needs the anchor is the arm whose case split
gives it. Hence the last binder below, which the weakened core would consume
directly.

The right disjunct has no named twin at all; the erased one is
`MovingSlotPreEntry.voteAnchor_preceq_prev_of_ceiling`
(`MovingChainCeilingRun.lean:923`), and that module already carries the plain
and named pair for the neighbouring confirmation-outcome lemma, at `:569` and
`:117`. -/
def W4ByzantineVoteAnchorPin (S : Setup V) (rho : Run V) : Prop :=
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





/-- Copy of `gammaNegOne_le_action_handoffExport`
(`MovingChainHandoffExportsRun.lean:187`). -/
private theorem w4d1_gammaNegOne_le_action (S : Setup V) (r : Round) :
    S.hc.Γ_neg1 S.E.Δ r ≤ S.a r := by
  rw [w4d1_gammaNegOne_normal, w4d1_action_time_normal]
  refine Int.mul_le_mul_of_nonneg_right ?_ (le_of_lt S.E.Δ_pos)
  omega

/-- Copy of `confirmation_time_mono_handoffExport`
(`MovingChainHandoffExportsRun.lean:67`). -/
private theorem w4d1_confirmation_time_mono
    (E : Env V) {a b : Slot} (hab : a ≤ b) :
    Protocol.confirmation_time E a ≤ Protocol.confirmation_time E b := by
  rw [w4d1_confirmation_time_normal, w4d1_confirmation_time_normal]
  refine Int.mul_le_mul_of_nonneg_right ?_ (le_of_lt E.Δ_pos)
  exact Int.add_le_add_right (by exact_mod_cast Nat.mul_le_mul_left 4 hab) 6

private theorem w4d1_nat_pred_add_one {n : Nat} (hn : 0 < n) :
    n - 1 + 1 = n := by omega

private theorem w4d1_nat_pred_eq_of_pos_eq_succ {a q : Nat}
    (ha : 0 < a) (h : a = q + 1) : a - 1 = q := by omega


/-- **`W4CarrierCeilingAtQPin` from the prepared handoff record alone.**

earlier's `carrierCeiling_q_of_handoff` argument. The base round
` = round_of (opening_slot q + 3)` is either `q + 1`, where the ceiling at
the base round IS the ceiling at `q`, or `q` itself, where the carrier's own
opening-slot confirmation carries the ceiling forward through
`movingEventFacts_action_of_previousCarrierCeiling_named`
(`MovingChainDispatchRun.lean:233`). -/
theorem w4CarrierCeilingAtQPin_of_prepared
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest) :
    W4CarrierCeilingAtQPin S rho := by
  intro q D carrier hhandoff hbaseTiming hbaseCarrier
  have hopeningHor : Protocol.confirmation_time S.E (S.hc.opening_slot q) ≤
      rho.horizon :=
    (w4d1_confirmation_time_mono S.E
      (Nat.le_add_right (S.hc.opening_slot q) 3)).trans hbaseTiming.2.2
  have haqHor : S.a q ≤ rho.horizon := by
    rw [Setup.a, Protocol.a_eq_confirmation_time]
    exact hopeningHor
  have hboundaryOutput : ∀ u ∈ rho.honest,
      GenuineConfirmationWith
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadAt S rho u (S.a q)).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho u (S.hc.opening_slot q))
        (S.hc.opening_slot q)
        (movingSlotConfirmationOutput S rho (S.hc.opening_slot q) u) ∧
      Block.Preceq (movingSlotConfirmationOutput S rho
        (S.hc.opening_slot q) u) D.erase := by
    intro u hu
    have hfield := hhandoff.boundary_outputs (S.hc.opening_slot q)
      (Or.inl rfl) u hu hopeningHor
    have hread : NamedActionReads.confirmationReadAt S rho u (S.a q) =
        confirmationInputRead S rho u (S.hc.opening_slot q) := by
      rw [confirmationInputRead, Setup.a, Protocol.a_eq_confirmation_time]
    rw [hread]
    exact hfield
  let R0 := S.hc.round_of (S.hc.opening_slot q + 3)
  let r0 := R0 - 1
  have hR0pos : 0 < R0 := by simpa only [R0] using hbaseTiming.1
  have hround : S.hc.round_of (S.hc.opening_slot q + 3) = r0 + 1 := by
    simpa only [R0, r0] using (w4d1_nat_pred_add_one hR0pos).symm
  have hqR0 : q ≤ R0 := by
    rw [← round_of_opening_slot_eq_schedule S.hc q]
    exact w4d1_round_of_mono S.hc (Nat.le_add_right _ _)
  have hR0q1 : R0 ≤ q + 1 := by
    simpa only [R0] using
      w4d1_round_of_opening_add_three_le_succ S.hc q
  by_cases htop : R0 = q + 1
  · have hr0q : r0 = q :=
      w4d1_nat_pred_eq_of_pos_eq_succ hR0pos htop
    simpa only [hr0q] using hbaseCarrier r0 hround
  · have hR0q : R0 = q := by
      apply Nat.le_antisymm _ hqR0
      exact Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hR0q1 htop)
    have hqpos : 0 < q := by simpa only [← hR0q] using hR0pos
    have hr0q : r0 = q - 1 := by simp only [r0, hR0q]
    intro u hu
    have hD := (hboundaryOutput u hu).1
    have hDNext := (hboundaryOutput u hu).2
    obtain ⟨i, hi, _ha⟩ :=
      honest_emits_exact_actionAttestationAt S adm hu q haqHor
    have hpost : S.E.t_GST ≤ S.a (q - 1) := by
      simpa only [← hr0q, r0, R0] using hbaseTiming.2.1
    have hcut : S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon :=
      (w4d1_gammaNegOne_le_action S q).trans haqHor
    exact (movingEventFacts_action_of_previousCarrierCeiling_named S adm hfb
      hqpos hpost hcut hu hi hD
      (by intro w hw
          simpa only [hr0q] using hbaseCarrier r0 hround w hw)
      hDNext).1

#print axioms w4CarrierCeilingAtQPin_of_prepared


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
