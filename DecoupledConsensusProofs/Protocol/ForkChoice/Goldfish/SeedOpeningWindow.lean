module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ExcludesRefute
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedAdoption
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.OpeningActiveCarrier
public import DecoupledConsensusProofs.Protocol.Schedule.SeedEntry

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# The gate-off opening window of one round

`GateOffOpeningWindowAt` is the record the opening adoption and the promotion
read at a carrier round. Every use of it in the tree is a hypothesis; this
module builds one from the raw gate-off time window and an honest opening
proposer.

Two of its fields are not reads of the window. The parent height is the
proposer's own head floor: the proposer walks the FULL filtered tree, so the
frontier bound `getHead_frontier_le_height_add_one_of_invariants` applies to
its tick store directly, with no candidate-path input. The three proposal
memberships are post-GST relay of an honest proposal; their only real premise
is the finalized-root guard at the deliveries, which under gate off is the
thin-block guard of `SeedBaseRun`.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The proposer's head floor -/

/-- **The opening parent reaches the frontier band.** The proposer's head is
computed over its own full filtered tree, so the frontier bound applies to the
proposal tick store with no candidate-path premise. -/


private theorem rootInjective_proposerReadAt
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hprop : S.E.proposer s ∈ rho.honest) :
    RootInjectiveBelow (proposerReadAt S rho s).st.core.T := by
  let t := Protocol.proposal_time S.E s
  let p := S.E.proposer s
  obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedScheduleWellFormed.sorted t
  have hrun : ∀ C ∈ (proposerReadAt S rho s).st.bodies, RunBlock S rho C := by
    intro C hC
    have hC' : C ∈ (rho.stateBeforeTime S t p).st.bodies := by
      simpa only [proposerReadAt, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        t, p] using hC
    have hCi : C ∈ (rho.stateBefore S i p).st.bodies := by
      simpa only [hi] using hC'
    exact Proofs.Bridges.runBlock_of_stateBefore_mem S hprop hCi
  have hinj := Proofs.Bridges.rootInjectiveBelow_of_runBlocks S
    adm.toNamedRootCollisionFree hrun
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg (proposerReadAt S rho s).st :=
    (proposerReadAt_invariant S rho s).1
  rwa [← hcoh.1] at hinj

/-- **The opening named parent reaches the frontier band.** -/
theorem seedOpeningParentHeight_of_frontier
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {M : Height} {s : Slot} {P : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hfrontier : (proposerDutyStore S rho s).h_max = M) :
    M - 1 ≤ (Protocol.derive_named S.E S.cfg P.parent).h := by
  let n := proposerReadAt S rho s
  let st := n.st.core
  let tree := Protocol.get_filtered_block_tree st.toHealing.toFG
  let gc := NamedProfile.gradeContract n.cache
  let votes := Protocol.proposer_view st.toHealing.toFG.toSG.toGoldfishStore st.s
  let support := Protocol.proposer_support_view st.toHealing.toFG.toSG.toGoldfishStore st.s
  let eligible := Protocol.goldfish_eligible S.E st.σ st.h_max st.T st.s
    votes.toFinset support.toFinset (st.s - 1)
  let H := Protocol.get_head_with gc S.E S.hc st.toHealing
    votes.toFinset support.toFinset (st.s - 1)
  have hHEq : H = proposedParent S rho s := by
    rfl
  have hHghost : H = Protocol.ghost
      (Protocol.get_sg_root_with gc S.E S.hc st.toHealing
        (S.hc.round_of st.s)) tree
      (Protocol.goldfish_score S.E st.T votes.toFinset support.toFinset
        (st.s - 1)) eligible := by
    rfl
  have hHfiltered : H ∈ tree := by
    rw [hHEq]
    simpa only [tree, st, n] using
      (selectedOpeningProposedParent_mem_filtered S (rho := rho) s)
  have hpc : ParentClosed st := by
    simpa only [st, n, proposerReadAt, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      (Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
        (Protocol.proposal_time S.E s) (S.E.proposer s))
  have hroot : RootInjectiveBelow st.T := by
    simpa only [st, n] using rootInjective_proposerReadAt S adm hprop
  have hrootTree : RootInjectiveBelow tree :=
    Protocol.RootInjectiveBelow.mono hroot
      (Proofs.Records.get_filtered_block_tree_subset st.toHealing.toFG)
  have hHdata := hHfiltered
  simp only [tree, Protocol.get_filtered_block_tree,
    Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
    Protocol.finalized_descendants, Protocol.viable,
    Finset.mem_filter, decide_eq_true_eq] at hHdata
  obtain ⟨⟨⟨-, hFH⟩, W, hWT, hHW, hWheight⟩, hrootH⟩ := hHdata
  have hbound : st.h_max ≤ (st.σ H).h + 1 := by
    by_contra hnot
    have hHlt : (st.σ H).h + 1 < st.h_max := Nat.lt_of_not_ge hnot
    have hHneW : H ≠ W := by
      intro hEq
      subst W
      have key : ∀ a b : Nat, a - 1 ≤ b → b + 1 < a → False := by omega
      exact key st.h_max (st.σ H).h hWheight hHlt
    obtain ⟨C, hCparent, hCW⟩ := Protocol.exists_child_towards W hHW hHneW
    have hHC : Block.Preceq H C := Protocol.preceq_of_parent? hCparent
    have hCT : C ∈ st.T :=
      Proofs.Records.mem_of_preceq ((parentClosed_iff st).mp hpc).2 C W hWT hCW
    have hFC : Block.Preceq st.F C := Block.preceq_trans hFH hHC
    have hrootC : Block.Preceq
        (Protocol.get_fg_root st.toHealing.toFG) C :=
      Block.preceq_trans hrootH hHC
    have hCfiltered : C ∈ tree := by
      simp only [tree, Protocol.get_filtered_block_tree,
        Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
        Protocol.finalized_descendants, Protocol.viable,
        Finset.mem_filter, decide_eq_true_eq]
      exact ⟨⟨⟨hCT, hFC⟩, W, hWT, hCW, hWheight⟩, hrootC⟩
    have hHlow : (st.σ H).h < st.h_max - 1 := by
      have key : ∀ a b : Nat, a + 1 < b → a < b - 1 := by omega
      exact key (st.σ H).h st.h_max hHlt
    have hCeligible : eligible C = true := by
      rw [Proofs.Optimistic.goldfish_eligible_iff, parent_eq_of_parent? hCparent]
      exact Or.inl hHlow
    have hCfalse : eligible C = false := by
      have hCparentGhost := hCparent
      rw [hHghost] at hCparentGhost
      exact eligible_child_false_at_ghost_result hrootTree hCfiltered hCparentGhost
    rw [hCfalse] at hCeligible
    contradiction
  have hpay := Proofs.NamedActions.proposal_payload
    (NamedProfile.gradeContract (proposerReadAt S rho s).cache)
    .poolAndCarried S.E S.hc (S.node (S.E.proposer s))
    (proposerReadAt S rho s).st P hP
  have hview : (proposerReadAt S rho s).st.core.σ P.parent.erase =
      Protocol.derive_named S.E S.cfg P.parent :=
    (proposerReadAt_invariant S rho s).1.2.2.2.2 P.parent hpay.1
  have hparentErase : P.parent.erase = H := hpay.2.1.trans hHEq.symm
  have hbound' : st.h_max ≤
      (Protocol.derive_named S.E S.cfg P.parent).h + 1 := by
    rw [← hview, hparentErase]
    exact hbound
  have hfrontier' : st.h_max = M := by
    simpa only [st, n, proposerReadAt, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, proposerDutyStore,
      Proofs.Optimistic.tickStore, Protocol.NamedStore.setClock] using hfrontier
  rw [hfrontier'] at hbound'
  have key : ∀ a b : Nat, a ≤ b + 1 → a - 1 ≤ b := by omega
  exact key M (Protocol.derive_named S.E S.cfg P.parent).h hbound'

/-! ## The opening proposal at the round's reads -/

/-- The finalized-root guard for an honest opening proposal under gate off.
The proposal is inside the frontier band, and at a gate-off exact-frontier read
the receiver's finalized block is below every run block of that band. -/


theorem seedOpeningProposal_finalizedBelow_of_gateOff
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {M : Height} {s : Slot} {P : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P)
    (hPrun : RunBlock S rho P)
    (hPthin : M - 1 ≤ (Protocol.derive_named S.E S.cfg P).h)
    (hvoteFrontier : ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v (Protocol.vote_time S.E s)).h_max = M)
    (hvoteGate : ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v (Protocol.vote_time S.E s)).h_j + 2 ≤ M) :
    ProposalFinalizedBelowAtDeliveries S rho s P := by
  intro v hv i hi
  exact seedBase_thinBlock_finalizedBelow S adm hsb hPrun hPthin hv
    (hvoteFrontier v hv) (hvoteGate v hv) i hi

private theorem proposedBlock_admittedBefore_vote_after_gst
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hs : 0 < s)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hvoteHor : Protocol.vote_time S.E s ≤ rho.horizon)
    {P : NamedBlock V} (hP : proposedBlockAt S rho s = some P)
    (hFhist : ProposalFinalizedBelowAtDeliveries S rho s P) :
    ∀ v ∈ rho.honest,
      AdmittedBefore S rho v P.erase (Protocol.vote_time S.E s) := by
  intro v hv
  by_cases hvp : v = S.E.proposer s
  · subst v
    obtain ⟨i, hacc⟩ := acceptsAt_proposedBlock S adm hs hprop
      ((Protocol.proposal_time_lt_vote_time S.E s).le.trans hvoteHor) hP
    exact ⟨P, rfl, i, Protocol.proposal_time S.E s, hacc,
      Protocol.proposal_time_lt_vote_time S.E s⟩
  · obtain ⟨P0, hP0, t, hlo, hhi, hproc⟩ :=
      Protocol.processes_proposedBlock_before_vote_after_gst
        S adm hs hprop hpost hvoteHor hv (by
          intro Q hQ
          have hQP : Q = P := proposedBlockAt_unique S rho s hQ hP
          subst Q
          change Block.Preceq
            (NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E s) v).st.core.F P.erase
          rw [stateBeforeTime_eq_stateBefore_filter_length S rho
            adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted]
          exact hFhist v hv _ le_rfl)
    have hP0P : P0 = P := proposedBlockAt_unique S rho s hP0 hP
    subst P0
    rcases hproc with hemits | ⟨i, hi⟩
    · have hshape := emits_block_shape S rho hemits
      have hslot : P.slot = s := proposedBlockAt_slot S rho s hP
      have heq : S.E.proposer s = v := by
        rw [← hslot]
        exact hshape.2.2
      exact absurd heq.symm hvp
    · have hvoteFreeze : Protocol.vote_time S.E s <
          Protocol.view_freeze S.E s := by
        have hvoteCutoff : Protocol.vote_time S.E s <
            Protocol.support_cutoff S.E s := by
          rw [← Proofs.Optimistic.vote_time_add_delta]
          exact Int.lt_add_of_pos_right _ S.E.Δ_pos
        exact lt_trans hvoteCutoff
          (Proofs.Optimistic.support_cutoff_lt_view_freeze S.E s)
      have hstoreSlot : (rho.stateBefore S i v).st.core.s = s :=
        delivery_store_slot_before_freeze S adm hv hi hlo
          (lt_trans hhi hvoteFreeze)
      have hslot : ¬ (rho.stateBefore S i v).st.core.s < P.erase.slot := by
        rw [hstoreSlot, Proofs.NamedWire.erase_slot, proposedBlockAt_slot S rho s hP]
        exact Nat.lt_irrefl s
      exact admittedBefore_of_delivery_guards S adm hi hslot
        (hFhist v hv i (Nat.le_trans (Nat.le_succ i)
          (index_succ_le_strict_filter_length rho
            adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted
            (Protocol.vote_time S.E s) hi
            (by simpa only [Event.time] using hhi))))
        (proposedBlock_proposer S rho s hP)
        (proposedBlock_parent_slot_lt S adm hs hP)
        (proposedBlock_carried_attestations_admissible S rho s hP) hhi

/-- **The opening proposal is processed at every honest read of the round.**
One post-GST relay puts an honest proposal in every honest store by the vote
duty, and the processed tree only grows. -/


theorem seedOpeningProposal_mem_of_gateOff
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {M : Height} {s : Slot} (hs : 0 < s)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hvoteHor : Protocol.vote_time S.E s ≤ rho.horizon)
    {P : NamedBlock V} (hP : proposedBlockAt S rho s = some P)
    (hPrun : RunBlock S rho P)
    (hPthin : M - 1 ≤ (Protocol.derive_named S.E S.cfg P).h)
    (hvoteFrontier : ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v (Protocol.vote_time S.E s)).h_max = M)
    (hvoteGate : ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v (Protocol.vote_time S.E s)).h_j + 2 ≤ M) :
    ∀ v ∈ rho.honest, ∀ read : Time, Protocol.vote_time S.E s ≤ read →
      P.erase ∈ (rho.storeBeforeTime S v read).T := by
  intro v hv read hread
  have hadmit := proposedBlock_admittedBefore_vote_after_gst S adm hs hprop
    hpost hvoteHor hP
    (seedOpeningProposal_finalizedBelow_of_gateOff S adm hsb hP hPrun hPthin
      hvoteFrontier hvoteGate) v hv
  exact (admittedBefore_mem_and_stamp_at S adm.toNamedScheduleWellFormed hadmit
    hread).1

/-! ## The window record -/

/-- Round arithmetic of the opening window, with bare `Nat` binders. -/
private theorem seedWindowRound_nat {base q : Nat} (h : base + 2 ≤ q) :
    0 < q ∧ base ≤ q - 1 ∧ base ≤ q - 2 ∧ q - 1 + 1 = q ∧
      q - 2 < q - 1 ∧ q - 1 ≤ q ∧ q - 2 ≤ q := by
  omega

/-- The opening slot of a round is at or below the slot before the next
opening. -/
private theorem seedWindowSlot_nat {a b : Nat} (hb : 2 ≤ b) :
    a ≤ a + b - 1 := by
  omega

/- `NamedGateOffOpeningWindowAt` moved to `SeedAdoptionRun.lean`, next to
the erased `GateOffOpeningWindowAt` it replaces, so that the gate-off
opening lifecycle can be stated there. Same namespace and same fields;
this module still sees it through its import of `SeedAdoptionRun`. -/

/-- **The gate-off opening window of a carrier round.** Everything but the
parent height and the three proposal memberships is a read of the raw gate-off
time window; those four come from the proposer's own head floor and one
post-GST relay of the honest proposal. -/

theorem gateOffOpeningWindow_of_window
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {base q : Round}
    (hpostBase : S.E.t_GST ≤ S.a base)
    (hbaseq : base + 2 ≤ q)
    (hhor : S.a (q + 1) ≤ rho.horizon)
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot q) = some P)
    (hwindow : ∀ read : Time, S.a base ≤ read → read ≤ S.a (q + 1) →
      ∀ w ∈ rho.honest,
        (rho.storeBeforeTime S w read).h_j + 2 ≤ M ∧
          (rho.storeBeforeTime S w read).h_max = M) :
    NamedGateOffOpeningWindowAt S rho M q P := by
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  obtain ⟨hqpos, hbasePred, hbasePred2, hqPred, hq21, hpredQ, hpred2Q⟩ :=
    seedWindowRound_nat hbaseq
  have hpostPrev : S.E.t_GST ≤ S.a (q - 1) :=
    hpostBase.trans (Assembly.a_mono S hbasePred)
  have hpostPrev2 : S.E.t_GST ≤ S.a (q - 2) :=
    hpostBase.trans (Assembly.a_mono S hbasePred2)
  have hactionHor : S.a q ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_succ q)).trans hhor
  have hproposalHi : Protocol.proposal_time S.E (S.hc.opening_slot q) ≤
      S.a q := by
    rw [Setup.a, Protocol.a_eq_confirmation_time]
    exact Protocol.proposal_time_le_confirmation_time S.E _
  have hproposalLo : S.a (q - 1) + S.E.Δ ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q) := by
    refine action_add_delta_le_openingProposal_of_round_lt S ?_
    rw [← hqPred]
    exact Nat.lt_succ_self _
  have hpostProposal : S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q) :=
    hpostPrev.trans
      ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans hproposalLo)
  have hpostVote : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot q) :=
    hpostProposal.trans
      (le_of_lt (Protocol.proposal_time_lt_vote_time S.E _))
  have hvoteHi : Protocol.vote_time S.E (S.hc.opening_slot q) ≤ S.a q := by
    rw [Setup.a, Protocol.a_eq_confirmation_time]
    exact Protocol.vote_time_le_confirmation_time S.E _
  have hvoteHor : Protocol.vote_time S.E (S.hc.opening_slot q) ≤
      rho.horizon := hvoteHi.trans hactionHor
  have hproposalHor : Protocol.proposal_time S.E (S.hc.opening_slot q) ≤
      rho.horizon := hproposalHi.trans hactionHor
  have hopenPos : 0 < S.hc.opening_slot q := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos hqpos
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hbaseAction : S.a base ≤ S.a q := Assembly.a_mono S
    (hbasePred.trans hpredQ)
  have hend : ∀ {read : Time}, S.a base ≤ read → read ≤ S.a q →
      ∀ w ∈ rho.honest,
        (rho.storeBeforeTime S w read).h_j + 2 ≤ M ∧
          (rho.storeBeforeTime S w read).h_max = M := by
    intro read hlo hhi w hw
    exact hwindow read hlo (hhi.trans (Assembly.a_mono S (Nat.le_succ q))) w hw
  have hbaseProposal : S.a base ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q) :=
    (Assembly.a_mono S hbasePred).trans
      ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans hproposalLo)
  have hproposerRead := fun w hw =>
    hend hbaseProposal hproposalHi w hw
  have hvoteRead := fun w hw =>
    hend (hbaseProposal.trans
      (le_of_lt (Protocol.proposal_time_lt_vote_time S.E _))) hvoteHi w hw
  have hconfRead := fun w hw =>
    hend (hbaseProposal.trans hproposalHi)
      (le_of_eq (by rw [Setup.a, Protocol.a_eq_confirmation_time])) w hw
  have hnextRead := fun w hw =>
    hwindow (S.a (q + 1)) (Assembly.a_mono S
      ((hbasePred.trans hpredQ).trans (Nat.le_succ q))) (le_refl _) w hw
  -- the parent height and the proposal relay
  have hproposerFrontier : (proposerDutyStore S rho (S.hc.opening_slot q)).h_max
      = M := by
    simpa only [proposerDutyStore, Proofs.Optimistic.tickStore] using
      (hproposerRead (S.E.proposer (S.hc.opening_slot q)) hprop).2
  have hparentHeight : M - 1 ≤
      (Protocol.derive_named S.E S.cfg P.parent).h :=
    seedOpeningParentHeight_of_frontier S adm hP hprop hproposerFrontier
  have hPrun : RunBlock S rho P :=
    Protocol.proposedBlock_runBlock S adm hopenPos hprop hproposalHor hP
  obtain ⟨parent, hparent, -, hheight⟩ :=
    proposedBlockAt_height S rho (S.hc.opening_slot q) hP
  have hparentEq : P.parent = parent := by
    cases P with
    | genesis => simp only [NamedBlock.parent?, reduceCtorEq] at hparent
    | node parent' slot root votes support rows proposer =>
        simpa only [NamedBlock.parent, NamedBlock.parent?, Option.some.injEq]
          using hparent
  subst parent
  have hPthin : M - 1 ≤
      (Protocol.derive_named S.E S.cfg P).h := by
    rcases hheight with hsucc | hsame
    · rw [hsucc]
      exact hparentHeight.trans (Nat.le_add_right _ _)
    · rwa [hsame]
  have hmem := seedOpeningProposal_mem_of_gateOff S adm hsb hopenPos hprop
    hpostProposal hvoteHor hP hPrun hPthin
    (fun w hw => (hvoteRead w hw).2) (fun w hw => (hvoteRead w hw).1)
  exact
    { proposal := hP
      roundPositive := hqpos
      postPreviousAction := hpostPrev
      postFrozenSnapshot := by
        refine hpostPrev2.trans ?_
        refine (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans ?_
        refine (action_add_delta_le_openingProposal_of_round_lt S
          (r := q - 2) (q := q - 1) hq21).trans ?_
        refine Protocol.proposal_time_mono S.E ?_
        have hsucc : S.hc.opening_slot q =
            S.hc.opening_slot (q - 1) + S.hc.R := by
          have h := opening_slot_succ_eq S.hc (q - 1)
          rw [hqPred] at h
          exact h
        rw [hsucc]
        exact seedWindowSlot_nat S.hc.R_ge_two
      postOpeningVote := hpostVote
      previousCutoffInHorizon := by
        refine le_trans ?_ hactionHor
        refine le_trans (le_of_lt (Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos q)) ?_
        refine le_trans (le_of_lt (Γ_0_lt_Γ_1 S.hc S.E.Δ_pos q)) ?_
        refine le_trans (le_of_lt (Γ_1_lt_Γ_2 S.hc S.E.Δ_pos q)) ?_
        rw [Setup.a]
        exact Γ_2_le_a S.hc S.E.Δ_pos q
      nextActionInHorizon := hhor
      parentHeight := hparentHeight
      proposerFrontier := hproposerFrontier
      proposerGateOff := by
        simpa only [proposerDutyStore, Proofs.Optimistic.tickStore] using
          (hproposerRead (S.E.proposer (S.hc.opening_slot q)) hprop).1
      voteFrontier := by
        intro v hv
        simpa only [voteDutyStore, voteStore, tickStore] using (hvoteRead v hv).2
      voteGateOff := by
        intro v hv
        simpa only [voteDutyStore, voteStore, tickStore] using (hvoteRead v hv).1
      proposalAtVote := by
        intro v hv
        simpa only [voteDutyStore, voteStore, tickStore] using
          hmem v hv (Protocol.vote_time S.E (S.hc.opening_slot q)) (le_refl _)
      confirmationFrontier := by
        intro v hv
        simpa only [confStore, tickStore] using (hconfRead v hv).2
      confirmationGateOff := by
        intro v hv
        simpa only [confStore, tickStore] using (hconfRead v hv).1
      proposalAtConfirmation := by
        intro v hv
        simpa only [confStore, tickStore] using
          hmem v hv (Protocol.confirmation_time S.E (S.hc.opening_slot q))
            (Protocol.vote_time_le_confirmation_time S.E _)
      nextFrontier := by
        intro v hv
        simpa only [healStoreAt] using (hnextRead v hv).2
      nextGateOff := by
        intro v hv
        simpa only [healStoreAt] using (hnextRead v hv).1
      proposalAtNext := by
        intro v hv
        simpa only [healStoreAt] using
          hmem v hv (S.a (q + 1))
            (hvoteHi.trans (Assembly.a_mono S (Nat.le_succ q))) }

/-! ## A common grade covers the round's action carriers -/

/-- **A common grade is below every honest action carrier of its round.** The
three SG selector arms all end at or above the store's own fresh anchor or its
own selected grade 2, and the common grade is below both. -/


theorem actionCarriersCover_of_gradeFormsAt
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (hr : 0 < r) (hhor : S.a r ≤ rho.horizon) {Q : Block V}
    (hforms : NamedGradeFormsAt S rho r Q)
    (hactive : ∀ v ∈ rho.honest,
      Q ∈ PhaseGrades.filteredTree (actionReadAt S rho v r)) :
    ActionCarriersCover S rho r Q := by
  intro v hv
  exact preceq_actionSGBlockAt_of_namedGradeFormsAt S
    adm.toNamedAdmissibleCore hr hhor hforms hv (hactive v hv)

/-! ## The exact-height opening package -/

/-- **Leaf (c) from an exact-height opening.** An honest opening proposal at
the exact frontier height, graded one round later, persists as a common grade
through the gate-off window and is still the proposed parent at a later
carrier round.

The parent height is forced: the grade is below every honest action carrier of
The previous round (`actionCarriersCover_of_gradeFormsAt`), those carriers are
below the later opening's parent (`openingAnchorsAligned_of_roundCeiling`), so
the parent is at least as deep as the grade, and the public cap makes it no
deeper. -/


private theorem proposedParent_runBlock
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hprop : S.E.proposer s ∈ rho.honest)
    {P : NamedBlock V} (hP : proposedBlockAt S rho s = some P) :
    RunBlock S rho P.parent := by
  let t := Protocol.proposal_time S.E s
  let p := S.E.proposer s
  have hpay := Proofs.NamedActions.proposal_payload
    (NamedProfile.gradeContract (proposerReadAt S rho s).cache)
    .poolAndCarried S.E S.hc (S.node (S.E.proposer s))
    (proposerReadAt S rho s).st P hP
  have hmem : P.parent ∈ (rho.stateBeforeTime S t p).st.bodies := by
    simpa only [proposerReadAt, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      t, p] using hpay.1
  obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedScheduleWellFormed.sorted t
  apply Proofs.Bridges.runBlock_of_stateBefore_mem S hprop (i := i)
  simpa only [hi] using hmem

/-- Named exact-opening package. The pinned persistence input is the named
replacement for the currently absent `GradeFormsAt` window producer. -/
theorem seedExactOpening_gradePackage
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {q q' : Round} {C' P P' : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot q) = some P)
    (hP' : proposedBlockAt S rho (S.hc.opening_slot q') = some P')
    (hcarrier' : ProposerCarrierAt S rho q')
    (hceiling' : RoundCeilingAt S rho M q' C')
    (hgradeNext : NamedGradeFormsAt S rho (q + 1) P.erase)
    (hPrun : RunBlock S rho P)
    (hexact : (Protocol.derive_named S.E S.cfg P).h = M)
    (hM : 1 ≤ M)
    (hqq' : q + 2 ≤ q')
    (hpostNext : S.E.t_GST ≤ S.a (q + 1))
    (hhorPrev : S.a (q' - 1) ≤ rho.horizon)
    (hactionFrontier : ∀ k, q + 1 ≤ k → k ≤ q' - 1 → ∀ w ∈ rho.honest,
      (actionStoreAt S rho w k).h_max = M)
    (hactionGate : ∀ k, q + 1 ≤ k → k ≤ q' - 1 → ∀ w ∈ rho.honest,
      (actionStoreAt S rho w k).h_j + 2 ≤ M)
    (_of_namedGradeFormsAt_persists_through_gateOffActionWindow :
      NamedGradeFormsAt S rho (q' - 1) P.erase ∧
        ∀ w ∈ rho.honest,
          P.erase ∈ PhaseGrades.filteredTree
            (actionReadAt S rho w (q' - 1)))
    (_of_openingAnchorsAligned_of_roundCeiling : ∀ w ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho w (q' - 1))
        (proposedParent S rho (S.hc.opening_slot q')))
    (hparentCap : (Protocol.derive_named S.E S.cfg P'.parent).h ≤ M) :
    NamedGradeFormsAt S rho (q' - 1) P.erase ∧
      NamedBlock.Preceq P P'.parent ∧
      (Protocol.derive_named S.E S.cfg P'.parent).h =
        (Protocol.derive_named S.E S.cfg P).h := by
  have hspan : q + 1 ≤ q' - 1 := by
    have key : ∀ a b : Nat, a + 2 ≤ b → a + 1 ≤ b - 1 := by
      intro a b h
      omega
    exact key q q' hqq'
  have hroundPos : 0 < q' - 1 :=
    Nat.zero_lt_of_lt (lt_of_lt_of_le (Nat.lt_succ_self q) hspan)
  have hforms := _of_namedGradeFormsAt_persists_through_gateOffActionWindow.1
  have hcover := actionCarriersCover_of_gradeFormsAt S adm hroundPos
    hhorPrev hforms
      _of_namedGradeFormsAt_persists_through_gateOffActionWindow.2
  have hpositive : 0 < ((S.E.committee 0) ∩ rho.honest).card := by
    have hc := hcom 0
    omega
  obtain ⟨x, hxmem⟩ := Finset.card_pos.mp hpositive
  have hx : x ∈ rho.honest := (Finset.mem_inter.mp hxmem).2
  have hbelow : Block.Preceq P.erase
      (proposedParent S rho (S.hc.opening_slot q')) :=
    Block.preceq_trans (hcover x hx)
      (_of_openingAnchorsAligned_of_roundCeiling x hx)
  obtain ⟨parent, hparent, hparentErase⟩ :=
    proposedBlockAt_parent S rho (S.hc.opening_slot q') hP'
  have hparentEq : P'.parent = parent := by
    cases P' with
    | genesis => simp only [NamedBlock.parent?, reduceCtorEq] at hparent
    | node parent' slot root votes support rows proposer =>
        simpa only [NamedBlock.parent, NamedBlock.parent?, Option.some.injEq]
          using hparent
  subst parent
  have hbelow' : Block.Preceq P.erase P'.parent.erase := by
    rw [hparentErase]
    exact hbelow
  obtain ⟨A, hAparent, hAerase⟩ :=
    Proofs.NamedAncestry.erased_ancestor_lift P'.parent hbelow'
  have hparentRun : RunBlock S rho P'.parent :=
    proposedParent_runBlock S adm hcarrier'.1 hP'
  have hArun : RunBlock S rho A :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hparentRun hAparent
  have hPA : P = A := by
    apply adm.toNamedRootCollisionFree.root_injective P A hPrun hArun P A
      (Or.inl (Proofs.NamedAncestry.named_self P))
      (Or.inr (Proofs.NamedAncestry.named_self A))
    rw [← Proofs.NamedWire.erase_root P, ← Proofs.NamedWire.erase_root A, hAerase]
  have hnamed : NamedBlock.Preceq P P'.parent := by
    rw [hPA]
    exact hAparent
  refine ⟨hforms, hnamed, ?_⟩
  have hlower : M ≤ (Protocol.derive_named S.E S.cfg P'.parent).h := by
    rw [← hexact]
    exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hnamed
  rw [hexact]
  exact Nat.le_antisymm hparentCap hlower

end HealingSurface
end Proofs
end DecoupledConsensusModel

#print axioms DecoupledConsensusModel.Proofs.HealingSurface.seedOpeningParentHeight_of_frontier
#print axioms DecoupledConsensusModel.Proofs.HealingSurface.seedOpeningProposal_finalizedBelow_of_gateOff
#print axioms DecoupledConsensusModel.Proofs.HealingSurface.seedOpeningProposal_mem_of_gateOff
#print axioms DecoupledConsensusModel.Proofs.HealingSurface.gateOffOpeningWindow_of_window
#print axioms DecoupledConsensusModel.Proofs.HealingSurface.actionCarriersCover_of_gradeFormsAt
#print axioms DecoupledConsensusModel.Proofs.HealingSurface.seedExactOpening_gradePackage

end
