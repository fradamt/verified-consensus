module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ExcludesRefute
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.SGLifetimeNamed
public import DecoupledConsensusProofs.Generic.FGSafetyFrontierBandNamed
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGOpeningFrozenSuffix
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.PreparedProtectedProposalPivotFrozenBandNamed
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.PreparedProtectedProposalPivotCaptureNamed
public import DecoupledConsensusProofs.Execution.WeakProposalHead
public import DecoupledConsensusProofs.Execution.CommonAncestorBound
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.CarrierInteriorInputs
public import DecoupledConsensusProofs.Protocol.Grades.RelativeOneChain
public import DecoupledConsensusProofs.Protocol.Grades.RelativeSupporter
public import DecoupledConsensusProofs.Generic.PostGSTCarrierAdmissionCore
public import DecoupledConsensusProofs.Protocol.Grades.ProposalWalkComposition

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# The frozen voter tree at a GENERAL honest proposal slot (W4 branches vse)

Conjunct 3 of `MovingSlotAdoptionSupply` (`MovingChainIterateRun.lean:725`):
at an honest proposal slot past the safety deadline, every honest voter's
frozen candidate tree at its vote-duty read is the proposer's tree with the
new proposal inserted as a leaf below the proposal's own parent.

`Proofs.Optimistic.NamedVoteStoreExtends` (`Optimistic/Agreement.lean:1048`) packages
that as six fields: the proposal sits in the read's current slot (`cur`), it
extends the frozen `proposedParent` (`parent`), the frozen tree is `tree₀`
with the proposal inserted (`tree`), the proposal is new there (`fresh`),
nothing yet builds on it (`leaf`), and the exact fork-choice head over the
frozen tree is the proposal itself (`head`).

The opening-slot route reaches all six through
`NamedSGOpeningFrozenVoteAt.voteStoreExtends`
(`SGProposalLifecycleRun.lean:816`), whose engine
`Protocol.namedProposalWalkTransferred_of_frozenCompatiblePivot`
(`ProposalPivotRun.lean:2785`) is already slot-general: everything
opening-specific lives in the SUPPLY of that engine's inputs, not in the
engine. The general-slot supply is exactly the body of the general-slot head
equality `honestProposal_voterHeadAt_eq_after_SG_healing_named_slot`
(`ProposalAdoptionNamedClosedRun`), which builds the walk-transfer record and
then keeps only its `head` field.

This leaf is that same argument returning the whole record. It is deliberately
self-contained (the private helpers the body uses are `private` in their home
module and are copied here verbatim under a `w4vse_` prefix), so the leaf does
not depend on the head equality as a committed export; the head
equality is re-derived here as the record's `head` field.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Internal.NamedRecoveryRead Protocol Proofs.Optimistic Proofs.HealingLemmas
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

private theorem w4vse_namedPreceq_of_runBlocks
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {A B : NamedBlock V} (hArun : RunBlock S rho A)
    (hBrun : RunBlock S rho B) (hAB : Block.Preceq A.erase B.erase) :
    NamedBlock.Preceq A B := by
  obtain ⟨A', hA'B, hA'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hAB
  have hA'run : RunBlock S rho A' :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hBrun hA'B
  have hroot : A.root = A'.root := by
    calc
      A.root = A.erase.root := (Proofs.NamedWire.erase_root A).symm
      _ = A'.erase.root := congrArg Block.root hA'erase.symm
      _ = A'.root := Proofs.NamedWire.erase_root A'
  have hEq : A = A' :=
    adm.toNamedRootCollisionFree.root_injective A A' hArun hA'run A A'
      (Or.inl (Proofs.NamedAncestry.named_self A))
      (Or.inr (Proofs.NamedAncestry.named_self A')) hroot
  rw [hEq]
  exact hA'B

private theorem w4vse_exists_namedGreatestPreviousHead
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {d : Slot} (hd : 0 < d)
    (hhor : Protocol.vote_time S.E d ≤ rho.horizon) :
    ∃ E : NamedBlock V,
      RunBlock S rho E ∧
      (∀ w ∈ rho.honest, Block.Preceq E.erase (voterHeadAt S rho w d)) ∧
      (∀ B : Block V,
        (∀ w ∈ rho.honest, Block.Preceq B (voterHeadAt S rho w d)) →
        Block.Preceq B E.erase) := by
  classical
  obtain ⟨x, hx⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
  have hxcPos : 0 < ((S.E.committee d) ∩ rho.honest).card := by
    have hc := hcom d
    omega
  obtain ⟨x0, hx0⟩ := Finset.card_pos.mp hxcPos
  have hx0c := (Finset.mem_inter.mp hx0).1
  have hx0h := (Finset.mem_inter.mp hx0).2
  let Pred : Block V → Prop := fun B =>
    ∀ w, w ∈ rho.honest → Block.Preceq B (voterHeadAt S rho w d)
  obtain ⟨G, hG, hmax⟩ := greatest_member_of_common_ancestor_bound
    Pred (D := Block.genesis) (H := voterHeadAt S rho x d)
      (fun _ _ => Protocol.preceq_genesis _)
      (fun B hB => hB x hx)
  obtain ⟨X, hXerase, hXrun, -⟩ :=
    WeakGoldfish.voterHead_runBlock_and_emits
      S adm hx0h hd hx0c hhor
  have hGX : Block.Preceq G X.erase := by
    rw [hXerase]
    exact hG x0 hx0h
  obtain ⟨E, hEX, hEerase⟩ := Proofs.NamedAncestry.erased_ancestor_lift X hGX
  have hErun : RunBlock S rho E :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hXrun hEX
  refine ⟨E, hErun, ?_, ?_⟩
  · intro w hw
    rw [hEerase]
    exact hG w hw
  · intro B hB
    rw [hEerase]
    exact hmax B hB

private theorem w4vse_proposedBlock_admittedBefore_vote_after_gst_named
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
      ((proposal_time_lt_vote_time S.E s).le.trans hvoteHor) hP
    exact ⟨P, rfl, i, Protocol.proposal_time S.E s, hacc,
      proposal_time_lt_vote_time S.E s⟩
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
        exact hvoteCutoff.trans
          (Proofs.Optimistic.support_cutoff_lt_view_freeze S.E s)
      have hstoreSlot : (rho.stateBefore S i v).st.core.s = s :=
        delivery_store_slot_before_freeze S adm hv hi hlo
          (hhi.trans hvoteFreeze)
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

private theorem w4vse_namedBody_of_mem_storeBeforeTime
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {t : Time} {P : NamedBlock V}
    (hmem : P.erase ∈ (rho.storeBeforeTime S v t).core.T)
    (hPrun : RunBlock S rho P) :
    P ∈ (rho.storeBeforeTime S v t).bodies := by
  obtain ⟨D, hD, hDErase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho t v hmem
  obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedScheduleWellFormed.sorted t
  have hDprefix : D ∈ (NamedRun.stateBefore S rho i v).st.bodies := by
    rw [← hi]
    exact hD
  have hDrun : RunBlock S rho D :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hv hDprefix
  have hroot : D.root = P.root := by
    rw [← Proofs.NamedWire.erase_root D, ← Proofs.NamedWire.erase_root P, hDErase]
  have hDP : D = P :=
    adm.toNamedRootCollisionFree.root_injective D P hDrun hPrun D P
      (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self P)) hroot
  simpa only [hDP] using hD


/-- Pure-`Nat` bookkeeping for the general-slot deadline bound, kept in its
own lemma with fully opaque parameters: `omega` unfolds
`Protocol.HealConfig.opening_slot` on sight (it is a plain `def`), which turns
`x + 2 * R ≤ start` into a genuinely nonlinear `D * R` term it then silently
drops instead of treating as an atom. Routing the arithmetic through a
top-level lemma with `Nat` parameters (no `HealConfig` in scope) keeps the
atoms opaque so `omega` can use them. -/
private theorem w4vse_deadlineBookkeeping
    (x R start d : Nat) (hRge2 : 2 ≤ R) (hdSucc : d + 1 = start)
    (hD2 : x + 2 * R ≤ start) :
    x + R ≤ d ∧ x + 2 ≤ d ∧ x + 1 ≤ d ∧ 0 < d ∧ x + 2 ≤ start := by omega

/-- Same reason as `w4vse_deadlineBookkeeping`: kept opaque for `omega`. -/
private theorem w4vse_interiorBookkeeping
    (y R start d : Nat) (hRge2 : 2 ≤ R) (hdSucc : d + 1 = start)
    (hstep : y + R ≤ start) :
    y + 1 ≤ d := by omega

/-- Same reason again: `r` below is `S.hc.round_of start = start / S.hc.R`,
a division by a variable that `omega` cannot reason about at all once it
zeta/delta-unfolds the local `let`; every fact about `r` beyond `hrGe`
itself (proved directly, without `omega`) goes through this opaque form. -/
private theorem w4vse_roundBookkeeping (D r : Nat) (hrGe : D + 2 ≤ r) :
    r - 1 + 1 = r ∧ r - 2 + 1 = r - 1 ∧ D ≤ r - 2 ∧ D ≤ r - 1 := by omega

theorem w4_honestProposal_voteStoreExtends_after_SG_healing_named_slot
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {s : Slot}
    (hround2 : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤ s + 1)
    (hhor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    (hopening : S.E.proposer (s + 1) ∈ rho.honest)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (s + 1) = some P) :
    ∀ v ∈ rho.honest, ∃ tree₀ : Finset (Block V),
      Proofs.Optimistic.NamedVoteStoreExtends S rho v (s + 1) tree₀
        (proposedParent S rho (s + 1)) P := by
  classical
  let D := fgSafetyProgressDeadline S rho rGST gap delayExtra
  let start := s + 1
  let d := s
  let r := S.hc.round_of start
  have hdSucc : d + 1 = start := rfl
  have hstartPos : 0 < start := Nat.succ_pos d
  have hRpos : 0 < S.hc.R := lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two
  -- Re-typed against the local `D` so `omega` sees the same atom as the
  -- `opening_slot`-expansion facts below (the raw hypothesis mentions
  -- `fgSafetyProgressDeadline S rho rGST gap delayExtra` syntactically).
  have hD2 : S.hc.opening_slot (D + 2) ≤ start := hround2
  -- Round-level consequence of the slot bound: start is at least two rounds
  -- past the deadline.
  have hrGe : D + 2 ≤ r := by
    show D + 2 ≤ start / S.hc.R
    have h : (D + 2) * S.hc.R ≤ start := by
      have h0 := hD2
      unfold Protocol.HealConfig.opening_slot at h0
      exact h0
    exact (Nat.le_div_iff_mul_le hRpos).mpr h
  have hrbook := w4vse_roundBookkeeping D r hrGe
  have hqEq : r - 1 + 1 = r := hrbook.1
  have hcEq : r - 2 + 1 = r - 1 := hrbook.2.1
  have hcDeadline : D ≤ r - 2 := hrbook.2.2.1
  have hGSTdead : rGST ≤ D := by
    unfold D fgSafetyProgressDeadline
    exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
  have hpostPrev : S.E.t_GST ≤ S.a (r - 1) := by
    have hDr1 : D ≤ r - 1 := hrbook.2.2.2
    exact hpost.trans ((action_strictMono S).monotone (hGSTdead.trans hDr1))
  -- Slot-level bookkeeping: everything below is pure arithmetic from
  -- `hD2` and `S.hc.R_ge_two`, replacing the multiplication-by-`m`
  -- reasoning of the opening-slot theorem. Routed through
  -- `w4vse_deadlineBookkeeping` (see its docstring for why).
  have hexpand1 : S.hc.opening_slot (D + 1) = S.hc.opening_slot D + S.hc.R := by
    unfold Protocol.HealConfig.opening_slot
    ring
  have hexpand2 : S.hc.opening_slot (D + 2) =
      S.hc.opening_slot D + 2 * S.hc.R := by
    unfold Protocol.HealConfig.opening_slot
    ring
  have hRge2 : 2 ≤ S.hc.R := S.hc.R_ge_two
  have hD2' : S.hc.opening_slot D + 2 * S.hc.R ≤ start := by
    rw [← hexpand2]; exact hD2
  have hbook := w4vse_deadlineBookkeeping (S.hc.opening_slot D) S.hc.R start d
    hRge2 hdSucc hD2'
  have hdeadlineRoundSlot : S.hc.opening_slot (D + 1) ≤ d := by
    rw [hexpand1]; exact hbook.1
  have hdeadlineTwoSlot : S.hc.opening_slot D + 2 ≤ d := hbook.2.1
  have hdeadlineSlot : S.hc.opening_slot D + 1 ≤ d := hbook.2.2.1
  have hdPos : 0 < d := hbook.2.2.2.1
  have hdeadlineProposal : S.a D ≤ Protocol.proposal_time S.E start := by
    have hstepD2 : S.hc.opening_slot D + 2 ≤ start := hbook.2.2.2.2
    exact (action_lt_proposal_time_two_after S D).le.trans
      (proposal_time_mono S.E hstepD2)
  have hdeadlineVote : S.a D ≤ Protocol.vote_time S.E start :=
    hdeadlineProposal.trans (proposal_time_lt_vote_time S.E start).le
  have hpostProposal : S.E.t_GST ≤ Protocol.proposal_time S.E start :=
    hpost.trans ((action_strictMono S).monotone hGSTdead |>.trans
      hdeadlineProposal)
  have hprop : S.E.proposer start ∈ rho.honest := hopening
  have hproposalHor : Protocol.proposal_time S.E start ≤ rho.horizon :=
    (proposal_time_lt_vote_time S.E start).le.trans hhor
  have hprevVoteHor : Protocol.vote_time S.E d ≤ rho.horizon :=
    (vote_time_mono_slots S.E (Nat.le_succ d)).trans hhor
  have hprevDelta : Protocol.vote_time S.E d + S.E.Δ ≤ rho.horizon := by
    rw [vote_time_add_delta]
    exact (support_cutoff_le_vote_time_succ S.E d).trans (by
      simpa only [hdSucc] using hhor)
  have hsupportHor : Protocol.support_cutoff S.E d ≤ rho.horizon := by
    simpa only [vote_time_add_delta] using hprevDelta
  have hpostVoteD : S.E.t_GST ≤ Protocol.vote_time S.E d := by
    have hpostD : S.E.t_GST ≤ S.a D := hpost.trans
      ((action_strictMono S).monotone hGSTdead)
    exact hpostD.trans ((a_le_Γ_neg1_succ S.hc S.E.Δ_pos D).trans
      ((Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos (D + 1)).le.trans
        (by
          rw [Protocol.Γ_0_eq_proposal_time]
          exact (proposal_time_mono S.E hdeadlineRoundSlot).trans
            (proposal_time_lt_vote_time S.E d).le)))
  have hpostFrozen : S.E.t_GST ≤ Protocol.proposal_time S.E d :=
    hpost.trans (((action_strictMono S).monotone hGSTdead).trans
      ((action_lt_proposal_time_two_after S D).le.trans
        (proposal_time_mono S.E hdeadlineTwoSlot)))
  obtain ⟨E, hErun, hEheads, hEmax⟩ :=
    w4vse_exists_namedGreatestPreviousHead S adm.toNamedAdmissibleCore hcom
      hdPos hprevVoteHor
  have hprotected : ProtectedVoteSlot S rho d E.erase := by
    refine ⟨hEheads, ?_⟩
    intro x hx hxc
    obtain ⟨X, hXerase, hXrun, hXemit⟩ :=
      WeakGoldfish.voterHead_runBlock_and_emits
        S adm.toNamedAdmissibleCore hx hdPos hxc hprevVoteHor
    exact ⟨X, by simpa only [hXerase] using hEheads x hx, hXrun, hXemit⟩
  have hinterior : S.hc.opening_slot (r - 1) + 1 ≤ d := by
    have hexpandR : S.hc.opening_slot (r - 1 + 1) =
        S.hc.opening_slot (r - 1) + S.hc.R := by
      unfold Protocol.HealConfig.opening_slot
      ring
    have hopenR : S.hc.opening_slot r ≤ start := by
      show S.hc.opening_slot (start / S.hc.R) ≤ start
      unfold Protocol.HealConfig.opening_slot
      exact Nat.div_mul_le_self start S.hc.R
    have hstepR : S.hc.opening_slot (r - 1) + S.hc.R ≤ start := by
      rw [← hexpandR, hqEq]; exact hopenR
    exact w4vse_interiorBookkeeping (S.hc.opening_slot (r - 1)) S.hc.R start d
      hRge2 hdSucc hstepR
  have hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u (r - 1)) E.erase := by
    intro u hu
    apply hEmax
    intro w hw
    have h := actionSGBlock_preceq_voterHeadAt_after_GST
      S adm hcom hbelow hrec hdelay hpost hcDeadline
      (by simpa only [hcEq] using hinterior) hprevDelta hu hw
    simpa only [hcEq] using h
  have hreadBound : ∀ {read : Time}, S.a D ≤ read →
      read ≤ rho.horizon → read ≤ Protocol.confirmation_time S.E d →
      ∀ {u : V}, u ∈ rho.honest →
      Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S u read).core.toHealing.toFG) E.erase := by
    intro read hread hreadHor hnext u hu
    apply hEmax
    intro w hw
    exact fgRoot_preceq_previousHead_through_confirmation_after_GST
      S adm hcom hbelow hrec hdelay hpost hread hreadHor
      hdeadlineSlot hnext hprevDelta hu hw
  have hproposalNext : Protocol.proposal_time S.E start ≤
      Protocol.confirmation_time S.E d := by
    rw [← hdSucc]
    exact (proposal_time_lt_vote_time S.E (d + 1)).le.trans (by
      rw [← vote_time_succ_add_delta_eq_confirmation_time S.E d]
      exact Int.le_add_of_nonneg_right S.E.Δ_pos.le)
  have hvoteNext : Protocol.vote_time S.E start ≤
      Protocol.confirmation_time S.E d := by
    rw [← hdSucc, ← vote_time_succ_add_delta_eq_confirmation_time S.E d]
    exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
  have hsourceRoot : Block.Preceq
      (Protocol.get_fg_root
        (proposerReadAt S rho start).st.core.toHealing.toFG) E.erase := by
    simpa only [proposerReadAt, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
      using hreadBound hdeadlineProposal hproposalHor hproposalNext hprop
  have hopenR : S.hc.opening_slot r ≤ start := by
    show S.hc.opening_slot (start / S.hc.R) ≤ start
    unfold Protocol.HealConfig.opening_slot
    exact Nat.div_mul_le_self start S.hc.R
  have hcut : S.hc.Γ_neg1 S.E.Δ r ≤ rho.horizon :=
    (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos r).le.trans
      (by
        rw [Protocol.Γ_0_eq_proposal_time]
        exact (proposal_time_mono S.E hopenR).trans hproposalHor)
  have hroundStart : S.hc.round_of start = r - 1 + 1 := hqEq.symm
  have hsourceAnchor : Block.Preceq
      (nodeAnchor S (proposerReadAt S rho start)
        (S.hc.round_of (proposerReadAt S rho start).st.core.s)) E.erase := by
    have h := proposalAnchorAt_preceq_of_previousCarriers_named
      S adm hbelow (q := r - 1) (s := start) hroundStart
      hpostPrev (by rw [hqEq]; exact hcut) hproposalHor hupper hprop hsourceRoot
    exact h
  have hsourceBandData := exists_namedCommonPreviousHeadAncestor_in_frontierBand_through_confirmation_after_GST
      S adm hcom hbelow hrec hdelay hpost
    hdeadlineProposal hproposalHor hdeadlineSlot hproposalNext hprevDelta hprop
  obtain ⟨Ts, hTsrun, hTsband, hTsheads⟩ := hsourceBandData
  have hTsE : Block.Preceq Ts.erase E.erase := hEmax Ts.erase hTsheads
  have hTsENamed : NamedBlock.Preceq Ts E :=
    w4vse_namedPreceq_of_runBlocks S adm hTsrun hErun hTsE
  have hsourceBand :
      (proposerReadAt S rho start).st.core.h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg E).h := by
    exact hTsband.trans
      (Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hTsENamed)
  have hEparent : Block.Preceq E.erase (proposedParent S rho start) := by
    have hrootCompat : Block.compatible
        (Protocol.get_fg_root
          (proposalDutyRead S rho start).st.core.toHealing.toFG) E.erase = true :=
      Block.compatible_of_preceq_common hsourceRoot (Block.preceq_self E.erase)
    have hheadsCone : NamedHonestVotesCone S rho d
        (fun X => Block.Preceq E.erase X) := hprotected.cone
    have hsupport := fixedRoot_preparedProposalConeSupport_of_namedCone
      S adm hcom hdPos hpostVoteD
      hsupportHor (by simpa only [hdSucc] using hprop)
      (by simpa only [hdSucc] using hsourceRoot) hheadsCone
    have hvalid := Protocol.proposerDutyStore_proposer_view_valid_core
      S adm.toNamedAdmissibleCore start
    have hproposerVoteRoot : Block.Preceq
        (Protocol.get_fg_root
          (voteDutyRead S rho (S.E.proposer start) start).st.core.toHealing.toFG)
        E.erase := by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
        using hreadBound hdeadlineVote hhor hvoteNext hprop
    have hwitness : CanonicalConeWitness
        (proposalDutyRead S rho start).st.core E.erase := by
      have hmem : E.erase ∈ (proposalDutyRead S rho start).st.core.T := by
        have havailable := honestHeadsAvailableBefore_of_namedPostHealingCone
          S adm hprop hpostVoteD hsupportHor
          (by simpa only [hdSucc] using hproposerVoteRoot)
          hheadsCone
        obtain ⟨x, hx⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
        have hxcPos : 0 < ((S.E.committee d) ∩ rho.honest).card := by
          have hc := hcom d
          omega
        obtain ⟨x0, hx0⟩ := Finset.card_pos.mp hxcPos
        have hx0c := (Finset.mem_inter.mp hx0).1
        have hx0h := (Finset.mem_inter.mp hx0).2
        obtain ⟨X, hXerase, hXrun, hXemit⟩ :=
          WeakGoldfish.voterHead_runBlock_and_emits S adm.toNamedAdmissibleCore
            hx0h hdPos hx0c hprevVoteHor
        have hXhead : HonestHead S rho d X.erase :=
          ⟨x0, hx0h, hx0c, ⟨X, rfl, hXrun⟩, hXemit⟩
        rcases havailable X.erase hXhead with hgen | hadmit
        · have hEgenPre : Block.Preceq E.erase Block.genesis := by
            have hh := hEheads x0 hx0h
            rw [← hXerase, hgen] at hh
            exact hh
          have hEgen : E.erase = Block.genesis :=
            Block.preceq_antisymm hEgenPre
              (Protocol.preceq_genesis E.erase)
          simpa only [hEgen, proposalDutyRead, proposerReadAt,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
            using (Protocol.genesis_mem_and_stamp_storeBeforeTime S
              adm.toNamedScheduleWellFormed (S.E.proposer start)
              (Protocol.proposal_time S.E start)
              (Protocol.proposal_time S.E start)).1
        · have hXT := (admittedBefore_mem_and_stamp_at S
              adm.toNamedScheduleWellFormed hadmit
              (support_cutoff_le_proposal_time_succ S.E d)).1
          have hpc := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
            (Protocol.proposal_time S.E start) (S.E.proposer start)
          have hEX : Block.Preceq E.erase X.erase := by
            rw [hXerase]
            exact hEheads x0 hx0h
          exact Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
            E.erase X.erase (by simpa only [hdSucc] using hXT) hEX
      have hEbody := w4vse_namedBody_of_mem_storeBeforeTime S adm hprop
        (by simpa only [proposalDutyRead, proposerReadAt,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
          using hmem) hErun
      have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho
        (Protocol.proposal_time S.E start) (S.E.proposer start) E hEbody
      refine ⟨E.erase, hmem, Block.preceq_self _, ?_⟩
      rw [show ((proposalDutyRead S rho start).st.core.σ E.erase).h =
          (Protocol.derive_named S.E S.cfg E).h by
        simpa only [proposalDutyRead, proposerReadAt,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
          using congrArg (fun z => z.h) hview]
      exact hsourceBand
    exact fixedRoot_preparedProposalHead_preceq_of_cone S adm
      hrootCompat hwitness hsourceAnchor (by simpa only [hdSucc] using hsupport) (by
        simpa only [proposalDutyRead, proposerReadAt,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
          using hvalid)
  obtain ⟨Parent, hParent, hParentErase⟩ := proposedBlockAt_parent S rho start hP
  have hEParent : Block.Preceq E.erase Parent.erase := by
    simpa only [hParentErase] using hEparent
  have hparentP : Block.Preceq Parent.erase P.erase := by
    calc
      Parent.erase = proposedParent S rho start := hParentErase
      _ = P.erase.parent := (proposedBlockErased_parent S rho start hP).symm
      _ ⪯ P.erase := preceq_parent P.erase
  have hEP : Block.Preceq E.erase P.erase := Block.preceq_trans hEParent hparentP
  have hPrun : RunBlock S rho P :=
    proposedBlock_runBlock S adm hstartPos hprop hproposalHor hP
  have hFhist : ProposalFinalizedBelowAtDeliveries S rho start P := by
    intro w hw i hi
    have hrootE : Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S w (Protocol.vote_time S.E start)).core.toHealing.toFG)
        E.erase := hreadBound hdeadlineVote hhor hvoteNext hw
    exact finalized_preceq_at_prefix_of_storeBeforeRoot_preceq S rho
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted
      (Block.preceq_trans hrootE hEP) hi
  have hadmit : ∀ v ∈ rho.honest,
      AdmittedBefore S rho v P.erase (Protocol.vote_time S.E start) :=
    w4vse_proposedBlock_admittedBefore_vote_after_gst_named S adm hstartPos hprop
      hpostProposal hhor hP hFhist
  intro v hv
  have htargetRoot : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho v start).st.core.toHealing.toFG) E.erase := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
      using hreadBound hdeadlineVote hhor hvoteNext hv
  have htargetBandData := exists_namedCommonPreviousHeadAncestor_in_frontierBand_through_confirmation_after_GST
      S adm hcom hbelow hrec hdelay hpost
    hdeadlineVote hhor hdeadlineSlot hvoteNext hprevDelta hv
  obtain ⟨Tt, hTtrun, hTtband, hTtheads⟩ := htargetBandData
  have hTtE : Block.Preceq Tt.erase E.erase := hEmax Tt.erase hTtheads
  have hTtP : Block.Preceq Tt.erase P.erase := Block.preceq_trans hTtE hEP
  have hTtPNamed : NamedBlock.Preceq Tt P :=
    w4vse_namedPreceq_of_runBlocks S adm hTtrun hPrun hTtP
  have hPmem : P.erase ∈ (voteDutyRead S rho v start).st.core.T :=
    (admittedBefore_mem_and_stamp_at S adm.toNamedScheduleWellFormed
      (hadmit v hv) (le_refl _)).1
  have hPbody := w4vse_namedBody_of_mem_storeBeforeTime S adm hv
    (by simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
      using hPmem) hPrun
  have hPview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho
    (Protocol.vote_time S.E start) v P hPbody
  have hPband : (Proofs.Optimistic.voteDutyStore S rho v start).h_max - 1 ≤
      ((Proofs.Optimistic.voteDutyStore S rho v start).σ P.erase).h := by
    rw [show ((Proofs.Optimistic.voteDutyStore S rho v start).σ P.erase).h =
        (Protocol.derive_named S.E S.cfg P).h by
      simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore] using
        congrArg (fun z => z.h) hPview]
    exact hTtband.trans
      (Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hTtPNamed)
  have hne : E.erase ≠ P.erase := by
    intro heq
    have hdepth := Block.preceq_depth_le hEParent
    have hpar : P.erase.parent? = some Parent.erase := by
      have hmapped := congrArg (Option.map NamedBlock.erase) hParent
      simpa only [Proofs.NamedWire.erase_parent_optional, Option.map_some] using hmapped
    have hstrict := depth_of_parent? hpar
    rw [heq] at hdepth
    omega
  obtain ⟨hcandidate, -, -⟩ := interiorProposal_candidateAndPivotPath
    S adm hstartPos hv hP hParent (hadmit v hv) hPband htargetRoot
      hEParent hne
  have hsourceCoreMem : E.erase ∈ (proposerReadAt S rho start).st.core.T := by
    have hpMem := proposedParent_mem S rho start
    have hpc := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
      (Protocol.proposal_time S.E start) (S.E.proposer start)
    exact Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
      E.erase (proposedParent S rho start) (by
        simpa only [proposerReadAt, NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
          using hpMem) hEparent
  have hsourceBody := w4vse_namedBody_of_mem_storeBeforeTime S adm hprop
    (by simpa only [proposerReadAt, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
      using hsourceCoreMem) hErun
  have htargetCoreMem : E.erase ∈ (voteDutyRead S rho v start).st.core.T := by
    have hpc := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
      (Protocol.vote_time S.E start) v
    exact Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
      E.erase P.erase hPmem hEP
  have htargetBody := w4vse_namedBody_of_mem_storeBeforeTime S adm hv
    (by simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
      using htargetCoreMem) hErun
  have htargetAnchor : Block.Preceq (voterAnchorAt S rho v start) E.erase := by
    have h := voterAnchorAt_preceq_of_previousCarriers S adm hbelow
      (q := r - 1) (s := d) (by simpa only [hdSucc] using hroundStart)
      hpostPrev (by rw [hqEq]; exact hcut) (by simpa only [hdSucc] using hhor)
      hupper hv (by simpa only [hdSucc] using htargetRoot)
    simpa only [hdSucc] using h
  have hpivot : PreparedProtectedProposalPivot S rho d v E :=
    { slotProtected := hprotected
      sourceAnchor := by simpa only [hdSucc] using hsourceAnchor
      targetAnchor := by simpa only [hdSucc] using htargetAnchor
      sourceBody := by simpa only [hdSucc] using hsourceBody
      targetBody := by simpa only [hdSucc] using htargetBody
      sourceBand := by simpa only [hdSucc] using hsourceBand
      targetBand := by
        simpa only [hdSucc] using hTtband.trans
          (Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg
            (w4vse_namedPreceq_of_runBlocks S adm hTtrun hErun hTtE))
      parent := by simpa only [hdSucc] using hEparent }
  have hfrozen := PreparedProtectedProposalPivot.frozenBandInputs
    S adm.toNamedAdmissibleCore (by simpa only [hdSucc] using hP)
      (by simpa only [hdSucc] using hcandidate) hpivot
  have htargetPass := PreparedProtectedProposalPivot.preceq_proposalFreeHead_core
    S adm.toNamedAdmissibleCore hcom hdPos
      hpostVoteD hsupportHor hv (by simpa only [hdSucc] using hP) hpivot
  have hsuffix := namedProposalPivotSuffixTransfer_of_riseLeOne
    S adm (by simpa only [hdSucc] using hstartPos)
      (by simpa only [hdSucc, Nat.add_sub_cancel] using hpostFrozen)
      (by simpa only [hdSucc] using hprop) hv
      (by simpa only [hdSucc] using hhor)
      (by simpa only [hdSucc] using hP) hfrozen
  have hscoreBridge := namedProposalCandidateScoreBridge_afterGST
    S adm (by simpa only [hdSucc] using hstartPos)
      (by simpa only [hdSucc, Nat.add_sub_cancel] using hpostFrozen)
      (by simpa only [hdSucc] using hprop) hv
      (by simpa only [hdSucc] using hhor)
      (by simpa only [hdSucc] using hP)
      (frozenVoterCandidateTree_subset_filtered S.E _ hfrozen.proposalCandidate)
  have hstore := Protocol.namedProposalWalkTransferred_of_frozenCompatiblePivot
    S adm (by simpa only [hdSucc] using hP)
      (by simpa only [hdSucc] using hprop) hv
      (by simpa only [hdSucc] using hcandidate)
      hfrozen.proposalAnchorCompatible hfrozen.sourceAnchor
      (by simpa only [hdSucc] using hEparent) htargetPass hsuffix
      (by
        simpa only [hdSucc] using
          (carrierInterior_scoreEq_of_scoreBridge
            (rho := rho) (s := start) (v := v) (P := P) S hP
              (by simpa only [hdSucc] using hscoreBridge)))
  exact ⟨namedWalkTargetTree S rho start v P, hstore⟩

#print axioms w4_honestProposal_voteStoreExtends_after_SG_healing_named_slot



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
