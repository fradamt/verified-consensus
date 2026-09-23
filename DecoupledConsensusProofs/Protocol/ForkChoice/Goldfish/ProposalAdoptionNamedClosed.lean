module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
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
# Arbitrary healed named proposal adoption

This leaf ports the direct arbitrary-carrier route. Its only pre-built input
is the pinned named global frontier witness. No band-selected lifecycle
records is used.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Internal.NamedRecoveryRead Protocol Proofs.Optimistic Proofs.HealingLemmas
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

private theorem namedPreceq_of_runBlocks
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



private theorem exists_namedGreatestPreviousHead
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

private theorem proposedBlock_admittedBefore_vote_after_gst_named
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

private theorem namedBody_of_mem_storeBeforeTime
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

theorem honestProposal_voterHeadAt_eq_after_SG_healing_named_of_pins
    (_of_frontier : ∀
      (S : Setup V) {rho : Run V}, Admissible S rho →
      HonestCommittees S rho.honest → BelowOneThird S rho.honest →
      ∀ {rGST gap : Round}, MultiProposerRecurrence S rho gap →
      TimeoutDelayBound S delayExtra → S.E.t_GST ≤ S.a rGST →
      ∀ {read : Time},
      S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) ≤ read →
      read ≤ rho.horizon →
      ∀ {s : Slot},
      S.hc.opening_slot
        (fgSafetyProgressDeadline S rho rGST gap delayExtra) + 1 ≤ s →
      read ≤ Protocol.confirmation_time S.E s →
      Protocol.vote_time S.E s + S.E.Δ ≤ rho.horizon →
      ∀ {u : V}, u ∈ rho.honest →
      ∃ T : NamedBlock V,
        RunBlock S rho T ∧
        (rho.storeBeforeTime S u read).h_max - 1 ≤
          (Protocol.derive_named S.E S.cfg T).h ∧
        ∀ w ∈ rho.honest, T.erase ⪯ voterHeadAt S rho w s)
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {m : Round}
    (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m)
    (hhor : Protocol.vote_time S.E (S.hc.opening_slot m) ≤ rho.horizon)
    (hopening : S.E.proposer (S.hc.opening_slot m) ∈ rho.honest)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot m) = some P) :
    ∀ v ∈ rho.honest,
      voterHeadAt S rho v (S.hc.opening_slot m) = P.erase := by
  classical
  let D := fgSafetyProgressDeadline S rho rGST gap delayExtra
  let start := S.hc.opening_slot m
  let d := start - 1
  have hmPos : 2 ≤ m := (Nat.le_add_left 2 D).trans hm
  have hstartPos : 0 < start := by
    unfold start Protocol.HealConfig.opening_slot
    exact Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_two hmPos)
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hdPos : 0 < d := by
    have hfour : 4 ≤ start := by
      unfold start Protocol.HealConfig.opening_slot
      exact (show 2 * 2 ≤ m * S.hc.R from
        Nat.mul_le_mul hmPos S.hc.R_ge_two)
    change 0 < start - 1
    exact Nat.sub_pos_of_lt ((by decide : 1 < 4).trans_le hfour)
  have hdSucc : d + 1 = start := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
    (Nat.ne_of_gt hstartPos))
  have hprop : S.E.proposer start ∈ rho.honest := by
    simpa only [start] using hopening
  have hproposalHor : Protocol.proposal_time S.E start ≤ rho.horizon :=
    (proposal_time_lt_vote_time S.E start).le.trans hhor
  have hprevVoteHor : Protocol.vote_time S.E d ≤ rho.horizon :=
    (vote_time_mono_slots S.E (Nat.sub_le start 1)).trans hhor
  have hprevDelta : Protocol.vote_time S.E d + S.E.Δ ≤ rho.horizon := by
    rw [vote_time_add_delta]
    exact (support_cutoff_le_vote_time_succ S.E d).trans (by
      simpa only [hdSucc] using hhor)
  have hsupportHor : Protocol.support_cutoff S.E d ≤ rho.horizon := by
    simpa only [vote_time_add_delta] using hprevDelta
  have hdeadlineSlot : S.hc.opening_slot D + 1 ≤ d := by
    have hstep : S.hc.opening_slot D + 1 <
        S.hc.opening_slot (D + 1) := by
      simpa only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
        using Nat.add_lt_add_left (Nat.lt_of_succ_le S.hc.R_ge_two)
          (D * S.hc.R)
    have hround : D + 1 ≤ m :=
      (Nat.le_succ (D + 1)).trans (by simpa only [Nat.add_assoc] using hm)
    have hlt : S.hc.opening_slot D + 1 < start :=
      hstep.trans_le (by
        simpa only [start, Protocol.HealConfig.opening_slot] using
          Nat.mul_le_mul_right S.hc.R hround)
    exact Nat.le_sub_of_add_le (Nat.succ_le_iff.mpr hlt)
  have hdeadlineProposal : S.a D ≤ Protocol.proposal_time S.E start := by
    have hround : S.hc.opening_slot D + 2 ≤ start := by
      have hstep : S.hc.opening_slot D + 2 ≤
          S.hc.opening_slot (D + 1) := by
        simp only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
        exact Nat.add_le_add_left S.hc.R_ge_two (D * S.hc.R)
      have hDm : D + 1 ≤ m :=
        (Nat.le_succ (D + 1)).trans (by simpa only [Nat.add_assoc] using hm)
      exact hstep.trans (by
        simpa only [start, Protocol.HealConfig.opening_slot] using
          Nat.mul_le_mul_right S.hc.R hDm)
    exact (action_lt_proposal_time_two_after S D).le.trans
      (proposal_time_mono S.E hround)
  have hdeadlineVote : S.a D ≤ Protocol.vote_time S.E start :=
    hdeadlineProposal.trans (proposal_time_lt_vote_time S.E start).le
  have hpostProposal : S.E.t_GST ≤ Protocol.proposal_time S.E start := by
    have hGSTdead : rGST ≤ D := by
      unfold D fgSafetyProgressDeadline
      exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
    exact hpost.trans ((action_strictMono S).monotone hGSTdead |>.trans
      hdeadlineProposal)
  obtain ⟨E, hErun, hEheads, hEmax⟩ :=
    exists_namedGreatestPreviousHead S adm.toNamedAdmissibleCore hcom
      hdPos hprevVoteHor
  have hprotected : ProtectedVoteSlot S rho d E.erase := by
    refine ⟨hEheads, ?_⟩
    intro x hx hxc
    obtain ⟨X, hXerase, hXrun, hXemit⟩ :=
      WeakGoldfish.voterHead_runBlock_and_emits
        S adm.toNamedAdmissibleCore hx hdPos hxc hprevVoteHor
    exact ⟨X, by simpa only [hXerase] using hEheads x hx, hXrun, hXemit⟩
  have hmOne : 1 ≤ m := (by decide : 1 ≤ 2).trans hmPos
  have hmPredOne : 1 ≤ m - 1 := Nat.le_sub_of_add_le hmPos
  have hqEq : m - 1 + 1 = m := Nat.sub_add_cancel hmOne
  have hcEq : m - 2 + 1 = m - 1 :=
    by
      simpa only [Nat.sub_sub, Nat.add_comm, Nat.reduceAdd] using
        Nat.sub_add_cancel hmPredOne
  have hcDeadline : D ≤ m - 2 := Nat.le_sub_of_add_le hm
  have hpostPrev : S.E.t_GST ≤ S.a (m - 1) := by
    have hGSTdead : rGST ≤ D := by
      unfold D fgSafetyProgressDeadline
      exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
    exact hpost.trans ((action_strictMono S).monotone
      (hGSTdead.trans (hcDeadline.trans (Nat.sub_le (m - 1) 1))))
  have hdeadlineRoundSlot : S.hc.opening_slot (D + 1) ≤ d := by
    have hround : D + 1 < m :=
      (Nat.lt_succ_self (D + 1)).trans_le
        (by simpa only [Nat.add_assoc] using hm)
    have hlt : S.hc.opening_slot (D + 1) < start := by
      unfold start Protocol.HealConfig.opening_slot
      exact Nat.mul_lt_mul_of_pos_right hround
        (Nat.zero_lt_of_lt S.hc.R_ge_two)
    exact Nat.le_sub_of_add_le (Nat.succ_le_iff.mpr hlt)
  have hpostVoteD : S.E.t_GST ≤ Protocol.vote_time S.E d := by
    have hGSTdead : rGST ≤ D := by
      unfold D fgSafetyProgressDeadline
      exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
    have hpostD : S.E.t_GST ≤ S.a D :=
      hpost.trans ((action_strictMono S).monotone hGSTdead)
    exact hpostD.trans ((a_le_Γ_neg1_succ S.hc S.E.Δ_pos D).trans
      ((Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos (D + 1)).le.trans
        (by
          rw [Protocol.Γ_0_eq_proposal_time]
          exact (proposal_time_mono S.E hdeadlineRoundSlot).trans
            (proposal_time_lt_vote_time S.E d).le)))
  have hdeadlineTwoSlot : S.hc.opening_slot D + 2 ≤ d := by
    have hstep : S.hc.opening_slot D + 2 ≤
        S.hc.opening_slot (D + 1) := by
      simp only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
      exact Nat.add_le_add_left S.hc.R_ge_two (D * S.hc.R)
    exact hstep.trans hdeadlineRoundSlot
  have hpostFrozen : S.E.t_GST ≤ Protocol.proposal_time S.E d := by
    have hGSTdead : rGST ≤ D := by
      unfold D fgSafetyProgressDeadline
      exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
    exact hpost.trans (((action_strictMono S).monotone hGSTdead).trans
      ((action_lt_proposal_time_two_after S D).le.trans
        (proposal_time_mono S.E hdeadlineTwoSlot)))
  have hinterior : S.hc.opening_slot (m - 1) + 1 ≤ d := by
    have hstep : S.hc.opening_slot (m - 1) + 1 <
        S.hc.opening_slot (m - 1 + 1) := by
      simpa only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
        using Nat.add_lt_add_left (Nat.lt_of_succ_le S.hc.R_ge_two)
          ((m - 1) * S.hc.R)
    have hlt : S.hc.opening_slot (m - 1) + 1 < start := by
      simpa only [hqEq, start] using hstep
    exact Nat.le_sub_of_add_le (Nat.succ_le_iff.mpr hlt)
  have hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u (m - 1)) E.erase := by
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
  have hcut : S.hc.Γ_neg1 S.E.Δ m ≤ rho.horizon := by
    have hopen : S.hc.Γ_0 S.E.Δ m =
        Protocol.proposal_time S.E start := by
      rw [Protocol.Γ_0_eq_proposal_time]
    exact (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos m).le.trans
      (by rw [hopen]; exact hproposalHor)
  have hsourceAnchor : Block.Preceq
      (nodeAnchor S (proposerReadAt S rho start)
        (S.hc.round_of (proposerReadAt S rho start).st.core.s)) E.erase := by
    have h := fixedRoot_preparedProposalAnchor_preceq_of_previousCarriers
      S adm hbelow (q := m - 1) hpostPrev (by simpa only [hqEq] using hcut)
      (by simpa only [hqEq, start] using hproposalHor) hupper
      (by simpa only [hqEq, start] using hprop)
      (by simpa only [hqEq, start] using hsourceRoot)
    have hround : S.hc.round_of (proposerReadAt S rho start).st.core.s = m := by
      simpa only [start, proposerReadAt, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.slotOf_proposal_time] using
          round_of_opening_slot_eq_schedule S.hc m
    simpa only [start, hqEq, hround] using h
  have hsourceBandData := _of_frontier S adm hcom hbelow hrec hdelay hpost
    hdeadlineProposal hproposalHor hdeadlineSlot hproposalNext hprevDelta hprop
  obtain ⟨Ts, hTsrun, hTsband, hTsheads⟩ := hsourceBandData
  have hTsE : Block.Preceq Ts.erase E.erase := hEmax Ts.erase hTsheads
  have hTsENamed : NamedBlock.Preceq Ts E :=
    namedPreceq_of_runBlocks S adm hTsrun hErun hTsE
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
      have hEbody := namedBody_of_mem_storeBeforeTime S adm hprop
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
    proposedBlock_admittedBefore_vote_after_gst_named S adm hstartPos hprop
      hpostProposal hhor hP hFhist
  intro v hv
  have htargetRoot : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho v start).st.core.toHealing.toFG) E.erase := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
      using hreadBound hdeadlineVote hhor hvoteNext hv
  have htargetBandData := _of_frontier S adm hcom hbelow hrec hdelay hpost
    hdeadlineVote hhor hdeadlineSlot hvoteNext hprevDelta hv
  obtain ⟨Tt, hTtrun, hTtband, hTtheads⟩ := htargetBandData
  have hTtE : Block.Preceq Tt.erase E.erase := hEmax Tt.erase hTtheads
  have hTtP : Block.Preceq Tt.erase P.erase := Block.preceq_trans hTtE hEP
  have hTtPNamed : NamedBlock.Preceq Tt P :=
    namedPreceq_of_runBlocks S adm hTtrun hPrun hTtP
  have hPmem : P.erase ∈ (voteDutyRead S rho v start).st.core.T :=
    (admittedBefore_mem_and_stamp_at S adm.toNamedScheduleWellFormed
      (hadmit v hv) (le_refl _)).1
  have hPbody := namedBody_of_mem_storeBeforeTime S adm hv
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
  have hsourceBody := namedBody_of_mem_storeBeforeTime S adm hprop
    (by simpa only [proposerReadAt, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
      using hsourceCoreMem) hErun
  have htargetCoreMem : E.erase ∈ (voteDutyRead S rho v start).st.core.T := by
    have hpc := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
      (Protocol.vote_time S.E start) v
    exact Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
      E.erase P.erase hPmem hEP
  have htargetBody := namedBody_of_mem_storeBeforeTime S adm hv
    (by simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
      using htargetCoreMem) hErun
  have hroundStart : S.hc.round_of start = m := by
    simpa only [start] using round_of_opening_slot_eq_schedule S.hc m
  have htargetAnchor : Block.Preceq (voterAnchorAt S rho v start) E.erase := by
    have h := voterAnchorAt_preceq_of_previousCarriers S adm hbelow
      (q := m - 1) (s := d) (by simpa only [hdSucc, hqEq] using hroundStart)
      hpostPrev (by simpa only [hqEq] using hcut) (by simpa only [hdSucc] using hhor)
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
            (namedPreceq_of_runBlocks S adm hTtrun hErun hTtE))
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
  simpa only [hdSucc, start] using hstore.head

#print axioms honestProposal_voterHeadAt_eq_after_SG_healing_named_of_pins



/-- Pure-`Nat` bookkeeping for the general-slot deadline bound, kept in its
own lemma with fully opaque parameters: `omega` unfolds
`Protocol.HealConfig.opening_slot` on sight (it is a plain `def`), which turns
`x + 2 * R ≤ start` into a genuinely nonlinear `D * R` term it then silently
drops instead of treating as an atom. Routing the arithmetic through a
top-level lemma with `Nat` parameters (no `HealConfig` in scope) keeps the
atoms opaque so `omega` can use them. -/
private theorem gs1_deadlineBookkeeping
    (x R start d : Nat) (hRge2 : 2 ≤ R) (hdSucc : d + 1 = start)
    (hD2 : x + 2 * R ≤ start) :
    x + R ≤ d ∧ x + 2 ≤ d ∧ x + 1 ≤ d ∧ 0 < d ∧ x + 2 ≤ start := by omega

/-- Same reason as `gs1_deadlineBookkeeping`: kept opaque for `omega`. -/
private theorem gs1_interiorBookkeeping
    (y R start d : Nat) (hRge2 : 2 ≤ R) (hdSucc : d + 1 = start)
    (hstep : y + R ≤ start) :
    y + 1 ≤ d := by omega

/-- Same reason again: `r` below is `S.hc.round_of start = start / S.hc.R`,
a division by a variable that `omega` cannot reason about at all once it
zeta/delta-unfolds the local `let`; every fact about `r` beyond `hrGe`
itself (proved directly, without `omega`) goes through this opaque form. -/
private theorem gs1_roundBookkeeping (D r : Nat) (hrGe : D + 2 ≤ r) :
    r - 1 + 1 = r ∧ r - 2 + 1 = r - 1 ∧ D ≤ r - 2 ∧ D ≤ r - 1 := by omega


/-- **Closed twin of `honestProposal_voterHeadAt_eq_after_SG_healing_named_slot_of_pins`,
with the `_of_sourceAnchor` pin discharged** ( gs, deliverable 1).

The pin above has no room for `Admissible`/`BelowOneThird`/post-GST hypotheses
in its own signature, so it cannot be discharged by the general anchor
producer (which needs them for its "active G1" branch). This twin proves the
general-slot head equality directly instead, reusing the SAME body shape
(the opening theorem's proof from `hreadBound` onward, byte for byte) but
closing the previous-round proposal anchor with the already-general
`proposalAnchorAt_preceq_of_previousCarriers_named`
(`SeedCeilingStepRun.lean:3539`, doc: "covers later slots"), which is the
general-slot counterpart of `fixedRoot_preparedProposalAnchor_preceq_of_previousCarriers`
in exactly the way `voterAnchorAt_preceq_of_previousCarriers` already is for
the vote anchor. -/
theorem honestProposal_voterHeadAt_eq_after_SG_healing_named_slot
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
    ∀ v ∈ rho.honest,
      voterHeadAt S rho v (s + 1) = P.erase := by
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
  have hrbook := gs1_roundBookkeeping D r hrGe
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
  -- `gs1_deadlineBookkeeping` (see its docstring for why).
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
  have hbook := gs1_deadlineBookkeeping (S.hc.opening_slot D) S.hc.R start d
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
    exists_namedGreatestPreviousHead S adm.toNamedAdmissibleCore hcom
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
    exact gs1_interiorBookkeeping (S.hc.opening_slot (r - 1)) S.hc.R start d
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
    namedPreceq_of_runBlocks S adm hTsrun hErun hTsE
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
      have hEbody := namedBody_of_mem_storeBeforeTime S adm hprop
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
    proposedBlock_admittedBefore_vote_after_gst_named S adm hstartPos hprop
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
    namedPreceq_of_runBlocks S adm hTtrun hPrun hTtP
  have hPmem : P.erase ∈ (voteDutyRead S rho v start).st.core.T :=
    (admittedBefore_mem_and_stamp_at S adm.toNamedScheduleWellFormed
      (hadmit v hv) (le_refl _)).1
  have hPbody := namedBody_of_mem_storeBeforeTime S adm hv
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
  have hsourceBody := namedBody_of_mem_storeBeforeTime S adm hprop
    (by simpa only [proposerReadAt, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
      using hsourceCoreMem) hErun
  have htargetCoreMem : E.erase ∈ (voteDutyRead S rho v start).st.core.T := by
    have hpc := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
      (Protocol.vote_time S.E start) v
    exact Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
      E.erase P.erase hPmem hEP
  have htargetBody := namedBody_of_mem_storeBeforeTime S adm hv
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
            (namedPreceq_of_runBlocks S adm hTtrun hErun hTtE))
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
  simpa only [hdSucc, start] using hstore.head

#print axioms honestProposal_voterHeadAt_eq_after_SG_healing_named_slot

/-- Five-line corollary: at an arbitrary healed carrier's slot, the honest
committee's votes are already in the cone below the adopted proposal, via
`protectedVoteSlot_of_coreHeads` read through the general-slot head
equality (same pattern as
`honestProposal_openingVoteCone_after_SG_healing_named_of_openingProposer`). -/
theorem honestProposal_slotVoteCone_after_SG_healing_named
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
    NamedHonestVotesCone S rho (s + 1) (fun X => Block.Preceq P.erase X) := by
  have hheads := honestProposal_voterHeadAt_eq_after_SG_healing_named_slot
    S adm hcom hbelow hrec hdelay hpost hround2 hhor hopening hP
  exact (protectedVoteSlot_of_coreHeads S adm.toNamedAdmissibleCore
    (Nat.succ_pos s) hhor (by
      intro v hv
      simpa only [Protocol.voteDutyHead, hheads v hv] using
        (Block.preceq_self P.erase))).cone

#print axioms honestProposal_slotVoteCone_after_SG_healing_named

theorem honestProposal_voterHeadAt_eq_after_SG_healing_named_of_openingProposer
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {m : Round}
    (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m)
    (hhor : Protocol.vote_time S.E (S.hc.opening_slot m) ≤ rho.horizon)
    (hopening : S.E.proposer (S.hc.opening_slot m) ∈ rho.honest)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot m) = some P) :
    ∀ v ∈ rho.honest,
      voterHeadAt S rho v (S.hc.opening_slot m) = P.erase :=
  honestProposal_voterHeadAt_eq_after_SG_healing_named_of_pins
    exists_namedCommonPreviousHeadAncestor_in_frontierBand_through_confirmation_after_GST
    S adm hcom hbelow hrec hdelay hpost hm hhor hopening hP

#print axioms honestProposal_voterHeadAt_eq_after_SG_healing_named_of_openingProposer

/-- At an arbitrary healed carrier, every honest opening confirmation read has
the prepared anchor below the named proposal and retains that proposal in its
confirmation candidate tree. -/
theorem honestProposal_confirmationReadFacts_after_SG_healing_named_of_openingProposer
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {m : Round}
    (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot m) ≤ rho.horizon)
    (hopening : S.E.proposer (S.hc.opening_slot m) ∈ rho.honest)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot m) = some P) :
    ∀ v ∈ rho.honest,
      namedConfirmationAnchor S
          (confirmationInputRead S rho v (S.hc.opening_slot m)) ⪯ P.erase ∧
        P.erase ∈
          confTree (confirmationInputRead S rho v
            (S.hc.opening_slot m)).st.core := by
  classical
  let D := fgSafetyProgressDeadline S rho rGST gap delayExtra
  let start := S.hc.opening_slot m
  have hmPos : 2 ≤ m := (Nat.le_add_left 2 D).trans hm
  have hstartPos : 0 < start := by
    unfold start Protocol.HealConfig.opening_slot
    exact Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_two hmPos)
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hprop : S.E.proposer start ∈ rho.honest := by
    simpa only [start] using hopening
  have hvoteHor : Protocol.vote_time S.E start ≤ rho.horizon :=
    (vote_time_le_confirmation_time S.E start).trans hhor
  have hproposalHor : Protocol.proposal_time S.E start ≤ rho.horizon :=
    (proposal_time_lt_vote_time S.E start).le.trans hvoteHor
  have hvoteDelta : Protocol.vote_time S.E start + S.E.Δ ≤ rho.horizon := by
    rw [vote_time_add_delta]
    exact (support_cutoff_le_confirmation_time S.E start).trans hhor
  have hdeadlineSlot : S.hc.opening_slot D + 1 ≤ start := by
    have hstep : S.hc.opening_slot D + 1 <
        S.hc.opening_slot (D + 1) := by
      simpa only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
        using Nat.add_lt_add_left (Nat.lt_of_succ_le S.hc.R_ge_two)
          (D * S.hc.R)
    have hround : D + 1 ≤ m :=
      (Nat.le_succ (D + 1)).trans (by simpa only [Nat.add_assoc] using hm)
    exact hstep.le.trans (by
      simpa only [start, Protocol.HealConfig.opening_slot] using
        Nat.mul_le_mul_right S.hc.R hround)
  have hdeadlineProposal : S.a D ≤ Protocol.proposal_time S.E start := by
    have hround : S.hc.opening_slot D + 2 ≤ start := by
      have hstep : S.hc.opening_slot D + 2 ≤
          S.hc.opening_slot (D + 1) := by
        simp only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
        exact Nat.add_le_add_left S.hc.R_ge_two (D * S.hc.R)
      have hDm : D + 1 ≤ m :=
        (Nat.le_succ (D + 1)).trans (by simpa only [Nat.add_assoc] using hm)
      exact hstep.trans (by
        simpa only [start, Protocol.HealConfig.opening_slot] using
          Nat.mul_le_mul_right S.hc.R hDm)
    exact (action_lt_proposal_time_two_after S D).le.trans
      (proposal_time_mono S.E hround)
  have hdeadlineVote : S.a D ≤ Protocol.vote_time S.E start :=
    hdeadlineProposal.trans (proposal_time_lt_vote_time S.E start).le
  have hdeadlineRead : S.a D ≤ Protocol.confirmation_time S.E start :=
    hdeadlineVote.trans (vote_time_le_confirmation_time S.E start)
  have hpostProposal : S.E.t_GST ≤ Protocol.proposal_time S.E start := by
    have hGSTdead : rGST ≤ D := by
      unfold D fgSafetyProgressDeadline
      exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
    exact hpost.trans (((action_strictMono S).monotone hGSTdead).trans
      hdeadlineProposal)
  have hheads : ∀ w ∈ rho.honest, voterHeadAt S rho w start = P.erase :=
    honestProposal_voterHeadAt_eq_after_SG_healing_named_of_openingProposer
      S adm hcom hbelow hrec hdelay hpost
        (by simpa only [D] using hm) (by simpa only [start] using hvoteHor)
        hopening (by simpa only [start] using hP)
  have hrootVote : ∀ w ∈ rho.honest,
      Block.Preceq
        (Protocol.get_fg_root
          (voteDutyRead S rho w start).st.core.toHealing.toFG) P.erase := by
    intro w hw
    have hrootHead := fgRoot_preceq_previousHead_through_confirmation_after_GST
      S adm hcom hbelow hrec hdelay hpost hdeadlineVote hvoteHor
        hdeadlineSlot (vote_time_le_confirmation_time S.E start)
        hvoteDelta hw hw
    have hrootHead' : Block.Preceq
        (Protocol.get_fg_root
          (voteDutyRead S rho w start).st.core.toHealing.toFG)
        (voterHeadAt S rho w start) := by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Protocol.voteDutyHead] using hrootHead
    simpa only [hheads w hw] using hrootHead'
  have hFhist : ProposalFinalizedBelowAtDeliveries S rho start P := by
    intro w hw i hi
    exact finalized_preceq_at_prefix_of_storeBeforeRoot_preceq S rho
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted
      (hrootVote w hw) hi
  have hadmit : ∀ w ∈ rho.honest,
      AdmittedBefore S rho w P.erase (Protocol.vote_time S.E start) :=
    proposedBlock_admittedBefore_vote_after_gst_named S adm hstartPos hprop
      hpostProposal hvoteHor hP hFhist
  have hPrun : RunBlock S rho P :=
    proposedBlock_runBlock S adm hstartPos hprop hproposalHor hP
  have hmOne : 1 ≤ m := (by decide : 1 ≤ 2).trans hmPos
  have hpred : m - 1 + 1 = m := Nat.sub_add_cancel hmOne
  have hcEq : m - 2 + 1 = m - 1 := by
    have hmPredOne : 1 ≤ m - 1 := Nat.le_sub_of_add_le hmPos
    simpa only [Nat.sub_sub, Nat.add_comm, Nat.reduceAdd] using
      Nat.sub_add_cancel hmPredOne
  have hcDeadline : D ≤ m - 2 := Nat.le_sub_of_add_le hm
  have hpostPrev : S.E.t_GST ≤ S.a (m - 1) := by
    have hGSTdead : rGST ≤ D := by
      unfold D fgSafetyProgressDeadline
      exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
    exact hpost.trans ((action_strictMono S).monotone
      (hGSTdead.trans (hcDeadline.trans (Nat.sub_le (m - 1) 1))))
  have hinterior : S.hc.opening_slot (m - 1) + 1 ≤ start := by
    have hstep : S.hc.opening_slot (m - 1) + 1 <
        S.hc.opening_slot (m - 1 + 1) := by
      simpa only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
        using Nat.add_lt_add_left (Nat.lt_of_succ_le S.hc.R_ge_two)
          ((m - 1) * S.hc.R)
    simpa only [hpred, start] using hstep.le
  have hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u (m - 1)) P.erase := by
    intro u hu
    have h := actionSGBlock_preceq_voterHeadAt_after_GST
      S adm hcom hbelow hrec hdelay hpost hcDeadline
        (by simpa only [hcEq] using hinterior) hvoteDelta hu hu
    rw [hheads u hu] at h
    simpa only [hcEq] using h
  have hcut : S.hc.Γ_neg1 S.E.Δ m ≤ rho.horizon := by
    have hopen : S.hc.Γ_0 S.E.Δ m =
        Protocol.proposal_time S.E start := by
      rw [Protocol.Γ_0_eq_proposal_time]
    exact (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos m).le.trans
      (by rw [hopen]; exact hproposalHor)
  intro v hv
  have hroot : Block.Preceq
      (Protocol.get_fg_root
        (confirmationInputRead S rho v start).st.core.toHealing.toFG) P.erase := by
    have hrootHead := fgRoot_preceq_previousHead_through_confirmation_after_GST
      S adm hcom hbelow hrec hdelay hpost hdeadlineRead hhor
        hdeadlineSlot (le_refl _) hvoteDelta hv hv
    have hrootHead' : Block.Preceq
        (Protocol.get_fg_root
          (confirmationInputRead S rho v start).st.core.toHealing.toFG)
        (voterHeadAt S rho v start) := by
      simpa only [confirmationInputRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Protocol.voteDutyHead] using hrootHead
    simpa only [hheads v hv] using hrootHead'
  have hround : S.hc.round_of (start + 1) = m - 1 + 1 := by
    simpa only [start, hpred] using Proofs.HealingLemmas.round_of_opening_succ S.hc m
  have hanchor : Block.Preceq (confirmationAnchorAt S rho v start) P.erase :=
    confirmationAnchorAt_preceq_of_previousCarriers S adm hbelow hround
      hpostPrev (by simpa only [hpred] using hcut) hhor
      (by simpa only [hpred] using hupper) hv hroot
  have hPmem : P.erase ∈
      (confirmationInputRead S rho v start).st.core.T :=
    (admittedBefore_mem_and_stamp_at S adm.toNamedScheduleWellFormed
      (hadmit v hv) (vote_time_le_confirmation_time S.E start)).1
  have hPbody := namedBody_of_mem_storeBeforeTime S adm hv
    (by simpa only [confirmationInputRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
      using hPmem) hPrun
  have hPview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho
    (Protocol.confirmation_time S.E start) v P hPbody
  obtain ⟨T, hTrun, hTband, hTheads⟩ :=
    exists_namedCommonPreviousHeadAncestor_in_frontierBand_through_confirmation_after_GST
      S adm hcom hbelow hrec hdelay hpost hdeadlineRead hhor
        hdeadlineSlot (le_refl _) hvoteDelta hv
  have hTP : Block.Preceq T.erase P.erase := by
    simpa only [hheads v hv] using hTheads v hv
  have hTPNamed : NamedBlock.Preceq T P :=
    namedPreceq_of_runBlocks S adm hTrun hPrun hTP
  have hPband :
      (confirmationInputRead S rho v start).st.core.h_max - 1 ≤
        ((confirmationInputRead S rho v start).st.core.σ P.erase).h := by
    rw [show ((confirmationInputRead S rho v start).st.core.σ P.erase).h =
        (Protocol.derive_named S.E S.cfg P).h by
      simpa only [confirmationInputRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
        congrArg (fun z => z.h) hPview]
    exact hTband.trans
      (Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hTPNamed)
  have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
    S rho (Protocol.confirmation_time S.E start) v
  have hFP : Block.Preceq
      (confirmationInputRead S rho v start).st.core.F P.erase := by
    exact Block.preceq_trans (by
      simpa only [confirmationInputRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
          (Proofs.Records.preceq_get_fg_root_of_F
            (st := (rho.storeBeforeTime S v
              (Protocol.confirmation_time S.E start)).core.toHealing.toFG) hFJ)) hroot
  have hV : P.erase ∈ Protocol.V_tree
      (confirmationInputRead S rho v start).st.core.toHealing.toFG := by
    simp only [Protocol.V_tree, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq, Protocol.Store.toHealing]
    exact ⟨⟨hPmem, hFP⟩, P.erase, hPmem, Block.preceq_self _, hPband⟩
  have hcandidate : P.erase ∈
      confTree (confirmationInputRead S rho v start).st.core :=
    Proofs.Records.mem_filtered_of_mem_V_tree hV hroot
  exact ⟨by simpa only [confirmationAnchorAt] using hanchor, hcandidate⟩

#print axioms honestProposal_confirmationReadFacts_after_SG_healing_named_of_openingProposer


/-- **The healed honest proposal's confirmation-read facts, at a GENERAL
slot** (W4 branches gs2).

Additive twin of
`honestProposal_confirmationReadFacts_after_SG_healing_named_of_openingProposer`
with the read slot generalised from `S.hc.opening_slot m` to an arbitrary
post-deadline slot `d + 1`, the same generalisation
`honestProposal_voterHeadAt_eq_after_SG_healing_named_slot` already carries
out for the head equality (now closed, no pins). `hheads` below is exactly
that theorem; every other named producer this proof calls
(`fgRoot_preceq_previousHead_through_confirmation_after_GST`,
`exists_namedCommonPreviousHeadAncestor_in_frontierBand_through_confirmation_after_GST`,
`actionSGBlock_preceq_voterHeadAt_after_GST`) is already general over its slot
argument, so the body is the opening-slot proof unchanged from `hheads`
onward, with the deadline/round bookkeeping re-derived the way
`honestProposal_voterHeadAt_eq_after_SG_healing_named_slot` re-derives it.

One step needed a second look versus the opening-slot proof: identifying the
confirmation anchor's prepared frame via
`confirmationAnchorAt_preceq_of_previousCarriers`'s `hround: round_of (start
+ 1) = q + 1`. At an opening slot `q:= m - 1` always works, because an
opening slot's successor never leaves its round (`R ≥ 2`). At a general slot
`start = d + 1` the successor CAN cross into the next round, exactly when
`start` is the last slot of its round; the proof below case-splits on that
(`start + 1 < opening_slot (m + 1)` vs. `start + 1 = opening_slot (m + 1)`),
using `q:= m - 1` in the first case (the existing `hupper`, unchanged) and
`q:= m` in the second, closed by instantiating
`actionSGBlock_preceq_voterHeadAt_after_GST` at round `m` itself (valid there
because the boundary case gives `S.hc.opening_slot m + 1 ≤ start`, the exact
bound that producer needs) and by computing
`S.hc.Γ_neg1 S.E.Δ (m + 1) ≤ rho.horizon` directly from `hhor` through the
`confirmation_time S.E start = proposal_time S.E (start + 1) + 2Δ` identity
(`Protocol.confirmation_time_eq_support_cutoff_succ`). -/
theorem honestProposal_confirmationReadFacts_after_SG_healing_named_slot
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {d : Slot}
    (hd : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤ d)
    (hhor : Protocol.confirmation_time S.E (d + 1) ≤ rho.horizon)
    (hopening : S.E.proposer (d + 1) ∈ rho.honest)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (d + 1) = some P) :
    ∀ v ∈ rho.honest,
      namedConfirmationAnchor S
          (confirmationInputRead S rho v (d + 1)) ⪯ P.erase ∧
        P.erase ∈
          confTree (confirmationInputRead S rho v (d + 1)).st.core := by
  classical
  let D := fgSafetyProgressDeadline S rho rGST gap delayExtra
  let start := d + 1
  let m := S.hc.round_of start
  have hroundMono : ∀ {a b : Slot}, a ≤ b →
      S.hc.round_of a ≤ S.hc.round_of b := by
    intro a b hab
    simpa only [Protocol.HealConfig.round_of] using Nat.div_le_div_right hab
  have hopenTwo : ∀ {a b : Round}, a + 1 ≤ b →
      S.hc.opening_slot a + 2 ≤ S.hc.opening_slot b := by
    intro a b hab
    have hstep : S.hc.opening_slot a + 2 ≤ S.hc.opening_slot (a + 1) := by
      simp only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
      exact Nat.add_le_add_left S.hc.R_ge_two (a * S.hc.R)
    exact hstep.trans (Nat.mul_le_mul_right S.hc.R hab)
  have hdTwo : S.hc.opening_slot (D + 2) ≤ d := hd
  have hdTwo' : S.hc.opening_slot (D + 1 + 1) ≤ d := hd
  have hdRound : D + 2 ≤ m := by
    have h1 := hroundMono (hdTwo.trans (Nat.le_succ d))
    rwa [round_of_opening_slot_eq_schedule S.hc (D + 2)] at h1
  have hopenLe : S.hc.opening_slot m ≤ start := by
    simp only [m, Protocol.HealConfig.round_of, Protocol.HealConfig.opening_slot]
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self start S.hc.R
  have hmPos : 2 ≤ m := (Nat.le_add_left 2 D).trans hdRound
  have hstartPos : 0 < start := Nat.succ_pos d
  have hGSTdeadTop : rGST ≤ D := by
    unfold D fgSafetyProgressDeadline
    exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
  have hprop : S.E.proposer start ∈ rho.honest := hopening
  have hvoteHor : Protocol.vote_time S.E start ≤ rho.horizon :=
    (vote_time_le_confirmation_time S.E start).trans hhor
  have hproposalHor : Protocol.proposal_time S.E start ≤ rho.horizon :=
    (proposal_time_lt_vote_time S.E start).le.trans hvoteHor
  have hvoteDelta : Protocol.vote_time S.E start + S.E.Δ ≤ rho.horizon := by
    rw [vote_time_add_delta]
    exact (support_cutoff_le_confirmation_time S.E start).trans hhor
  have hdeadlineTwoSlot : S.hc.opening_slot D + 2 ≤ d :=
    (hopenTwo (Nat.le_add_right (D + 1) 1)).trans hdTwo'
  have hdeadlineSlotPrev : S.hc.opening_slot D + 1 ≤ d :=
    Nat.le_of_succ_le hdeadlineTwoSlot
  have hdeadlineSlot : S.hc.opening_slot D + 1 ≤ start :=
    hdeadlineSlotPrev.trans (Nat.le_succ d)
  have hdeadlineProposal : S.a D ≤ Protocol.proposal_time S.E start :=
    (action_lt_proposal_time_two_after S D).le.trans
      (proposal_time_mono S.E (hdeadlineTwoSlot.trans (Nat.le_succ d)))
  have hdeadlineVote : S.a D ≤ Protocol.vote_time S.E start :=
    hdeadlineProposal.trans (proposal_time_lt_vote_time S.E start).le
  have hdeadlineRead : S.a D ≤ Protocol.confirmation_time S.E start :=
    hdeadlineVote.trans (vote_time_le_confirmation_time S.E start)
  have hpostProposal : S.E.t_GST ≤ Protocol.proposal_time S.E start :=
    hpost.trans ((action_strictMono S).monotone hGSTdeadTop |>.trans
      hdeadlineProposal)
  have hheads : ∀ w ∈ rho.honest, voterHeadAt S rho w start = P.erase :=
    honestProposal_voterHeadAt_eq_after_SG_healing_named_slot
      S adm hcom hbelow hrec hdelay hpost
      (hd.trans (Nat.le_succ d)) hvoteHor hopening hP
  have hrootVote : ∀ w ∈ rho.honest,
      Block.Preceq
        (Protocol.get_fg_root
          (voteDutyRead S rho w start).st.core.toHealing.toFG) P.erase := by
    intro w hw
    have hrootHead := fgRoot_preceq_previousHead_through_confirmation_after_GST
      S adm hcom hbelow hrec hdelay hpost hdeadlineVote hvoteHor
        hdeadlineSlot (vote_time_le_confirmation_time S.E start)
        hvoteDelta hw hw
    have hrootHead' : Block.Preceq
        (Protocol.get_fg_root
          (voteDutyRead S rho w start).st.core.toHealing.toFG)
        (voterHeadAt S rho w start) := by
      simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Protocol.voteDutyHead] using hrootHead
    simpa only [hheads w hw] using hrootHead'
  have hFhist : ProposalFinalizedBelowAtDeliveries S rho start P := by
    intro w hw i hi
    exact finalized_preceq_at_prefix_of_storeBeforeRoot_preceq S rho
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted
      (hrootVote w hw) hi
  have hadmit : ∀ w ∈ rho.honest,
      AdmittedBefore S rho w P.erase (Protocol.vote_time S.E start) :=
    proposedBlock_admittedBefore_vote_after_gst_named S adm hstartPos hprop
      hpostProposal hvoteHor hP hFhist
  have hPrun : RunBlock S rho P :=
    proposedBlock_runBlock S adm hstartPos hprop hproposalHor hP
  have hmOne : 1 ≤ m := (by decide : 1 ≤ 2).trans hmPos
  have hmPredOne : 1 ≤ m - 1 := Nat.le_sub_of_add_le hmPos
  have hqEq : m - 1 + 1 = m := Nat.sub_add_cancel hmOne
  have hcEq : m - 2 + 1 = m - 1 := by
    simpa only [Nat.sub_sub, Nat.add_comm, Nat.reduceAdd] using
      Nat.sub_add_cancel hmPredOne
  have hcDeadline : D ≤ m - 2 := Nat.le_sub_of_add_le hdRound
  have hinterior : S.hc.opening_slot (m - 1) + 1 ≤ start :=
    (Nat.le_succ (S.hc.opening_slot (m - 1) + 1)).trans
      ((hopenTwo (Nat.le_of_eq hqEq)).trans hopenLe)
  have hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u (m - 1)) P.erase := by
    intro u hu
    have h := actionSGBlock_preceq_voterHeadAt_after_GST
      S adm hcom hbelow hrec hdelay hpost hcDeadline
        (by simpa only [hcEq] using hinterior) hvoteDelta hu hu
    rw [hheads u hu] at h
    simpa only [hcEq] using h
  have hDm1 : D ≤ m - 1 := by
    rw [← hcEq]
    exact hcDeadline.trans (Nat.le_succ (m - 2))
  have hpostPrev : S.E.t_GST ≤ S.a (m - 1) :=
    hpost.trans ((action_strictMono S).monotone (hGSTdeadTop.trans hDm1))
  have hcut : S.hc.Γ_neg1 S.E.Δ m ≤ rho.horizon := by
    have hopen : S.hc.Γ_0 S.E.Δ m =
        Protocol.proposal_time S.E (S.hc.opening_slot m) := by
      rw [Protocol.Γ_0_eq_proposal_time]
    exact (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos m).le.trans
      (by rw [hopen]; exact (proposal_time_mono S.E hopenLe).trans hproposalHor)
  -- `start + 1` is either still inside round `m` or crosses into round
  -- `m + 1` (it can only ever cross by at most one round). The interior
  -- branch reuses `hupper`/`hpostPrev`/`hcut` above unchanged, at `q:= m - 1`;
  -- the boundary branch (`start` the last slot of round `m`) needs its own
  -- `q:= m` versions, closed directly below rather than pinned.
  have hstartLtNext : start < S.hc.opening_slot (m + 1) := by
    show start < (start / S.hc.R + 1) * S.hc.R
    apply (Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt S.hc.R_ge_two)).mp
    exact Nat.lt_succ_self (start / S.hc.R)
  intro v hv
  have hroot : Block.Preceq
      (Protocol.get_fg_root
        (confirmationInputRead S rho v start).st.core.toHealing.toFG) P.erase := by
    have hrootHead := fgRoot_preceq_previousHead_through_confirmation_after_GST
      S adm hcom hbelow hrec hdelay hpost hdeadlineRead hhor
        hdeadlineSlot (le_refl _) hvoteDelta hv hv
    have hrootHead' : Block.Preceq
        (Protocol.get_fg_root
          (confirmationInputRead S rho v start).st.core.toHealing.toFG)
        (voterHeadAt S rho v start) := by
      simpa only [confirmationInputRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Protocol.voteDutyHead] using hrootHead
    simpa only [hheads v hv] using hrootHead'
  have hanchor : Block.Preceq (confirmationAnchorAt S rho v start) P.erase := by
    rcases (Nat.succ_le_of_lt hstartLtNext).lt_or_eq with hlt | heqBoundary
    · have hroundSucc : S.hc.round_of (start + 1) = (m - 1) + 1 := by
        rw [hqEq]
        exact round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc
          (Nat.succ_le_succ hopenLe) hlt
      exact confirmationAnchorAt_preceq_of_previousCarriers S adm hbelow
        hroundSucc hpostPrev (by rw [hqEq]; exact hcut) hhor hupper hv hroot
    · have heqB : start + 1 = S.hc.opening_slot (m + 1) := heqBoundary
      have hroundSucc : S.hc.round_of (start + 1) = m + 1 := by
        rw [heqB]
        exact round_of_opening_slot_eq_schedule S.hc (m + 1)
      have hopenSuccEq : S.hc.opening_slot (m + 1) =
          S.hc.opening_slot m + S.hc.R := by
        unfold Protocol.HealConfig.opening_slot
        ring
      have hstartEq : start + 1 = S.hc.opening_slot m + S.hc.R := by
        rw [heqB, hopenSuccEq]
      have hRge2 := S.hc.R_ge_two
      have hopenLtStart : S.hc.opening_slot m + 1 ≤ start := by
        have hstep : S.hc.opening_slot m + 1 + 1 ≤
            S.hc.opening_slot m + S.hc.R := Nat.add_le_add_left hRge2 _
        rw [← hstartEq] at hstep
        exact Nat.le_of_succ_le_succ hstep
      have hDm : D ≤ m := (Nat.le_add_right D 2).trans hdRound
      have hpostM : S.E.t_GST ≤ S.a m :=
        hpost.trans ((action_strictMono S).monotone (hGSTdeadTop.trans hDm))
      have hΓeq : S.hc.Γ_neg1 S.E.Δ (m + 1) =
          Protocol.proposal_time S.E (S.hc.opening_slot (m + 1)) - S.E.Δ := by
        rw [← Protocol.Γ_0_eq_proposal_time]
        rfl
      have hcutM : S.hc.Γ_neg1 S.E.Δ (m + 1) ≤ rho.horizon := by
        have hce : Protocol.confirmation_time S.E start =
            Protocol.proposal_time S.E (start + 1) + 2 * S.E.Δ := by
          rw [Protocol.confirmation_time_eq_support_cutoff_succ]
          rfl
        have hΔpos := S.E.Δ_pos
        have hstep : Protocol.proposal_time S.E (start + 1) - S.E.Δ ≤
            Protocol.confirmation_time S.E start := by
          rw [hce]; linarith
        rw [hΓeq, ← heqB]
        exact hstep.trans hhor
      have hupperM : ∀ u ∈ rho.honest,
          Block.Preceq (actionSGBlockAt S rho u m) P.erase := by
        intro u hu
        have h := actionSGBlock_preceq_voterHeadAt_after_GST
          S adm hcom hbelow hrec hdelay hpost (c := m - 1)
          hDm1 (by rw [hqEq]; exact hopenLtStart) hvoteDelta hu hu
        rw [hheads u hu] at h
        simpa only [hqEq] using h
      exact confirmationAnchorAt_preceq_of_previousCarriers S adm hbelow
        hroundSucc hpostM hcutM hhor hupperM hv hroot
  have hPmem : P.erase ∈
      (confirmationInputRead S rho v start).st.core.T :=
    (admittedBefore_mem_and_stamp_at S adm.toNamedScheduleWellFormed
      (hadmit v hv) (vote_time_le_confirmation_time S.E start)).1
  have hPbody := namedBody_of_mem_storeBeforeTime S adm hv
    (by simpa only [confirmationInputRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
      using hPmem) hPrun
  have hPview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho
    (Protocol.confirmation_time S.E start) v P hPbody
  obtain ⟨T, hTrun, hTband, hTheads⟩ :=
    exists_namedCommonPreviousHeadAncestor_in_frontierBand_through_confirmation_after_GST
      S adm hcom hbelow hrec hdelay hpost hdeadlineRead hhor
        hdeadlineSlot (le_refl _) hvoteDelta hv
  have hTP : Block.Preceq T.erase P.erase := by
    simpa only [hheads v hv] using hTheads v hv
  have hTPNamed : NamedBlock.Preceq T P :=
    namedPreceq_of_runBlocks S adm hTrun hPrun hTP
  have hPband :
      (confirmationInputRead S rho v start).st.core.h_max - 1 ≤
        ((confirmationInputRead S rho v start).st.core.σ P.erase).h := by
    rw [show ((confirmationInputRead S rho v start).st.core.σ P.erase).h =
        (Protocol.derive_named S.E S.cfg P).h by
      simpa only [confirmationInputRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
        congrArg (fun z => z.h) hPview]
    exact hTband.trans
      (Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hTPNamed)
  have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
    S rho (Protocol.confirmation_time S.E start) v
  have hFP : Block.Preceq
      (confirmationInputRead S rho v start).st.core.F P.erase := by
    exact Block.preceq_trans (by
      simpa only [confirmationInputRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
          (Proofs.Records.preceq_get_fg_root_of_F
            (st := (rho.storeBeforeTime S v
              (Protocol.confirmation_time S.E start)).core.toHealing.toFG) hFJ)) hroot
  have hV : P.erase ∈ Protocol.V_tree
      (confirmationInputRead S rho v start).st.core.toHealing.toFG := by
    simp only [Protocol.V_tree, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq, Protocol.Store.toHealing]
    exact ⟨⟨hPmem, hFP⟩, P.erase, hPmem, Block.preceq_self _, hPband⟩
  have hcandidate : P.erase ∈
      confTree (confirmationInputRead S rho v start).st.core :=
    Proofs.Records.mem_filtered_of_mem_V_tree hV hroot
  exact ⟨by simpa only [confirmationAnchorAt] using hanchor, hcandidate⟩

#print axioms honestProposal_confirmationReadFacts_after_SG_healing_named_slot



/-- P3 with the carrier's post-deadline bound made explicit. The bound rules
out the slot-zero case that the unqualified statement admitted. -/
theorem honestProposal_openingVoteCone_after_SG_healing_named_of_openingProposer
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {rGST gap : Round} {m : Round}
    (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m)
    (hopening : S.E.proposer (S.hc.opening_slot m) ∈ rho.honest)
    (hhor : Protocol.vote_time S.E (S.hc.opening_slot m) ≤ rho.horizon)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot m) = some P)
    (hheads : ∀ v ∈ rho.honest,
      voterHeadAt S rho v (S.hc.opening_slot m) = P.erase) :
    NamedHonestVotesCone S rho (S.hc.opening_slot m)
      (fun X => Block.Preceq P.erase X) := by
  have hmPos : 2 ≤ m :=
    (Nat.le_add_left 2
      (fgSafetyProgressDeadline S rho rGST gap delayExtra)).trans hm
  have hstartPos : 0 < S.hc.opening_slot m := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_two hmPos)
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  exact (protectedVoteSlot_of_coreHeads S adm.toNamedAdmissibleCore
    hstartPos hhor (by
      intro v hv
      simpa only [Protocol.voteDutyHead, hheads v hv] using
        (Block.preceq_self P.erase))).cone

#print axioms honestProposal_openingVoteCone_after_SG_healing_named_of_openingProposer



theorem honestProposal_voterHeadAt_eq_after_SG_healing_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {m : Round}
    (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m)
    (hhor : Protocol.vote_time S.E (S.hc.opening_slot m) ≤ rho.horizon)
    (hcarrier : ProposerCarrierAt S rho m)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot m) = some P) :
    ∀ v ∈ rho.honest,
      voterHeadAt S rho v (S.hc.opening_slot m) = P.erase :=
  honestProposal_voterHeadAt_eq_after_SG_healing_named_of_openingProposer
    S adm hcom hbelow hrec hdelay hpost hm hhor hcarrier.1 hP

#print axioms honestProposal_voterHeadAt_eq_after_SG_healing_named

theorem honestProposal_confirmationReadFacts_after_SG_healing_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {m : Round}
    (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot m) ≤ rho.horizon)
    (hcarrier : ProposerCarrierAt S rho m)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot m) = some P) :
    ∀ v ∈ rho.honest,
      namedConfirmationAnchor S
          (confirmationInputRead S rho v (S.hc.opening_slot m)) ⪯ P.erase ∧
        P.erase ∈
          confTree (confirmationInputRead S rho v
            (S.hc.opening_slot m)).st.core :=
  honestProposal_confirmationReadFacts_after_SG_healing_named_of_openingProposer
    S adm hcom hbelow hrec hdelay hpost hm hhor hcarrier.1 hP

#print axioms honestProposal_confirmationReadFacts_after_SG_healing_named

theorem honestProposal_openingVoteCone_after_SG_healing_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {rGST gap : Round} {m : Round}
    (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m)
    (hcarrier : ProposerCarrierAt S rho m)
    (hhor : Protocol.vote_time S.E (S.hc.opening_slot m) ≤ rho.horizon)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot m) = some P)
    (hheads : ∀ v ∈ rho.honest,
      voterHeadAt S rho v (S.hc.opening_slot m) = P.erase) :
    NamedHonestVotesCone S rho (S.hc.opening_slot m)
      (fun X => Block.Preceq P.erase X) :=
  honestProposal_openingVoteCone_after_SG_healing_named_of_openingProposer
    S adm hcom hm hcarrier.1 hhor hP hheads

#print axioms honestProposal_openingVoteCone_after_SG_healing_named

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
