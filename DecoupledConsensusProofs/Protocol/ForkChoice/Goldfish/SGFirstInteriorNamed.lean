module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.FGSafetyRootNamed
public import DecoupledConsensusProofs.Protocol.Grades.PreparedFrameAfterDeadline
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FGSafetyFrozenHeadNamed
public import DecoupledConsensusProofs.Protocol.Grades.SGFirstInteriorAnchorNamed
public import DecoupledConsensusProofs.Execution.RecoveryActionLiveSourceSplit
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedEntryCanonical
public import DecoupledConsensusProofs.Protocol.Grades.SeedRelativeGrade

@[expose] public section

/-!
# Prepared first-interior SG safety

This module proves the first-interior SG argument from the three producer
conditions stated in its imports.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface
open Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

private theorem firstInterior_lt_nextOpening (S : Setup V) (r : Round) :
    S.hc.opening_slot r + 1 < S.hc.opening_slot (r + 1) := by
  simpa only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul] using
    Nat.add_lt_add_left (Nat.lt_of_succ_le S.hc.R_ge_two) (r * S.hc.R)

private theorem voteTime_lt_nextProposal (E : Env V) (s : Slot) :
    Protocol.vote_time E s < Protocol.proposal_time E (s + 1) := by
  simp only [Protocol.vote_time, Protocol.proposal_time, Env.t, slotStart]
  push_cast
  nlinarith [E.Δ_pos]

private theorem firstInterior_schedule
    (S : Setup V) {rho : Run V} {rGST gap c : Round}
    (hpost : S.E.t_GST ≤ S.a rGST)
    (hc : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ c)
    (hhor : S.a (c + 1) ≤ rho.horizon) :
    S.E.t_GST ≤ Protocol.proposal_time S.E (S.hc.opening_slot (c + 1)) ∧
      S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) <
        Protocol.vote_time S.E (S.hc.opening_slot (c + 1) + 1) ∧
      Protocol.vote_time S.E (S.hc.opening_slot (c + 1) + 1) ≤ rho.horizon := by
  have hGSTdead : rGST ≤ fgSafetyProgressDeadline S rho rGST gap delayExtra := by
    unfold fgSafetyProgressDeadline
    exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
  have hpostc := hpost.trans ((action_strictMono S).monotone (hGSTdead.trans hc))
  have hround : S.hc.round_of (S.hc.opening_slot (c + 1) + 1) = c + 1 :=
    round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc (le_refl _)
      (firstInterior_lt_nextOpening S (c + 1))
  have hcut := Γ_0_le_vote_time_of_round_eq S hround
  refine ⟨(gst_le_Γ_neg1_succ S c hpostc).trans
    (Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos (c + 1)).le, ?_,
    (next_vote_time_lt_action S (c + 1)).le.trans hhor⟩
  exact (((action_strictMono S).monotone hc).trans
    (a_le_Γ_neg1_succ S.hc S.E.Δ_pos c)).trans_lt
    ((Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos (c + 1)).trans_le hcut)

private theorem preceq_voterHeadAt_of_namedNextVoteAdoption
    (S : Setup V) {rho : Run V} {source : Protocol.Store V}
    {s : Slot} {B : Block V} {w : V}
    (heligible : Protocol.voters_count S.E (confLate S.E source s) s <
      2 * Protocol.goldfish_score S.E source.T
        (confVotes S.E source s) (confVotes S.E source s) s B)
    (hadopt : NamedNextVoteAdoption S rho source s B w) :
    Block.Preceq B (voterHeadAt S rho w (s + 1)) := by
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
  change Block.Preceq B
    (Protocol.get_head_in_tree_with_layer
      (NamedProfile.gradeContract read.cache) S.E S.hc st.toHealing
      tree votes support (st.s - 1))
  rw [Proofs.Optimistic.get_head_in_tree_split_with, hprev]
  simpa only [Protocol.Store.toHealing, read, st] using
    (Protocol.goldfish_fork_choice_captures_of_confirmation
      S.E st.σ st.h_max source.T st.T tree st.s
      (confEarly S.E source s) (confLate S.E source s)
      (confVotes S.E source s) votes support s
      (confNumerator S.E source s) hadopt.transport heligible
        hadopt.support_subset hadopt.anchor hadopt.path)

private theorem ancestorConfirmation_eligible_with_of_preceq
    (E : Env V) (hc : Protocol.HealConfig) (source : Protocol.Store V)
    (s : Slot) {T C : Block V} {contract : Protocol.GradeContract V}
    (hTC : Block.Preceq T C)
    (hC : GenuineConfirmationWith contract E hc source s C) :
    Protocol.voters_count E (confLate E source s) s <
      2 * Protocol.goldfish_score E source.T
        (confVotes E source s) (confVotes E source s) s T := by
  have hN := confNumerator E source s
  have hsupport := supporters_mono E source.T
    (confVotes E source s) (confVotes E source s) s hTC
  have hcard := Finset.card_le_card hsupport
  have hCg : GenuineConfirmation E hc source s C (contract := contract) :=
    ⟨hC.selected, hC.genuine⟩
  have hCeligible := hCg.eligible
  rw [hN.score_eq_supporters] at hCeligible ⊢
  exact lt_of_lt_of_le hCeligible (Nat.mul_le_mul_left 2 hcard)


/-- The prepared genuine-confirmation selector case, closed over the available
post-deadline producers. The anchor producer's extra delivery horizon is
discharged at the first interior slot. -/
theorem actionSGBlock_preceq_firstInteriorHead_of_genuine_after_GST_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {c : Round} (hc : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ c)
    (hhor : S.a (c + 1) ≤ rho.horizon)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) {C : Block V}
    (hC : GenuineConfirmationWith
      (NamedProfile.gradeContract
        (NamedActionReads.confirmationReadAt S rho v (S.a (c + 1))).cache)
      S.E S.hc
      (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot (c + 1)))
      (S.hc.opening_slot (c + 1)) C)
    (hBC : Block.Preceq (actionSGBlockAt S rho v (c + 1)) C) :
    Block.Preceq (actionSGBlockAt S rho v (c + 1))
      (voterHeadAt S rho w (S.hc.opening_slot (c + 1) + 1)) := by
  let s := S.hc.opening_slot (c + 1)
  let B := actionSGBlockAt S rho v (c + 1)
  obtain ⟨hpostOpening, -, hvoteHor⟩ :=
    firstInterior_schedule S hpost hc hhor
  have hsourceHor : Protocol.confirmation_time S.E s ≤ rho.horizon := by
    simpa only [s, opening_confirmation_time_eq_action] using hhor
  have hspos : 0 < s := by
    unfold s Protocol.HealConfig.opening_slot
    exact Nat.mul_pos (Nat.succ_pos c)
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E s :=
    hpostOpening.trans (proposal_time_lt_vote_time S.E s).le
  have hCg : GenuineConfirmation
      (contract := NamedProfile.gradeContract
        (NamedActionReads.confirmationReadAt S rho v (S.a (c + 1))).cache)
      S.E S.hc (Proofs.Optimistic.confStore S rho v s) s C :=
    ⟨hC.selected, hC.genuine⟩
  obtain ⟨u, hu, -, hCu⟩ :=
    WeakGoldfish.genuineConfirmation_exists_honestVoteSupporter_after_gst
      S adm.toNamedAdmissibleCore hcom hv hspos hpostVote hsourceHor hC
  have hBprev : Block.Preceq B (voterHeadAt S rho u s) :=
    Block.preceq_trans hBC hCu
  have hanchorCompat : Block.compatible
      (voterAnchorAt S rho w (s + 1)) B = true := by
    exact voterAnchorAt_firstInterior_compatible_actionSGBlock_after_GST
      S adm hcom hbelow hrec hdelay hpost hc hhor
      (le_refl _) (firstInterior_lt_nextOpening S (c + 1)) hvoteHor
      (firstInterior_vote_add_delta_le_horizon S hhor) hv hw
  rcases (show Block.Preceq (voterAnchorAt S rho w (s + 1)) B ∨
      Block.Preceq B (voterAnchorAt S rho w (s + 1)) by
    simpa only [Block.compatible, Bool.or_eq_true] using hanchorCompat) with
    hanchorB | hBanchor
  · have hrootB : Block.Preceq
        (Protocol.get_fg_root
          (Internal.NamedRecoveryRead.voteDutyRead S rho w
            (s + 1)).st.core.toHealing.toFG) B :=
      Block.preceq_trans
        (fg_root_preceq_get_sg_root_with_frame
          (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).cache
          S.E S.hc
          (Internal.NamedRecoveryRead.voteDutyRead S rho w
            (s + 1)).st.core.toHealing
          (S.hc.round_of
            (Internal.NamedRecoveryRead.voteDutyRead S rho w
              (s + 1)).st.core.s)) hanchorB
    have hrootBare : Block.Preceq
        (Protocol.get_fg_root
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) B := by
      simpa only [Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore] using hrootB
    have hCprocessed :=
      Protocol.voterProcessedTarget_of_genuineConfirmation_after_gst
        S adm hv hw hpostOpening hsourceHor hCg
          (Block.preceq_trans hrootBare hBC)
    have hBprocessed := WeakGoldfish.ancestorProcessed_of_voterProcessed
      S adm.toNamedAdmissibleCore hw hCprocessed B hBC
    have hBprocessed' : B ∈ Protocol.voter_processed_block_tree S.E
        (Internal.NamedRecoveryRead.voteDutyRead S rho w
          (s + 1)).st.core.toHealing.toFG.toSG.toGoldfishStore (s + 1) := by
      simpa only [Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Proofs.Optimistic.toHealing_slot,
        Proofs.Optimistic.slotOf_vote_time, Run.storeBeforeTime, s] using hBprocessed
    have hsDead : S.hc.opening_slot
        (fgSafetyProgressDeadline S rho rGST gap delayExtra) + 1 ≤ s := by
      unfold s Protocol.HealConfig.opening_slot
      calc
        fgSafetyProgressDeadline S rho rGST gap delayExtra * S.hc.R + 1 ≤
            c * S.hc.R + 1 :=
          Nat.add_le_add_right (Nat.mul_le_mul_right S.hc.R hc) 1
        _ ≤ c * S.hc.R + S.hc.R :=
          Nat.add_le_add_left
            (Nat.succ_le_of_lt
              (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)) _
        _ = (c + 1) * S.hc.R := by
          rw [Nat.add_mul, Nat.one_mul]
    rcases honestPreviousHead_voterCandidateMem_or_preceq_root_after_GST_named
        S adm hcom hbelow hrec hdelay hpost hsDead hvoteHor
        hw hu hBprev hBprocessed' with hcandidate | hBroot
    · have hadopt := nextVoteAdoption_of_recovery_after_gst
        S adm hv hw hpostOpening hsourceHor hrootB hanchorB hcandidate
      exact preceq_voterHeadAt_of_namedNextVoteAdoption S
        (ancestorConfirmation_eligible_with_of_preceq S.E S.hc
          (Proofs.Optimistic.confStore S rho v s) s hBC hC) hadopt
    · exact Block.preceq_trans hBroot
        (fgRoot_preceq_voterHeadAt S rho w (s + 1))
  · exact Block.preceq_trans hBanchor
      (voterAnchorAt_preceq_voterHeadAt S rho w (s + 1))

private theorem actionSGBlock_preceq_firstInteriorHead_after_GST_core
    (hrawPin : ∀
      (S : Setup V) {rho : Run V}, Admissible S rho →
      HonestCommittees S rho.honest → BelowOneThird S rho.honest →
      ∀ {rGST gap : Round}, MultiProposerRecurrence S rho gap →
      TimeoutDelayBound S delayExtra → S.E.t_GST ≤ S.a rGST →
      ∀ {c : Round}, fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ c →
      S.a (c + 1) ≤ rho.horizon →
      ∀ v ∈ rho.honest,
        Internal.PhaseGrades.nodeRawG2 S
          (actionReadAt S rho v (c + 1)) (c + 1))
    (hq2Pin : ∀
      (S : Setup V) {rho : Run V}, Admissible S rho →
      HonestCommittees S rho.honest → BelowOneThird S rho.honest →
      ∀ {rGST gap : Round}, MultiProposerRecurrence S rho gap →
      TimeoutDelayBound S delayExtra → S.E.t_GST ≤ S.a rGST →
      ∀ {c : Round}, fgSafetyProgressDeadline S rho rGST gap delayExtra + 1 ≤ c →
      GradeRoundReady S rho c → S.a c ≤ rho.horizon →
      ∀ {p : V}, p ∈ rho.honest → ∀ {Q : Block V},
      PhaseGrades.nodeQ2 S (actionReadAt S rho p c) c = some Q →
      ∀ {d : Slot}, S.hc.round_of d = c →
      S.hc.opening_slot c + 1 ≤ d →
      Protocol.vote_time S.E d ≤ rho.horizon →
      Protocol.vote_time S.E d ≤ S.a (c + 1) →
      ∀ {w : V}, w ∈ rho.honest →
      Block.Preceq Q
          (Protocol.get_fg_root
            (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.toFG) ∨
        Q ∈ PhaseGrades.filteredTree
          (Internal.NamedRecoveryRead.voteDutyRead S rho w d))
    (hgenuine : ∀
      (S : Setup V) {rho : Run V}, Admissible S rho →
      HonestCommittees S rho.honest → BelowOneThird S rho.honest →
      ∀ {rGST gap : Round}, MultiProposerRecurrence S rho gap →
      TimeoutDelayBound S delayExtra → S.E.t_GST ≤ S.a rGST →
      ∀ {c : Round}, fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ c →
      S.a (c + 1) ≤ rho.horizon →
      ∀ {v w : V}, v ∈ rho.honest → w ∈ rho.honest → ∀ {C : Block V},
      GenuineConfirmationWith
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadAt S rho v (S.a (c + 1))).cache)
        S.E S.hc
        (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot (c + 1)))
        (S.hc.opening_slot (c + 1)) C →
      Block.Preceq (actionSGBlockAt S rho v (c + 1)) C →
      Block.Preceq (actionSGBlockAt S rho v (c + 1))
        (voterHeadAt S rho w (S.hc.opening_slot (c + 1) + 1)))
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {c : Round} (hc : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ c)
    (hhor : S.a (c + 1) ≤ rho.horizon)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) :
    Block.Preceq (actionSGBlockAt S rho v (c + 1))
      (voterHeadAt S rho w (S.hc.opening_slot (c + 1) + 1)) := by
  let d := S.hc.opening_slot (c + 1) + 1
  obtain ⟨-, hdeadlineVote, hvoteHor⟩ := firstInterior_schedule S hpost hc hhor
  have hround : S.hc.round_of d = c + 1 :=
    round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc (le_refl _)
      (firstInterior_lt_nextOpening S (c + 1))
  have hnextFrame : Protocol.vote_time S.E d ≤
      DecoupledConsensusModel.Protocol.opening S.E S.hc (c + 1 + 1) := by
    have hstep : Protocol.proposal_time S.E (d + 1) ≤
        Protocol.proposal_time S.E (S.hc.opening_slot (c + 1 + 1)) :=
      proposal_time_mono S.E
        (Nat.succ_le_of_lt (firstInterior_lt_nextOpening S (c + 1)))
    exact (voteTime_lt_nextProposal S.E d).le.trans hstep
  have hnext : Protocol.vote_time S.E d ≤ S.a (c + 1 + 1) :=
    (next_vote_time_lt_action S (c + 1)).le.trans
      ((action_strictMono S).monotone (Nat.le_succ _))
  have hGSTdead : rGST ≤ fgSafetyProgressDeadline S rho rGST gap delayExtra := by
    unfold fgSafetyProgressDeadline
    exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
  have hpostc := hpost.trans ((action_strictMono S).monotone (hGSTdead.trans hc))
  have hroundDead : rGST + 2 ≤ c + 1 := by
    have hbase : rGST + 1 ≤
        fgSafetyProgressDeadline S rho rGST gap delayExtra := by
      unfold fgSafetyProgressDeadline
      exact Nat.le_add_right _ _
    exact Nat.succ_le_succ (hbase.trans hc)
  have hgstLagged : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ (rGST + 2) :=
    gstLagged_le_Γ_neg1_of_gst_le_a S rGST hpost
  have ready : GradeRoundReady S rho (c + 1) :=
    gradeRoundReady_of_action_horizon S hgstLagged hroundDead hhor
  have hraw := hrawPin S adm hcom hbelow hrec hdelay hpost hc hhor v hv
  have hslotDead : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra) + 1 ≤ d :=
    Nat.add_le_add_right
      (Nat.mul_le_mul_right S.hc.R (hc.trans (Nat.le_succ c))) 1
  have hshor : Protocol.vote_time S.E d + S.E.Δ ≤ rho.horizon := by
    simpa only [d, vote_time_succ_add_delta_eq_confirmation_time,
      opening_confirmation_time_eq_action] using hhor
  have hrootHead := fgRoot_preceq_previousHead_after_GST
    S adm hcom hbelow hrec hdelay hpost
      ((action_strictMono S).monotone (hc.trans (Nat.le_succ c))) hhor
      hslotDead (action_lt_vote_time_two_after S (c + 1)).le hshor hv hw
  rcases actionSGBlockAt_tiers_of_rawG2 S rho v (c + 1) hraw with
    hclear | ⟨Q, hQ, hsg⟩ | hsg
  · rcases actionStoreAt_liveConfirmed_genuine_or_fgRoot S rho v (c + 1) with
      ⟨C, hC, hClive⟩ | ⟨R, hRroot, hRlive⟩
    · exact hgenuine S adm hcom hbelow hrec hdelay hpost hc hhor hv hw hC
        (hClive.symm ▸ hclear.2.1)
    · have hBroot : Block.Preceq (actionSGBlockAt S rho v (c + 1))
          (Protocol.get_fg_root
            (actionStoreAt S rho v (c + 1)).toHealing.toFG) := by
        rw [actionStoreAt_fgRoot_eq_openingConfStore, ← hRroot, hRlive]
        exact hclear.2.1
      apply Block.preceq_trans hBroot
      rw [actionStoreAt_fgRoot_eq_storeBeforeTime]
      exact hrootHead
  · rw [hsg]
    rcases hq2Pin S adm hcom hbelow hrec hdelay hpost
        (Nat.succ_le_succ hc) ready hhor hv hQ hround (le_refl _)
        hvoteHor hnext hw with
      hQroot | hQactive
    · exact Block.preceq_trans hQroot (fgRoot_preceq_voterHeadAt S rho w d)
    · exact preceq_voterHeadAt_of_nodeQ2_activeAtDutyRead
        S adm (slashableBound_of_admissible_belowOneThird S adm hbelow)
          (Nat.succ_pos c) (Nat.le_succ _) hround hnextFrame hvoteHor ready.1
          ready.2 hv hw hQ hQactive
  · rw [hsg]
    change Block.Preceq
      (Protocol.get_fg_root
        (actionStoreAt S rho v (c + 1)).toHealing.toFG)
      (voterHeadAt S rho w d)
    rw [actionStoreAt_fgRoot_eq_storeBeforeTime]
    exact hrootHead


theorem actionSGBlock_preceq_firstInteriorHead_after_GST_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {c : Round} (hc : fgSafetyProgressDeadline S rho rGST gap delayExtra ≤ c)
    (hhor : S.a (c + 1) ≤ rho.horizon)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) :
    Block.Preceq (actionSGBlockAt S rho v (c + 1))
      (voterHeadAt S rho w (S.hc.opening_slot (c + 1) + 1)) := by
  exact actionSGBlock_preceq_firstInteriorHead_after_GST_core
    nodeRawG2_at_action_after_recovery_deadline
    actionQ2_preceq_fgRoot_or_activeAtVoteDuty_after_deadline
    actionSGBlock_preceq_firstInteriorHead_of_genuine_after_GST_named
    S adm hcom hbelow hrec hdelay hpost hc hhor hv hw


#print axioms actionSGBlock_preceq_firstInteriorHead_after_GST_core
#print axioms actionSGBlock_preceq_firstInteriorHead_of_genuine_after_GST_named
#print axioms actionSGBlock_preceq_firstInteriorHead_after_GST_named

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
