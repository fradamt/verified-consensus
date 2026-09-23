module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.LayerAHistoryIndices
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ConfirmationQueryIdxEmitted
public import DecoupledConsensusProofs.Execution.IdxDriverHelpers
public import DecoupledConsensusInternal.Definitions.NamedOutageEntry
public import DecoupledConsensusInternal.Definitions.NamedStableChainOutage
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.WeakBootstrapJoin
public import DecoupledConsensusProofs.Objects.WeakLiveConfirmationCore
public import DecoupledConsensusProofs.Protocol.Grades.BoundedSelectionChain
public import DecoupledConsensusProofs.Protocol.Grades.Q31_actionSGBlock_tiers

@[expose] public section

/-!
# Bounded confirmation-chain consequences

This module proves the action-source and live-selection bounds before the
healthy-prefix cutoff. It then derives compatibility of honest selections and
the emitted confirmation-index query. The bounds use the protected-vote-slot
fold as an explicit input. The action-source argument obtains honest-weight
majority from a covered positive round; a cap before round one's G2 domain
does not by itself supply that majority.
-/



namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Internal Execution Internal.NamedOutageEntry
open Internal.NamedOutageEntry.History
open DecoupledConsensusModel.Protocol
open Proofs.HealingSurface Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

set_option maxHeartbeats 400000 in
theorem actionSources_preceq_voteDutyHead_before_of_T1
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hroundOne : domain S.E S.hc 1 .g2 ≤ b0)
    (hT1 : ∀ d : Slot, 1 ≤ d → Protocol.vote_time S.E d + S.E.Δ ≤ b0 →
      Proofs.HealingSurface.ProtectedVoteSlot S rho d Block.genesis ∧
      (∀ q : Slot, q < d → ∀ w ∈ rho.honest, ∀ B,
        GenuineConfirmationWith
          (NamedProfile.gradeContract
            (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
          S.E S.hc (Proofs.Optimistic.confStore S rho w q) q B →
          Proofs.HealingSurface.ProtectedVoteSlot S rho d B))
    {d : Slot} (hd : 1 ≤ d)
    (hcap : Protocol.vote_time S.E d + S.E.Δ ≤ b0)
    {x : V} (hx : x ∈ rho.honest) :
    ∀ r, S.a r < Protocol.vote_time S.E (d + 1) →
      (∀ w ∈ rho.honest,
        rho.emits S w (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
          Block.Preceq (actionSGBlockAt S rho w r) (voteDutyHead S rho x d)) ∧
      (∀ w ∈ rho.honest,
        Block.Preceq (Protocol.get_fg_root (actionStoreAt S rho w r).toHealing.toFG)
          (voteDutyHead S rho x d) ∧
        ∀ T, fgConfirmationWitness S (actionStoreAt S rho w r) = some T →
          Block.Preceq T (voteDutyHead S rho x d)) := by
  have hcapHor : b0 ≤ rho.horizon :=
    hexec.interval.2.1.trans hexec.interval.2.2
  have hroundOneNonneg : 0 ≤ domain S.E S.hc 1 .g2 :=
    (Proofs.HealingLemmas.a_nonneg S 0).trans
      (action_le_domain S S.hc.R_ge_three (by decide))
  have hmajority : HonestWeightMajority S rho.honest := by
    apply Proofs.HealingSurface.WeakSG.honestWeightMajority_of_awakeWindowMajority S
    exact hsleep 1 (by decide)
      (Or.inr ⟨.g2, hroundOneNonneg, hroundOne.trans hcapHor⟩)
  have hprior := (hT1 d hd hcap).2
  have hactionCap : ∀ r, S.a r < Protocol.vote_time S.E (d + 1) →
      S.a r ≤ b0 := by
    intro r ht
    have hopenNext := Proofs.HealingSurface.openingNext_le_of_action_before_nextVote S ht
    have hopen : S.hc.opening_slot r ≤ d - 1 :=
      Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hopenNext)
    have htime : S.a r ≤ Protocol.confirmation_time S.E (d - 1) := by
      rw [Setup.a, Protocol.a_eq_confirmation_time]
      rw [Protocol.confirmation_time_eq_support_cutoff_succ,
        Protocol.confirmation_time_eq_support_cutoff_succ]
      exact support_cutoff_mono S.E (Nat.add_le_add_right hopen 1)
    apply htime.trans
    rw [← vote_time_succ_add_delta_eq_confirmation_time S.E (d - 1)]
    simpa only [Nat.sub_add_cancel hd] using hcap
  have hsources :=
    Proofs.HealingSurface.WeakJoint.actionSources_preceq_of_priorConfirmations_and_historyCut_of_delivery
      S hexec.core hexec.healthy hcapHor hmajority
      (base := 0) (cut := 0) (s := d) (D := voteDutyHead S rho x d)
      (Nat.zero_le _)
      (by
        intro r hr hold ht w hw hemit
        exact False.elim (Nat.not_lt_zero _ hold))
      (by
        intro q hq hqd w hw B hB
        exact (hprior q hqd w hw B hB).heads x hx)
      (by
        intro r hr ht w hw C a
        dsimp only
        intro hC hJ ha hemit hold hpair hT
        exact False.elim (Nat.not_lt_zero _ hold))
      (by
        intro r hr hrpos ht
        apply hsleep r hrpos
        exact Or.inl ⟨Proofs.HealingLemmas.a_nonneg S r,
          (hactionCap r ht).trans hcapHor⟩)
      (by
        intro r hr hrpos ht p
        have hp : domain S.E S.hc r p ≤ domain S.E S.hc r .g0 := by
          have hDelta := S.E.Δ_pos
          cases p <;> unfold domain Phase.domainOffset <;> linarith
        have hdomainAction : domain S.E S.hc r p ≤ S.a r := hp.trans (by
            rw [Proofs.HealingSurface.domain_g0_eq_Γ_1]
            exact (Proofs.HealingLemmas.Γ_1_lt_Γ_2 S.hc S.E.Δ_pos r).le.trans
              (Proofs.HealingSurface.Γ_2_le_a S.hc S.E.Δ_pos r))
        exact hdomainAction.trans (hactionCap r ht))
  intro r ht
  have hr := hsources r (Nat.zero_le _) ht
  exact ⟨hr.1, hr.2 (Nat.zero_le _)⟩

#print axioms actionSources_preceq_voteDutyHead_before_of_T1


set_option maxHeartbeats 400000 in
theorem liveConfirmedSelection_preceq_voteDutyHead_before_of_T1
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hroundOne : domain S.E S.hc 1 .g2 ≤ b0)
    (hT1 : ∀ d : Slot, 1 ≤ d → Protocol.vote_time S.E d + S.E.Δ ≤ b0 →
      Proofs.HealingSurface.ProtectedVoteSlot S rho d Block.genesis ∧
      (∀ q : Slot, q < d → ∀ w ∈ rho.honest, ∀ B,
        GenuineConfirmationWith
          (NamedProfile.gradeContract
            (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
          S.E S.hc (Proofs.Optimistic.confStore S rho w q) q B →
          Proofs.HealingSurface.ProtectedVoteSlot S rho d B))
    {q d : Slot} (hqd : q < d)
    (hcap : Protocol.vote_time S.E d + S.E.Δ ≤ b0)
    {w x : V} (hw : w ∈ rho.honest) (hx : x ∈ rho.honest) :
    Block.Preceq
      (Protocol.update_confirmation_with
        (NamedProfile.gradeContract
          (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho w q) q).live_confirmed
      (voteDutyHead S rho x d) := by
  have hd : 1 ≤ d := (Nat.succ_le_succ (Nat.zero_le q)).trans
    (Nat.succ_le_of_lt hqd)
  let contract := NamedProfile.gradeContract
    (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache
  by_cases hg : confEligible S.E (confStore S rho w q) q
      (confWalkWith contract S.E S.hc (confStore S rho w q) q) = true
  · exact ((hT1 d hd hcap).2 q hqd w hw _ ⟨rfl, hg⟩).heads x hx
  · rw [update_confirmation_with_live_confirmed, if_neg hg]
    have hcapHor : b0 ≤ rho.horizon :=
      hexec.interval.2.1.trans hexec.interval.2.2
    have hroundOneNonneg : 0 ≤ domain S.E S.hc 1 .g2 :=
      (Proofs.HealingLemmas.a_nonneg S 0).trans
        (action_le_domain S S.hc.R_ge_three (by decide))
    have hmajority : HonestWeightMajority S rho.honest := by
      apply Proofs.HealingSurface.WeakSG.honestWeightMajority_of_awakeWindowMajority S
      exact hsleep 1 (by decide)
        (Or.inr ⟨.g2, hroundOneNonneg, hroundOne.trans hcapHor⟩)
    have hconfQCap : Protocol.confirmation_time S.E q ≤ b0 := by
      rw [← vote_time_succ_add_delta_eq_confirmation_time S.E q]
      exact (Int.add_le_add_right
        (vote_time_mono_slots S.E (Nat.succ_le_of_lt hqd)) S.E.Δ).trans hcap
    have hprior := (hT1 d hd hcap).2
    have hsources :=
      Proofs.HealingSurface.WeakJoint.actionSources_preceq_of_priorConfirmations_and_historyCut_of_delivery
        S hexec.core hexec.healthy hcapHor hmajority
        (base := 0) (cut := 0) (s := q + 1) (D := voteDutyHead S rho x d)
        (Nat.zero_le _)
        (by
          intro r hr hold ht w hw hemit
          exact False.elim (Nat.not_lt_zero _ hold))
        (by
          intro e he heq w hw B hB
          have hed : e < d := heq.trans_le hqd
          exact (hprior e hed w hw B hB).heads x hx)
        (by
          intro r hr ht w hw C a
          dsimp only
          intro hC hJ ha hemit hold hpair hT
          exact False.elim (Nat.not_lt_zero _ hold))
        (by
          intro r hr hrpos ht
          apply hsleep r hrpos
          apply Or.inl
          refine ⟨Proofs.HealingLemmas.a_nonneg S r, ?_⟩
          have hopenNext := Proofs.HealingSurface.openingNext_le_of_action_before_nextVote S ht
          have hopen : S.hc.opening_slot r ≤ q :=
            Nat.le_of_succ_le_succ hopenNext
          have htime : S.a r ≤ Protocol.confirmation_time S.E q := by
            rw [Setup.a, Protocol.a_eq_confirmation_time]
            rw [Protocol.confirmation_time_eq_support_cutoff_succ,
              Protocol.confirmation_time_eq_support_cutoff_succ]
            exact support_cutoff_mono S.E (Nat.add_le_add_right hopen 1)
          exact htime.trans (hconfQCap.trans hcapHor))
        (by
          intro r hr hrpos ht p
          have hopenNext := Proofs.HealingSurface.openingNext_le_of_action_before_nextVote S ht
          have hopen : S.hc.opening_slot r ≤ q :=
            Nat.le_of_succ_le_succ hopenNext
          have htime : S.a r ≤ Protocol.confirmation_time S.E q := by
            rw [Setup.a, Protocol.a_eq_confirmation_time]
            rw [Protocol.confirmation_time_eq_support_cutoff_succ,
              Protocol.confirmation_time_eq_support_cutoff_succ]
            exact support_cutoff_mono S.E (Nat.add_le_add_right hopen 1)
          have hp : domain S.E S.hc r p ≤ domain S.E S.hc r .g0 := by
            have hDelta := S.E.Δ_pos
            cases p <;> unfold domain Phase.domainOffset <;> linarith
          have hdomainAction : domain S.E S.hc r p ≤ S.a r := hp.trans (by
            rw [Proofs.HealingSurface.domain_g0_eq_Γ_1]
            exact (Proofs.HealingLemmas.Γ_1_lt_Γ_2 S.hc S.E.Δ_pos r).le.trans
              (Proofs.HealingSurface.Γ_2_le_a S.hc S.E.Δ_pos r))
          exact hdomainAction.trans (htime.trans hconfQCap))
    have hroot : Block.Preceq
        (Protocol.get_fg_root
          (Run.storeBeforeTime S rho w
            (Protocol.confirmation_time S.E q)).toHealing.toFG)
        (voteDutyHead S rho x d) := by
      rcases Proofs.HealingSurface.WeakFG.fgRoot_confirmationWitness_at_read
          S hexec.core hmajority hw (Protocol.confirmation_time S.E q) with
        hgen | ⟨C, hC, hJ, a, ta, ha, hemit, ht, hheight, hT⟩
      · rw [hgen]
        exact Protocol.preceq_genesis _
      · have hat : S.a a.round < Protocol.vote_time S.E (q + 1 + 1) := by
          have htime : ta = S.a a.round := (emits_attest_shape S hemit).2
          rw [← htime]
          apply ht.trans
          have hnext : Protocol.vote_time S.E (q + 1 + 1) =
              Protocol.vote_time S.E (q + 1) + 4 * S.E.Δ := by
            unfold Protocol.vote_time Env.t slotStart
            push_cast
            ring
          rw [← vote_time_succ_add_delta_eq_confirmation_time S.E q, hnext]
          have harith : ∀ a z : Int, 0 < z → a + z < a + 4 * z := by
            intro a z hz
            omega
          exact harith _ _ S.E.Δ_pos
        exact ((hsources a.round (Nat.zero_le _) hat).2
          (Nat.zero_le _) a.val_index ha).2 _ hT
    simpa only [contract, confRoot, confStore, tickStore] using hroot

#print axioms liveConfirmedSelection_preceq_voteDutyHead_before_of_T1

set_option maxHeartbeats 400000 in
theorem honestSelectionsFormChain_before_of_T1
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hroundOne : domain S.E S.hc 1 .g2 ≤ b0)
    (hT1 : ∀ d : Slot, 1 ≤ d → Protocol.vote_time S.E d + S.E.Δ ≤ b0 →
      Proofs.HealingSurface.ProtectedVoteSlot S rho d Block.genesis ∧
      (∀ q : Slot, q < d → ∀ w ∈ rho.honest, ∀ B,
        GenuineConfirmationWith
          (NamedProfile.gradeContract
            (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
          S.E S.hc (Proofs.Optimistic.confStore S rho w q) q B →
          Proofs.HealingSurface.ProtectedVoteSlot S rho d B)) :
    ∀ v ∈ rho.honest, ∀ i C,
      ConfirmationSelectionAt S rho v i C → i < boundaryIdx rho b0 →
      ∀ w ∈ rho.honest, ∀ j D,
        ConfirmationSelectionAt S rho w j D → j < boundaryIdx rho b0 →
        Block.compatible C D = true := by
  have hnormalize : ∀ {v : V} {i : Nat} {C : Block V},
      ConfirmationSelectionAt S rho v i C →
      ∃ q : Slot,
        rho.events[i]? = some
          (Event.tick v (Protocol.confirmation_time S.E q)) ∧
        (Protocol.update_confirmation_with
          (NamedProfile.gradeContract
            (Internal.NamedRecoveryRead.confirmationInputRead S rho v q).cache)
          S.E S.hc (confStore S rho v q) q).live_confirmed = C := by
    intro v i C hsel
    rcases hsel with ⟨time, hi, hpos, htime, hC⟩
    let k := S.E.slotOf time
    let q := k - 1
    have hkpos : 0 < k := by simpa only [k] using hpos
    have hk : q + 1 = k := by
      dsimp only [q, k]
      exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hkpos))
    have hconfirmation : time = Protocol.confirmation_time S.E q := by
      rw [Protocol.confirmation_time_eq_support_cutoff_succ S.E q, hk]
      exact htime
    have hstate := Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
      S hexec.core.toNamedScheduleWellFormed hi
    have hC' : confirmationWrite S
        (Run.stateBeforeTime S rho time v) time = C := by
      change confirmationWrite S (Run.stateBefore S rho i v) time = C at hC
      rw [hstate] at hC
      exact hC
    refine ⟨q, by simpa only [hconfirmation] using hi, ?_⟩
    rw [hconfirmation] at hC'
    rw [Proofs.Optimistic.confStore_eq_confirmationInputRead]
    change (Protocol.NamedDuties.update_confirmation_with
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v q).cache)
      S.E S.hc (Internal.NamedRecoveryRead.confirmationInputRead S rho v q).st q).core.live_confirmed = C
    simpa only [confirmationWrite,
      Internal.NamedRecoveryRead.confirmationInputRead,
      NamedActionReads.confirmationReadAt,
      Proofs.Optimistic.slotOf_confirmation_time, Nat.add_sub_cancel,
      Protocol.NamedStore.live_confirmed,
      Protocol.NamedDuties.update_confirmation_with] using hC'
  intro v hv i C hC hi w hw j D hD hj
  obtain ⟨q, hqi, hqC⟩ := hnormalize hC
  obtain ⟨r, hrj, hrD⟩ := hnormalize hD
  have hqCap : Protocol.confirmation_time S.E q ≤ b0 := by
    have h := NamedOutageHistory.IdxDriverHelpers.time_le_of_lt_boundaryIdx
      rho hexec.core.sorted hqi hi
    simpa only [NamedEvent.time] using h
  have hrCap : Protocol.confirmation_time S.E r ≤ b0 := by
    have h := NamedOutageHistory.IdxDriverHelpers.time_le_of_lt_boundaryIdx
      rho hexec.core.sorted hrj hj
    simpa only [NamedEvent.time] using h
  have hmaxCap : Protocol.confirmation_time S.E (max q r) ≤ b0 := by
    rcases le_total q r with hqr | hrq
    · simpa only [max_eq_right hqr] using hrCap
    · simpa only [max_eq_left hrq] using hqCap
  have hheadCap : Protocol.vote_time S.E (max q r + 1) + S.E.Δ ≤ b0 := by
    simpa only [vote_time_succ_add_delta_eq_confirmation_time] using hmaxCap
  have hleft := liveConfirmedSelection_preceq_voteDutyHead_before_of_T1
    S rho b0 b1 hexec hcom hsleep hroundOne hT1
    (q := q) (d := max q r + 1)
    (Nat.lt_succ_of_le (Nat.le_max_left q r)) hheadCap hv hv
  have hright := liveConfirmedSelection_preceq_voteDutyHead_before_of_T1
    S rho b0 b1 hexec hcom hsleep hroundOne hT1
    (q := r) (d := max q r + 1)
    (Nat.lt_succ_of_le (Nat.le_max_right q r)) hheadCap hw hv
  rw [hqC] at hleft
  rw [hrD] at hright
  exact Block.compatible_of_preceq_common hleft hright

#print axioms honestSelectionsFormChain_before_of_T1

/- The computed SG carrier is comparable with the live value written by the
same prepared action read. No emission is needed: this is a read-local
selector fact. -/


set_option maxHeartbeats 400000 in
theorem namedConfirmationIdxQueryEmitted_of_healthyPrefix_of_T1
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hroundOne : domain S.E S.hc 1 .g2 ≤ b0)
    (hT1 : ∀ d : Slot, 1 ≤ d → Protocol.vote_time S.E d + S.E.Δ ≤ b0 →
      Proofs.HealingSurface.ProtectedVoteSlot S rho d Block.genesis ∧
      (∀ q : Slot, q < d → ∀ w ∈ rho.honest, ∀ B,
        GenuineConfirmationWith
          (NamedProfile.gradeContract
            (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
          S.E S.hc (Proofs.Optimistic.confStore S rho w q) q B →
          Proofs.HealingSurface.ProtectedVoteSlot S rho d B)) :
    NamedConfirmationIdxQueryEmitted S rho b0 := by
  have hgenPrec : ∀ B : NamedBlock V, NamedBlock.Preceq .genesis B := by
    intro B
    induction B with
    | genesis => exact Proofs.NamedAncestry.named_self _
    | node parent s root votes support rows proposer ih =>
        exact Proofs.NamedAncestry.named_extend s root votes support rows proposer ih
  have hcapHor : b0 ≤ rho.horizon :=
    hexec.interval.2.1.trans hexec.interval.2.2
  have hroundOneNonneg : 0 ≤ domain S.E S.hc 1 .g2 :=
    (Proofs.HealingLemmas.a_nonneg S 0).trans
      (action_le_domain S S.hc.R_ge_three (by decide))
  have hmajority : HonestWeightMajority S rho.honest := by
    apply Proofs.HealingSurface.WeakSG.honestWeightMajority_of_awakeWindowMajority S
    exact hsleep 1 (by decide)
      (Or.inr ⟨.g2, hroundOneNonneg, hroundOne.trans hcapHor⟩)
  intro n C hhistory i v r hv hi hin hcap
  subst i
  let read := actionReadFrom S (NamedRun.stateBefore S rho n v) r
  have hinv := Proofs.NamedOutageInputs.action_read_invariant S rho n v r
  have hlive : read.st.core.live_confirmed ∈ read.st.core.T := hinv.2.1
  have hliveImage : read.st.core.live_confirmed ∈
      read.st.bodies.image NamedBlock.erase := by
    rw [← hinv.1.1.1]
    exact hlive
  obtain ⟨L, hLbody, hLe⟩ := Finset.mem_image.mp hliveImage
  have hLbefore : L ∈ (NamedRun.stateBefore S rho n v).st.bodies := by
    simpa only [read, NamedActionReads.actionReadFrom] using hLbody
  have hLrun : NamedRun.blockInRun S rho L :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hv hLbefore
  have hselection : ∀ (j : Nat) (w : V) (q : Round),
      rho.events[j]? = some (.tick w (S.a q)) →
      ConfirmationSelectionAt S rho w j
        (actionReadFrom S
          (NamedRun.stateBefore S rho j w) q).st.core.live_confirmed := by
    intro j w q hj
    refine ⟨S.a q, hj, ?_, ?_, ?_⟩
    · rw [Setup.a, Protocol.a_eq_support_cutoff_succ,
        Proofs.Optimistic.slotOf_support_cutoff]
      exact Nat.zero_lt_succ _
    · rw [Setup.a, Protocol.a_eq_support_cutoff_succ,
        Proofs.Optimistic.slotOf_support_cutoff]
    · rfl
  have hLsel : ConfirmationSelectionAt S rho v n L.erase := by
    simpa only [hLe] using hselection n v r hi
  have htimeOfKey : ∀ {e f : NamedEvent V}, e.key ≤ f.key → e.time ≤ f.time := by
    intro e f hkey
    rcases Prod.Lex.le_iff.mp hkey with hlt | ⟨heq, hphase⟩
    · exact hlt.le
    · exact heq.le
  have hprefix : PrefixThrough rho (n + 1) b0 := by
    constructor
    · exact Nat.succ_le_of_lt (List.getElem?_eq_some_iff.mp hi).1
    · intro k hk e he
      have hkn : k ≤ n := Nat.le_of_lt_succ hk
      rcases lt_or_eq_of_le hkn with hknlt | rfl
      · obtain ⟨hkLen, hkGet⟩ := List.getElem?_eq_some_iff.mp he
        obtain ⟨hnLen, hnGet⟩ := List.getElem?_eq_some_iff.mp hi
        have hkey := (List.pairwise_iff_getElem.mp hexec.core.sorted)
          k n hkLen hnLen hknlt
        rw [hkGet, hnGet] at hkey
        exact (htimeOfKey hkey).trans hcap
      · have heq : e = .tick v (S.a r) := Option.some.inj (he.symm.trans hi)
        subst e
        simpa only [NamedEvent.time] using hcap
  have hnBoundary : n < boundaryIdx rho b0 :=
    (Nat.lt_succ_self n).trans_le
      (prefixThrough_le_boundaryIdx rho hprefix)
  have hcompat : NamedBlock.compatible C L = true := by
    rcases hhistory.2 with hgen |
        ⟨j, w, q, hjn, hw, hj, hCbody, hsource⟩
    · subst C
      simp only [NamedBlock.compatible, Bool.or_eq_true]
      exact Or.inl (hgenPrec L)
    · rcases hsource with hliveC | ⟨hsgC, hemit⟩
      · have hCsel : ConfirmationSelectionAt S rho w j C.erase := by
          simpa only [hliveC] using hselection j w q hj
        have hjBoundary : j < boundaryIdx rho b0 := hjn.trans_lt hnBoundary
        have hraw := honestSelectionsFormChain_before_of_T1
          S rho b0 b1 hexec hcom hsleep hroundOne hT1
          w hw j C.erase hCsel hjBoundary v hv n L.erase hLsel hnBoundary
        simp only [Block.compatible, Bool.or_eq_true] at hraw
        simp only [NamedBlock.compatible, Bool.or_eq_true]
        rcases hraw with hCL | hLC
        · exact Or.inl
            (NamedOutageHistory.JointHistoryProducersTime.named_of_erase_preceq
              S rho hexec.core hhistory.1.1.1 hLrun hCL)
        · exact Or.inr
            (NamedOutageHistory.JointHistoryProducersTime.named_of_erase_preceq
              S rho hexec.core hLrun hhistory.1.1.1 hLC)
      · have hqCap : S.a q ≤ b0 := by
          have h := NamedOutageHistory.IdxDriverHelpers.time_le_of_lt_boundaryIdx
            rho hexec.core.sorted hj (hjn.trans_lt hnBoundary)
          simpa only [NamedEvent.time] using h
        let qs := S.hc.opening_slot q
        let rs := S.hc.opening_slot r
        let d := max qs rs + 1
        have hqsCap : Protocol.confirmation_time S.E qs ≤ b0 := by
          simpa only [qs, Setup.a, Protocol.a_eq_confirmation_time] using hqCap
        have hrsCap : Protocol.confirmation_time S.E rs ≤ b0 := by
          simpa only [rs, Setup.a, Protocol.a_eq_confirmation_time] using hcap
        have hmaxCap : Protocol.confirmation_time S.E (max qs rs) ≤ b0 := by
          rcases le_total qs rs with hqr | hrq
          · simpa only [max_eq_right hqr] using hrsCap
          · simpa only [max_eq_left hrq] using hqsCap
        have hheadCap : Protocol.vote_time S.E d + S.E.Δ ≤ b0 := by
          simpa only [d, vote_time_succ_add_delta_eq_confirmation_time] using hmaxCap
        have hd : 1 ≤ d := Nat.succ_le_succ (Nat.zero_le _)
        have hqBefore : S.a q < Protocol.vote_time S.E (d + 1) := by
          rw [Setup.a, Protocol.a_eq_confirmation_time]
          exact Proofs.HealingSurface.confirmationTime_lt_nextVote_of_lt S.E
            (show qs < d from Nat.lt_succ_of_le (Nat.le_max_left qs rs))
        have hChead :=
          (actionSources_preceq_voteDutyHead_before_of_T1
            S rho b0 b1 hexec hcom hsleep hroundOne hT1 hd hheadCap hv
            q hqBefore).1 w hw hemit
        have hstateJ := Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
          S hexec.core.toNamedScheduleWellFormed hj
        change NamedRun.stateBefore S rho j w =
          NamedRun.stateBeforeTime S rho (S.a q) w at hstateJ
        have hreadJ : actionReadFrom S (NamedRun.stateBefore S rho j w) q =
            Proofs.HealingSurface.actionReadAt S rho w q := by
          simp only [Proofs.HealingSurface.actionReadAt]
          rw [hstateJ]
          rfl
        have hsgEq : C.erase = actionSGBlockAt S rho w q := by
          rw [hreadJ] at hsgC
          unfold actionSGBlockAt
          dsimp only
          have hk : S.hc.round_of
              (Proofs.HealingSurface.actionReadAt S rho w q).st.core.toHealing.s = q := by
            simpa only [Protocol.Store.toHealing, actionStoreAt] using
              Proofs.HealingSurface.actionStoreAt_round S rho w q
          rw [hk]
          exact hsgC
        rw [← hsgEq] at hChead
        have hrlt : rs < d := Nat.lt_succ_of_le (Nat.le_max_right qs rs)
        have hLhead0 := liveConfirmedSelection_preceq_voteDutyHead_before_of_T1
          S rho b0 b1 hexec hcom hsleep hroundOne hT1 hrlt hheadCap hv hv
        have hstate := Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
          S hexec.core.toNamedScheduleWellFormed hi
        change NamedRun.stateBefore S rho n v =
          NamedRun.stateBeforeTime S rho (S.a r) v at hstate
        have hreadEq : read = actionStoreAt S rho v r := by
          simp only [read, actionStoreAt, Proofs.HealingSurface.actionReadAt]
          rw [hstate]
          rfl
        have hactionEq :=
          Proofs.HealingSurface.actionStoreAt_eq_update_confirmation_openingConfStore
            S rho v r
        have hLhead : Block.Preceq L.erase (voteDutyHead S rho v d) := by
          rw [hreadEq] at hLe
          rw [hactionEq] at hLe
          simpa only [rs, Internal.NamedRecoveryRead.confirmationInputRead,
            Setup.a, Protocol.a_eq_confirmation_time,
            Proofs.Optimistic.confStore_eq_confirmationInputRead] using
              (hLe.symm ▸ hLhead0)
        have hraw : Block.compatible C.erase L.erase = true :=
          Block.compatible_of_preceq_common hChead hLhead
        simp only [Block.compatible, Bool.or_eq_true] at hraw
        simp only [NamedBlock.compatible, Bool.or_eq_true]
        rcases hraw with hCL | hLC
        · exact Or.inl
            (NamedOutageHistory.JointHistoryProducersTime.named_of_erase_preceq
              S rho hexec.core hhistory.1.1.1 hLrun hCL)
        · exact Or.inr
            (NamedOutageHistory.JointHistoryProducersTime.named_of_erase_preceq
              S rho hexec.core hLrun hhistory.1.1.1 hLC)
  simp only [NamedBlock.compatible, Bool.or_eq_true] at hcompat
  rcases hcompat with hCL | hLC
  · exact ⟨L, L, hLrun, hCL, Or.inr rfl, hLrun, hLbody, hLe,
      NamedOutageHistory.JointHistoryProducersTime.named_preceq_self L⟩
  · exact ⟨C, L, hhistory.1.1.1,
      NamedOutageHistory.JointHistoryProducersTime.named_preceq_self C,
      Or.inl rfl, hLrun, hLbody, hLe, hLC⟩

#print axioms namedConfirmationIdxQueryEmitted_of_healthyPrefix_of_T1




end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
