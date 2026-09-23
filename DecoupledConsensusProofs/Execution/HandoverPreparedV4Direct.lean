module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.HandoverHeightNamedDirect
public import DecoupledConsensusProofs.Generic.HandoverFGWitnessesNamedClosed
public import DecoupledConsensusProofs.Execution.HandoverPreparedV4
public import DecoupledConsensusProofs.Execution.ProposalConfirmationPreparedLiveNamed
public import DecoupledConsensusProofs.Protocol.Handlers.ProposalConfirmationPreparedLatestNamed
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.SGLifetimeNamed

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Direct prepared V4 handover selector -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Internal.NamedRecoveryRead Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

private theorem directV4_trigger_after_gst_nat {r d l eta n : Nat}
    (hrd : r ≤ d) (hn : d + 2 * l + 1 + eta ≤ n) : r < n := by
  omega

private theorem confirmationTime_mono_directV4
    (E : Env V) {s t : Slot} (hst : s ≤ t) :
    Protocol.confirmation_time E s ≤ Protocol.confirmation_time E t := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ,
    Protocol.confirmation_time_eq_support_cutoff_succ]
  exact support_cutoff_mono E (Nat.add_le_add_right hst 1)

private theorem openingSlot_succ_le_of_lt_directV4
    (S : Setup V) {m n : Round} (h : m < n) :
    S.hc.opening_slot m + 1 ≤ S.hc.opening_slot n := by
  have hnext : S.hc.opening_slot m + 1 < S.hc.opening_slot (m + 1) := by
    simpa only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul] using
      Nat.add_lt_add_left (Nat.lt_of_succ_le S.hc.R_ge_two) (m * S.hc.R)
  exact (Nat.le_of_lt hnext).trans (Nat.mul_le_mul_right S.hc.R h)

/-- The direct recurrence carrier supplies the live-only prepared V4 handover
from the three direct proposal facts. -/
theorem settledBootstrap_of_strong_preparedV4_of_live_pins
    (_of_heads : ∀
      (S : Setup V) {rho : Run V}, Admissible S rho →
      HonestCommittees S rho.honest → BelowOneThird S rho.honest →
      ∀ {rGST gap : Round}, MultiProposerRecurrence S rho gap →
      TimeoutDelayBound S delayExtra → S.E.t_GST ≤ S.a rGST →
      ∀ {m : Round},
      fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m →
      Protocol.vote_time S.E (S.hc.opening_slot m) ≤ rho.horizon →
      ProposerCarrierAt S rho m → ∀ {P : NamedBlock V},
      proposedBlockAt S rho (S.hc.opening_slot m) = some P →
      ∀ v ∈ rho.honest,
        voterHeadAt S rho v (S.hc.opening_slot m) = P.erase)
    (_of_cone : ∀
      (S : Setup V) {rho : Run V}, Admissible S rho →
      HonestCommittees S rho.honest → ∀ {rGST gap m : Round},
      fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ m →
      ProposerCarrierAt S rho m →
      Protocol.vote_time S.E (S.hc.opening_slot m) ≤ rho.horizon →
      ∀ {P : NamedBlock V},
      proposedBlockAt S rho (S.hc.opening_slot m) = some P →
      (∀ v ∈ rho.honest,
        voterHeadAt S rho v (S.hc.opening_slot m) = P.erase) →
      NamedHonestVotesCone S rho (S.hc.opening_slot m)
        (fun X => Block.Preceq P.erase X))
    (_of_confirmationSeed : ∀
      (S : Setup V) {rho : Run V}, Admissible S rho →
      HonestCommittees S rho.honest → BelowOneThird S rho.honest →
      ∀ {rGST gap : Round}, MultiProposerRecurrence S rho gap →
      TimeoutDelayBound S delayExtra → S.E.t_GST ≤ S.a rGST →
      ∀ {m : Round} {P : NamedBlock V},
      fgSafetyProgressDeadline S rho rGST gap delayExtra +
        2 * progressLag' gap delayExtra + 1 + S.hc.η_SG ≤ m →
      ProposerCarrierAt S rho m →
      proposedBlockAt S rho (S.hc.opening_slot m) = some P →
      Protocol.confirmation_time S.E
        (S.hc.opening_slot m) ≤ rho.horizon →
      ∀ v ∈ rho.honest,
        (Protocol.update_confirmation_with
          (NamedProfile.gradeContract
            (confirmationInputRead S rho v (S.hc.opening_slot m)).cache)
          S.E S.hc (confStore S rho v (S.hc.opening_slot m))
          (S.hc.opening_slot m)).live_confirmed = P.erase)
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbot : BelowOneThird S rho.honest)
    {rGST gap : Round} (hdelay : TimeoutDelayBound S delayExtra)
    (hrec : MultiProposerRecurrence S rho gap) (hpost : S.E.t_GST ≤ S.a rGST)
    {n : Round}
    (hn : fgSafetyProgressDeadline S rho rGST gap delayExtra +
      2 * progressLag' gap delayExtra + 1 + S.hc.η_SG ≤ n)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot (n + gap)) ≤ rho.horizon) :
    ∃ m : Round, n ≤ m ∧ m ≤ n + gap ∧ ProposerCarrierAt S rho m ∧
      ∃ P : NamedBlock V,
        proposedBlockAt S rho (S.hc.opening_slot m) = some P ∧
        SettledBootstrapPreparedV4 S rho
          (fgSafetyProgressDeadline S rho rGST gap delayExtra + 1)
          (fgSafetyProgressDeadline S rho rGST gap delayExtra +
            2 * progressLag' gap delayExtra + 1)
          (S.hc.opening_slot m) P
          (honestHMaxAt S rho
            (S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra))) ∧
        honestHMaxAt S rho
            (S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra)) <
          (Protocol.derive_named S.E S.cfg P).h := by
  classical
  let D := fgSafetyProgressDeadline S rho rGST gap delayExtra
  let L := progressLag' gap delayExtra
  let base : Round := D + 2 * L + 1
  have hGSTdead : rGST ≤ D := by
    dsimp only [D]
    unfold fgSafetyProgressDeadline
    exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
  have hGSTtrigger : S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot n) :=
    hpost.trans ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
      (Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt S
        (directV4_trigger_after_gst_nat hGSTdead (by simpa only [D, L] using hn))))
  have hhorAction : S.a (n + gap) ≤ rho.horizon := by
    simpa only [opening_confirmation_time_eq_action] using hhor
  have hhorTrigger :=
    (Proofs.HealingLemmas.openingProposal_window_le_action S n gap).trans hhorAction
  obtain ⟨m, hmlo, hmhi, hcarrier⟩ := hrec n hGSTtrigger hhorTrigger
  let start := S.hc.opening_slot m
  obtain ⟨P, hP⟩ := proposedBlockAt_isSome S rho start
  have hhorM : Protocol.confirmation_time S.E start ≤ rho.horizon :=
    (confirmationTime_mono_directV4 S.E
      (by simpa only [start] using Nat.mul_le_mul_right S.hc.R hmhi)).trans hhor
  have hhorVote : Protocol.vote_time S.E start ≤ rho.horizon :=
    (vote_time_le_confirmation_time S.E start).trans hhorM
  have hhorVoteDelta : Protocol.vote_time S.E start + S.E.Δ ≤ rho.horizon := by
    have htime : ∀ p d : Int, 0 < d → p + d + d ≤ p + 6 * d := by
      intro p d hd
      omega
    exact (htime _ _ S.E.Δ_pos).trans hhorM
  have hbaseN : base + S.hc.η_SG ≤ n := by
    simpa only [D, L, base, Nat.add_assoc] using hn
  have hbaseM : base + S.hc.η_SG ≤ m := hbaseN.trans hmlo
  have hDtwoM : D + 2 ≤ m := by
    have hLpos : 1 ≤ L := by simpa only [L] using progressLag'_pos gap
    have h2L : 2 ≤ 2 * L := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left 2 hLpos
    exact (Nat.add_le_add_left h2L D).trans
      ((Nat.le_add_right (D + 2 * L) (1 + S.hc.η_SG)).trans (by
        simpa only [base, Nat.add_assoc] using hbaseM))
  have hheads : ∀ v ∈ rho.honest, voterHeadAt S rho v start = P.erase :=
    _of_heads S adm hcom hbot hrec hdelay hpost
      (by simpa only [D, start] using hDtwoM) hhorVote hcarrier
      (by simpa only [start] using hP)
  have hcone : NamedHonestVotesCone S rho start
      (fun X => Block.Preceq P.erase X) :=
    _of_cone S adm hcom hDtwoM hcarrier hhorVote
      (by simpa only [start] using hP) (by simpa only [start] using hheads)
  have hconfirmationSeed :=
    _of_confirmationSeed S adm hcom hbot hrec hdelay hpost
      (by simpa only [D, L, base, start] using hbaseM) hcarrier
      (by simpa only [start] using hP) hhorM
  have hheights := handoverHeights_of_carrier_named
    S adm hcom hbot hrec hdelay hpost
      (base := base) (m := m) (show D + 2 * L + 1 ≤ base by rfl) hbaseM
      hcarrier hhorM (by simpa only [start] using hP)
  have hDbase : D ≤ base + S.hc.η_SG := by
    simpa only [base, Nat.add_assoc] using
      Nat.le_add_right D (2 * L + 1 + S.hc.η_SG)
  have hDle : D ≤ n + gap :=
    hDbase.trans (hbaseN.trans (Nat.le_add_right n gap))
  have hDhor : S.a D ≤ rho.horizon := by
    rw [← opening_confirmation_time_eq_action]
    exact (confirmationTime_mono_directV4 S.E
      (Nat.mul_le_mul_right S.hc.R hDle)).trans hhor
  obtain ⟨blocked, first, Tprev, hdeadline, hregime⟩ :=
    exists_namedHeightRegimeBaseRun_before_fgSafetyProgressDeadline
      S adm hcom hbot hrec hdelay hpost (by simpa only [D] using hDhor)
  have hfg := fgWitnessesBelow_of_namedHeightRegimeBaseRun_of_headEq
    S adm hcom hbot (gstLagged_le_Γ_neg1_of_gst_le_a S rGST hpost)
      hregime hdeadline (by simpa only [D, L, base, start] using hbaseM)
      (by simpa only [start] using hheads) hhorM
  have hmPos : 1 ≤ m := by
    have hDpos : 1 ≤ D := by
      dsimp only [D]
      unfold fgSafetyProgressDeadline
      exact (Nat.le_add_left 1 _).trans (Nat.le_add_right _ _)
    exact hDpos.trans ((Nat.le_add_right D (2 * L + 1 + S.hc.η_SG)).trans
      (by simpa only [base, Nat.add_assoc] using hbaseM))
  have hstartPos : 1 ≤ start := by
    simpa only [start] using
      (show 1 ≤ S.hc.opening_slot m from
        (by decide : (1 : Nat) ≤ 2).trans
          (S.hc.R_ge_two.trans (Nat.le_mul_of_pos_left S.hc.R hmPos)))
  have hrun : RunBlock S rho P :=
    proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
      start hstartPos (by simpa only [start] using hcarrier.1)
      ((proposal_time_le_confirmation_time S.E start).trans hhorM)
      (by simpa only [start] using hP)
  have hsg : ∀ r, base ≤ r → r < base + S.hc.η_SG →
      ∀ w ∈ rho.honest,
      NamedRun.emits S rho w
        (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
      Block.Preceq (actionSGBlockAt S rho w r) P.erase := by
    intro r hrlo hrhi w hw _
    have hrpos : 1 ≤ r := by
      have hDpos : 1 ≤ D := by
        dsimp only [D]
        unfold fgSafetyProgressDeadline
        exact (Nat.le_add_left 1 _).trans (Nat.le_add_right _ _)
      exact hDpos.trans ((Nat.le_add_right D (2 * L + 1)).trans
        (by simpa only [base, Nat.add_assoc] using hrlo))
    obtain ⟨c, rfl⟩ : ∃ c, r = c + 1 :=
      ⟨r - 1, (Nat.sub_add_cancel hrpos).symm⟩
    have hcD : D ≤ c := by
      have : D + 1 ≤ c + 1 :=
        (Nat.add_le_add_right (Nat.le_add_right D (2 * L)) 1).trans
          (by simpa only [base, Nat.add_assoc] using hrlo)
      exact Nat.le_of_succ_le_succ this
    have hcm : c + 1 < m := hrhi.trans_le hbaseM
    have hslot : S.hc.opening_slot (c + 1) + 1 ≤ start := by
      simpa only [start] using openingSlot_succ_le_of_lt_directV4 S hcm
    have hpre := actionSGBlock_preceq_voterHeadAt_after_GST
      S adm hcom hbot hrec hdelay hpost hcD hslot hhorVoteDelta hw hw
    rwa [hheads w hw] at hpre
  have hconf : ∀ q, S.hc.opening_slot (base + S.hc.η_SG) ≤ q →
      q < start → ∀ w ∈ rho.honest, ∀ B,
      GenuineConfirmationWith
        (NamedProfile.gradeContract
          (confirmationInputRead S rho w q).cache)
        S.E S.hc (confStore S rho w q) q B →
      Block.Preceq B P.erase := by
    intro q hqlo hqhi w hw B hB
    have hDtwoCut : D + 2 < base + S.hc.η_SG := by
      have hLpos : 1 ≤ L := by simpa only [L] using progressLag'_pos gap
      have h2L : 2 ≤ 2 * L := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left 2 hLpos
      have htail : D + 2 * L < base + S.hc.η_SG := by
        calc
          D + 2 * L < D + 2 * L + 1 := Nat.lt_succ_self _
          _ ≤ base + S.hc.η_SG := by
            simpa only [base] using
              Nat.le_add_right (D + 2 * L + 1) S.hc.η_SG
      exact Nat.lt_of_le_of_lt (Nat.add_le_add_left h2L D)
        htail
    have hopen : S.hc.opening_slot (D + 2) + 1 ≤ q :=
      (openingSlot_succ_le_of_lt_directV4 S hDtwoCut).trans hqlo
    have hqhor : Protocol.confirmation_time S.E q ≤ rho.horizon :=
      (confirmationTime_mono_directV4 S.E (Nat.le_of_lt hqhi)).trans hhorM
    have hpre := genuineConfirmationWith_preceq_laterVoterHeads_after_GST
      S adm hcom hbot hrec hdelay hpost (c := D + 1) (le_refl (D + 1))
      hopen hqhor hw hB start (Nat.succ_le_of_lt hqhi) hhorVote w hw
    rwa [hheads w hw] at hpre
  refine ⟨m, hmlo, hmhi, hcarrier, P, by simpa only [start] using hP, ?_, ?_⟩
  · refine
      { settled := by
          simpa only [base, start] using Nat.mul_le_mul_right S.hc.R hbaseM
        basePost := ?_
        seed := ⟨?_, hcone⟩
        seedAll := ?_
        confirmationSeedPrepared := hconfirmationSeed
        runBlock := hrun
        oldRows := ?_
        heightCap := ?_
        frontierSeed := ?_
        sgBoot := hsg
        confBoot := hconf
        fgAll := hfg }
    · have hrGSTbase : rGST ≤ base :=
        ((Nat.le_succ rGST).trans
          (gstRound_succ_le_deadline (delayExtra := delayExtra)
            S rho rGST gap)).trans (by
              simpa only [D, base] using Nat.le_add_right D (2 * L + 1))
      exact hpost.trans (Assembly.a_mono S hrGSTbase)
    · intro w hw _
      rw [hheads w hw]
      exact Block.preceq_self _
    · intro w hw
      rw [hheads w hw]
      exact Block.preceq_self _
    · simpa only [D, Nat.add_sub_cancel] using
        WeakJoint.oldHeightRowsBounded_of_honestFrontier
          S adm.toNamedAdmissibleCore (D + 1)
    · simpa only [D, Nat.add_sub_cancel] using hheights.heightOld.le
    · exact Or.inr (by
        simpa only [D, L, base, Nat.add_sub_cancel, start] using
          hheights.frontierSeed)
  · simpa only [D, Nat.add_sub_cancel] using hheights.heightOld

#print axioms settledBootstrap_of_strong_preparedV4_of_live_pins



/-- P10: the public-bound direct selector uses the available live confirmation
producer and has no proof-layer pin. -/
theorem settledBootstrap_of_strong_preparedV4
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbot : BelowOneThird S rho.honest)
    {rGST gap : Round} (hdelay : TimeoutDelayBound S delayExtra)
    (hrec : MultiProposerRecurrence S rho gap) (hpost : S.E.t_GST ≤ S.a rGST)
    {n : Round}
    (hn : fgSafetyProgressDeadline S rho rGST gap delayExtra +
      2 * progressLag' gap delayExtra + 1 + S.hc.η_SG ≤ n)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot (n + gap)) ≤ rho.horizon) :
    ∃ m : Round, n ≤ m ∧ m ≤ n + gap ∧ ProposerCarrierAt S rho m ∧
      ∃ P : NamedBlock V,
        proposedBlockAt S rho (S.hc.opening_slot m) = some P ∧
        SettledBootstrapPreparedV4 S rho
          (fgSafetyProgressDeadline S rho rGST gap delayExtra + 1)
          (fgSafetyProgressDeadline S rho rGST gap delayExtra +
            2 * progressLag' gap delayExtra + 1)
          (S.hc.opening_slot m) P
          (honestHMaxAt S rho
            (S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra))) ∧
        honestHMaxAt S rho
            (S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra)) <
          (Protocol.derive_named S.E S.cfg P).h := by
  exact settledBootstrap_of_strong_preparedV4_of_live_pins
    honestProposal_voterHeadAt_eq_after_SG_healing_named
    honestProposal_openingVoteCone_after_SG_healing_named
    honestProposal_confirmationSeedPrepared_live_after_SG_healing_named
    S adm hcom hbot hdelay hrec hpost hn hhor

#print axioms settledBootstrap_of_strong_preparedV4




/-- Additive closed stable-side selector under the  recovery window. The
older theorem with the unsuffixed name remains as the compatibility pin used
by existing consumers. -/
theorem settledBootstrap_of_strong_preparedV4_latest_closed
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbot : BelowOneThird S rho.honest)
    {rGST gap : Round} (hdelay : TimeoutDelayBound S delayExtra)
    (hrec : MultiProposerRecurrence S rho gap) (hpost : S.E.t_GST ≤ S.a rGST)
    {n : Round}
    (hn : fgSafetyProgressDeadline S rho rGST gap delayExtra +
      2 * progressLag' gap delayExtra +
      max (1 + S.hc.η_SG) (gap + 3) ≤ n)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot (n + gap)) ≤ rho.horizon) :
    ∃ m : Round, n ≤ m ∧ m ≤ n + gap ∧ ProposerCarrierAt S rho m ∧
      ∃ P : NamedBlock V,
        proposedBlockAt S rho (S.hc.opening_slot m) = some P ∧
        SettledBootstrapPreparedV4 S rho
          (fgSafetyProgressDeadline S rho rGST gap delayExtra + 1)
          (fgSafetyProgressDeadline S rho rGST gap delayExtra +
            2 * progressLag' gap delayExtra + 1)
          (S.hc.opening_slot m) P
          (honestHMaxAt S rho
            (S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra))) ∧
        SettledBootstrapPreparedV4.LatestSeed S rho
          (S.hc.opening_slot m) P ∧
        honestHMaxAt S rho
            (S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra)) <
          (Protocol.derive_named S.E S.cfg P).h := by
  have hnOld : fgSafetyProgressDeadline S rho rGST gap delayExtra +
      2 * progressLag' gap delayExtra + 1 + S.hc.η_SG ≤ n := by
    have hmax : 1 + S.hc.η_SG ≤ max (1 + S.hc.η_SG) (gap + 3) :=
      le_max_left _ _
    have hold := (Nat.add_le_add_left hmax
      (fgSafetyProgressDeadline S rho rGST gap delayExtra +
        2 * progressLag' gap delayExtra)).trans (by
          simpa only [Nat.add_assoc] using hn)
    simpa only [Nat.add_assoc] using hold
  obtain ⟨m, hmlo, hmhi, hcarrier, P, hP, hboot, hheight⟩ :=
    settledBootstrap_of_strong_preparedV4
      S adm hcom hbot hdelay hrec hpost hnOld hhor
  have hmSeed : fgSafetyProgressDeadline S rho rGST gap delayExtra +
      2 * progressLag' gap delayExtra +
      max (1 + S.hc.η_SG) (gap + 3) ≤ m :=
    hn.trans hmlo
  have hhorM : Protocol.confirmation_time S.E (S.hc.opening_slot m) ≤
      rho.horizon :=
    (confirmationTime_mono_directV4 S.E
      (Nat.mul_le_mul_right S.hc.R hmhi)).trans hhor
  have hlatest : SettledBootstrapPreparedV4.LatestSeed S rho
      (S.hc.opening_slot m) P :=
    honestProposal_confirmationSeedPrepared_latest_after_SG_healing_named
      S adm hcom hbot hrec hdelay hpost hmSeed hcarrier hP hhorM
  exact ⟨m, hmlo, hmhi, hcarrier, P, hP, hboot, hlatest, hheight⟩

#print axioms settledBootstrap_of_strong_preparedV4_latest_closed

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
