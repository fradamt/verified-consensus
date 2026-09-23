module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.SeedRelativeGrade
public import DecoupledConsensusProofs.Protocol.Handlers.MutualInduction
public import DecoupledConsensusProofs.Protocol.Grades.Stage2
public import DecoupledConsensusProofs.Protocol.Grades.BoundedChainPrebuild
public import DecoupledConsensusProofs.Protocol.Grades.OutageEnvEmitted
public import DecoupledConsensusProofs.Protocol.Grades.HealthyPrefixCommittees
public import DecoupledConsensusProofs.Protocol.Grades.ClaimOneGuardR172

@[expose] public section

/-!
# Stable-round Claim 1 inputs for outage resilience

This additive module connects the public `stableAt` witness to the relative
grade used by height progress. It also records the exact residual needed to
apply Claim 1 at every honest vote duty.
-/

namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Internal.NamedOutageEntry Internal.NamedStableChainOutage
open DecoupledConsensusModel.Protocol
open Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The public stable read and the prepared action read select the same active
G2 block once the round frame is closed. -/
theorem stableAt_nodeQ2_actionRead
    (S : Setup V) (rho : NamedRun V) (v : V) (s : Round) (P : Block V)
    (core : NamedAdmissibleCore S rho) (hv : v ∈ rho.honest)
    (hs : 0 < s) (hhor : S.a s ≤ rho.horizon)
    (hstable : stableAt S rho v s P) :
    ∃ G, PhaseGrades.nodeQ2 S (Proofs.HealingSurface.actionReadAt S rho v s) s = some G ∧
      Block.Preceq P G := by
  obtain ⟨G, hG, hPG⟩ := hstable
  refine ⟨G, ?_, hPG⟩
  have hclosed := Proofs.HealingSurface.actionFrame_allClosed S core hv hs hhor
  have hround : S.hc.round_of
      (Internal.NamedOutageEntry.confirmationReadAt S rho v (S.a s)).st.core.toHealing.s = s :=
    Proofs.HealingLemmas.round_of_slotOf_a S s
  simp only [PhaseGrades.nodeQ2, PhaseGrades.nodeRead,
    NamedProfile.gradeContract, DecoupledConsensusModel.Protocol.frameContract,
    DecoupledConsensusModel.Protocol.frameGradeRead]
  unfold DecoupledConsensusModel.Protocol.grade2Block
  rw [if_pos hclosed]
  unfold Internal.NamedStableChainOutage.activeG2
    Internal.NamedStableChainOutage.roundConfirmationRead
    DecoupledConsensusModel.Protocol.frameSGCandidate at hG
  rw [hround] at hG
  simpa only [Proofs.HealingSurface.actionReadAt, NamedActionReads.actionReadAt,
    Internal.NamedOutageEntry.confirmationReadAt,
    NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom,
    NamedActionReads.actionReadFrom,
    NamedActionReads.preparedCache, Protocol.NamedStore.setClock,
    Protocol.NamedDuties.update_confirmation_with,
    Protocol.update_confirmation_with,
    DecoupledConsensusModel.Protocol.readFrame, DecoupledConsensusModel.Protocol.clipFrame,
    DecoupledConsensusModel.Protocol.clipResult] using hG

/-- The public stable witness exposes the raw G2-domain root graded at the
source reader. Clipping gives `P ⪯ G ⪯ raw`. -/
theorem stableAt_rawG2_grade
    (S : Setup V) (rho : NamedRun V) (v : V) (s : Round) (P : Block V)
    (core : NamedAdmissibleCore S rho) (hv : v ∈ rho.honest)
    (hs : 0 < s) (hhor : S.a s ≤ rho.horizon)
    (hstable : stableAt S rho v s P) :
    ∃ G raw : Block V,
      PhaseGrades.nodeQ2 S (Proofs.HealingSurface.actionReadAt S rho v s) s = some G ∧
      PhaseGrades.storeGrade S.E S.hc
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc s .g2) v).st s .g2 raw = true ∧
      Block.Preceq P G ∧ Block.Preceq G raw := by
  obtain ⟨G, hG, hPG⟩ := stableAt_nodeQ2_actionRead
    S rho v s P core hv hs hhor hstable
  obtain ⟨raw, hgrade, hGraw⟩ :=
    Proofs.HealingSurface.namedG2At_freezeRoot_of_nodeQ2 S core hG
  exact ⟨G, raw, hG, hgrade, hPG, hGraw⟩

/-! A stable G2 root at one honest reader is a G1 root at every honest
reader. The healthy-prefix delivery supplies the phase transport, and the
stable-round guard supplies the cross-reader body-open condition. -/
set_option maxHeartbeats 400000 in
theorem stableAt_rawG2_is_G1_everywhere
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (v : V)
    (s : Round) (P : Block V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho)
    (hv : v ∈ rho.honest) (hmargin : FormationMargin S s b0)
    (hstable : stableAt S rho v s P) (hs : 0 < s) :
    ∃ G raw : Block V, Block.Preceq P G ∧ Block.Preceq G raw ∧
      ∀ w ∈ rho.honest,
        PhaseGrades.storeGrade S.E S.hc
          (PhaseGrades.readAt S rho
            (DecoupledConsensusModel.Protocol.domain S.E S.hc s .g1) w).st s .g1 raw = true := by
  have hcap : b0 ≤ rho.horizon :=
    hexec.interval.2.1.trans hexec.interval.2.2
  have has : S.a s ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_succ s)).trans
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans (hmargin.trans hcap))
  obtain ⟨G, raw, hG, hgrade, hPG, hGraw⟩ :=
    stableAt_rawG2_grade S rho v s P hexec.core hv hs has hstable
  refine ⟨G, raw, hPG, hGraw, ?_⟩
  have hdomainCap : domain S.E S.hc s .g0 ≤ b0 :=
    (FrameForward.domain_le_a S s .g0).trans
      ((Assembly.a_mono S (Nat.le_succ s)).trans
        ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin))
  have hdomainHor : domain S.E S.hc s .g0 ≤ rho.horizon :=
    hdomainCap.trans hcap
  have delivery := twoCutoffDelivery_of_healthyPrefix
    S rho b0 hexec.healthy hdomainCap
  intro w hw
  apply Proofs.HealingSurface.storeGrade_g1_of_storeGrade_g2_cross_reader
    S rho hexec.core s delivery hdomainHor v w hv hw raw hgrade
  exact claimOne_guard_at_stableRound S rho b0 b1 hexec hslash hs hmargin
    hv hw hG hGraw

#print axioms stableAt_rawG2_is_G1_everywhere

/-! Clauses 2 and 5 are not residual once no-conflict, clause 1, and
confirmation coverage are available. -/

#print axioms stableAt_nodeQ2_actionRead
#print axioms stableAt_rawG2_grade





end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
