module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.CrossReaderHealthyPrefix

@[expose] public section

/-!
# Stable-round Claim 1 body-open guard

The forward finality cap uses the healthy-prefix finality relay in the reverse
reader direction. The target's G1 finalized root reaches the source one delay
later. Local finality monotonicity then reaches the stable action read. The
action's active G2 prefix is above that finalized root and below the raw G2
root. Thus, every source input head that covers the raw root also covers the
target finalized root.
-/

namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Internal.NamedOutageEntry Internal.NamedStableChainOutage
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem claimOne_domain_g1_add_delta_eq_g0
    (S : Setup V) (s : Round) :
    domain S.E S.hc s .g1 + S.E.Δ = domain S.E S.hc s .g0 := by
  unfold domain Phase.domainOffset
  ring

set_option maxHeartbeats 400000 in
/-- The stable action chain also gives the finalized-prefix orientation at the
G1 read and at the opening vote read. The latter is obtained by one healthy
prefix finality relay before the source action; local finality monotonicity is
used only after that relay. -/
theorem stableAt_finalized_below_raw_at_reader
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    {s : Round} (hs : 0 < s)
    (hmargin : FormationMargin S s b0)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {G raw : Block V}
    (hG : PhaseGrades.nodeQ2 S (Proofs.HealingSurface.actionReadAt S rho v s) s = some G)
    (hGraw : Block.Preceq G raw) :
    Block.Preceq
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc s .g1) w).st.core.F raw ∧
      Block.Preceq
        (Internal.NamedRecoveryRead.voteDutyRead S rho w
          (S.hc.opening_slot s)).st.core.F raw := by
  have hcap : b0 ≤ rho.horizon :=
    hexec.interval.2.1.trans hexec.interval.2.2
  have has : S.a s ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_succ s)).trans
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans (hmargin.trans hcap))
  have hdomainCap : domain S.E S.hc s .g0 ≤ b0 :=
    (FrameForward.domain_le_a S s .g0).trans
      ((Assembly.a_mono S (Nat.le_succ s)).trans
        ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin))
  have hdomainHor : domain S.E S.hc s .g0 ≤ rho.horizon :=
    hdomainCap.trans hcap
  have hG' : DecoupledConsensusModel.Protocol.grade2Block
      (Proofs.HealingSurface.actionReadAt S rho v s).st.core.toHealing
      (DecoupledConsensusModel.Protocol.readFrame
        (Proofs.HealingSurface.actionReadAt S rho v s).cache
        (Proofs.HealingSurface.actionReadAt S rho v s).st.core.toHealing s) = some G := hG
  unfold DecoupledConsensusModel.Protocol.grade2Block at hG'
  rw [if_pos (Proofs.HealingSurface.actionFrame_allClosed
    S hexec.core hv hs has)] at hG'
  obtain ⟨root, -, hactive⟩ := Option.bind_eq_some_iff.mp hG'
  have hGmem : G ∈ Protocol.get_filtered_block_tree
      (Proofs.HealingSurface.actionReadAt S rho v s).st.core.toHealing.toFG :=
    NamedProposalParent.activePrefix_mem _ root G hactive
  have hactionFG : Block.Preceq
      (Proofs.HealingSurface.actionReadAt S rho v s).st.core.F G :=
    q10_filtered_F hGmem
  have hactionRaw : Block.Preceq
      (Proofs.HealingSurface.actionReadAt S rho v s).st.core.F raw :=
    Block.preceq_trans hactionFG hGraw
  have hhop : domain S.E S.hc s .g1 + S.E.Δ =
      domain S.E S.hc s .g0 :=
    claimOne_domain_g1_add_delta_eq_g0 S s
  have hrelay :=
    Proofs.HealingSurface.finalized_preceq_of_evidence_delivered_healthyPrefix
      S hexec.core hslash b0 hexec.healthy hw hv hhop hdomainCap hdomainHor
  have houtAction : domain S.E S.hc s .g0 ≤ S.a s :=
    FrameForward.domain_le_a S s .g0
  have hmono : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc s .g0) v).st.core.F
      (Proofs.HealingSurface.actionReadAt S rho v s).st.core.F := by
    show Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc s .g0) v).st.core.F
      (NamedRun.stateBeforeTime S rho (S.a s) v).st.core.F
    rw [strict_read_eq_index S rho hexec.core.sorted (domain S.E S.hc s .g0),
      strict_read_eq_index S rho hexec.core.sorted (S.a s)]
    exact Proofs.NamedRuntime.stateBefore_F_mono S rho v
      (strict_lengths_mono rho houtAction)
  have htargetRaw : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc s .g1) w).st.core.F raw :=
    Block.preceq_trans hrelay
      (Block.preceq_trans hmono hactionRaw)
  have hvoteDeltaAction :
      Protocol.vote_time S.E (S.hc.opening_slot s) + S.E.Δ ≤ S.a s := by
    calc
      Protocol.vote_time S.E (S.hc.opening_slot s) + S.E.Δ =
          Protocol.support_cutoff S.E (S.hc.opening_slot s) :=
        Proofs.Optimistic.vote_time_add_delta S.E _
      _ ≤ Protocol.confirmation_time S.E (S.hc.opening_slot s) :=
        Protocol.support_cutoff_le_confirmation_time S.E _
      _ = S.a s := (Protocol.a_eq_confirmation_time S.hc S.E s).symm
  have hvoteDeltaCap :
      Protocol.vote_time S.E (S.hc.opening_slot s) + S.E.Δ ≤ b0 :=
    hvoteDeltaAction.trans
      ((Assembly.a_mono S (Nat.le_succ s)).trans
        ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin))
  have hvoteDeltaHor :
      Protocol.vote_time S.E (S.hc.opening_slot s) + S.E.Δ ≤ rho.horizon :=
    hvoteDeltaCap.trans hcap
  have hrelayVote :=
    Proofs.HealingSurface.finalized_preceq_of_evidence_delivered_healthyPrefix
      S hexec.core hslash b0 hexec.healthy hw hv
        (read := Protocol.vote_time S.E (S.hc.opening_slot s))
        (out := Protocol.vote_time S.E (S.hc.opening_slot s) + S.E.Δ)
        rfl hvoteDeltaCap hvoteDeltaHor
  have hmonoVote : Block.Preceq
      (NamedRun.stateBeforeTime S rho
        (Protocol.vote_time S.E (S.hc.opening_slot s) + S.E.Δ) v).st.core.F
      (Proofs.HealingSurface.actionReadAt S rho v s).st.core.F := by
    show Block.Preceq
      (NamedRun.stateBeforeTime S rho
        (Protocol.vote_time S.E (S.hc.opening_slot s) + S.E.Δ) v).st.core.F
      (NamedRun.stateBeforeTime S rho (S.a s) v).st.core.F
    rw [strict_read_eq_index S rho hexec.core.sorted
          (Protocol.vote_time S.E (S.hc.opening_slot s) + S.E.Δ),
      strict_read_eq_index S rho hexec.core.sorted (S.a s)]
    exact Proofs.NamedRuntime.stateBefore_F_mono S rho v
      (strict_lengths_mono rho hvoteDeltaAction)
  have hvoteRaw : Block.Preceq
      (NamedRun.stateBeforeTime S rho
        (Protocol.vote_time S.E (S.hc.opening_slot s)) w).st.core.F raw :=
    Block.preceq_trans hrelayVote
      (Block.preceq_trans hmonoVote hactionRaw)
  constructor
  · exact htargetRaw
  · simpa only [Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      hvoteRaw

#print axioms stableAt_finalized_below_raw_at_reader

set_option maxHeartbeats 400000 in
theorem claimOne_guard_at_stableRound
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    {s : Round} (hs : 0 < s)
    (hmargin : FormationMargin S s b0)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {G raw : Block V}
    (hG : PhaseGrades.nodeQ2 S (Proofs.HealingSurface.actionReadAt S rho v s) s = some G)
    (hGraw : Block.Preceq G raw) :
    CrossReaderBodyReadyGuard S rho s v w raw := by
  have hcap : b0 ≤ rho.horizon :=
    hexec.interval.2.1.trans hexec.interval.2.2
  have has : S.a s ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_succ s)).trans
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans (hmargin.trans hcap))
  have hdomainCap : domain S.E S.hc s .g0 ≤ b0 :=
    (FrameForward.domain_le_a S s .g0).trans
      ((Assembly.a_mono S (Nat.le_succ s)).trans
        ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hmargin))
  have hdomainHor : domain S.E S.hc s .g0 ≤ rho.horizon :=
    hdomainCap.trans hcap
  have hfinalized := stableAt_finalized_below_raw_at_reader S rho b0 b1 hexec
    hslash hs hmargin hv hw hG hGraw
  have htargetRaw : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc s .g1) w).st.core.F raw :=
    hfinalized.1
  have hbelow : CrossReaderFinalizedBelow S rho s v w raw :=
    Proofs.HealingSurface.crossReaderFinalizedBelow_of_slashableBound_and_healthyPrefix
      S hexec.core hslash (r := s) b0 hexec.healthy hdomainCap hdomainHor
      hv hw (B := raw) (by
        intro sender u root H _hu hcover hconf hfind
        refine Block.preceq_trans htargetRaw ?_
        simp only [DecoupledConsensusModel.Protocol.localCovers, Protocol.head_covers,
          hconf, hfind] at hcover
        exact hcover)
  exact Proofs.HealingSurface.crossReaderBodyReadyGuard_of_finalizedBelow_and_healthyPrefix
    S hexec.core (r := s) hs b0 hexec.healthy hdomainCap hdomainHor hv hw hbelow

#print axioms claimOne_guard_at_stableRound

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
