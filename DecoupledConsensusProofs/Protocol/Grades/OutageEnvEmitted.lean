module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.OutageEnvIdx
public import DecoupledConsensusProofs.Execution.IdxDriverEmitted

@[expose] public section

/-! # Outage instance of the emission-backed history driver -/

namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.OutageEnv

open DecoupledConsensusModel
open Internal Execution Internal.NamedOutageEntry DecoupledConsensusModel.Protocol
open Internal.NamedOutageEntry.History Internal.NamedStableChainOutage

variable {V : Type} [DecidableEq V] [Fintype V]

theorem layerA_joint_history_idx_emitted_of_outage
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s : Round)
    (hexec : OutageExecution S rho b0 b1)
    (hsleepy : OutageSleepyThroughout S rho)
    (hmargin : FormationMargin S s b0)
    (committees : HonestCommittees S rho.honest)
    (hconf : NamedConfirmationIdxQueryEmitted S rho b0) :
    ∀ n : Nat, n ≤ boundaryIdx rho b0 →
      ∃ C : NamedBlock V, LayerAJointHistoryIdxEmitted S rho n C := by
  have hcap : b0 ≤ rho.horizon :=
    hexec.interval.2.1.trans hexec.interval.2.2
  have hwindows : ∀ k, 0 < k → domain S.E S.hc k .g2 ≤ b0 →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG k := by
    intro k hk hkb0
    exact hsleepy k hk
      (Or.inr ⟨.g2, domain_g2_nonneg S hk, hkb0.trans hcap⟩)
  have hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q :=
    Proofs.NamedOutageInputs.boundary_faulty_lt_quorum S rho b0 b1 s
      hexec hmargin hsleepy
  exact IdxDriverEmitted.layerA_joint_history_idx_emitted S rho b0 hexec.core
    hexec.healthy committees S.hc.R_ge_three hcap hwindows hbad hconf

#print axioms layerA_joint_history_idx_emitted_of_outage

end DecoupledConsensusModel.Proofs.NamedOutageHistory.OutageEnv

end
