module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Generic.FrontierCoverage
public import DecoupledConsensusProofs.Protocol.ChainState.Main
public import DecoupledConsensusInternal.Execution.Assumptions
public import DecoupledConsensusProofs.Protocol.Handlers.NamedStore
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge
public import DecoupledConsensusProofs.Protocol.ChainState.NjGap
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordFresh
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordTargetHistory
public import DecoupledConsensusProofs.Execution.EmissionShape
public import DecoupledConsensusProofs.Protocol.ChainState.NamedNjGap
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecoveryTimeout
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Generic.RecoveryConcentration
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FinalityFilterRetention
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionActivity
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsBridge
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The fresh cap removes strict action sources -/

/-- The virtual action store's frontier is below the inclusive moving honest
frontier at the same action instant. -/
theorem actionStoreHMax_le_honestHMaxAt_action
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) (r : Round) :
    (actionStoreAt S rho v r).st.core.h_max ≤
      honestHMaxAt S rho (S.a r) := by
  have hpre : (actionStoreAt S rho v r).st.core.h_max =
      (rho.storeBeforeTime S v (S.a r)).core.h_max := rfl
  rw [hpre, storeBeforeTime_eq_storeAt_sub_one_recovery]
  exact (stateAt_h_max_mono S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v
      (sub_le_self _ (by norm_num : (0 : Time) ≤ 1))).trans
    (localHMax_le_honestHMaxAt S rho (S.a r) hv)




/-! ## A carrier at one bounded honest proposal -/





 

/-! ## The named next-grade continuation -/




#print axioms actionStoreHMax_le_honestHMaxAt_action

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
