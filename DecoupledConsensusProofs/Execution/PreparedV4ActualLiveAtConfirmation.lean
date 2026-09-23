module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.PreparedV4ActualLiveSelectionComplete

@[expose] public section

/-! # Prepared V4 stored live values at an actual vote -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every covered stored confirmation value is below every honest head at the
actual destination vote. -/
theorem SettledBootstrapPreparedV4.liveConfirmedAtConfirmation_at_actual_vote_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start d : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hd : start ≤ d) (hhor : Protocol.vote_time S.E d ≤ rho.horizon) :
    ∀ q, S.hc.opening_slot (base + S.hc.η_SG) ≤ q → q < d →
      Protocol.confirmation_time S.E q ≤ rho.horizon →
      ∀ w ∈ rho.honest, ∀ v ∈ rho.honest,
        Block.Preceq
          (rho.storeAt S w (Protocol.confirmation_time S.E q)).live_confirmed
          (voteDutyHead S rho v d) := by
  intro q hq hqd hqhor w hw v hv
  rw [live_confirmed_eq_update
    S adm.toNamedScheduleWellFormed hw q hqhor]
  exact (SettledBootstrapPreparedV4.liveConfirmedSelection_at_actual_vote_core
    S adm hcom hboot hawake hfinality hd hhor hq hqhor hqd hw).heads v hv

#print axioms SettledBootstrapPreparedV4.liveConfirmedAtConfirmation_at_actual_vote_core

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
