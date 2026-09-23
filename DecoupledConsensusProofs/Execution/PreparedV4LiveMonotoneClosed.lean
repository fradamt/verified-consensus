module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.PreparedV4ConfirmationOutputsClosed
public import DecoupledConsensusProofs.Protocol.Schedule.PreparedV4LiveMonotone

@[expose] public section

/-! # Closed prepared V4 live-confirmed monotonicity -/

namespace DecoupledConsensusModel.Proofs.HealingSurface.Handover

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

theorem SettledBootstrapPreparedV4.liveConfirmed_mono_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    {v : V} (hv : v ∈ rho.honest) {t u : Time}
    (ht : Protocol.confirmation_time S.E start ≤ t) (htu : t ≤ u) :
    Block.Preceq (rho.storeAt S v t).live_confirmed
      (rho.storeAt S v u).live_confirmed := by
  exact SettledBootstrapPreparedV4.liveConfirmed_mono_core_of_pins
    S adm hcom hboot hawake hfinality
      (fun s hs hhor v hv' w hw t htlo hthi =>
        SettledBootstrapPreparedV4.liveConfirmed_preceq_at_confirmation_core
          S adm hcom hboot hawake hfinality hs hhor hv' hw htlo hthi)
      hv ht htu

#print axioms SettledBootstrapPreparedV4.liveConfirmed_mono_core

end DecoupledConsensusModel.Proofs.HealingSurface.Handover

end
