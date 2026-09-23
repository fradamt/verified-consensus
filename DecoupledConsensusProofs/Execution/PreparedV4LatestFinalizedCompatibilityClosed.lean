module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.PreparedV4LatestHeadClosed
public import DecoupledConsensusProofs.Execution.PreparedV4LatestFinalizedCompatibility

@[expose] public section

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

theorem SettledBootstrapPreparedV4.latest_compatible_finalized_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hlatest : SettledBootstrapPreparedV4.LatestSeed S rho start P)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hstartHor : Protocol.confirmation_time S.E start ≤ rho.horizon)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {t u : Time}
    (ht : Protocol.confirmation_time S.E start ≤ t)
    (hu : Protocol.confirmation_time S.E start ≤ u)
    (htHor : t ≤ rho.horizon) (huHor : u ≤ rho.horizon) :
    Block.compatible (rho.storeAt S v t).core.latest_confirmed
      (rho.storeAt S w u).core.F = true := by
  exact SettledBootstrapPreparedV4.latest_compatible_finalized_core_of_latest_pin
    S adm hcom hboot hlatest hawake hfinality hstartHor
    (fun {v} hv {t} ht =>
      SettledBootstrapPreparedV4.latest_has_voteHead_bound_core
        S adm hcom hboot hlatest hawake hfinality hstartHor (v := v) hv (t := t) ht)
    hv hw ht hu htHor huHor

#print axioms SettledBootstrapPreparedV4.latest_compatible_finalized_core

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
