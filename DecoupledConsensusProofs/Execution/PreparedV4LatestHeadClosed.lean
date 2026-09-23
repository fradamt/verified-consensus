module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.PreparedV4LatestHeadCore
public import DecoupledConsensusProofs.Execution.PreparedV4ConfirmationOutputsClosed

@[expose] public section

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

theorem SettledBootstrapPreparedV4.latest_has_voteHead_bound_core
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
    {v : V} (hv : v ∈ rho.honest) {t : Time}
    (ht : Protocol.confirmation_time S.E start ≤ t) :
    ∃ first : Slot, start ≤ first ∧
      Protocol.confirmation_time S.E first ≤ rho.horizon ∧
      ∀ last, first ≤ last →
        Protocol.confirmation_time S.E last ≤ rho.horizon →
        ∀ x ∈ rho.honest,
          Block.Preceq (rho.storeAt S v t).core.latest_confirmed
            (voterHeadAt S rho x (last + 1)) := by
  exact SettledBootstrapPreparedV4.latest_has_voteHead_bound_core_of_genuine_pin
    S adm hcom hboot hlatest hawake hfinality hstartHor
    (fun q hq hqHor v hv =>
      SettledBootstrapPreparedV4.genuineConfirmationAt_core
        S adm hcom hboot hawake hfinality hq hqHor hv)
    hv ht

#print axioms SettledBootstrapPreparedV4.latest_has_voteHead_bound_core

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
