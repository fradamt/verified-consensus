module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.PreparedV4VoteSources
public import DecoupledConsensusProofs.Execution.PreparedV4ProtectedVoteAtVoteCore
public import DecoupledConsensusProofs.Execution.PreparedV4ActualLiveAtConfirmation
public import DecoupledConsensusProofs.Execution.PreparedV4ActualActionOutputs

@[expose] public section

/-! # Closed prepared V4 actual-vote sources -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

theorem SettledBootstrapPreparedV4.voteSourcesSafeAt_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start d : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hd : start ≤ d) (hhor : Protocol.vote_time S.E d ≤ rho.horizon) :
    VoteSourcesSafeAt S rho (base + S.hc.η_SG) d P.erase := by
  exact SettledBootstrapPreparedV4.voteSourcesSafeAt_core_of_pins
    S adm hcom hboot hawake hfinality
    (SettledBootstrapPreparedV4.protectedVoteSlot_at_vote_core
      S adm hcom hboot hawake hfinality)
    (SettledBootstrapPreparedV4.liveConfirmedAtConfirmation_at_actual_vote_core
      S adm hcom hboot hawake hfinality hd hhor)
    (SettledBootstrapPreparedV4.actionOutputs_at_actual_vote_core
      S adm hcom hboot hawake hfinality hd hhor)
    hd hhor

#print axioms SettledBootstrapPreparedV4.voteSourcesSafeAt_core

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
