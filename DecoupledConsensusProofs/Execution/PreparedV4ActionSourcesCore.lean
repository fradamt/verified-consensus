module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.PreparedV4ProtectedVoteHorizonCore

@[expose] public section

/-! # Prepared V4 post-cut action sources
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

theorem SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start last d : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hd : start ≤ d) (hupper : d ≤ last + 1)
    {x : V} (hx : x ∈ rho.honest) :
    ∀ r, base + S.hc.η_SG ≤ r →
      S.a r < Protocol.vote_time S.E (d + 1) →
      (∀ w ∈ rho.honest,
        NamedRun.emits S rho w
          (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
        Block.Preceq (actionSGBlockAt S rho w r) (voterHeadAt S rho x d)) ∧
      (∀ w ∈ rho.honest,
        Block.Preceq (Protocol.get_fg_root
          (actionStoreAt S rho w r).st.core.toHealing.toFG)
          (voterHeadAt S rho x d) ∧
        ∀ T, fgConfirmationWitness S (actionStoreAt S rho w r) = some T →
          Block.Preceq T (voterHeadAt S rho x d)) :=
  SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_aux
    S adm hcom hboot hawake hfinality hhor hd hupper hx

#print axioms SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_core

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
