module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.GSTZeroSafetyField
public import DecoupledConsensusProofs.Execution.WeakGenesisLatestAtProposalClosed

@[expose] public section

/-! # GST-zero safety assembly over the ten red-cone fields -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

theorem gstZeroSafety_of_tenFields
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest) (hgst : S.E.t_GST = 0)
    (hawake : ∀ r, 0 < r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (havailableChain : AvailableChainFrom S rho 0)
    (havailableConfirmations : AvailableConfirmationsFrom S rho 0)
    (hselectionChain : ∀ v ∈ rho.honest, ∀ i B,
      ActualConfirmationSelection S rho v i B →
      ∀ w ∈ rho.honest, ∀ j C,
        ActualConfirmationSelection S rho w j C →
        Block.compatible B C = true)
    (hconfirmationFields : ∀ last,
      Protocol.confirmation_time S.E last ≤ rho.horizon →
      ∀ t u, t ≤ Protocol.confirmation_time S.E last →
      u ≤ Protocol.confirmation_time S.E last →
      ∀ v ∈ rho.honest, ∀ w ∈ rho.honest,
        Block.compatible (rho.storeAt S v t).latest_confirmed
            (rho.storeAt S w u).latest_confirmed = true ∧
        Block.compatible (rho.storeAt S v t).live_confirmed
            (rho.storeAt S w u).live_confirmed = true ∧
        Block.compatible (rho.storeAt S v t).latest_confirmed
            (rho.storeAt S w u).live_confirmed = true)
    (hliveMonotone : ∀ v ∈ rho.honest, ∀ t t', t ≤ t' →
      Block.Preceq (rho.storeAt S v t).live_confirmed
        (rho.storeAt S v t').live_confirmed)
    (hliveAtConfirmation : ∀ s, 0 < s →
      Protocol.confirmation_time S.E s ≤ rho.horizon →
      ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t,
      t < Protocol.confirmation_time S.E s →
      Block.Preceq (rho.storeAt S u t).live_confirmed
        (rho.storeAt S v
          (Protocol.confirmation_time S.E s)).live_confirmed)
    (hproposalReads : ∀ s, 0 < s →
      Protocol.confirmation_time S.E s ≤ rho.horizon →
      S.E.proposer s ∈ rho.honest → HonestProposalReadSafety S rho s)
    (houtputCompatible : ConfirmedOutputCompatibleFrom S rho 0)
    (houtputMonotone : ConfirmedOutputMonotoneFrom S rho 0)
    (huserProposals : UserProposalsConfirmedAfter S rho 0) :
    GSTZeroGuarantees S rho := by
  exact gstZeroSafety_of_pins
    WeakGenesis.latestAtProposalField_of_weakGenesis
    S adm hcom hgst hawake havailableChain havailableConfirmations
    hselectionChain hconfirmationFields hliveMonotone
    hliveAtConfirmation hproposalReads houtputCompatible
    houtputMonotone huserProposals

#print axioms gstZeroSafety_of_tenFields

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
