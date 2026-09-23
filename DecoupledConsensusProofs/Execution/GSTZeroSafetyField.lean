module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.SafetyRegimes
public import DecoupledConsensusProofs.Protocol.Grades.GSTZeroPreparedWalk
public import DecoupledConsensusProofs.Objects.AdmissibleCore

@[expose] public section

/-! # Green GST-zero safety field assembly, prebuilt over pins -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

theorem gstZeroSafety_of_pins
    (hlatest : ∀ (S : Setup V) (rho : Run V), WeakGenesis S rho →
      LatestAtProposalField S rho 0)
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
  let h : WeakGenesis S rho :=
    { execution := ExecutionValid.ofNamedAdmissibleCore adm
      synchrony := adm.toNamedSynchrony
      committees := hcom
      gstZero := hgst
      windows := hawake }
  exact
    { availableChain := havailableChain
      availableConfirmations := havailableConfirmations
      selectionChain := hselectionChain
      confirmationFields := hconfirmationFields
      latestAtProposal := hlatest S rho h
      liveMonotone := hliveMonotone
      liveAtConfirmation := hliveAtConfirmation
      proposalReads := hproposalReads
      outputCompatible := houtputCompatible
      outputMonotone := houtputMonotone
      userProposals := huserProposals }

#print axioms gstZeroSafety_of_pins

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
