module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.WeakGenesisAvailabilityNamed
public import DecoupledConsensusProofs.Objects.AdmissibleCore
public import DecoupledConsensusProofs.Protocol.Schedule.WeakGenesisReadSafetyNamed

@[expose] public section

/-! # Closed GST-zero safety over prepared named reads -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The four directed weak-genesis fields close the full GST-zero safety
surface. -/
theorem gstZeroSafety
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest) (hgst : S.E.t_GST = 0)
    (hawake : ∀ r, 0 < r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r) :
    GSTZeroGuarantees S rho := by
  let h : WeakGenesis S rho :=
    { execution := ExecutionValid.ofNamedAdmissibleCore adm
      synchrony := adm.toNamedSynchrony
      committees := hcom
      gstZero := hgst
      windows := hawake }
  exact gstZeroSafety_of_fourFields S adm hcom hgst hawake
    (WeakGenesis.availableConfirmationsFrom_of_weakGenesis_named S h)
    (fun v hv t t' ht =>
      WeakGenesis.liveConfirmed_mono_of_weakGenesis_named S h hv ht)
    (fun s hs hhor u hu v hv t ht =>
      WeakGenesis.liveConfirmed_preceq_at_confirmation_of_weakGenesis_named
        S h hs hhor hu hv ht)
    (WeakGenesis.honestProposalReadSafety_of_weakGenesis_named S h)

#print axioms gstZeroSafety

/-- Weak genesis supplies exactly the inputs of the closed GST-zero theorem. -/
theorem gstZeroGuarantees_of_weakGenesis (S : Setup V) :
    ∀ rho, WeakGenesis S rho → GSTZeroGuarantees S rho := by
  intro rho h
  exact gstZeroSafety S h.core h.committees h.gstZero h.windows

#print axioms gstZeroGuarantees_of_weakGenesis

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
