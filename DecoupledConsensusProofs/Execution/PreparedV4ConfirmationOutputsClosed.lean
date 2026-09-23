module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.PreparedV4ConfirmationAnchor
public import DecoupledConsensusProofs.Execution.PreparedV4ConfirmationReadBand
public import DecoupledConsensusProofs.Protocol.Grades.PreparedV4ConfirmationOutputs

@[expose] public section

/-! # Closed prepared V4 confirmation outputs -/

namespace DecoupledConsensusModel.Proofs.HealingSurface.Handover

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

theorem SettledBootstrapPreparedV4.confirmationWalk_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    {s : Slot} (hs : start ≤ s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) {B : Block V}
    (hheads : ∀ x ∈ rho.honest,
      Block.Preceq B (voterHeadAt S rho x s)) :
    Block.Preceq B
        (namedConfirmationWalk S
          (Internal.NamedRecoveryRead.confirmationInputRead S rho v s) s) ∧
      confirmationEligible S.E
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).st.core s
        (namedConfirmationWalk S
          (Internal.NamedRecoveryRead.confirmationInputRead S rho v s) s) = true := by
  exact SettledBootstrapPreparedV4.confirmationWalk_core_of_pins
    S adm hcom hboot hawake hfinality
      (fun {s} hs' hhor' {w x} hw' hx' =>
        SettledBootstrapPreparedV4.preparedConfirmationAnchor_preceq_voterHeadAt_core
          S adm hcom hboot hawake hfinality hs' hhor' hw' hx')
      (fun {s} hs' hhor' {v x} hx' {X} hX hXrun =>
        SettledBootstrapPreparedV4.confirmationReadBand_le_voterHeadHeight_core
          S adm hcom hboot hawake hfinality hs' hhor' hx' hX hXrun)
      hs hhor hv hheads

theorem SettledBootstrapPreparedV4.genuineConfirmationAt_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    {s : Slot} (hs : start ≤ s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) :
    GenuineConfirmationAt S rho v s := by
  exact SettledBootstrapPreparedV4.genuineConfirmationAt_core_of_pins
    S adm hcom hboot hawake hfinality
      (fun {s} hs' hhor' {v} hv' {B} hheads =>
        SettledBootstrapPreparedV4.confirmationWalk_core
          S adm hcom hboot hawake hfinality hs' hhor' hv' hheads)
      hs hhor hv

theorem SettledBootstrapPreparedV4.liveConfirmed_preceq_at_confirmation_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start s : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hs : start ≤ s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest) {t : Time}
    (htlo : Protocol.confirmation_time S.E
      (S.hc.opening_slot (base + S.hc.η_SG)) ≤ t)
    (hthi : t < Protocol.confirmation_time S.E s) :
    Block.Preceq (rho.storeAt S w t).live_confirmed
      (rho.storeAt S v (Protocol.confirmation_time S.E s)).live_confirmed := by
  exact SettledBootstrapPreparedV4.liveConfirmed_preceq_at_confirmation_core_of_pins
    S adm hcom hboot hawake hfinality
      (fun {s} hs' hhor' {v} hv' {B} hheads =>
        SettledBootstrapPreparedV4.confirmationWalk_core
          S adm hcom hboot hawake hfinality hs' hhor' hv' hheads)
      hs hhor hv hw htlo hthi

#print axioms SettledBootstrapPreparedV4.confirmationWalk_core
#print axioms SettledBootstrapPreparedV4.genuineConfirmationAt_core
#print axioms SettledBootstrapPreparedV4.liveConfirmed_preceq_at_confirmation_core

end DecoupledConsensusModel.Proofs.HealingSurface.Handover

end
