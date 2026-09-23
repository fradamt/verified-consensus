module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGRepresentation
public import DecoupledConsensusProofs.Execution.EmissionShape

@[expose] public section

/-!
# Post-GST relay

The GST-zero availability proof specializes every relay deadline with
`t_GST = 0`. A post-healing suffix needs the same facts only for objects whose
source event is already at or after GST. This file records that exact
generalization without changing the execution model. The conclusion is
`NamedRun.actualHandlesAt`, not `Run.processes`: `Synchrony.broadcast`,
`relay_block`, `relay_gf_vote` and `relay_attest` conclude actual-handler
calls, matching the already-restated `broadcast_gst_zero` family in
`Availability/Sync.lean`.

The relative-SG representation chain is now stated over `NamedAttestation`
and `NamedRun.actualHandlesAt`. `NamedEmissionShape` supplies the emitted-row
shape and the CarriesRow-aware `NamedSGArrival` producer retains the row at
the actual receiver call. The five post-GST declarations below use this
route and keep the original timing and horizon hypotheses.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Delivery-parametric interface -/

/-- Honest delivery before a fixed cap. This is the delivery surface used by
the bounded safety folds. It is definitionally the healthy-prefix contract:
the separate name records that consumers must not inspect `t_GST`. -/
abbrev HonestDeliveryBefore (S : Setup V) (rho : Run V) (cap : Time) : Prop :=
  NamedHealthyPrefixDelivery S rho cap



/-! ## Relay from a post-GST source -/

/-- An honest emission at or after GST reaches every honest node before one
network delay. -/
theorem broadcast_after_gst (S : Setup V) {rho : Run V}
    (adm : Proofs.AdmissibleCore S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {o : Object V} {t : Time} (hpost : S.E.t_GST ≤ t)
    (hemit : rho.emits S v o t) (hhor : t + S.E.Δ ≤ rho.horizon)
    (hguard : NamedReceipt.excludes
      (rho.stateBeforeTime S (t + S.E.Δ) w).st o = false) :
    ∃ t', t ≤ t' ∧ t' < t + S.E.Δ ∧
      ∃ j : Nat, NamedRun.actualHandlesAt S rho j w o t' := by
  have hmax : max t S.E.t_GST = t := max_eq_left hpost
  have h := adm.broadcast v hv o t hemit w hw (by simpa only [hmax] using hhor)
    (by simpa only [hmax] using hguard)
  simpa only [hmax] using h


/-- An accepted Goldfish vote forwarded at or after GST reaches every honest
node before one network delay. -/
theorem relay_gf_vote_after_gst_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {i : Nat} {u : GoldfishVote V} {t : Time} (hpost : S.E.t_GST ≤ t)
    (hacc : NamedRun.acceptsAt S rho i v (Object.gfVote u) t)
    (hunaccepted : NamedReceipt.processed
      (rho.stateBefore S (i + 1) w).st (Object.gfVote u) = false)
    (hhor : t + S.E.Δ ≤ rho.horizon) :
    ∃ t', t ≤ t' ∧ t' < t + S.E.Δ ∧
      ∃ j : Nat, NamedRun.actualHandlesAt S rho j w (Object.gfVote u) t' := by
  have hmax : max t S.E.t_GST = t := max_eq_left hpost
  have h := adm.relay_gf_vote v hv i u t hacc w hw hunaccepted
    (by simpa only [hmax] using hhor) rfl
  simpa only [hmax] using h

theorem relay_gf_vote_after_gst (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {i : Nat} {u : GoldfishVote V} {t : Time} (hpost : S.E.t_GST ≤ t)
    (hacc : NamedRun.acceptsAt S rho i v (Object.gfVote u) t)
    (hunaccepted : NamedReceipt.processed
      (rho.stateBefore S (i + 1) w).st (Object.gfVote u) = false)
    (hhor : t + S.E.Δ ≤ rho.horizon) :
    ∃ t', t ≤ t' ∧ t' < t + S.E.Δ ∧
      ∃ j : Nat, NamedRun.actualHandlesAt S rho j w (Object.gfVote u) t' :=
  relay_gf_vote_after_gst_core S adm.toNamedAdmissibleCore hv hw hpost
    hacc hunaccepted hhor

#print axioms relay_gf_vote_after_gst_core

/-- An accepted attestation forwarded at or after GST reaches every honest
node before one network delay. -/
theorem relay_attest_after_gst (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {i : Nat} {a : NamedAttestation V} {t : Time}
    (hpost : S.E.t_GST ≤ t)
    (hacc : NamedRun.acceptsAt S rho i v (Object.attest a) t)
    (hunaccepted : NamedReceipt.processed
      (rho.stateBefore S (i + 1) w).st (Object.attest a) = false)
    (hhor : t + S.E.Δ ≤ rho.horizon) :
    ∃ t', t ≤ t' ∧ t' < t + S.E.Δ ∧
      ∃ j : Nat, NamedRun.actualHandlesAt S rho j w (Object.attest a) t' := by
  have hmax : max t S.E.t_GST = t := max_eq_left hpost
  have h := adm.relay_attest v hv i a t hacc w hw hunaccepted
    (by simpa only [hmax] using hhor) rfl
  simpa only [hmax] using h


/-! ## Relative-SG representation from post-GST actions -/







end Protocol
end DecoupledConsensusModel

end
