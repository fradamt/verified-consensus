module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.RoundBase
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RoundStep
public import DecoupledConsensusProofs.Protocol.Grades.SupportCarry
public import DecoupledConsensusProofs.Objects.IntervalInduction
public import DecoupledConsensusProofs.Execution.FinalizedViable
public import DecoupledConsensusProofs.Protocol.Handlers.FrozenRootOrder
public import DecoupledConsensusProofs.Protocol.Grades.Interpolation
public import DecoupledConsensusProofs.Protocol.Schedule.RecordAtBoundary
public import DecoupledConsensusInternal.Legacy.Assumptions.Regimes

@[expose] public section


namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The frozen post-GST certificate boundary -/








/-- Named synchrony gives a healthy delivery window for every source at or after
GST. The `max` in each synchrony deadline reduces to the source time. -/
theorem healthyWindowDelivery_after_gst (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) :
    NamedHealthyWindowDelivery S rho S.E.t_GST rho.horizon where
  broadcast := by
    intro v hv o t hemit w hw hpost hhor hguard
    have hmax : max t S.E.t_GST = t := max_eq_left hpost
    have h := core.toNamedSynchrony.broadcast v hv o t hemit w hw
      (by simpa only [hmax] using hhor)
      (by simpa only [hmax] using hguard)
    simpa only [hmax] using h
  relay_block := by
    intro v hv i B t hacc w hw hmissing hpost hhor hguard
    have hmax : max t S.E.t_GST = t := max_eq_left hpost
    have h := core.toNamedSynchrony.relay_block v hv i B t hacc w hw hmissing
      (by simpa only [hmax] using hhor)
      (by simpa only [hmax] using hguard)
    simpa only [hmax] using h
  relay_gf_vote := by
    intro v hv i u t hacc w hw hmissing hpost hhor _
    have hmax : max t S.E.t_GST = t := max_eq_left hpost
    have h := core.toNamedSynchrony.relay_gf_vote v hv i u t hacc w hw hmissing
      (by simpa only [hmax] using hhor) rfl
    simpa only [hmax] using h
  relay_attest := by
    intro v hv i a t hacc w hw hmissing hpost hhor _
    have hmax : max t S.E.t_GST = t := max_eq_left hpost
    have h := core.toNamedSynchrony.relay_attest v hv i a t hacc w hw hmissing
      (by simpa only [hmax] using hhor) rfl
    simpa only [hmax] using h

#print axioms healthyWindowDelivery_after_gst

/-! ## Post-GST SG arrival -/

/- The proof is the deadline proof with the delivery source changed to the
windowed synchrony bridge. The remaining row, stamp, and raw-input steps are
the named SG-arrival exports. -/



/-! ## Viability of a stable root at its write -/

/- The stable-root write is either an active prefix of the filtered tree or the
   FG root. The latter is viable from the finalized-root invariant, or from
   the named justified-root producer in the cascade branch. -/


/-! ## Stable roots above a frame floor -/





end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
