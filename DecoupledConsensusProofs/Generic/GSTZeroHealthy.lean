module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Execution.NamedAdmissible

@[expose] public section

/-! Layer A environmental bridge: GST-zero global named synchrony gives
healthy delivery through the full
run horizon. This is a direct contract conversion, not an outage
specialization. -/
namespace DecoupledConsensusModel.Proofs.NamedGSTZeroHealthy
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-- At GST zero, every global named synchrony deadline is its send time plus
one delay. Event well-formedness supplies nonnegative send times. -/
theorem healthyPrefixDelivery_of_gstZero
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (hgst : S.E.t_GST = 0) :
    NamedHealthyPrefixDelivery S rho rho.horizon where
  broadcast := by
    intro v hv o t hemit w hw hhor hguard
    obtain ⟨i, hi, ho⟩ := hemit
    have h0 : 0 ≤ t := by
      simpa only [Generic.Event.time, NamedEvent.time] using
        (core.in_horizon (.tick v t) (List.mem_of_getElem? hi)).1
    have hmax : max t S.E.t_GST = t := by
      rw [hgst]
      exact max_eq_left h0
    have h := core.broadcast v hv o t ⟨i, hi, ho⟩ w hw (by rw [hmax]; exact hhor)
      (by rw [hmax]; exact hguard)
    rw [hmax] at h
    exact h
  relay_block := by
    intro v hv i B t hacc w hw hmissing hhor hguard
    obtain ⟨e, he, _, het⟩ := hacc.1.2
    have htime : NamedEvent.time e = t := het
    have h0 : 0 ≤ t := by
      simpa only [htime] using (core.in_horizon e (List.mem_of_getElem? he)).1
    have hmax : max t S.E.t_GST = t := by
      rw [hgst]
      exact max_eq_left h0
    have h := core.relay_block v hv i B t hacc w hw hmissing
      (by rw [hmax]; exact hhor) (by rw [hmax]; exact hguard)
    rw [hmax] at h
    exact h
  relay_gf_vote := by
    intro v hv i u t hacc w hw hmissing hhor _
    obtain ⟨e, he, _, het⟩ := hacc.1.2
    have htime : NamedEvent.time e = t := het
    have h0 : 0 ≤ t := by
      simpa only [htime] using (core.in_horizon e (List.mem_of_getElem? he)).1
    have hmax : max t S.E.t_GST = t := by
      rw [hgst]
      exact max_eq_left h0
    have h := core.relay_gf_vote v hv i u t hacc w hw hmissing
      (by rw [hmax]; exact hhor) rfl
    rw [hmax] at h
    exact h
  relay_attest := by
    intro v hv i a t hacc w hw hmissing hhor _
    obtain ⟨e, he, _, het⟩ := hacc.1.2
    have htime : NamedEvent.time e = t := het
    have h0 : 0 ≤ t := by
      simpa only [htime] using (core.in_horizon e (List.mem_of_getElem? he)).1
    have hmax : max t S.E.t_GST = t := by
      rw [hgst]
      exact max_eq_left h0
    have h := core.relay_attest v hv i a t hacc w hw hmissing
      (by rw [hmax]; exact hhor) rfl
    rw [hmax] at h
    exact h

end DecoupledConsensusModel.Proofs.NamedGSTZeroHealthy

end
