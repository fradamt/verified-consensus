module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.Alignment
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

/-! # Low proposal-tick transport facts
Timing and field-preservation facts processes an honest proposal without
post-healing or recovery dependencies.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every instant from the slot start through the view freeze belongs to that
slot. -/
theorem slotOf_of_proposal_before_freeze (E : Env V) (s : Slot) {p : Time}
    (hlo : Protocol.proposal_time E s ≤ p) (hhi : p < Protocol.view_freeze E s) :
    E.slotOf p = s := by
  have hbounds : ∀ a d q : Int, 0 < d → a ≤ q → q < a + 3 * d →
      0 ≤ q - a ∧ q - a < 4 * d := by
    intro a d q hd h1 h2
    omega
  obtain ⟨h0, h1⟩ := hbounds (E.t s) E.Δ p E.Δ_pos hlo hhi
  have hrw : p = 4 * E.Δ * (s : Time) + (p - E.t s) := by
    unfold Env.t slotStart
    ring
  rw [Env.slotOf, hrw]
  exact Proofs.Optimistic.slotOfTime_add E.Δ E.Δ_pos s _ h0 h1

/-- A delivery between the slot start and the view freeze reads that slot in
the receiver's store. -/
theorem delivery_store_slot_before_freeze
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {i : Nat} {o : Object V} {s : Slot} {t : Time}
    (hi : rho.events[i]? = some (Event.deliver w o t))
    (hlo : Protocol.proposal_time S.E s ≤ t)
    (hhi : t < Protocol.view_freeze S.E s) :
    (rho.stateBefore S i w).st.s = s := by
  have htick : Event.tick w (Protocol.proposal_time S.E s) ∈ rho.events :=
    adm.tick_total w hw _ (Proofs.Optimistic.publicTime_proposal_time S s)
      (Proofs.Optimistic.proposal_time_nonneg S.E s)
      (le_trans hlo (adm.in_horizon _ (List.mem_of_getElem? hi)).2)
  have hclock : Protocol.proposal_time S.E s ≤ (rho.stateBefore S i w).st.t :=
    tick_le_store_time S adm.toNamedScheduleWellFormed hi htick hlo
  have hup : (rho.stateBefore S i w).st.t ≤ t := by
    simpa [Event.time] using
      store_time_le_event_time S adm.toNamedScheduleWellFormed hi w
  have hslot := Proofs.NamedStoreBridge.slotOfClock_stateBefore S rho i w
  unfold Proofs.Optimistic.SlotOfClock at hslot
  show (rho.stateBefore S i w).st.core.s = s
  rw [hslot]
  exact slotOf_of_proposal_before_freeze S.E s hclock (lt_of_le_of_lt hup hhi)


end Protocol
end DecoupledConsensusModel

end
