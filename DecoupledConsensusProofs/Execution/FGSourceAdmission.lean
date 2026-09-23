module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeDelivery
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsProducers

@[expose] public section

/-!
# Admission of an honest FG source at later reads

An honest opening store already contains the exact FG source. The source
therefore reaches a reader by the action if the reader's finalized block
at its later read is below that source. No common frontier or no-rise cap
is needed. A source at most one height below the reader's frontier then
supplies viability for its protected ancestors.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A block in an honest strict store is admitted at a later honest read
after one network delay, provided the later finalized block is below it.
The later finalized bound covers every earlier admission guard. -/
theorem honestBlock_mem_after_delay_of_finalizedPreceq
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {p w : V} (hp : p ∈ rho.honest) (hw : w ∈ rho.honest)
    {sourceRead read : Time} {B : Block V}
    (hB : B ∈ (rho.storeBeforeTime S p sourceRead).T)
    (hpost : S.E.t_GST ≤ sourceRead)
    (hdelay : sourceRead + S.E.Δ ≤ read)
    (hhor : read ≤ rho.horizon)
    (hFB : Block.Preceq (rho.storeBeforeTime S w read).F B) :
    B ∈ (rho.storeBeforeTime S w read).T := by
  obtain ⟨n, hn, hbefore⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed sourceRead
  have hprocessed : B ∈ (rho.stateBefore S n p).st.core.T := by
    simpa only [Run.storeBeforeTime, hn] using hB
  obtain hgen | ⟨D, hDe, i, hi, ta, hacc⟩ :=
    Protocol.acceptsAt_block_of_processed_erased S rho p n hprocessed
  · subst B
    exact (Protocol.genesis_mem_and_stamp_storeBeforeTime
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed w read read).1
  have hta : ta < sourceRead := by
    obtain ⟨_, ⟨e, he, _, het⟩⟩ := hacc.1
    simpa only [het] using hbefore i e hi he
  have hpos : 0 < D.slot := by
    rw [← Proofs.NamedWire.erase_slot]
    exact Nat.zero_lt_of_lt (Protocol.parent_slot_lt_of_acceptsAt_block S hacc)
  have hFhist := GradeDeliveryRun.finalizedBelowAtDeliveries_of_finalizedPreceqAtRead
    S adm hdelay hFB (by rw [hDe]; exact Block.preceq_self B)
  have hadmit := Protocol.block_admittedBefore_of_accepted_after_cutoff
    S adm hp hw hpos hacc hta hpost rfl (hdelay.trans hhor) hFhist
  rw [hDe] at hadmit
  exact (Protocol.admittedBefore_mem_and_stamp_at
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hadmit hdelay).1

end HealingSurface
end Proofs

end DecoupledConsensusModel

end
