module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.W4NamedExecution
public import DecoupledConsensusProofs.Protocol.Schedule.W4NamedInitialStage0

@[expose] public section

/-!
# The named fold at every slot from stage-0 data

This leaf composes the stage-0 initial fold with the available hybrid iterator.
The iterator owns the ordinary and ceiling supplies and retains the initial
base equality at every later slot.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.NamedRecoveryRead
open Protocol Proofs.HealingLemmas
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}


/-- The named fold at every in-horizon slot from the selected stage-0 records. -/
theorem w4NamedFoldAtEverySlotFrom_stage0
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {rGST gap q : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    (hqLate : fgSafetyProgressDeadline S rho rGST gap delayExtra + 3 ≤ q)
    {D : NamedBlock V} {carrier : V} {M0 : Height}
    (hhandoff : HealedTwoSlotHandoffPrepared S rho q D.erase carrier)
    (hboundary : W4NamedHandoffBoundaryCore S rho q
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0 D)
    (hbaseTiming :
      0 < S.hc.round_of (S.hc.opening_slot q + 3) ∧
      S.E.t_GST ≤ S.a
        (S.hc.round_of (S.hc.opening_slot q + 3) - 1) ∧
      Protocol.confirmation_time S.E (S.hc.opening_slot q + 3) ≤
        rho.horizon) :
    ∀ {s : Slot}, S.hc.opening_slot q + 3 ≤ s →
      Protocol.confirmation_time S.E (s - 1) ≤ rho.horizon →
      ∃ F : Slot → Block V, ∃ End : Block V,
        MovingSlotFoldAtN S rho
          (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
          (S.hc.opening_slot q + 3) s F End ∧
        F (S.hc.opening_slot q + 3) = D.erase := by
  obtain ⟨F0, End0, hfold0, hbaseEq0⟩ :=
    w4MovingSlotFoldAtN_boundary_initial_stage0 S adm hcom hfb hrec hdelay
      hpost hqLate hhandoff hboundary hbaseTiming
  exact w4NamedFoldAtEverySlotFrom_of_initial S adm hcom hfb hrec hdelay hpost
    hqLate hhandoff hboundary hbaseTiming hfold0 hbaseEq0

#print axioms w4NamedFoldAtEverySlotFrom_stage0

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
