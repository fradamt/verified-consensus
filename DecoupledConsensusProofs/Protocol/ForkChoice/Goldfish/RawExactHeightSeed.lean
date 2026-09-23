module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FinalityFilterRetention
public import DecoupledConsensusProofs.Protocol.Grades.RawHeightProgressCore
public import DecoupledConsensusProofs.Protocol.ChainState.RawHeightCoverage
public import DecoupledConsensusProofs.Execution.ReleasedCertificateHeightProgress
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RawProposerSelection
public import DecoupledConsensusProofs.Protocol.ChainState.RecurringFinality
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusInternal.Definitions.NamedLifecycle

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Raw exact-height lifecycle seed

This file keeps the Claim-4 lifecycle as an explicit input. It does not derive
that lifecycle from recurrence. A recurrent proposer carrier may be selected
outside this module, with its opening supplied as the bounded next proposal.

The first lifecycle proposal is allowed to have derived height `M - 1`. In the
no-progress branch, the selected read window keeps it active, its persisted
common grade puts it below the next honest proposal parent, and the public
height cap leaves only two parent heights. A parent at `M - 1` crosses to `M`
through exact action coverage. A parent at `M` already forces the accepted
next lifecycle proposal to have exact height `M`. Otherwise the retained
right-hand result is the local raw height-filter progress witness.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades

variable {V : Type} [DecidableEq V] [Fintype V]





/-- An honest accepted proposal's derived height is bounded by the inclusive
public honest frontier at its proposal time. -/
theorem honestProposedBlock_height_le_honestHMaxAt
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hs : 0 < s)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E s ≤ rho.horizon)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B) :
    (Protocol.derive_named S.E S.cfg B).h ≤
      honestHMaxAt S rho (Protocol.proposal_time S.E s) := by
  obtain ⟨i, hacc⟩ :=
    Protocol.acceptsAt_proposedBlock S adm hs hprop hhor hB
  have hBmem : B ∈
      (rho.stateBefore S (i + 1) (S.E.proposer s)).st.bodies := by
    simpa only [Execution.NamedReceipt.processed, decide_eq_true_eq]
      using hacc.2.2
  have hheightLe :
      (Protocol.derive_named S.E S.cfg B).h ≤
        (rho.stateBefore S (i + 1) (S.E.proposer s)).st.h_max :=
    Proofs.NamedStoreBridge.heights_le_hMax_stateBefore S rho (i + 1)
      (S.E.proposer s) B hBmem
  have hlocalLe :
      (rho.stateBefore S (i + 1) (S.E.proposer s)).st.h_max ≤
        honestHMaxBeforeIndex S rho (i + 1) :=
    localHMax_le_honestHMaxBeforeIndex S rho (i + 1) hprop
  obtain ⟨_, e, hie, _, hetime⟩ := hacc.1
  have hi : i < inclusiveEventIndex rho
      (Protocol.proposal_time S.E s) := by
    unfold inclusiveEventIndex
    exact Proofs.Optimistic.index_lt_stateAt_length S adm.toNamedScheduleWellFormed hie
      (le_of_eq hetime)
  have hprefixLe : honestHMaxBeforeIndex S rho (i + 1) ≤
      honestHMaxBeforeIndex S rho
        (inclusiveEventIndex rho (Protocol.proposal_time S.E s)) :=
    honestHMaxBeforeIndex_mono S rho (Nat.succ_le_iff.mpr hi)
  rw [honestHMaxAt_eq_honestHMaxBeforeIndex
    S adm.toNamedScheduleWellFormed]
  exact hheightLe.trans (hlocalLe.trans hprefixLe)



namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms honestProposedBlock_height_le_honestHMaxAt
end DecoupledConsensusModel.Proofs.HealingSurface

end HealingSurface
end Proofs
end DecoupledConsensusModel

end


