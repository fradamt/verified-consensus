module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradePersistence
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FinalityFilterRetention
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

/-!
# Windowed named action activity and sources

`NamedGradeFormsAt` reads the relative grade at the G2-domain read. The
filtered-tree fact needed by the action is a separate read-local retention
fact. This module keeps that distinction explicit and then adds the named
run-block witness required by the proof consumers.

The retention hypothesis is the same finality-filter window fact used by the
pre-rewrite proofs. It is not a new protocol assumption and it does not
assert transport from the domain read to the action read.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A retained action read supplies the filtered-tree membership consumed by a
named grade proof. -/
theorem namedGradeFormsAt_actionStore_of_window
    (S : Setup V) {rho : Run V} {r : Round} {P : Block V}
    (hforms : NamedGradeFormsAt S rho r P)
    {v : V} (hv : v ∈ rho.honest)
    (hwindow : FinalityFilterRetainedAtRead S rho v (S.a r) P) :
    P ∈ PhaseGrades.filteredTree (actionReadAt S rho v r) := by
  have hretained : P ∈ Protocol.get_filtered_block_tree
      (healStoreAt S rho v r).toFG := by
    simpa only [FinalityFilterRetainedAtRead, healStoreAt,
      PhaseGrades.filteredTree, actionReadAt, Run.storeBeforeTime] using hwindow
  exact activeAtAction_of_retainedAtRead S hretained

private theorem actionFGSource_mem_actionRead
    (S : Setup V) {rho : Run V} {r : Round} {v : V} {Q : Block V}
    (hsource : PhaseGrades.nodeFGSource S (actionReadAt S rho v r) r = some Q) :
    Q ∈ (actionReadAt S rho v r).st.core.T := by
  let n := actionReadAt S rho v r
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg n.st := by
    apply Proofs.NamedConfirmationMembership.invariant_update
    exact Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ (S.a r)
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a r) v).1
  change Protocol.fg_source_with (NamedProfile.gradeContract n.cache)
      S.E S.hc n.st.core.toHealing r
      (Protocol.grade2_block_with (NamedProfile.gradeContract n.cache)
        S.E S.hc n.st.core.toHealing r) = some Q at hsource
  exact NamedActionSources.frame_fg_source_mem S n.cache n.st r hinv hsource

/-- A named grade plus the action read's retention fact produces a nonempty
action FG source together with its named run-block witness. -/
theorem exists_actionSource_of_namedGradeFormsAt (S : Setup V)
    {rho : Run V} (core : NamedAdmissibleCore S rho) {r : Round} (hr : 0 < r)
    (hhor : S.a r ≤ rho.horizon) {P : Block V}
    (hforms : NamedGradeFormsAt S rho r P) {v : V} (hv : v ∈ rho.honest)
    (hwindow : FinalityFilterRetainedAtRead S rho v (S.a r) P) :
    ∃ Q : Block V,
      PhaseGrades.nodeFGSource S (actionReadAt S rho v r) r = some Q ∧
        ∃ D : NamedBlock V, D.erase = Q ∧ RunBlock S rho D := by
  have hactive := namedGradeFormsAt_actionStore_of_window
    S hforms hv hwindow
  obtain ⟨Q, hsource⟩ := exists_actionFGSource_of_namedGradeFormsAt
    S core hr hhor hforms hv hactive
  have hQmem : Q ∈ (actionReadAt S rho v r).st.core.T :=
    actionFGSource_mem_actionRead S hsource
  have hQmem' : Q ∈ (rho.storeBeforeTime S v (S.a r)).core.T := by
    simpa only [actionReadAt, NamedActionReads.actionReadAt,
      NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hQmem
  obtain ⟨D, hDerase, hDrun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
      core.toNamedScheduleWellFormed hv (S.a r) hQmem'
  exact ⟨Q, hsource, D, hDerase, hDrun⟩

end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms namedGradeFormsAt_actionStore_of_window
#print axioms exists_actionSource_of_namedGradeFormsAt
end DecoupledConsensusModel.Proofs.HealingSurface

end
