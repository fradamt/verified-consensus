module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGTargetCanonicality
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionActivity
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore

@[expose] public section

/-!
# SG-target canonicality at quiet concrete reads

This file removes exact common FG-root equality from the selected-G2 and
FG-root-clear branches of SG-target canonicality. The quiet interface names
only the finite action and vote reads used by one target slot. At an action
read, `GradeFormsAt` puts the common grade above the actual FG root, so the
root arm of `FinalityFilterNoninterferenceAtRead` collapses to filtered
membership of the selected G2. At the vote read, the other arm is consumed
directly by the actual root-to-head theorem.

The same argument does not close the genuine-clear branch from finality-filter
noninterference alone. Its exact remaining read-local case is recorded below:
the selected G2 is below the actual vote FG root but is not active, while that
root is strictly below the active clear target. In that case G2 persistence
cannot make `fresh_anchor` total, and the MajoritySG fallback anchor need not
be compatible with the clear target. This is same-height root movement, not
an `h_max` rise.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]






/-! ## Named action-read quietness -/







/-- The prepared clear branch collapses to the selected Q2 when the action's
live value is its FG root. -/
theorem clearTarget_eq_fgRoot_and_selectedG2_of_selectedG2
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (hr : 0 < r) (hhor : S.a r ≤ rho.horizon)
    {u : V} (hu : u ∈ rho.honest) {Q T R : Block V}
    (hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho u r) r = some Q)
    (hclear : Protocol.deepest_clear
      (some (PhaseGrades.nodeAnchor S (actionReadAt S rho u r) r))
      (actionReadAt S rho u r).st.core.live_confirmed
      (PhaseGrades.nodeClear S (actionReadAt S rho u r) r) = some T)
    (hRroot : R = Protocol.get_fg_root
      (Proofs.Optimistic.confStore S rho u
        (S.hc.opening_slot r)).toHealing.toFG)
    (hRlive : R = (actionReadAt S rho u r).st.core.live_confirmed) :
    T = R ∧ T = Q := by
  let n := actionReadAt S rho u r
  have hQaction : Q ∈ PhaseGrades.filteredTree n := by
    simpa only [n] using actionQ2_mem_filteredTree S rho u r hQ
  have hrootQ : Block.Preceq
      (Protocol.get_fg_root n.st.core.toHealing.toFG) Q :=
    Proofs.Records.preceq_get_fg_root_of_mem_filtered hQaction
  have hQcheck : DecoupledConsensusModel.Protocol.grade2Block
      (Internal.NamedJointOutage.checkpoint S rho u r).st.core.toHealing
      (DecoupledConsensusModel.Protocol.readFrame
        (Internal.NamedJointOutage.checkpoint S rho u r).cache
        (Internal.NamedJointOutage.checkpoint S rho u r).st.core.toHealing r) =
      some Q := by
    change DecoupledConsensusModel.Protocol.grade2Block n.st.core.toHealing
      (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r) = some Q
    simpa only [n, PhaseGrades.nodeQ2, PhaseGrades.nodeRead,
      Protocol.grade2_block_with, NamedProfile.gradeContract,
      DecoupledConsensusModel.Protocol.frameContract,
      DecoupledConsensusModel.Protocol.frameGradeRead] using hQ
  have hQA := NamedOutageClosure.grade2_preceq_anchor_at_checkpoint
    S rho adm.toNamedAdmissibleCore u hu 0 r
      ⟨hr, Proofs.HealingLemmas.a_nonneg S r, hhor⟩ Q hQcheck
  have hQA' : Block.Preceq Q (PhaseGrades.nodeAnchor S n r) := by
    simpa only [Internal.NamedJointOutage.checkpoint, n,
      PhaseGrades.nodeAnchor, PhaseGrades.nodeRead,
      actionRead_readFrame_eq_checkpoint S rho u r] using hQA
  have hAT : Block.Preceq (PhaseGrades.nodeAnchor S n r) T := by
    have hmem := Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hclear)
    simpa only [Option.elim_some] using hmem.2.1
  have hrootEq : Protocol.get_fg_root n.st.core.toHealing.toFG =
      Protocol.get_fg_root
        (Proofs.Optimistic.confStore S rho u
          (S.hc.opening_slot r)).toHealing.toFG := by
    change Protocol.get_fg_root
      (actionStoreAt S rho u r).st.core.toHealing.toFG = _
    rw [actionStoreAt_eq_update_confirmation_confStore]
    rfl
  have hRQ : Block.Preceq R Q := by
    rw [hRroot, ← hrootEq]
    exact hrootQ
  have hTR : Block.Preceq T R := by
    rw [hRlive]
    simpa only [n] using Proofs.Engine.deepest_clear_preceq hclear
  have hRT : Block.Preceq R T :=
    Block.preceq_trans hRQ (Block.preceq_trans hQA' hAT)
  refine ⟨Block.preceq_antisymm hTR hRT, ?_⟩
  exact Block.preceq_antisymm (Block.preceq_trans hTR hRQ)
    (Block.preceq_trans hQA' hAT)



/-
/-- Complete FG-root-clear cone theorem. Store-local selector geometry first
identifies the clear target with the selected G2; the quiet selected-G2 theorem
then supplies the target cone. -/
theorem honestVotesCone_of_fgRootClear_finalityFilterQuiet
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {r: Round} (ready: GradeRoundReady S rho r)
    {J: Block V} (hforms: GradeFormsAt S rho r J)
    {u: V} (hu: u ∈ rho.honest) {Q T R: Block V}
    (hQ: Protocol.grade2_block S.E S.hc
      (actionStoreAt S rho u r).toHealing r = some Q)
    (hclear: Protocol.deepest_clear
      (some (Protocol.get_sg_root S.E S.hc
        (actionStoreAt S rho u r).toHealing r))
      (actionStoreAt S rho u r).live_confirmed
      (fun B => Protocol.g0_clear S.E
        (actionStoreAt S rho u r).toHealing.gradeView S.hc r B) = some T)
    (hRroot: R = Protocol.get_fg_root
      (Proofs.Optimistic.confStore S rho u (S.hc.opening_slot r)).toHealing.toFG)
    (hRlive: R = (actionStoreAt S rho u r).live_confirmed)
    {s: Slot}
    (hslo: S.hc.opening_slot r + 1 ≤ s)
    (hshi: s < S.hc.opening_slot (r + 1))
    (hhor: Protocol.vote_time S.E s ≤ rho.horizon)
    (hquiet: SelectedG2FinalityFilterQuietAt S rho r s Q):
    NamedHonestVotesCone S rho s (fun X => Block.Preceq T X):= by
  have hTQ:=
    (clearTarget_eq_fgRoot_and_selectedG2_of_selectedG2
      S hQ hclear hRroot hRlive).2
  have hcone:= honestVotesCone_of_selectedActionG2_finalityFilterQuiet
    S adm ready hforms hu hQ hslo hshi hhor hquiet
  simpa only [hTQ] using hcone

-/




end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

#print axioms clearTarget_eq_fgRoot_and_selectedG2_of_selectedG2

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
