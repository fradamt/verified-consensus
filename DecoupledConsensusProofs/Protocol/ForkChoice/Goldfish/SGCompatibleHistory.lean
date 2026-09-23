module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Store.HonestPoolActionBridge
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryRelativeMajorityProvenance
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FGWitnessCandidate

@[expose] public section

/-!
# SG compatibility from actual honest emission history

Pool provenance identifies each present honest vote without requiring absent
validators to vote or requiring all named heads to resolve. Compatible honest
history then controls fresh anchors, the raw-grade root fallback, and the
relative-majority anchor. Filtered activity may change between reads.

The history is a joint-induction input. These lemmas do not establish its
initial recovery bootstrap or the awake-duty window-majority producer.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Only actual honest SG emissions are constrained. No statement about a
nonparticipating validator's hypothetical action is required. -/
def HonestSGEmissionsCompatibleAtRound
    (S : Setup V) (rho : Run V) (r : Round) (B : Block V) : Prop :=
  ∀ v ∈ rho.honest,
    rho.emits S v (Object.attest (actionAttestationAt S rho v r)) (S.a r) →
      Block.compatible (actionSGBlockAt S rho v r) B = true

/-- A present honest SG vote has a compatible resolved head if its actual
emission is compatible. An unresolved head contributes no conflicting support. -/
theorem rootCompatible_of_emittedSGHistory_at_read
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {time : Time} {r : Round} {B : Block V}
    (hhistory : HonestSGEmissionsCompatibleAtRound S rho r B)
    {u : Protocol.SGVote V}
    (hu : u ∈ (rho.storeBeforeTime S w time).toHealing.sg_votes r)
    (huh : u.val_index ∈ rho.honest) :
    rootCompatible (rho.storeBeforeTime S w time).T B u.confirmed = true := by
  obtain ⟨huEq, hemit⟩ :=
    honestSGVote_actionEmission_of_mem_storeBeforeTime S adm huh hu rfl
  have hcompat := hhistory u.val_index huh hemit
  let C := actionSGBlockAt S rho u.val_index r
  have hconfirmed : u.confirmed = some C.root := by
    rw [huEq]
    rfl
  rw [hconfirmed]
  cases hfind : Block.find? (rho.storeBeforeTime S w time).T C.root with
  | none => simp only [rootCompatible, hfind]
  | some X =>
      have hXmem := find?_mem hfind
      obtain ⟨Xn, hXerase, hXrun⟩ :=
        Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hw time hXmem
      have hCmem : C ∈ (rho.storeBeforeTime S u.val_index (S.a r)).T :=
        actionSGBlockAt_mem_storeBeforeTime S rho u.val_index r
      obtain ⟨Cn, hCerase, hCrun⟩ :=
        Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed huh (S.a r) hCmem
      have hroot : Xn.root = Cn.root := by
        rw [← Proofs.NamedWire.erase_root Xn, ← Proofs.NamedWire.erase_root Cn,
          hXerase, hCerase]
        exact find?_root hfind
      have hnamed := adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
        Xn Cn hXrun hCrun Xn Cn (Or.inl (Proofs.NamedAncestry.named_self Xn))
          (Or.inr (Proofs.NamedAncestry.named_self Cn)) hroot
      have hXC : X = C := hXerase.symm.trans
        ((congrArg NamedBlock.erase hnamed).trans hCerase)
      simpa only [rootCompatible, hfind, hXC] using hcompat






/-- A relative graded block cannot conflict with a compatible interpreted
honest batch under the reader's window-majority premise. -/
theorem grade_compatible_of_batchCompatible_of_faulty_lt_m
    (E : Env V) {gv : Protocol.GradeView V} {hc : Protocol.HealConfig}
    {F : Block V} {Hon : Finset V} {r : Round} {B X : Block V}
    {p : DecoupledConsensusModel.Protocol.Phase}
    (hbatch : Internal.PhaseGrades.BatchCompatibleAt hc gv F Hon r
      (DecoupledConsensusModel.Protocol.late E hc r p) B)
    (hmajority : Internal.PhaseGrades.WindowMajorityAt E hc gv F Hon r
      (DecoupledConsensusModel.Protocol.late E hc r p))
    (hgrade : Internal.PhaseGrades.phaseGrade E hc gv F r p X = true) :
    Block.compatible X B = true := by
  by_contra hn
  have hconf : Block.conflicts X B = true := by
    rw [Bool.not_eq_true] at hn
    simp only [Block.conflicts, hn, Bool.not_false]
  have hfalse := Proofs.HealingLemmas.q7_grade_eq_false_of_conflicts
    E hc gv F Hon r B X p hbatch hmajority hconf
  rw [hfalse] at hgrade
  cases hgrade



#print axioms rootCompatible_of_emittedSGHistory_at_read

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
