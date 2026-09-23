module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGProposalLifecycle
public import DecoupledConsensusProofs.Protocol.Grades.RelativeCarrierWindowGateOff
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FixedHeightRootOpeningParent

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Height-progress lifecycle closure: the `g0ClearAtAction` pin

The lifecycle producer
`fixedHeightJustificationRoot_boundedProposalLifecycle_of_proposerRecurrence_of_faultBound`
(`FixedHeightRootClaimFourOuterRun.lean:36-106`) carries the pinned premise

```lean
(_of_g0ClearAtAction: ∀ (q: Round) (P: NamedBlock V),
  proposedBlockAt S rho (S.hc.opening_slot q) = some P →
  ∀ v ∈ rho.honest,
    nodeClear S (actionReadAt S rho v q) q P.erase = true)
```

This module carries that premise as far as the current cone allows.

`g0ClearAtAction_of_relativeCarrierWindow` below is the whole protocol
argument, at one arbitrary round `q`: every frozen G0 root of an honest
action read at round `q` lies below an honest round-`(q - 1)` action carrier
(the relative grade-formation interface), every such carrier lies below the
parent the round-`q` opening proposer selected, and that parent lies below the
proposal itself, so the proposal is compatible with the frozen root and the
G0 veto never fires. `GradeFormingMajority` — the second input of the
carrier interface — is discharged internally from `Admissible` and
`BelowOneThird`.

Two inputs stay open, and they are the reason the pin is NOT closed here.
See the Open record at the end of this file.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open Internal.NamedOutageEntry
open Internal.NamedRecoveryRead
open Protocol
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- A named block's parent field is one of its own ancestors after erasure. -/
private theorem g0Closure_parent_erase_preceq (P : NamedBlock V) :
    Block.Preceq P.parent.erase P.erase := by
  cases P with
  | genesis => exact Block.preceq_self _
  | node parent slot root votes support rows proposer =>
      exact Proofs.NamedWire.erase_preceq
        (Proofs.NamedAncestry.named_extend slot root votes support rows proposer
          (Proofs.NamedAncestry.named_self parent))

/-- The parent the proposal duty selected is below the block it built. -/
theorem proposedParent_preceq_proposedBlockAt
    (S : Setup V) (rho : Run V) (s : Slot) {P : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P) :
    Block.Preceq (proposedParent S rho s) P.erase := by
  obtain ⟨parent, hparent, hparentErase⟩ := proposedBlockAt_parent S rho s hP
  have hparentEq : P.parent = parent := by
    cases P with
    | genesis => simp only [NamedBlock.parent?, reduceCtorEq] at hparent
    | node p slot root votes support rows proposer =>
        simpa only [NamedBlock.parent, NamedBlock.parent?, Option.some.injEq]
          using hparent
  rw [← hparentErase, ← hparentEq]
  exact g0Closure_parent_erase_preceq P

/-- The G0 veto never fires against the round-`q` opening proposal at an
honest action read.

This is `NamedSGProposalLifecycleInputs.g0ClearAtAction`
(`SGProposalLifecycleRun.lean:918`) with the lifecycle-inputs bundle replaced
by exactly the two facts its proof uses — the relative carrier window of the
preceding round and the parent cover of the honest round-`(q - 1)` action
carriers — stated at an arbitrary round `q` rather than at `r + 1`. -/
theorem g0ClearAtAction_of_relativeCarrierWindow
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {q : Round} (hq : 0 < q)
    (hactionHor : S.a q ≤ rho.horizon)
    (hgradeHor : domain S.E S.hc q .g2 ≤ rho.horizon)
    (hpost : S.E.t_GST ≤ S.a (q - 1))
    (hwindow : RelativeCarrierWindowAt S rho (q - 1) .g0)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot q) = some P)
    (hparent : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u (q - 1))
        (proposedParent S rho (S.hc.opening_slot q))) :
    ∀ v ∈ rho.honest,
      nodeClear S (actionReadAt S rho v q) q P.erase = true := by
  have hqPred : q - 1 + 1 = q := Nat.sub_add_cancel hq
  have hforming : GradeFormingMajority S rho (q - 1 + 1) := by
    rw [hqPred]
    exact gradeFormingMajority_of_admissible_belowOneThird S adm hfb hq hgradeHor hpost
  have hwindow' : RelativeCarrierWindowAt S rho (q - 1) .g0 := hwindow
  have hparentP : Block.Preceq (proposedParent S rho (S.hc.opening_slot q)) P.erase :=
    proposedParent_preceq_proposedBlockAt S rho (S.hc.opening_slot q) hP
  intro v hv
  have hframe := actionFrame_g0 S adm.toNamedAdmissibleCore hv hq hactionHor
  unfold nodeClear nodeRead
  change DecoupledConsensusModel.Protocol.clear
    (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho v q).cache
      (actionReadAt S rho v q).st.core.toHealing q) P.erase = true
  unfold DecoupledConsensusModel.Protocol.clear
  rw [hframe]
  cases hroot : storeRoot S.E S.hc
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc q .g0) v).st q .g0 with
  | none => rfl
  | some raw =>
      have hrawGrade : DecoupledConsensusModel.Protocol.gradeBool S.E
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc q .g0) v).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc q .g0) v).st.core.F
          S.hc.η_SG q (early S.E S.hc q .g0)
          (late S.E S.hc q .g0) raw = true := by
        exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hroot)).2
      have hrawGrade' : DecoupledConsensusModel.Protocol.gradeBool S.E
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (q - 1 + 1) .g0) v).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (q - 1 + 1) .g0) v).st.core.F
          S.hc.η_SG (q - 1 + 1) (early S.E S.hc (q - 1 + 1) .g0)
          (late S.E S.hc (q - 1 + 1) .g0) raw = true := by
        rw [hqPred]
        exact hrawGrade
      obtain ⟨u, hu, hrawCarrier⟩ := relativeGrade_has_roundCarrier
        S adm.toNamedAdmissibleCore hwindow' hforming hv hrawGrade'
      have huHon : u ∈ rho.honest :=
        ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u (q - 1)).mp hu).1
      have hrawP : Block.Preceq raw P.erase :=
        Block.preceq_trans hrawCarrier
          (Block.preceq_trans (hparent u huHon) hparentP)
      have hclipP : Block.Preceq
          (DecoupledConsensusModel.Protocol.clipGrade raw
            (actionReadAt S rho v q).st.core.F) P.erase :=
        Block.preceq_trans
          (NamedOutageClosure.q10_clip_preceq raw
            (actionReadAt S rho v q).st.core.F) hrawP
      change Block.compatible P.erase
        (DecoupledConsensusModel.Protocol.clipGrade raw
          (actionReadAt S rho v q).st.core.F) = true
      simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inr hclipP

/-- The consumer-facing form. At the pinned premise's single use site
(`FixedHeightRootClaimFourOuterRun.lean:643-645`) the outer theorem already
holds `hqPos: 0 < q`, `hactionQHor: S.a q ≤ rho.horizon`,
`hdomainAction: domain S.E S.hc q.g2 ≤ S.a q` and
`hparents: FixedHeightRootOpeningParentRun S rho q`, so the G0 clearance of
the round-`q` opening proposal follows from the relative carrier window of
round `q - 1` alone. -/
theorem g0ClearAtAction_of_relativeCarrierWindow_of_openingParentRun
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {q : Round} (hq : 0 < q)
    (hactionHor : S.a q ≤ rho.horizon)
    (hgradeHor : domain S.E S.hc q .g2 ≤ rho.horizon)
    (hpost : S.E.t_GST ≤ S.a (q - 1))
    (hwindow : RelativeCarrierWindowAt S rho (q - 1) .g0)
    (hparents : FixedHeightRootOpeningParentRun S rho q)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot q) = some P) :
    ∀ v ∈ rho.honest,
      nodeClear S (actionReadAt S rho v q) q P.erase = true :=
  g0ClearAtAction_of_relativeCarrierWindow S adm hfb hq hactionHor hgradeHor
    hpost hwindow hP hparents.actionTargetParent

end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms proposedParent_preceq_proposedBlockAt
#print axioms g0ClearAtAction_of_relativeCarrierWindow
#print axioms g0ClearAtAction_of_relativeCarrierWindow_of_openingParentRun
end DecoupledConsensusModel.Proofs.HealingSurface

end
