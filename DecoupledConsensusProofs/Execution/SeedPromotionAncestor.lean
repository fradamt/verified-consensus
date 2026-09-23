module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedAdoption
public import DecoupledConsensusProofs.Protocol.Grades.SeedFlush
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedCeiling
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedOpeningWindow

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Local opening ancestry for seed promotion

The `M - 1` promotion needs the opening proposal of one carrier round below
the later carrier opening's parent. The common grade persists through the
intervening gate-off action reads; the named action-carrier cover and the
later round-ceiling alignment then give the erased ancestry. This module keeps
that proof below `SeedHeightProgressRun`, so the height seed can use it without
an import cycle.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem seedPromotionAncestor_namedParent_preceq (P : NamedBlock V) :
    NamedBlock.Preceq P.parent P := by
  cases P with
  | genesis => exact Proofs.NamedAncestry.named_self _
  | node parent slot root votes support rows proposer =>
      exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
        (Proofs.NamedAncestry.named_self parent)

private theorem seedPromotionAncestor_rounds_nat
    {q q' : Nat} (h : q + 2 ≤ q') :
    q + 1 ≤ q' - 1 ∧ 0 < q' - 1 := by
  omega

/-- The opening proposal of `q` precedes the later opening's named parent when
its grade persists through the gate-off interval. -/
theorem seedOpeningProposal_preceq_nextOpeningParent_of_grade
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {q q' : Round} {C' B B' : NamedBlock V}
    (hwindow' : NamedGateOffOpeningWindowAt S rho M q' B')
    (hcarrier' : ProposerCarrierAt S rho q')
    (hceiling' : RoundCeilingAt S rho M q' C')
    (hgradeNext : NamedGradeFormsAt S rho (q + 1) B.erase)
    (hBrun : RunBlock S rho B)
    (hBheight : (Protocol.derive_named S.E S.cfg B).h = M - 1)
    (hM : 1 ≤ M)
    (hqq' : q + 2 ≤ q')
    (hpostNext : S.E.t_GST ≤ S.a (q + 1))
    (hhorPrev' : S.a (q' - 1) ≤ rho.horizon)
    (hframe : ∀ read : Time, S.a (q + 1) ≤ read →
      read ≤ S.a (q' - 1) → ∀ w ∈ rho.honest,
        (rho.storeBeforeTime S w read).h_j + 2 ≤ M ∧
          (rho.storeBeforeTime S w read).h_max = M) :
    ∀ Parent : NamedBlock V, NamedBlock.parent? B' = some Parent →
      NamedBlock.Preceq B Parent := by
  obtain ⟨hspan, hq'PredPos⟩ :=
    seedPromotionAncestor_rounds_nat hqq'
  have hformsAt := namedGradeFormsAt_persists_through_gateOffActionWindow
    S adm hfb (Nat.succ_pos q) (r0 := q + 1) (q := q' - 1) hgradeNext hBrun
    (by simpa only [hBheight] using (Nat.le_refl (M - 1))) hM hpostNext hhorPrev'
    (fun read hlo hhi w hw =>
      let h := hframe read hlo hhi w hw
      ⟨h.2, h.1⟩)
  have hforms := hformsAt (q' - 1) hspan (le_refl _)
  have hcover := actionCarriersCover_of_gradeFormsAt S adm
    hq'PredPos hhorPrev' hforms.1 hforms.2
  have haligned := openingAnchorsAligned_of_roundCeiling
    S adm hcom hcarrier' hceiling'
  have hpositive : 0 < ((S.E.committee 0) ∩ rho.honest).card := by
    have hc := hcom 0
    omega
  obtain ⟨x, hxmem⟩ := Finset.card_pos.mp hpositive
  have hx : x ∈ rho.honest := (Finset.mem_inter.mp hxmem).2
  have hbelow : Block.Preceq B.erase
      (proposedParent S rho (S.hc.opening_slot q')) :=
    Block.preceq_trans (hcover x hx)
      (haligned.previousCarriersBelowParent x hx)
  intro Parent hParent
  obtain ⟨p, hp, hparentErase⟩ := proposedBlockAt_parent
    S rho (S.hc.opening_slot q') hwindow'.proposal
  have hparentEq : B'.parent = p := by
    cases B' with
    | genesis => cases hp
    | node parent slot root votes support rows proposer =>
        exact Option.some.inj hp
  have hParentEq : Parent = p := by
    exact Option.some.inj (hParent.symm.trans (by simpa using hp))
  have hbelowParent : Block.Preceq B.erase B'.parent.erase := by
    rw [hparentEq, hparentErase]
    exact hbelow
  obtain ⟨A, hAparent, hAerase⟩ := Proofs.NamedAncestry.erased_ancestor_lift
    B'.parent hbelowParent
  have hB'run : RunBlock S rho B' := by
    have hs' : 0 < S.hc.opening_slot q' := by
      unfold Protocol.HealConfig.opening_slot
      exact Nat.mul_pos hwindow'.roundPositive
        (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
    have hproposalHor' : Protocol.proposal_time S.E
        (S.hc.opening_slot q') ≤ rho.horizon :=
      (Protocol.proposal_time_le_confirmation_time S.E _).trans
        (by simpa only [Setup.a, Protocol.a_eq_confirmation_time] using
          ((Assembly.a_mono S (Nat.le_succ q')).trans
            hwindow'.nextActionInHorizon))
    exact proposedBlockAt_blockInRun_of_admissible S
      adm.toNamedAdmissibleCore (S.hc.opening_slot q') hs'
      hcarrier'.1 hproposalHor' hwindow'.proposal
  have hparentRun : RunBlock S rho B'.parent :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hB'run
      (seedPromotionAncestor_namedParent_preceq B')
  have hArun : RunBlock S rho A :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hparentRun hAparent
  have hBA : B = A := by
    apply adm.toNamedRootCollisionFree.root_injective B A hBrun hArun B A
      (Or.inl (Proofs.NamedAncestry.named_self B))
      (Or.inr (Proofs.NamedAncestry.named_self A))
    rw [← Proofs.NamedWire.erase_root B, ← Proofs.NamedWire.erase_root A, hAerase]
  have hnamed : NamedBlock.Preceq B B'.parent := by
    rw [hBA]
    exact hAparent
  have hBParent : B'.parent = Parent := hparentEq.trans hParentEq.symm
  simpa only [hBParent] using hnamed

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
