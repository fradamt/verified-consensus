module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.RawHeightCoverage
public import DecoupledConsensusProofs.Protocol.ChainState.SeedFreshRowRenewal

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Fresh-row promotion on the seed branch
The predecessor rows used by a later opening are emitted at the immediately
preceding round `r = q' - 1`. Such a row is still inside the proposer's
inclusive SG window because `η_SG ≥ 1`, so the general named coverage theorem
can be used directly. This is a local replacement for the previous long-distance
`chainRows` route: it does not claim that an earlier row remains available.
The promotion theorem keeps the existing parent-height split. In the
still-`M - 1` branch, a source-height cap relative to the later parent feeds
`seedFreshActionRows_of_persistedGrade`; the persisted opening block supplies
the opposite height inequality and `Proofs.NamedEntryHeight.entry_eq_on_plateau`
supplies the matching entry. If the parent is already at `M`, the later
proposal is already successful. A public frontier rise is also returned
unchanged.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Round-local window facts -/

omit [Fintype V] in
private theorem seedFresh_parent_preceq_self (B : NamedBlock V) :
    NamedBlock.Preceq B.parent B := by
  cases B with
  | genesis => exact Proofs.NamedAncestry.named_self _
  | node parent slot root votes support rows proposer =>
      exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
        (Proofs.NamedAncestry.named_self parent)

private theorem seedFresh_opening_slot_pos
    (S : Setup V) (r : Round) :
    0 < S.hc.opening_slot (r + 1) := by
  unfold Protocol.HealConfig.opening_slot
  exact Nat.mul_pos (Nat.succ_pos r)
    (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)

private theorem seedFresh_inWindow_at_nextOpening
    (S : Setup V) (rho : Run V) (r : Round) :
    Protocol.ProposalRows.inWindow S.hc
      (proposerReadAt S rho (S.hc.opening_slot (r + 1))).st.core r = true := by
  have hslot :
      (proposerReadAt S rho (S.hc.opening_slot (r + 1))).st.core.s =
        S.hc.opening_slot (r + 1) := by
    simpa only [proposerReadAt, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      Proofs.Optimistic.slotOf_proposal_time S.E
        (S.hc.opening_slot (r + 1))
  have hround : S.hc.round_of
      (proposerReadAt S rho (S.hc.opening_slot (r + 1))).st.core.s = r + 1 := by
    rw [hslot]
    exact round_of_opening_slot_eq S.hc (r + 1)
  unfold Protocol.ProposalRows.inWindow
  rw [hround]
  simp only [decide_eq_true_eq]
  have heta : 1 ≤ S.hc.η_SG := S.hc.η_SG_ge_one
  exact ⟨by
    have hle := Nat.sub_le_sub_left heta (r + 1)
    simpa only [Nat.add_sub_cancel] using hle,
    Nat.le_succ r⟩

/-! ## Fresh proposal coverage -/

/-- Rows renewed at the immediately preceding round cover a later opening
proposal in the named targeted-coverage format. The source cap is relative
to the later selected parent. It is used only in the parent-predecessor
branch by the caller below. -/
theorem seedFreshProposalCoverage_of_persistedGrade
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {M : Height} {r : Round} {C B : NamedBlock V}
    (hr : 0 < r)
    (hpost : S.E.t_GST ≤ S.a r)
    (hCrun : RunBlock S rho C)
    (hCheight : (derive_named S.E S.cfg C).h = M - 1)
    (hforms : NamedGradeFormsAt S rho r C.erase)
    (hwindow : ∀ v ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho v (S.a r) C.erase)
    (hsourceToParent : ∀ v ∈ rho.honest, ∀ Q : Block V,
      PhaseGrades.nodeFGSource S (actionReadAt S rho v r) r = some Q →
      ((actionReadAt S rho v r).st.core.toHealing.σ Q).h ≤
        (derive_named S.E S.cfg B.parent).h)
    (hgateOff : ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v (S.a r)).h_j + 2 ≤ M)
    (hB : proposedBlockAt S rho (S.hc.opening_slot (r + 1)) = some B)
    (hCP : NamedBlock.Preceq C B.parent)
    (hparentHeight : (derive_named S.E S.cfg B.parent).h = M - 1)
    (hprop : S.E.proposer (S.hc.opening_slot (r + 1)) ∈ rho.honest)
    (hproposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot (r + 1)) ≤ rho.horizon) :
    NamedTargetedHonestActionProposalCoverageAt S rho r B (M - 1)
      (derive_named S.E S.cfg C).T_h.root := by
  have hsourceUpper : ∀ v ∈ rho.honest, ∀ Q : Block V,
      PhaseGrades.nodeFGSource S (actionReadAt S rho v r) r = some Q →
      ((actionReadAt S rho v r).st.core.toHealing.σ Q).h ≤ M - 1 := by
    intro v hv Q hQ
    have h := hsourceToParent v hv Q hQ
    simpa only [hparentHeight] using h
  have hdelay : S.a r + S.E.Δ ≤ Protocol.proposal_time S.E
      (S.hc.opening_slot (r + 1)) :=
    action_add_delta_le_openingProposal_of_round_lt S (Nat.lt_succ_self r)
  have hhor : S.a r ≤ rho.horizon :=
    (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
      (hdelay.trans hproposalHor)
  have hrows := seedFreshActionRows_of_persistedGrade S adm
    hr hhor hCrun hCheight hforms hwindow hsourceUpper hgateOff
  have hinWindow := seedFresh_inWindow_at_nextOpening S rho r
  intro v hv
  have hpair := hrows v hv
  refine ⟨?_, hpair⟩
  exact actionAttestationAt_coveredAtProposal S adm hforms hCrun hCheight rfl
    hB hCP hparentHeight hprop hproposalHor hpost hdelay hv
    (hwindow v hv) hinWindow hpair

/-! ## The parent-height split -/


/-- Fresh predecessor rows promote the later opening in the no-rise branch.
The `hsourceToParent` premise is the local source-capture cap supplied by the
caller. It is not a public records field. -/
theorem seedFreshOpening_promotion_of_persistedGrade
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {r : Round} {C B : NamedBlock V}
    (hM : 2 ≤ M)
    (hr : 0 < r)
    (hpost : S.E.t_GST ≤ S.a r)
    (hCrun : RunBlock S rho C)
    (hCheight : (derive_named S.E S.cfg C).h = M - 1)
    (hforms : NamedGradeFormsAt S rho r C.erase)
    (hwindow : ∀ v ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho v (S.a r) C.erase)
    (hsourceToParent : ∀ v ∈ rho.honest, ∀ Q : Block V,
      PhaseGrades.nodeFGSource S (actionReadAt S rho v r) r = some Q →
      ((actionReadAt S rho v r).st.core.toHealing.σ Q).h ≤
        (derive_named S.E S.cfg B.parent).h)
    (hgateOff : ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v (S.a r)).h_j + 2 ≤ M)
    (hB : proposedBlockAt S rho (S.hc.opening_slot (r + 1)) = some B)
    (hCP : NamedBlock.Preceq C B.parent)
    (hparentCap : (derive_named S.E S.cfg B.parent).h ≤ M)
    (hprop : S.E.proposer (S.hc.opening_slot (r + 1)) ∈ rho.honest)
    (hproposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot (r + 1)) ≤ rho.horizon)
    (hpostMature_of_parentPred :
      (derive_named S.E S.cfg B.parent).h = M - 1 →
        ProposalTimeoutMatureAt S rho (S.hc.opening_slot (r + 1))) :
    (derive_named S.E S.cfg B).h = M ∨
      M < honestHMaxAt S rho
        (Protocol.proposal_time S.E (S.hc.opening_slot (r + 1))) := by
  have hM1 : 1 ≤ M := (by decide : (1 : Nat) ≤ 2).trans hM
  have hparentLower : M - 1 ≤
      (derive_named S.E S.cfg B.parent).h := by
    rw [← hCheight]
    exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hCP
  have hparentCases :
      (derive_named S.E S.cfg B.parent).h = M - 1 ∨
        (derive_named S.E S.cfg B.parent).h = M := by
    rcases Nat.eq_or_lt_of_le hparentCap with hEq | hLt
    · exact Or.inr hEq
    · exact Or.inl (Nat.le_antisymm (Nat.le_pred_of_lt hLt) hparentLower)
  have hspos : 0 < S.hc.opening_slot (r + 1) :=
    seedFresh_opening_slot_pos S r
  by_cases hrise : M < honestHMaxAt S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot (r + 1)))
  · exact Or.inr hrise
  left
  have hpublicCap : honestHMaxAt S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot (r + 1))) ≤ M :=
    Nat.le_of_not_gt hrise
  have hproposalUpper : (derive_named S.E S.cfg B).h ≤ M :=
    (honestProposedBlock_height_le_honestHMaxAt S adm hspos hprop
      hproposalHor hB).trans hpublicCap
  rcases hparentCases with hparentPred | hparentExact
  · have hsame : (derive_named S.E S.cfg C).h =
        (derive_named S.E S.cfg B.parent).h := by
      rw [hCheight, hparentPred]
    have hparentTarget : (derive_named S.E S.cfg B.parent).T_h.root =
        (derive_named S.E S.cfg C).T_h.root := by
      exact congrArg (fun x : Block V => x.root)
        (Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hCP hsame).symm
    have hcoverage := seedFreshProposalCoverage_of_persistedGrade S adm
      hr hpost hCrun hCheight hforms hwindow hsourceToParent hgateOff hB hCP
      hparentPred hprop hproposalHor
    have hheight := named_proposedBlock_height_eq_succ_of_actionCoverage
      S hfb hB (hpostMature_of_parentPred hparentPred) hcoverage hparentPred
      hparentTarget
    calc
      (derive_named S.E S.cfg B).h = M - 1 + 1 := hheight
      _ = M := Nat.sub_add_cancel hM1
  · have hproposalLower : M ≤ (derive_named S.E S.cfg B).h := by
      rw [← hparentExact]
      exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg
        (seedFresh_parent_preceq_self B)
    exact Nat.le_antisymm hproposalUpper hproposalLower

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
