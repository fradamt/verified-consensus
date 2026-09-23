module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ValidatorClient.SeedPredPromotion

@[expose] public section

/-! # Fresh height rows on the gate-off seed branch
The opening lifecycle producer
`seedGateOff_lifecycleAction_rows_of_selected` gives the row shape at the
opening proposal. A later action need not emit the same byte-level row: its
round action reads its current FG source and its current record. This module
therefore renews the row shape at that action.
The source-height and source-entry facts are kept explicit. A persisted
common grade and its action-read activity put the opening block below each
current source. The named action-source witness and named store coherence
derive the source body and its cached `derive_named` state. The only
branch-specific input is the source-height upper bound in the still-`M - 1`
branch. The lower bound comes from the persisted opening block and
`Proofs.NamedEntryHeight.derive_height_mono`; on the higher branch the existing exact
height continuation already closes promotion. `Proofs.NamedEntryHeight.entry_eq_on_plateau`
then identifies the current source entry with the opening entry. The gate-off
own-lock producer supplies the empty lock needed by the named height-pair
rules. No previous row, carried-row window, or `eta_SG` bound is used.
The pre-rewrite proof performs the same final codec step in
`lifecycleAction_rows_at_pred`: it obtains the source from the lifecycle,
rewrites the action store with `DerivedStateAgrees`, applies
`round_action_height_pair_target_or_timeout_of_source_lock_none_or_aligned`,
and closes the lock disjunction. This module keeps that step, while replacing
The previous lifecycle-source equality with the current persisted-grade source and
making the no-rise height cap explicit.
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
open Protocol (own_lock)
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The named source witness -/

private theorem seedFresh_actionBody_runBlock
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionReadAt S rho v r).st.bodies) : RunBlock S rho D := by
  have hDpre : D ∈ (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    simpa only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
      NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hD
  obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted (S.a r)
  have hDi : D ∈ (rho.stateBefore S i v).st.bodies := by
    change D ∈ (NamedRun.stateBefore S rho i v).st.bodies
    rw [← hi]
    exact hDpre
  exact Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hDi)

/- The source theorem below is the named-store counterpart of the previous
`exists_actionSource_of_gradeFormsAt` witness. The action-source existence
producer supplies the erased source; `NamedActionSources.action_witness`
supplies the retained named body and its stored derivation. -/
theorem seedFresh_namedSource_witness
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {Q : Block V}
    (hsource : PhaseGrades.nodeFGSource S
      (actionReadAt S rho v r) r = some Q) :
    ∃ D : NamedBlock V,
      D ∈ (actionReadAt S rho v r).st.bodies ∧
      D.erase = Q ∧
      RunBlock S rho D ∧
      (actionReadAt S rho v r).st.core.toHealing.σ Q =
        derive_named S.E S.cfg D := by
  have hround : S.hc.round_of
      (actionReadAt S rho v r).st.core.toHealing.s = r := by
    simpa only [actionStoreAt, Protocol.Store.toHealing] using
      actionStoreAt_round S rho v r
  have hsource' : actionFGSource S (actionReadAt S rho v r) = some Q := by
    have hsource0 := hsource
    simp only [PhaseGrades.nodeFGSource] at hsource0
    simpa only [actionFGSource, hround] using hsource0
  obtain ⟨D, hDbody, hDerase, hσ, -⟩ :=
    NamedActionSources.action_witness S rho v r Q hsource'
  have hDrun := seedFresh_actionBody_runBlock S adm hv hDbody
  refine ⟨D, hDbody, hDerase, hDrun, ?_⟩
  change (actionReadAt S rho v r).st.core.σ Q =
    derive_named S.E S.cfg D
  exact hσ

/-! ## The current source row -/

/-- A current named FG source at height `M - 1` and entry `T`, with the
gate-off empty-lock result. The source may differ from the opening block; the
height-pair codec still emits the current action's own round row. -/
theorem seedFreshActionRow_of_source
    (S : Setup V) {rho : Run V}
    {M : Height} {r : Round} {v : V} {Q : Block V} {T : BlockId}
    (hsource : PhaseGrades.nodeFGSource S
      (actionReadAt S rho v r) r = some Q)
    (hsourceHeight :
      ((actionReadAt S rho v r).st.core.toHealing.σ Q).h = M - 1)
    (hsourceEntry :
      ((actionReadAt S rho v r).st.core.toHealing.σ Q).T_h.root = T)
    (hlock : own_lock (actionReadAt S rho v r).record.legacy
        ((actionReadAt S rho v r).st.core.toHealing.σ Q).h
        (Protocol.NamedActions.round_action_with
          (NamedProfile.gradeContract (actionReadAt S rho v r).cache)
          S.E S.hc (S.node v)
          (actionReadAt S rho v r).st.core.toHealing
          (actionReadAt S rho v r).record).2.finality_pair = none) :
    (actionAttestationAt S rho v r).height_pair =
        NamedHeightPair.vote (M - 1) T false ∨
      (actionAttestationAt S rho v r).height_pair =
        NamedHeightPair.vote (M - 1) T true := by
  have hround : S.hc.round_of
      (actionReadAt S rho v r).st.core.toHealing.s = r := by
    simpa only [actionStoreAt, Protocol.Store.toHealing] using
      actionStoreAt_round S rho v r
  have hsource' : actionSource
      (NamedProfile.gradeContract (actionReadAt S rho v r).cache)
      S.E S.hc (actionReadAt S rho v r).st.core.toHealing = some Q := by
    simpa only [actionSource, hround, PhaseGrades.nodeFGSource] using hsource
  have hlock' : own_lock (actionReadAt S rho v r).record.legacy
      ((actionReadAt S rho v r).st.core.toHealing.σ Q).h
      (Protocol.NamedActions.round_action_with
        (NamedProfile.gradeContract (actionReadAt S rho v r).cache)
        S.E S.hc (S.node v)
        (actionReadAt S rho v r).st.core.toHealing
        (actionReadAt S rho v r).record).2.finality_pair = none := hlock
  have hpairs :=
    round_action_height_pair_target_or_timeout_of_source_lock_none_or_aligned
      (NamedProfile.gradeContract (actionReadAt S rho v r).cache)
      S.E S.hc (S.node v) (actionReadAt S rho v r).st.core.toHealing
      (actionReadAt S rho v r).record hsource' (Or.inl hlock')
  rw [hsourceHeight, hsourceEntry] at hpairs
  simpa only [actionAttestationAt, Protocol.NamedDuties.attest_with] using hpairs

/-! ## Renewal from the persisted opening grade -/


/-- Renew the height row at every current action in the still-`M - 1` branch.
The common grade and retained action read prove the opening block is below the
current source. The source witness and its named derivation are reconstructed
from the live action store. `hsourceUpper` is the local no-rise cap; it is not
a public seed-records field and the higher-height branch is handled by the
existing exact-height continuation. -/
theorem seedFreshActionRows_of_persistedGrade
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {M : Height} {r : Round} {B0 : NamedBlock V}
    (hr : 0 < r)
    (hhor : S.a r ≤ rho.horizon)
    (hB0run : RunBlock S rho B0)
    (hB0height : (derive_named S.E S.cfg B0).h = M - 1)
    (hforms : NamedGradeFormsAt S rho r B0.erase)
    (hwindow : ∀ v ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho v (S.a r) B0.erase)
    (hsourceUpper : ∀ v ∈ rho.honest, ∀ Q : Block V,
      PhaseGrades.nodeFGSource S (actionReadAt S rho v r) r = some Q →
      ((actionReadAt S rho v r).st.core.toHealing.σ Q).h ≤ M - 1)
    (hgateOff : ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v (S.a r)).h_j + 2 ≤ M) :
    ∀ v ∈ rho.honest,
      (actionAttestationAt S rho v r).height_pair =
          NamedHeightPair.vote (M - 1)
            (derive_named S.E S.cfg B0).T_h.root false ∨
      (actionAttestationAt S rho v r).height_pair =
          NamedHeightPair.vote (M - 1)
            (derive_named S.E S.cfg B0).T_h.root true := by
  intro v hv
  have hactive : B0.erase ∈
      PhaseGrades.filteredTree (actionReadAt S rho v r) :=
    namedGradeFormsAt_actionStore_of_window S hforms hv (hwindow v hv)
  obtain ⟨Q, hsource, -, -, -⟩ :=
    exists_actionSource_of_namedGradeFormsAt S adm.toNamedAdmissibleCore
      hr hhor hforms hv (hwindow v hv)
  obtain ⟨Qn, hQnbody, hQnerase, hQnrun, hσ⟩ :=
    seedFresh_namedSource_witness S adm hv hsource
  have hB0Q : Block.Preceq B0.erase Q :=
    namedGradeFormsAt_preceq_actionSource S adm.toNamedAdmissibleCore
      hr hhor hforms hv hactive hsource
  have hB0QnErase : Block.Preceq B0.erase Qn.erase := by
    rw [hQnerase]
    exact hB0Q
  obtain ⟨A, hAQn, hAerased⟩ :=
    Proofs.NamedAncestry.erased_ancestor_lift Qn hB0QnErase
  have hArun : RunBlock S rho A :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hQnrun hAQn
  have hroot : A.root = B0.root := by
    rw [← Proofs.NamedWire.erase_root A, hAerased, Proofs.NamedWire.erase_root]
  have hAB0 : A = B0 :=
    adm.toNamedRootCollisionFree.root_injective A B0 hArun hB0run A B0
      (Or.inl (Proofs.NamedAncestry.named_self A))
      (Or.inr (Proofs.NamedAncestry.named_self B0)) hroot
  have hB0Qn : NamedBlock.Preceq B0 Qn := by
    simpa only [hAB0] using hAQn
  have hDheightUpper : (derive_named S.E S.cfg Qn).h ≤ M - 1 := by
    have hsourceHeightUpper := hsourceUpper v hv Q hsource
    rw [hσ] at hsourceHeightUpper
    exact hsourceHeightUpper
  have hDheightLower : M - 1 ≤
      (derive_named S.E S.cfg Qn).h := by
    have hmono := Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hB0Qn
    rw [hB0height] at hmono
    exact hmono
  have hQnheight : (derive_named S.E S.cfg Qn).h = M - 1 :=
    Nat.le_antisymm hDheightUpper hDheightLower
  have hsameHeight : (derive_named S.E S.cfg B0).h =
      (derive_named S.E S.cfg Qn).h := by
    rw [hB0height, hQnheight]
  have hentry : (derive_named S.E S.cfg B0).T_h =
      (derive_named S.E S.cfg Qn).T_h :=
    Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hB0Qn hsameHeight
  have hsourceHeight :
      ((actionReadAt S rho v r).st.core.toHealing.σ Q).h = M - 1 := by
    rw [hσ, hQnheight]
  have hsourceEntry :
      ((actionReadAt S rho v r).st.core.toHealing.σ Q).T_h.root =
        (derive_named S.E S.cfg B0).T_h.root := by
    calc
      ((actionReadAt S rho v r).st.core.toHealing.σ Q).T_h.root =
          (derive_named S.E S.cfg Qn).T_h.root :=
        congrArg (fun x : Protocol.ChainState V => x.T_h.root) hσ
      _ = (derive_named S.E S.cfg B0).T_h.root :=
        congrArg (fun x : Block V => x.root) hentry.symm
  have hlock := gateOff_actionOwnLock_at_pred_none S adm v r
    (hgateOff v hv)
  have hlock' : own_lock (actionReadAt S rho v r).record.legacy
      ((actionReadAt S rho v r).st.core.toHealing.σ Q).h
      (Protocol.NamedActions.round_action_with
        (NamedProfile.gradeContract (actionReadAt S rho v r).cache)
        S.E S.hc (S.node v) (actionReadAt S rho v r).st.core.toHealing
        (actionReadAt S rho v r).record).2.finality_pair = none := by
    rw [hsourceHeight]
    simpa only [actionAttestationAt, Protocol.NamedDuties.attest_with] using hlock
  exact seedFreshActionRow_of_source S hsource hsourceHeight hsourceEntry hlock'

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
