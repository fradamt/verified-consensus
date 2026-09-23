module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.PostHealingContinuation
public import DecoupledConsensusInternal.Definitions.NamedLifecycle

@[expose] public section

/-!
# Regime-free Goldfish cone persistence

This module owns the proof-only input shapes for the Goldfish cone step. The
input shapes use the prepared named vote and confirmation reads. The endpoint
is still an erased `Block`, because the Goldfish fork-choice algebra and the
confirmation predicates use erased block geometry.

The path and induction declarations from the earlier tree remain absent. The
confirmation consumer below uses the prepared named cone, anchor, and
contract-carrying genuine confirmation. The remaining live consumers keep
their exact old goals below.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Named input shapes -/

/-- The non-Goldfish inputs at one slot-`(s+1)` vote duty.

`path` contains only strict intermediate blocks. `candidate` supplies the
endpoint, so callers do not have to repeat it in the path premise. -/
structure GoldfishConeVoteInputs
    (S : Setup V) (rho : Run V) (s : Slot) (C : Block V) (w : V) : Prop where
  candidate : C ∈ voterCandidateTreeAt S rho w (s + 1)
  root : Block.Preceq
    (Protocol.get_fg_root
      (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) C
  anchor : Block.compatible
    (voterAnchorAt S rho w (s + 1)) C = true
  path : ∀ D : Block V,
    Block.Preceq (voterAnchorAt S rho w (s + 1)) D →
    D ≠ voterAnchorAt S rho w (s + 1) →
    Block.Preceq D C → D ≠ C →
    D ∈ voterCandidateTreeAt S rho w (s + 1)

/-- The corresponding non-Goldfish inputs at one slot-`s` confirmation read. -/
structure GoldfishConeConfirmationInputs
    (S : Setup V) (rho : Run V) (s : Slot) (C : Block V) (w : V) : Prop where
  candidate : C ∈ filteredTree (confirmationInputRead S rho w s)
  root : Block.Preceq
    (Protocol.get_fg_root
      (confirmationInputRead S rho w s).st.core.toHealing.toFG) C
  anchor : Block.compatible
    (namedConfirmationAnchor S (confirmationInputRead S rho w s)) C = true
  path : ∀ D : Block V,
    Block.Preceq
      (namedConfirmationAnchor S (confirmationInputRead S rho w s)) D →
    D ≠ namedConfirmationAnchor S (confirmationInputRead S rho w s) →
    Block.Preceq D C → D ≠ C →
    D ∈ filteredTree (confirmationInputRead S rho w s)

/-- The per-slot supplier interface used by `goldfishCone_induction`. -/
structure GoldfishConeSlotInputs
    (S : Setup V) (rho : Run V) (s : Slot) (C : Block V) : Prop where
  vote : ∀ w ∈ rho.honest, GoldfishConeVoteInputs S rho s C w
  confirmation : ∀ w ∈ rho.honest,
    GoldfishConeConfirmationInputs S rho s C w

/-- Regime-free non-Goldfish inputs at one slot-`(s+1)` vote duty.

When the selected FG root precedes `C`, the caller supplies the candidate and
the strict path. When `C` precedes the selected root, the explicit walk
already starts above `C`, so no candidate fact for `C` is required. -/
structure GoldfishConeVoteInputs'
    (S : Setup V) (rho : Run V) (s : Slot) (C : Block V) (w : V) : Prop where
  rootSide :
    (Block.Preceq
        (Protocol.get_fg_root
          (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) C ∧
      C ∈ voterCandidateTreeAt S rho w (s + 1) ∧
      ∀ D : Block V,
        Block.Preceq (voterAnchorAt S rho w (s + 1)) D →
        D ≠ voterAnchorAt S rho w (s + 1) →
        Block.Preceq D C → D ≠ C →
        D ∈ voterCandidateTreeAt S rho w (s + 1)) ∨
    Block.Preceq C
      (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG)
  anchor : Block.compatible
    (voterAnchorAt S rho w (s + 1)) C = true



/-- Regime-free non-Goldfish inputs at one slot-`s` confirmation read. -/
structure GoldfishConeConfirmationInputs'
    (S : Setup V) (rho : Run V) (s : Slot) (C : Block V) (w : V) : Prop where
  rootSide :
    (Block.Preceq
        (Protocol.get_fg_root
          (confirmationInputRead S rho w s).st.core.toHealing.toFG) C ∧
      C ∈ filteredTree (confirmationInputRead S rho w s) ∧
      ∀ D : Block V,
        Block.Preceq
          (namedConfirmationAnchor S (confirmationInputRead S rho w s)) D →
        D ≠ namedConfirmationAnchor S (confirmationInputRead S rho w s) →
        Block.Preceq D C → D ≠ C →
        D ∈ filteredTree (confirmationInputRead S rho w s)) ∨
    Block.Preceq C
      (Protocol.get_fg_root
        (confirmationInputRead S rho w s).st.core.toHealing.toFG)
  anchor : Block.compatible
    (namedConfirmationAnchor S (confirmationInputRead S rho w s)) C = true

/-- The regime-free per-slot supplier used by `goldfishCone_induction'`. -/
structure GoldfishConeSlotInputs'
    (S : Setup V) (rho : Run V) (s : Slot) (C : Block V) : Prop where
  vote : ∀ w ∈ rho.honest, GoldfishConeVoteInputs' S rho s C w
  confirmation : ∀ w ∈ rho.honest,
    GoldfishConeConfirmationInputs' S rho s C w

/-- The strict root-below input is a root-side input. -/
def GoldfishConeVoteInputs.toRootSide
    {S : Setup V} {rho : Run V} {s : Slot} {C : Block V} {w : V}
    (h : GoldfishConeVoteInputs S rho s C w) :
    GoldfishConeVoteInputs' S rho s C w where
  rootSide := Or.inl ⟨h.root, h.candidate, h.path⟩
  anchor := h.anchor

/-- The strict root-below confirmation input is a root-side input. -/
def GoldfishConeConfirmationInputs.toRootSide
    {S : Setup V} {rho : Run V} {s : Slot} {C : Block V} {w : V}
    (h : GoldfishConeConfirmationInputs S rho s C w) :
    GoldfishConeConfirmationInputs' S rho s C w where
  rootSide := Or.inl ⟨h.root, h.candidate, h.path⟩
  anchor := h.anchor

/-- Every strict slot supplier gives a root-side slot supplier. -/
def GoldfishConeSlotInputs.toRootSide
    {S : Setup V} {rho : Run V} {s : Slot} {C : Block V}
    (h : GoldfishConeSlotInputs S rho s C) :
    GoldfishConeSlotInputs' S rho s C where
  vote := fun w hw => (h.vote w hw).toRootSide
  confirmation := fun w hw => (h.confirmation w hw).toRootSide











/-- A prepared confirmation cone carries the protected block to a genuine
confirmation selected by the same prepared confirmation read. -/
theorem goldfishCone_confirmation
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V}
    (hnames : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq C X))
    {w : V} (hw : w ∈ rho.honest)
    (hinputs : GoldfishConeConfirmationInputs S rho s C w)
    {D : Block V}
    (hgenuine : GenuineConfirmationWith
      (NamedProfile.gradeContract (confirmationInputRead S rho w s).cache)
      S.E S.hc (Proofs.Optimistic.confStore S rho w s) s D) :
    Block.Preceq C D := by
  let read := confirmationInputRead S rho w s
  let st := Proofs.Optimistic.confStore S rho w s
  let contract := NamedProfile.gradeContract read.cache
  have hroot : Block.Preceq (confRoot st) C := by
    simpa only [st, confRoot, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
      Run.storeBeforeTime, read, confirmationInputRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      hinputs.root
  have hresolve := headsResolveIn_confStore_of_postHealingCone
    S adm hw hpost (support_cutoff_le_confirmation_time S.E s |>.trans hhor)
      hroot hnames
  have hsupport := coneSupport_confVotes_after_gst
    S adm hcom hs hpost hhor hnames hw hresolve
  have hvalid : Protocol.VoteSetValid S.E s (confLate S.E st s) := by
    simpa only [st, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using
      voteSetValid_confLate_stateBeforeTime S adm.toNamedScheduleWellFormed w
        (Protocol.confirmation_time S.E s) s
  have hcompat : Block.compatible
      (confAnchorWith contract S.E S.hc st) C = true := by
    simpa only [confAnchorWith, contract, st, read, namedConfirmationAnchor,
      Proofs.Optimistic.confStore_eq_confirmationInputRead] using hinputs.anchor
  have hpath : ∀ D' : Block V,
        Block.Preceq (confAnchorWith contract S.E S.hc st) D' →
        D' ≠ confAnchorWith contract S.E S.hc st →
        Block.Preceq D' C → D' ∈ confTree st := by
    intro D' hAD hDne hD'C
    by_cases hEq : D' = C
    · subst D'
      simpa only [confTree, st, read, confirmationInputRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.confStore_eq_confirmationInputRead] using hinputs.candidate
    · simpa only [confAnchorWith, confTree, contract, st, read,
        namedConfirmationAnchor, confirmationInputRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Proofs.Optimistic.confStore_eq_confirmationInputRead] using
        hinputs.path D' hAD hDne hD'C hEq
  have horder : Block.Preceq
      (confAnchorWith contract S.E S.hc st) C ∨
      Block.Preceq C (confAnchorWith contract S.E S.hc st) := by
    simpa only [Block.compatible, Bool.or_eq_true] using hcompat
  rcases horder with hanchorC | hCanchor
  · have hpre := Proofs.Optimistic.update_confirmation_preceq_with contract
        S.E S.hc st s rho.honest hsupport hvalid hanchorC hpath
    rw [hgenuine.selected] at hpre
    exact hpre
  · have hwalk : Block.Preceq
        (confAnchorWith contract S.E S.hc st)
        (confWalkWith contract S.E S.hc st s) := by
      simpa only [confWalkWith] using
        Protocol.ghost_preceq
          (confAnchorWith contract S.E S.hc st) (confTree st)
          (confScore S.E st s) (confEligible S.E st s)
    have hDwalk : D = confWalkWith contract S.E S.hc st s := by
      rw [← hgenuine.selected, update_confirmation_with_live_confirmed,
        if_pos hgenuine.genuine]
    rw [hDwalk]
    exact Block.preceq_trans hCanchor hwalk





end HealingSurface
end Proofs
end DecoupledConsensusModel

end
