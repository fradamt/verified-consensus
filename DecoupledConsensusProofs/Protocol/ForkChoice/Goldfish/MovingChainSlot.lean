module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.MovingChainDispatch
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedCeilingStep

@[expose] public section

/-!
# Moving-frontier slot entry

This module projects the event-indexed moving chain just past the proposal
phase of one slot. The slot endpoint has genuine-confirmation provenance from
The current slot or an earlier slot, and the vote cone belongs to the current
slot. The `s`-to-`s + 1` step branches on the slot-`s + 1` proposer. Thus an
honest proposal is installed only after its own proposal event, while the
Byzantine branch can select the deepest genuine output of slot `s`.

The exact-lifecycle bootstrap fragment at the end records the facts that the
current records supplies before the slot cursor is advanced. The read dispatch
is in `MovingChainDispatchRun`.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.NamedRecoveryRead
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]



/-- Additive named entry state for the prepared moving-chain fold.
The entry keeps the existing named vote and confirmation obligations. Only the
history witness changes from the compatibility state to `MovingFrontierChainStateN`,
which removes the erased previous-row callback from the forward fold. -/
structure MovingSlotEntryStateN
    (S : Setup V) (rho : Run V) (t1 : Time) (M0 : Height)
    (s : Slot) (Prev End : Block V) : Prop where
  startTime : t1 ≤ Protocol.proposal_time S.E s
  prevEndpoint : ∃ EndAt : Nat → Block V,
    MovingFrontierChainStateN S rho t1 M0
        (strictEventIndex rho t1)
        (inclusiveEventIndex rho (Protocol.proposal_time S.E s)) EndAt ∧
      EndAt (strictEventIndex rho (Protocol.proposal_time S.E s)) = Prev ∧
      EndAt (inclusiveEventIndex rho (Protocol.proposal_time S.E s)) = End
  prevVotes : NamedHonestVotesCone S rho (s - 1)
    (fun X => Block.Preceq Prev X)
  votes : NamedHonestVotesCone S rho s
    (fun X => Block.Preceq End X)
  headEq : S.E.proposer s ∈ rho.honest → ∀ w ∈ rho.honest,
    voteDutyHead S rho w s = End
  confCompatible : ∀ w ∈ rho.honest, ∀ D : Block V,
    GenuineConfirmationWith
      (NamedProfile.gradeContract
        (confirmationInputRead S rho w (s - 1)).cache)
      S.E S.hc
        (Proofs.Optimistic.confStore S rho w (s - 1)) (s - 1) D →
      Block.compatible D End = true

/-- The value selected by one honest slot-`s` confirmation handler. -/
def movingSlotConfirmationOutput
    (S : Setup V) (rho : Run V) (s : Slot) (v : V) : Block V :=
  (Protocol.update_confirmation_with
    (NamedProfile.gradeContract (confirmationInputRead S rho v s).cache)
    S.E S.hc
    (Proofs.Optimistic.confStore S rho v s) s).live_confirmed

/-- The finite set of honest slot-`s` outputs whose confirmation selection is
genuine. A retained FG-root fallback is deliberately excluded. -/
noncomputable def movingSlotGenuineOutputs
    (S : Setup V) (rho : Run V) (s : Slot) : Finset (Block V) := by
  classical
  exact (rho.honest.filter fun v =>
    GenuineConfirmationWith
      (NamedProfile.gradeContract
        (confirmationInputRead S rho v s).cache)
      S.E S.hc
      (Proofs.Optimistic.confStore S rho v s) s
      (movingSlotConfirmationOutput S rho s v)).image
        (movingSlotConfirmationOutput S rho s)

/-- the previous endpoint together with all genuine outputs of the current slot. -/
noncomputable def movingSlotFrontierCandidates
    (S : Setup V) (rho : Run V) (s : Slot) (End : Block V) :
    Finset (Block V) :=
  insert End (movingSlotGenuineOutputs S rho s)

/-- The deepest compatible current-slot genuine output, or the retained old
endpoint when there is no deeper genuine output. -/
structure MovingSlotFrontierAt
    (S : Setup V) (rho : Run V) (s : Slot)
    (End End' : Block V) : Prop where
  selected : Block.deepest?
      (movingSlotFrontierCandidates S rho s End) = some End'
  oldPreceq : Block.Preceq End End'
  genuinePreceq : ∀ v ∈ rho.honest, ∀ D : Block V,
    GenuineConfirmationWith
      (NamedProfile.gradeContract
        (confirmationInputRead S rho v s).cache)
      S.E S.hc
        (Proofs.Optimistic.confStore S rho v s) s D →
      Block.Preceq D End'
  source : End' = End ∨ ∃ v ∈ rho.honest,
    GenuineConfirmationWith
      (NamedProfile.gradeContract
        (confirmationInputRead S rho v s).cache)
      S.E S.hc
      (Proofs.Optimistic.confStore S rho v s) s End'

private theorem movingSlotGenuineOutputs_mem_iff
    (S : Setup V) (rho : Run V) (s : Slot) (D : Block V) :
    D ∈ movingSlotGenuineOutputs S rho s ↔
      ∃ v ∈ rho.honest,
        GenuineConfirmationWith
          (NamedProfile.gradeContract
            (confirmationInputRead S rho v s).cache)
          S.E S.hc
          (Proofs.Optimistic.confStore S rho v s) s D := by
  classical
  simp only [movingSlotGenuineOutputs, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨v, ⟨hv, hgenuine⟩, rfl⟩
    exact ⟨v, hv, hgenuine⟩
  · rintro ⟨v, hv, hgenuine⟩
    refine ⟨v, ⟨hv, ?_⟩, ?_⟩
    · simpa only [movingSlotConfirmationOutput, hgenuine.selected]
        using hgenuine
    · exact hgenuine.selected

private theorem movingSlotFrontierCandidates_compatible
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {c : Slot}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E c)
    (hhor : Protocol.confirmation_time S.E c ≤ rho.horizon)
    {End : Block V}
    (hcompat : ∀ w ∈ rho.honest, ∀ D : Block V,
      GenuineConfirmationWith
        (NamedProfile.gradeContract
          (confirmationInputRead S rho w c).cache)
        S.E S.hc
          (Proofs.Optimistic.confStore S rho w c) c D →
        Block.compatible D End = true) :
    ∀ X ∈ movingSlotFrontierCandidates S rho c End,
      ∀ Y ∈ movingSlotFrontierCandidates S rho c End,
        Block.compatible X Y = true := by
  intro X hX Y hY
  simp only [movingSlotFrontierCandidates, Finset.mem_insert] at hX hY
  rcases hX with hXEq | hX
  · subst X
    rcases hY with hYEq | hY
    · subst Y
      exact Block.compatible_of_preceq_common
        (Block.preceq_self End) (Block.preceq_self End)
    · obtain ⟨v, hv, hgenuine⟩ :=
        (movingSlotGenuineOutputs_mem_iff S rho c Y).mp hY
      exact Protocol.compatible_comm (hcompat v hv Y hgenuine)
  · obtain ⟨v, hv, hXgenuine⟩ :=
      (movingSlotGenuineOutputs_mem_iff S rho c X).mp hX
    rcases hY with hYEq | hY
    · subst Y
      exact hcompat v hv X hXgenuine
    · obtain ⟨w, hw, hYgenuine⟩ :=
        (movingSlotGenuineOutputs_mem_iff S rho c Y).mp hY
      exact Protocol.sameSlot_genuine_compatible_after_gst
        S adm hv hw hpost hhor hXgenuine hYgenuine

/-- A deepest compatible slot frontier always exists. It dominates the previous
endpoint and every honest genuine output of the confirmation slot `c`.
The only input is compatibility of the endpoint with each slot-`c` genuine
output; same-slot outputs are compatible with each other after GST. In a slot
window `(t_s, t_{s+1}]` the caller instantiates `c:= s - 1`. -/
theorem movingSlot_existsFrontier
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {c : Slot}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E c)
    (hhor : Protocol.confirmation_time S.E c ≤ rho.horizon)
    {End : Block V}
    (hcompat : ∀ w ∈ rho.honest, ∀ D : Block V,
      GenuineConfirmationWith
        (NamedProfile.gradeContract
          (confirmationInputRead S rho w c).cache)
        S.E S.hc
          (Proofs.Optimistic.confStore S rho w c) c D →
        Block.compatible D End = true) :
    ∃ End' : Block V, MovingSlotFrontierAt S rho c End End' := by
  classical
  let candidates := movingSlotFrontierCandidates S rho c End
  have hcompatible : ∀ X ∈ candidates, ∀ Y ∈ candidates,
      Block.compatible X Y = true := by
    simpa only [candidates] using
      movingSlotFrontierCandidates_compatible S adm hpost hhor hcompat
  have hnonempty : candidates.Nonempty := by
    exact ⟨End, by simp only [candidates, movingSlotFrontierCandidates,
      Finset.mem_insert, true_or]⟩
  obtain ⟨End', hselected⟩ := Option.isSome_iff_exists.mp
    (deepest?_isSome_of_compatible hcompatible hnonempty)
  have hEnd'Mem : End' ∈ candidates := Proofs.Engine.deepest?_mem hselected
  have hEndMem : End ∈ candidates := by
    simp only [candidates, movingSlotFrontierCandidates,
      Finset.mem_insert, true_or]
  have hold : Block.Preceq End End' :=
    Proofs.HealingLemmas.deepest?_dominates hselected hEndMem
      (hcompatible End hEndMem End' hEnd'Mem)
  refine ⟨End', hselected, hold, ?_, ?_⟩
  · intro v hv D hgenuine
    have hDMem : D ∈ candidates := by
      simp only [candidates, movingSlotFrontierCandidates,
        Finset.mem_insert]
      exact Or.inr ((movingSlotGenuineOutputs_mem_iff S rho c D).mpr
        ⟨v, hv, hgenuine⟩)
    exact Proofs.HealingLemmas.deepest?_dominates hselected hDMem
      (hcompatible D hDMem End' hEnd'Mem)
  · simp only [candidates, movingSlotFrontierCandidates,
      Finset.mem_insert] at hEnd'Mem
    rcases hEnd'Mem with hEq | hmem
    · exact Or.inl hEq
    · exact Or.inr
        ((movingSlotGenuineOutputs_mem_iff S rho c End').mp hmem)


/-- A genuine confirmation selected by an honest reader is a run block. -/
theorem runBlock_of_genuineConfirmation
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot} {D : Block V}
    (hD : GenuineConfirmationWith
      (NamedProfile.gradeContract
        (confirmationInputRead S rho w s).cache)
      S.E S.hc
      (Proofs.Optimistic.confStore S rho w s) s D) :
    ∃ Dn : NamedBlock V, Dn.erase = D ∧ RunBlock S rho Dn := by
  exact genuineConfirmation_runBlock_step S adm hw hD

/-- The selected slot frontier is a run block whenever the previous endpoint is. -/
theorem MovingSlotFrontierAt.runBlock
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {c : Slot} {End End' : Block V}
    (hrun : ∃ D : NamedBlock V, D.erase = End ∧ RunBlock S rho D)
    (hfrontier : MovingSlotFrontierAt S rho c End End') :
    ∃ D : NamedBlock V, D.erase = End' ∧ RunBlock S rho D := by
  rcases hfrontier.source with hEq | hsource
  · subst End'
    exact hrun
  · obtain ⟨v, hv, hgenuine⟩ := hsource
    exact runBlock_of_genuineConfirmation S adm hv hgenuine







/-
/-- The directed `h_max - 1` floor projects to the exact slot-entry prefix. -/
theorem MovingSlotEntryState.frontier_sub_one_le_endpointHeight
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hmajority: HonestWeightMajority S rho.honest)
    {t1: Time} {M0: Height} {s: Slot} {Prev End: Block V}
    (h: MovingSlotEntryState S rho t1 M0 s Prev End):
    honestHMaxBeforeIndex S rho
        (inclusiveEventIndex rho (Protocol.proposal_time S.E s)) - 1 ≤
      (derived_state S.E S.cfg End).h:= by
  obtain ⟨EndAt, hhistory, hEnd⟩:= h.eventHistory
  have hfloor:= hhistory.frontier_sub_one_le_endpointHeight
    S adm hmajority
  simpa only [hEnd] using hfloor
-/


/-
/-- The slot-entry state supplies the full root-side path classification at
the exact proposal-time prefix. A later vote or confirmation read still needs
its own processed-tree transfer. -/
theorem MovingSlotEntryState.endpoint_rootSideWithPath
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hmajority: HonestWeightMajority S rho.honest)
    {t1: Time} {M0: Height} {s: Slot} {Prev End: Block V}
    (h: MovingSlotEntryState S rho t1 M0 s Prev End)
    {v: V} (hv: v ∈ rho.honest)
    (hmem: End ∈
      (movingSlotEntryStore S rho s v).T)
    (hcompat: Block.compatible
      (Protocol.get_fg_root
        (movingSlotEntryStore S rho s v).toHealing.toFG) End = true):
    (Block.Preceq
        (Protocol.get_fg_root
          (movingSlotEntryStore S rho s v).toHealing.toFG) End ∧
      End ∈ Protocol.get_filtered_block_tree
        (movingSlotEntryStore S rho s v).toHealing.toFG ∧
      ∀ D: Block V,
        Block.Preceq
          (Protocol.get_fg_root
            (movingSlotEntryStore S rho s v).toHealing.toFG) D →
        Block.Preceq D End →
        D ∈ Protocol.get_filtered_block_tree
          (movingSlotEntryStore S rho s v).toHealing.toFG) ∨
    Block.Preceq End
      (Protocol.get_fg_root
        (movingSlotEntryStore S rho s v).toHealing.toFG):= by
  obtain ⟨EndAt, hhistory, hEnd⟩:= h.eventHistory
  have hroot:= hhistory.endpoint_rootSideWithPath_atIndex
    S adm hmajority hv (by
      simpa only [movingSlotEntryStore, hEnd] using hmem)
      (by simpa only [movingSlotEntryStore, hEnd] using hcompat)
  simpa only [movingSlotEntryStore, hEnd] using hroot
-/





#print axioms movingSlot_existsFrontier
#print axioms runBlock_of_genuineConfirmation
#print axioms MovingSlotFrontierAt.runBlock

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
