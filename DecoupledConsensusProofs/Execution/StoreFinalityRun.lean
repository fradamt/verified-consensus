module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.Monotone
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.StoreFinalityLockIn
public import DecoupledConsensusProofs.Protocol.ChainState.SlashableBoundBridge
public import DecoupledConsensusProofs.Execution.FinalizedViable

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Run-facing finalized-prefix canonicality

This file lifts the shared doc1 store properties to the final Section 7 run.
Canonicality has its operational meaning: every call to `Protocol.get_head`,
for every vote input and slot argument, returns a descendant of the protected
block.

For a finality accepted by the same store, the finality-specific proof open items at
`get_fg_root`; one generic lemma transports the prefix through the SG root and
the final Goldfish walk. External B11 lock-in has doc1's one necessary
exception: in the non-cascade case the FG root can still be the older local
finality below external `F`, and the height-filter argument makes the walk pass
through `F`.
-/

/-! proof note. The two private step folds are gone: finality
monotonicity across one named world event is
`Protocol.step_F_mono` and body retention is
`NamedBodyRetention.step_bodies_subset`, both public over `NamedWorld.step`.
The processed tree is read off the retained bodies through the coherence tree
view, so no separate tree-step induction is needed. -/



namespace DecoupledConsensusModel
namespace Proofs
namespace StoreFinality

open Protocol (HeightConfig)
open Protocol (HealConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]



/-- Folding any later event suffix moves a node's finalized root forward. -/
private theorem foldlWorld_F_mono (S : Setup V) (v : V)
    (events : List (Event V)) (w : World V) :
    Block.Preceq (w v).st.F ((events.foldl (World.step S) w) v).st.F := by
  induction events generalizing w with
  | nil => exact Block.preceq_self _
  | cons e events ih =>
      exact Block.preceq_trans (Protocol.step_F_mono S w e v)
        (ih (w := World.step S w e))

/-- Folding any later event suffix retains every held named body. -/
private theorem foldlWorld_bodies_subset (S : Setup V) (v : V)
    (events : List (Event V)) (w : World V) :
    (w v).st.bodies ⊆ ((events.foldl (World.step S) w) v).st.bodies := by
  induction events generalizing w with
  | nil => exact Finset.Subset.refl _
  | cons e events ih =>
      exact (NamedBodyRetention.step_bodies_subset S w e v).trans
        (ih (w := World.step S w e))

/-- A node's finalized root is monotone between two `stateAt` reads. -/
theorem stateAt_F_mono (S : Setup V) {ρ : Run V}
    (sch : ScheduleWellFormed S ρ) (v : V) {t t' : Time} (htt' : t ≤ t') :
    Block.Preceq (ρ.storeAt S v t).F (ρ.storeAt S v t').F := by
  obtain ⟨events, hevents⟩ := Protocol.stateAt_eq_foldl S sch htt'
  simp only [Run.storeAt, hevents]
  exact foldlWorld_F_mono S v events (Run.stateAt S ρ t)

/-- A node's processed block tree is monotone between two `stateAt` reads.
The tree is the erasure image of the retained bodies at both reads. -/
theorem stateAt_T_subset (S : Setup V) {ρ : Run V}
    (sch : ScheduleWellFormed S ρ) (v : V) {t t' : Time} (htt' : t ≤ t') :
    (ρ.storeAt S v t).T ⊆ (ρ.storeAt S v t').T := by
  intro B hB
  have hTt : (Run.readAt S ρ t v).st.core.T =
      (Run.readAt S ρ t v).st.bodies.image NamedBlock.erase :=
    (Proofs.NamedRuntime.readAt_invariants S ρ t v).1.1.1.1
  have hTt' : (Run.readAt S ρ t' v).st.core.T =
      (Run.readAt S ρ t' v).st.bodies.image NamedBlock.erase :=
    (Proofs.NamedRuntime.readAt_invariants S ρ t' v).1.1.1.1
  have hB' : B ∈ (Run.readAt S ρ t v).st.core.T := hB
  rw [hTt] at hB'
  obtain ⟨D, hD, hDB⟩ := Finset.mem_image.mp hB'
  show B ∈ (Run.readAt S ρ t' v).st.core.T
  rw [hTt']
  refine Finset.mem_image.mpr ⟨D, ?_, hDB⟩
  obtain ⟨events, hevents⟩ := Protocol.stateAt_eq_foldl S sch htt'
  have hsub : (Run.readAt S ρ t v).st.bodies ⊆
      (NamedRun.readAt S ρ t' v).st.bodies := by
    have h := foldlWorld_bodies_subset S v events (Run.stateAt S ρ t)
    rwa [← hevents] at h
  exact hsub hD

/-- A block held by an honest node at a `stateAt` read is in the run-wide block
scope used by collision freedom and accountable safety. -/
theorem runBlock_of_storeAt_mem (S : Setup V) {ρ : Run V}
    (sch : ScheduleWellFormed S ρ) {v : V} (hv : v ∈ ρ.honest)
    {t : Time} {B : Block V} (hB : B ∈ (ρ.storeAt S v t).T) :
    ∃ D : NamedBlock V, D.erase = B ∧ RunBlock S ρ D :=
  Proofs.NamedStoreBridge.runBlock_of_mem_core_T_readAt S sch hv t hB

/-- Once one store has finalized `F`, every later FG root at that store
descends from `F`. This is the finality-specific core of operational
canonicality; it does not inspect SG or Protocol. -/
theorem finalized_preceq_fgRoot_from (S : Setup V) {ρ : Run V}
    (adm : AdmissibleCore S ρ) {v : V} {F : Block V} {t₀ : Time}
    (hF : Block.Preceq F (ρ.storeAt S v t₀).F) :
    ∀ t : Time, t₀ ≤ t → t ≤ ρ.horizon →
      Block.Preceq F
        (Protocol.get_fg_root (ρ.storeAt S v t).toHealing.toFG) := by
  intro t ht₀ _
  have hcurrent : Block.Preceq F (ρ.storeAt S v t).F :=
    Block.preceq_trans hF
      (stateAt_F_mono S adm.toNamedScheduleWellFormed v ht₀)
  have hFJ : FinalizedPrecedesJustified (ρ.storeAt S v t).core :=
    Proofs.NamedStoreBridge.finalized_preceq_justified_stateAt S ρ t v
  exact Block.preceq_trans hcurrent (finalized_preceq_fgRoot hFJ)



private theorem run_bodies_stateAt (S : Setup V) {ρ : Run V}
    (sch : ScheduleWellFormed S ρ) {v : V} (hv : v ∈ ρ.honest) (t : Time) :
    ∀ D ∈ (ρ.storeAt S v t).bodies, RunBlock S ρ D := by
  obtain ⟨n, hn⟩ := Proofs.Bridges.stateAt_eq_stateBefore S sch t
  intro D hD
  apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i := n)
  simpa only [Run.storeAt, hn] using hD

private theorem run_bodies_stateBeforeTime (S : Setup V) {ρ : Run V}
    (sch : ScheduleWellFormed S ρ) {v : V} (hv : v ∈ ρ.honest) (t : Time) :
    ∀ D ∈ (ρ.storeBeforeTime S v t).bodies, RunBlock S ρ D := by
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S sch t
  intro D hD
  apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i := n)
  simpa only [Run.storeBeforeTime, hn] using hD

theorem lockIn_external_fgRoot_boundary_storeAt {S : Setup V} {ρ : Run V}
    (adm : AdmissibleCore S ρ) (hsb : SlashableBound S ρ)
    {v : V} (hv : v ∈ ρ.honest) {t : Time}
    {BF B : NamedBlock V} {F : Block V} {h_f : Height}
    (hBF : RunBlock S ρ BF) (hB : B ∈ (ρ.storeAt S v t).bodies)
    (hjust : Internal.NamedJustifiedAt S.E S.cfg B F h_f)
    (hfin : Statements.Instantiation.NamedFinalizedAt S.E S.cfg BF F h_f) :
    Block.Preceq F (ρ.storeAt S v t).core.J ∧
      Internal.HasViableDescendant (ρ.storeAt S v t).core F ∧
      (Block.Preceq F
          (Protocol.get_fg_root (ρ.storeAt S v t).core.toHealing.toFG) ∨
        (Protocol.get_fg_root (ρ.storeAt S v t).core.toHealing.toFG =
            (ρ.storeAt S v t).core.F ∧
          Block.Preceq (ρ.storeAt S v t).core.F F ∧
          h_f < (ρ.storeAt S v t).core.h_max - 1)) := by
  exact lockIn_external_fgRoot_boundary
    (Proofs.NamedRuntime.readAt_invariants S ρ t v).1.1.1
    (NamedJustificationBound.noHighJustifications_stateAt S ρ t v)
    (Proofs.Bridges.namedProvenance_readAt S ρ t v)
    (NamedJustificationBound.justificationBelowMax_stateAt S ρ t v)
    (NamedFinalizedViable.finalizedViable_stateAt S ρ t v)
    (Proofs.NamedStoreBridge.finalized_preceq_justified_stateAt S ρ t v)
    (Proofs.NamedStoreBridge.maximum_carrier_stateAt S ρ t v) hB hjust hsb
    adm.toNamedRootCollisionFree hBF
    (run_bodies_stateAt S adm.toNamedScheduleWellFormed hv t) hfin

theorem lockIn_external_fgRoot_boundary_storeBeforeTime {S : Setup V} {ρ : Run V}
    (adm : AdmissibleCore S ρ) (hsb : SlashableBound S ρ)
    {v : V} (hv : v ∈ ρ.honest) {read : Time}
    {BF B : NamedBlock V} {F : Block V} {h_f : Height}
    (hBF : RunBlock S ρ BF) (hB : B ∈ (ρ.storeBeforeTime S v read).bodies)
    (hjust : Internal.NamedJustifiedAt S.E S.cfg B F h_f)
    (hfin : Statements.Instantiation.NamedFinalizedAt S.E S.cfg BF F h_f) :
    Block.Preceq F (ρ.storeBeforeTime S v read).core.J ∧
      Internal.HasViableDescendant (ρ.storeBeforeTime S v read).core F ∧
      (Block.Preceq F
          (Protocol.get_fg_root
            (ρ.storeBeforeTime S v read).core.toHealing.toFG) ∨
        (Protocol.get_fg_root
            (ρ.storeBeforeTime S v read).core.toHealing.toFG =
              (ρ.storeBeforeTime S v read).core.F ∧
          Block.Preceq (ρ.storeBeforeTime S v read).core.F F ∧
          h_f < (ρ.storeBeforeTime S v read).core.h_max - 1)) := by
  exact lockIn_external_fgRoot_boundary
    (Proofs.NamedRuntime.stateBeforeTime_invariants S ρ read v).1.1.1
    (NamedJustificationBound.noHighJustifications_stateBeforeTime S ρ read v)
    (Proofs.Bridges.namedProvenance_stateBeforeTime S ρ read v)
    (NamedJustificationBound.justificationBelowMax_stateBeforeTime S ρ read v)
    (NamedFinalizedViable.finalizedViable_stateBeforeTime S ρ read v)
    (Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S ρ read v)
    (Proofs.NamedStoreBridge.maximum_carrier_stateBeforeTime S ρ read v) hB hjust hsb
    adm.toNamedRootCollisionFree hBF
    (run_bodies_stateBeforeTime S adm.toNamedScheduleWellFormed hv read) hfin

end StoreFinality
end Proofs
end DecoupledConsensusModel

end
