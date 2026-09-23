module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.MovingChainFloorBridge
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

/-!
# The base of the slot fold

The iteration of `MovingChainIterateRun` starts from a slot-entry state. This
module builds the two halves of that first state that do not depend on any
previous window.

* `movingFrontierChainState_bootstrapAt` is the empty-interval moving history
  at any cutoff time: the endpoint function is constant and every per-event
  field is vacuous. It generalises
  `movingFrontierChainState_of_exactLifecycle`, which fixes the cutoff at the
  round action `a_q`.
* `MovingSlotPreEntry.toEntry` is the last mile: a pre-entry state — the moving
  history through the slot's proposal cursor plus the PREVIOUS slot's honest
  vote cone — together with the slot's head equality is a full entry state.
  Both of the step's branches are instances of it, and so is the base.

What the base still needs from the boundary side is exactly the pre-entry: the
history from the bootstrap through the first slot's proposal cursor, and that
slot's previous-slot cone. The cone is the one input the moving chain cannot
produce for itself, because the votes it speaks about are cast before the
bootstrap cutoff.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.NamedRecoveryRead
open Protocol
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]



/-- **The two boundary inputs of the moving history.**

Both speak about the world BEFORE the fold's cutoff, which is why the fold
cannot produce them for itself.

* `frontierFloor` is monotonicity of the honest frontier from the cutoff on:
  the boundary block sits at `M0` and every honest reader has processed it
  there, so no honest `h_max` ever falls back below `M0`.
* `boundaryTargets` is the healing exit's store-local safety: an honest height
  target at or above `M0 - 1` emitted before the cutoff names a source on the
  boundary chain. Everything emitted after the cutoff is bounded by the moving
  history's own `outputs` field instead. -/
structure MovingBoundaryFloor (S : Setup V) (rho : Run V) (t1 : Time)
    (M0 : Height) (B : Block V) : Prop where
  frontierFloor : ∀ v ∈ rho.honest, ∀ k : Nat,
    strictEventIndex rho t1 ≤ k →
    M0 ≤ (rho.stateBefore S k v).st.core.h_max
  boundaryTargets : ∀ (a : NamedAttestation V) (ta : Time),
    a.val_index ∈ rho.honest →
    rho.emits S a.val_index (Object.attest a) ta →
    ta < t1 →
    ∀ (hh : Height) (target : BlockId), M0 - 1 ≤ hh →
    a.height_pair = NamedHeightPair.vote hh target false →
    ∀ X : NamedBlock V, RunBlock S rho X → X.erase.root = target →
    Block.Preceq X.erase B


/-- **A processed block pins the reader's frontier from below.**

`h_max` dominates every processed block's height (`TreeHeightsLeHMax`), and the
store's own state map agrees with the derived state on processed blocks, so a
block held at height `M0` forces `M0 ≤ h_max`. -/
theorem hMax_ge_of_mem_stateBefore
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} {k : Nat} {D : NamedBlock V}
    (hmem : D ∈ (rho.stateBefore S k v).st.bodies) :
    (derive_named S.E S.cfg D).h ≤
      (rho.stateBefore S k v).st.core.h_max := by
  exact Proofs.NamedStoreBridge.heights_le_hMax_stateBefore S rho k v D hmem

/-- **The frontier floor, from a block every honest reader has processed.**

This is `MovingBoundaryFloor.frontierFloor` reduced to ONE fact about the
boundary block: that every honest reader holds it at the cutoff index. The
floor at later indices is `h_max` monotonicity, which is free. -/
theorem frontierFloor_of_processed_at_start
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {M0 : Height} {D : NamedBlock V} {n0 : Nat}
    (hheight : (derive_named S.E S.cfg D).h = M0)
    (hmem : ∀ v ∈ rho.honest,
      D ∈ (rho.stateBefore S n0 v).st.bodies) :
    ∀ v ∈ rho.honest, ∀ k : Nat, n0 ≤ k →
      M0 ≤ (rho.stateBefore S k v).st.core.h_max := by
  intro v hv k hk
  rw [← hheight]
  exact (hMax_ge_of_mem_stateBefore S adm (hmem v hv)).trans
    (NamedNumericStore.stateBefore_hmax_mono S rho v hk)












/-
/-- **The base of the fold, packaged.**

One entry state, with the two facts about its own slot that the fold's
invariant records, is a one-slot `MovingSlotFoldAt`. Every other field is
vacuous on a one-slot range: nothing has been passed yet. With this, the base
of the whole fold reduces to two things and no more — the moving history
through the first slot's proposal cursor, and that slot's PREVIOUS-slot honest
vote cone. -/
theorem movingSlotFoldAt_of_entry
    (S: Setup V) {rho: Run V}
    {t1: Time} {M0: Height} {c: Slot} {Prev End: Block V}
    (hentry: MovingSlotEntryState S rho t1 M0 (c + 1) Prev End)
    (hproposal: S.E.proposer (c + 1) ∈ rho.honest →
      End = proposedBlock S rho (c + 1))
    (hparent: S.E.proposer (c + 1) ∈ rho.honest →
      Block.Preceq Prev (proposedParent S rho (c + 1))):
    MovingSlotFoldAt S rho t1 M0 (c + 1) (c + 1) (fun _ => Prev) End where
  base:= Nat.le_refl _
  entry:= hentry
  endpointProposal:= hproposal
  mono:= fun _ _ _ _ _ => Block.preceq_self _
  parent:= by
    intro d hd hdle hdprop
    have hdeq: d = c + 1:= Nat.le_antisymm hdle hd
    subst hdeq
    exact hparent hdprop
  absorbed:= fun d hd hdlt => absurd (hd.trans_lt hdlt) (lt_irrefl _)
  confAbsorbed:= fun d hd hdlt =>
    absurd (hd.trans_lt (Nat.lt_of_succ_lt hdlt)) (lt_irrefl _)
  confAbove:= fun d hd hdlt =>
    absurd (hd.trans_lt (Nat.lt_of_succ_lt hdlt)) (lt_irrefl _)
  windowCone:= fun d hd hdlt => absurd (hd.trans_lt hdlt) (lt_irrefl _)
  historyAt:= by
    intro d hd hdle
    have hdeq: d = c + 1:= Nat.le_antisymm hdle hd
    subst hdeq
    obtain ⟨EndAt, hhistory, hprev, _hEnd⟩:= hentry.prevEndpoint
    exact ⟨EndAt, hhistory.prefix
      (strictEventIndex_mono rho hentry.startTime)
      (strictEventIndex_le_inclusiveEventIndex rho _), hprev⟩
-/





end HealingSurface
end Proofs
end DecoupledConsensusModel

end
