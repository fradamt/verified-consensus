module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.W4HandoffStructures

@[expose] public section

/-! # The named handoff boundary without erased derived-state fields
The named event history uses the endpoint's named row bound and the
processed-block floor. The erased height and erased row cap of
`MovingChainHandoffRowCapBoundary` feed only the compatibility history.
This record keeps the selected height `M0`; in particular its
`targets` field still uses the threshold `M0 - 1`.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface
open Protocol
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The fields consumed by the named handoff history. -/
structure W4NamedHandoffBoundaryCore (S : Setup V) (rho : Run V)
    (q : Round) (t1 : Time) (M0 : Height) (D : NamedBlock V) : Prop where
  height : (derive_named S.E S.cfg D).h = M0
  run : RunBlock S rho D
  processed : ∀ v ∈ rho.honest,
    D ∈ (rho.stateBefore S (strictEventIndex rho t1) v).st.bodies
  targets : ∀ (a : NamedAttestation V) (ta : Time),
    a.val_index ∈ rho.honest →
    rho.emits S a.val_index (Object.attest a) ta →
    ta < t1 →
    ∀ (hh : Height) (target : BlockId), M0 - 1 ≤ hh →
    a.height_pair = NamedHeightPair.vote hh target false →
    ∀ X : NamedBlock V, RunBlock S rho X → X.erase.root = target →
    Block.Preceq X.erase D.erase
  rowCapNamed : ∀ {j : Nat} {a : NamedAttestation V} {time : Time},
    a.val_index ∈ rho.honest →
    rho.events[j]? = some (Event.tick a.val_index time) →
    Object.attest a ∈ NamedRun.emittedAt S rho j a.val_index time →
    j < strictEventIndex rho t1 → ∀ hh : Height,
    a.height_pair.erase.height? = some hh →
    ∀ E : NamedBlock V, E.erase = D.erase → RunBlock S rho E →
      hh ≤ (derive_named S.E S.cfg E).h
  carrierCeiling : ∀ r : Round,
    S.hc.round_of (S.hc.opening_slot q + 3) = r + 1 →
    ∀ u ∈ rho.honest, Block.Preceq (actionSGBlockAt S rho u r) D.erase

/-- The named boundary retains the exact moving floor and target threshold. -/
theorem W4NamedHandoffBoundaryCore.toBoundaryFloor
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} {t1 : Time} {M0 : Height} {D : NamedBlock V}
    (h : W4NamedHandoffBoundaryCore S rho q t1 M0 D) :
    MovingBoundaryFloor S rho t1 M0 D.erase where
  frontierFloor := frontierFloor_of_processed_at_start S adm h.height h.processed
  boundaryTargets := h.targets

/-- The named bootstrap needs no erased height or erased row cap. -/
theorem W4NamedHandoffBoundaryCore.bootstrapAtN
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} {t1 : Time} {M0 : Height} {D : NamedBlock V}
    (h : W4NamedHandoffBoundaryCore S rho q t1 M0 D) :
    MovingFrontierChainStateN S rho t1 M0
      (strictEventIndex rho t1) (strictEventIndex rho t1)
      (fun _ => D.erase) where
  historyStart := rfl
  start_le := Nat.le_refl _
  endpointRun := fun _ _ _ => ⟨D, rfl, h.run⟩
  endpointMono := fun _ hj hlt => absurd (hj.trans_lt hlt) (lt_irrefl _)
  proposalChain := fun _ hj hlt => absurd (hj.trans_lt hlt) (lt_irrefl _)
  genuineConfirmations := fun _ hj hlt => absurd (hj.trans_lt hlt) (lt_irrefl _)
  sgCarriers := fun _ hj hlt => absurd (hj.trans_lt hlt) (lt_irrefl _)
  outputs := fun _ hj hlt => absurd (hj.trans_lt hlt) (lt_irrefl _)
  anchors := fun _ hj hlt => absurd (hj.trans_lt hlt) (lt_irrefl _)
  oldRows_named := h.rowCapNamed
  frontierFloor := (h.toBoundaryFloor S adm).frontierFloor
  boundaryTargets := (h.toBoundaryFloor S adm).boundaryTargets



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
