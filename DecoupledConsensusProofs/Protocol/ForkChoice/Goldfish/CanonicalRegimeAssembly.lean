module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.CarrierTimeoutGate
public import DecoupledConsensusProofs.Objects.MovingChainStep
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ReaderLocalCone
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge

@[expose] public section

/-!
# Canonical-regime assembly bridges

This module records the strongest canonical-root and grade-activity facts
available from the retained moving-frontier state. The public suffix
execution does not retain that state, so these theorems state the exact
pointwise facts needed to cross that interface.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]


/-
/-- After two public rises, every honest FG root at a read before the moving
cursor is on the retained canonical endpoint chain. -/
theorem honestRoots_canonical
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {n0 i: Nat} {End: Nat → Block V}
    (hmoving: MovingFrontierChainState S rho t1 M0 n0 i End)
    {t: Time} (hcursor: strictEventIndex rho t ≤ i)
    (htwoRises: ∀ v ∈ rho.honest,
      M0 + 2 ≤ (rho.storeBeforeTime S v t).h_max):
    ∀ v ∈ rho.honest,
      Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S v t).toHealing.toFG) (End i):= by
  intro v hv
  exact hmoving.newRoot_on_endpointChain S adm hfb hv hcursor
    (htwoRises v hv)
-/

/-- A canonical floor with a local cone witness is active at every honest round
read when every selected FG root is below that floor.

This theorem isolates the exact local geometry. It does not claim that
`CanonicalSuffixExecution` supplies the root or witness premises.

**The floor's own processing is not needed.** Parent closure and `C ⪯ W`
put the floor in the reader's tree for free, so only the witness has to be
exhibited there.

**The witness, not the floor, carries the band.** The earlier form asked the
floor itself to sit at the reader's frontier band, which fails as soon as the
frontier rises past a fixed historical floor. Viability only ever needs a
PROCESSED DESCENDANT of the floor in the band, which is exactly
`CanonicalConeWitness`, and the floor's own processing then comes for free from
parent closure. -/
theorem gradeFloor_active_everywhere
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {C : Block V}
    (hroot : ∀ v ∈ rho.honest,
      Block.Preceq
        (Protocol.get_fg_root (healStoreAt S rho v r).toFG) C)
    (hwitness : ∀ v ∈ rho.honest,
      CanonicalConeWitness (rho.storeBeforeTime S v (S.a r)).core C) :
    ∀ v ∈ rho.honest,
      C ∈ Protocol.get_filtered_block_tree
        (healStoreAt S rho v r).toFG := by
  intro v hv
  let st := rho.storeBeforeTime S v (S.a r)
  have hpc : ParentClosed st.core := by
    simpa only [st] using
      Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho (S.a r) v
  have hFJ : Block.Preceq st.core.F st.core.J := by
    simpa only [st] using
      Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
        (S.a r) v
  have hrootC : Block.Preceq
      (Protocol.get_fg_root st.core.toHealing.toFG) C := by
    simpa only [st, healStoreAt] using hroot v hv
  obtain ⟨W, hWT, hCW, hheightW⟩ : CanonicalConeWitness st.core C :=
    hwitness v hv
  have hactive := canonicalConeSegment_mem_filtered_of_root_preceq
    hpc hFJ hrootC hWT hheightW (Block.preceq_self C) hCW
  simpa only [st, healStoreAt] using hactive


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
