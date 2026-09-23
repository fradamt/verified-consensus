module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.MovingChainRoundFloorFields
public import DecoupledConsensusProofs.Generic.CanonicalRegimeFromChain

@[expose] public section

/-!
# The moving-chain round floor, or the exact lost-round obstruction

When a round is not lost, all honest selected FG roots are below all honest
previous-round SG carriers. Choose an honest root of maximum depth. The
linearity of ancestors below one carrier puts every other root below that
choice. The fold's carrier sandwich and later processed endpoint then give
the floor's cone witness.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A common carrier ceiling with a processed frontier-band witness
supplies the exact lost-or-floor alternative. No slot fold is needed.

`canonicalConeWitness_of_bandDescendant` supplies the cone witness. The named
store agrees with `Protocol.derive_named` on its bodies, while agreement with
`derived_state` of an erasure requires a query hypothesis. The `hwitness` field
therefore combines membership with the band bound: each honest round read
retains a named body above `End` whose derived height reaches the band. -/
theorem movingChainRoundFloor_or_lost_of_carrierCeiling
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {r : Round} {End : Block V}
    (hcarriers : ∀ w ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho w (r - 1)) End)
    (hwitness : ∀ v ∈ rho.honest, ∃ W : NamedBlock V,
      W ∈ (rho.storeBeforeTime S v (S.a r)).bodies ∧
      Block.Preceq End W.erase ∧
      (rho.storeBeforeTime S v (S.a r)).h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg W).h) :
    LostRoundAt S rho r ∨ ∃ C : Block V, RoundFloorFieldsAt S rho r C := by
  classical
  have _adm := adm
  by_cases hlost : LostRoundAt S rho r
  · exact Or.inl hlost
  · right
    have hne : rho.honest.Nonempty :=
      Protocol.honest_nonempty_of_honestCommittees hcom
    let root : V → Block V := fun v =>
      Protocol.get_fg_root (healStoreAt S rho v r).toFG
    obtain ⟨v0, hv0, hmaxEq⟩ :=
      Finset.exists_mem_eq_sup' hne (fun v => Block.depth (root v))
    have hmax : ∀ v ∈ rho.honest,
        Block.depth (root v) ≤ Block.depth (root v0) := by
      intro v hv
      rw [← hmaxEq]
      exact Finset.le_sup' (fun u => Block.depth (root u)) hv
    have hnotLost : ∀ v ∈ rho.honest, ∀ w ∈ rho.honest,
        Block.Preceq (root v) (actionSGBlockAt S rho w (r - 1)) := by
      intro v hv w hw
      by_contra hbad
      exact hlost ⟨v, hv, w, hw, hbad⟩
    obtain ⟨w0, hw0⟩ := hne
    have hroots : ∀ v ∈ rho.honest,
        Block.Preceq (root v) (root v0) := by
      intro v hv
      rcases Block.preceq_linear (hnotLost v hv w0 hw0)
          (hnotLost v0 hv0 w0 hw0) with hbelow | habove
      · exact hbelow
      · have heq : root v0 = root v :=
          Block.preceq_eq_of_depth_le habove (hmax v hv)
        rw [heq]
        exact Block.preceq_self _
    have hCendpoint : Block.Preceq (root v0)
        End :=
      Block.preceq_trans (hnotLost v0 hv0 w0 hw0) (hcarriers w0 hw0)
    refine ⟨root v0, ?_⟩
    refine
      { floorBelowCarriers := ?_
        floorAboveRoots := hroots
        floorWitness := ?_ }
    · intro w hw
      exact hnotLost v0 hv0 w hw
    · intro v hv
      obtain ⟨W, hWbody, hEndW, hWband⟩ := hwitness v hv
      exact canonicalConeWitness_of_bandDescendant S
        (Block.preceq_trans hCendpoint hEndW) hWbody hWband



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
