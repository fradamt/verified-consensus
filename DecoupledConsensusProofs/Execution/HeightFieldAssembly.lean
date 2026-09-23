module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ValidatorClient.HeightProgressFixedRoot
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedEntryCanonical
public import DecoupledConsensusProofs.Execution.SeedSourceCapClosure
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FixedRootSourceCap

@[expose] public section

/-!
# The height-progress field

This theorem composes the named seed and fixed-root proofs into
`EventualHeightProgressFrom` from the public run assumptions alone
(closed ).

The fixed-root target entry is proved by
`namedJustification_targetRoot_of_fixedRoot`. The source-height callback is
provided by `fixedRoot_sourceHeight_le_nextOpeningParent`, which uses the
common-root route at the actual fixed-root lifecycle window. The seed's
pointwise relative-grade canonicity proof is connected. Its promotion inputs
remain explicit.
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

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

/-- **The public height-progress field from the public run assumptions.** No
residual hypothesis remains: the seed side is closed by
`seedPredPromotionInputs_of_public` and the fixed-root side by
`fixedRoot_sourceHeight_le_nextOpeningParent`. `FinalAssembly` uses this term. -/
theorem heightProgress_public
    (S : Setup V) (hdelay : TimeoutDelayBound S delayExtra)
    {gap : Round} {rho : Run V} {rGST : Round}
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbot : BelowOneThird S rho.honest)
    (hpost : S.E.t_GST ≤ S.a rGST)
    (hrec : MultiProposerRecurrence S rho gap) :
    EventualHeightProgressFrom S rho rGST (progressLag' gap delayExtra) :=
  eventualHeightProgressFrom_of_seed S adm hcom hbot hrec
    (heightProgressSeedFrom_of_canonicity S adm hcom hbot hdelay hrec hpost
      (seedPredPromotionInputs_of_public S adm hcom hbot hdelay hrec))
    hdelay hpost
    (fixedRootProgress_of_rows S adm hcom hbot hrec hdelay
      (fixedRoot_sourceHeight_le_nextOpeningParent S adm hcom hbot))





end HealingSurface
end Proofs
end DecoupledConsensusModel

end
