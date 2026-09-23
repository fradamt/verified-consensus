module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.CanonicalRegimeFromChain

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]




/-- The carrier facts used by the height count, with the proposal named. -/
structure CanonicalCarrierHeightReadAt
    (S : Setup V) (rho : Run V) (q0 r : Round) : Prop where
  openingLive : ∀ v ∈ rho.honest, ∀ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P →
    (actionStoreAt S rho v r).st.core.live_confirmed = P.erase
  openingSource : ∀ v ∈ rho.honest, ∀ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P → ∀ Q,
    actionFGSource S (actionReadAt S rho v r) = some Q → Q = P.erase
  heightHistory : ∀ P : NamedBlock V,
    proposedBlockAt S rho (S.hc.opening_slot r) = some P →
    CanonicalHeightSourceHistoryAt S rho q0 r P

/-- A full regime supplies the conditional height-read facts. -/
theorem CanonicalRegimeRoundAt.toHeightRead
    {S : Setup V} {rho : Run V} {q0 r : Round}
    (h : CanonicalRegimeRoundAt S rho q0 r) :
    CanonicalCarrierHeightReadAt S rho q0 r :=
  ⟨h.openingLive, fun v hv P hP _Q hsource =>
    Option.some.inj (hsource.symm.trans (h.openingSource v hv P hP)),
    h.heightHistory⟩




end HealingSurface
end Proofs
end DecoupledConsensusModel

end
