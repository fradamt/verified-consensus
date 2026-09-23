module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.OpeningCarrier
public import DecoupledConsensusProofs.Execution.CanonicalDensityDischarge

@[expose] public section

/-! # Carrier selection with two earlier honest openings
The density proof needs only the selected carrier. The selection retains
its earlier honest openings for the later finality proof.
-/
namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
open Internal Execution Internal.HealingSurface Protocol Proofs.Optimistic Proofs.HealingLemmas
variable {V : Type} [DecidableEq V] [Fintype V]



theorem proposerRecurrence_of_openingCarrierRecurrence
    (S : Setup V) {rho : Run V} {gap : Round}
    (h : ProposerOpeningCarrierRecurrence S rho gap) :
    MultiProposerRecurrence S rho gap := by
  intro k
  obtain ⟨r, hlo, hhi, _, _, hc⟩ := h k
  exact ⟨r, (Nat.le_add_right k 2).trans hlo, hhi, hc⟩



















end HealingSurface
end Proofs
end DecoupledConsensusModel

end
