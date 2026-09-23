module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryProposalConfirmationRead
public import DecoupledConsensusProofs.Protocol.Handlers.FrameFloorBridge
public import DecoupledConsensusProofs.Protocol.Grades.GoldfishConePersistence
public import DecoupledConsensusProofs.Protocol.Grades.Q10Frame
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

/-!
# Bridges for clean action reads and prepared confirmation anchors

The relative grade is read at the G2-domain read. A retained action read is
therefore a separate proof-layer input. This module packages that input with
the existing named clean-read producer.

The anchor bridge below also keeps the frame-floor case explicit. It does not
identify a bare contract with a prepared contract.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.NamedRecoveryRead
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]



/-- A named grade, retained action reads, and retained next-domain reads give a
clean action read. The retention facts are proof-layer inputs. -/
theorem cleanActionReadFor_of_namedGradeFormsAt_and_retained_active
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (hr : 0 < r) {P : Block V}
    (hforms : NamedGradeFormsAt S rho r P)
    (hpost : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hwindow : ∀ v ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho v (S.a r) P)
    (hactive : ∀ w ∈ rho.honest,
      P ∈ Protocol.get_filtered_block_tree
        (healStoreAt S rho w (r + 1)).toFG)
    (hdomainWindow : ∀ w ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho w
        (domain S.E S.hc (r + 1) .g2) P) :
    CleanActionReadFor S rho r P := by
  have hownActive : ∀ v ∈ rho.honest,
      P ∈ PhaseGrades.filteredTree (actionReadAt S rho v r) := by
    intro v hv
    exact namedGradeFormsAt_actionStore_of_window S hforms hv
      (hwindow v hv)
  have hactiveDomain : ∀ w ∈ rho.honest,
      P ∈ PhaseGrades.filteredTree (relativeG2Read S rho (r + 1) w) := by
    intro w hw
    have hretained := hdomainWindow w hw
    exact activeDomain_of_retainedAtDomainRead S (fun x hx => by
      simpa only [FinalityFilterRetainedAtRead] using hdomainWindow x hx) w hw
  exact cleanActionReadFor_of_namedGradeFormsAt_and_next_active
    S adm hr hforms hpost hcut hownActive hactive hactiveDomain

/-! ## Prepared confirmation-anchor floor -/


/-! ## Relative grade implication -/


/-- The phase-based G2 early cutoff is strictly before the round's Gamma zero. -/
theorem early_g2_lt_Γ_0 (S : Setup V) (r : Round) :
    early S.E S.hc r .g2 < S.hc.Γ_0 S.E.Δ r := by
  have hopen : opening S.E S.hc r = S.hc.Γ_0 S.E.Δ r :=
    (Protocol.Γ_0_eq_proposal_time S.hc S.E r).symm
  unfold early Phase.earlyOffset
  rw [hopen]
  have hpos : (0 : Int) < S.E.Δ := S.E.Δ_pos
  have hdelta : (-5 : Int) * S.E.Δ < 0 := by omega
  simpa only [zero_mul, add_zero] using
    (Int.add_lt_add_left hdelta (S.hc.Γ_0 S.E.Δ r))

/- The named prepared Goldfish path and induction producers are now available
in `NamedGoldfishConeRun` (`af9ce08`). This bridge module does not re-export
those declarations. -/

end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms cleanActionReadFor_of_namedGradeFormsAt_and_retained_active
#print axioms early_g2_lt_Γ_0
end DecoupledConsensusModel.Proofs.HealingSurface

end
