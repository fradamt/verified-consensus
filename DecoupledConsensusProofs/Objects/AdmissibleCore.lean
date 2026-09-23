module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Assumptions.Regimes
public import DecoupledConsensusInternal.Definitions.NamedOutageEntry

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Proof-layer admissibility assembly

Public statements keep non-network execution validity and partial synchrony as
separate premises. Existing proof implementations consume the historical
five-family bundle. This module is the only assembly seam between those forms.
-/

namespace DecoupledConsensusModel.Proofs

open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The healing boundary is at least the action time of its round. -/
theorem a_le_healingBoundaryTime (S : Setup V) (q : Round) :
    S.a q ≤ Statements.Instantiation.healingBoundaryTime S q := by
  unfold Statements.Instantiation.healingBoundaryTime Setup.a Protocol.HealConfig.a
    Protocol.vote_time Env.t slotStart
  push_cast
  have hmul : (6 : Time) * S.E.Δ ≤ 9 * S.E.Δ :=
    Int.mul_le_mul_of_nonneg_right (by omega) S.E.Δ_pos.le
  calc
    4 * S.E.Δ * (S.hc.opening_slot q : Time) + 6 * S.E.Δ ≤
        4 * S.E.Δ * (S.hc.opening_slot q : Time) + 9 * S.E.Δ :=
      Int.add_le_add_left hmul _
    _ = 4 * S.E.Δ * ((S.hc.opening_slot q : Time) + 2) + S.E.Δ := by ring

/-- Historical five-family input, available only to proof implementation. -/
abbrev AdmissibleCore (S : Setup V) (rho : Run V) : Prop := NamedAdmissibleCore S rho

namespace AdmissibleCore

abbrev toScheduleWellFormed := @NamedAdmissibleCore.toNamedScheduleWellFormed
abbrev toDeliveryWellFormed := @NamedAdmissibleCore.toNamedDeliveryWellFormed
abbrev toRootCollisionFree := @NamedAdmissibleCore.toNamedRootCollisionFree
abbrev toUnforgeableSignatures := @NamedAdmissibleCore.toNamedUnforgeable
abbrev toSynchrony := @NamedAdmissibleCore.toNamedSynchrony

/-- Assemble the historical proof input from the two explicit public parts. -/
def ofParts {S : Setup V} {rho : Run V}
    (execution : ExecutionValid S rho) (synchrony : PartialSynchrony S rho) :
    AdmissibleCore S rho where
  toNamedScheduleWellFormed := execution.toNamedScheduleWellFormed
  toNamedDeliveryWellFormed := execution.toNamedDeliveryWellFormed
  toNamedRootCollisionFree := execution.toNamedRootCollisionFree
  toNamedUnforgeable := execution.toNamedUnforgeable
  toNamedSynchrony := synchrony

/-- Assemble the full-participation input used by existing strong-run proofs. -/
def admissibleOfParts {S : Setup V} {rho : Run V}
    (execution : ExecutionValid S rho) (synchrony : PartialSynchrony S rho)
    (allAwake : ∀ v ∈ rho.honest, ∀ r : Round, S.E.t_GST ≤ S.a r → S.a r ≤ rho.horizon →
      (S.node v).awake r = true) : Admissible S rho where
  toExecutionValid := execution
  toNamedSynchrony := synchrony
  all_awake := allAwake

end AdmissibleCore
end DecoupledConsensusModel.Proofs

namespace DecoupledConsensusModel

open Internal Execution

variable {V : Type} [DecidableEq V] [Fintype V]

namespace Execution.Admissible

/-- Proof-only projection to the historical five-family input. -/
def toNamedAdmissibleCore {S : Setup V} {rho : Run V} (h : Admissible S rho) :
    NamedAdmissibleCore S rho :=
  Proofs.AdmissibleCore.ofParts h.toExecutionValid h.toNamedSynchrony

end Execution.Admissible

namespace Statements.WeakGenesis

/-- Proof-only reconstruction of the historical five-family input. -/
def core {S : Setup V} {rho : Run V} (h : Statements.WeakGenesis S rho) :
    Proofs.AdmissibleCore S rho :=
  Proofs.AdmissibleCore.ofParts h.execution h.synchrony

end Statements.WeakGenesis

namespace Statements.StrongRecoveryPrefix

/-- Proof-only reconstruction of the historical full-participation input. -/
def admissible {S : Setup V} {rho : Run V} {rGST gap : Round} {extra : Nat} {n : Round}
    (h : Statements.StrongRecoveryPrefix S rho rGST gap extra n) : Admissible S rho :=
  Proofs.AdmissibleCore.admissibleOfParts h.execution h.synchrony h.allAwake

end Statements.StrongRecoveryPrefix

namespace Statements.WeakContinuation

/-- Proof-only reconstruction of the historical five-family input. -/
def core {S : Setup V} {source rho : Run V} {endRound : Round}
    (h : Statements.WeakContinuation S source rho endRound) :
    Proofs.AdmissibleCore S rho :=
  Proofs.AdmissibleCore.ofParts h.execution h.synchrony

end Statements.WeakContinuation

namespace Statements.StrongFinalityRun

/-- Proof-only reconstruction of the historical full-participation input. -/
def admissible {S : Setup V} {rho : Run V} {gap : Round}
    (h : Statements.StrongFinalityRun S rho gap) : Admissible S rho :=
  Proofs.AdmissibleCore.admissibleOfParts h.execution h.synchrony h.allAwake

end Statements.StrongFinalityRun

namespace Internal.NamedOutageEntry.OutageExecution

/-- Proof-only reconstruction of the historical named five-family input. -/
def core {S : Setup V} {rho : NamedRun V} {b0 b1 : Time}
    (h : Internal.NamedOutageEntry.OutageExecution S rho b0 b1) :
    NamedAdmissibleCore S rho :=
  Proofs.AdmissibleCore.ofParts h.execution h.synchrony

end Internal.NamedOutageEntry.OutageExecution

end DecoupledConsensusModel

end
