module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.RecoveryCrossingCore
public import DecoupledConsensusProofs.Protocol.ValidatorClient.Schedule

@[expose] public section

/-!
# Iterating the public raw height-progress contract

These lemmas consume `EventualHeightProgressFrom`; they do not assume or expose
recovery, canonicality, or finality facts.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Repeated applications of a uniform positive-lag progress contract gain at
least one honest frontier height per application. -/
theorem eventualHeightProgress_iterate
    (S : Setup V) {rho : Run V} {r0 lag r : Round}
    (progress : EventualHeightProgressFrom S rho r0 lag)
    (hr : r0 ≤ r) (k : Nat)
    (horizon : S.a (r + k * lag) ≤ rho.horizon) :
    honestHMaxAt S rho (S.a r) + k ≤
      honestHMaxAt S rho (S.a (r + k * lag)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hindex : r + (k + 1) * lag = (r + k * lag) + lag := by
        simp only [Nat.add_mul, Nat.one_mul, Nat.add_assoc]
      have hintermediateRound : r + k * lag ≤ r + (k + 1) * lag := by
        rw [hindex]
        exact Nat.le_add_right _ _
      have hintermediateHorizon :
          S.a (r + k * lag) ≤ rho.horizon :=
        (Assembly.a_mono S hintermediateRound).trans horizon
      have ih' := ih hintermediateHorizon
      have hstart : r0 ≤ r + k * lag := hr.trans (Nat.le_add_right r (k * lag))
      have hstep :
          honestHMaxAt S rho (S.a (r + k * lag)) <
            honestHMaxAt S rho (S.a ((r + k * lag) + lag)) :=
        progress.2 (r + k * lag) hstart (by simpa only [← hindex] using horizon)
      rw [hindex]
      simpa only [Nat.add_assoc] using
        (Nat.add_le_add_right ih' 1).trans (Nat.succ_le_iff.mpr hstep)




end HealingSurface
end Proofs
end DecoupledConsensusModel

end
