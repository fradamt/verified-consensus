module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ValidatorClient.Schedule
public import DecoupledConsensusProofs.Execution.EmissionShape

@[expose] public section

/-!
# Recovery action intervals

The final Section 7 action times are strictly increasing. Therefore, an
attestation emitted in the half-open interval `[a_r, a_(r+1))` is exactly a
round-`r` attestation. This lets one recovery step obtain its source invariant
from `GradeFormsAt r P`; it does not need an unbounded history premise.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Section 7 round-action times are strictly increasing. -/
theorem actionTime_strictMono (S : Setup V) : StrictMono S.a := by
  intro r q hrq
  have hrq' : (r : Time) < (q : Time) := by exact_mod_cast hrq
  have hRnat : 0 < S.hc.R :=
    lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two
  have hR : (0 : Time) < (S.hc.R : Time) := by exact_mod_cast hRnat
  have hrounds :
      (r : Time) * (S.hc.R : Time) <
        (q : Time) * (S.hc.R : Time) :=
    Int.mul_lt_mul_of_pos_right hrq' hR
  have hscale : (0 : Time) < 4 * S.E.Δ := by
    exact Int.mul_pos (by norm_num) S.E.Δ_pos
  have hscaled := Int.mul_lt_mul_of_pos_left hrounds hscale
  unfold Setup.a Protocol.HealConfig.a Protocol.HealConfig.opening_slot slotStart
  push_cast
  simpa only [add_comm] using
    (add_lt_add_right hscaled (6 * S.E.Δ))





end HealingSurface
end Proofs
end DecoupledConsensusModel

end
