module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.SlotInduction

@[expose] public section

/-!
# Bounded captured-cone fold

This file contains only the structural fold used by the recovery argument.
The caller supplies the protocol-specific one-slot step and may package any
of its exits in one proposition. Thus this leaf does not encode a recovery
measure, a protocol state, or a particular classification of exits.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Fold a captured Goldfish cone from `lo` through `hi`.

The step hypothesis is required only for indices in the half-open interval
`[lo, hi)`. At every step it may either produce the next cone or return the
caller-supplied `Exit` proposition. Consequently the result is the cone at
`hi`, or the first (or any later) exit encountered by the fold. -/
theorem honestVotesCone_or_exit_of_bounded_fold
    (S : Setup V) (rho : Run V) {lo hi : Nat} {B : Block V}
    {Exit : Prop}
    (hlohi : lo ≤ hi)
    (hbase : NamedHonestVotesCone S rho lo
      (fun X => Block.Preceq B X))
    (hstep : ∀ k, lo ≤ k → k < hi →
      NamedHonestVotesCone S rho k
        (fun X => Block.Preceq B X) →
      NamedHonestVotesCone S rho (k + 1)
        (fun X => Block.Preceq B X) ∨ Exit) :
    NamedHonestVotesCone S rho hi
        (fun X => Block.Preceq B X) ∨ Exit := by
  revert lo
  induction hi with
  | zero =>
      intro lo hlohi hbase hstep
      have hlo : lo = 0 := Nat.le_zero.mp hlohi
      subst lo
      exact Or.inl hbase
  | succ hi ih =>
      intro lo hlohi hbase hstep
      by_cases htop : lo = hi + 1
      · subst lo
        exact Or.inl hbase
      · have hmid : lo ≤ hi := by omega
        have hfold :
            NamedHonestVotesCone S rho hi
                (fun X => Block.Preceq B X) ∨ Exit :=
          ih hmid hbase (fun k hk hkh hcone =>
            hstep k hk (by omega) hcone)
        rcases hfold with hcone | hexit
        · rcases hstep hi hmid (Nat.lt_succ_self hi) hcone with hnext | hexit
          · exact Or.inl hnext
          · exact Or.inr hexit
        · exact Or.inr hexit


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
