module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionHistory
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Execution.Runtime
public import DecoupledConsensusProofs.Execution.Wire

@[expose] public section

/-!
# Event-indexed attestation suffix history

This module records only the half-open event suffix `[n0, n)`. Its time-facing
projection keeps target, confirmed-root, and height-source facts separate. The
suffix has no premise about earlier events and its endpoint is proof state, not
protocol state.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Strict time-prefix index -/


/-- Every strict time prefix ending no later than a scheduled tick lies before
that tick's event index. -/
theorem filterBefore_length_le_tickIndex
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {i : Nat} {v : V} {t Gamma : Time}
    (hi : rho.events[i]? = some (Event.tick v t)) (hGamma : Gamma ≤ t) :
    (rho.events.filter (fun e => decide (e.time < Gamma))).length ≤ i := by
  by_contra hnot
  have hiN : i <
      (rho.events.filter (fun e => decide (e.time < Gamma))).length :=
    Nat.lt_of_not_ge hnot
  have hmem : Event.tick v t ∈
      rho.events.filter (fun e => decide (e.time < Gamma)) := by
    rw [Proofs.Optimistic.filter_eq_take S sch _ (Proofs.Optimistic.downward_lt Gamma)]
    exact List.mem_of_getElem? (by
      rw [List.getElem?_take_of_lt hiN]
      exact hi)
  have htGamma := (List.mem_filter.mp hmem).2
  simp only [decide_eq_true_eq, Event.time] at htGamma
  exact (not_lt_of_ge hGamma) htGamma

/-! ## Event-indexed suffix -/





/-! ## Time-facing suffix -/


/-- Every named run block sharing an erased root below a named endpoint's
erasure is a named ancestor of that endpoint.

This is the root-collision-free lift from an erased prefix fact to the named
one ( 1636/): `Proofs.NamedAncestry.erased_ancestor_lift` produces some
named ancestor `A` of `B` with `A.erase = X.erase`; `RunBlock` is closed under
taking named ancestors (`Proofs.NamedRuntime.blockInRun_of_ancestor`), so `A` and `X`
are both run blocks with the same erased root, hence equal by
root-collision-freeness. -/
theorem namedPreceq_of_runBlock_erase_preceq
    {S : Setup V} {rho : Run V}
    (adm : Admissible S rho) {X B : NamedBlock V}
    (hXrun : RunBlock S rho X) (hBrun : RunBlock S rho B)
    (h : Block.Preceq X.erase B.erase) :
    NamedBlock.Preceq X B := by
  obtain ⟨A, hAB, hAerase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B h
  have hArun : RunBlock S rho A :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hBrun hAB
  have hrootEq : A.root = X.root := by
    rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root X, hAerase]
  have hAX : A = X :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      A X hArun hXrun A X
      (Or.inl (Proofs.NamedAncestry.named_self A)) (Or.inr (Proofs.NamedAncestry.named_self X))
      hrootEq
  rw [← hAX]
  exact hAB



end Protocol
end DecoupledConsensusModel

end
