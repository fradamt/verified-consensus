module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.CarrierAdmission
public import DecoupledConsensusProofs.Protocol.Schedule.ConfirmationHistory

@[expose] public section

/-!
# Post-GST accepted-block convergence

This is the availability-layer form of the fixed-cutoff relay hop. It is
kept below the healing-surface grade-delivery module so that Goldfish proposal
snapshot proofs can use the same typed `Synchrony.relay_block` contract
without introducing an import cycle.

**Named-runtime proof (design note).** The delivered object is a
`NamedBlock V` (`Object:= NamedObject`), stores are `Protocol.NamedStore V`
read through `.core`, and the two store invariants come from the named runtime
(`Proofs.NamedRuntime.stateBefore_F_mono`,
`Proofs.NamedStoreBridge.finalized_preceq_justified_stateBefore`) instead of the
retired `DepReachableStore` chain, so the theorem now takes no
`DeliveryWellFormed` premise beyond admissibility.
-/



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- If the FG root at an arbitrary later read is below `B`, then every earlier
delivery to that reader sees a finalized root below `B`. This is the common
time-parametric core of the existing vote-duty and confirmation-store
specializations. -/
theorem finalized_preceq_at_delivery_of_storeBeforeRoot_preceq
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {Gamma : Time} {v : V} {B : Block V} {X : NamedBlock V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v Gamma).core.toHealing.toFG) B)
    {i : Nat} {t : Time}
    (hi : rho.events[i]? = some (Event.deliver v (Object.block X) t))
    (hlt : t < Gamma) :
    Block.Preceq (rho.stateBefore S i v).st.core.F B := by
  let n := (rho.events.filter (fun e => decide (e.time < Gamma))).length
  have hiN : i < n := by
    by_contra hnot
    have hni : n ≤ i := Nat.le_of_not_gt hnot
    have hGamma : Gamma ≤ t :=
      Proofs.Optimistic.le_time_of_index_ge S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
        (t := Gamma) (j := i) (e := Event.deliver v (Object.block X) t)
        (by simpa only [n] using hni) hi
    exact (not_le_of_gt hlt) hGamma
  have hstore : rho.storeBeforeTime S v Gamma = (rho.stateBefore S n v).st := by
    show (NamedRun.stateBeforeTime S rho Gamma v).st = _
    rw [show NamedRun.stateBeforeTime S rho Gamma v =
      NamedRun.stateBefore S rho n v from
        congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed Gamma) v]
  have hmono : Block.Preceq (rho.stateBefore S i v).st.core.F
      (rho.storeBeforeTime S v Gamma).core.F := by
    rw [hstore]
    exact Proofs.NamedRuntime.stateBefore_F_mono S rho v (Nat.le_of_lt hiN)
  have hFJ : Block.Preceq (rho.storeBeforeTime S v Gamma).core.F
      (rho.storeBeforeTime S v Gamma).core.J := by
    rw [hstore]
    exact Proofs.NamedStoreBridge.finalized_preceq_justified_stateBefore S rho n v
  have hFroot : Block.Preceq (rho.storeBeforeTime S v Gamma).core.F
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v Gamma).core.toHealing.toFG) :=
    Proofs.Records.preceq_get_fg_root_of_F
      (st := (rho.storeBeforeTime S v Gamma).core.toHealing.toFG) hFJ
  exact Block.preceq_trans hmono (Block.preceq_trans hFroot hroot)

#print axioms finalized_preceq_at_delivery_of_storeBeforeRoot_preceq


end Protocol
end DecoupledConsensusModel

end
