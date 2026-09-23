module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.Confirmation
public import DecoupledConsensusProofs.Protocol.Handlers.ConfirmationRecordOrigin
public import DecoupledConsensusProofs.Protocol.Handlers.StableRecordWrites

@[expose] public section

/-! # Proof-layer residual for strong head extension

The public selection regimes do not carry this obligation. Strong-regime consumers
must pass it explicitly until height progress after healing discharges it.
-/

namespace DecoupledConsensusModel
namespace Internal

open Execution NamedRecoveryRead
open DecoupledConsensusModel.Proofs

variable {V : Type} [DecidableEq V] [Fintype V]



/-- The stronger post-healing residual: the complete stable write is below the
confirmation arm's result. This is the exact walk-bound form needed when a
keep-case residual does not expose the projected-G2 or FG-root arm. -/
def StableWriteBelowWalkFrom (S : Setup V) (rho : Run V) (t0 : Time) : Prop :=
  ∀ v ∈ rho.honest, ∀ s : Slot, t0 ≤ Protocol.confirmation_time S.E s →
    Protocol.confirmation_time S.E s ≤ rho.horizon →
    Block.Preceq (confirmationStableWrite S (confirmationInputRead S rho v s))
      (Protocol.advance_confirmed
        (confirmationInputRead S rho v s).st.core.latest_confirmed
        (namedConfirmationWalk S (confirmationInputRead S rho v s) s))

theorem StableWriteBelowWalkFrom.honestHeadExtendsStableFrom
    {S : Setup V} {rho : Run V} {t0 : Time}
    (h : StableWriteBelowWalkFrom S rho t0) :
    Internal.HonestHeadExtendsStableFrom S rho t0 := h

/-- The explicit prepared-read facts needed by the GST-zero floor discharge. -/
def CarrierWindowAt (S : Setup V) (rho : Run V) (t0 : Time) : Prop :=
  ∀ v ∈ rho.honest, ∀ s : Slot, t0 ≤ Protocol.confirmation_time S.E s →
    Protocol.confirmation_time S.E s ≤ rho.horizon →
    (∀ G, (NamedProfile.gradeContract
        (confirmationInputRead S rho v s).cache).stableRoot S.E S.hc
        (confirmationInputRead S rho v s).st.core.toHealing
        (S.hc.round_of (confirmationInputRead S rho v s).st.core.s) = some G →
      Block.Preceq G
        (namedConfirmationWalk (S := S) (confirmationInputRead S rho v s) s)) ∧
    Block.compatible (confirmationInputRead S rho v s).st.core.latest_confirmed
      (namedConfirmationWalk (S := S) (confirmationInputRead S rho v s) s) = true

theorem latest_compatible_confWalk_of_gstZero_of_carrierWindow
    (S : Setup V) {rho : Run V}
    (hcarrierWindow : CarrierWindowAt S rho 0) :
    ∀ v ∈ rho.honest, ∀ s : Slot,
      Protocol.confirmation_time S.E s ≤ rho.horizon →
      Block.compatible (confirmationInputRead S rho v s).st.core.latest_confirmed
        (namedConfirmationWalk (S := S) (confirmationInputRead S rho v s) s) = true := by
  intro v hv s hhor
  exact (hcarrierWindow v hv s (by
    exact Proofs.Optimistic.confirmation_time_nonneg S.E s) hhor).2


theorem stableWrite_preceq_advanceWalk_of_gstZero_of_carrierWindow
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    (hcarrierWindow : CarrierWindowAt S rho 0) :
    StableWriteBelowWalkFrom S rho 0 := by
  intro v hv s hs hhor
  have hnest : Block.Preceq
      (confirmationInputRead S rho v s).st.core.latest_stable
      (confirmationInputRead S rho v s).st.core.latest_confirmed := by
    let t := Protocol.confirmation_time S.E s
    let n := (rho.events.filter (fun e => decide (e.time < t))).length
    have hstate : NamedRun.stateBeforeTime S rho t v =
        NamedRun.stateBefore S rho n v := by
      simpa only [Run.stateBeforeTime, Run.stateBefore, n, t] using
        congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S sch t) v
    unfold confirmationInputRead NamedActionReads.confirmationReadAt
      NamedActionReads.confirmationReadFrom
    rw [hstate]
    exact ConfirmationOrigin.stateBefore_stable_below_confirmed S rho v n
  have hnew : confirmationStableWrite S (confirmationInputRead S rho v s) =
      (confirmationInputRead S rho v s).st.core.latest_stable ∨
      Block.Preceq (confirmationStableWrite S (confirmationInputRead S rho v s))
        (namedConfirmationWalk (S := S) (confirmationInputRead S rho v s) s) := by
    unfold confirmationStableWrite
    cases hroot : (NamedProfile.gradeContract
        (confirmationInputRead S rho v s).cache).stableRoot S.E S.hc
        (confirmationInputRead S rho v s).st.core.toHealing
        (S.hc.round_of (confirmationInputRead S rho v s).st.core.s) with
    | none => exact Or.inl rfl
    | some G =>
        dsimp only
        rcases Proofs.ConfirmationPolicy.advance_eq_old_or_candidate
          (confirmationInputRead S rho v s).st.core.latest_stable G with hkeep | hnew
        · exact Or.inl hkeep
        · exact Or.inr (by
            rw [hnew]
            exact (hcarrierWindow v hv s hs hhor).1 G hroot)
  exact StableRecord.preceq_advance_of_nesting hnew hnest
    (latest_compatible_confWalk_of_gstZero_of_carrierWindow S hcarrierWindow v hv s hhor)


theorem honestHeadExtendsStable_of_weakGenesis_of_carrierWindow
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    (hGST : S.E.t_GST = 0) (hcom : HonestCommittees S rho.honest)
    (hawake : ∀ q, 0 < q → S.a (q - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG q)
    (hcarrierWindow : CarrierWindowAt S rho 0) :
    Internal.HonestHeadExtendsStableFrom S rho 0 := by
  clear hGST hcom hawake
  exact (stableWrite_preceq_advanceWalk_of_gstZero_of_carrierWindow S
    core.toNamedScheduleWellFormed hcarrierWindow).honestHeadExtendsStableFrom

#print axioms honestHeadExtendsStable_of_weakGenesis_of_carrierWindow



end Internal
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.HealingSurface

open Internal Execution Internal.NamedRecoveryRead Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

namespace WeakGenesis





theorem honestHeadExtendsStable_of_weakGenesis_of_carrierWindow
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    (hGST : S.E.t_GST = 0) (hcom : HonestCommittees S rho.honest)
    (hawake : ∀ q, 0 < q → S.a (q - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG q)
    (hcarrierWindow : Internal.CarrierWindowAt S rho 0) :
    Internal.HonestHeadExtendsStableFrom S rho 0 :=
  Internal.honestHeadExtendsStable_of_weakGenesis_of_carrierWindow
    S core hGST hcom hawake hcarrierWindow

#print axioms honestHeadExtendsStable_of_weakGenesis_of_carrierWindow

end WeakGenesis


#print axioms StableWriteBelowWalkFrom.honestHeadExtendsStableFrom

end DecoupledConsensusModel.Proofs.HealingSurface

end
