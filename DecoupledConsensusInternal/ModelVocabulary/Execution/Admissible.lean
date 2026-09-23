module
public import DecoupledConsensusModel
public import DecoupledConsensusModel.Execution.Run
public import DecoupledConsensusInternal.ModelVocabulary.Execution.Setup
public import DecoupledConsensusInternal.ModelVocabulary.Execution.NamedRun
public import DecoupledConsensusInternal.ModelVocabulary.Execution.NamedAdmissible
public import DecoupledConsensusInternal.ModelVocabulary.Execution.NamedReceiptCalls

@[expose] public section

/-! Canonical environmental contracts for the selected named execution.
The full-participation clause has the finite-horizon formula used by the
selected runtime. Named binding, admission, and timeout processing are active
in the execution path. -/
namespace DecoupledConsensusModel.Execution
variable {V : Type} [DecidableEq V] [Fintype V]

abbrev ScheduleWellFormed (S : Setup V) (rho : Run V) : Prop := NamedScheduleWellFormed S rho
abbrev DeliveryWellFormed (S : Setup V) (rho : Run V) : Prop := NamedDeliveryWellFormed S rho
abbrev RootCollisionFree (S : Setup V) (rho : Run V) : Prop := NamedRootCollisionFree S rho
/-- The four non-network execution-validity families.

This public bundle contains schedule well-formedness, delivery well-formedness,
run-scoped root collision freedom, and authenticity.
It deliberately does not contain a synchrony premise. -/
structure ExecutionValid (S : Setup V) (rho : Run V) : Prop extends
  NamedScheduleWellFormed S rho, NamedDeliveryWellFormed S rho,
  NamedRootCollisionFree S rho,
  NamedUnforgeable S rho

/-- The partial-synchrony network premise, kept separate from execution validity. -/
abbrev PartialSynchrony (S : Setup V) (rho : Run V) : Prop := NamedSynchrony S rho

abbrev HealthyPrefixDelivery (S : Setup V) (rho : Run V) (cut : Time) : Prop :=
  NamedHealthyPrefixDelivery S rho cut
namespace ScheduleWellFormed
abbrev mk := @NamedScheduleWellFormed.mk
abbrev horizon_nonneg {S : Setup V} {rho : Run V} (h : ScheduleWellFormed S rho) :=
  NamedScheduleWellFormed.horizon_nonneg h
abbrev sorted {S : Setup V} {rho : Run V} (h : ScheduleWellFormed S rho) :=
  NamedScheduleWellFormed.sorted h
abbrev nodup := @NamedScheduleWellFormed.nodup
abbrev in_horizon {S : Setup V} {rho : Run V} (h : ScheduleWellFormed S rho) :=
  NamedScheduleWellFormed.in_horizon h
end ScheduleWellFormed
namespace DeliveryWellFormed
abbrev mk := @NamedDeliveryWellFormed.mk
abbrev wire := @NamedDeliveryWellFormed.wire
abbrev deps := @NamedDeliveryWellFormed.deps
abbrev fresh := @NamedDeliveryWellFormed.fresh
end DeliveryWellFormed
namespace RootCollisionFree
abbrev mk := @NamedRootCollisionFree.mk
abbrev root_injective := @NamedRootCollisionFree.root_injective
end RootCollisionFree
namespace Unforgeable
abbrev mk := @NamedUnforgeable.mk
abbrev unforgeable := @NamedUnforgeable.unforgeable
abbrev carried_gf := @NamedUnforgeable.carried_gf
abbrev carried_attest := @NamedUnforgeable.carried_attest
end Unforgeable
namespace Synchrony
abbrev mk := @NamedSynchrony.mk
abbrev broadcast := @NamedSynchrony.broadcast
abbrev relay_block := @NamedSynchrony.relay_block
abbrev relay_gf_vote := @NamedSynchrony.relay_gf_vote
abbrev relay_attest := @NamedSynchrony.relay_attest
end Synchrony
namespace ExecutionValid
abbrev toScheduleWellFormed := @ExecutionValid.toNamedScheduleWellFormed
abbrev toDeliveryWellFormed := @ExecutionValid.toNamedDeliveryWellFormed
abbrev toRootCollisionFree := @ExecutionValid.toNamedRootCollisionFree
abbrev toUnforgeableSignatures := @ExecutionValid.toNamedUnforgeable
/-- Forget the network component of the historical named proof input. -/
def ofNamedAdmissibleCore {S : Setup V} {rho : Run V}
    (h : NamedAdmissibleCore S rho) : ExecutionValid S rho where
  toNamedScheduleWellFormed := h.toNamedScheduleWellFormed
  toNamedDeliveryWellFormed := h.toNamedDeliveryWellFormed
  toNamedRootCollisionFree := h.toNamedRootCollisionFree
  toNamedUnforgeable := h.toNamedUnforgeable
end ExecutionValid
namespace PartialSynchrony
abbrev mk := @NamedSynchrony.mk
abbrev broadcast := @NamedSynchrony.broadcast
abbrev relay_block := @NamedSynchrony.relay_block
abbrev relay_gf_vote := @NamedSynchrony.relay_gf_vote
abbrev relay_attest := @NamedSynchrony.relay_attest
end PartialSynchrony
namespace AdmissibleCore
abbrev mk := @ExecutionValid.mk
abbrev toScheduleWellFormed := @ExecutionValid.toNamedScheduleWellFormed
abbrev toDeliveryWellFormed := @ExecutionValid.toNamedDeliveryWellFormed
abbrev toRootCollisionFree := @ExecutionValid.toNamedRootCollisionFree
abbrev toUnforgeableSignatures := @ExecutionValid.toNamedUnforgeable
end AdmissibleCore

/-- Backward-compatible public name for the named authenticity premise. -/
abbrev Unforgeable (S : Setup V) (rho : Run V) : Prop := NamedUnforgeable S rho

/-- Backward-compatible public name for the named synchrony premise. -/
abbrev Synchrony (S : Setup V) (rho : Run V) : Prop := NamedSynchrony S rho

/-- Backward-compatible public name for non-network execution validity. -/
abbrev AdmissibleCore (S : Setup V) (rho : Run V) : Prop := ExecutionValid S rho

/-- Full participation over an explicitly split execution and network contract. -/
structure Admissible (S : Setup V) (rho : Run V) : Prop extends
    ExecutionValid S rho, PartialSynchrony S rho where
  all_awake : ∀ v ∈ rho.honest, ∀ r : Round, S.a r ≤ rho.horizon →
    (S.node v).awake r = true

end DecoupledConsensusModel.Execution

end
