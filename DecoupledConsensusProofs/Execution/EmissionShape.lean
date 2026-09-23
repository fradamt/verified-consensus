module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.OutageInputs
public import DecoupledConsensusProofs.Execution.OutageProvenance
public import DecoupledConsensusProofs.Protocol.Handlers.SGArrival

@[expose] public section

/-! # The shape of an emitted attestation, over the named runtime

. `Optimistic/Alignment.lean` records that
`emits_attest_shape`, `emits_attest_awake` and `emits_attest_unique` blocked
type-checking when `Object.attest` began carrying a `NamedAttestation V`, and
declines to guess whether the bound attestation becomes named or stays erased.

The choice is settled by what is already proved here.
`Proofs.NamedOutageInputs.emitted_attestation_stages` establishes every clause of all
three lemmas at once, over `NamedAttestation V`, from the actual tick alone:
the emission is the emitter's own, at its round's action time, with the round
the emitter's own clock round at that read, the payload the attest duty's own
output, and the emitter awake. So the exports below are wrappers, not proofs.

They keep the retired names and sit in `Proofs.Optimistic`, so that a consumer
which already opens `Optimistic` needs only an added import; the attestation it
binds becomes `NamedAttestation V`.
-/


namespace DecoupledConsensusModel
namespace Proofs
namespace Optimistic

open Internal Execution Internal.NamedOutageEntry
variable {V : Type} [DecidableEq V] [Fintype V]

/-- **An emitted attestation is the emitter's own, at its round's action time**
(PROTOCOL.md#the-complete-protocol). -/
theorem emits_attest_shape (S : Setup V) {rho : NamedRun V} {v : V}
    {a : NamedAttestation V} {t : Time}
    (h : NamedRun.emits S rho v (NamedObject.attest a) t) :
    a.val_index = v ∧ t = S.a a.round := by
  obtain ⟨-, -, -, -, hval, -, ht, -⟩ :=
    Proofs.NamedOutageInputs.emitted_attestation_stages S rho h
  exact ⟨hval, ht⟩

/-- An actual attestation emission proves that its author was awake at that
action. No full-participation or admissibility premise is needed. -/
theorem emits_attest_awake (S : Setup V) {rho : NamedRun V} {v : V}
    {a : NamedAttestation V} {t : Time}
    (h : NamedRun.emits S rho v (NamedObject.attest a) t) :
    (S.node v).awake a.round = true := by
  obtain ⟨-, -, -, -, -, -, -, hawake⟩ :=
    Proofs.NamedOutageInputs.emitted_attestation_stages S rho h
  exact hawake


/-- The emitted attestation is exactly the attest duty's output on that read,
under the frame contract of the read's own cache. -/
theorem emits_attest_duty (S : Setup V) {rho : NamedRun V} {v : V}
    {a : NamedAttestation V} {t : Time}
    (h : NamedRun.emits S rho v (NamedObject.attest a) t) :
    ∃ i : Nat, rho.events[i]? = some (.tick v t) ∧
      (Protocol.NamedDuties.attest_with
        (NamedProfile.gradeContract
          (actionReadFrom S (NamedRun.stateBefore S rho i v) a.round).cache)
        S.E S.hc (S.node v)
        (actionReadFrom S (NamedRun.stateBefore S rho i v) a.round).st
        (actionReadFrom S (NamedRun.stateBefore S rho i v) a.round).record).2.2 = a := by
  obtain ⟨i, hi, -, hduty, -, -, -, -⟩ :=
    Proofs.NamedOutageInputs.emitted_attestation_stages S rho h
  exact ⟨i, hi, hduty⟩

/-- **An honest validator emits at most one attestation per round**
(PROTOCOL.md#the-complete-protocol). Both emissions are at `a_r`, the tick at an instant is
unique, and a tick emits at most one attestation. -/
theorem emits_attest_unique (S : Setup V) {rho : NamedRun V}
    (sch : ScheduleWellFormed S rho)
    {v : V} {a b : NamedAttestation V} {t₁ t₂ : Time}
    (h₁ : NamedRun.emits S rho v (NamedObject.attest a) t₁)
    (h₂ : NamedRun.emits S rho v (NamedObject.attest b) t₂)
    (hround : a.round = b.round) : a = b :=
  NamedOutageProvenance.emitted_same_round_unique S rho sch h₁ h₂ hround

#print axioms emits_attest_shape
#print axioms emits_attest_awake
#print axioms emits_attest_duty
#print axioms emits_attest_unique


/-! ## Delivery puts a row in the receiver's SG rows

`Proofs.HealingLemmas.Schedule.attest_pooled_of_delivery` is the one unarchived
class-d residue with live consumers. earlier's proof reached the pool through
`on_sg_vote_eq_two_guard`, `sg_pool_no_honest_equivocation` and
`sgRounds_stateBefore`, none of which exists here, and it used them to *rule
out* the handler's guard branches from honesty. The named form below does not
rule them out: it states the guard the handler actually imposes, so the caller
carries exactly the four side conditions `Protocol.on_sg_vote` reads and no
honesty premise at all.
-/










/-- **The emitting tick is at its round's action time** (earlier's
`Proofs.Optimistic.a_of_attest_mem`). An emitted attestation pins the tick's instant
to the action of the round the row itself names. -/
theorem a_of_attest_mem (S : Setup V) {rho : NamedRun V} {v : V}
    {a : NamedAttestation V} {t : Time}
    (h : NamedRun.emits S rho v (NamedObject.attest a) t) :
    ∃ r : Round, t = S.a r :=
  ⟨a.round, (emits_attest_shape S h).2⟩

/-- **The emitted row is the attest duty's own output** (earlier's
`Proofs.Optimistic.attest_eq_of_mem_on_tick_emit`, duty half). earlier's second conjunct
was about the erased store's `live_confirmed` across the same tick; that is a
store-transport fact, not part of the reconstruction, and is not restated here. -/
theorem attest_eq_of_mem_on_tick_emit (S : Setup V) {rho : NamedRun V} {v : V}
    {a : NamedAttestation V} {t : Time}
    (h : NamedRun.emits S rho v (NamedObject.attest a) t) :
    ∃ i : Nat, rho.events[i]? = some (.tick v t) ∧
      (Protocol.NamedDuties.attest_with
        (NamedProfile.gradeContract
          (actionReadFrom S (NamedRun.stateBefore S rho i v) a.round).cache)
        S.E S.hc (S.node v)
        (actionReadFrom S (NamedRun.stateBefore S rho i v) a.round).st
        (actionReadFrom S (NamedRun.stateBefore S rho i v) a.round).record).2.2 = a :=
  emits_attest_duty S h

#print axioms a_of_attest_mem
#print axioms attest_eq_of_mem_on_tick_emit

end Optimistic
end Proofs
end DecoupledConsensusModel

end
