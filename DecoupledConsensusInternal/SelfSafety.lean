module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Derived
public import DecoupledConsensusModel.Protocol.ValidatorClient

@[expose] public section

/-!
# P2 honest self-safety (design note P2; PROTOCOL.md#the-complete-protocol)

A validator that follows `alg:pair-rules` never emits attestations that satisfy
E1 or E2 — against itself in one attestation, or across any two of its own
emissions, under any delivery schedule.

The statement is at §5's layer, where `attest` is
`Protocol.attest` (PROTOCOL.md#the-complete-protocol). §6 redefines the duty
(PROTOCOL.md#the-complete-protocol) and adds the graded branch and the veto; re-proving P2
there is deferred with §6 (`the design note:12`).

Two shapes are forced here.

* **The schedule is the store sequence.** The record `Λ` is the only state
  carried between emissions — "it belongs to the validator, not to the store"
  (PROTOCOL.md#the-complete-protocol, choices S5.8) — so a delivery schedule enters the
  statement only as the stores the validator attests at. `AttestHistory`
  therefore quantifies over an arbitrary store at every step and threads only
  `Λ`. Nothing relates one store to the next: the weakest possible hypothesis,
  and what makes P2 hold "under any delivery schedule".
* **The emission budget is not assumed.** `HonestEmissionBudget` caps an honest
  validator at one attestation per round (PROTOCOL.md#the-complete-protocol), but P2 does
  not need it: a history of many emissions per round is admitted and the
  conclusion still holds, because `Λ` is indexed by height, not round.
-/

namespace DecoupledConsensusModel
namespace Internal

open Protocol (Record)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The Λ-thread (PROTOCOL.md#the-complete-protocol) -/

/-- P2 the record one attestation step threads out (PROTOCOL.md#the-complete-protocol).
`attest` returns `(Σ', Λ', a)`; this is `Λ'`. -/
def attest_record (record : Protocol.NamedRecord) (input : Protocol.NamedRecord.Input V) :
    Protocol.NamedRecord :=
  (Protocol.NamedRecord.create record input).1

/-- P2 the attestation one step emits (PROTOCOL.md#the-complete-protocol). -/
def attest_emission (record : Protocol.NamedRecord) (input : Protocol.NamedRecord.Input V) :
    NamedAttestation V :=
  (Protocol.NamedRecord.create record input).2

/-- P2 an honest attest history of the node `nd`: the record reached, and the
attestations emitted in order, after some finite sequence of `attest` calls
starting from `Λ` initial (PROTOCOL.md#the-complete-protocol).

Each step attests at an arbitrary store; only the record is threaded. The store
carries the whole of the node's view, so quantifying it freely at every step is
what "under any delivery schedule" means here. -/
inductive AttestHistory {V : Type} [DecidableEq V] [Fintype V] :
    Protocol.NamedRecord → List (NamedAttestation V) → Prop where
  /-- The empty history: the initial record, nothing emitted
  (PROTOCOL.md#the-complete-protocol). -/
  | nil : AttestHistory Protocol.NamedRecord.initial []
  /-- One more signing call, at an arbitrary shared-read input (the store
  determines the input; quantifying the input freely is the named form of
  "at an arbitrary store"). -/
  | step {record : Protocol.NamedRecord} {emitted : List (NamedAttestation V)}
      (input : Protocol.NamedRecord.Input V) :
      AttestHistory record emitted →
      AttestHistory (attest_record record input)
        (emitted ++ [attest_emission record input])

/-! ## The P2 statements (PROTOCOL.md#the-complete-protocol) -/

/-- P2 no single emission is slashable against itself — "the conflicting
occurrences can be in one attestation" (PROTOCOL.md#the-complete-protocol). This is the `a = b`
case of `NoPairSlashing`, named separately because the document names it. -/
def NoSelfSlashing (emitted : List (NamedAttestation V)) : Prop :=
  ∀ a ∈ emitted, Protocol.selfSlashable a.erase = false

/-- P2 no two emissions are slashable against each other
(PROTOCOL.md#the-complete-protocol). -/
def NoPairSlashing (emitted : List (NamedAttestation V)) : Prop :=
  ∀ a ∈ emitted, ∀ b ∈ emitted, Protocol.slashable a.erase b.erase = false

/-- **P2, honest self-safety** (design note P2; PROTOCOL.md#the-complete-protocol).

Every attest history of `nd` emits attestations that are slashable neither
alone nor in pairs.

`finality_pair` runs before `height_pair` so the lock it writes is visible in the
same action (PROTOCOL.md#the-complete-protocol), which is what closes the single-attestation
case; `Λ.target[h]`, `Λ.timeout[h]` and `Λ.lock[h]` are each written at most once
per height, which closes the cross-emission cases. -/
def HonestSelfSafety : Prop :=
  ∀ (record : Protocol.NamedRecord) (emitted : List (NamedAttestation V)),
    AttestHistory record emitted → NoSelfSlashing emitted ∧ NoPairSlashing emitted

end Internal
end DecoupledConsensusModel

end
