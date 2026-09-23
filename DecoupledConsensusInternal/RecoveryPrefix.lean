module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Availability
public import DecoupledConsensusInternal.Safety
public import DecoupledConsensusInternal.Definitions.NamedEvidence

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Causal recovery prefixes

Recovery reasons only about objects and honest stores available at one exact
event prefix. No declaration in this module ranges over a later run suffix.
-/

namespace DecoupledConsensusModel
namespace Internal

open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Objects delivered in the first `n` events. -/
def objectsBeforeIndex (rho : Run V) (n : Nat) : List (Object V) :=
  (rho.events.take n).filterMap Event.object?

/-- A named block available from the exact event prefix: either a delivery
in that prefix or a held body in an honest store at that prefix. -/
def PrefixRunBlock (S : Setup V) (rho : Run V) (n : Nat) (B : NamedBlock V) : Prop :=
  Object.block B ∈ objectsBeforeIndex rho n ∨
    ∃ v ∈ rho.honest, B ∈ (rho.stateBefore S n v).st.bodies

/-- Every block available at the exact event prefix has named finalized
height at most `hF0`. -/
def PrefixFinalityCap
    (S : Setup V) (rho : Run V) (n : Nat) (hF0 : Height) : Prop :=
  ∀ B, PrefixRunBlock S rho n B →
    (Protocol.derive_named S.E S.cfg B).h_F ≤ hF0

/-- A finalization above `hF0` already visible at the exact event prefix. -/
def ObservedFinalityBeforeIndex
    (S : Setup V) (rho : Run V) (n : Nat) (hF0 : Height) : Prop :=
  ∃ carrier : NamedBlock V, ∃ checkpoint : Block V, ∃ blocked : Height,
    PrefixRunBlock S rho n carrier ∧
    NamedFinalizedAt S.E S.cfg carrier checkpoint blocked ∧
    hF0 < blocked

/-! ## Honest-store causal scope -/

/-- Every held body in an honest store at the exact event prefix has named
finalized height at most `hF0`. Faulty-only deliveries are outside this
recovery surface. -/
def HonestPrefixFinalityCap
    (S : Setup V) (rho : Run V) (n : Nat) (hF0 : Height) : Prop :=
  ∀ v ∈ rho.honest, ∀ B ∈ (rho.stateBefore S n v).st.bodies,
    (Protocol.derive_named S.E S.cfg B).h_F ≤ hF0

/-- A finalization above `hF0` visible in one honest store at the exact event
prefix. -/
def HonestObservedFinalityBeforeIndex
    (S : Setup V) (rho : Run V) (n : Nat) (hF0 : Height) : Prop :=
  ∃ v ∈ rho.honest, ∃ carrier ∈ (rho.stateBefore S n v).st.bodies,
    ∃ checkpoint : Block V, ∃ blocked : Height,
      NamedFinalizedAt S.E S.cfg carrier checkpoint blocked ∧ hF0 < blocked

/-- No honest attestation emitted strictly before event prefix `n` has a
nonempty height pair at `blocked`. The emitted rows are the named tick's
own output at that event (`NamedRun.emittedAt`). -/
def NoLocalHeightPairBefore
    (S : Setup V) (rho : Run V) (n : Nat) (blocked : Height) : Prop :=
  ∀ {i : Nat} {v : V} {t : Time} {a : NamedAttestation V},
    i < n →
    v ∈ rho.honest →
    rho.events[i]? = some (Event.tick v t) →
    Object.attest a ∈ NamedRun.emittedAt S rho i v t →
    a.height_pair.erase.height? ≠ some blocked

/-- The exact prefix block universe has the recovery-height `nj` bit wherever
its named derived height is `blocked`, and no member records a justification
at `blocked`. The two source forms of `PrefixRunBlock` cover prefix
deliveries and exact honest-prefix stores. -/
def PrefixNJUniverse
    (S : Setup V) (rho : Run V) (n : Nat) (blocked : Height) : Prop :=
  ∀ B, PrefixRunBlock S rho n B →
    ((Protocol.derive_named S.E S.cfg B).h = blocked →
      (Protocol.derive_named S.E S.cfg B).nj = true) ∧
    (Protocol.derive_named S.E S.cfg B).h_j ≠ blocked

/-- The exact honest-prefix store universe has the recovery-height `nj` bit
wherever its named derived height is `blocked`, and no member records a
justification at `blocked`. -/
def HonestPrefixNJUniverse
    (S : Setup V) (rho : Run V) (n : Nat) (blocked : Height) : Prop :=
  ∀ v ∈ rho.honest, ∀ B ∈ (rho.stateBefore S n v).st.bodies,
    ((Protocol.derive_named S.E S.cfg B).h = blocked →
      (Protocol.derive_named S.E S.cfg B).nj = true) ∧
    (Protocol.derive_named S.E S.cfg B).h_j ≠ blocked

end Internal
end DecoupledConsensusModel

end
