module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.NamedConfirmationWalk

@[expose] public section

/-! # Actual candidates of the user-facing confirmation record -/

namespace DecoupledConsensusModel
namespace Internal

open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The user candidate computed by a confirmation tick at an event prefix. -/
def userCandidateAtIndex (S : Setup V) (rho : Run V) (v : V)
    (i : Nat) (time : Time) : Block V :=
  let n := NamedActionReads.confirmationReadFrom S (NamedRun.stateBefore S rho i v) time
  namedConfirmationWalk S n (S.E.slotOf time - 1)


/-- The SG candidate a confirmation tick writes when the walk fails the gate
(addendum 35 ): under a contract with an optional
selection, the selection on the same prepared read at the duty's slot, taken
exactly when the walk is not eligible; `none` under the walk contract, and
`none` when the walk is eligible, since the walk is then the value written.
This is the not-eligible arm of `update_confirmation_with` read off the
prepared read, the third value of the confirmation record beside genesis and
the walk. -/
def userSGCandidateAtIndex (S : Setup V) (rho : Run V) (v : V)
    (i : Nat) (time : Time) : Option (Block V) :=
  let n := NamedActionReads.confirmationReadFrom S (NamedRun.stateBefore S rho i v) time
  let s := S.E.slotOf time - 1
  match (NamedProfile.gradeContract n.cache).confirmationSG with
  | .optional select =>
    if confirmationEligible S.E n.st.core s (namedConfirmationWalk S n s) then none
    else select S.E S.hc n.st.core.toHealing s


/-- A user candidate is the value an actual confirmation event writes through
`advance_confirmed`: the complete confirmation walk result, or, when the walk
fails the gate under a contract with an optional selection, the SG candidate
. The walk arm includes the SG-root case when Goldfish is
unavailable. -/
def UserConfirmationSelectionAt (S : Setup V) (rho : Run V) (v : V)
    (i : Nat) (C : Block V) : Prop :=
  ∃ time : Time,
    rho.events[i]? = some (Event.tick v time) ∧
      0 < S.E.slotOf time ∧
      time = Protocol.support_cutoff S.E (S.E.slotOf time) ∧
      (userCandidateAtIndex S rho v i time = C ∨
        userSGCandidateAtIndex S rho v i time = some C)

/-- Earlier user candidates are below one endpoint. This proof invariant is
distinct from the history of protocol confirmations and FG-root floor values. -/
def PriorUserCandidatesPreceqAtIndex (S : Setup V) (rho : Run V) (v : V)
    (n : Nat) (B : Block V) : Prop :=
  ∀ i C, i < n → UserConfirmationSelectionAt S rho v i C → Block.Preceq C B

/-- The corresponding history before a strict time read. -/
def PriorUserCandidatesPreceqBefore (S : Setup V) (rho : Run V) (v : V)
    (time : Time) (B : Block V) : Prop :=
  PriorUserCandidatesPreceqAtIndex S rho v
    (rho.events.filter (fun e => decide (e.time < time))).length B

/-- Agreement of actual user candidates. Regime theorems must derive this
invariant from protocol behavior, rather than assume it as a safety condition. -/
def HonestUserCandidatesFormChain (S : Setup V) (rho : Run V) : Prop :=
  ∀ v ∈ rho.honest, ∀ i C, UserConfirmationSelectionAt S rho v i C →
    ∀ w ∈ rho.honest, ∀ j D, UserConfirmationSelectionAt S rho w j D →
      Block.compatible C D = true

end Internal
end DecoupledConsensusModel

end
