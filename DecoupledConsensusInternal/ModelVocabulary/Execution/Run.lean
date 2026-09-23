module
public import DecoupledConsensusModel
public import DecoupledConsensusModel.Execution.Run
public import DecoupledConsensusInternal.ModelVocabulary.Execution.Event
public import DecoupledConsensusInternal.ModelVocabulary.Execution.Node
public import DecoupledConsensusInternal.ModelVocabulary.Execution.Objects
public import DecoupledConsensusInternal.ModelVocabulary.Execution.NamedRun
public import DecoupledConsensusInternal.ModelVocabulary.Execution.NamedReceiptCalls

@[expose] public section

/-! Canonical execution observations are computed by the selected named fold.
Geometry remains the internal Block projection; the wire carries full named
blocks and rows. No erased-run simulation or state reconstruction is used. -/
namespace DecoupledConsensusModel.Execution

namespace Run
abbrev honest {V : Type} (rho : Run V) : Finset V := Generic.Run.honest rho
abbrev horizon {V : Type} (rho : Run V) : Time := Generic.Run.horizon rho
abbrev events {V : Type} (rho : Run V) : List (Event V) := Generic.Run.events rho
abbrev stateBefore {V : Type} [DecidableEq V] [Fintype V]
    (S : Setup V) (rho : Run V) (i : Nat) : World V :=
  NamedRun.stateBefore S rho i
abbrev stateAt := @NamedRun.readAt
abbrev readAt := @NamedRun.readAt
abbrev stateBeforeTime {V : Type} [DecidableEq V] [Fintype V]
    (S : Setup V) (rho : Run V) (t : Time) : World V :=
  NamedRun.stateBeforeTime S rho t
abbrev emits {V : Type} [DecidableEq V] [Fintype V]
    (S : Setup V) (rho : Run V) (v : V) (o : Object V) (t : Time) : Prop :=
  NamedRun.emits S rho v o t
abbrev processes := @NamedRun.processes
abbrev acceptsAt := @NamedRun.acceptsAt
variable {V : Type} [DecidableEq V] [Fintype V]

def storeBeforeTime (S : Setup V) (rho : Run V) (v : V) (t : Time) : Protocol.NamedStore V :=
  (NamedRun.stateBeforeTime S rho t v).st

def lastTickIn (v : V) : List (Event V) → Option Time
  | [] => none
  | e :: rest => match lastTickIn v rest with
    | some t => some t
    | none => match e with
      | .tick w t => if w = v then some t else none
      | .deliver _ _ _ => none
end Run

abbrev RunBlock := @NamedRun.blockInRun
abbrev RunGoldfishVote := @NamedRun.goldfishVoteInRun
namespace Run
variable {V : Type} [DecidableEq V] [Fintype V]

end Run

structure WorldView (V : Type) where
  time : Time
  honest : Finset V
  state : V → NodeState V
  objects : List (Object V)

namespace Run

variable {V : Type} [DecidableEq V] [Fintype V]

def viewAt (S : Setup V) (rho : Run V) (t : Time) : WorldView V :=
  ⟨t, rho.honest, NamedRun.readAt S rho t, NamedRun.objects rho⟩

def viewBeforeTime (S : Setup V) (rho : Run V) (t : Time) : WorldView V :=
  ⟨t, rho.honest, NamedRun.stateBeforeTime S rho t, NamedRun.objects rho⟩

def roundView (S : Setup V) (rho : Run V) (r : Round) : WorldView V :=
  viewBeforeTime S rho (S.a r)

def recordAt (S : Setup V) (rho : Run V) (v : V) (t : Time) :
    Protocol.NamedRecord :=
  (NamedRun.readAt S rho t v).record

end Run

namespace NamedRun

variable {V : Type} [DecidableEq V] [Fintype V]

def attestationInRun (S : Setup V) (rho : NamedRun V) (a : NamedAttestation V) : Prop :=
  (∃ v : V, ∃ t : Time, processes S rho v (.attest a) t) ∨
    (∃ B : NamedBlock V, blockInRun S rho B ∧ a ∈ B.attestations) ∨
      ∃ v ∈ rho.honest, ∃ i : Nat, a ∈ (stateBefore S rho i v).st.sg_rows a.round

end NamedRun

end DecoupledConsensusModel.Execution

end
