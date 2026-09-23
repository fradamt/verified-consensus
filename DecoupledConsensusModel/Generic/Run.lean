module
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Prod.Lex
public import Mathlib.Logic.Function.Basic
public import DecoupledConsensusModel.Objects.Time

@[expose] public section

/-!
# `DecoupledConsensusModel/Generic/Run.lean`

Purpose: generic execution model — events, protocol spec, worlds, runs.
Paper: generic execution model (not a paper algorithm).

Defines: Event, ProtocolSpec, World.step, Run.readAt, and Run.handlesAt.

Read after: `DecoupledConsensusModel.Objects.Time`
Read next: `DecoupledConsensusModel.Generic.Env`.

State read: generic events, protocol specifications, worlds, and runs.
State written: generic world/run values and observations.

Representation notes: The generic layer is independent of the Section 7 protocol and uses typed events and folds over worlds.
-/

-- ── from Generic/Run.lean ──
namespace DecoupledConsensusModel.Generic

/-- A scheduler event at a node: its local clock tick, or the delivery of one object. -/
inductive Event (V Object : Type) where
  | tick (v : V) (t : Time)
  | deliver (v : V) (object : Object) (t : Time)
  deriving DecidableEq

namespace Event
variable {V Object : Type}
def time : Event V Object → Time
  | .tick _ t => t
  | .deliver _ _ t => t
def node : Event V Object → V
  | .tick v _ => v
  | .deliver v _ _ => v
def object? : Event V Object → Option Object
  | .tick _ _ => none
  | .deliver _ object _ => some object
def phase : Event V Object → Nat
  | .tick _ _ => 0
  | .deliver _ _ _ => 1
/-- Event order is lexicographic by time and phase. Ticks therefore precede
deliveries at the same time; equal-phase deliveries keep their list order. -/
def key (e : Event V Object) : Lex (Time × Nat) := toLex (e.time, e.phase)
end Event

/-- A protocol: a node's local state, the objects it exchanges, its initial state,
what it does at a clock tick (new state and the objects it emits), how it
processes a delivered object, and the observation hooks used by the statement
layer. The environment holds `Δ`, GST, electorate weights, and the awake
profile. The proposal schedule and committees are interface reads. -/
structure ProtocolSpec (V : Type) where
  State : Type
  Object : Type
  init : State
  tick : V → State → Time → State × List Object
  process : State → Object → State
  /-- The validator an object is attributed to, if any. -/
  author : Object → Option V
  /-- Syntactic well-formedness of an object on the wire. -/
  wellFormed : Object → Bool
  /-- The node's state holds what the object depends on (e.g. the parent block). -/
  depsPresent : State → Object → Bool
  /-- The node's state already holds the object. -/
  processed : State → Object → Bool
  /-- The node's state excludes the object for good: the node rejects it now and
  in every later state. For a block: it conflicts with the node's finalized block.
  Delivery obligations do not apply to excluded objects. -/
  excludes : State → Object → Bool
  /-- In state `s`, event `e` makes the node handle object `o` (directly, or
  carried inside the delivered or emitted object). `handles` is the handler-call
  gate; it can hold even when the object is rejected. -/
  handles : State → Event V Object → Object → Prop
  /-- An object structurally contains another object, such as a vote carried by
  a block. `carries` is structural containment, with the containing object first. -/
  carries : Object → Object → Prop

/-- Every node's local state. -/
abbrev World (V : Type) (P : ProtocolSpec V) := V → P.State

namespace World
variable {V : Type} [DecidableEq V] {P : ProtocolSpec V}
def init : World V P := fun _ => P.init
def step (w : World V P) : Event V P.Object → World V P
  | .tick v t => Function.update w v (P.tick v (w v) t).1
  | .deliver v o _ => Function.update w v (P.process (w v) o)
end World

/-- A run: the honest set, the horizon, and the event list. -/
structure Run (V Object : Type) where
  honest : Finset V
  horizon : Time
  events : List (Event V Object)

namespace Run
variable {V : Type} [DecidableEq V] (P : ProtocolSpec V)
/-- Events before index `i` have been folded into the returned world. -/
def stateBefore (rho : Run V P.Object) (i : Nat) : World V P :=
  (rho.events.take i).foldl World.step World.init
/-- The returned world includes events strictly before time `t`. -/
def stateBeforeTime (rho : Run V P.Object) (t : Time) : World V P :=
  (rho.events.filter (fun e => decide (e.time < t))).foldl World.step World.init
/-- The returned world includes events up to and including time `t`. -/
def readAt (rho : Run V P.Object) (t : Time) : World V P :=
  (rho.events.filter (fun e => decide (e.time ≤ t))).foldl World.step World.init
/-- The returned world includes the complete event list. -/
def final (rho : Run V P.Object) : World V P :=
  rho.events.foldl World.step World.init
/-- The objects emitted by the tick at index `i`, recomputed from its
pre-event state. -/
def emittedAt (rho : Run V P.Object) (i : Nat) (v : V) (t : Time) : List P.Object :=
  (P.tick v (stateBefore P rho i v) t).2
/-- Payloads from delivery events only; self-emitted objects are not included. -/
def objects (rho : Run V P.Object) : List P.Object := rho.events.filterMap Event.object?
/-- An object appears in a tick's output (self-emission). -/
def emits (rho : Run V P.Object) (v : V) (o : P.Object) (t : Time) : Prop :=
  ∃ i : Nat, rho.events[i]? = some (.tick v t) ∧ o ∈ emittedAt P rho i v t

/-- An outer object has a direct processing occurrence when it is emitted or
delivered. Delivery records the handler call even when the handler rejects;
carried children are covered by `UnforgeableSignatures.carried` and
`handlesAt`. -/
def processes (rho : Run V P.Object) (v : V) (o : P.Object) (t : Time) : Prop :=
  emits P rho v o t ∨ ∃ i : Nat, rho.events[i]? = some (.deliver v o t)

/-- The handler call recorded at index `i`. A handler call may reject the object;
the false-to-true `processed` transition belongs to `acceptsAt`. -/
def handlesAt (rho : Run V P.Object) (i : Nat) (v : V) (o : P.Object)
    (t : Time) : Prop :=
  ∃ e, rho.events[i]? = some e ∧ e.node = v ∧ e.time = t ∧
    P.handles (stateBefore P rho i v) e o

/-- An accepted call is a handler call that flips `processed` from `false` to
`true`. -/
def acceptsAt (rho : Run V P.Object) (i : Nat) (v : V) (o : P.Object)
    (t : Time) : Prop :=
  handlesAt P rho i v o t ∧ P.processed (stateBefore P rho i v) o = false ∧
    P.processed (stateBefore P rho (i + 1) v) o = true
end Run
end DecoupledConsensusModel.Generic

end
