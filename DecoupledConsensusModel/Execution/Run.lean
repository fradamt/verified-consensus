module
public import DecoupledConsensusModel.Execution.Node
public import DecoupledConsensusModel.Execution.Objects

@[expose] public section

/-!
# `DecoupledConsensusModel/Execution/Run.lean`

Purpose: execution — worlds, runs, the reads a run exposes, and admissibility.
Paper: generic execution adapter around the Section 7 protocol.

Defines: NamedRun, NamedWorld.step, and NamedRun.readAt.

Read after: `DecoupledConsensusModel.Execution.Node`, `DecoupledConsensusModel.Execution.Objects`
Read next: `DecoupledConsensusModel.Execution.Instance`.

State read: `Setup`, node state, protocol records, and event/run observations.
State written: execution state, receipts, handles, or the protocol-spec value returned by the adapter.

Representation notes: Execution records keep named payloads beside erased protocol state; adapters preserve the protocol definitions.
-/

-- ── from Execution/NamedRun.lean ──
section
/-! One concrete named event fold with full named data. The initial world and
all observations are computed. Direct processing and data scopes are separate
from the later actual-handler and acceptance relations. -/
namespace DecoupledConsensusModel.Execution

abbrev NamedWorld (V : Type) := V → NamedNodeState V

namespace NamedWorld
variable {V : Type} [DecidableEq V]

def init : NamedWorld V := fun _ => NamedNode.initial

def step [Fintype V] (S : Setup V) (w : NamedWorld V) : NamedEvent V → NamedWorld V
  | .tick v t => Function.update w v (NamedNode.tick S v (w v) t).1
  | .deliver v o _ => Function.update w v (NamedNode.process S (w v) o)

end NamedWorld

abbrev NamedRun (V : Type) := Generic.Run V (NamedObject V)

namespace NamedRun
variable {V : Type}

abbrev honest (rho : NamedRun V) : Finset V := Generic.Run.honest rho
abbrev events (rho : NamedRun V) : List (NamedEvent V) := Generic.Run.events rho

end NamedRun

namespace NamedRun
variable {V : Type} [DecidableEq V] [Fintype V]

def stateBefore (S : Setup V) (rho : NamedRun V) (i : Nat) : NamedWorld V :=
  (rho.events.take i).foldl (NamedWorld.step S) NamedWorld.init

def stateBeforeTime (S : Setup V) (rho : NamedRun V) (t : Time) : NamedWorld V :=
  (rho.events.filter (fun e => decide (e.time < t))).foldl (NamedWorld.step S) NamedWorld.init

def readAt (S : Setup V) (rho : NamedRun V) (t : Time) : NamedWorld V :=
  (rho.events.filter (fun e => decide (e.time ≤ t))).foldl (NamedWorld.step S) NamedWorld.init

def objects (rho : NamedRun V) : List (NamedObject V) :=
  rho.events.filterMap NamedEvent.object?

/-- Full directly delivered or prefix-held bodies, before ancestor closure. -/
def directBlockInRun (S : Setup V) (rho : NamedRun V) (B : NamedBlock V) : Prop :=
  NamedObject.block B ∈ objects rho ∨
    ∃ v ∈ rho.honest, ∃ i : Nat, B ∈ (stateBefore S rho i v).st.bodies

/-- Full ancestors retain their own signed payloads in the run scope. -/
def blockInRun (S : Setup V) (rho : NamedRun V) (A : NamedBlock V) : Prop :=
  ∃ B : NamedBlock V, directBlockInRun S rho B ∧ NamedBlock.Preceq A B

end NamedRun
end DecoupledConsensusModel.Execution
end

-- ── from Execution/NamedReceiptCalls.lean ──
section
/-! Actual named handler-call observers. Full object identity, event ownership,
carried-object insertion gates and original list positions determine the calls.
The internal stored GF stage remains inside the existing block handler. -/
namespace DecoupledConsensusModel.Execution

namespace NamedReceiptCalls
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The existing named core call, with the supplied configuration unchanged. -/
def postCore (S : Setup V) (before : Protocol.NamedStore V) (B : NamedBlock V) :
    Protocol.NamedStore V :=
  Protocol.NamedStore.process_block_core S.E S.hc S.cfg before B

end NamedReceiptCalls

namespace NamedRun
variable {V : Type} [DecidableEq V] [Fintype V]

end NamedRun
end DecoupledConsensusModel.Execution
end

-- ── from Execution/NamedActionReads.lean ──
section
/-! Exact named action reads, extracted without a body change. -/
namespace DecoupledConsensusModel.Execution.NamedActionReads
open DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The actual cache preparation at the start of NamedNode.tick. -/
def preparedCache (S : Setup V) (before : NamedNodeState V) (t : Time) : Cache V :=
  onPhaseTick S.E S.hc before.st.core.toHealing t before.cache

/-- The confirmation input at a support-cutoff tick: clock update and the
same prepared cache, with the incoming signing record. The absence of the
proposal and vote branches at such a tick is a proof obligation. -/
def confirmationReadFrom (S : Setup V) (before : NamedNodeState V) (t : Time) :
    NamedNodeState V :=
  ⟨Protocol.NamedStore.setClock S.E before.st t, before.record, preparedCache S before t⟩

/-- The strict read followed by support-cutoff clock/cache staging. Only the
support-cutoff and round-action times below are used as confirmation reads. -/
def confirmationReadAt (S : Setup V) (rho : NamedRun V) (v : V) (t : Time) :
    NamedNodeState V :=
  confirmationReadFrom S (NamedRun.stateBeforeTime S rho t v) t

end DecoupledConsensusModel.Execution.NamedActionReads
end

-- ── from Execution/Run.lean ──
section
/-! Canonical execution observations are computed by the selected named fold.
Geometry remains the internal Block projection; the wire carries full named
blocks and rows. No erased-run simulation or state reconstruction is used. -/
namespace DecoupledConsensusModel.Execution

abbrev Run := NamedRun
namespace Run
variable {V : Type} [DecidableEq V] [Fintype V]

def storeAt (S : Setup V) (rho : Run V) (v : V) (t : Time) : Protocol.NamedStore V :=
  (NamedRun.readAt S rho t v).st

end Run

namespace Run
variable {V : Type} [DecidableEq V] [Fintype V]

end Run

end DecoupledConsensusModel.Execution
end

-- ── from Execution/NamedAdmissible.lean ──
section
/-! Full named environmental contracts over the concrete run. Schedule and
bounds retain their existing formulas. The named recipient relation
counts actual direct/self/carried calls; it does not promise successful admission.
No prior contract or supplied configuration is changed. -/
namespace DecoupledConsensusModel.Execution
variable {V : Type} [DecidableEq V] [Fintype V]

structure NamedRootCollisionFree (S : Setup V) (rho : NamedRun V) : Prop where
  root_injective : ∀ B C : NamedBlock V,
    NamedRun.blockInRun S rho B → NamedRun.blockInRun S rho C →
    ∀ A D : NamedBlock V,
      (NamedBlock.Preceq A B ∨ NamedBlock.Preceq A C) →
      (NamedBlock.Preceq D B ∨ NamedBlock.Preceq D C) → A.root = D.root → A = D

end DecoupledConsensusModel.Execution
end

end
