module
public import Mathlib.Data.Prod.Lex
public import DecoupledConsensusModel.Objects.NamedBlocks
public import DecoupledConsensusModel.Generic.Run
public import DecoupledConsensusModel.Objects.Time

@[expose] public section

/-!
# `DecoupledConsensusModel/Execution/Objects.lean`

Purpose: execution — the objects and events a run carries.
Paper: generic execution adapter around the Section 7 protocol.

Defines: NamedObject, NamedEvent, and their projections.

Read after: `DecoupledConsensusModel.Objects.NamedBlocks`, `DecoupledConsensusModel.Generic.Run`, `DecoupledConsensusModel.Objects.Time`
Read next: `DecoupledConsensusModel.Execution.Run`.

State read: `Setup`, node state, protocol records, and event/run observations.
State written: execution state, receipts, handles, or the protocol-spec value returned by the adapter.

Representation notes: Execution records keep named payloads beside erased protocol state; adapters preserve the protocol definitions.
-/

-- ── from Execution/NamedObjects.lean ──
section
/-! Named wire objects retain full signed row data. There is no processing,
acceptance or forwarding implementation in this data-only module. -/
namespace DecoupledConsensusModel.Execution

inductive NamedObject (V : Type) where
  | block (B : NamedBlock V)
  | gfVote (vote : GoldfishVote V)
  | attest (row : NamedAttestation V)
  deriving DecidableEq, Repr

namespace NamedObject
variable {V : Type}

def author : NamedObject V → Option V
  | .block B => B.proposer?
  | .gfVote vote => some vote.val_index
  | .attest row => some row.val_index

end NamedObject
end DecoupledConsensusModel.Execution
end

-- ── from Execution/NamedEvent.lean ──
section
/-! Named event data, with the existing time/phase ordering. Erasure is not
an execution simulation and does not discard the original named object. -/
namespace DecoupledConsensusModel.Execution

abbrev NamedEvent (V : Type) := Generic.Event V (NamedObject V)

namespace NamedEvent
variable {V : Type}

abbrev tick := @Generic.Event.tick V (NamedObject V)
abbrev deliver := @Generic.Event.deliver V (NamedObject V)
def time : NamedEvent V → Time
  | .tick _ t => t
  | .deliver _ _ t => t

def node : NamedEvent V → V
  | .tick v _ => v
  | .deliver v _ _ => v

def object? : NamedEvent V → Option (NamedObject V)
  | .tick _ _ => none
  | .deliver _ object _ => some object

end NamedEvent
end DecoupledConsensusModel.Execution
end

end
