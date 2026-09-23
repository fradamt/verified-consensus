module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusModel.Protocol.ChainState
public import DecoupledConsensusModel.Protocol.Evidence

@[expose] public section

/-! Stream 5: a derived per-block inactivity ledger ( 1204/1206).
No field is added to ChainState and no charge changes weights or transitions.
The snapshot is after carried rows and before process_height_events resets
participation. Targeted-row snapshot wiring is a separate future profile.
LeakFairnessL1 and the canonical-lock producer are separate obligations. -/


namespace DecoupledConsensusModel
namespace Internal.LeakLedger
open Protocol
variable {V : Type} [DecidableEq V]

/-- Separate layer charges preserve overlap without counting a validator
more than once in the identified set used by tightness. -/
structure LayerCharges where
  l1 : Nat
  l2Target : Nat
  l2Finalize : Nat

def LayerCharges.scale (slots : Nat) (c : LayerCharges) : LayerCharges :=
  ⟨slots * c.l1, slots * c.l2Target, slots * c.l2Finalize⟩

variable [Fintype V]

/-- L1: no height advance; identify validators outside pre-height progress. -/
def layerOne (pre post : ChainState V) : Finset V :=
  if post.h = pre.h then Finset.univ \ pre.progress else ∅

/-- L2 target: no justification advance at a justifiable pre-height state. -/
def layerTwoTarget (pre post : ChainState V) : Finset V :=
  if post.h_j = pre.h_j ∧ pre.nj = false then
    Finset.univ \ pre.target_participation else ∅

/-- L2 finality: finality was pending and did not advance. -/
def layerTwoFinalize (pre post : ChainState V) : Finset V :=
  if pre.h_F < pre.h_j ∧ post.h_F = pre.h_F then Finset.univ \ pre.finalize else ∅

/-- Per-layer 0/1 charges. Their sum is not the identified weight. -/
def charges (pre post : ChainState V) (v : V) : LayerCharges :=
  ⟨if v ∈ layerOne pre post then 1 else 0,
   if v ∈ layerTwoTarget pre post then 1 else 0,
   if v ∈ layerTwoFinalize pre post then 1 else 0⟩

/-- Slots elapsed along this actual parent link. Natural subtraction keeps
the definition total on malformed blocks; admitted links have increasing slots. -/
def slotSpan (B : Block V) : Nat := B.slot - B.parent.slot

end Internal.LeakLedger
end DecoupledConsensusModel

end
