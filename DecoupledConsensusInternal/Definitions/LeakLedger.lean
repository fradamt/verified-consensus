module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Definitions.LeakLedger
public import DecoupledConsensusInternal.Definitions.Evidence

@[expose] public section

/-! Proof-side leak-ledger machinery outside `Statements.Consensus`. -/
namespace DecoupledConsensusModel.Internal.LeakLedger
open Protocol
variable {V : Type} [DecidableEq V]

def currentPreHeightSnapshot (parent : ChainState V) (B : Block V) : ChainState V :=
  let afterSlot := { parent with s := B.slot }
  let afterRows := B.attestations.foldl process_attestation afterSlot
  { afterRows with L := B }

def LayerCharges.zero : LayerCharges := ⟨0, 0, 0⟩

def LayerCharges.add (a b : LayerCharges) : LayerCharges :=
  ⟨a.l1 + b.l1, a.l2Target + b.l2Target, a.l2Finalize + b.l2Finalize⟩

variable [Fintype V]

def identified (pre post : ChainState V) : Finset V :=
  layerOne pre post ∪ layerTwoTarget pre post ∪ layerTwoFinalize pre post

def identifiedWeight (E : Env V) (pre post : ChainState V) : Nat :=
  E.electorate.weightOf (identified pre post)

def derivedPreHeightSnapshot (E : Env V) (cfg : HeightConfig) (B : Block V) : ChainState V :=
  currentPreHeightSnapshot (Internal.derived_state E cfg B.parent) B

def blockCharges (E : Env V) (cfg : HeightConfig) (B : Block V) (v : V) : LayerCharges :=
  LayerCharges.scale (slotSpan B)
    (charges (derivedPreHeightSnapshot E cfg B) (Internal.derived_state E cfg B) v)

def ledger (E : Env V) (cfg : HeightConfig) : Block V → V → LayerCharges
  | .genesis, _ => LayerCharges.zero
  | B@(.node parent _ _ _ _ _ _), v =>
    LayerCharges.add (ledger E cfg parent v) (blockCharges E cfg B v)

def Waiting (E : Env V) (cfg : HeightConfig) (pre : ChainState V) : Prop :=
  pre.progQuorum E = true ∧ pre.targetQuorum E = false ∧
    pre.s < pre.T_h.slot + cfg.timeoutDelay

def SameCounters (pre post : ChainState V) : Prop :=
  post.h = pre.h ∧ post.h_j = pre.h_j ∧ post.h_F = pre.h_F

def Stalled (E : Env V) (cfg : HeightConfig) (pre post : ChainState V) : Prop :=
  SameCounters pre post ∧ ¬ Waiting E cfg pre

def LeakTightness (E : Env V) (cfg : HeightConfig) : Prop :=
  ∀ pre : ChainState V,
    Stalled E cfg pre (process_height_events E cfg pre) →
      E.W - E.q ≤ identifiedWeight E pre (process_height_events E cfg pre)

end DecoupledConsensusModel.Internal.LeakLedger

end
