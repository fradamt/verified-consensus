module
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Pairs
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Blocks
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Time
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Weights
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Env
public import DecoupledConsensusProofs.ModelVocabulary.Goldfish.Objects
public import DecoupledConsensusProofs.ModelVocabulary.FinalityGadget.ChainState
public import DecoupledConsensusProofs.ModelVocabulary.FinalityGadget.Transition
public import DecoupledConsensusProofs.ModelVocabulary.Goldfish.Store
public import DecoupledConsensusProofs.ModelVocabulary.Goldfish.ForkChoice
public import DecoupledConsensusProofs.ModelVocabulary.MajoritySG.Objects
public import DecoupledConsensusProofs.ModelVocabulary.MajoritySG.ForkChoice
public import DecoupledConsensusProofs.ModelVocabulary.FGForkChoice.Finality
public import DecoupledConsensusProofs.ModelVocabulary.Healing.Schedule
public import DecoupledConsensusModel.Protocol.Grades

@[expose] public section

/-!
Generic weighted opposition grades and receipt-level equivocation.
No runtime or protocol binding is included.
-/
namespace DecoupledConsensusModel.Protocol

variable {Key Block : Type*}

section Weights

variable {V : Type*} [Fintype V] [DecidableEq V]

def weight (w : V → Nat) (s : Finset V) : Nat := ∑ v ∈ s, w v

noncomputable def coverSupporters (covers : Key → Block → Prop)
    (early late raw : V → Finset (Token Key)) (B : Block) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => Supports covers (early v) (late v) (raw v) B)

noncomputable def opponents (covers : Key → Block → Prop)
    (early late raw : V → Finset (Token Key)) (B : Block) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => Opposes covers (early v) (late v) (raw v) B)

noncomputable def grade (w : V → Nat) (covers : Key → Block → Prop)
    (early late raw : V → Finset (Token Key)) (B : Block) : Prop :=
  weight w (opponents covers early late raw B) <
    weight w (coverSupporters covers early late raw B)

end Weights

/-- Receipt-level equivocation at one round. Head bodies are not required. -/
def EquivocationAt (raw : Finset (Token Key)) (k : Nat) : Prop :=
  ∃ x ∈ raw, ∃ y ∈ raw, x.round = k ∧ y.round = k ∧ x.key ≠ y.key

end DecoupledConsensusModel.Protocol

end
