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
public import DecoupledConsensusModel.Protocol.Grades
public import DecoupledConsensusModel.Protocol.Grades

@[expose] public section

/-! Support/opposition runtime definitions for the selected named frame contract.
Research namespaces are retained so existing proof names stay unchanged. -/

namespace DecoupledConsensusModel.Protocol
open DecoupledConsensusModel
variable {V : Type} [DecidableEq V] [Fintype V]

open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token)

section DecidableGrades
variable {Key B : Type*} [DecidableEq Key]

end DecidableGrades

/-- Preserve both current clear walks and all three SG fallback cases. -/
def selectedSGVote (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (r : Round) (frame : Frame V) : Block V :=
  let A := anchor E hc st r frame.g1
  match Protocol.deepest_clear (some A) st.live_confirmed (clear frame) with
  | some B => B
  | none => match grade2Block st frame with
    | some Q => Q
    | none => if (frame.g2.bind id).isSome then Protocol.get_fg_root st.toFG else A

end DecoupledConsensusModel.Protocol

end
