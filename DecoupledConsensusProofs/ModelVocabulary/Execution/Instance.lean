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
public import DecoupledConsensusProofs.ModelVocabulary.Execution.Setup
public import DecoupledConsensusProofs.ModelVocabulary.Execution.GradeRuntime.Selectors
public import DecoupledConsensusProofs.ModelVocabulary.Healing.Action
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.NamedAttestations
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.NamedBlocks
public import DecoupledConsensusProofs.ModelVocabulary.Protocol.Store
public import DecoupledConsensusProofs.ModelVocabulary.Protocol.Handlers
public import DecoupledConsensusProofs.ModelVocabulary.Execution.NamedEvent
public import DecoupledConsensusProofs.ModelVocabulary.Execution.NamedRun
public import DecoupledConsensusProofs.ModelVocabulary.Execution.NamedReceiptCalls
public import DecoupledConsensusModel.Execution.Instance
public import DecoupledConsensusModel.Generic.Run
public import DecoupledConsensusModel.Execution.Node
public import DecoupledConsensusModel.Execution.Run
public import DecoupledConsensusModel.Execution.Run
public import DecoupledConsensusModel.Execution.Setup

@[expose] public section

namespace DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

theorem World.step_eq (S : Setup V) :
    Generic.World.step (P := DecoupledConsensusModel.Execution.spec S) =
      NamedWorld.step S := by
  funext w e
  cases e <;> rfl

theorem World.init_eq (S : Setup V) :
    Generic.World.init (P := DecoupledConsensusModel.Execution.spec S) =
      NamedWorld.init := by
  rfl

theorem stateBefore_eq (S : Setup V) (rho : NamedRun V) :
    Generic.Run.stateBefore (DecoupledConsensusModel.Execution.spec S) rho =
      NamedRun.stateBefore S rho := by
  funext i
  simp only [Generic.Run.stateBefore, NamedRun.stateBefore, World.step_eq,
    World.init_eq]
  rfl

theorem stateBeforeTime_eq (S : Setup V) (rho : NamedRun V) :
    Generic.Run.stateBeforeTime (DecoupledConsensusModel.Execution.spec S) rho =
      NamedRun.stateBeforeTime S rho := by
  funext t
  simp only [Generic.Run.stateBeforeTime, NamedRun.stateBeforeTime, World.step_eq,
    World.init_eq]
  congr 1
  apply List.filter_congr
  intro e _
  cases e <;> rfl

theorem readAt_eq (S : Setup V) (rho : NamedRun V) :
    Generic.Run.readAt (DecoupledConsensusModel.Execution.spec S) rho =
      NamedRun.readAt S rho := by
  funext t
  simp only [Generic.Run.readAt, NamedRun.readAt, World.step_eq,
    World.init_eq]
  congr 1
  apply List.filter_congr
  intro e _
  cases e <;> rfl

theorem final_eq (S : Setup V) (rho : NamedRun V) :
    Generic.Run.final (DecoupledConsensusModel.Execution.spec S) rho =
      NamedRun.final S rho := by
  funext v
  simp only [Generic.Run.final, NamedRun.final, World.step_eq,
    World.init_eq]
  rfl

theorem emittedAt_eq (S : Setup V) (rho : NamedRun V) :
    Generic.Run.emittedAt (DecoupledConsensusModel.Execution.spec S) rho =
      NamedRun.emittedAt S rho := by
  funext i v t
  change (NamedNode.tick S v
      (Generic.Run.stateBefore (DecoupledConsensusModel.Execution.spec S) rho i v) t).2 =
    (NamedNode.tick S v (NamedRun.stateBefore S rho i v) t).2
  rw [stateBefore_eq S rho]

end DecoupledConsensusModel.Execution

end
