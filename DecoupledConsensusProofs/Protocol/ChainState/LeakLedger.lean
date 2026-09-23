module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.LeakLedger
public import DecoupledConsensusProofs.Objects.Weights
public import DecoupledConsensusProofs.Protocol.ChainState.Chain

@[expose] public section

/-! Local per-stalled-block tightness and the derived slot-scaled ledger. The post-state is
the real process_height_events result. No ChainOrder, reachability, voting,
fairness or lock hypothesis is assumed. L1 alone proves the lower bound;
the other layers add identified validators through the union. -/
namespace DecoupledConsensusModel.Proofs.LeakLedger
open DecoupledConsensusModel Protocol Internal.LeakLedger
variable {V : Type} [DecidableEq V]





variable [Fintype V]




private theorem afterFin_targetReady (E : Env V) (pre : ChainState V) :
    targetReady E (Protocol.afterFin E pre) = targetReady E pre := by
  unfold Protocol.afterFin
  split_ifs <;> rfl

private theorem afterFin_progReady (E : Env V) (cfg : HeightConfig) (pre : ChainState V) :
    progReady E cfg (Protocol.afterFin E pre) = progReady E cfg pre := by
  unfold Protocol.afterFin
  split_ifs <;> rfl

/-- Either height branch increases h by one, even on an arbitrary pre-state. -/
theorem height_event_counter (E : Env V) (cfg : HeightConfig) (pre : ChainState V) :
    (process_height_events E cfg pre).h =
      if targetReady E pre then pre.h + 1
      else if progReady E cfg pre then pre.h + 1 else pre.h := by
  rw [Protocol.process_height_events_eq, afterFin_targetReady, afterFin_progReady]
  split_ifs <;> simp only [advance_height, Protocol.afterFin_h]


















#print axioms height_event_counter
end DecoupledConsensusModel.Proofs.LeakLedger

end
