module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.ProgressQuorumCore

@[expose] public section

/-!
# Low target and finality quorum transitions

This module contains the parent-or-child target and finality quorum algebra used
by a height phase. Coverage is stated over live parent participation and exact
rows in one child payload. The finality surface carries an explicit checkpoint,
so participation retained through a progress carrier cannot be reinterpreted at
a different justification.
-/

namespace DecoupledConsensusModel
namespace Proofs

open Protocol (ChainState HeightConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

namespace HealingSurface

/-! ## Transition kernels -/



/-- A true finality guard performs the actual finality write before either
height branch runs. -/
theorem process_height_events_actual_F
    (E : Env V) (cfg : HeightConfig) (σ : ChainState V)
    (hready : Protocol.finalityReady E σ) :
    let out := Protocol.process_height_events E cfg σ
    out.F = σ.J ∧ out.h_F = σ.h_j := by
  dsimp only
  constructor
  · rw [Protocol.process_height_events_F, Protocol.afterFin_F, if_pos hready]
  · rw [Protocol.process_height_events_h_F, Protocol.afterFin_h_F, if_pos hready]


/-! ## Live parent-or-child target coverage -/





/-! ## Live parent-or-child finality coverage -/







end HealingSurface
end Proofs
end DecoupledConsensusModel

end
