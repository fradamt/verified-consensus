module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.AlignedRoundLemmas

@[expose] public section

/-!
# Low progress-quorum transitions

This module contains the recovery-independent algebra for live target and
progress participation. A child can preserve a quorum by combining bits that
are still live in its parent state with exact target or timeout attestations in
its own payload. Folding that payload produces a live progress quorum and the
height event advances.

This is a low dependency leaf over model, property, safety, and quorum facts.
-/

namespace DecoupledConsensusModel
namespace Proofs

open Protocol (ChainState HeightConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

namespace NjGap

/-! ## Progress participation through an attestation fold -/




/-! ## A live progress quorum advances the height -/

/-- A mature progress quorum advances the height on either height-event
branch. -/
theorem advances_of_progress_quorum (E : Env V) (cfg : HeightConfig)
    {σ : ChainState V} (hmature : σ.T_h.slot + cfg.timeoutDelay ≤ σ.s)
    (hq : E.electorate.IsQuorum σ.progress) :
    (Protocol.process_height_events E cfg σ).h = σ.h + 1 := by
  have hprog : Protocol.progReady E cfg (Protocol.afterFin E σ) = true := by
    have hp : (Protocol.afterFin E σ).progress = σ.progress := Protocol.afterFin_progress E
    have hslot : (Protocol.afterFin E σ).T_h.slot + cfg.timeoutDelay ≤
        (Protocol.afterFin E σ).s := by
      rw [Protocol.afterFin_T_h]
      unfold Protocol.afterFin
      split_ifs <;> exact hmature
    simp only [Protocol.progReady, Bool.or_eq_true, Bool.and_eq_true,
      ChainState.progQuorum, ChainState.Q_prog, Electorate.quorumCheck,
      decide_eq_true_eq, hp]
    exact Or.inr ⟨hslot, hq⟩
  rw [Protocol.process_height_events_eq]
  by_cases h1 : Protocol.targetReady E (Protocol.afterFin E σ) = true
  · rw [if_pos h1, Protocol.advance_height_h]
    exact congrArg (· + 1) (Protocol.afterFin_h E)
  · rw [if_neg h1, if_pos hprog, Protocol.advance_height_h]
    exact congrArg (· + 1) (Protocol.afterFin_h E)




end NjGap

end Proofs
end DecoupledConsensusModel

end
