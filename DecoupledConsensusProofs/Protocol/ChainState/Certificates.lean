module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.Chain
public import DecoupledConsensusInternal.ModelVocabulary.FinalityGadget.Crossing

@[expose] public section



namespace DecoupledConsensusModel
namespace Protocol

open Protocol (ChainState HeightConfig)
open Internal

/-! ## Quorum weakening (PROTOCOL.md#the-complete-protocol) -/

section Weakening

variable {V : Type} [Fintype V]

/-- §4 a superset of a quorum is a quorum (PROTOCOL.md#the-complete-protocol). -/
theorem isQuorum_of_subset {E : Electorate V} {S T : Finset V} (h : E.IsQuorum S)
    (hst : S ⊆ T) : E.IsQuorum T :=
  Nat.le_trans h (E.weightOf_mono hst)

end Weakening


/-! ## The height crossing (PROTOCOL.md#the-complete-protocol) -/

section Crossing

variable {V : Type} [DecidableEq V] [Fintype V]


/-- §4 **one transition advances the height by at most one, and only on a
progress quorum** (PROTOCOL.md#the-complete-protocol).
The previous `height_progression` (proof map node 19), with the justify branch folded
into the progress branch: `targetReady` is a quorum on `target_participation`
and a target vote sets the progress bit too, so both branches leave a quorum on
`σ.progress`. -/
theorem height_advance_step (E : Env V) (cfg : HeightConfig) {σ : ChainState V}
    (hsub : σ.target_participation ⊆ σ.progress) :
    (Protocol.process_height_events E cfg σ).h = σ.h ∨
      ((Protocol.process_height_events E cfg σ).h = σ.h + 1 ∧
        E.electorate.IsQuorum σ.progress) := by
  rw [process_height_events_eq]
  split_ifs with h1 h2
  · refine Or.inr ⟨by rw [advance_height_h, afterFin_h], ?_⟩
    have hq := isQuorum_of_targetReady E h1
    rw [afterFin_target_participation] at hq
    exact isQuorum_of_subset hq hsub
  · refine Or.inr ⟨by rw [advance_height_h, afterFin_h], ?_⟩
    rcases quorum_of_progReady E cfg h2 with hq | ⟨-, hq⟩
    · rw [afterFin_target_participation] at hq
      exact isQuorum_of_subset hq hsub
    · rwa [afterFin_progress] at hq
  · exact Or.inl (afterFin_h E)


variable (E : Env V) (cfg : HeightConfig)


end Crossing

end Protocol
end DecoupledConsensusModel

end
