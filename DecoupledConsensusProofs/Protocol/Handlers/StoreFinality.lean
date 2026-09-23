module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.StoreFinality
public import DecoupledConsensusProofs.Protocol.ChainState.Checkpoints
public import DecoupledConsensusProofs.Protocol.ChainState.Main
public import DecoupledConsensusInternal.Execution.Assumptions
public import DecoupledConsensusProofs.Protocol.Handlers.Bridges
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordClean

@[expose] public section

/-!
# FGStore finality properties shared with doc1

This file proves B13: no processed block carries a justification height above
the store's current justification height.

The difficult case is an accepted block whose offered justification does not
pass the store's ancestry filter. Both the current finalized block and the
offered justification are ancestors of the accepted block, so they are
comparable. If the offer is below the current finalization, the checkpoint
height identities and height monotonicity bound it by the derived height of
`F`, which is at most `h_j`. Otherwise,
the ancestry filter passes, and the lexicographic update either adopts the
offer or already stores an event at least as high.

The result needs the dependency-complete contract only to connect stored states
to derived chain states and to preserve store provenance. It needs no fault
bound, synchrony premise, or new protocol assumption.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace StoreFinality

open Protocol (ChainState HeightConfig)
open Protocol (Record HeightId)
open Protocol (HealConfig)
open Internal

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The finalized block is genesis, or its derived height is at most the
store's justification height.
This replaces the previous cached `Σ.h_F ≤ Σ.h_j` argument. The current
justification's provenance identifies its height; `Σ.F ⪯ Σ.J` then transports
that bound to `F`. -/
theorem finalized_height_le_justification (E : Env V) (cfg : HeightConfig)
    (st : Protocol.Store V) (hpre : FinalizedPrecedesJustified st)
    (hjust : Proofs.Bridges.StoreJustificationOnChain E cfg st) :
    st.F = Block.genesis ∨ (derived_state E cfg st.F).h ≤ st.h_j := by
  obtain ⟨B, _, hhj, hJ⟩ := hjust
  rcases Protocol.derived_justified_height E cfg B with hz | hh
  · left
    have hJg : st.J = Block.genesis := by
      rw [← hJ]
      exact AlignedRoundLemmas.derived_state_J_of_h_j_zero E cfg B hz
    exact Block.preceq_antisymm (by
      change Block.preceq st.F st.J = true at hpre
      rw [hJg] at hpre
      exact hpre)
      (preceq_genesis st.F)
  · right
    calc
      (derived_state E cfg st.F).h ≤ (derived_state E cfg st.J).h :=
        Protocol.derived_h_mono E cfg hpre
      _ = (derived_state E cfg (derived_state E cfg B).J).h := by rw [hJ]
      _ = (derived_state E cfg B).h_j := hh
      _ = st.h_j := hhj


/-- The derived finalized-height view is ordered below `h_j` at a store that
holds its finalized block and its justification provenance. This is the
replacement for the obsolete cached-field invariant.

Statement change (ledger row C, /): the prior premise was
`DepReachableStore E hc cfg nd st`, and its whole use was to produce the four
facts below through `Proofs.Bridges.reachableStore_of_depReachableStore` and
`Proofs.Bridges.provenance_depReachable`, both archived under (A) in
`the compatibility layer`.  forbids resurrecting
that route, so the facts are taken directly, the way
`Proofs.FrameStoreRoot.fgRoot_mem_filtered_of_state_facts` takes its own. The
old goal was

    finalityHeightsOrdered_depReachable
    (E: Env V) (hc: HealConfig) (cfg: HeightConfig) (nd: Protocol.Node V)
    (st: Protocol.Store V) (hst: DepReachableStore E hc cfg nd st):
    FinalityHeightsOrdered st

and with it `finalityHeightsOrderedInvariant`, whose statement
`Internal.FinalityHeightsOrderedInvariant E hc cfg nd` quantifies the same retired
premise and therefore has no producer either. -/
theorem finalityHeightsOrdered_of_state_facts (E : Env V) (cfg : HeightConfig)
    (st : Protocol.Store V)
    (hpre : FinalizedPrecedesJustified st)
    (hjust : Proofs.Bridges.StoreJustificationOnChain E cfg st)
    (hagree : DerivedStateAgrees E cfg st)
    (hFmem : st.F ∈ st.T) : FinalityHeightsOrdered st := by
  by_cases hF : st.F = Block.genesis
  · simp [FinalityHeightsOrdered, Protocol.Store.finalized_height, hF]
  · have hheight : (derived_state E cfg st.F).h ≤ st.h_j :=
      (finalized_height_le_justification E cfg st hpre hjust).resolve_left hF
    rw [FinalityHeightsOrdered, Protocol.Store.finalized_height, if_neg hF,
      hagree st.F hFmem]
    exact hheight

/-- An accepted block's offered justification is not above the store produced
by its finality update. -/
theorem offered_justification_le_update_finality (E : Env V)
    (cfg : HeightConfig) (st : Protocol.Store V) (B : Block V)
    (hFB : Block.preceq st.F B = true)
    (hbound : st.F = Block.genesis ∨
      (derived_state E cfg st.F).h ≤ st.h_j) :
    (derived_state E cfg B).h_j ≤
      (Protocol.update_finality st (derived_state E cfg B)).h_j := by
  let σ := derived_state E cfg B
  by_cases hFJ : Block.preceq st.F σ.J = true
  · by_cases hlex : HeightId.mk st.h_j st.J.root < HeightId.mk σ.h_j σ.J.root
    · have hguard : (Block.preceq st.F σ.J &&
          decide (HeightId.mk st.h_j st.J.root < HeightId.mk σ.h_j σ.J.root)) = true := by
        rw [Bool.and_eq_true]
        exact ⟨hFJ, decide_eq_true hlex⟩
      have hwrite : (Protocol.update_finality st σ).h_j = σ.h_j := by
        unfold Protocol.update_finality
        dsimp only
        rw [if_pos hguard]
        split_ifs <;> rfl
      rw [hwrite]
    · have hle : σ.h_j ≤ st.h_j :=
        heightId_height_le_of_le (not_lt.mp hlex)
      exact le_trans hle (heightId_height_le_of_le (update_finality_heightId st σ))
  · have hJB : Block.preceq σ.J B = true := Proofs.Records.derived_state_J_preceq E cfg B
    have hJF : Block.preceq σ.J st.F = true :=
      (Block.preceq_linear hJB hFB).resolve_right hFJ
    have hle : σ.h_j ≤ st.h_j := by
      rcases hbound with hFg | hFh
      · exfalso
        apply hFJ
        rw [hFg]
        exact preceq_genesis σ.J
      · rcases Protocol.derived_justified_height E cfg B with hz | hJh
        · simpa only [σ, hz] using Nat.zero_le st.h_j
        · calc
            σ.h_j = (derived_state E cfg σ.J).h := hJh.symm
            _ ≤ (derived_state E cfg st.F).h := Protocol.derived_h_mono E cfg hJF
            _ ≤ st.h_j := hFh
    exact le_trans hle (heightId_height_le_of_le (update_finality_heightId st σ))

/-! ## The justification is strictly below the running maximum -/

omit [Fintype V] in
/-- `update_finality` preserves `h_j < h_max`. If it installs the offered
justification, that justification is below the offered chain-state height. If
it does not, the previous justification remains below the previous maximum. -/
theorem justificationBelowMax_update_finality (st : Protocol.Store V)
    (σ : ChainState V) (hst : JustificationBelowMax st)
    (hσ : σ.h_j < σ.h) :
    JustificationBelowMax (Protocol.update_finality st σ) := by
  simp only [JustificationBelowMax, Protocol.update_finality]
  split_ifs <;>
    first
      | exact lt_of_lt_of_le hσ (Nat.le_max_right _ _)
      | exact lt_of_lt_of_le hst (Nat.le_max_left _ _)

omit [DecidableEq V] [Fintype V] in
/-- Transport `h_j < h_max` across a handler that carries both fields. -/
theorem justificationBelowMax_of_eq {st st' : Protocol.Store V}
    (hhj : st'.h_j = st.h_j) (hmax : st'.h_max = st.h_max)
    (h : JustificationBelowMax st) : JustificationBelowMax st' := by
  rw [JustificationBelowMax, hhj, hmax]
  exact h

end StoreFinality
end Proofs
end DecoupledConsensusModel

end
