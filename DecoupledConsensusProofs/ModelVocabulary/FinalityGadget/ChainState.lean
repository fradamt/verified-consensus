module
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Pairs
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Blocks
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Time
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Weights
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Env
public import DecoupledConsensusModel.Protocol.ChainState
public import DecoupledConsensusModel.Objects.Time
public import DecoupledConsensusModel.Objects.Identifiers
public import DecoupledConsensusModel.Objects.Parameters
public import DecoupledConsensusModel.Objects.Blocks
public import DecoupledConsensusModel.Objects.Weights

@[expose] public section

/-!
# §4 Chain state (PROTOCOL.md `sec:state-machine`)

`def:chain-state` as one flat twelve-field structure, in the document's order:
`σ = (L, s, h, T_h, nj, target_participation, progress, finalize, J, h_j, F,
h_F)` (PROTOCOL.md `def:chain-state`).

Two deviations from `decoupled-consensus-full`'s `Finality/Model.lean`, both
forced by the rewrite:

* `T_h` is a `Block`, never `⊥`. The full model carries
  `heightTarget: Option BlockId` and materializes it lazily from
  `heightStartSlot` inside `process_slot`; here `advance_height` sets
  `T_h ← L` directly and the initial state sets `T_h = B_gen`, so neither field
  nor the `Option` survives.
* The state is flat. The full model splits `latest` from a `StateData` record so
  a post-state commitment can be taken over the data half alone; no rule of the
  rewrite reads a post-state root (F4.1, modeling-choices row 13).

The three participation arrays are `Finset V` (modeling-choices row 7): the
document's `V → Bool` array and its derived quorum set carry the same
information, and every rule reads the set. `Repr` is therefore not derivable —
Mathlib's `Repr (Finset α)` is an `unsafe` instance — so this structure derives
`DecidableEq` only.
-/

namespace DecoupledConsensusModel

namespace Protocol

namespace HeightConfig


/-- §4 the retired lower bound `K ≥ 3`, now a consequence of `K ≥ 4`
(: the opening-carrier recurrence forces `gap ≥ 2` and
finality liveness needs `gap + 2 ≤ K`, so `K = 3` made the finality contracts
vacuous). Kept as a theorem so every consumer of the weaker bound is unaffected. -/
theorem K_ge_three (cfg : HeightConfig) : 3 ≤ cfg.K :=
  Nat.le_of_succ_le cfg.K_ge_four

/-- §4 the retired lower bound `K ≥ 2`, now a consequence
(PROTOCOL.md `sec:state-machine`, "Fix constants $K\geq4$, $D\geq2$"). Kept
under its own name because three lemmas need exactly
this and nothing stronger — `Proofs.Engine.nonjustifiable_succ_of_dvd` and
`Proofs.HealingLemmas.njEntry_initial` — and neither should have to know that
the domain moved. -/
theorem K_ge_two (cfg : HeightConfig) : 2 ≤ cfg.K :=
  Nat.le_of_succ_le cfg.K_ge_three

/-- §4 the retired lower bound `D ≥ 1`, now a consequence
(PROTOCOL.md `sec:state-machine`, "Fix constants $K\geq4$, $D\geq2$"). Read
by `Proofs.HealingLemmas.lt_of_recoveryHeight`. -/
theorem D_ge_one (cfg : HeightConfig) : 1 ≤ cfg.D :=
  Nat.le_of_succ_le cfg.D_ge_two

end HeightConfig

namespace ChainState

variable {V : Type}

variable [DecidableEq V] [Fintype V]

end ChainState

end Protocol

end DecoupledConsensusModel

end
