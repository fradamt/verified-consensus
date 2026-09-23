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
public import DecoupledConsensusProofs.ModelVocabulary.Healing.Action
public import DecoupledConsensusProofs.ModelVocabulary.Protocol.Store
public import DecoupledConsensusModel.Protocol.Handlers
public import DecoupledConsensusModel.Protocol.Store
public import DecoupledConsensusModel.Protocol.Handlers
public import DecoupledConsensusModel.Protocol.Handlers

@[expose] public section

/-!
# §7.2 Duties and handlers — `sec:public-handlers` (PROTOCOL.md `sec:public-handlers`)

The inactive erased handler family retained for proof compatibility. The
selected executable path is `NamedRun → NamedNode.tick → NamedProfile.tick`.
It reuses the generic `_with` algorithms with saved frame grades.

The module is thin by construction. Everything §6 decides — the head, the round
decision, the proposal, the graded action — is called through
`Protocol.Store.toHealing`, so no rule of §6 is restated here. The integrated
reference store writes stay here because Lean binds a store type at definition time and
`Σ` is its own structure (modeling-choices row 21). Named reduction theorems in
the proof library guard these calls to the lower component cores.

One ordering is load-bearing, and it is branch order, not prose: the
confirmation evaluation runs **before** `attest` at `a_r = t_{rR+1} + 2Δ`, so
`attest` reads a `Σ.live_confirmed` recomputed in the same tick
(PROTOCOL.md `sec:healing-schedule`). The `t_s + Δ` branch's other ordering —
`set_fresh_root` before `goldfish_vote` — went with the round decision.

All four branches are independent `if`s, not `elif`s, and each reads the store as
mutated so far in the tick (F7.7, modeling-choices row 6).
-/

namespace DecoupledConsensusModel
namespace Protocol

open Protocol (ChainState HeightConfig)
open Protocol (SGVote)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- §6.4 `get_head(Σ, votes, support_votes, k)` at the cumulative store: the
ordinary full-tree wrapper through the §6 projection.

"At slot 0 the head is genesis" (PROTOCOL.md `sec:public-handlers`) needs no clause, but
not because the current-slot eligibility clause is false. It holds from
`Store.init`, whose `Σ.T` is `{B_gen}`, so the walk has no child to descend
to. -/
def get_head_with_vocab (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Store V)
    (votes support_votes : Finset (GoldfishVote V)) (k : Slot) : Block V :=
  get_head_in_tree_with contract E hc st
    (Protocol.get_filtered_block_tree st.toHealing.toFG)
    votes support_votes k

end Protocol
end DecoupledConsensusModel

end
