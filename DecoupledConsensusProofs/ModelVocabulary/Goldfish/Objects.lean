module
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Pairs
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Blocks
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Time
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Weights
public import DecoupledConsensusProofs.ModelVocabulary.Substrate.Env
public import DecoupledConsensusModel.Protocol.Schedule
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.Ring
public import DecoupledConsensusModel.Objects.Time
public import DecoupledConsensusModel.Objects.Identifiers
public import DecoupledConsensusModel.Objects.Parameters
public import DecoupledConsensusModel.Objects.Blocks
public import DecoupledConsensusModel.Objects.Weights

@[expose] public section

/-!
# §2.1 Schedule and wire objects — `sec:goldfish-schedule`
(PROTOCOL.md `sec:goldfish-schedule`)

The five per-slot public instants, the identity `val_index` of the validator running the
node, the two wire constraints the section states, and the vote-set vocabulary
that both the store and the fork choice read.

The wire objects themselves are not defined here: `GoldfishVote` and
`Block.gf_votes` live in the substrate, because Lean cannot add a field to a
structure after the fact (modeling-choices row 11). This module only names the
schedule and the stated constraints.

`confirmation_time E s = support_cutoff E (s+1)` (PROTOCOL.md
`sec:goldfish-schedule`, "the last action is also the support action of
slot") is what lets `on_tick` dispatch the slot-`s` confirmation evaluation
from the slot-`(s+1)` support branch.
-/

namespace DecoupledConsensusModel
namespace Protocol

section Vocabulary

variable {V : Type} [DecidableEq V]

end Vocabulary

section Schedule

variable {V : Type} [DecidableEq V] [Fintype V]

/-- §2.1 `t_s + 6Δ = t_{s+1} + 2Δ`: the slot-`s` confirmation evaluation is the
support action of slot `s+1` (PROTOCOL.md `sec:goldfish-schedule`, "the last
action is also the support action of slot"). -/
theorem confirmation_time_eq_support_cutoff_succ (E : Env V) (s : Slot) :
    confirmation_time E s = support_cutoff E (s + 1) := by
  unfold confirmation_time support_cutoff Env.t slotStart
  push_cast
  ring

end Schedule

end Protocol
end DecoupledConsensusModel

end
