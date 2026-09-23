module
public import DecoupledConsensusModel.Protocol.Grades

@[expose] public section

/-!
# `DecoupledConsensusModel/Protocol/ForkChoice/Head.lean`

Purpose: Section 7, block 2a — get_sg_root, get_head_in_tree and get_head over the saved grades.
Paper: `docs/PROTOCOL.md` `sec:complete-store`; algorithm block: `alg:goldfish` / `alg:fg-store`.

Defines: get_sg_root_with and get_head_with.

Read after: `DecoupledConsensusModel.Protocol.Grades`
Read next: `DecoupledConsensusModel.Protocol.Duties.Inputs`.

State read: the protocol environment, schedule, store layers, and the view inputs named by the definitions.
State written: the returned store, chain state, record, or view value; pure readers write no state.

Representation notes: Typed Lean records, finite collections, and projections preserve the executable protocol representation. This module states no proof theorem.
-/

-- ── from Healing/ForkChoice.lean ──
/-!
# The SG root and composed head

The selected protocol supplies a `GradeContract` to the SG root and head
operations. The explicit-tree head is the finality-gadget Goldfish walk with
the contract's anchor.
-/

namespace DecoupledConsensusModel
namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The SG root supplied by the contract's anchor read. -/
def get_sg_root_with (contract : GradeContract V)
    (E : Env V) (hc : HealConfig) (st : HealingStore V) (r : Round) : Block V :=
  (contract.read E hc st r).anchor

/-- The explicit-tree composed head at the contract's SG root. -/
def get_head_in_tree_with_layer (contract : GradeContract V)
    (E : Env V) (hc : HealConfig) (st : HealingStore V)
    (tree : Finset (Block V)) (votes support_votes : Finset (GoldfishVote V))
    (k : Slot) : Block V :=
  let A := get_sg_root_with contract E hc st (hc.round_of st.s)
  Protocol.goldfish_fork_choice E st.σ st.h_max st.T st.s A tree votes
    support_votes k

/-- The ordinary full-tree composed head. -/
def get_head_with (contract : GradeContract V)
    (E : Env V) (hc : HealConfig) (st : HealingStore V)
    (votes support_votes : Finset (GoldfishVote V)) (k : Slot) : Block V :=
  get_head_in_tree_with_layer contract E hc st
    (Protocol.get_filtered_block_tree st.toFG) votes support_votes k

end Protocol
end DecoupledConsensusModel

end
