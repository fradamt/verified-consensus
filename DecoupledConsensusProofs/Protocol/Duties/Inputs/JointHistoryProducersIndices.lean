module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.LayerAHistoryIndices
public import DecoupledConsensusProofs.Protocol.Grades.JointHistoryProducers

@[expose] public section

/-!
# Index form of the small joint-layer-A producers (task 1)

None of `JointHistoryProducers.lean`'s theorems take the time-based
`LayerAJointHistoryOn S rho t C` (or any of its three clause predicates) as a
hypothesis at all: every one of them is already history-free (bounded only by
an explicit event index such as `q2_capture_at_action_read`'s `j < i`, or by
no run-history argument whatsoever, e.g. `named_preceq_trans`,
`honest_positive_of_gradeBool`, `named_of_erase_preceq`). There is therefore
nothing to proof: this file imports the index-bounded history
(`LayerAHistoryIdx`) alongside the original producers file and reuses
every declaration verbatim through `open... JointHistoryProducersTime`.
Downstream index files (`JointHistoryB4B5Idx.lean`, `JointHistoryGapsIdx.lean`,
`SGVoteHistoryIndices.lean`) import this file and pick up the producers
that way; nothing new is declared here.
-/


namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.JointHistoryProducers
open Execution Internal.NamedOutageEntry Protocol
open Internal.NamedOutageEntry.History
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open JointHistoryProducersTime
variable {V : Type} [DecidableEq V] [Fintype V]

-- Sanity check: the history-free producers type-check unchanged in the
-- presence of the index-bounded history import (no ambient name clash with
-- `LayerAHistoryIdx`/`SGVoteIdx`/`ConfirmationIdx`/`LayerAJointHistoryIdx`).
example (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (i : Nat) (v : V) (r : Round) {q : Block V}
    (hQ : Protocol.grade2_block_with
        (NamedProfile.gradeContract (actionReadFrom S (NamedRun.stateBefore S rho i v) r).cache)
        S.E S.hc (actionReadFrom S (NamedRun.stateBefore S rho i v) r).st.core.toHealing r =
      some q) :
    ∃ (j : Nat) (raw : Block V),
      j < i ∧
      rho.events[j]? = some (.tick v (domain S.E S.hc r .g2)) ∧
      freezeRoot S.E (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
        (NamedRun.stateBefore S rho j v).st.core.F S.hc.η_SG r
        (early S.E S.hc r .g2) (late S.E S.hc r .g2) = some raw ∧
      Block.Preceq q raw :=
  q2_capture_at_action_read S rho i v r hQ

example {A B : NamedBlock V} (hAB : NamedBlock.Preceq A B) {C : NamedBlock V}
    (hBC : NamedBlock.Preceq B C) : NamedBlock.Preceq A C :=
  named_preceq_trans hAB hBC

end DecoupledConsensusModel.Proofs.NamedOutageHistory.JointHistoryProducers

end
