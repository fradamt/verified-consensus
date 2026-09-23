module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
public import DecoupledConsensusProofs.Protocol.Grades.Q20_graded_has_honest_supporter
public import DecoupledConsensusProofs.Execution.FinalizedViable
public import DecoupledConsensusProofs.Protocol.Grades.JointHistoryProducers
public import DecoupledConsensusProofs.Protocol.Handlers.FrozenRootOrder

@[expose] public section

/-!
# Named producers for the relative grade surface

This module is the entry point for producers that consume the named
relative grade at the G2-domain read. the prior absolute-grade producers are
not aliases: a proof must use the frame contract and the action read's own
filtered tree.

The first reusable producer below is the run-level filtered FG-root fact. It
uses the named viability fold in the non-cascade branch and the named
justification-carrier proof in the cascade branch. The remaining grade
producers stay recorded at their consumer sites until their relative-support
bridge is available.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]


/-- The FG root is in the filtered tree at every named strict read.

The cascade branch uses the named justification carrier. The non-cascade
branch uses the premise-free named `FinalizedViable` producer. -/
theorem named_fgRoot_mem_filtered_stateBeforeTime
    (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    Protocol.get_fg_root
        (NamedRun.stateBeforeTime S rho t v).st.core.toHealing.toFG ∈
      Protocol.get_filtered_block_tree
        (NamedRun.stateBeforeTime S rho t v).st.core.toHealing.toFG := by
  let st := (NamedRun.stateBeforeTime S rho t v).st
  by_cases hgate : st.core.h_max = st.core.h_j + 1
  · simpa only [st] using
      NamedOutageClosure.justifiedRoot_mem_filtered S rho t v hgate
  · have hroot : Protocol.get_fg_root st.core.toHealing.toFG = st.core.F := by
      change (if st.core.h_max = st.core.h_j + 1 then st.core.J else st.core.F) = st.core.F
      rw [if_neg hgate]
    rw [hroot]
    exact finalizedViable_mem_filtered hroot
      (NamedFinalizedViable.finalizedViable_stateBeforeTime S rho t v)


/-- A contract-Q2 result at an indexed action read comes from the same
validator's earlier G2-domain freeze. -/
theorem contractQ2_capture_at_action_index
    (S : Setup V) (rho : Run V) (i : Nat) (v : V) (r : Round) {B : Block V}
    (hQ : Protocol.grade2_block_with
      (NamedProfile.gradeContract
        (NamedActionReads.actionReadFrom S (NamedRun.stateBefore S rho i v) r).cache)
      S.E S.hc
      (NamedActionReads.actionReadFrom S (NamedRun.stateBefore S rho i v) r).st.core.toHealing r =
        some B) :
    ∃ j raw, j < i ∧
      rho.events[j]? = some (.tick v (domain S.E S.hc r .g2)) ∧
      DecoupledConsensusModel.Protocol.freezeRoot S.E
        (NamedRun.stateBefore S rho j v).st.core.toHealing.gradeView
        (NamedRun.stateBefore S rho j v).st.core.F S.hc.η_SG r
        (early S.E S.hc r .g2) (late S.E S.hc r .g2) = some raw ∧
      Block.Preceq B raw :=
  NamedOutageHistory.JointHistoryProducersTime.q2_capture_at_action_read
    S rho i v r hQ



end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms named_fgRoot_mem_filtered_stateBeforeTime
#print axioms contractQ2_capture_at_action_index
end DecoupledConsensusModel.Proofs.HealingSurface

end
