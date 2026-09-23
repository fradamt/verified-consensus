module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusStatements.Instantiation.Deadlines

@[expose] public section

namespace DecoupledConsensusModel
namespace Statements

open DecoupledConsensusModel.Execution
open DecoupledConsensusModel.Statements.Instantiation

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The closed startup formula is positive for every setup and parameter. -/
theorem finalityStartup_pos (S : Setup V) (gap : Round) (extra : Nat) :
    0 < finalityStartup S gap extra := by
  unfold finalityStartup
  have h : 0 < 1 +
      (S.cfg.D + S.cfg.K + 5) * (7 * gap + 22 + 4 * extra) :=
    Nat.add_pos_left Nat.zero_lt_one _
  exact ((h.trans_le (Nat.le_add_right _
    (3 * (7 * gap + 22 + 4 * extra)))).trans_le
      (Nat.le_add_right _ gap)).trans_le (Nat.le_add_right _ 5)

end Statements
end DecoupledConsensusModel

end
