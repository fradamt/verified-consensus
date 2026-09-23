module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Walk
public import DecoupledConsensusProofs.Protocol.Grades.LegacyVocabulary

@[expose] public section

/-!
# Low store-finality fork-choice bridges

Generic ancestry facts from the FG root through the SG root and final Goldfish
walk. These facts depend only on the record and walk layers.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace StoreFinality

open Protocol (HealConfig)
open Internal

variable {V : Type} [DecidableEq V] [Fintype V]

/- Kept for live fork-choice ancestry consumers. -/
theorem get_fg_root_preceq_get_sg_root (E : Env V) (hc : HealConfig)
    (st : Protocol.Store V) :
    Block.Preceq (Protocol.get_fg_root st.toHealing.toFG)
      (Protocol.get_sg_root E hc st.toHealing (hc.round_of st.s)) := by
  simp only [Protocol.get_sg_root, Protocol.get_sg_root_with,
    Protocol.GradeContract.current, Protocol.currentGradeRead]
  split
  · rename_i A hA
    exact Proofs.Records.fresh_anchor_root_preceq E hc st.toHealing _ hA
  · split
    · exact Block.preceq_self _
    · exact Protocol.ghost_preceq _ _ _ _

theorem get_sg_root_preceq_get_head (E : Env V) (hc : HealConfig)
    (st : Protocol.Store V) (votes supportVotes : Finset (GoldfishVote V))
    (k : Slot) :
    Block.Preceq (Protocol.get_sg_root E hc st.toHealing (hc.round_of st.s))
      (Protocol.get_head E hc st votes supportVotes k) :=
  Protocol.ghost_preceq _ _ _ _

theorem get_head_of_preceq_fgRoot (E : Env V) (hc : HealConfig)
    (st : Protocol.Store V) (F : Block V)
    (votes supportVotes : Finset (GoldfishVote V)) (k : Slot)
    (hroot : Block.Preceq F (Protocol.get_fg_root st.toHealing.toFG)) :
    Block.Preceq F (Protocol.get_head E hc st votes supportVotes k) :=
  Block.preceq_trans hroot
    (Block.preceq_trans (get_fg_root_preceq_get_sg_root E hc st)
      (get_sg_root_preceq_get_head E hc st votes supportVotes k))

theorem finalized_preceq_fgRoot {st : Protocol.Store V}
    (hFJ : Block.preceq st.F st.J = true) :
    Block.Preceq st.F (Protocol.get_fg_root st.toHealing.toFG) :=
  Proofs.Records.preceq_get_fg_root_of_F (st := st.toHealing.toFG) hFJ

end StoreFinality
end Proofs
end DecoupledConsensusModel

end
