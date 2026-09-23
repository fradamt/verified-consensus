module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Walk
public import DecoupledConsensusModel.Protocol.ForkChoice.Head

@[expose] public section

/-!
# Pure round-zero reductions

Section 7 gives round zero no prior grade batch and no prior relative-SG
window. The grade and majority branches therefore reduce to their empty-input
forms, and the integrated SG root is exactly the FG root.
-/



namespace DecoupledConsensusModel
namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in

@[simp] theorem round_batch_zero (gv : Protocol.GradeView V) :
    Protocol.round_batch gv 0 = ∅ := by
  simp [Protocol.round_batch]

omit [Fintype V] in

@[simp] theorem batch_first_empty (ts : TimestampMap (Protocol.SGVote V)) :
    Protocol.batch_first? ts ∅ = none := by
  exact pickUnique?_empty rfl

omit [Fintype V] in
/-- Every validator has the empty grade summary in round zero. -/
@[simp] theorem summary_zero (gv : Protocol.GradeView V) (v : V) :
    Protocol.summary gv 0 v = ⟨none, none, none⟩ := by
  simp [Protocol.summary, Protocol.equivocation_instant, Protocol.sg_votes_by]

/-- Direct grade support is zero in round zero. -/
@[simp] theorem direct_support_zero (E : Env V) (gv : Protocol.GradeView V)
    (Γ_h Γ_e : Time) (B : Block V) :
    Protocol.direct_support E gv 0 Γ_h Γ_e B = 0 := by
  simp [Protocol.direct_support,
    occurrenceBefore, occurrenceAtLeast, Electorate.weightOf]

/-- Favorable grade support is zero in round zero. -/
@[simp] theorem favorable_support_zero (E : Env V) (gv : Protocol.GradeView V)
    (Γ : Time) (B : Block V) :
    Protocol.favorable_support E gv 0 Γ B = 0 := by
  simp [Protocol.favorable_support,
    occurrenceBefore, Electorate.weightOf]

/-- Grade 2 is false in round zero. -/
@[simp] theorem G2_zero (E : Env V) (gv : Protocol.GradeView V)
    (hc : Protocol.HealConfig) (B : Block V) :
    Protocol.G2 E gv hc 0 B = false := by
  simp [Protocol.G2, Env.m, Electorate.strictMajorityThreshold]

/-- Grade 1 is false in round zero. -/
@[simp] theorem G1_zero (E : Env V) (gv : Protocol.GradeView V)
    (hc : Protocol.HealConfig) (B : Block V) :
    Protocol.G1 E gv hc 0 B = false := by
  simp [Protocol.G1, Env.m, Electorate.strictMajorityThreshold]


@[simp] theorem relative_G1_zero (E : Env V) (gv : Protocol.GradeView V)
    (hc : Protocol.HealConfig) (F : Block V) (B : Block V) :
    Internal.PhaseGrades.phaseGrade E hc gv F 0 .g1 B = false := by
  simp [Internal.PhaseGrades.phaseGrade, DecoupledConsensusModel.Protocol.gradeBool,
    DecoupledConsensusModel.Protocol.positive, DecoupledConsensusModel.Protocol.opposing,
    DecoupledConsensusModel.Protocol.readyView, DecoupledConsensusModel.Protocol.rawView,
    DecoupledConsensusModel.Protocol.interpretedInputs, DecoupledConsensusModel.Protocol.rawInputs,
    Protocol.latest_window, DecoupledConsensusModel.Protocol.Supports,
    DecoupledConsensusModel.Protocol.Opposes, Electorate.weightOf]

#print axioms relative_G1_zero

/-- Grade 0 is false in round zero. -/
@[simp] theorem G0_zero (E : Env V) (gv : Protocol.GradeView V)
    (hc : Protocol.HealConfig) (B : Block V) :
    Protocol.G0 E gv hc 0 B = false := by
  simp [Protocol.G0, Env.m, Electorate.strictMajorityThreshold]

/-- The fresh grade-1 anchor is absent in round zero. -/
@[simp] theorem fresh_anchor_zero (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) :
    Protocol.fresh_anchor E hc st 0 = none := by
  rw [Protocol.fresh_anchor]
  have hempty :
      (Protocol.get_filtered_block_tree st.toFG).filter
          (fun B => Protocol.G1 E st.gradeView hc 0 B = true) = ∅ := by
    ext B
    simp
  rw [hempty]
  unfold Block.deepest?
  exact pickUnique?_empty rfl

/-- The relative-SG expiry window is empty in round zero. -/
@[simp] theorem latest_window_zero (η_SG : Round) :
    Protocol.latest_window η_SG 0 = [] := by
  simp [Protocol.latest_window]

omit [Fintype V] in
/-- No validator is represented in the round-zero relative-SG window. -/
@[simp] theorem represented_zero (pool : Round → Finset (Protocol.SGVote V))
    (η_SG : Round) (v : V) :
    Protocol.represented pool η_SG v 0 = false := by
  simp [Protocol.represented]

/-- The round-zero relative-SG denominator is zero. -/
@[simp] theorem W_r_zero (E : Env V)
    (pool : Round → Finset (Protocol.SGVote V)) (η_SG : Round) :
    Protocol.W_r E pool η_SG 0 = 0 := by
  simp [Protocol.W_r, Protocol.represented_set, Electorate.weightOf]

omit [Fintype V] in
/-- A validator has no selected relative-SG support vote in round zero. -/
@[simp] theorem latest_support_vote_zero
    (pool : Round → Finset (Protocol.SGVote V)) (η_SG : Round)
    (T : Finset (Block V)) (v : V) :
    Protocol.latest_support_vote pool η_SG T v 0 = none := by
  simp [Protocol.latest_support_vote, Protocol.latest_support_round]

/-- Relative SG support is zero for every block in round zero. -/
@[simp] theorem sg_support_zero (E : Env V)
    (pool : Round → Finset (Protocol.SGVote V)) (η_SG : Round)
    (T : Finset (Block V)) (B : Block V) :
    Protocol.sg_support E pool η_SG T 0 B = 0 := by
  simp [Protocol.sg_support, Protocol.sgSupporters, Protocol.supports,
    Electorate.weightOf]

omit [Fintype V] in
/-- A GHOST walk with no eligible block stays at its anchor. -/
theorem ghost_all_ineligible (anchor : Block V) (tree : Finset (Block V))
    (score : Block V → Nat) (eligible : Block V → Bool)
    (hfalse : ∀ B : Block V, eligible B = false) :
    Protocol.ghost anchor tree score eligible = anchor := by
  have hnone : Protocol.ghost_step tree score eligible anchor = none :=
    ghost_step_none (by
      intro C _ _
      exact hfalse C)
  unfold Protocol.ghost
  cases tree.card with
  | zero => rfl
  | succ n =>
      simp only [Protocol.ghost_walk]
      rw [hnone]

/-- The relative-majority walk does not leave its anchor in round zero. -/
@[simp] theorem majority_fork_choice_zero (E : Env V)
    (pool : Round → Finset (Protocol.SGVote V)) (η_SG : Round)
    (T : Finset (Block V)) (anchor : Block V) (tree : Finset (Block V)) :
    Protocol.majority_fork_choice E pool η_SG T anchor tree 0 = anchor := by
  apply ghost_all_ineligible
  intro B
  simp [Protocol.W_r, Protocol.represented_set, Protocol.represented,
    Protocol.latest_window]

/-- At round zero the Section 7 SG root is exactly the FG root. -/
@[simp] theorem get_sg_root_zero (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) :
    Protocol.get_sg_root E hc st 0 = Protocol.get_fg_root st.toFG := by
  simp [Protocol.get_sg_root, Protocol.get_sg_root_with,
    Protocol.GradeContract.current, Protocol.currentGradeRead]

end Protocol
end DecoupledConsensusModel

end
