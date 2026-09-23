module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.PhaseGradeQueries
public import DecoupledConsensusProofs.Protocol.Grades.Grades
public import DecoupledConsensusProofs.Protocol.Grades.GradeCutoffMono

@[expose] public section

/-! # Row 20 (`Q20_graded_has_honest_supporter`)

A block graded in phase `p` has an honest supporter: an honest validator with
an interpreted input in the phase's early window whose confirmed head, once
resolved in the tree, sits above `B`.

**The argument.** `WindowMajorityAt` says the faulty weight is below the
weight of honest validators present (an interpreted input) by the early
cutoff. Every present validator is a token holder: its ready view at the
early cutoff is nonempty, and the early cutoff is no later than the late one,
so its early ready view sits inside its late one. A validator in that
position either `DecoupledConsensusModel.Protocol.Supports` `B` (is `positive`) or
`DecoupledConsensusModel.Protocol.Opposes` it (is `opposing`) — the two runtime
predicates are read off the same maximal-round early token, and one of the
three conditions `Supports` demands of it (it covers `B`, the token set is
clean at its round, every later ready token also covers `B`) must fail for
`Opposes` to hold instead. This dichotomy, `supports_or_opposes` below, needs
nothing but the token bookkeeping already in `Algebra.lean`.

If no honest validator were positive, every honest present validator would
have to be opposing, so the opposing weight would be at least the honest
present weight, itself above the faulty weight (`WindowMajorityAt`); and
every positive validator would have to be faulty, so the positive weight
would be at most the faulty weight. Chaining with the grade's own weight
comparison (`opposing < positive`, from `phaseGrade`/`gradeBool`) closes a
loop `faulty < faulty`. So some honest validator is positive, and unpacking
`Supports` for it hands back exactly the row's witnesses via
`exists_head_of_head_covers` (`HealingLemmas/Grades.lean`, §3). -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingLemmas
namespace Rows

open Internal.PhaseGrades DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token Supports Opposes CleanFrom)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A present validator (nonempty early token set, early window inside the
late one) either supports or opposes `B`. Take the maximal-round early
token `u`: if it does not cover `B`, it already witnesses `Opposes`'s first
disjunct (it lies in the late set too, since early ⊆ late); if it covers `B`
but the raw set is not clean from its round, the equivocating pair witnesses
`Opposes`'s second disjunct; if it covers `B` and is clean but some later
ready token fails to cover `B`, that later token witnesses the first
disjunct again (it is at least as late as every early token, `u` included);
otherwise all three of `Supports`'s conditions hold at `u`. -/
theorem supports_or_opposes {Key Blk : Type*} (c : Key → Blk → Prop)
    (early late raw : Finset (Token Key)) (B : Blk)
    (hne : early.Nonempty) (hsub : early ⊆ late) :
    Supports c early late raw B ∨ Opposes c early late raw B := by
  classical
  obtain ⟨u, hu, hmax⟩ := Finset.exists_max_image early (fun t => t.round) hne
  by_cases hcov : c u.key B
  · by_cases hclean : CleanFrom raw u.round
    · by_cases hsweep : ∀ x ∈ late, u.round < x.round → c x.key B
      · exact Or.inl ⟨u, hu, hmax, hcov, hclean, hsweep⟩
      · push_neg at hsweep
        obtain ⟨x, hx, hlt, hncov⟩ := hsweep
        exact Or.inr (Or.inl ⟨x, hx, fun v hv => le_trans (hmax v hv) hlt.le, hncov⟩)
    · unfold CleanFrom at hclean
      push_neg at hclean
      obtain ⟨x, hx, y, hy, hle, heq, hkey⟩ := hclean
      exact Or.inr (Or.inr ⟨x, hx, y, hy, fun v hv => le_trans (hmax v hv) hle, heq, hkey⟩)
  · exact Or.inr (Or.inl ⟨u, hsub hu, hmax, hcov⟩)


/-- **Row 20** (N36 restated cone): a graded block has an
honest window voter whose interpreted head, once resolved in the tree,
covers it. -/
theorem q20_graded_has_honest_supporter (E : Env V) (hc : Protocol.HealConfig) :
    Internal.PhaseGrades.Q20_graded_has_honest_supporter E hc := by
  intro gv F Hon r B p hmaj hgrade
  by_contra hno
  push_neg at hno
  -- No honest validator is a positive supporter: unpacking `positive` for one
  -- would hand back exactly the witnesses `hno` rules out.
  have hnopos : ∀ v ∈ Hon,
      DecoupledConsensusModel.Protocol.positive gv F hc.η_SG r (DecoupledConsensusModel.Protocol.early E hc r p)
        (DecoupledConsensusModel.Protocol.late E hc r p) v B ≠ true := by
    intro v hv hpos
    simp only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq] at hpos
    obtain ⟨u, hu, -, hcov, -, -⟩ := hpos
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
    simp only [DecoupledConsensusModel.Protocol.localCovers, DecoupledConsensusModel.Protocol.token] at hcov
    obtain ⟨root, head, hHroot, hf, -, hpre⟩ := exists_head_of_head_covers hcov
    have hheadroot : head.root = root := find?_root hf
    exact hno v hv w hw head (by rw [hheadroot]; exact hHroot) (by rw [hheadroot]; exact hf) hpre
  -- Every honest present validator is therefore an opponent.
  have hopp : Internal.PhaseGrades.honestPresent hc gv F Hon r (DecoupledConsensusModel.Protocol.early E hc r p) ⊆
      Finset.univ.filter fun v =>
        DecoupledConsensusModel.Protocol.opposing gv F hc.η_SG r (DecoupledConsensusModel.Protocol.early E hc r p)
          (DecoupledConsensusModel.Protocol.late E hc r p) v B = true := by
    intro v hv
    simp only [Internal.PhaseGrades.honestPresent, Finset.mem_filter] at hv
    obtain ⟨hvH, hvne⟩ := hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, DecoupledConsensusModel.Protocol.opposing,
      decide_eq_true_eq]
    rcases supports_or_opposes (fun k b => DecoupledConsensusModel.Protocol.localCovers gv k b = true)
        (DecoupledConsensusModel.Protocol.readyView gv F hc.η_SG r (DecoupledConsensusModel.Protocol.early E hc r p) v)
        (DecoupledConsensusModel.Protocol.readyView gv F hc.η_SG r (DecoupledConsensusModel.Protocol.late E hc r p) v)
        (DecoupledConsensusModel.Protocol.rawView gv hc.η_SG r (DecoupledConsensusModel.Protocol.late E hc r p) v) B
        (hvne.image DecoupledConsensusModel.Protocol.token)
        (GradeCutoffMono.readyView_mono gv F hc.η_SG r
          (GradeCutoffMono.early_le_late E hc r p) v) with hs | ho
    · exact absurd
        (show DecoupledConsensusModel.Protocol.positive gv F hc.η_SG r (DecoupledConsensusModel.Protocol.early E hc r p)
            (DecoupledConsensusModel.Protocol.late E hc r p) v B = true by
          simp only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq]; exact hs)
        (hnopos v hvH)
    · exact ho
  -- Every positive validator is therefore faulty.
  have hposfaulty : Finset.univ.filter (fun v =>
      DecoupledConsensusModel.Protocol.positive gv F hc.η_SG r (DecoupledConsensusModel.Protocol.early E hc r p)
        (DecoupledConsensusModel.Protocol.late E hc r p) v B = true) ⊆ Finset.univ \ Hon := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    exact fun hvH => hnopos v hvH hv
  simp only [Internal.PhaseGrades.phaseGrade, DecoupledConsensusModel.Protocol.gradeBool,
    decide_eq_true_eq] at hgrade
  simp only [Internal.PhaseGrades.WindowMajorityAt] at hmaj
  have h1 : E.electorate.weightOf (Finset.univ \ Hon) <
      E.electorate.weightOf (Finset.univ.filter fun v =>
        DecoupledConsensusModel.Protocol.opposing gv F hc.η_SG r (DecoupledConsensusModel.Protocol.early E hc r p)
          (DecoupledConsensusModel.Protocol.late E hc r p) v B = true) :=
    lt_of_lt_of_le hmaj (E.electorate.weightOf_mono hopp)
  have h2 : E.electorate.weightOf (Finset.univ.filter fun v =>
      DecoupledConsensusModel.Protocol.positive gv F hc.η_SG r (DecoupledConsensusModel.Protocol.early E hc r p)
        (DecoupledConsensusModel.Protocol.late E hc r p) v B = true) ≤ E.electorate.weightOf (Finset.univ \ Hon) :=
    E.electorate.weightOf_mono hposfaulty
  exact absurd (lt_of_lt_of_le (lt_trans h1 hgrade) h2) (lt_irrefl _)

#print axioms q20_graded_has_honest_supporter

end Rows
end HealingLemmas
end Proofs
end DecoupledConsensusModel

end
