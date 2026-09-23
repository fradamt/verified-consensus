module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.Ancestry
public import DecoupledConsensusInternal.Definitions.PhaseGrades

@[expose] public section

/-!
# Cutoff monotonicity of the retained phase inputs 

Every retained-input set of the §6.2 grade machinery grows with its cutoff, and
the ready view sits inside the raw view at a common cutoff. These are the only
facts the phase-grade inclusions (`Q5`–`Q7`) need about time.

restated from the reviewed producer draft
`collab/sg-grades-revamp/.../GuardedGradeHelpers.lean`, restricted
to the cutoff lemmas; the named-runtime helpers of that draft are not used here.
-/



namespace DecoupledConsensusModel.Proofs.GradeCutoffMono

open Internal.PhaseGrades DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token Supports Opposes)

variable {V : Type} [DecidableEq V] [Fintype V]

theorem stampedBefore_mono {α : Type} (ts : TimestampMap α) {c d : Time} (hcd : c ≤ d)
    {x : α} (h : stampedBefore ts c x = true) : stampedBefore ts d x = true := by
  rw [stampedBefore_eq_occurrenceBefore] at h ⊢
  exact occurrenceBefore_mono hcd h

theorem rawInputs_mono (gv : Protocol.GradeView V) (eta r : Round) {c d : Time}
    (hcd : c ≤ d) (sender : V) :
    DecoupledConsensusModel.Protocol.rawInputs gv eta r c sender ⊆
      DecoupledConsensusModel.Protocol.rawInputs gv eta r d sender := by
  intro u hu
  simp only [DecoupledConsensusModel.Protocol.rawInputs, Finset.mem_filter] at hu ⊢
  exact ⟨hu.1, hu.2.1, occurrenceBefore_mono hcd hu.2.2⟩

theorem bodyReady_mono (gv : Protocol.GradeView V) (F : Block V) {c d : Time}
    (hcd : c ≤ d) (u : Protocol.SGVote V)
    (h : DecoupledConsensusModel.Protocol.bodyReady gv F c u = true) :
    DecoupledConsensusModel.Protocol.bodyReady gv F d u = true := by
  cases hconf : u.confirmed with
  | none => simp only [DecoupledConsensusModel.Protocol.bodyReady, hconf]
  | some root =>
    simp only [DecoupledConsensusModel.Protocol.bodyReady, hconf] at h ⊢
    cases hf : Block.find? gv.T root with
    | none => rw [hf] at h; exact absurd h (by simp)
    | some H =>
      rw [hf] at h
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨stampedBefore_mono _ hcd h.1, h.2⟩

theorem interpretedInputs_mono (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    {c d : Time} (hcd : c ≤ d) (sender : V) :
    DecoupledConsensusModel.Protocol.interpretedInputs gv F eta r c sender ⊆
      DecoupledConsensusModel.Protocol.interpretedInputs gv F eta r d sender := by
  intro u hu
  simp only [DecoupledConsensusModel.Protocol.interpretedInputs, Finset.mem_filter] at hu ⊢
  exact ⟨rawInputs_mono gv eta r hcd sender hu.1, bodyReady_mono gv F hcd u hu.2⟩

theorem readyView_mono (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    {c d : Time} (hcd : c ≤ d) (v : V) :
    readyView gv F eta r c v ⊆ readyView gv F eta r d v :=
  Finset.image_subset_image (interpretedInputs_mono gv F eta r hcd v)

theorem rawView_mono (gv : Protocol.GradeView V) (eta r : Round)
    {c d : Time} (hcd : c ≤ d) (v : V) :
    rawView gv eta r c v ⊆ rawView gv eta r d v :=
  Finset.image_subset_image (rawInputs_mono gv eta r hcd v)

theorem readyView_subset_rawView (gv : Protocol.GradeView V) (F : Block V)
    (eta r : Round) (c : Time) (v : V) :
    readyView gv F eta r c v ⊆ rawView gv eta r c v :=
  Finset.image_subset_image (Finset.filter_subset _ _)

/-! ## The nested phase windows

`g2`'s window strictly contains `g1`'s on both ends, and `g1`'s early cutoff is
still inside `g2`'s late cutoff. That last inequality is what lets `g2`'s forward
clause police the token `g1` will pick as its latest. -/

theorem early_g2_le_early_g1 (E : Env V) (hc : Protocol.HealConfig) (r : Round) :
    early E hc r .g2 ≤ early E hc r .g1 := by
  simp only [early, Phase.earlyOffset]
  exact Int.add_le_add_left
    (Int.mul_le_mul_of_nonneg_right (by decide) E.Δ_pos.le) _

theorem late_g1_le_late_g2 (E : Env V) (hc : Protocol.HealConfig) (r : Round) :
    late E hc r .g1 ≤ late E hc r .g2 := by
  simp only [late, Phase.lateOffset]
  exact Int.add_le_add_left
    (Int.mul_le_mul_of_nonneg_right (by decide) E.Δ_pos.le) _

theorem early_g1_le_late_g2 (E : Env V) (hc : Protocol.HealConfig) (r : Round) :
    early E hc r .g1 ≤ late E hc r .g2 := by
  simp only [early, late, Phase.earlyOffset, Phase.lateOffset]
  exact Int.add_le_add_left
    (Int.mul_le_mul_of_nonneg_right (by decide) E.Δ_pos.le) _

theorem early_g2_le_early_g0 (E : Env V) (hc : Protocol.HealConfig) (r : Round) :
    early E hc r .g2 ≤ early E hc r .g0 := by
  simp only [early, Phase.earlyOffset]
  exact Int.add_le_add_left
    (Int.mul_le_mul_of_nonneg_right (by decide) E.Δ_pos.le) _

theorem late_g0_le_late_g2 (E : Env V) (hc : Protocol.HealConfig) (r : Round) :
    late E hc r .g0 ≤ late E hc r .g2 := by
  simp only [late, Phase.lateOffset]
  exact Int.add_le_add_left
    (Int.mul_le_mul_of_nonneg_right (by decide) E.Δ_pos.le) _

theorem early_g0_le_late_g2 (E : Env V) (hc : Protocol.HealConfig) (r : Round) :
    early E hc r .g0 ≤ late E hc r .g2 := by
  simp only [early, late, Phase.earlyOffset, Phase.lateOffset]
  exact Int.add_le_add_left
    (Int.mul_le_mul_of_nonneg_right (by decide) E.Δ_pos.le) _





theorem early_le_late (E : Env V) (hc : Protocol.HealConfig) (r : Round) (p : Phase) :
    early E hc r p ≤ late E hc r p := by
  cases p <;>
    simp only [early, late, Phase.earlyOffset, Phase.lateOffset] <;>
    exact Int.add_le_add_left
      (Int.mul_le_mul_of_nonneg_right (by decide) E.Δ_pos.le) _

/-! ## Transporting support and opposition between nested windows -/

theorem supports_narrow {Key Blk : Type*} (c : Key → Blk → Prop)
    {e₂ e₁ l₁ l₂ raw₁ raw₂ : Finset (Token Key)} {B : Blk}
    (he : e₂ ⊆ e₁) (hl : l₁ ⊆ l₂) (hraw : raw₁ ⊆ raw₂)
    (hel : e₁ ⊆ l₂) (her : e₁ ⊆ raw₂)
    (hS : Supports c e₂ l₂ raw₂ B) : Supports c e₁ l₁ raw₁ B := by
  obtain ⟨u, hu, hmax, hcov, hclean, hsweep⟩ := hS
  obtain ⟨u', hu', hmax'⟩ :=
    Finset.exists_max_image e₁ (fun t => t.round) ⟨u, he hu⟩
  have hle : u.round ≤ u'.round := hmax' u (he hu)
  refine ⟨u', hu', hmax', ?_, ?_, ?_⟩
  · rcases lt_or_eq_of_le hle with hlt | heq
    · exact hsweep u' (hel hu') hlt
    · have hkey : u'.key = u.key :=
        hclean u' (her hu') u (her (he hu)) hle heq.symm
      rw [hkey]
      exact hcov
  · intro x hx y hy hkx hxy
    exact hclean x (hraw hx) y (hraw hy) (le_trans hle hkx) hxy
  · intro x hx hlt
    exact hsweep x (hl hx) (lt_of_le_of_lt hle hlt)

theorem opposes_widen {Key Blk : Type*} (c : Key → Blk → Prop)
    {e₂ e₁ l₁ l₂ raw₁ raw₂ : Finset (Token Key)} {B : Blk}
    (he : e₂ ⊆ e₁) (hl : l₁ ⊆ l₂) (hraw : raw₁ ⊆ raw₂)
    (hO : Opposes c e₁ l₁ raw₁ B) : Opposes c e₂ l₂ raw₂ B := by
  rcases hO with ⟨x, hx, hguard, hnot⟩ | ⟨x, hx, y, hy, hguard, hround, hkey⟩
  · exact Or.inl ⟨x, hl hx, fun u hu => hguard u (he hu), hnot⟩
  · exact Or.inr ⟨x, hraw hx, y, hraw hy, fun u hu => hguard u (he hu), hround, hkey⟩



/-! ## The two phase-level inclusions

Per validator: a grade-2 supporter is a grade-1 supporter, and a grade-1
opponent is a grade-2 opponent. Everything else about `Q5` is weight
monotonicity. -/

theorem positive_g2_imp_g1 (E : Env V) (hc : Protocol.HealConfig)
    (gv : Protocol.GradeView V) (F : Block V) (r : Round) (v : V) (B : Block V)
    (h : positive gv F hc.η_SG r (early E hc r .g2) (late E hc r .g2) v B = true) :
    positive gv F hc.η_SG r (early E hc r .g1) (late E hc r .g1) v B = true := by
  simp only [positive, decide_eq_true_eq] at h ⊢
  refine supports_narrow _
    (readyView_mono gv F hc.η_SG r (early_g2_le_early_g1 E hc r) v)
    (readyView_mono gv F hc.η_SG r (late_g1_le_late_g2 E hc r) v)
    (rawView_mono gv hc.η_SG r (late_g1_le_late_g2 E hc r) v)
    (readyView_mono gv F hc.η_SG r (early_g1_le_late_g2 E hc r) v)
    (Finset.Subset.trans (readyView_subset_rawView gv F hc.η_SG r _ v)
      (rawView_mono gv hc.η_SG r (early_g1_le_late_g2 E hc r) v)) h

theorem opposing_g1_imp_g2 (E : Env V) (hc : Protocol.HealConfig)
    (gv : Protocol.GradeView V) (F : Block V) (r : Round) (v : V) (B : Block V)
    (h : opposing gv F hc.η_SG r (early E hc r .g1) (late E hc r .g1) v B = true) :
    opposing gv F hc.η_SG r (early E hc r .g2) (late E hc r .g2) v B = true := by
  simp only [opposing, decide_eq_true_eq] at h ⊢
  exact opposes_widen _
    (readyView_mono gv F hc.η_SG r (early_g2_le_early_g1 E hc r) v)
    (readyView_mono gv F hc.η_SG r (late_g1_le_late_g2 E hc r) v)
    (rawView_mono gv hc.η_SG r (late_g1_le_late_g2 E hc r) v) h

theorem positive_g2_imp_g0 (E : Env V) (hc : Protocol.HealConfig)
    (gv : Protocol.GradeView V) (F : Block V) (r : Round) (v : V) (B : Block V)
    (h : positive gv F hc.η_SG r (early E hc r .g2) (late E hc r .g2) v B = true) :
    positive gv F hc.η_SG r (early E hc r .g0) (late E hc r .g0) v B = true := by
  simp only [positive, decide_eq_true_eq] at h ⊢
  refine supports_narrow _
    (readyView_mono gv F hc.η_SG r (early_g2_le_early_g0 E hc r) v)
    (readyView_mono gv F hc.η_SG r (late_g0_le_late_g2 E hc r) v)
    (rawView_mono gv hc.η_SG r (late_g0_le_late_g2 E hc r) v)
    (readyView_mono gv F hc.η_SG r (early_g0_le_late_g2 E hc r) v)
    (Finset.Subset.trans (readyView_subset_rawView gv F hc.η_SG r _ v)
      (rawView_mono gv hc.η_SG r (early_g0_le_late_g2 E hc r) v)) h

theorem opposing_g0_imp_g2 (E : Env V) (hc : Protocol.HealConfig)
    (gv : Protocol.GradeView V) (F : Block V) (r : Round) (v : V) (B : Block V)
    (h : opposing gv F hc.η_SG r (early E hc r .g0) (late E hc r .g0) v B = true) :
    opposing gv F hc.η_SG r (early E hc r .g2) (late E hc r .g2) v B = true := by
  simp only [opposing, decide_eq_true_eq] at h ⊢
  exact opposes_widen _
    (readyView_mono gv F hc.η_SG r (early_g2_le_early_g0 E hc r) v)
    (readyView_mono gv F hc.η_SG r (late_g0_le_late_g2 E hc r) v)
    (rawView_mono gv hc.η_SG r (late_g0_le_late_g2 E hc r) v) h





/-! ## Support of one block opposes any conflicting block

A supporter's latest early token covers the block it supports, and one key
cannot cover two conflicting blocks, so that same token witnesses opposition to
every conflicting block at the same phase. -/

theorem opposing_of_positive_conflicts (E : Env V) (hc : Protocol.HealConfig)
    (gv : Protocol.GradeView V) (F : Block V) (r : Round) (p : Phase) (v : V)
    {B B' : Block V} (hconf : Block.conflicts B' B = true)
    (h : positive gv F hc.η_SG r (early E hc r p) (late E hc r p) v B' = true) :
    opposing gv F hc.η_SG r (early E hc r p) (late E hc r p) v B = true := by
  simp only [positive, decide_eq_true_eq] at h
  simp only [opposing, decide_eq_true_eq]
  obtain ⟨u, hu, hmax, hcov, -, -⟩ := h
  refine Or.inl ⟨u, readyView_mono gv F hc.η_SG r (early_le_late E hc r p) v hu,
    hmax, ?_⟩
  intro hcovB
  have hcompat : Block.compatible B' B = true := by
    simp only [localCovers] at hcov hcovB
    cases hkey : u.key with
    | none => simp [Protocol.head_covers, hkey] at hcov
    | some root =>
      simp only [Protocol.head_covers, hkey] at hcov hcovB
      cases hf : Block.find? gv.T root with
      | none => simp [hf] at hcov
      | some head =>
        simp only [hf] at hcov hcovB
        exact Block.compatible_of_preceq_common hcov hcovB
  simp [Block.conflicts, hcompat] at hconf

#print axioms opposing_of_positive_conflicts

end DecoupledConsensusModel.Proofs.GradeCutoffMono

end
