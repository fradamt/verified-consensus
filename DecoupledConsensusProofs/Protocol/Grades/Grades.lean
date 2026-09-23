module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.PhaseGradeQueries
public import DecoupledConsensusProofs.Protocol.Grades.Anchor
public import DecoupledConsensusProofs.Protocol.Grades.GradeCutoffMono

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingLemmas

open Protocol (GradeView HealConfig)
open Protocol (SGVote)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 0. Plumbing

Two leaves: weight is monotone along an implication between filters, and two
strict majorities meet. -/

/-- Weight is monotone along an implication between two decidable filters over
`V` (PROTOCOL.md#the-complete-protocol). The companion of `Proofs.Optimistic.weight_filter_le_faulty`,
which is the same step with `q:= (· ∉ Hon)`. -/
theorem weightOf_filter_mono (E : Env V) {p q : V → Prop} [DecidablePred p]
    [DecidablePred q] (h : ∀ v, p v → q v) :
    E.electorate.weightOf (Finset.univ.filter p) ≤
      E.electorate.weightOf (Finset.univ.filter q) :=
  E.electorate.weightOf_mono (fun i hi =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, h i (Finset.mem_filter.mp hi).2⟩)

/-- **Two strict majorities meet** (PROTOCOL.md#the-complete-protocol).
`m = ⌊W/2⌋ + 1`, so `2m > W` and two sets of weight `≥ m` cannot be disjoint.

The pigeonhole behind the two-view lemma. It is pure weight arithmetic: no
honesty, no fault bound, no quorum. -/
theorem exists_mem_inter_of_strictMajorities (E : Env V) {S T : Finset V}
    (hS : E.m ≤ E.electorate.weightOf S) (hT : E.m ≤ E.electorate.weightOf T) :
    ∃ v, v ∈ S ∧ v ∈ T := by
  by_contra hno
  have hno' : ∀ v, v ∈ S → v ∉ T := fun v hvS hvT => hno ⟨v, hvS, hvT⟩
  have hsub : S ∩ T ⊆ (∅ : Finset V) := by
    intro v hv
    exact absurd (Finset.mem_inter.mp hv).2 (hno' v (Finset.mem_inter.mp hv).1)
  have hinter : E.electorate.weightOf (S ∩ T) ≤ 0 :=
    le_trans (E.electorate.weightOf_mono hsub) (le_of_eq Finset.sum_empty)
  have hie := E.electorate.weight_inter_add_weight_union S T
  have hle : E.electorate.weightOf (S ∪ T) ≤ E.electorate.totalWeight :=
    E.electorate.weightOf_mono (Finset.subset_univ _)
  unfold Env.m Electorate.strictMajorityThreshold at hS hT
  omega

/-! ## 1. The cutoff order (PROTOCOL.md#the-complete-protocol)

`Γ_r^{−1} = t_{rR} − Δ`, `Γ_r^0 = t_{rR}`, `Γ_r^1 = t_{rR} + Δ`,
`Γ_r^2 = t_{rR} + 2Δ`. Four instants around one slot start, so the order is
`Δ > 0` and nothing else — which is exactly the sensitivity O1 was recorded for:
"it would fail loudly if a cutoff were ever edited".

The three are stated against the slot start as one `Int` atom, in the idiom
`Availability/Sync.lean` uses throughout: `omega` is handed an explicit `Int`
lemma rather than a `Time`-typed goal. -/

/-- §6.1 `Γ_r^{−1} < Γ_r^0` (PROTOCOL.md#the-complete-protocol). -/
theorem Γ_neg1_lt_Γ_0 (hc : HealConfig) {Δ : Time} (hΔ : 0 < Δ) (r : Round) :
    hc.Γ_neg1 Δ r < hc.Γ_0 Δ r := by
  have key : ∀ a d : Int, 0 < d → a - d < a := by intro a d h; omega
  exact key (slotStart Δ (hc.opening_slot r)) Δ hΔ

/-- §6.1 `Γ_r^0 < Γ_r^1` (PROTOCOL.md#the-complete-protocol). -/
theorem Γ_0_lt_Γ_1 (hc : HealConfig) {Δ : Time} (hΔ : 0 < Δ) (r : Round) :
    hc.Γ_0 Δ r < hc.Γ_1 Δ r := by
  have key : ∀ a d : Int, 0 < d → a < a + d := by intro a d h; omega
  exact key (slotStart Δ (hc.opening_slot r)) Δ hΔ

/-- §6.1 `Γ_r^1 < Γ_r^2` (PROTOCOL.md#the-complete-protocol). -/
theorem Γ_1_lt_Γ_2 (hc : HealConfig) {Δ : Time} (hΔ : 0 < Δ) (r : Round) :
    hc.Γ_1 Δ r < hc.Γ_2 Δ r := by
  have key : ∀ a d : Int, 0 < d → a + d < a + 2 * d := by intro a d h; omega
  exact key (slotStart Δ (hc.opening_slot r)) Δ hΔ

/-! ## 2. O1 — the monotonicity chain (PROTOCOL.md#the-complete-protocol; obligations O1)

Two support monotonicities and one inclusion. `direct_support` is monotone
**up** in the head cutoff and **down** in the equivocation cutoff — the two
arguments move in opposite directions, because `Γ_e` gates `Γ_e ≤ e_v` — and
every direct supporter at a head cutoff is a favorable supporter at any later
one. -/

/-- §6.2 `direct_support` is monotone: later head cutoff, earlier equivocation
cutoff (PROTOCOL.md#the-complete-protocol). -/
theorem direct_support_mono (E : Env V) (gv : GradeView V) (r : Round)
    {Γ_h Γ_h' Γ_e Γ_e' : Time} (hh : Γ_h ≤ Γ_h') (he : Γ_e' ≤ Γ_e) (B : Block V) :
    Protocol.direct_support E gv r Γ_h Γ_e B ≤
      Protocol.direct_support E gv r Γ_h' Γ_e' B := by
  simp only [Protocol.direct_support]
  refine weightOf_filter_mono E ?_
  intro v hv
  obtain ⟨ht, hcov, hev⟩ := hv
  exact ⟨occurrenceBefore_mono hh ht, hcov, occurrenceAtLeast_anti he hev⟩

/-- **O1 row 5, `Q5_G2_imp_G1`.** The relative G2 window is contained in
the relative G1 window at both cutoffs. -/
theorem q5_G2_imp_G1 (E : Env V) (hc : Protocol.HealConfig) :
    DecoupledConsensusModel.Internal.PhaseGrades.Q5_G2_imp_G1 E hc := by
  intro gv F r B h
  simp only [DecoupledConsensusModel.Internal.PhaseGrades.phaseGrade,
    DecoupledConsensusModel.Protocol.gradeBool, decide_eq_true_eq] at h ⊢
  refine lt_of_le_of_lt (weightOf_filter_mono E ?_)
    (lt_of_lt_of_le h (weightOf_filter_mono E ?_))
  · exact fun v hv => DecoupledConsensusModel.Proofs.GradeCutoffMono.opposing_g1_imp_g2 E hc gv F r v B hv
  · exact fun v hv => DecoupledConsensusModel.Proofs.GradeCutoffMono.positive_g2_imp_g1 E hc gv F r v B hv

/-- The relative G1/G2 compatibility query. -/
theorem q6_G1_G2_compatible (E : Env V) (hc : Protocol.HealConfig) :
    DecoupledConsensusModel.Internal.PhaseGrades.Q6_G1_G2_compatible E hc := by
  intro gv F r B B' hB hB'
  by_contra hne
  have hcompatBB' : Block.compatible B B' = false := by
    cases h : Block.compatible B B' with
    | false => rfl
    | true => exact absurd h hne
  have hcompatB'B : Block.compatible B' B = false := by
    simp only [Block.compatible, Bool.or_eq_false_iff] at hcompatBB' ⊢
    exact ⟨hcompatBB'.2, hcompatBB'.1⟩
  have hconfBB' : Block.conflicts B B' = true := by
    simp [Block.conflicts, hcompatBB']
  have hconfB'B : Block.conflicts B' B = true := by
    simp [Block.conflicts, hcompatB'B]
  have hB'1 := q5_G2_imp_G1 E hc gv F r B' hB'
  simp only [DecoupledConsensusModel.Internal.PhaseGrades.phaseGrade,
    DecoupledConsensusModel.Protocol.gradeBool, decide_eq_true_eq] at hB hB'1
  have hPB : ∀ v, DecoupledConsensusModel.Protocol.positive gv F hc.η_SG r
      (DecoupledConsensusModel.Protocol.early E hc r .g1) (DecoupledConsensusModel.Protocol.late E hc r .g1) v B = true →
      DecoupledConsensusModel.Protocol.opposing gv F hc.η_SG r
        (DecoupledConsensusModel.Protocol.early E hc r .g1) (DecoupledConsensusModel.Protocol.late E hc r .g1) v B' = true :=
    fun v hv => GradeCutoffMono.opposing_of_positive_conflicts E hc gv F r .g1 v hconfBB' hv
  have hPB' : ∀ v, DecoupledConsensusModel.Protocol.positive gv F hc.η_SG r
      (DecoupledConsensusModel.Protocol.early E hc r .g1) (DecoupledConsensusModel.Protocol.late E hc r .g1) v B' = true →
      DecoupledConsensusModel.Protocol.opposing gv F hc.η_SG r
        (DecoupledConsensusModel.Protocol.early E hc r .g1) (DecoupledConsensusModel.Protocol.late E hc r .g1) v B = true :=
    fun v hv => GradeCutoffMono.opposing_of_positive_conflicts E hc gv F r .g1 v hconfB'B hv
  exact absurd (lt_of_le_of_lt (weightOf_filter_mono E hPB)
    (lt_of_lt_of_le hB'1 (weightOf_filter_mono E hPB'))) (lt_asymm hB)



/-- **O1 row 5 in the compatibility grade vocabulary.** The `Protocol.G*` chain is still
what the delivered-grade ladder consumes; it is unrelated to `phaseGrade`. -/

theorem G2_imp_G1 (E : Env V) (gv : GradeView V) (hc : HealConfig) (r : Round)
    (B : Block V) (h : Protocol.G2 E gv hc r B = true) :
    Protocol.G1 E gv hc r B = true := by
  simp only [Protocol.G2, decide_eq_true_eq] at h
  simp only [Protocol.G1, decide_eq_true_eq]
  refine le_trans h (direct_support_mono E gv r ?_ ?_ B)
  · exact le_of_lt (Γ_neg1_lt_Γ_0 hc E.Δ_pos r)
  · exact le_trans (le_of_lt (Γ_0_lt_Γ_1 hc E.Δ_pos r))
      (le_of_lt (Γ_1_lt_Γ_2 hc E.Δ_pos r))

omit [Fintype V] in
/-- Root resolution returns a member of the tree it ranges over
(PROTOCOL.md#the-complete-protocol). -/
theorem find?_mem {T : Finset (Block V)} {root : BlockId} {H : Block V}
    (h : Block.find? T root = some H) : H ∈ T := by
  unfold Block.find? at h
  exact Proofs.Engine.pickUnique?_mem h

omit [Fintype V] in
/-- Root resolution answers with the root it was asked for
(PROTOCOL.md#the-complete-protocol). -/
theorem find?_root {T : Finset (Block V)} {root : BlockId} {H : Block V}
    (h : Block.find? T root = some H) : H.root = root := by
  unfold Block.find? pickUnique? at h
  split at h
  · rename_i hex
    rw [Option.some_inj] at h
    subst h
    exact of_decide_eq_true (Finset.choose_property _ _ hex)
  · exact absurd h (by simp)

omit [Fintype V] in
/-- §6.2 a head root that covers a block resolves, and the block is below the
resolved head (PROTOCOL.md#the-complete-protocol). The elimination form of `head_covers`. -/
theorem exists_head_of_head_covers {T : Finset (Block V)} {B : Block V}
    {H : Option BlockId} (h : Protocol.head_covers T B H = true) :
    ∃ (root : BlockId) (head : Block V), H = some root ∧
      Block.find? T root = some head ∧ head ∈ T ∧ Block.preceq B head = true := by
  cases H with
  | none => exact absurd h (by simp [Protocol.head_covers])
  | some root =>
    simp only [Protocol.head_covers] at h
    cases hf : Block.find? T root with
    | none => rw [hf] at h; exact absurd h (by simp)
    | some head =>
      rw [hf] at h
      exact ⟨root, head, rfl, hf, find?_mem hf, h⟩

omit [Fintype V] in
/-- **One head covers two compatible blocks** (PROTOCOL.md#the-complete-protocol). Two
blocks below one head are ancestors of a common block, hence comparable. -/
theorem compatible_of_head_covers {T : Finset (Block V)} {B B' : Block V}
    {H : Option BlockId} (h : Protocol.head_covers T B H = true)
    (h' : Protocol.head_covers T B' H = true) : Block.compatible B B' = true := by
  obtain ⟨root, head, hH, hf, -, hB⟩ := exists_head_of_head_covers h
  subst hH
  simp only [Protocol.head_covers, hf] at h'
  exact Block.compatible_of_preceq_common hB h'

/-- **The two-view lemma** (doc2 §4 `cor:g3-chain`; PROTOCOL.md#the-complete-protocol,
952–954).

Two blocks whose **direct** support reaches `m` in one view are compatible, at
any two pairs of cutoffs. The two majorities meet in a validator, that validator
has one `C_v`, and both blocks lie below it.

Restricted to direct support, and it has to be: `favorable_support`'s second set
is `B`-independent, so an equivocating majority credits *every* branch and two
conflicting blocks can both hold grade 1 (PROTOCOL.md#the-complete-protocol). -/
theorem direct_support_compatible (E : Env V) {gv : GradeView V} {r : Round}
    {Γ_h Γ_e Γ_h' Γ_e' : Time} {B B' : Block V}
    (hB : E.m ≤ Protocol.direct_support E gv r Γ_h Γ_e B)
    (hB' : E.m ≤ Protocol.direct_support E gv r Γ_h' Γ_e' B') :
    Block.compatible B B' = true := by
  simp only [Protocol.direct_support] at hB hB'
  obtain ⟨v, hv, hv'⟩ := exists_mem_inter_of_strictMajorities E hB hB'
  obtain ⟨-, hcov, -⟩ := (Finset.mem_filter.mp hv).2
  obtain ⟨-, hcov', -⟩ := (Finset.mem_filter.mp hv').2
  exact compatible_of_head_covers hcov hcov'





/-- **Two `g0`-graded `phaseGrade` blocks are compatible** (
`SelfClearance` route step 3). `q6_G1_G2_compatible`'s proof, specialised to
one phase throughout: no lift is needed because both hypotheses are already
`g0`, so `opposing_of_positive_conflicts` is applied at `.g0` directly. -/
theorem phaseGrade_g0_compatible (E : Env V) (hc : Protocol.HealConfig)
    (gv : GradeView V) (F : Block V) (r : Round) (B B' : Block V)
    (hB : DecoupledConsensusModel.Internal.PhaseGrades.phaseGrade E hc gv F r .g0 B = true)
    (hB' : DecoupledConsensusModel.Internal.PhaseGrades.phaseGrade E hc gv F r .g0 B' = true) :
    Block.compatible B B' = true := by
  by_contra hne
  have hcompatBB' : Block.compatible B B' = false := by
    cases h : Block.compatible B B' with
    | false => rfl
    | true => exact absurd h hne
  have hcompatB'B : Block.compatible B' B = false := by
    simp only [Block.compatible, Bool.or_eq_false_iff] at hcompatBB' ⊢
    exact ⟨hcompatBB'.2, hcompatBB'.1⟩
  have hconfBB' : Block.conflicts B B' = true := by
    simp [Block.conflicts, hcompatBB']
  have hconfB'B : Block.conflicts B' B = true := by
    simp [Block.conflicts, hcompatB'B]
  simp only [DecoupledConsensusModel.Internal.PhaseGrades.phaseGrade,
    DecoupledConsensusModel.Protocol.gradeBool, decide_eq_true_eq] at hB hB'
  have hPB : ∀ v, DecoupledConsensusModel.Protocol.positive gv F hc.η_SG r
      (DecoupledConsensusModel.Protocol.early E hc r .g0) (DecoupledConsensusModel.Protocol.late E hc r .g0) v B = true →
      DecoupledConsensusModel.Protocol.opposing gv F hc.η_SG r
        (DecoupledConsensusModel.Protocol.early E hc r .g0) (DecoupledConsensusModel.Protocol.late E hc r .g0) v B' = true :=
    fun v hv => GradeCutoffMono.opposing_of_positive_conflicts E hc gv F r .g0 v hconfBB' hv
  have hPB' : ∀ v, DecoupledConsensusModel.Protocol.positive gv F hc.η_SG r
      (DecoupledConsensusModel.Protocol.early E hc r .g0) (DecoupledConsensusModel.Protocol.late E hc r .g0) v B' = true →
      DecoupledConsensusModel.Protocol.opposing gv F hc.η_SG r
        (DecoupledConsensusModel.Protocol.early E hc r .g0) (DecoupledConsensusModel.Protocol.late E hc r .g0) v B = true :=
    fun v hv => GradeCutoffMono.opposing_of_positive_conflicts E hc gv F r .g0 v hconfB'B hv
  exact absurd (lt_of_le_of_lt (weightOf_filter_mono E hPB)
    (lt_of_lt_of_le hB' (weightOf_filter_mono E hPB'))) (lt_asymm hB)

/-- **Two grade-1 blocks are compatible** (PROTOCOL.md#the-complete-protocol): the fact
that makes `fresh_anchor`'s "deepest" well defined. -/
theorem G1_compatible (E : Env V) {gv : GradeView V} {hc : HealConfig} {r : Round}
    {B B' : Block V} (hB : Protocol.G1 E gv hc r B = true)
    (hB' : Protocol.G1 E gv hc r B' = true) : Block.compatible B B' = true := by
  simp only [Protocol.G1, decide_eq_true_eq] at hB hB'
  exact direct_support_compatible E hB hB'

omit [Fintype V] in
/-- §1 `Block.deepest?` dominates every member of its set that is compatible
with it (PROTOCOL.md#the-complete-protocol). -/
theorem deepest?_dominates {T : Finset (Block V)} {L B : Block V}
    (hL : Block.deepest? T = some L) (hB : B ∈ T)
    (hcmp : Block.compatible B L = true) : Block.preceq B L = true := by
  have hLmem : L ∈ T := Proofs.Engine.deepest?_mem hL
  have hdeep : Block.isDeepestIn T L = true := by
    unfold Block.deepest? pickUnique? at hL
    split at hL
    · rename_i hex
      rw [Option.some_inj] at hL
      subst hL
      exact Finset.choose_property _ _ hex
    · exact absurd hL (by simp)
  simp only [Block.isDeepestIn, decide_eq_true_eq] at hdeep
  have hBL := hdeep B hB
  simp only [Block.deeper, Bool.or_eq_false_iff, Bool.and_eq_false_imp,
    decide_eq_false_iff_not, Nat.not_lt] at hBL
  exact AlignedRoundLemmas.preceq_of_compatible_of_depth_le hcmp hBL.1


/-- A head root that is compatible with `B`: the empty head and an unresolvable
root both qualify, since neither supports anything (modeling-choices row 1,
choices S2.5). The compatibility twin of `Proofs.Optimistic.rootOnCan`. -/
def rootCompatible (T : Finset (Block V)) (B : Block V) : Option BlockId → Bool
  | none => true
  | some root =>
    match Block.find? T root with
    | some H => Block.compatible H B
    | none => true







omit [Fintype V] in
/-- **A head compatible with `B` covers nothing that conflicts with `B`**
(PROTOCOL.md#the-complete-protocol). The clearing step.

Two cases, and both collapse: if the head is an ancestor of `B`, a block below
the head is below `B`; if `B` is an ancestor of the head, the two are ancestors
of a common block. Either way the covered block is compatible with `B`. -/
theorem head_covers_eq_false_of_conflicts {T : Finset (Block V)} {B B' : Block V}
    {H : Option BlockId} (hcmp : rootCompatible T B H = true)
    (hconf : Block.conflicts B' B = true) : Protocol.head_covers T B' H = false := by
  rw [← Bool.not_eq_true]
  intro hcov
  obtain ⟨root, head, hH, hf, -, hB'⟩ := exists_head_of_head_covers hcov
  subst hH
  simp only [rootCompatible, hf] at hcmp
  simp only [Block.compatible, Bool.or_eq_true] at hcmp
  have hcompat : Block.compatible B' B = true := by
    rcases hcmp with h | h
    · simp only [Block.compatible, Bool.or_eq_true]
      exact Or.inl (Block.preceq_trans hB' h)
    · exact Block.compatible_of_preceq_common hB' h
  simp only [Block.conflicts, hcompat] at hconf
  exact absurd hconf (by simp)



omit [Fintype V] in

/-- An honest reader's retained token never covers a block that conflicts with
the block its whole batch is compatible with. -/
theorem not_localCovers_of_batchCompatibleAt
    {gv : GradeView V} {hc : HealConfig} {F : Block V} {Hon : Finset V} {r : Round}
    {cutoff : Time} {B B' : Block V}
    (hbatch : DecoupledConsensusModel.Internal.PhaseGrades.BatchCompatibleAt
      hc gv F Hon r cutoff B)
    (hconf : Block.conflicts B' B = true) {v : V} (hv : v ∈ Hon)
    {u : Protocol.SGVote V}
    (hu : u ∈ DecoupledConsensusModel.Protocol.interpretedInputs gv F hc.η_SG r cutoff v) :
    DecoupledConsensusModel.Protocol.localCovers gv (DecoupledConsensusModel.Protocol.token u).key B' ≠ true := by
  intro hcov
  have hroot : rootCompatible gv.T B u.confirmed = true := by
    cases hc' : u.confirmed with
    | none => rfl
    | some root =>
      simp only [rootCompatible]
      cases hf : Block.find? gv.T root with
      | none => rfl
      | some head =>
        have hhead : head.root = root := find?_root hf
        have hcmp := hbatch v hv u hu head (by rw [hc', hhead]) (by rw [hhead]; exact hf)
        simp only [Block.compatible, Bool.or_eq_true] at hcmp ⊢
        exact hcmp.symm
  simp only [DecoupledConsensusModel.Protocol.localCovers, DecoupledConsensusModel.Protocol.token] at hcov
  rw [head_covers_eq_false_of_conflicts hroot hconf] at hcov
  exact absurd hcov (by simp)


/-- **O1 row 7, `Q7`**. Under a batch compatible with `B`, an
honest present reader opposes every conflicting `B'` and none supports it, so
the conflicting block's support is faulty weight and its opposition is at least
the honest present weight. -/
theorem q7_grade_eq_false_of_conflicts (E : Env V) (hc : Protocol.HealConfig) :
    DecoupledConsensusModel.Internal.PhaseGrades.Q7_grade_eq_false_of_conflicts E hc := by
  intro gv F Hon r B B' p hbatch hmaj hconf
  simp only [DecoupledConsensusModel.Internal.PhaseGrades.phaseGrade,
    DecoupledConsensusModel.Protocol.gradeBool, decide_eq_false_iff_not, not_lt]
  have hearly : DecoupledConsensusModel.Protocol.early E hc r p ≤ DecoupledConsensusModel.Protocol.late E hc r p :=
    GradeCutoffMono.early_le_late E hc r p
  -- no honest reader supports the conflicting block
  have hpos : E.electorate.weightOf (Finset.univ.filter fun v =>
      DecoupledConsensusModel.Protocol.positive gv F hc.η_SG r (DecoupledConsensusModel.Protocol.early E hc r p)
        (DecoupledConsensusModel.Protocol.late E hc r p) v B' = true) ≤
      E.electorate.weightOf (Finset.univ \ Hon) := by
    refine Proofs.Optimistic.weight_filter_le_faulty E ?_
    intro v hp hvH
    simp only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq] at hp
    obtain ⟨u, hu, -, hcov, -, -⟩ := hp
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hu
    exact not_localCovers_of_batchCompatibleAt hbatch hconf hvH
      (GradeCutoffMono.interpretedInputs_mono gv F hc.η_SG r hearly v hw) hcov
  -- every honest present reader opposes it
  have hopp : E.electorate.weightOf
      (DecoupledConsensusModel.Internal.PhaseGrades.honestPresent hc gv F Hon r
        (DecoupledConsensusModel.Protocol.late E hc r p)) ≤
      E.electorate.weightOf (Finset.univ.filter fun v =>
        DecoupledConsensusModel.Protocol.opposing gv F hc.η_SG r (DecoupledConsensusModel.Protocol.early E hc r p)
          (DecoupledConsensusModel.Protocol.late E hc r p) v B' = true) := by
    refine E.electorate.weightOf_mono ?_
    intro v hv
    simp only [DecoupledConsensusModel.Internal.PhaseGrades.honestPresent,
      Finset.mem_filter] at hv
    obtain ⟨hvH, hne⟩ := hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      DecoupledConsensusModel.Protocol.opposing, decide_eq_true_eq]
    obtain ⟨x, hx, hmax⟩ :=
      Finset.exists_max_image
        (DecoupledConsensusModel.Protocol.readyView gv F hc.η_SG r
          (DecoupledConsensusModel.Protocol.late E hc r p) v)
        (fun t => t.round) (hne.image DecoupledConsensusModel.Protocol.token)
    refine Or.inl ⟨x, hx, fun w hw => hmax w
      (GradeCutoffMono.readyView_mono gv F hc.η_SG r hearly v hw), ?_⟩
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
    exact not_localCovers_of_batchCompatibleAt hbatch hconf hvH hw
  exact le_trans hpos (le_trans (le_of_lt hmaj) hopp)



/-! `active_grade_eq_false_of_conflicts` — the same statement about the
`active_grade` wrapper — is **retired** with the wrapper (PROTOCOL.md#the-complete-protocol
is now prose). It restricted `grade_eq_false_of_conflicts` by a conjunct that can
only shrink the set, so it never carried content, and every site that reads a
grade now reads it bare. -/





/-! ## 5. The honest supporter (doc2 §4 `lem:g1-acceptance`;
PROTOCOL.md#the-complete-protocol)

The store-level half of the visibility guarantee: a graded block has an
**honest** supporter, and that supporter's own head names it. The run-level half
— that the head therefore reaches every honest node before the grade-0 freeze —
is `HealingLemmas/Delivery.lean`, which consumes exactly this. -/

/-- **A direct majority contains an honest supporter**
(PROTOCOL.md#the-complete-protocol). `w(faulty) < m`, so the supporting set cannot
be faulty throughout. -/
theorem exists_honest_direct_supporter_of_faulty_lt_m (E : Env V) {gv : GradeView V}
    {Hon : Finset V} {r : Round} {B : Block V} {Γ_h Γ_e : Time}
    (hmlt : E.electorate.weightOf (Finset.univ \ Hon) < E.m)
    (hm : E.m ≤ Protocol.direct_support E gv r Γ_h Γ_e B) :
    ∃ v ∈ Hon, occurrenceBefore (Protocol.summary gv r v).t_v Γ_h = true ∧
      Protocol.head_covers gv.T B (Protocol.summary gv r v).C_v = true := by
  by_contra hno
  have hno' : ∀ v ∈ Hon, occurrenceBefore (Protocol.summary gv r v).t_v Γ_h = true →
      Protocol.head_covers gv.T B (Protocol.summary gv r v).C_v = false := by
    intro v hv ht
    rw [← Bool.not_eq_true]
    exact fun hcov => hno ⟨v, hv, ht, hcov⟩
  have hle : Protocol.direct_support E gv r Γ_h Γ_e B ≤
      E.electorate.weightOf (Finset.univ \ Hon) := by
    simp only [Protocol.direct_support]
    refine Proofs.Optimistic.weight_filter_le_faulty E ?_
    intro v hp hvH
    obtain ⟨ht, hcov, -⟩ := hp
    rw [hno' v hvH ht] at hcov
    exact absurd hcov (by simp)
  omega

/-- Compatibility wrapper for callers with the stronger fault bound. -/
theorem exists_honest_direct_supporter (E : Env V) {gv : GradeView V}
    {Hon : Finset V} {r : Round} {B : Block V} {Γ_h Γ_e : Time}
    (hfb : 3 * E.electorate.weightOf (Finset.univ \ Hon) < E.W)
    (hm : E.m ≤ Protocol.direct_support E gv r Γ_h Γ_e B) :
    ∃ v ∈ Hon, occurrenceBefore (Protocol.summary gv r v).t_v Γ_h = true ∧
      Protocol.head_covers gv.T B (Protocol.summary gv r v).C_v = true := by
  have hmlt : E.electorate.weightOf (Finset.univ \ Hon) < E.m := by
    unfold Env.m Env.W Electorate.strictMajorityThreshold at *
    omega
  exact exists_honest_direct_supporter_of_faulty_lt_m E hmlt hm


#print axioms q7_grade_eq_false_of_conflicts
#print axioms G2_imp_G1


end HealingLemmas
end Proofs
end DecoupledConsensusModel

end
