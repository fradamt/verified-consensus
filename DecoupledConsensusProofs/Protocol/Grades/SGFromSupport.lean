module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.NonInterference
public import DecoupledConsensusProofs.Protocol.Grades.FrameForward
public import DecoupledConsensusProofs.Protocol.Grades.FrameCompleted
public import DecoupledConsensusProofs.Protocol.Grades.Grades
public import DecoupledConsensusProofs.Protocol.Grades.VoteBelowSource
public import DecoupledConsensusProofs.Protocol.Grades.ProposalParent
public import DecoupledConsensusProofs.Execution.EarlyHolding
public import DecoupledConsensusProofs.Execution.OutageProvenance
public import DecoupledConsensusProofs.Protocol.Handlers.SGArrival
public import DecoupledConsensusProofs.Protocol.Grades.HealthyHeadReady
public import DecoupledConsensusProofs.Protocol.Handlers.BlockStamp
public import DecoupledConsensusInternal.Definitions.NamedJointOutage
public import DecoupledConsensusProofs.Execution.OutputSeedCore

@[expose] public section



namespace DecoupledConsensusModel.Proofs.NamedOutageClosure
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedJointOutage Internal.OutageEntryRevision
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. A wider cutoff sees more inputs -/

omit [Fintype V] in
private theorem sg_raw_inputs_mono (gv : Protocol.GradeView V) (eta r : Round)
    {c c' : Time} (h : c ≤ c') (u : V) :
    DecoupledConsensusModel.Protocol.rawInputs gv eta r c u ⊆ DecoupledConsensusModel.Protocol.rawInputs gv eta r c' u := by
  intro x hx
  simp only [DecoupledConsensusModel.Protocol.rawInputs, Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.1, occurrenceBefore_mono h hx.2.2⟩

omit [Fintype V] in
private theorem sg_body_ready_mono (gv : Protocol.GradeView V) (F : Block V)
    {c c' : Time} (h : c ≤ c') {u : Protocol.SGVote V}
    (hu : DecoupledConsensusModel.Protocol.bodyReady gv F c u = true) :
    DecoupledConsensusModel.Protocol.bodyReady gv F c' u = true := by
  unfold DecoupledConsensusModel.Protocol.bodyReady at hu ⊢
  rcases Option.eq_none_or_eq_some u.confirmed with hcr | ⟨root, hcr⟩
  · rw [hcr]
  · rw [hcr] at hu ⊢
    dsimp only at hu ⊢
    rcases Option.eq_none_or_eq_some (Block.find? gv.T root) with hf | ⟨H, hf⟩
    · rw [hf] at hu
      exact absurd hu (by simp)
    · rw [hf] at hu ⊢
      simp only [Bool.and_eq_true] at hu ⊢
      exact ⟨occurrenceBefore_mono h hu.1, hu.2⟩

omit [Fintype V] in
private theorem sg_ready_view_mono (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    {c c' : Time} (h : c ≤ c') (u : V) :
    readyView gv F eta r c u ⊆ readyView gv F eta r c' u := by
  intro x hx
  simp only [readyView, Finset.mem_image] at hx ⊢
  obtain ⟨a, ha, hax⟩ := hx
  simp only [DecoupledConsensusModel.Protocol.interpretedInputs, Finset.mem_filter] at ha
  exact ⟨a, Finset.mem_filter.mpr ⟨sg_raw_inputs_mono gv eta r h u ha.1,
    sg_body_ready_mono gv F h ha.2⟩, hax⟩

/-! ## 2. Two blocks that carry the runtime grade are compatible -/

omit [Fintype V] in
private theorem sg_compatible_symm {B C : Block V} (h : Block.compatible B C = true) :
    Block.compatible C B = true := by
  simp only [Block.compatible, Bool.or_eq_true] at h ⊢
  exact h.symm

omit [Fintype V] in
/-- Two blocks covered by the same signed head are ancestors of that head, so
they are compatible. -/
private theorem sg_covers_compatible (gv : Protocol.GradeView V) {k : Option BlockId}
    {B B' : Block V} (hB : localCovers gv k B = true) (hB' : localCovers gv k B' = true) :
    Block.compatible B B' = true := by
  unfold localCovers Protocol.head_covers at hB hB'
  rcases Option.eq_none_or_eq_some k with hkr | ⟨root, hkr⟩
  · rw [hkr] at hB
    exact absurd hB (by simp)
  · rw [hkr] at hB hB'
    dsimp only at hB hB'
    rcases Option.eq_none_or_eq_some (Block.find? gv.T root) with hf | ⟨H, hf⟩
    · rw [hf] at hB
      exact absurd hB (by simp)
    · rw [hf] at hB hB'
      exact Block.compatible_of_preceq_common hB hB'

omit [Fintype V] in
/-- A sender that supports `B` opposes every block incompatible with `B`: its
maximal-round early head survives to the late view and cannot cover both. -/
private theorem sg_opposing_of_positive (gv : Protocol.GradeView V) (F : Block V)
    (eta r : Round) {e l : Time} (hel : e ≤ l) (u : V) {B B' : Block V}
    (hne : Block.compatible B B' = false)
    (hpos : positive gv F eta r e l u B = true) :
    opposing gv F eta r e l u B' = true := by
  simp only [positive, decide_eq_true_eq] at hpos
  obtain ⟨x, hx, hmax, hcov, -, -⟩ := hpos
  simp only [opposing, decide_eq_true_eq]
  refine Or.inl ⟨x, sg_ready_view_mono gv F eta r hel u hx, hmax, ?_⟩
  intro hcov'
  rw [sg_covers_compatible gv hcov hcov'] at hne
  exact absurd hne (by simp)

/-- **Two graded blocks are compatible.** If they were not, every supporter of
one would oppose the other, and the two strict weight margins would chase each
other in a circle. This is the `gradeBool` twin of `Proofs.HealingLemmas.G1_compatible`;
nothing on the tree proved it for the support/opposition runtime. -/
private theorem sg_graded_compatible (E : Env V) (gv : Protocol.GradeView V) (F : Block V)
    (eta r : Round) {e l : Time} (hel : e ≤ l) {B B' : Block V}
    (hB : gradeBool E gv F eta r e l B = true)
    (hB' : gradeBool E gv F eta r e l B' = true) : Block.compatible B B' = true := by
  by_contra hcon
  have hne : Block.compatible B B' = false := by
    simpa only [Bool.not_eq_true] using hcon
  have hne' : Block.compatible B' B = false := by
    by_contra h
    exact hcon (sg_compatible_symm (by simpa only [Bool.not_eq_false] using h))
  simp only [gradeBool, decide_eq_true_eq] at hB hB'
  have hsub : (Finset.univ.filter fun v => positive gv F eta r e l v B = true) ⊆
      Finset.univ.filter fun v => opposing gv F eta r e l v B' = true := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v,
      sg_opposing_of_positive gv F eta r hel v hne (Finset.mem_filter.mp hv).2⟩
  have hsub' : (Finset.univ.filter fun v => positive gv F eta r e l v B' = true) ⊆
      Finset.univ.filter fun v => opposing gv F eta r e l v B = true := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v,
      sg_opposing_of_positive gv F eta r hel v hne' (Finset.mem_filter.mp hv).2⟩
  have h1 := E.electorate.weightOf_mono hsub
  have h2 := E.electorate.weightOf_mono hsub'
  omega




/-! ## 3. The frozen root of a graded block covers it -/

/-- `freezeRoot` is the deepest graded block of the store tree. A graded member
is compatible with it, so the frozen root is at or above it. -/
theorem sg_freeze_of_graded (E : Env V) (gv : Protocol.GradeView V) (F : Block V)
    (eta r : Round) {e l : Time} (hel : e ≤ l) {B : Block V}
    (hmem : B ∈ gv.T) (hgrade : gradeBool E gv F eta r e l B = true) :
    ∃ raw : Block V, freezeRoot E gv F eta r e l = some raw ∧ Block.Preceq B raw := by
  have hBT : B ∈ gv.T.filter fun X => gradeBool E gv F eta r e l X = true :=
    Finset.mem_filter.mpr ⟨hmem, hgrade⟩
  have hcmp : ∀ X ∈ gv.T.filter fun X => gradeBool E gv F eta r e l X = true,
      ∀ Y ∈ gv.T.filter fun X => gradeBool E gv F eta r e l X = true,
      Block.compatible X Y = true := by
    intro X hX Y hY
    exact sg_graded_compatible E gv F eta r hel (Finset.mem_filter.mp hX).2
      (Finset.mem_filter.mp hY).2
  obtain ⟨raw, hraw⟩ := Option.isSome_iff_exists.mp
    (Proofs.HealingSurface.deepest?_isSome_of_compatible hcmp ⟨B, hBT⟩)
  refine ⟨raw, hraw, Proofs.HealingLemmas.deepest?_dominates hraw hBT
    (hcmp B hBT raw (Proofs.Engine.deepest?_mem hraw))⟩

/-! ## 4. From a covering frozen root in the frame to `activeG2` -/


/-! ## 5. Finality clipping keeps a compatible prefix (copies) -/

omit [Fintype V] in
/-- Copy of the private `NamedCacheProvenance.clip_preceq`. -/
private theorem sg_clip_preceq (g F : Block V) : Block.Preceq (clipGrade g F) g := by
  induction g with
  | genesis => exact Block.preceq_self _
  | node p s root gv gsv ats v ih =>
    simp only [clipGrade]
    split
    · exact Block.preceq_self _
    · apply Block.preceq_trans ih
      simp only [Block.preceq, Bool.or_eq_true]
      exact Or.inr (Block.preceq_self p)

omit [Fintype V] in
/-- Copy of the private `NamedCacheProvenance.retained_prefix`. -/
private theorem sg_retained_prefix (g F B : Block V) (hBF : Block.compatible B F = true) :
    Block.Preceq B (clipGrade g F) ↔ Block.Preceq B g := by
  constructor
  · intro h
    exact Block.preceq_trans h (sg_clip_preceq g F)
  · induction g with
    | genesis => exact fun h => h
    | node p s root gv gsv ats v ih =>
      intro hBg
      by_cases hGF : Block.compatible (.node p s root gv gsv ats v) F = true
      · simpa only [clipGrade, hGF, ↓reduceIte] using hBg
      · have hBp : Block.Preceq B p := by
          simp only [Block.Preceq, Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at hBg
          rcases hBg with hEq | hBp
          · subst B
            exact False.elim (hGF hBF)
          · exact hBp
        simpa only [clipGrade, hGF, Bool.eq_false_iff.mpr hGF, ↓reduceIte] using ih hBp

/-! ## 6. Schedule arithmetic -/

private theorem sg_early_le_late (S : Setup V) (r : Round) :
    early S.E S.hc r .g2 ≤ late S.E S.hc r .g2 := by
  have h : ∀ x d : Int, 0 < d → x + -5 * d ≤ x + -1 * d := by
    intro x d hd
    omega
  simpa only [early, late, Phase.earlyOffset, Phase.lateOffset] using
    h (opening S.E S.hc r) S.E.Δ S.E.Δ_pos

private theorem sg_a_eq (S : Setup V) (k : Round) :
    S.a k = 4 * S.E.Δ * ((S.hc.opening_slot k : Nat) : Int) + 6 * S.E.Δ := by
  unfold Setup.a Protocol.HealConfig.a slotStart
  ring

private theorem sg_domain_eq (S : Setup V) (k : Round) :
    domain S.E S.hc k .g2 = 4 * S.E.Δ * ((S.hc.opening_slot k : Nat) : Int) - S.E.Δ := by
  unfold domain opening Phase.domainOffset Protocol.proposal_time Env.t slotStart
  ring

private theorem sg_formation_eq (S : Setup V) (k : Round) :
    formationConfirmationTime S k =
      4 * S.E.Δ * ((S.hc.opening_slot k : Nat) : Int) + 2 * S.E.Δ := by
  unfold formationConfirmationTime Protocol.support_cutoff Env.t slotStart
  ring

/-- Pure arithmetic core of `sg_stable_deadline`. `m` and `n` are the opening
slots of `s` and `r`; `m + 3 ≤ n` is `3 ≤ R` together with `s < r`. -/
private theorem sg_deadline_arith : ∀ d m n : Int, 0 < d → m + 3 ≤ n →
    4 * d * m + 6 * d + d ≤ 4 * d * n - d := by
  intro d m n hd hmn
  have hnn : (0 : Int) ≤ 4 * d := by omega
  have h4 : 4 * d * (m + 3) ≤ 4 * d * n := Int.mul_le_mul_of_nonneg_left hmn hnn
  have h6 : 4 * d * (m + 3) = 4 * d * m + 12 * d := by ring
  omega

/-- The stable round's action deadline clears the round-`r` G2 domain tick.
**Boundary-free.** The only consequence of the previous
`b0 ≤ S.a r` that this gap used is the round bound `s < r`: with three slots of
headroom from `3 ≤ R` the schedule already leaves `12Δ` where the inequality
needs `8Δ`. The lemma therefore also holds for a round whose whole G2 phase runs
BEFORE the outage boundary, which is what the pre-boundary frame premise reads. -/
private theorem sg_stable_deadline (S : Setup V) (s r : Round)
    (hR : 3 ≤ S.hc.R) (hsr : s < r) :
    S.a s + S.E.Δ ≤ domain S.E S.hc r .g2 := by
  have hmn : ((S.hc.opening_slot s : Nat) : Int) + 3 ≤
      ((S.hc.opening_slot r : Nat) : Int) := by
    have hnat : S.hc.opening_slot s + 3 ≤ S.hc.opening_slot r := by
      unfold Protocol.HealConfig.opening_slot
      calc s * S.hc.R + 3 ≤ s * S.hc.R + S.hc.R := Nat.add_le_add_left hR _
        _ = (s + 1) * S.hc.R := by ring
        _ ≤ r * S.hc.R := Nat.mul_le_mul_right _ hsr
    exact_mod_cast hnat
  rw [sg_a_eq, sg_domain_eq]
  exact sg_deadline_arith S.E.Δ _ _ S.E.Δ_pos hmn

/-! ## 6b. Schedule arithmetic for the inventory time

`supportBoundary = min b0 (early S.E S.hc r.g2)` is the inventory time. The
five facts below place every honest action of a round at or below the stable
round `s` a full delay before **both** halves of that minimum. -/

private theorem sg_opening_eq (S : Setup V) (k : Round) :
    opening S.E S.hc k = 4 * S.E.Δ * ((S.hc.opening_slot k : Nat) : Int) := by
  unfold opening Protocol.proposal_time Env.t slotStart
  ring

private theorem sg_early_eq (S : Setup V) (k : Round) :
    early S.E S.hc k .g2 =
      4 * S.E.Δ * ((S.hc.opening_slot k : Nat) : Int) - 5 * S.E.Δ := by
  unfold early opening Phase.earlyOffset Protocol.proposal_time Env.t slotStart
  ring

private theorem sg_opening_slot_gap (S : Setup V) {p q : Round} (hR : 3 ≤ S.hc.R)
    (h : p < q) : S.hc.opening_slot p + 3 ≤ S.hc.opening_slot q := by
  unfold Protocol.HealConfig.opening_slot
  calc p * S.hc.R + 3 ≤ p * S.hc.R + S.hc.R := Nat.add_le_add_left hR _
    _ = (p + 1) * S.hc.R := by ring
    _ ≤ q * S.hc.R := Nat.mul_le_mul_right _ h

private theorem sg_gap_arith : ∀ d m n : Int, 0 < d → m + 3 ≤ n →
    4 * d * m - d ≤ 4 * d * n - 5 * d := by
  intro d m n hd h
  have hnn : (0 : Int) ≤ 4 * d := by omega
  have h1 : 4 * d * (m + 3) ≤ 4 * d * n := Int.mul_le_mul_of_nonneg_left h hnn
  have h2 : 4 * d * (m + 3) = 4 * d * m + 12 * d := by ring
  omega

/-- A round strictly below `r` closes its whole G2 phase before round `r`'s G2
early cutoff. This is `BoundaryRows.action_delta_le_early` one phase earlier. -/
private theorem sg_domain_le_early (S : Setup V) {p r : Round} (hR : 3 ≤ S.hc.R)
    (h : p < r) : domain S.E S.hc p .g2 ≤ early S.E S.hc r .g2 := by
  have hslot : ((S.hc.opening_slot p : Nat) : Int) + 3 ≤
      ((S.hc.opening_slot r : Nat) : Int) := by
    exact_mod_cast sg_opening_slot_gap S hR h
  rw [sg_domain_eq, sg_early_eq]
  exact sg_gap_arith S.E.Δ _ _ S.E.Δ_pos hslot

private theorem sg_le_add_six : ∀ x d : Int, 0 < d → x ≤ x + 6 * d := by
  intro x d hd; omega

private theorem sg_le_of_add_le : ∀ x d b : Int, 0 < d → x + d ≤ b → x ≤ b := by
  intro x d b hd h; omega

private theorem sg_lt_of_add_le : ∀ x d b : Int, 0 < d → x + d ≤ b → x < b := by
  intro x d b hd h; omega

private theorem sg_deadline_early_arith : ∀ d m n : Int, 0 < d → m + 3 ≤ n →
    4 * d * m + 6 * d + d ≤ 4 * d * n - 5 * d := by
  intro d m n hd h
  have hnn : (0 : Int) ≤ 4 * d := by omega
  have h1 : 4 * d * (m + 3) ≤ 4 * d * n := Int.mul_le_mul_of_nonneg_left h hnn
  have h2 : 4 * d * (m + 3) = 4 * d * m + 12 * d := by ring
  omega

/-- Copied from `BoundaryRows.action_delta_le_early`. -/
private theorem sg_action_delta_le_early (S : Setup V) {q r : Round} (hR : 3 ≤ S.hc.R)
    (hqr : q < r) : S.a q + S.E.Δ ≤ early S.E S.hc r .g2 := by
  have hslot : ((S.hc.opening_slot q : Nat) : Int) + 3 ≤
      ((S.hc.opening_slot r : Nat) : Int) := by
    exact_mod_cast sg_opening_slot_gap S hR hqr
  rw [sg_a_eq, sg_early_eq]
  exact sg_deadline_early_arith S.E.Δ _ _ S.E.Δ_pos hslot

/-- Copied from `BoundaryRows.early_le_domain`. -/
private theorem sg_early_le_domain (S : Setup V) (q : Round) :
    early S.E S.hc q .g2 ≤ domain S.E S.hc q .g2 := by
  change opening S.E S.hc q + (-5) * S.E.Δ ≤ opening S.E S.hc q + (-1) * S.E.Δ
  exact Int.add_le_add_left
    (Int.mul_le_mul_of_nonneg_right (show (-5 : Time) ≤ -1 by decide) S.E.Δ_pos.le) _

/-- Copied from `BoundaryRows.domain_le_opening`. -/
private theorem sg_domain_le_opening (S : Setup V) (q : Round) :
    domain S.E S.hc q .g2 ≤ opening S.E S.hc q := by
  change opening S.E S.hc q + (-1) * S.E.Δ ≤ opening S.E S.hc q
  have hneg : (-1) * S.E.Δ ≤ 0 :=
    Int.mul_nonpos_of_nonpos_of_nonneg (by decide) S.E.Δ_pos.le
  simpa only [add_zero] using Int.add_le_add_left hneg (opening S.E S.hc q)




private theorem sg_domain_g1_eq (S : Setup V) (k : Round) :
    domain S.E S.hc k .g1 = 4 * S.E.Δ * ((S.hc.opening_slot k : Nat) : Int) := by
  unfold domain opening Phase.domainOffset Protocol.proposal_time Env.t slotStart
  ring

private theorem sg_sub_lt_succ : ∀ x d : Int, 0 < d → x - d < x + 1 := by
  intro x d hd; omega

private theorem sg_sub_le_self : ∀ x d : Int, 0 < d → x - d ≤ x := by
  intro x d hd; omega

private theorem sg_succ_le_add_six : ∀ x d : Int, 0 < d → x + 1 ≤ x + 6 * d := by
  intro x d hd; omega



private theorem sg_a_gap_arith : ∀ d m n : Int, 0 < d → m + 3 ≤ n →
    4 * d * m + 6 * d ≤ 4 * d * n := by
  intro d m n hd h
  have hnn : (0 : Int) ≤ 4 * d := by omega
  have h1 : 4 * d * (m + 3) ≤ 4 * d * n := Int.mul_le_mul_of_nonneg_left h hnn
  have h2 : 4 * d * (m + 3) = 4 * d * m + 12 * d := by ring
  omega

/-- Arithmetic core over bare `Int` for the `Δ` grid. -/
private theorem sg_public_gap : ∀ d x y : Int, 0 < d → d * x < d * y → d * x + d ≤ d * y := by
  intro d x y hd h
  have hxy : x < y := by
    by_contra hcon
    exact absurd (Int.mul_le_mul_of_nonneg_left (Int.not_lt.mp hcon) hd.le) (not_le.mpr h)
  have h1 : x + 1 ≤ y := by omega
  calc d * x + d = d * (x + 1) := by ring
    _ ≤ d * y := Int.mul_le_mul_of_nonneg_left h1 hd.le


/-- Addendum 34 17: the outage boundary is a public time
and every action time `Δ(4qR + 6)` is a multiple of `Δ`, so a strict inequality
between them leaves a full delay. Copied from
`Premises.a_add_delta_le_of_lt_public`, which this file must not import. -/
private theorem sg_a_add_delta_le_of_lt_public (S : Setup V) (b0 : Time)
    (hpub : Execution.PublicTime S b0) (q : Round) (h : S.a q < b0) :
    S.a q + S.E.Δ ≤ b0 := by
  obtain ⟨k, hk⟩ := hpub
  have ha : S.a q = S.E.Δ * (4 * ((S.hc.opening_slot q : Nat) : Int) + 6) := by
    rw [sg_a_eq]; ring
  have hb : b0 = S.E.Δ * (k : Int) := by rw [hk]; ring
  rw [ha, hb] at h ⊢
  exact sg_public_gap S.E.Δ _ _ S.E.Δ_pos h

/-- A round strictly below `r` has its whole action before round `r`'s opening:
`a_q = 4Δ·os(q) + 6Δ` and `os(q) + 3 ≤ os(r)` for `R ≥ 3`. This replaces the
horizon step `S.a q ≤ S.a r ≤ rho.horizon`, which `DomainIncluded` does not
supports. -/
private theorem sg_a_le_domain_g1 (S : Setup V) {q r : Round} (hR : 3 ≤ S.hc.R)
    (hqr : q < r) : S.a q ≤ domain S.E S.hc r .g1 := by
  have hslot : ((S.hc.opening_slot q : Nat) : Int) + 3 ≤
      ((S.hc.opening_slot r : Nat) : Int) := by
    exact_mod_cast sg_opening_slot_gap S hR hqr
  rw [sg_a_eq, sg_domain_g1_eq]
  exact sg_a_gap_arith S.E.Δ _ _ S.E.Δ_pos hslot


/-- The round-`r` G2 domain is strictly before the strict cut that realises the
round-`r` opening read. -/
private theorem sg_g2_lt_opening_cut (S : Setup V) (r : Round) :
    domain S.E S.hc r .g2 < domain S.E S.hc r .g1 + 1 := by
  rw [sg_domain_eq, sg_domain_g1_eq]
  exact sg_sub_lt_succ _ _ S.E.Δ_pos

/-- That strict cut is still at or before the round action. -/
private theorem sg_opening_cut_le_a (S : Setup V) (r : Round) :
    domain S.E S.hc r .g1 + 1 ≤ S.a r := by
  rw [sg_domain_g1_eq, sg_a_eq]
  exact sg_succ_le_add_six _ _ S.E.Δ_pos

/-- The round-`r` G2 domain is at or before the opening. -/
private theorem sg_g2_le_domain_g1 (S : Setup V) (r : Round) :
    domain S.E S.hc r .g2 ≤ domain S.E S.hc r .g1 := by
  rw [sg_domain_eq, sg_domain_g1_eq]
  exact sg_sub_le_self _ _ S.E.Δ_pos


omit [DecidableEq V] [Fintype V] in
private theorem sg_sgVote_round (a : NamedAttestation V) :
    (Protocol.sgVote a.erase).round = a.round := rfl

omit [DecidableEq V] [Fintype V] in
private theorem sg_sgVote_confirmed (a : NamedAttestation V) :
    (Protocol.sgVote a.erase).confirmed = a.confirmed := rfl

/-- Copied from `BoundaryRows.mem_retainedRounds`. -/
private theorem sg_mem_retainedRounds (S : Setup V) {sr k : Round}
    (hlo : sr - S.hc.η_SG ≤ k) (hhi : k ≤ sr) :
    k ∈ Internal.OutageEntryRevision.retainedRounds S sr := by
  simp only [Internal.OutageEntryRevision.retainedRounds, Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le hhi, hlo⟩

private theorem sg_delay_absurd : ∀ x d b : Int, 0 < d → x + d ≤ b → b ≤ x → False := by
  intro x d b hd h1 h2; omega

private theorem sg_opening_le_a (S : Setup V) (k : Round) :
    opening S.E S.hc k ≤ S.a k := by
  rw [sg_opening_eq, sg_a_eq]
  exact sg_le_add_six _ _ S.E.Δ_pos

private theorem sg_a_mono (S : Setup V) {p q : Round} (h : p ≤ q) : S.a p ≤ S.a q := by
  have hslot : ((S.hc.opening_slot p : Nat) : Int) ≤
      ((S.hc.opening_slot q : Nat) : Int) := by
    exact_mod_cast Nat.mul_le_mul_right S.hc.R h
  have hmul := Int.mul_le_mul_of_nonneg_left hslot
    (Int.mul_nonneg (show (0 : Int) ≤ 4 by norm_num) S.E.Δ_pos.le)
  rw [sg_a_eq, sg_a_eq]
  exact Int.add_le_add_right hmul _

private theorem sg_margin_arith : ∀ d m k b : Int, 0 < d → m + 3 ≤ k →
    4 * d * k + 2 * d + d ≤ b → 4 * d * m + 6 * d + d ≤ b := by
  intro d m k b hd hmk hb
  have hnn : (0 : Int) ≤ 4 * d := by omega
  have h1 : 4 * d * (m + 3) ≤ 4 * d * k := Int.mul_le_mul_of_nonneg_left hmk hnn
  have h2 : 4 * d * (m + 3) = 4 * d * m + 12 * d := by ring
  omega

/-- Every round at or below the stable round has its healthy action deadline
before the outage. `Proofs.NamedSGArrival.formation_margin_action_deadline` at `q = s`,
carried down by monotonicity of the schedule. -/
private theorem sg_action_deadline (S : Setup V) (b0 : Time) (s q : Round)
    (hR : 3 ≤ S.hc.R) (hmargin : FormationMargin S s b0) (hq : q ≤ s) :
    S.a q + S.E.Δ ≤ b0 := by
  have hslot : ((S.hc.opening_slot q : Nat) : Int) + 3 ≤
      ((S.hc.opening_slot (s + 1) : Nat) : Int) := by
    exact_mod_cast sg_opening_slot_gap S hR (Nat.lt_succ_of_le hq)
  have hmar : 4 * S.E.Δ * ((S.hc.opening_slot (s + 1) : Nat) : Int) +
      2 * S.E.Δ + S.E.Δ ≤ b0 := by
    replace hmargin := old_margin_of_new S s b0 hmargin
    rw [sg_formation_eq] at hmargin
    exact hmargin
  rw [sg_a_eq]
  exact sg_margin_arith S.E.Δ _ _ b0 S.E.Δ_pos hslot hmar

/-- The stable round is strictly below every included round. -/
private theorem sg_stable_lt_round (S : Setup V) (b0 : Time) (s r : Round)
    (hR : 3 ≤ S.hc.R) (hmargin : FormationMargin S s b0) (har : b0 ≤ S.a r) : s < r := by
  by_contra hcon
  have hdead := sg_action_deadline S b0 s r hR hmargin (Nat.le_of_not_lt hcon)
  exact sg_delay_absurd _ _ _ S.E.Δ_pos hdead har

/-! ## 6c. Bucket rounds and the strict-read traceback (private copies)

This module must not import the collaboration files that already carry this
machinery (`RowTrace.lean`, `RetainedRows.lean`, `BoundaryRows.lean`,
`Inclusions.lean`, `SupportCarry.lean`): they are edited concurrently. The
block below repeats, privately and unchanged apart from the `sg_` prefix, the
parts of `NamedRawSource`, `NamedHealthyHeadReady`, `NamedClockUniform` and
`NamedOutageInputs` whose originals are `private`. No new protocol content. -/

/-- Copied from `NamedRawSource`. -/
private def SGRowsOwn (st : Protocol.NamedStore V) : Prop :=
  ∀ k (a : NamedAttestation V), a ∈ st.sg_rows k → a.round = k

omit [Fintype V] in
/-- Copied from `NamedRawSource`. -/
private theorem sg_row_mem_cases_at (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (incoming a : NamedAttestation V) (k : Round)
    (ha : a ∈ (Protocol.NamedAdmission.admit_row hc st incoming).sg_rows k) :
    a ∈ st.sg_rows k ∨ (a = incoming ∧ k = incoming.round) := by
  dsimp only [Protocol.NamedAdmission.admit_row] at ha
  split_ifs at ha <;> aesop

omit [Fintype V] in
/-- Copied from `NamedRawSource`. -/
private theorem sg_row_own (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (incoming : NamedAttestation V) (h : SGRowsOwn st) :
    SGRowsOwn (Protocol.NamedAdmission.admit_row hc st incoming) := by
  intro k a ha
  rcases sg_row_mem_cases_at hc st incoming a k ha with hold | ⟨rfl, rfl⟩
  · exact h k a hold
  · rfl

omit [Fintype V] in
/-- Copied from `NamedRawSource`. -/
private theorem sg_rows_own (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) (h : SGRowsOwn st) :
    SGRowsOwn (Protocol.NamedAdmission.admit_rows hc st rows) := by
  induction rows generalizing st with
  | nil => exact h
  | cons a rows ih => exact ih _ (sg_row_own hc st a h)

/-- Copied from `NamedRawSource`. -/
private theorem sg_core_block_rows (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) :
    (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).sg_rows = st.sg_rows := by
  unfold Protocol.NamedStore.process_block_core
  split_ifs
  · exact NamedStore.commit_rows st _ B
  · rfl

/-- Copied from `NamedRawSource`. -/
private theorem sg_block_own (S : Setup V) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (h : SGRowsOwn st) :
    SGRowsOwn (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B) := by
  have hc : SGRowsOwn (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B) := by
    simpa only [SGRowsOwn, sg_core_block_rows] using h
  unfold Protocol.NamedAdmission.on_block_with Protocol.NamedAdmission.admit_carried
  split_ifs
  · exact sg_rows_own S.hc _ B.attestations hc
  · exact hc

/-- Copied from `NamedRawSource`. -/
private theorem sg_propose_own (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (h : SGRowsOwn st) :
    SGRowsOwn (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1 := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact h
  · exact sg_block_own S st _ h

/-- Copied from `NamedRawSource`. -/
private theorem sg_tick_preserves_own (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (t : Time) (P : Protocol.NamedStore V → Prop)
    (hclock : ∀ st, P st → P (Protocol.NamedStore.setClock S.E st t))
    (hprop : ∀ st, P st →
      P (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1)
    (hgf : ∀ st, P st →
      P (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st).1)
    (hconf : ∀ st s, P st →
      P (Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st s))
    (hatt : ∀ st record, P st →
      P (Protocol.NamedDuties.attest_with gc S.E S.hc nd st record).1)
    (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (h : P st) :
    P (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 := by
  rw [NamedTick.tick_computed_duties]
  dsimp only
  split_ifs <;> solve_by_elim (maxDepth := 10) [hclock, hprop, hgf, hconf, hatt]

/-- Copied from `NamedRawSource`. -/
private theorem sg_tick_own (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord)
    (t : Time) (h : SGRowsOwn st) :
    SGRowsOwn (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 := by
  have hclock : ∀ st, SGRowsOwn st →
      SGRowsOwn (Protocol.NamedStore.setClock S.E st t) := fun _ hs => hs
  have hprop : ∀ st, SGRowsOwn st →
      SGRowsOwn (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1 :=
    sg_propose_own gc S nd
  have hgf : ∀ st, SGRowsOwn st →
      SGRowsOwn (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st).1 :=
    fun _ hs => hs
  have hconf : ∀ st s, SGRowsOwn st →
      SGRowsOwn (Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st s) :=
    fun _ _ hs => hs
  have hatt : ∀ st record, SGRowsOwn st →
      SGRowsOwn (Protocol.NamedDuties.attest_with gc S.E S.hc nd st record).1 :=
    fun st record hs => sg_row_own S.hc st _ hs
  exact sg_tick_preserves_own gc S nd t SGRowsOwn hclock hprop hgf hconf hatt st record h

/-- Copied from `NamedRawSource`. -/
private theorem sg_process_own (S : Setup V) (st : Protocol.NamedStore V) (o : NamedObject V)
    (h : SGRowsOwn st) : SGRowsOwn (NamedReceipt.process S st o) := by
  cases o with
  | block B => exact sg_block_own S st B h
  | gfVote u => exact h
  | attest a => exact sg_row_own S.hc st a h

/-- Copied from `NamedRawSource`. -/
private theorem sg_own_stateBefore (S : Setup V) (rho : NamedRun V) (i : Nat) (reader : V) :
    SGRowsOwn (NamedRun.stateBefore S rho i reader).st := by
  induction i with
  | zero =>
    intro k a ha
    simp only [Proofs.NamedRuntime.stateBefore_zero, NamedWorld.init, NamedNode.initial,
      Protocol.NamedStore.initial, List.not_mem_nil] at ha
  | succ i ih =>
    rw [Proofs.NamedRuntime.stateBefore_succ]
    cases he : rho.events[i]? with
    | none => exact ih
    | some e =>
      change SGRowsOwn (NamedWorld.step S (NamedRun.stateBefore S rho i) e reader).st
      by_cases hv : reader = e.node
      · cases e with
        | tick v t =>
          change reader = v at hv
          subst v
          rw [Proofs.NamedRuntime.step_tick]
          exact sg_tick_own _ S (S.node reader) _ _ t ih
        | deliver v o t =>
          change reader = v at hv
          subst v
          rw [Proofs.NamedRuntime.step_deliver]
          exact sg_process_own S _ o ih
      · rw [Proofs.NamedRuntime.step_other S _ e reader hv]
        exact ih

/-- Copied from `NamedRawSource`: a held row sits in its own bucket at any
strict read. -/
private theorem sg_own_strict_read (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (read : Time) (reader : V) :
    ∀ k (a : NamedAttestation V),
      a ∈ (NamedRun.stateBeforeTime S rho read reader).st.sg_rows k → a.round = k := by
  obtain ⟨n, hn, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho sch.sorted read
  rw [hn]
  exact sg_own_stateBefore S rho n reader

omit [DecidableEq V] [Fintype V] in
/-- Copied from `NamedHealthyHeadReady`. -/
private theorem sg_time_le_of_key_le {e f : NamedEvent V} (h : e.key ≤ f.key) :
    e.time ≤ f.time := by
  rcases Prod.Lex.le_iff.mp h with hlt | ⟨heq, _⟩
  · exact hlt.le
  · exact heq.le

omit [DecidableEq V] [Fintype V] in
/-- Copied from `NamedHealthyHeadReady`. -/
private theorem sg_strict_filter_eq_take (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (cut : Time) :
    rho.events.filter (fun e => decide (e.time < cut)) =
      rho.events.take (rho.events.filter (fun e => decide (e.time < cut))).length := by
  have hdown : ∀ e f : NamedEvent V, e.key ≤ f.key →
      decide (f.time < cut) = true → decide (e.time < cut) = true := by
    intro e f hkey hf
    simp only [decide_eq_true_eq] at hf ⊢
    exact (sg_time_le_of_key_le hkey).trans_lt hf
  refine List.prefix_iff_eq_take.mp ?_
  rw [Proofs.Bridges.filter_eq_takeWhile_of_pairwise hdown _ hsorted]
  exact List.takeWhile_prefix _

/-- Copied from `NamedHealthyHeadReady`. -/
private theorem sg_strict_read_eq_index (S : Setup V) (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (t : Time) :
    NamedRun.stateBeforeTime S rho t =
      NamedRun.stateBefore S rho (rho.events.filter (fun e => decide (e.time < t))).length :=
  congrArg (fun events => events.foldl (NamedWorld.step S) NamedWorld.init)
    (sg_strict_filter_eq_take rho hsorted t)

omit [DecidableEq V] [Fintype V] in
/-- Copied from `NamedHealthyHeadReady`. -/
private theorem sg_strict_lengths_mono (rho : NamedRun V) {c d : Time} (ht : c ≤ d) :
    (rho.events.filter (fun e => decide (e.time < c))).length ≤
      (rho.events.filter (fun e => decide (e.time < d))).length := by
  have hsub := List.Sublist.filter (fun e : NamedEvent V => decide (e.time < d))
    (List.filter_sublist (p := fun e : NamedEvent V => decide (e.time < c)) (l := rho.events))
  have hs : (rho.events.filter (fun e => decide (e.time < c))).filter
      (fun e => decide (e.time < d)) = rho.events.filter (fun e => decide (e.time < c)) := by
    apply List.filter_eq_self.mpr
    intro e he
    have hc : e.time < c := by
      simpa only [decide_eq_true_eq] using (List.mem_filter.mp he).2
    simpa only [decide_eq_true_eq] using hc.trans_le ht
  rw [hs] at hsub
  exact hsub.length_le

/-- Time-monotone carry of a held SG row and its projection stamp. -/
private theorem sg_strict_sg_row_carry (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (reader : V) {c d : Time} (hcd : c ≤ d)
    {a : NamedAttestation V}
    (ha : a ∈ (NamedRun.stateBeforeTime S rho c reader).st.sg_rows a.round) :
    a ∈ (NamedRun.stateBeforeTime S rho d reader).st.sg_rows a.round ∧
      (NamedRun.stateBeforeTime S rho d reader).st.core.timestamp_sg_vote
          (Protocol.sgVote a.erase) =
        (NamedRun.stateBeforeTime S rho c reader).st.core.timestamp_sg_vote
          (Protocol.sgVote a.erase) := by
  rw [sg_strict_read_eq_index S rho sch.sorted c] at ha
  rw [sg_strict_read_eq_index S rho sch.sorted c, sg_strict_read_eq_index S rho sch.sorted d]
  exact Proofs.NamedSGArrival.stateBefore_sg_row_stamp_mono S rho reader
    (sg_strict_lengths_mono rho hcd) ha

/-- Time-monotone carry of a held body and its block stamp. -/
private theorem sg_strict_body_carry (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (reader : V) {c d : Time} (hcd : c ≤ d)
    {B : NamedBlock V} (hB : B ∈ (NamedRun.stateBeforeTime S rho c reader).st.bodies) :
    B ∈ (NamedRun.stateBeforeTime S rho d reader).st.bodies ∧
      (NamedRun.stateBeforeTime S rho d reader).st.core.timestamp_block B.erase =
        (NamedRun.stateBeforeTime S rho c reader).st.core.timestamp_block B.erase := by
  rw [sg_strict_read_eq_index S rho sch.sorted c] at hB
  rw [sg_strict_read_eq_index S rho sch.sorted c, sg_strict_read_eq_index S rho sch.sorted d]
  exact NamedBlockStamp.stateBefore_body_stamp_mono S rho reader
    (sg_strict_lengths_mono rho hcd) hB

/-- Time-monotone growth of the finalized prefix at a named strict read. Same
index bridge as the two carries above, over `Proofs.NamedRuntime.stateBefore_F_mono`. -/
private theorem sg_strict_F_mono (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (reader : V) {c d : Time} (hcd : c ≤ d) :
    Block.Preceq (NamedRun.stateBeforeTime S rho c reader).st.core.F
      (NamedRun.stateBeforeTime S rho d reader).st.core.F := by
  rw [sg_strict_read_eq_index S rho sch.sorted c, sg_strict_read_eq_index S rho sch.sorted d]
  exact Proofs.NamedRuntime.stateBefore_F_mono S rho reader (sg_strict_lengths_mono rho hcd)

/-- Copied from `NamedHealthyHeadReady`. -/
private theorem sg_held_find_at_strict (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (roots : NamedRootCollisionFree S rho)
    (reader : V) (hreader : reader ∈ rho.honest) (t : Time) (H : NamedBlock V)
    (hH : H ∈ (NamedRun.stateBeforeTime S rho t reader).st.bodies) :
    Block.find? (NamedRun.stateBeforeTime S rho t reader).st.core.T H.erase.root =
      some H.erase := by
  obtain ⟨n, hread, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho sch.sorted t
  rw [hread] at hH ⊢
  have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho n reader).1.1.1
  have hHscope := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hreader n hH)
  have hHraw : H.erase ∈ (NamedRun.stateBefore S rho n reader).st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hH
  apply Proofs.Optimistic.find?_eq_some_of_unique hHraw
  intro raw hraw hroot
  rw [hcoh.1] at hraw
  obtain ⟨other, hother, rfl⟩ := Finset.mem_image.mp hraw
  have hotherScope := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hreader n hother)
  have hroots : other.root = H.root :=
    (Proofs.NamedWire.erase_root other).symm.trans (hroot.trans (Proofs.NamedWire.erase_root H))
  have hself : ∀ B : NamedBlock V, NamedBlock.Preceq B B := by
    intro B; cases B <;> simp [NamedBlock.Preceq, NamedBlock.preceq]
  exact congrArg NamedBlock.erase (roots.root_injective other H hotherScope hHscope other H
    (Or.inl (hself other)) (Or.inr (hself H)) hroots)

/-- Copied from `RowTrace.lean`: a pooled SG token at a strict read comes from
an original full row held at that read, in its own bucket. -/
private theorem sg_pool_token_row (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (cut : Time) (reader : V)
    {k : Round} {x : Protocol.SGVote V}
    (hx : x ∈
      (NamedRun.stateBeforeTime S rho cut reader).st.core.toHealing.gradeView.sg_votes k) :
    ∃ a : NamedAttestation V, a.round = k ∧ Protocol.sgVote a.erase = x ∧
      a ∈ (NamedRun.stateBeforeTime S rho cut reader).st.sg_rows a.round := by
  let n := NamedRun.stateBeforeTime S rho cut reader
  change x ∈ (n.st.core.sg_pool k).image Protocol.sgVote at hx
  obtain ⟨erased, herased, hproj⟩ := Finset.mem_image.mp hx
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg n.st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho cut reader).1.1.1
  change erased ∈ (n.st.core.sg_votes k).toFinset at herased
  rw [hcoh.2.2.2.1 k] at herased
  obtain ⟨a, ha, herase⟩ := List.mem_map.mp (List.mem_toFinset.mp herased)
  have hround : a.round = k := sg_own_strict_read S rho sch cut reader k a ha
  exact ⟨a, hround, (congrArg Protocol.sgVote herase).trans hproj,
    by simpa only [hround] using ha⟩

/-- Copied from `RowTrace.lean`: an honest sender's row held at a strict read
was emitted at that round's action, strictly before the read. -/
private theorem sg_honest_held_row_before_cut (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (auth : NamedUnforgeable S rho)
    (cut : Time) (reader : V) {a : NamedAttestation V}
    (ha : a ∈ (NamedRun.stateBeforeTime S rho cut reader).st.sg_rows a.round)
    (hHon : a.val_index ∈ rho.honest) :
    S.a a.round < cut ∧ NamedRun.emits S rho a.val_index (.attest a) (S.a a.round) := by
  obtain ⟨i, hread, hbefore⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho sch.sorted cut
  rw [hread] at ha
  obtain ⟨j, hj, t, hacc, hsend, hem⟩ :=
    NamedOutageProvenance.honest_held_row_emission S rho auth i reader ha hHon
  obtain ⟨e, he, _, het⟩ := hacc.1.2
  have ht : t < cut := by simpa only [het] using hbefore j e hj he
  exact ⟨lt_of_le_of_lt hsend ht, hem⟩

/-! ## 6d. Window membership and the clock at the inventory time -/

private theorem sg_window_witness : ∀ eta r k : Nat, r - eta ≤ k → k < r →
    k - (r - eta) < min r eta ∧ k = r - eta + (k - (r - eta)) := by
  intro eta r k h1 h2
  exact ⟨by omega, by omega⟩

/-- Copied from `NamedOutageInputs`. -/
private theorem sg_mem_latest_window {eta r k : Round} (hlo : r - eta ≤ k) (hhi : k < r) :
    k ∈ Protocol.latest_window eta r := by
  simp only [Protocol.latest_window, List.mem_range', Nat.one_mul]
  exact ⟨k - (r - eta), (sg_window_witness eta r k hlo hhi).1,
    (sg_window_witness eta r k hlo hhi).2⟩

/-- Copied from `NamedOutageInputs`. -/
private theorem sg_window_bounds {eta r k : Nat} (hk : k ∈ Protocol.latest_window eta r) :
    r - eta ≤ k ∧ k < r := by
  simp only [Protocol.latest_window, List.mem_range', Nat.one_mul] at hk
  obtain ⟨i, hi, heq⟩ := hk
  omega

private theorem sg_no_gap : ∀ A B d : Int, 0 < d → B ≤ A →
    ¬ (A + 6 * d ≤ B - 5 * d) := by
  intro A B d hd hopen h
  omega

/-- Copied from `Inclusions.lean`: an action time at or before round `q`'s G2
early cutoff forces the round strictly below `q`. -/
private theorem sg_round_lt_of_a_le_early (S : Setup V) {r q : Round}
    (h : S.a r ≤ early S.E S.hc q .g2) : r < q := by
  by_contra hcon
  have hslot : S.hc.opening_slot q ≤ S.hc.opening_slot r :=
    Nat.mul_le_mul_right _ (Nat.le_of_not_lt hcon)
  have hopen : Protocol.proposal_time S.E (S.hc.opening_slot q) ≤
      Protocol.proposal_time S.E (S.hc.opening_slot r) :=
    Protocol.proposal_time_mono S.E hslot
  have hearly : early S.E S.hc q .g2 =
      Protocol.proposal_time S.E (S.hc.opening_slot q) - 5 * S.E.Δ := by
    simp only [early, opening, Phase.earlyOffset]
    ring
  have ha : S.a r = Protocol.proposal_time S.E (S.hc.opening_slot r) + 6 * S.E.Δ := by
    simp only [Setup.a, Protocol.HealConfig.a, Protocol.proposal_time, Env.t]
  rw [hearly, ha] at h
  exact sg_no_gap _ _ _ S.E.Δ_pos hopen h

/-- Copied from `NamedClockUniform`. -/
private theorem sg_tick_mem_le_strict_clock (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) {cut : Time} {reader : V} {t : Time}
    (htick : NamedEvent.tick reader t ∈
      rho.events.filter (fun e => decide (e.time < cut))) :
    t ≤ (NamedRun.stateBeforeTime S rho cut reader).st.core.t := by
  let filtered := rho.events.filter (fun e => decide (e.time < cut))
  let filteredRun : NamedRun V := { rho with events := filtered }
  have hsorted : filtered.Pairwise (fun e f => e.key ≤ f.key) := by
    simpa only [filtered] using sch.sorted.filter (fun e => decide (e.time < cut))
  have hnonneg : ∀ e ∈ filteredRun.events, 0 ≤ e.time := by
    intro e he
    change e ∈ filtered at he
    exact (sch.in_horizon e (List.mem_filter.mp he).1).1
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp htick
  have hiLen : i < filtered.length := (List.getElem?_eq_some_iff.mp hi).1
  have hle := Proofs.NamedRuntime.tick_time_le_clock S filteredRun hsorted hnonneg hi hiLen
  simpa only [filteredRun, filtered, NamedRun.stateBeforeTime, NamedRun.stateBefore,
    List.take_length] using hle

/-- Copied from `SupportCarry.lean`. -/
private theorem sg_round_of_mono (hc : Protocol.HealConfig) {c d : Slot} (h : c ≤ d) :
    hc.round_of c ≤ hc.round_of d :=
  Nat.div_le_div_right h

/-- Copied from `SupportCarry.lean`. -/
private theorem sg_round_of_opening (hc : Protocol.HealConfig) (r : Round) :
    hc.round_of (hc.opening_slot r) = r := by
  have hR : 0 < hc.R := lt_of_lt_of_le (by norm_num) hc.R_ge_two
  simp only [Protocol.HealConfig.round_of, Protocol.HealConfig.opening_slot]
  exact Nat.mul_div_cancel _ hR

/-- Copied from `NamedClockUniform`. -/
private theorem sg_stateBefore_slot_clock (S : Setup V) (rho : NamedRun V)
    (i : Nat) (reader : V) :
    (NamedRun.stateBefore S rho i reader).st.core.s =
      S.E.slotOf (NamedRun.stateBefore S rho i reader).st.core.t := by
  induction i with
  | zero =>
      simp [Proofs.NamedRuntime.stateBefore_zero, NamedWorld.init, NamedNode.initial,
        Protocol.NamedStore.initial, Protocol.Store.init, Env.slotOf, slotOfTime]
  | succ i ih =>
      rw [Proofs.NamedRuntime.stateBefore_succ]
      cases he : rho.events[i]? with
      | none => simpa only [Option.toList_none, List.foldl_nil] using ih
      | some e =>
          change (NamedWorld.step S (NamedRun.stateBefore S rho i) e reader).st.core.s =
            S.E.slotOf
              (NamedWorld.step S (NamedRun.stateBefore S rho i) e reader).st.core.t
          by_cases hv : e.node = reader
          · cases e with
            | tick v t =>
                change v = reader at hv
                subst v
                rw [Proofs.NamedRuntime.step_tick]
                rw [(Proofs.NamedNode.tick_clock S reader _ t).1,
                  (Proofs.NamedNode.tick_clock S reader _ t).2]
            | deliver v o t =>
                change v = reader at hv
                subst v
                rw [Proofs.NamedRuntime.step_deliver]
                rw [(Proofs.NamedNode.process_clock S _ o).1,
                  (Proofs.NamedNode.process_clock S _ o).2]
                exact ih
          · rw [Proofs.NamedRuntime.step_other S _ e reader (Ne.symm hv)]
            exact ih

/-- Copied from `NamedClockUniform`. -/
private theorem sg_stateBeforeTime_slot_clock (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (cut : Time) (reader : V) :
    (NamedRun.stateBeforeTime S rho cut reader).st.core.s =
      S.E.slotOf (NamedRun.stateBeforeTime S rho cut reader).st.core.t := by
  obtain ⟨i, hread, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho sch.sorted cut
  rw [hread]
  exact sg_stateBefore_slot_clock S rho i reader

/-- **The clock at the inventory time has entered every already-acted round.**
Every honest node ticks at the public time `S.a q`; if that tick is strictly
before the cut, the strict read's clock is at or past it, so its round is at
least `q`. This is what puts a traced row's round inside `retainedRounds`. -/
private theorem sg_round_le_clock_round (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (cut : Time) (reader : V)
    (hreader : reader ∈ rho.honest) (q : Round) (hq : S.a q < cut)
    (hhor : S.a q ≤ rho.horizon) :
    q ≤ S.hc.round_of (NamedRun.stateBeforeTime S rho cut reader).st.core.s := by
  have hpublic : PublicTime S (S.a q) := by
    refine ⟨4 * S.hc.opening_slot q + 6, ?_⟩
    rw [sg_a_eq]
    push_cast
    ring
  have hnonneg : (0 : Time) ≤ S.a q :=
    (Proofs.Optimistic.proposal_time_nonneg S.E (S.hc.opening_slot q)).trans (sg_opening_le_a S q)
  have htick : NamedEvent.tick reader (S.a q) ∈ rho.events :=
    sch.tick_total reader hreader (S.a q) hpublic hnonneg hhor
  have hfiltered : NamedEvent.tick reader (S.a q) ∈
      rho.events.filter (fun e => decide (e.time < cut)) :=
    List.mem_filter.mpr ⟨htick, by simpa only [NamedEvent.time, decide_eq_true_eq] using hq⟩
  have hclock : S.a q ≤ (NamedRun.stateBeforeTime S rho cut reader).st.core.t :=
    sg_tick_mem_le_strict_clock S rho sch hfiltered
  have hslot : S.hc.opening_slot q ≤
      S.E.slotOf (NamedRun.stateBeforeTime S rho cut reader).st.core.t :=
    Protocol.slot_le_slotOf_of_proposal_time_le S.E ((sg_opening_le_a S q).trans hclock)
  have hmono := sg_round_of_mono S.hc hslot
  rw [sg_round_of_opening] at hmono
  simpa only [sg_stateBeforeTime_slot_clock S rho sch cut reader] using hmono

/-! ## 6c. The round opening read

`NamedRun.readAt S rho t` keeps every event with `e.time ≤ t`, so it is the
strict fold at `t + 1`. The bridge is private in `NonInterference.lean` and so
is not importable; the copy below is verbatim. The two clock-bound helpers are
copies of the private helpers of the same names in `NamedRuntime` and
`CommonSupportBase`. -/

/-- Copy of the private `readAt_eq_stateBeforeTime_succ` of `NonInterference`. -/
private theorem sg_readAt_eq_succ (S : Setup V) (rho : NamedRun V) (t : Time) :
    NamedRun.readAt S rho t = NamedRun.stateBeforeTime S rho (t + 1) := by
  have hp : (fun e : NamedEvent V => decide (e.time ≤ t)) =
      fun e : NamedEvent V => decide (e.time < t + 1) := by
    funext e
    exact decide_eq_decide.mpr Int.lt_add_one_iff.symm
  unfold NamedRun.readAt NamedRun.stateBeforeTime
  rw [hp]




/-! ## 7. The certificate makes the protected prefix graded at every needing reader -/

local instance sgNeedsDecidable (S : Setup V) (rho : NamedRun V) (P : NamedBlock V)
    (r : Round) (v : V) : Decidable (NeedsSG S rho P r v) :=
  inferInstanceAs (Decidable (¬ Block.Preceq P.erase
    (NamedRun.readAt S rho (domain S.E S.hc r .g1) v).st.core.F))

/-- Every common supporter is positive for the protected prefix at the round-`r`
G2 phase read of any reader that still needs the grade. This is clause 4 of
`commonSupporters`, instantiated at that reader. -/
private theorem sg_supporters_positive (S : Setup V) (rho : NamedRun V)
    (supportBoundary : Time) (Pn : NamedBlock V) (supportRound r : Round)
    {v : V} (hv : v ∈ rho.honest) (hneed : NeedsSG S rho Pn r v) :
    commonSupporters S rho supportBoundary Pn supportRound r ⊆
      Finset.univ.filter fun u => positive
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.F
        S.hc.η_SG r (early S.E S.hc r .g2) (late S.E S.hc r .g2) u Pn.erase = true := by
  intro u hu
  have hclauses := (Finset.mem_filter.mp hu).2 v hv hneed
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ u, hclauses.2.2.2⟩

/-! ## 7b. The opposition containment, proved

The two stage-1 premises. `SGHonestConfirmedAbove` is the local twin of the
selection definition `Internal.NamedStableChainOutage.HonestConfirmedAbove`: that
name does **not** exist in the production tree yet, and `Premises.lean`, which
carries the same body, is edited concurrently and must not be imported here. -/

/-- Honest pre-outage SG votes from rounds at or above the stable round confirm
above the protected prefix. -/
def SGHonestConfirmedAtOrAbove (S : Setup V) (rho : NamedRun V) (b0 : Time) (s : Round)
    (P : Block V) : Prop :=
  ∀ (a : NamedAttestation V) (t : Time), a.val_index ∈ rho.honest →
    NamedRun.emits S rho a.val_index (.attest a) t → t < b0 → s ≤ a.round →
    ∀ key, a.confirmed = some key →
      ∀ K : NamedBlock V, NamedRun.blockInRun S rho K → K.root = key →
        Block.Preceq P K.erase


/-- The reader-side companion: the confirmed head is held, finality-compatible
and stamped at every honest reader from one delay after the sender's action
onwards. Addendum 34 17: the emission margin is
`t + Δ ≤ b0`, the read is at `t + Δ` or later, and the clause is guarded by
`F(cut) ⪯ P`, which every consumer gets from `NeedsSG`. -/
def SGHonestHeadHeldAbove (S : Setup V) (rho : NamedRun V) (b0 : Time) (s : Round)
    (P : Block V) : Prop :=
  ∀ (a : NamedAttestation V) (t : Time), a.val_index ∈ rho.honest →
    NamedRun.emits S rho a.val_index (.attest a) t → t + S.E.Δ ≤ b0 → s ≤ a.round →
    ∀ reader ∈ rho.honest, ∀ cut : Time, t + S.E.Δ ≤ cut →
      Block.Preceq (NamedRun.stateBeforeTime S rho cut reader).st.core.F P →
      ∀ key, a.confirmed = some key →
        ∃ H : NamedBlock V,
          H ∈ (NamedRun.stateBeforeTime S rho cut reader).st.bodies ∧ H.root = key ∧
          Block.compatible H.erase
            (NamedRun.stateBeforeTime S rho cut reader).st.core.F = true ∧
          ∀ gamma : Time, t + S.E.Δ ≤ gamma →
            stampedBefore (NamedRun.stateBeforeTime S rho cut reader).st.core.timestamp_block
              gamma H.erase = true


/-- The stage-1 premise: the conjunction of the sender-side
and the reader-side clause at the same stable round. -/
def SGHonestConfirmedAbove (S : Setup V) (rho : NamedRun V) (b0 : Time) (s : Round)
    (P : Block V) : Prop :=
  SGHonestConfirmedAtOrAbove S rho b0 s P ∧ SGHonestHeadHeldAbove S rho b0 s P

/-- Traceback from a raw phase input of an honest sender. Copied from
`BoundaryRows.rawInputs_trace`, with the held row kept in the conclusion. -/
private theorem sg_rawInputs_trace (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (auth : NamedUnforgeable S rho)
    (cut cutoff : Time) (reader : V) (eta r : Round) (u : V) (hu : u ∈ rho.honest)
    {y : Protocol.SGVote V}
    (hy : y ∈ DecoupledConsensusModel.Protocol.rawInputs
      (NamedRun.stateBeforeTime S rho cut reader).st.core.toHealing.gradeView eta r cutoff u) :
    ∃ a : NamedAttestation V, a.val_index = u ∧ a.round = y.round ∧
      Protocol.sgVote a.erase = y ∧ y.round ∈ Protocol.latest_window eta r ∧
      S.a a.round < cut ∧ NamedRun.emits S rho u (.attest a) (S.a a.round) := by
  obtain ⟨hpool, hfields⟩ := Finset.mem_filter.mp hy
  obtain ⟨k, hk, hyk⟩ := Finset.mem_biUnion.mp hpool
  obtain ⟨a, hround, hproj, hmem⟩ := sg_pool_token_row S rho sch cut reader hyk
  have hyround : y.round = a.round := by rw [← hproj, sg_sgVote_round]
  have hval : a.val_index = u := by
    have hvy : y.val_index = u := hfields.1
    rw [← hproj] at hvy
    exact hvy
  subst hval
  obtain ⟨hlt, hem⟩ := sg_honest_held_row_before_cut S rho sch auth cut reader hmem hu
  exact ⟨a, rfl, hyround.symm, hproj,
    by rw [hyround, hround]; exact List.mem_toFinset.mp hk, hlt, hem⟩

/-- Traceback from a retained raw row. Copied from `RetainedRows.retained_trace`,
with the held row kept in the conclusion. -/
private theorem sg_retained_trace (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (auth : NamedUnforgeable S rho)
    (cut : Time) (reader : V) (sr : Round) (u : V) (hu : u ∈ rho.honest)
    {x : Protocol.SGVote V}
    (hx : x ∈ Internal.OutageEntryRevision.retainedRaw S
      (NamedRun.stateBeforeTime S rho cut reader).st.core sr cut u) :
    ∃ a : NamedAttestation V, a.val_index = u ∧ a.round = x.round ∧
      Protocol.sgVote a.erase = x ∧ S.a a.round < cut ∧
      NamedRun.emits S rho u (.attest a) (S.a a.round) ∧
      a ∈ (NamedRun.stateBeforeTime S rho cut reader).st.sg_rows a.round := by
  obtain ⟨hpool, hfields⟩ := Finset.mem_filter.mp hx
  obtain ⟨k, hk, hxk⟩ := Finset.mem_biUnion.mp hpool
  obtain ⟨a, hround, hproj, hmem⟩ := sg_pool_token_row S rho sch cut reader hxk
  have hxround : x.round = a.round := by rw [← hproj, sg_sgVote_round]
  have hval : a.val_index = u := by
    have hvx : x.val_index = u := hfields.1
    rw [← hproj] at hvx
    exact hvx
  subst hval
  obtain ⟨hlt, hem⟩ := sg_honest_held_row_before_cut S rho sch auth cut reader hmem hu
  exact ⟨a, rfl, hxround.symm, hproj, hlt, hem, hmem⟩

/-- A resolved root at an honest reader's strict read names a body the reader
holds. -/
private theorem sg_find_named_at_strict (S : Setup V) (rho : NamedRun V)
    (t : Time) (reader : V) {key : BlockId} {Hb : Block V}
    (hfind : Block.find? (NamedRun.stateBeforeTime S rho t reader).st.core.T key = some Hb) :
    ∃ H : NamedBlock V, H ∈ (NamedRun.stateBeforeTime S rho t reader).st.bodies ∧
      H.erase = Hb ∧ H.root = key := by
  have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t reader).1.1.1
  have hmem : Hb ∈ (NamedRun.stateBeforeTime S rho t reader).st.core.T :=
    Proofs.HealingLemmas.find?_mem hfind
  rw [hcoh.1] at hmem
  obtain ⟨H, hH, hHe⟩ := Finset.mem_image.mp hmem
  refine ⟨H, hH, hHe, ?_⟩
  rw [← Proofs.NamedWire.erase_root H, hHe]
  exact Proofs.HealingLemmas.find?_root hfind

private theorem sg_held_blockInRun (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (reader : V) (hreader : reader ∈ rho.honest)
    (t : Time) {H : NamedBlock V}
    (hH : H ∈ (NamedRun.stateBeforeTime S rho t reader).st.bodies) :
    NamedRun.blockInRun S rho H := by
  obtain ⟨n, hread, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho sch.sorted t
  rw [hread] at hH
  exact Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hreader n hH)

/-- **A row that covers at the inventory time still covers at the later phase
read.** The head is a body the reader already held, bodies survive, and root
collision freedom makes the later lookup return that same body. -/
private theorem sg_covers_transfer (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (roots : NamedRootCollisionFree S rho)
    (reader : V) (hreader : reader ∈ rho.honest) {c d : Time} (hcd : c ≤ d)
    (P : Block V) {y : Protocol.SGVote V}
    (hy : Internal.OutageEntryRevision.covers
      (NamedRun.stateBeforeTime S rho c reader).st.core P y = true) :
    localCovers (NamedRun.stateBeforeTime S rho d reader).st.core.toHealing.gradeView
      y.confirmed P = true := by
  unfold Internal.OutageEntryRevision.covers at hy
  rcases Option.eq_none_or_eq_some y.confirmed with hk | ⟨key, hk⟩
  · rw [hk] at hy
    exact absurd hy (by simp)
  · rw [hk] at hy
    dsimp only [Option.bind] at hy
    cases hf : Block.find? (NamedRun.stateBeforeTime S rho c reader).st.core.T key with
    | none =>
      rw [hf] at hy
      exact absurd hy (by simp)
    | some B =>
      rw [hf] at hy
      obtain ⟨H, hH, hHe, hHroot⟩ := sg_find_named_at_strict S rho c reader hf
      obtain ⟨hHd, -⟩ := sg_strict_body_carry S rho sch reader hcd hH
      have hfind := sg_held_find_at_strict S rho sch roots reader hreader d H hHd
      have hfind' : Block.find? (NamedRun.stateBeforeTime S rho d reader).st.core.T key
          = some B := by
        rw [← hHroot, ← Proofs.NamedWire.erase_root H, hfind, hHe]
      change Protocol.head_covers
        (NamedRun.stateBeforeTime S rho d reader).st.core.T P y.confirmed = true
      rw [hk]
      show (match Block.find? (NamedRun.stateBeforeTime S rho d reader).st.core.T key with
        | some head => Block.preceq P head
        | none => false) = true
      rw [hfind']
      exact hy

/-- **Cases 1 and 2 of the containment.** Every body-ready input of an honest
sender at the round-`r` G2 read covers the protected prefix, as soon as the
sender's row is either a post-boundary emission of a round below `r` (`hpost`)
or a pre-boundary emission of a round at or above the stable round (`hconf`).
Copied from `SupportCarry.carry_interpreted_localCovers` with the round
side-condition relaxed to the implication actually used. -/
private theorem sg_interpreted_covers (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (auth : NamedUnforgeable S rho)
    (b0 : Time) (s r : Round) (Pn : NamedBlock V)
    (hconf : SGHonestConfirmedAtOrAbove S rho b0 s Pn.erase)
    (hpost : ∀ (a : NamedAttestation V) (t : Time), a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (.attest a) t → b0 ≤ t → a.round < r →
      ∀ key, a.confirmed = some key →
        ∀ K : NamedBlock V, NamedRun.blockInRun S rho K → K.root = key →
          Block.Preceq Pn.erase K.erase)
    (w : V) (hw : w ∈ rho.honest) (u : V) (hu : u ∈ rho.honest) (cutoff : Time)
    {z : Protocol.SGVote V}
    (hz : z ∈ DecoupledConsensusModel.Protocol.interpretedInputs
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.F
      S.hc.η_SG r cutoff u)
    (hzs : S.a z.round < b0 → s ≤ z.round) :
    localCovers
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
      z.confirmed Pn.erase = true := by
  obtain ⟨hzraw, hready⟩ := Finset.mem_filter.mp hz
  obtain ⟨b, hbval, hbround, hbproj, hbwin, _hblt, hbem⟩ :=
    sg_rawInputs_trace S rho sch auth (domain S.E S.hc r .g2) cutoff w S.hc.η_SG r u hu hzraw
  have hzr : z.round < r := (sg_window_bounds hbwin).2
  have hbr : b.round < r := by rw [hbround]; exact hzr
  obtain ⟨_, _, _, K, _, hkey⟩ := Proofs.NamedOutageInputs.emitted_attestation_head S rho hbem
  have hzconf : z.confirmed = some K.root := by rw [← hbproj, sg_sgVote_confirmed, hkey]
  have hfindsome : ∃ Hb : Block V,
      Block.find? (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.T K.root
        = some Hb := by
    cases hf : Block.find?
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.T K.root with
    | some Hb => exact ⟨Hb, rfl⟩
    | none =>
      exfalso
      have hfalse : DecoupledConsensusModel.Protocol.bodyReady
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.F cutoff z
            = false := by
        simp only [DecoupledConsensusModel.Protocol.bodyReady, Protocol.HealingStore.gradeView,
          Protocol.Store.toHealing, hzconf, hf]
      rw [hfalse] at hready
      exact absurd hready (by simp)
  obtain ⟨Hb, hfind⟩ := hfindsome
  obtain ⟨H, hHmem, hHe, hHroot⟩ :=
    sg_find_named_at_strict S rho (domain S.E S.hc r .g2) w hfind
  have hHrun : NamedRun.blockInRun S rho H :=
    sg_held_blockInRun S rho sch w hw (domain S.E S.hc r .g2) hHmem
  have hcover : Block.Preceq Pn.erase H.erase := by
    by_cases hlt : S.a b.round < b0
    · refine hconf b (S.a b.round) (hbval ▸ hu) (hbval ▸ hbem) hlt ?_ K.root hkey H hHrun
        hHroot
      rw [hbround]
      exact hzs (by rw [← hbround]; exact hlt)
    · exact hpost b (S.a b.round) (hbval ▸ hu) (hbval ▸ hbem) (not_lt.mp hlt) hbr
        K.root hkey H hHrun hHroot
  change Protocol.head_covers
    (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.T Pn.erase z.confirmed
      = true
  rw [hzconf]
  show (match Block.find?
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.T K.root with
    | some head => Block.preceq Pn.erase head
    | none => false) = true
  rw [hfind, ← hHe]
  exact hcover

private theorem sg_nat_succ_lt : ∀ a s r : Nat, a < s → s < r → a + 1 < r := by
  intro a s r h1 h2; omega

private theorem sg_nat_succ_le : ∀ a s : Nat, a < s → a + 1 ≤ s := by
  intro a s h; omega


/-- **The opposition containment (addendum 34, 9).** Every honest
opponent of the protected prefix at a needing reader's round-`r` G2 read is a
stale risk of the inventory taken at `tau = min b0 (early S.E S.hc r.g2)`.

`Opposes` has two arms. The equivocation arm asks for two raw tokens of the
same round with different confirmed heads; both trace back to honest emissions
of that one round, which `emitted_same_round_unique` makes the same emission,
so the arm is empty for an honest sender.

The first arm produces a body-ready token `x` of `u` in the reader's late view
that does not cover the prefix and whose round dominates every token of the
reader's **early** view. Trace `x` back to the honest emission `a`:

1. `b0 ≤ S.a a.round`: `hpost` applies and `x` covers — no opponent.
2. `S.a a.round < b0` and `s ≤ a.round`: `hconf`'s sender clause applies and `x`
   covers — no opponent.
3. `S.a a.round < b0` and `a.round < s`: the row's healthy deadline
   `S.a a.round + Δ` is at or before **both** `b0` (formation margin) and
   `early S.E S.hc r.g2` (schedule gap), hence at or before `tau`. So the row
   is already in the reader's store at `tau`, inside `retainedRounds`, and the
   inventory is nonempty. Its maximal element `m` either has `x`'s own round —
   then `x` itself is a non-covering maximal retained row and `u` is a stale
   risk — or a strictly larger one, and then `m` is itself body-ready at the
   round-`r` early cutoff, which contradicts the domination clause.

**The empty-early-view shape is not a counterexample any more.** With the prior
boundary `b0 ≤ supportBoundary ≤ S.a r` a sender with no early-view token
opposed vacuously through the domination clause, and its non-covering late
token could sit outside the boundary inventory. At `tau = min b0 (early r.g2)`
that cannot happen: the late token still traces back to an honest emission, and
every honest emission falls into case 1, case 2 or case 3 above. In case 3 the
row is *in* the inventory at `tau` — the inventory cutoff is at or before
the early cutoff, so nothing that the early view could have shown is missing
from it — so the sender is a stale risk rather than a free opponent. -/
private theorem sg_opposition_contained (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (s r : Round) (Pn : NamedBlock V) (tau : Time)
    (htau : tau = min b0 (early S.E S.hc r .g2))
    (hexec : OutageExecution S rho b0 b1)
    (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hentry : IntrinsicHighEntryHistory S rho Pn r)
    (hslt : s < r) (hhor : domain S.E S.hc r .g1 ≤ rho.horizon)
    (hpost : ∀ (a : NamedAttestation V) (t : Time), a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (.attest a) t → b0 ≤ t → a.round < r →
      ∀ key, a.confirmed = some key →
        ∀ K : NamedBlock V, NamedRun.blockInRun S rho K → K.root = key →
          Block.Preceq Pn.erase K.erase)
    (hconf : SGHonestConfirmedAbove S rho b0 s Pn.erase)
    (supportRound : Round) (hsr : supportRound ≤ r)
    (v : V) (hv : v ∈ rho.honest) (hneed : NeedsSG S rho Pn r v)
    (hclock : S.hc.round_of (NamedRun.stateBeforeTime S rho tau v).st.core.s = supportRound)
    (u : V) (hu : u ∈ rho.honest)
    (hopp : opposing
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.F
      S.hc.η_SG r (early S.E S.hc r .g2) (late S.E S.hc r .g2) u Pn.erase = true) :
    u ∈ commonStaleRisks S rho tau Pn supportRound r := by
  have hR : 3 ≤ S.hc.R := S.hc.R_ge_three
  have sch : NamedScheduleWellFormed S rho := hexec.core.toNamedScheduleWellFormed
  have auth : NamedUnforgeable S rho := hexec.core.toNamedUnforgeable
  have roots : NamedRootCollisionFree S rho := hexec.core.toNamedRootCollisionFree
  have htau_b0 : tau ≤ b0 := by rw [htau]; exact min_le_left _ _
  have htau_e : tau ≤ early S.E S.hc r .g2 := by rw [htau]; exact min_le_right _ _
  have htau_dom : tau ≤ domain S.E S.hc r .g2 := htau_e.trans (sg_early_le_domain S r)
  
  -- from `NeedsSG`. The reader's finalized prefix at the round-`r` G2 read is
  -- comparable with the protected prefix — that is L4's finalized-compatibility,
  -- which rests on the intrinsic whole-history premise `hentry` and so holds at
  -- every read at or before round `r`'s action, before `b0` included. If the
  -- protected prefix were at or below it, the same would hold at the opening
  -- read, because the finalized prefix only grows, and the reader would not need
  -- a support grade at all, contradicting `hneed`.
  have hFPdom : Block.Preceq
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.F Pn.erase := by
    have hdomle : domain S.E S.hc r .g2 ≤ S.a r :=
      (sg_domain_le_opening S r).trans (sg_opening_le_a S r)
    have hPF := finalized_compatible_after_boundary S rho b0 b1 s r Pn
      hexec hmargin hsleep hentry v hv (domain S.E S.hc r .g2) hdomle
    rcases (show Block.Preceq Pn.erase (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc r .g2) v).st.core.F ∨
        Block.Preceq (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc r .g2) v).st.core.F Pn.erase by
      simpa only [Block.compatible, Bool.or_eq_true] using hPF) with hPle | hFle
    · exfalso
      refine hneed ?_
      have hstage : NamedRun.readAt S rho (domain S.E S.hc r .g1) v =
          NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1 + 1) v := by
        rw [sg_readAt_eq_succ]
      rw [hstage]
      exact Block.preceq_trans hPle (sg_strict_F_mono S rho sch v
        (le_of_lt (sg_g2_lt_opening_cut S r)))
    · exact hFle
  refine Finset.mem_filter.mpr ⟨hu, v, hv, hneed, ?_⟩
  simp only [opposing, decide_eq_true_eq] at hopp
  rcases hopp with ⟨x, hx, hdom, hncov⟩ | ⟨p, hp, q, hq, -, hpqround, hpqkey⟩
  · simp only [readyView, Finset.mem_image] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    rw [← hzx] at hncov hdom
    have hzraw := (Finset.mem_filter.mp hz).1
    obtain ⟨a, hav, har, hap, hwin, halt, haem⟩ :=
      sg_rawInputs_trace S rho sch auth (domain S.E S.hc r .g2) (late S.E S.hc r .g2) v
        S.hc.η_SG r u hu hzraw
    have hzr : z.round < r := (sg_window_bounds hwin).2
    have hzlo : r - S.hc.η_SG ≤ z.round := (sg_window_bounds hwin).1
    by_cases hcase : S.a z.round < b0 → s ≤ z.round
    · exact absurd (sg_interpreted_covers S rho sch auth b0 s r Pn hconf.1 hpost v hv u hu
        (late S.E S.hc r .g2) hz hcase) hncov
    · push_neg at hcase
      obtain ⟨hltb0, hnotle⟩ := hcase
      have hars : a.round < s := by rw [har]; exact hnotle
      have hdb0 : S.a a.round + S.E.Δ ≤ b0 :=
        sg_action_deadline S b0 s a.round hR hmargin (Nat.le_of_lt hars)
      have hde : S.a a.round + S.E.Δ ≤ early S.E S.hc r .g2 :=
        sg_action_delta_le_early S hR (Nat.lt_trans hars hslt)
      have hdtau : S.a a.round + S.E.Δ ≤ tau := by
        rw [htau]; exact le_min hdb0 hde
      have hnext_e : domain S.E S.hc (a.round + 1) .g2 ≤ early S.E S.hc r .g2 :=
        sg_domain_le_early S hR (sg_nat_succ_lt _ _ _ hars hslt)
      have has_b0 : S.a s ≤ b0 :=
        sg_le_of_add_le _ _ _ S.E.Δ_pos (sg_action_deadline S b0 s s hR hmargin le_rfl)
      have hnext_b0 : domain S.E S.hc (a.round + 1) .g2 ≤ b0 :=
        ((sg_domain_le_opening S (a.round + 1)).trans
          ((sg_opening_le_a S (a.round + 1)).trans
            (sg_a_mono S (sg_nat_succ_le _ _ hars)))).trans has_b0
      have hnext_tau : domain S.E S.hc (a.round + 1) .g2 ≤ tau := by
        rw [htau]; exact le_min hnext_b0 hnext_e
      have hahon : a.val_index ∈ rho.honest := by rw [hav]; exact hu
      have haem' : NamedRun.emits S rho a.val_index (.attest a) (S.a a.round) := by
        rw [hav]; exact haem
      obtain ⟨hrow, hstampnext, -⟩ :=
        Proofs.NamedSGArrival.healthy_emitted_sg_at_next_g2_of_deadline S rho b0 b1 hexec
          hahon haem' hdb0 v hv
      obtain ⟨hrowtau, hstampeq⟩ := sg_strict_sg_row_carry S rho sch v hnext_tau hrow
      have hstamptau : occurrenceBefore
          ((NamedRun.stateBeforeTime S rho tau v).st.core.timestamp_sg_vote
            (Protocol.sgVote a.erase)) tau = true := by
        rw [hstampeq]
        exact occurrenceBefore_mono
          ((sg_early_le_domain S (a.round + 1)).trans hnext_tau) hstampnext
      have hcoh : Proofs.NamedStore.Coherent S.E S.cfg (NamedRun.stateBeforeTime S rho tau v).st :=
        (Proofs.NamedRuntime.stateBeforeTime_invariants S rho tau v).1.1.1
      have hpool := NamedAdmission.pool_view_mem
        (NamedRun.stateBeforeTime S rho tau v).st hcoh.2.2.2.1 a hrowtau
      have hsgv : Protocol.sgVote a.erase ∈
          (NamedRun.stateBeforeTime S rho tau v).st.core.toHealing.gradeView.sg_votes a.round :=
        Finset.mem_image_of_mem Protocol.sgVote hpool
      have halttau : S.a a.round < tau := sg_lt_of_add_le _ _ _ S.E.Δ_pos hdtau
      have hahor : S.a a.round ≤ rho.horizon :=
        (sg_a_le_domain_g1 S hR (by rw [har]; exact hzr)).trans hhor
      have hround_le : a.round ≤ supportRound := by
        have hcl := sg_round_le_clock_round S rho sch tau v hv a.round halttau hahor
        rw [hclock] at hcl
        exact hcl
      have hretr : z.round ∈ Internal.OutageEntryRevision.retainedRounds S supportRound :=
        sg_mem_retainedRounds S ((Nat.sub_le_sub_right hsr _).trans hzlo)
          (by rw [← har]; exact hround_le)
      have hzval : z.val_index = u := (Finset.mem_filter.mp hzraw).2.1
      have hzret : z ∈ Internal.OutageEntryRevision.retainedRaw S
          (NamedRun.stateBeforeTime S rho tau v).st.core supportRound tau u := by
        refine Finset.mem_filter.mpr
          ⟨Finset.mem_biUnion.mpr ⟨z.round, hretr, ?_⟩, hzval, ?_⟩
        · rw [← hap]; exact hsgv
        · rw [← hap]; exact hstamptau
      by_cases hbad : ∃ y ∈ Internal.OutageEntryRevision.latest
          (Internal.OutageEntryRevision.retainedRaw S
            (NamedRun.stateBeforeTime S rho tau v).st.core supportRound tau u),
          Internal.OutageEntryRevision.covers
            (NamedRun.stateBeforeTime S rho tau v).st.core Pn.erase y = false
      · simp only [Internal.OutageEntryRevision.staleAt, decide_eq_true_eq]
        exact Or.inl hbad
      · exfalso
        push_neg at hbad
        have hcov : ∀ y ∈ Internal.OutageEntryRevision.latest
            (Internal.OutageEntryRevision.retainedRaw S
              (NamedRun.stateBeforeTime S rho tau v).st.core supportRound tau u),
            Internal.OutageEntryRevision.covers
              (NamedRun.stateBeforeTime S rho tau v).st.core Pn.erase y = true := by
          intro y hy
          simpa only [Bool.not_eq_false] using hbad y hy
        obtain ⟨m, hm, hmmax⟩ := Finset.exists_max_image
          (Internal.OutageEntryRevision.retainedRaw S
            (NamedRun.stateBeforeTime S rho tau v).st.core supportRound tau u)
          (fun y => y.round) ⟨z, hzret⟩
        have hmlat : m ∈ Internal.OutageEntryRevision.latest
            (Internal.OutageEntryRevision.retainedRaw S
              (NamedRun.stateBeforeTime S rho tau v).st.core supportRound tau u) :=
          Finset.mem_filter.mpr ⟨hm, hmmax⟩
        have hmcov := hcov m hmlat
        have hzm : z.round ≤ m.round := hmmax z hzret
        rcases Nat.eq_or_lt_of_le hzm with heq | hlt
        · have hzlat : z ∈ Internal.OutageEntryRevision.latest
              (Internal.OutageEntryRevision.retainedRaw S
                (NamedRun.stateBeforeTime S rho tau v).st.core supportRound tau u) :=
            Finset.mem_filter.mpr ⟨hzret, fun y hy => by rw [heq]; exact hmmax y hy⟩
          exact hncov
            (sg_covers_transfer S rho sch roots v hv htau_dom Pn.erase (hcov z hzlat))
        · obtain ⟨c, hcv, hcr, hcp, hclt, hcem, hcrow⟩ :=
            sg_retained_trace S rho sch auth tau v supportRound u hu hm
          have hmr : m.round < r := by
            refine sg_round_lt_of_a_le_early S ?_
            rw [← hcr]
            exact le_of_lt (lt_of_lt_of_le hclt htau_e)
          have hmwin : m.round ∈ Protocol.latest_window S.hc.η_SG r :=
            sg_mem_latest_window (hzlo.trans (Nat.le_of_lt hlt)) hmr
          obtain ⟨hcrowr, hcstampeq⟩ := sg_strict_sg_row_carry S rho sch v htau_dom hcrow
          have hcohr : Proofs.NamedStore.Coherent S.E S.cfg
              (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st :=
            (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (domain S.E S.hc r .g2) v).1.1.1
          have hpoolr := NamedAdmission.pool_view_mem
            (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st hcohr.2.2.2.1 c hcrowr
          have hsgvr : Protocol.sgVote c.erase ∈
              (NamedRun.stateBeforeTime S rho
                (domain S.E S.hc r .g2) v).st.core.toHealing.gradeView.sg_votes c.round :=
            Finset.mem_image_of_mem Protocol.sgVote hpoolr
          have hmstamptau : occurrenceBefore
              ((NamedRun.stateBeforeTime S rho tau v).st.core.timestamp_sg_vote m) tau = true :=
            (Finset.mem_filter.mp hm).2.2
          have hmval : m.val_index = u := (Finset.mem_filter.mp hm).2.1
          have hmstampr : occurrenceBefore ((NamedRun.stateBeforeTime S rho
              (domain S.E S.hc r .g2) v).st.core.timestamp_sg_vote m)
              (early S.E S.hc r .g2) = true := by
            rw [← hcp] at hmstamptau ⊢
            rw [hcstampeq]
            exact occurrenceBefore_mono htau_e hmstamptau
          have hmraw : m ∈ DecoupledConsensusModel.Protocol.rawInputs
              (NamedRun.stateBeforeTime S rho
                (domain S.E S.hc r .g2) v).st.core.toHealing.gradeView
              S.hc.η_SG r (early S.E S.hc r .g2) u := by
            refine Finset.mem_filter.mpr
              ⟨Finset.mem_biUnion.mpr ⟨m.round, List.mem_toFinset.mpr hmwin, ?_⟩,
                hmval, hmstampr⟩
            rw [← hcp]; exact hsgvr
          have hmready : DecoupledConsensusModel.Protocol.bodyReady
              (NamedRun.stateBeforeTime S rho
                (domain S.E S.hc r .g2) v).st.core.toHealing.gradeView
              (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.F
              (early S.E S.hc r .g2) m = true := by
            by_cases hms : s ≤ m.round
            · obtain ⟨-, -, -, K, -, hkey⟩ :=
                Proofs.NamedOutageInputs.emitted_attestation_head S rho hcem
              have hcs : s ≤ c.round := by rw [hcr]; exact hms
              obtain ⟨H, hH, hHroot, hHcompat, hHstamp⟩ :=
                hconf.2 c (S.a c.round) (hcv ▸ hu) (hcv ▸ hcem)
                  (sg_a_add_delta_le_of_lt_public S b0 hexec.boundaryPublic c.round
                    (hclt.trans_le htau_b0)) hcs
                  v hv (domain S.E S.hc r .g2)
                  ((sg_action_delta_le_early S hR (by rw [hcr]; exact hmr)).trans
                    (sg_early_le_domain S r))
                  hFPdom K.root hkey
              have hmconf : m.confirmed = some H.root := by
                rw [← hcp, sg_sgVote_confirmed, hkey, hHroot]
              have hfindH : Block.find? (NamedRun.stateBeforeTime S rho
                  (domain S.E S.hc r .g2) v).st.core.T H.root = some H.erase := by
                simpa only [Proofs.NamedWire.erase_root] using
                  sg_held_find_at_strict S rho sch roots v hv (domain S.E S.hc r .g2) H hH
              simp only [DecoupledConsensusModel.Protocol.bodyReady, Protocol.HealingStore.gradeView,
                Protocol.Store.toHealing, hmconf, hfindH]
              exact Bool.and_eq_true_iff.mpr
                ⟨hHstamp (early S.E S.hc r .g2)
                  (sg_action_delta_le_early S hR (by rw [hcr]; exact hmr)), hHcompat⟩
            unfold Internal.OutageEntryRevision.covers at hmcov
            rcases Option.eq_none_or_eq_some m.confirmed with hk | ⟨key, hk⟩
            · rw [hk] at hmcov
              exact absurd hmcov (by simp)
            · rw [hk] at hmcov
              dsimp only [Option.bind] at hmcov
              cases hf : Block.find? (NamedRun.stateBeforeTime S rho tau v).st.core.T key with
              | none =>
                rw [hf] at hmcov
                exact absurd hmcov (by simp)
              | some B =>
                rw [hf] at hmcov
                obtain ⟨H, hH, hHe, hHroot⟩ := sg_find_named_at_strict S rho tau v hf
                obtain ⟨hHd, hHstampeq⟩ := sg_strict_body_carry S rho sch v htau_dom hH
                have hfindr := sg_held_find_at_strict S rho sch roots v hv
                  (domain S.E S.hc r .g2) H hHd
                have hfindr' : Block.find?
                    (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.T key
                    = some H.erase := by
                  rw [← hHroot, ← Proofs.NamedWire.erase_root H]; exact hfindr
                have hst := NamedBlockStamp.held_body_stampedBefore_stateBeforeTime S rho sch
                  v tau H hH
                have hstr : stampedBefore ((NamedRun.stateBeforeTime S rho
                    (domain S.E S.hc r .g2) v).st.core.timestamp_block)
                    (early S.E S.hc r .g2) H.erase = true := by
                  rw [stampedBefore_eq_occurrenceBefore, hHstampeq]
                  rw [stampedBefore_eq_occurrenceBefore] at hst
                  exact occurrenceBefore_mono htau_e hst
                by_cases hcompat : Block.compatible H.erase
                    (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.F = true
                · simp only [DecoupledConsensusModel.Protocol.bodyReady, Protocol.HealingStore.gradeView,
                    Protocol.Store.toHealing, hk, hfindr']
                  exact Bool.and_eq_true_iff.mpr ⟨hstr, hcompat⟩
                · -- CLOSED (was the single documented placeholder of this file).
                  -- The head `H` was confirmed honestly before `b0` in a round
                  -- strictly below the stable round, the one band neither
                  -- `hpost` nor `hconf` reaches. No premise about that band is
                  -- needed: the configuration cannot occur.
                  --
                  -- `hFPdom` already puts the reader's finalized prefix at or
                  -- below the protected prefix, and `H` covers the protected
                  -- prefix, so the finalized prefix is at or below `H` and the
                  -- two ARE compatible — which is what this branch assumed they
                  -- are not.
                  exfalso
                  refine hcompat ?_
                  simp only [Block.compatible, Bool.or_eq_true]
                  exact Or.inr (Block.preceq_trans hFPdom (hHe ▸ hmcov))
          have hmtoken := hdom (DecoupledConsensusModel.Protocol.token m)
            (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hmraw, hmready⟩))
          exact Nat.not_le.mpr hlt hmtoken
  · exfalso
    simp only [rawView, Finset.mem_image] at hp hq
    obtain ⟨zp, hzp, hzpx⟩ := hp
    obtain ⟨zq, hzq, hzqx⟩ := hq
    obtain ⟨ap, hapv, hapr, happ, -, -, hapem⟩ :=
      sg_rawInputs_trace S rho sch auth (domain S.E S.hc r .g2) (late S.E S.hc r .g2) v
        S.hc.η_SG r u hu hzp
    obtain ⟨aq, haqv, haqr, haqp, -, -, haqem⟩ :=
      sg_rawInputs_trace S rho sch auth (domain S.E S.hc r .g2) (late S.E S.hc r .g2) v
        S.hc.η_SG r u hu hzq
    have hrounds : ap.round = aq.round := by
      rw [hapr, haqr]
      rw [← hzpx, ← hzqx] at hpqround
      exact hpqround
    have hab : ap = aq :=
      NamedOutageProvenance.emitted_same_round_unique S rho sch hapem haqem hrounds
    apply hpqkey
    rw [← hzpx, ← hzqx, ← happ, ← haqp, hab]

/-- The faulty/honest split of the opposition set. The honest half is
`sg_opposition_contained`; a faulty opponent is paid for by the
`Finset.univ \ rho.honest` term of the certificate's margin. -/
private theorem sg_opposition_stale (S : Setup V) (rho : NamedRun V)
    (supportBoundary : Time) (Pn : NamedBlock V) (supportRound r : Round)
    {v : V} (_hv : v ∈ rho.honest) (_hneed : NeedsSG S rho Pn r v)
    (hopp : ∀ u ∈ rho.honest, opposing
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.F
        S.hc.η_SG r (early S.E S.hc r .g2) (late S.E S.hc r .g2) u Pn.erase = true →
      u ∈ commonStaleRisks S rho supportBoundary Pn supportRound r) :
    (Finset.univ.filter fun u => opposing
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.F
        S.hc.η_SG r (early S.E S.hc r .g2) (late S.E S.hc r .g2) u Pn.erase = true) ⊆
      (Finset.univ \ rho.honest) ∪
        commonStaleRisks S rho supportBoundary Pn supportRound r := by
  intro u hu
  by_cases hh : u ∈ rho.honest
  · exact Finset.mem_union_right _ (hopp u hh (Finset.mem_filter.mp hu).2)
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, hh⟩)

/-- Copy of the private `NamedPhaseSource.action_after_g2`. -/
private theorem sg_action_after_g2 (S : Setup V) (r : Round) :
    domain S.E S.hc r .g2 < S.a r := by
  have he : S.a r = domain S.E S.hc r .g2 + 7 * S.E.Δ := by
    unfold Setup.a Protocol.HealConfig.a domain opening Phase.domainOffset
      Protocol.proposal_time Env.t slotStart
    ring
  rw [he]
  exact lt_add_of_pos_right _
    (Int.mul_pos (by decide : (0 : Int) < 7) S.E.Δ_pos)

/-- The protected prefix is in the grade-view tree of reader `v`'s store strictly
before the round-`r` G2 domain tick. **Closed on both sides.**

The post-boundary case is L4 at `t = domain S.E S.hc r.g2` plus store coherence.
The pre-boundary case, when the round-`r` G2 phase closes before the outage
starts, is `NamedEarlyHolding.stable_prefix_held_before_boundary` at the cut
`domain S.E S.hc r.g2`: the stable source's prefix is held at *every* honest
reader at every cut between `S.a s + Δ` and `b0`, and `sg_stable_deadline` says
the round-`r` G2 domain tick is such a cut. That lemma returns its own named
representative of `Pn.erase`, which is all the grade view needs, so the
conclusion is stated on the erased tree rather than on `bodies`. -/
private theorem sg_protected_in_grade_tree (S : Setup V) (rho : NamedRun V)
    (b0 b1 : Time) (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hmargin : FormationMargin S s b0) (hsleep : OutageSleepyThroughout S rho)
    (hPn : NamedRun.blockInRun S rho Pn)
    (hsr : s < r)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hband : IntrinsicConflictingCarrierBand S rho Pn r)
    (hentry : IntrinsicHighEntryHistory S rho Pn r)
    (hheld0 : ∀ w ∈ rho.honest, Pn ∈ (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (w0 : V) (hw0 : w0 ∈ rho.honest)
    (hseed : OutputSeed S rho b0 s Pn.erase)
    {v : V} (hv : v ∈ rho.honest) :
    Pn.erase ∈
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.toHealing.gradeView.T := by
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (domain S.E S.hc r .g2) v).1.1.1
  show Pn.erase ∈ (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.T
  rw [hcoh.1]
  by_cases hb0 : b0 ≤ domain S.E S.hc r .g2
  · exact Finset.mem_image.mpr ⟨Pn,
      (fg_noninterference_after_boundary S rho b0 b1 s r Pn hexec hslash hmargin
        hsleep hPn hno hband hentry hheld0 v hv _ hb0
        (le_of_lt (sg_action_after_g2 S r))).1, rfl⟩
  · obtain ⟨Pm, hPmE, -, hheld⟩ := NamedEarlyHolding.stable_prefix_held_before_boundary_of_seed
      S rho b0 b1 hexec hsleep w0 hw0 s Pn.erase hmargin hseed hno
      (domain S.E S.hc r .g2)
      (sg_stable_deadline S s r S.hc.R_ge_three hsr)
      (le_of_lt (not_le.mp hb0))
    exact Finset.mem_image.mpr ⟨Pm, hheld v hv, hPmE⟩






/-! ## 9. The grade at a needing reader, and the checkpoint conclusion -/

/-- The certificate's strict margin is the `gradeBool` margin at the round-`r`
G2 phase read of a reader that still needs the grade. -/
private theorem sg_grade_true (S : Setup V) (rho : NamedRun V)
    (supportBoundary : Time) (Pn : NamedBlock V) (supportRound r : Round)
    {v : V} (hv : v ∈ rho.honest) (hneed : NeedsSG S rho Pn r v)
    (hopp : ∀ u ∈ rho.honest, opposing
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.F
        S.hc.η_SG r (early S.E S.hc r .g2) (late S.E S.hc r .g2) u Pn.erase = true →
      u ∈ commonStaleRisks S rho supportBoundary Pn supportRound r)
    (hweight : S.E.electorate.weightOf ((Finset.univ \ rho.honest) ∪
        commonStaleRisks S rho supportBoundary Pn supportRound r) <
      S.E.electorate.weightOf (commonSupporters S rho supportBoundary Pn supportRound r)) :
    gradeBool S.E
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.F
      S.hc.η_SG r (early S.E S.hc r .g2) (late S.E S.hc r .g2) Pn.erase = true := by
  have h1 := S.E.electorate.weightOf_mono
    (sg_opposition_stale S rho supportBoundary Pn supportRound r hv hneed hopp)
  have h2 := S.E.electorate.weightOf_mono
    (sg_supporters_positive S rho supportBoundary Pn supportRound r hv hneed)
  simp only [gradeBool, decide_eq_true_eq]
  omega



/-- **L5 at the round opening (addendum 34, 12 as amended).**
Every honest reader's round-`r` *opening* read either has the protected prefix at
or below its FG root, or carries a round-`r` grade-2 frame result whose active
prefix covers the protected prefix.

**This is the round-free form (before the boundary frame).** `DomainIncluded` is replaced
by the three facts its components actually supply: the round is positive, the
round is strictly above the stable round, and the round's opening is inside the
horizon. The lower bound `b0 ≤ S.a r` is NOT among them. It entered the support
machinery in exactly two places, `sg_protected_in_grade_tree` and
`sg_opposition_contained`, and in both it was consumed only to produce the round
bound `s < r` (through `sg_stable_deadline` and `sg_stable_lt_round`). Every
other time fact of the proof is read at or before `S.a r`, which holds on either
side of the boundary; in particular `finalized_compatible_after_boundary` asks
for `t ≤ S.a r` alone. The window form below is the instance at a round with
`b0 ≤ S.a r`; `stage2_preBoundaryFrames` is the instance at a round with
`S.a r < b0`.

Three reads move and nothing else does.

* The filtered-tree membership and the finality compatibility come from the
  `readAt` form of L4, `fg_noninterference_after_boundary_readAt`, whose window
  is `b0 ≤ t < S.a r`; the opening is inside it by `FrameForward.opening_lt_a`.
  Its conclusion is already stated at `NamedRun.readAt`, so no staging step is
  needed between the read and the goal.
* The completed round-`r` G2 slot is `FrameCompleted.frame_g2_completed` at the
  strict cut `domain S.E S.hc r.g1 + 1`, which is the opening read: the G2
  domain is one `Δ` earlier, the action `6Δ` later, and the G2 domain is inside
  the horizon because the opening is.
* The clock round of the opening read is `r` (`sg_round_at_opening`), which is
  what `activeG2` addresses. That is the reason the field reads at the opening
  and not at the G2 domain, whose clock round is `r − 1`.

`NeedsSG` is itself stated at the opening read, so its negative branch *is* the
goal's left disjunct and the grade side of the proof — `sg_protected_in_grade_tree`,
`sg_grade_true`, `sg_opposition_contained`, `sg_freeze_of_graded`, all stated at
the round-`r` G2 domain read and at the support inventory — is reused verbatim. -/
theorem sg_at_domain_read_of_common_support_at
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hsleep : OutageSleepyThroughout S rho)
    (_hforming : GradeFormingThroughout S rho) (hPn : NamedRun.blockInRun S rho Pn)
    (hrpos : 0 < r) (hsr : s < r) (hopenhor : domain S.E S.hc r .g1 ≤ rho.horizon)
    (hmargin : FormationMargin S s b0)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hband : IntrinsicConflictingCarrierBand S rho Pn r)
    (hentry : IntrinsicHighEntryHistory S rho Pn r)
    (hheld0 : ∀ w ∈ rho.honest, Pn ∈ (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (hpost : ∀ (a : NamedAttestation V) (t : Time), a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (.attest a) t → b0 ≤ t → a.round < r →
      ∀ key, a.confirmed = some key →
        ∀ K : NamedBlock V, NamedRun.blockInRun S rho K → K.root = key →
          Block.Preceq Pn.erase K.erase)
    (hconf : SGHonestConfirmedAbove S rho b0 s Pn.erase)
    (w0 : V) (hw0 : w0 ∈ rho.honest)
    (hseed : OutputSeed S rho b0 s Pn.erase)
    (hsupport : ∃ supportBoundary : Time, ∃ supportRound : Round,
      supportBoundary = min b0 (early S.E S.hc r .g2) ∧ supportRound ≤ r ∧
      (∀ v ∈ rho.honest,
        S.hc.round_of (NamedRun.stateBeforeTime S rho supportBoundary v).st.core.s =
          supportRound) ∧
      S.E.electorate.weightOf
          ((Finset.univ \ rho.honest) ∪
            commonStaleRisks S rho supportBoundary Pn supportRound r) <
        S.E.electorate.weightOf (commonSupporters S rho supportBoundary Pn supportRound r)) :
    ∀ v ∈ rho.honest,
      let n := NamedRun.readAt S rho (domain S.E S.hc r .g1) v
      Block.Preceq Pn.erase n.st.core.F ∨
        ∃ raw : Block V,
          (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g2 = some (some raw) ∧
          Block.Preceq Pn.erase raw := by
  have hg2hor : domain S.E S.hc r .g2 ≤ rho.horizon :=
    (sg_g2_le_domain_g1 S r).trans hopenhor
  obtain ⟨supportBoundary, supportRound, hsbeq, hsrle, hclock, hweight⟩ := hsupport
  intro v hv
  show Block.Preceq Pn.erase (NamedRun.readAt S rho (domain S.E S.hc r .g1) v).st.core.F ∨
    ∃ raw : Block V,
      (DecoupledConsensusModel.Protocol.readFrame (NamedRun.readAt S rho (domain S.E S.hc r .g1) v).cache
        (NamedRun.readAt S rho (domain S.E S.hc r .g1) v).st.core.toHealing r).g2 =
          some (some raw) ∧
      Block.Preceq Pn.erase raw
  by_cases hneed : NeedsSG S rho Pn r v
  · right
    
    -- root, so the reader's filtered tree is never consulted and the L4
    -- disjunction is not needed here. Only the finality compatibility is, and
    -- `finalized_compatible_after_boundary` asks for `t ≤ S.a r` alone, not for
    -- `b0 ≤ t`. That is what covers the round that straddles `b0`, whose opening
    -- read is a PRE-outage read: `DomainIncluded` now bounds the action from
    -- below and only the opening from above, so such a round is included.
    have hF : Block.compatible Pn.erase
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1 + 1) v).st.core.F = true :=
      finalized_compatible_after_boundary S rho b0 b1 s r Pn hexec hmargin hsleep hentry v hv
        (domain S.E S.hc r .g1 + 1) (sg_opening_cut_le_a S r)
    obtain ⟨raw0, hfreeze, hPraw0⟩ := sg_freeze_of_graded S.E
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.toHealing.gradeView
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.F S.hc.η_SG r
      (sg_early_le_late S r)
      (sg_protected_in_grade_tree S rho b0 b1 s r Pn hexec hslash hmargin hsleep hPn
        hsr hno hband hentry hheld0 w0 hw0 hseed hv)
      (sg_grade_true S rho supportBoundary Pn supportRound r hv hneed
        (fun u hu hopp => sg_opposition_contained S rho b0 b1 s r Pn supportBoundary hsbeq
          hexec hmargin hsleep hentry hsr hopenhor hpost hconf supportRound hsrle v hv
          hneed (hclock v hv) u hu hopp)
        hweight)
    have hbridge : NamedRun.readAt S rho (domain S.E S.hc r .g1) v =
        NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1 + 1) v := by
      rw [sg_readAt_eq_succ]
    have hcomp := FrameCompleted.frame_g2_completed S rho hexec.core v hv r hrpos
      (domain S.E S.hc r .g1 + 1) (sg_g2_lt_opening_cut S r) (sg_opening_cut_le_a S r) hg2hor
    rw [hfreeze] at hcomp
    rw [← hbridge] at hcomp
    simp only [Option.map_some] at hcomp
    have hF' : Block.compatible Pn.erase
        (NamedRun.readAt S rho (domain S.E S.hc r .g1) v).st.core.F = true := by
      rw [hbridge]; exact hF
    exact ⟨_, hcomp, (sg_retained_prefix raw0 _ Pn.erase hF').mpr hPraw0⟩
  · exact Or.inl (not_not.mp hneed)

/-- **L5 at the round opening, window form.** The instance of
`sg_at_domain_read_of_common_support_at` at an included round: `DomainIncluded`
supplies the positivity and the horizon bound directly, and the round bound
`s < r` through `sg_stable_lt_round` from its lower bound `b0 ≤ S.a r` and the
formation margin. The signature is unchanged, so `RoundBase` and every other
caller keeps working verbatim. -/
theorem sg_at_domain_read_of_common_support
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hsleep : OutageSleepyThroughout S rho)
    (hforming : GradeFormingThroughout S rho) (hPn : NamedRun.blockInRun S rho Pn)
    (hr : DomainIncluded S rho b0 r)
    (hmargin : FormationMargin S s b0)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hband : IntrinsicConflictingCarrierBand S rho Pn r)
    (hentry : IntrinsicHighEntryHistory S rho Pn r)
    (hheld0 : ∀ w ∈ rho.honest, Pn ∈ (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (hpost : ∀ (a : NamedAttestation V) (t : Time), a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (.attest a) t → b0 ≤ t → a.round < r →
      ∀ key, a.confirmed = some key →
        ∀ K : NamedBlock V, NamedRun.blockInRun S rho K → K.root = key →
          Block.Preceq Pn.erase K.erase)
    (hconf : SGHonestConfirmedAbove S rho b0 s Pn.erase)
    (w0 : V) (hw0 : w0 ∈ rho.honest)
    (hseed : OutputSeed S rho b0 s Pn.erase)
    (hsupport : ∃ supportBoundary : Time, ∃ supportRound : Round,
      supportBoundary = min b0 (early S.E S.hc r .g2) ∧ supportRound ≤ r ∧
      (∀ v ∈ rho.honest,
        S.hc.round_of (NamedRun.stateBeforeTime S rho supportBoundary v).st.core.s =
          supportRound) ∧
      S.E.electorate.weightOf
          ((Finset.univ \ rho.honest) ∪
            commonStaleRisks S rho supportBoundary Pn supportRound r) <
        S.E.electorate.weightOf (commonSupporters S rho supportBoundary Pn supportRound r)) :
    ∀ v ∈ rho.honest,
      let n := NamedRun.readAt S rho (domain S.E S.hc r .g1) v
      Block.Preceq Pn.erase n.st.core.F ∨
        ∃ raw : Block V,
          (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g2 = some (some raw) ∧
          Block.Preceq Pn.erase raw :=
  sg_at_domain_read_of_common_support_at S rho b0 b1 s r Pn hexec hslash hsleep hforming hPn
    hr.1 (sg_stable_lt_round S b0 s r S.hc.R_ge_three hmargin hr.2.1) hr.2.2
    hmargin hno hband hentry hheld0 hpost hconf w0 hw0 hseed hsupport

#print axioms sg_at_domain_read_of_common_support_at
#print axioms sg_at_domain_read_of_common_support
#print axioms sg_ready_view_mono
#print axioms sg_stable_deadline
#print axioms sg_protected_in_grade_tree
#print axioms sg_opposition_contained
#print axioms sg_interpreted_covers
#print axioms sg_covers_transfer
#print axioms sg_rawInputs_trace
#print axioms sg_round_le_clock_round
#print axioms sg_opposition_stale
#print axioms sg_grade_true
#print axioms sg_graded_compatible
#print axioms sg_freeze_of_graded
#print axioms sg_supporters_positive
#print axioms sg_early_le_late
#print axioms sg_action_after_g2
#print axioms sg_retained_prefix

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
