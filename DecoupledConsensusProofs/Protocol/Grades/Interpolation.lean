module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.RoundBase
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RoundStep
public import DecoupledConsensusProofs.Protocol.Grades.SupportCarry
public import DecoupledConsensusProofs.Objects.IntervalInduction
public import DecoupledConsensusProofs.Protocol.Handlers.NonInterference
public import DecoupledConsensusProofs.Protocol.Grades.Q10Frame
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Records
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Walk

@[expose] public section


namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedJointOutage
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

set_option linter.unusedSectionVars false

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. Block algebra -/

/-- The predicate half of `pickUnique?`. `Proofs.Engine.pickUnique?_mem` is the
membership half; the tree has no companion for the property. -/
private theorem pick_property {α : Type} [DecidableEq α] {T : Finset α} {p : α → Bool}
    {x : α} (h : pickUnique? T p = some x) : p x = true := by
  unfold pickUnique? at h
  split at h
  · rename_i hex
    rw [Option.some_inj] at h
    subst h
    exact Finset.choose_property _ _ hex
  · exact absurd h (by simp)

/-- `deepest?` of a set returns an upper bound of every member it is comparable
with. Only comparability with the returned block is used. -/
private theorem preceq_deepest_of_compatible {T : Finset (Block V)} {G P : Block V}
    (hG : Block.deepest? T = some G) (hP : P ∈ T)
    (hcomp : Block.compatible P G = true) : Block.Preceq P G := by
  rcases (show Block.Preceq P G ∨ Block.Preceq G P by
    simpa only [Block.compatible, Bool.or_eq_true] using hcomp) with hPG | hGP
  · exact hPG
  · have hdeep : Block.isDeepestIn T G = true := pick_property hG
    simp only [Block.isDeepestIn, decide_eq_true_eq] at hdeep
    have hno : Block.deeper P G = false := hdeep P hP
    simp only [Block.deeper, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt] at hno
    have hle : P.depth ≤ G.depth := hno.1
    have heq := Block.preceq_eq_of_depth_le hGP hle
    subst heq
    exact Block.preceq_self _

/-- Two comparable blocks of the same depth are equal. -/
private theorem eq_of_compatible_depth {A B : Block V}
    (hcomp : Block.compatible A B = true) (h : A.depth = B.depth) : A = B := by
  rcases (show Block.Preceq A B ∨ Block.Preceq B A by
    simpa only [Block.compatible, Bool.or_eq_true] using hcomp) with hAB | hBA
  · exact Block.preceq_eq_of_depth_le hAB (le_of_eq h.symm)
  · exact (Block.preceq_eq_of_depth_le hBA (le_of_eq h)).symm

/-- **`deepest?` of a nonempty chain is `some`.** Distinct members of a chain
have distinct depths, so the maximal-depth member is the unique block no member
beats. This is the `none` case that every `activePrefix` consumer has to
exclude by hand. -/
private theorem deepest_some_of_chain {T : Finset (Block V)} {P : Block V}
    (hP : P ∈ T) (hchain : ∀ A ∈ T, ∀ B ∈ T, Block.compatible A B = true) :
    ∃ G, Block.deepest? T = some G := by
  obtain ⟨M, hM, hmax⟩ := T.exists_max_image (fun B : Block V => B.depth) ⟨P, hP⟩
  have hMdeep : Block.isDeepestIn T M = true := by
    simp only [Block.isDeepestIn, decide_eq_true_eq]
    intro C hC
    simp only [Block.deeper, Bool.or_eq_false_iff, Bool.and_eq_false_imp,
      decide_eq_false_iff_not, not_lt, decide_eq_true_eq]
    refine ⟨hmax C hC, ?_⟩
    intro hdepth
    have hCM : C = M := eq_of_compatible_depth (hchain C hC M hM) hdepth.symm
    subst hCM
    simp
  have huniq : ∃! a, a ∈ T ∧ Block.isDeepestIn T a = true := by
    refine ⟨M, ⟨hM, hMdeep⟩, ?_⟩
    rintro a ⟨haT, hadeep⟩
    simp only [Block.isDeepestIn, decide_eq_true_eq] at hadeep
    have hno : Block.deeper M a = false := hadeep M hM
    simp only [Block.deeper, Bool.or_eq_false_iff, decide_eq_false_iff_not, not_lt] at hno
    exact eq_of_compatible_depth (hchain a haT M hM)
      (Nat.le_antisymm (hmax a haT) hno.1)
  refine ⟨T.choose (fun a => Block.isDeepestIn T a = true) huniq, ?_⟩
  unfold Block.deepest? pickUnique?
  rw [dif_pos huniq]

/-- The active prefix of a saved root covers every tree member below that root,
and is never `none` when there is such a member. The filtered set is a set of
ancestors of `root`, hence a chain. -/
theorem activePrefix_covers {tree : Finset (Block V)} {root P : Block V}
    (hPT : P ∈ tree) (hPr : Block.Preceq P root) :
    ∃ G, activePrefix tree root = some G ∧ Block.Preceq P G := by
  set T := tree.filter (fun B => Block.preceq B root = true) with hT
  have hmem : P ∈ T := Finset.mem_filter.mpr ⟨hPT, hPr⟩
  have hchain : ∀ A ∈ T, ∀ B ∈ T, Block.compatible A B = true := by
    intro A hA B hB
    exact Block.compatible_of_preceq_common (Finset.mem_filter.mp hA).2
      (Finset.mem_filter.mp hB).2
  obtain ⟨G, hG⟩ := deepest_some_of_chain hmem hchain
  refine ⟨G, hG, ?_⟩
  have hGmem : G ∈ T := Proofs.Engine.deepest?_mem hG
  exact preceq_deepest_of_compatible hG hmem (hchain P hmem G hGmem)

/-! ### Clipping -/

/-- A clipped root is an ancestor of the root it was clipped from.
Copy of the private `NamedCacheProvenance.clip_preceq`. -/
theorem clip_preceq (g F : Block V) : Block.Preceq (clipGrade g F) g := by
  induction g with
  | genesis => exact Block.preceq_self _
  | node p s root gv gsv ats v ih =>
    simp only [clipGrade]
    split
    · exact Block.preceq_self _
    · apply Block.preceq_trans ih
      simp only [Block.preceq, Bool.or_eq_true]
      exact Or.inr (Block.preceq_self p)

/-- Clipping keeps every ancestor that is itself compatible with the finalized
block. Copy of the private `NamedCacheProvenance.retained_prefix`. -/
theorem clip_retains (g F B : Block V) (hBF : Block.compatible B F = true)
    (hBg : Block.Preceq B g) : Block.Preceq B (clipGrade g F) := by
  induction g with
  | genesis => exact hBg
  | node p s root gv gsv ats v ih =>
    by_cases hGF : Block.compatible (Block.node p s root gv gsv ats v) F = true
    · simpa only [clipGrade, hGF, ↓reduceIte] using hBg
    · have hBp : Block.Preceq B p := by
        simp only [Block.Preceq, Block.preceq, Bool.or_eq_true, decide_eq_true_eq] at hBg
        rcases hBg with hEq | hBp
        · subst B
          exact False.elim (hGF hBF)
        · exact hBp
      simpa only [clipGrade, hGF, Bool.eq_false_iff.mpr hGF, ↓reduceIte] using ih hBp


/-! ## 2. The two frame conjuncts at one read

`activeG2` and `sgRoot` are two projections of ONE frame: the frame the read's
own clock round addresses. Both unfold definitionally. -/

/-- The read's own governing round: the clock round of its store. -/
abbrev readRound (S : Setup V) (n : NamedNodeState V) : Round :=
  S.hc.round_of n.st.core.s

/-- The frame `activeG2` and `sgRoot` are both read from. -/
abbrev readFrameAt (S : Setup V) (n : NamedNodeState V) : Frame V :=
  DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing (readRound S n)

theorem activeG2_eq (S : Setup V) (n : NamedNodeState V) :
    activeG2 S n = ((readFrameAt S n).g2.bind id).bind
      (activePrefix (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG)) := rfl

theorem sgRoot_eq (S : Setup V) (n : NamedNodeState V) :
    sgRoot S n = DecoupledConsensusModel.Protocol.anchor S.E S.hc n.st.core.toHealing
      (readRound S n) (readFrameAt S n).g1 := rfl

/-- **Conjunct 1 at one read.** A completed, non-empty saved G2 root that covers
the protected prefix makes the active G2 candidate exist and cover it, provided
the prefix is in the reader's filtered tree. -/
theorem activeG2_covers (S : Setup V) (n : NamedNodeState V) {P raw : Block V}
    (hg2 : (readFrameAt S n).g2 = some (some raw))
    (hPT : P ∈ Protocol.get_filtered_block_tree n.st.core.toHealing.toFG)
    (hPr : Block.Preceq P raw) :
    ∃ G, activeG2 S n = some G ∧ Block.Preceq P G := by
  obtain ⟨G, hG, hPG⟩ := activePrefix_covers hPT hPr
  refine ⟨G, ?_, hPG⟩
  rw [activeG2_eq, hg2]
  exact hG

/-- The SG anchor is never below the FG root: it is either the root itself or a
member of the filtered tree, and every member of that tree is above the root. -/
theorem fg_root_preceq_anchor (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) (g1 : Option (Option (Block V))) :
    Block.Preceq (Protocol.get_fg_root st.toFG)
      (DecoupledConsensusModel.Protocol.anchor E hc st r g1) := by
  rcases g1 with _ | g
  · exact Block.preceq_self _
  rcases g with _ | root
  · exact Block.preceq_self _
  show Block.Preceq (Protocol.get_fg_root st.toFG)
    ((activePrefix (Protocol.get_filtered_block_tree st.toFG) root).getD
      (Protocol.get_fg_root st.toFG))
  cases hA : activePrefix (Protocol.get_filtered_block_tree st.toFG) root with
  | none => exact Block.preceq_self _
  | some A =>
    exact Proofs.Records.preceq_get_fg_root_of_mem_filtered
      (NamedProposalParent.activePrefix_mem _ root A hA)

/-- **Conjunct 2, FG-root branch.** -/
theorem preceq_sgRoot_of_fg_root (S : Setup V) (n : NamedNodeState V) {P : Block V}
    (h : Block.Preceq P (Protocol.get_fg_root n.st.core.toHealing.toFG)) :
    Block.Preceq P (sgRoot S n) :=
  Block.preceq_trans h (fg_root_preceq_anchor S.E S.hc n.st.core.toHealing
    (readRound S n) (readFrameAt S n).g1)

/-- **Conjunct 2, saved-G1 branch.** A completed, non-empty saved G1 root that
covers the protected prefix puts the prefix below the anchor. -/
theorem preceq_sgRoot_of_g1 (S : Setup V) (n : NamedNodeState V) {P root1 : Block V}
    (hg1 : (readFrameAt S n).g1 = some (some root1))
    (hPT : P ∈ Protocol.get_filtered_block_tree n.st.core.toHealing.toFG)
    (hPr : Block.Preceq P root1) : Block.Preceq P (sgRoot S n) := by
  obtain ⟨A, hA, hPA⟩ := activePrefix_covers hPT hPr
  rw [sgRoot_eq, hg1]
  show Block.Preceq P
    ((activePrefix (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG)
      root1).getD (Protocol.get_fg_root n.st.core.toHealing.toFG))
  rw [hA]
  exact hPA

#print axioms activePrefix_covers
#print axioms clip_preceq
#print axioms clip_retains
#print axioms activeG2_covers
#print axioms preceq_sgRoot_of_fg_root
#print axioms preceq_sgRoot_of_g1

/-! ## 3. The stable output and the candidate clause -/


/-- **Conjunct 3 at one store.** Addendum 34 22, revised (
1733, 1734): the stable output is a DURABLE STORE RECORD. `Protocol.get_stable`
is that record when it extends the finalized block, and the finalized block
otherwise. A prefix below the record and compatible with `F` is below both. -/
theorem preceq_get_stable (st : Protocol.Store V) {P : Block V}
    (hlat : Block.Preceq P st.latest_stable)
    (hF : Block.compatible P st.F = true) :
    Block.Preceq P (Protocol.get_stable st) := by
  unfold Protocol.get_stable
  split
  · exact hlat
  · rename_i hno
    rcases (show Block.Preceq P st.F ∨ Block.Preceq st.F P by
      simpa only [Block.compatible, Bool.or_eq_true] using hF) with hPF | hFP
    · exact hPF
    · exact absurd (Block.preceq_trans hFP hlat) hno

/-- **Conjunct 3 from the write's own disjunction.** The confirmation duty leaves
the stable record untouched when its grade-2 block is absent, so what the
boundary carry delivers is `P ⪯ F ∨ P ⪯ latest_stable`. Both arms give the user
output, and the finality arm is the stronger one: `get_stable` is
`latest_stable` when `F ⪯ latest_stable` and `F` otherwise, so `P ⪯ F` closes
BOTH branches, while the record arm needs the compatibility side condition that
`preceq_get_stable` consumes. L4 supplies that side condition at every read of
the window. -/
theorem preceq_get_stable_of_cases (st : Protocol.Store V) {P : Block V}
    (h : Block.Preceq P st.F ∨ Block.Preceq P st.latest_stable)
    (hF : Block.compatible P st.F = true) :
    Block.Preceq P (Protocol.get_stable st) := by
  rcases h with hPF | hlat
  · unfold Protocol.get_stable
    split
    · rename_i hle
      exact Block.preceq_trans hPF hle
    · exact hPF
  · exact preceq_get_stable st hlat hF

/-- The optional-G2 confirmation candidate: the eligible Goldfish head, or the
active G2 fallback. `frameSGCandidate` ignores its slot argument, so the
fallback is exactly `activeG2`. -/
theorem confirmationCandidate_eq (S : Setup V) (n : NamedNodeState V) (s : Slot) :
    confirmationCandidate S n s =
      (if (goldfishChoiceAt S n s).2 then some (goldfishChoiceAt S n s).1
        else activeG2 S n) := rfl

/-- The Goldfish walk starts at the SG anchor, so its head is above it. -/
theorem sgRoot_preceq_goldfishChoice (S : Setup V) (n : NamedNodeState V) (s : Slot) :
    Block.Preceq (sgRoot S n) (goldfishChoiceAt S n s).1 :=
  Protocol.ghost_preceq _ _ _ _

/-- **Conjunct 4 at one read.** Both branches of the candidate are covered: the
eligible head by the anchor, the fallback by the active G2. -/
theorem candidate_covers (S : Setup V) (n : NamedNodeState V) (s : Slot) {P B : Block V}
    (hcand : confirmationCandidate S n s = some B)
    (hsg : Block.Preceq P (sgRoot S n))
    (hg2 : ∀ G, activeG2 S n = some G → Block.Preceq P G) :
    Block.Preceq P B := by
  rw [confirmationCandidate_eq] at hcand
  split at hcand
  · rw [Option.some_inj] at hcand
    subst hcand
    exact Block.preceq_trans hsg (sgRoot_preceq_goldfishChoice S n s)
  · exact hg2 B hcand

/-! ## 4. The window statement and its three frame obligations -/

/-- `EntryPrefixOutputs` restricted to a window `[b0, cap]`. The production
statement is the `cap = rho.horizon` instance. -/
def EntryPrefixOutputsUpTo (S : Setup V) (rho : NamedRun V) (b0 cap : Time)
    (P : Block V) : Prop :=
  ∀ w ∈ rho.honest, ∀ t : Time, b0 ≤ t → t ≤ cap → t ≤ rho.horizon →
    let n := NamedRun.readAt S rho t w
    (Block.Preceq P (Protocol.get_fg_root n.st.core.toHealing.toFG) ∨
      ∃ G, activeG2 S n = some G ∧ Block.Preceq P G) ∧
    Block.Preceq P (sgRoot S n) ∧
    Block.Preceq P (Protocol.get_stable n.st.core) ∧
    (∀ u, b0 ≤ u → u ≤ t → ∀ B, CandidateWritten S rho w u B → Block.Preceq P B)


/-- The window statement at `cap = b1 + Δ` IS the production statement: addendum
34 caps `EntryPrefixOutputs` at one delivery delay after recovery. -/
theorem entryPrefixOutputs_of_upTo (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (P : Block V) (h : EntryPrefixOutputsUpTo S rho b0 (b1 + S.E.Δ) P) :
    EntryPrefixOutputs S rho b0 b1 P :=
  fun w hw t hb0 hcap hhor => h w hw t hb0 hcap hhor



/-- **Obligation C (conjunct 4).** The two frame conjuncts at the STAGED
support-cutoff read, which is not a plain `readAt`: `confirmationReadAt` sets
the clock to the cutoff slot and runs the cache preparation, so its frame is
not the frame of any strict read. -/
def CandidateReadCoverage (S : Setup V) (rho : NamedRun V) (b0 cap : Time)
    (P : Block V) : Prop :=
  ∀ w ∈ rho.honest, ∀ u : Time, b0 ≤ u → u ≤ cap → u ≤ rho.horizon →
    0 < S.E.slotOf u → u = Protocol.support_cutoff S.E (S.E.slotOf u) →
    Block.Preceq P (sgRoot S (confirmationReadAt S rho w u)) ∧
    ∀ G, activeG2 S (confirmationReadAt S rho w u) = some G → Block.Preceq P G


/-- **Obligation D (conjunct 3).** The stable record's own disjunction at every
read of the window: either the reader's finalized block already covers the
protected prefix, or the reader's durable stable record does.

 22 revised made the stable output a store field, so this
is not a frame obligation at all: it is the boundary record and its retention,
`RecordAtBoundary.stable_record_at_boundary_of_coverage` carried forward over
the candidate coverage that obligation C already supplies. It enters L11 as the
pair `hrecord` / `hretain` below. -/
def ReadStableCoverage (S : Setup V) (rho : NamedRun V) (b0 cap : Time) (P : Block V) :
    Prop :=
  ∀ w ∈ rho.honest, ∀ t : Time, b0 ≤ t → t ≤ cap → t ≤ rho.horizon →
    Block.Preceq P (NamedRun.readAt S rho t w).st.core.F ∨
      Block.Preceq P (NamedRun.readAt S rho t w).st.core.latest_stable

/-! ## 5. L11 -/


#print axioms preceq_get_stable
#print axioms preceq_get_stable_of_cases
#print axioms candidate_covers

/-! ## 6. Discharging obligation A from the round invariant

Arm 2 of the `sg` field DOES move from the checkpoint back to an earlier read of
the same round: both stores read the same completed G2 slot, whose value is the
freeze of the round's G2 domain tick clipped against each reader's own finalized
block, and clipping keeps every compatible ancestor. -/

theorem readAt_eq_succ (S : Setup V) (rho : NamedRun V) (t : Time) :
    NamedRun.readAt S rho t = NamedRun.stateBeforeTime S rho (t + 1) := by
  have hp : (fun e : NamedEvent V => decide (e.time ≤ t)) =
      fun e : NamedEvent V => decide (e.time < t + 1) := by
    funext e
    exact decide_eq_decide.mpr Int.lt_add_one_iff.symm
  unfold NamedRun.readAt NamedRun.stateBeforeTime
  rw [hp]




/-! ## 7. Discharging obligation B from obligation A

Once the three phase slots of the round the read addresses are closed, the
frame's `grade2Block` IS `activeG2`, and row Q10 puts it below the anchor. -/






/-- The schedule round of a time. -/
abbrev clockRoundAt (S : Setup V) (t : Time) : Round := S.hc.round_of (S.E.slotOf t)

/-! `omega` reads the type argument of `≤` syntactically, so every `Time` and
`Round` inequality below is discharged through a raw `Int` or `Nat` helper. -/

private theorem ip_le_of_lt_succ : ∀ a b : Int, a < b + 1 → a ≤ b := by
  intro a b h; omega

private theorem ip_lt_succ_of_le : ∀ a b : Int, a ≤ b → a < b + 1 := by
  intro a b h; omega

private theorem ip_lt_succ_of_lt : ∀ a b : Int, a < b → a < b + 1 := by
  intro a b h; omega

private theorem ip_lt_of_succ_le : ∀ a b : Int, a + 1 ≤ b → a < b := by
  intro a b h; omega

private theorem ip_succ_le_of_lt : ∀ a b : Int, a < b → a + 1 ≤ b := by
  intro a b h; omega

private theorem ip_succ_le_succ_of_le : ∀ a b : Int, a ≤ b → a + 1 ≤ b + 1 := by
  intro a b h; omega

private theorem ip_lt_of_eq_add_two : ∀ u x d : Int, 0 < d → u = x + 2 * d → x < u := by
  intro u x d h he; omega

private theorem ip_four_delta_pos : ∀ d : Int, 0 < d → 0 < 4 * d := by
  intro d h; omega

private theorem ip_sub_delta_lt : ∀ x d : Int, 0 < d → x + (-1) * d < x := by
  intro x d h; omega

private theorem ip_six_lt : ∀ x d : Int, 0 ≤ x → 0 < d → 6 * d < x + 6 * d + d := by
  intro x d h1 h2; omega

private theorem ip_nonneg_of_six_lt : ∀ b d : Int, 0 < d → 6 * d < b → 0 ≤ b := by
  intro b d h1 h2; omega

private theorem ip_lt_of_add_delta_le : ∀ a b d : Int, 0 < d → a + d ≤ b → a < b := by
  intro a b d h1 h2; omega

private theorem ip_nat_no_succ_le : ∀ a : Nat, ¬ (a + 1 ≤ a) := by
  intro a; omega

private theorem ip_nat_antisymm : ∀ a b : Nat, a < b + 1 → b < a + 1 → a = b := by
  intro a b h1 h2; omega


/-- Copied from the private helper of the same name in `NamedRuntime`, through
the private copy in `CommonSupportBase`. -/
private theorem ip_fold_clock_bounds (S : Setup V) (lo hi : Time) :
    ∀ (events : List (NamedEvent V)) (w : NamedWorld V),
      (∀ v, lo ≤ (w v).st.core.t ∧ (w v).st.core.t ≤ hi) →
      (∀ e ∈ events, lo ≤ e.time ∧ e.time ≤ hi) →
      ∀ v, lo ≤ (events.foldl (NamedWorld.step S) w v).st.core.t ∧
        (events.foldl (NamedWorld.step S) w v).st.core.t ≤ hi := by
  intro events
  induction events with
  | nil => intro w h _; exact h
  | cons e events ih =>
    intro w h ht
    apply ih
    · intro v
      rw [Proofs.NamedRuntime.step_clock_eq]
      cases e with
      | tick u t =>
        dsimp only
        split_ifs
        · exact ht _ (List.mem_cons_self ..)
        · exact h v
      | deliver u o t => exact h v
    · intro f hf
      exact ht f (List.mem_cons_of_mem _ hf)

/-- The read at `t` has its clock in `[0, t]`: the strict fold at `t + 1` sees
only events of time at most `t`. -/
private theorem ip_read_clock_bounds (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (t : Time) (ht : 0 ≤ t) (w : V) :
    0 ≤ (NamedRun.stateBeforeTime S rho (t + 1) w).st.core.t ∧
      (NamedRun.stateBeforeTime S rho (t + 1) w).st.core.t ≤ t := by
  have hinit : ∀ v : V, 0 ≤ (NamedWorld.init v).st.core.t ∧
      (NamedWorld.init (V := V) v).st.core.t ≤ t := by
    intro v
    constructor
    · simp [NamedWorld.init, NamedNode.initial, Protocol.NamedStore.initial, Protocol.Store.init]
    · simpa [NamedWorld.init, NamedNode.initial, Protocol.NamedStore.initial,
        Protocol.Store.init] using ht
  have hevents : ∀ e ∈ rho.events.filter (fun e => decide (e.time < t + 1)),
      0 ≤ e.time ∧ e.time ≤ t := by
    intro e he
    have hmem := List.mem_filter.mp he
    have hlt : e.time < t + 1 := by simpa only [decide_eq_true_eq] using hmem.2
    exact ⟨(sch.in_horizon e hmem.1).1, ip_le_of_lt_succ _ _ hlt⟩
  simpa only [NamedRun.stateBeforeTime] using
    ip_fold_clock_bounds S 0 t (rho.events.filter (fun e => decide (e.time < t + 1)))
      NamedWorld.init hinit hevents w

/-- Copied from the private helper of the same name in `NamedClockUniform`. -/
private theorem ip_tick_mem_le_strict_clock (S : Setup V) (rho : NamedRun V)
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

/-- Copied from the private helper of the same name in `NamedClockUniform`. -/
private theorem ip_stateBefore_slot_clock (S : Setup V) (rho : NamedRun V)
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

/-- Copied from the private helper of the same name in `NamedClockUniform`. -/
private theorem ip_stateBeforeTime_slot_clock (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (cut : Time) (reader : V) :
    (NamedRun.stateBeforeTime S rho cut reader).st.core.s =
      S.E.slotOf (NamedRun.stateBeforeTime S rho cut reader).st.core.t := by
  obtain ⟨i, hread, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho sch.sorted cut
  rw [hread]
  exact ip_stateBefore_slot_clock S rho i reader

/-- **The clock round of a read is the schedule round of its time.** The lower
bound is the tick at the start of the read's own slot, which is a public time at
or before the read and inside the horizon; the upper bound is the strict clock
bound. -/
theorem readRound_readAt (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (w : V) (hw : w ∈ rho.honest)
    (t : Time) (ht0 : (0 : Time) ≤ t) (hhor : t ≤ rho.horizon) :
    readRound S (NamedRun.readAt S rho t w) = clockRoundAt S t := by
  obtain ⟨hlo, hhi⟩ := ip_read_clock_bounds S rho sch t ht0 w
  have hup : S.E.slotOf (NamedRun.stateBeforeTime S rho (t + 1) w).st.core.t ≤
      S.E.slotOf t :=
    Protocol.slot_le_slotOf_of_proposal_time_le S.E
      ((Protocol.proposal_time_slotOf_le S.E hlo).trans hhi)
  have hpt : Protocol.proposal_time S.E (S.E.slotOf t) ≤ t :=
    Protocol.proposal_time_slotOf_le S.E ht0
  have htick : NamedEvent.tick w (Protocol.proposal_time S.E (S.E.slotOf t)) ∈ rho.events :=
    sch.tick_total w hw _ (Proofs.Optimistic.publicTime_proposal_time S (S.E.slotOf t))
      (Proofs.Optimistic.proposal_time_nonneg S.E (S.E.slotOf t)) (hpt.trans hhor)
  have hfil : NamedEvent.tick w (Protocol.proposal_time S.E (S.E.slotOf t)) ∈
      rho.events.filter (fun e => decide (e.time < t + 1)) :=
    List.mem_filter.mpr ⟨htick, by
      simp only [NamedEvent.time, decide_eq_true_eq]
      exact ip_lt_succ_of_le _ _ hpt⟩
  have hdown : S.E.slotOf t ≤
      S.E.slotOf (NamedRun.stateBeforeTime S rho (t + 1) w).st.core.t :=
    Protocol.slot_le_slotOf_of_proposal_time_le S.E
      (ip_tick_mem_le_strict_clock S rho sch hfil)
  show S.hc.round_of (NamedRun.readAt S rho t w).st.core.s = _
  rw [readAt_eq_succ, ip_stateBeforeTime_slot_clock S rho sch (t + 1) w,
    le_antisymm hup hdown]

/-! ### Round openings -/

/-- The G1 domain IS the round opening: its domain offset is zero. -/
theorem domain_g1_eq_opening (S : Setup V) (r : Round) :
    domain S.E S.hc r .g1 = opening S.E S.hc r := by
  simp only [domain, Phase.domainOffset]
  ring

private theorem ip_healR_pos (S : Setup V) : 0 < S.hc.R :=
  lt_of_lt_of_le (by norm_num) S.hc.R_ge_two

private theorem ip_opening_slot_mono (S : Setup V) {q r : Round} (h : q ≤ r) :
    S.hc.opening_slot q ≤ S.hc.opening_slot r := by
  simp only [Protocol.HealConfig.opening_slot]
  exact Nat.mul_le_mul h (le_refl S.hc.R)

private theorem ip_opening_mono (S : Setup V) {q r : Round} (h : q ≤ r) :
    opening S.E S.hc q ≤ opening S.E S.hc r :=
  Protocol.proposal_time_mono S.E (ip_opening_slot_mono S h)

private theorem ip_opening_lt (S : Setup V) {q r : Round}
    (h : opening S.E S.hc q < opening S.E S.hc r) : q < r := by
  by_contra hc
  exact absurd (ip_opening_mono S (Nat.le_of_not_lt hc)) (not_le.mpr h)

/-- A read has already passed the opening of its own clock round: the round's
opening slot is `⌊slot/R⌋ · R`, which is at or below the read's own slot. -/
theorem opening_le_clockRound (S : Setup V) (t : Time) (ht : (0 : Time) ≤ t) :
    opening S.E S.hc (clockRoundAt S t) ≤ t := by
  have hslot : S.hc.opening_slot (clockRoundAt S t) ≤ S.E.slotOf t := by
    simp only [clockRoundAt, Protocol.HealConfig.opening_slot, Protocol.HealConfig.round_of]
    exact Nat.div_mul_le_self _ _
  exact le_trans (Protocol.proposal_time_mono S.E hslot)
    (Protocol.proposal_time_slotOf_le S.E ht)

/-- A read is strictly before the opening of the round after its own. -/
theorem clockRound_lt_opening_succ (S : Setup V) (t : Time) :
    t < opening S.E S.hc (clockRoundAt S t + 1) := by
  by_contra hc
  have hslot : S.hc.opening_slot (clockRoundAt S t + 1) ≤ S.E.slotOf t :=
    Protocol.slot_le_slotOf_of_proposal_time_le S.E (not_lt.mp hc)
  have hdiv : clockRoundAt S t + 1 ≤ S.E.slotOf t / S.hc.R := by
    simpa only [Protocol.HealConfig.opening_slot] using
      (Nat.le_div_iff_mul_le (ip_healR_pos S)).mpr hslot
  have hnat : S.E.slotOf t / S.hc.R + 1 ≤ S.E.slotOf t / S.hc.R := hdiv
  exact absurd hnat (ip_nat_no_succ_le _)

/-- A time inside round `r`'s own span has clock round `r`. -/
theorem clockRoundAt_eq (S : Setup V) (t : Time) (r : Round) (ht0 : (0 : Time) ≤ t)
    (hlo : opening S.E S.hc r ≤ t) (hhi : t < opening S.E S.hc (r + 1)) :
    clockRoundAt S t = r := by
  have h1 : clockRoundAt S t < r + 1 :=
    ip_opening_lt S (lt_of_le_of_lt (opening_le_clockRound S t ht0) hhi)
  have h2 : r < clockRoundAt S t + 1 :=
    ip_opening_lt S (lt_of_le_of_lt hlo (clockRound_lt_opening_succ S t))
  exact ip_nat_antisymm _ _ h1 h2



/-- A support cutoff is two delays into its own slot, hence strictly after the
opening of its own clock round. -/
theorem opening_lt_support_cutoff (S : Setup V) (u : Time) (_hu : (0 : Time) ≤ u)
    (hcut : u = Protocol.support_cutoff S.E (S.E.slotOf u)) :
    opening S.E S.hc (clockRoundAt S u) < u := by
  have hsc : Protocol.support_cutoff S.E (S.E.slotOf u)
      = Protocol.proposal_time S.E (S.E.slotOf u) + 2 * S.E.Δ := by
    simp only [Protocol.support_cutoff, Protocol.proposal_time, Env.t, slotStart]
  have hlt : Protocol.proposal_time S.E (S.E.slotOf u) < u :=
    ip_lt_of_eq_add_two _ _ _ S.E.Δ_pos (hcut.trans hsc)
  have hslot : S.hc.opening_slot (clockRoundAt S u) ≤ S.E.slotOf u := by
    simp only [clockRoundAt, Protocol.HealConfig.opening_slot, Protocol.HealConfig.round_of]
    exact Nat.div_mul_le_self _ _
  exact lt_of_le_of_lt (Protocol.proposal_time_mono S.E hslot) hlt

/-- Round zero acts at `6Δ`. -/
private theorem ip_a_zero (S : Setup V) : S.a 0 = 6 * S.E.Δ := by
  show 4 * S.E.Δ * ((S.hc.opening_slot 0 : Nat) : Time) + 6 * S.E.Δ = 6 * S.E.Δ
  simp [Protocol.HealConfig.opening_slot]

/-- The outage boundary is past round zero's action: the formation margin puts
it one delay past a round action, and every round action is at least `6Δ`. -/
theorem six_delta_lt_b0 (S : Setup V) (s : Round) (b0 : Time)
    (hmargin : FormationMargin S s b0) : 6 * S.E.Δ < b0 := by
  have ha : S.a (s + 1) = 4 * S.E.Δ * ((S.hc.opening_slot (s + 1) : Nat) : Time)
      + 6 * S.E.Δ := rfl
  have hnn : (0 : Time) ≤ 4 * S.E.Δ * ((S.hc.opening_slot (s + 1) : Nat) : Time) :=
    Int.mul_nonneg (ip_four_delta_pos _ S.E.Δ_pos).le (Int.natCast_nonneg _)
  refine lt_of_lt_of_le ?_ hmargin
  rw [ha]
  exact ip_six_lt _ _ hnn S.E.Δ_pos

/-- **The read's own clock round is a ladder round.** Addendum 34 rulings 12 and
15: the inclusion condition keeps its lower bound at the round ACTION and its
horizon bound at the round OPENING, and the retention bound sits at the round's
G2 domain, `opening r - Δ`. Two of the three are consequences of the read being
inside the window — the round has opened at or before the read
(`opening_le_clockRound`), so its opening is inside the horizon, and its G2
domain is one delay earlier still, hence at or before `cap ≤ b1 + Δ`. The third,
`b0 ≤ S.a r`, is the guard: it fails exactly on the round that straddles `b0` in
the action sense. -/
theorem domainIncluded_clockRound (S : Setup V) (rho : NamedRun V) (b0 b1 cap t : Time)
    (hb0pos : 6 * S.E.Δ < b0) (hb0 : b0 ≤ t) (hcap : t ≤ cap)
    (hcapb1 : cap ≤ b1 + S.E.Δ) (hhor : t ≤ rho.horizon)
    (hpb : b0 ≤ S.a (clockRoundAt S t)) :
    DomainIncluded S rho b0 (clockRoundAt S t) ∧
      domain S.E S.hc (clockRoundAt S t) .g2 ≤ b1 + S.E.Δ := by
  have ht0 : (0 : Time) ≤ t :=
    le_trans (ip_nonneg_of_six_lt _ _ S.E.Δ_pos hb0pos) hb0
  have hopen : opening S.E S.hc (clockRoundAt S t) ≤ t := opening_le_clockRound S t ht0
  have hpos : 0 < clockRoundAt S t := by
    rcases Nat.eq_zero_or_pos (clockRoundAt S t) with hz | hp
    · rw [hz, ip_a_zero] at hpb
      exact absurd hpb (not_le.mpr hb0pos)
    · exact hp
  have hg2 : domain S.E S.hc (clockRoundAt S t) .g2 <
      opening S.E S.hc (clockRoundAt S t) := by
    have hd : domain S.E S.hc (clockRoundAt S t) .g2
        = opening S.E S.hc (clockRoundAt S t) + (-1) * S.E.Δ := rfl
    rw [hd]
    exact ip_sub_delta_lt _ _ S.E.Δ_pos
  refine ⟨⟨hpos, hpb, ?_⟩, ?_⟩
  · rw [domain_g1_eq_opening]; exact hopen.trans hhor
  · exact le_trans hg2.le (le_trans hopen (hcap.trans hcapb1))

/-- Every read is strictly before the action of the round after its own. -/
theorem lt_a_succ_clockRound (S : Setup V) (t : Time) : t < S.a (clockRoundAt S t + 1) :=
  lt_of_lt_of_le (clockRound_lt_opening_succ S t)
    (by rw [← domain_g1_eq_opening]; exact FrameForward.domain_le_a S _ .g1)


/-- ** 10's round floor at a read.** Every read of the window has a clock
round at or above `s + 1`: the formation margin puts round `s + 1`'s action
strictly before `b0`, and `b0 ≤ t < opening (clockRoundAt S t + 1)`. -/
theorem succ_le_clockRound (S : Setup V) (s : Round) (b0 t : Time)
    (hmargin : FormationMargin S s b0) (hb0 : b0 ≤ t) : s + 1 ≤ clockRoundAt S t := by
  have ha : S.a (s + 1) < b0 := ip_lt_of_add_delta_le _ _ _ S.E.Δ_pos hmargin
  have hop : opening S.E S.hc (s + 1) ≤ S.a (s + 1) := by
    rw [← domain_g1_eq_opening]; exact FrameForward.domain_le_a S _ .g1
  have hlt : opening S.E S.hc (s + 1) < opening S.E S.hc (clockRoundAt S t + 1) :=
    lt_of_le_of_lt hop (lt_of_lt_of_le (lt_of_lt_of_le ha hb0)
      (le_of_lt (clockRound_lt_opening_succ S t)))
  exact Nat.lt_succ_iff.mp (ip_opening_lt S hlt)

#print axioms readRound_readAt
#print axioms clockRoundAt_eq
#print axioms six_delta_lt_b0
#print axioms domainIncluded_clockRound
#print axioms succ_le_clockRound


/-- ** 10's round floor from a round opening.** Every read at or after
round `q`'s opening has a clock round at or above `q`. -/
theorem succ_le_clockRound_of_opening (S : Setup V) (q : Round) (t : Time)
    (hop : opening S.E S.hc q ≤ t) : q ≤ clockRoundAt S t :=
  Nat.lt_succ_iff.mp (ip_opening_lt S
    (lt_of_le_of_lt hop (clockRound_lt_opening_succ S t)))

private theorem ip_lt_add_two : ∀ x d : Int, 0 < d → x < x + 2 * d := by
  intro x d hd; omega

private theorem ip_le_add_delta : ∀ a d : Int, 0 < d → a ≤ a + d := by
  intro a d hd; omega

private theorem ip_formation_eq (S : Setup V) (k : Round) :
    formationConfirmationTime S k = opening S.E S.hc k + 2 * S.E.Δ := by
  unfold formationConfirmationTime Protocol.support_cutoff opening
    Protocol.proposal_time Env.t slotStart
  ring

/-- A round's formation cutoff is `2Δ` past its own opening. -/
theorem opening_lt_formation (S : Setup V) (k : Round) :
    opening S.E S.hc k < formationConfirmationTime S k := by
  rw [ip_formation_eq]
  exact ip_lt_add_two _ _ S.E.Δ_pos

#print axioms succ_le_clockRound_of_opening
#print axioms opening_lt_formation







/-- **The `sg` disjunction BEFORE the boundary**, from round `s + 1`'s formation
cutoff onwards. The split is the pre-boundary twin of `sg_at_clockRound`: a read
whose own round ACTS before the outage is covered by 15's pre-boundary
frame premise, and a
read whose own round acts at or after `b0` sits in a DOMAIN-INCLUDED round —
its opening is before `b0`, so its G2 domain is well inside `b1 + Δ` — and the
ladder's own `sg` field covers it. -/
theorem sg_before_boundary (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (s : Round) (Pn : NamedBlock V) (hexec : OutageExecution S rho b0 b1)
    (hinv : ∀ r : Round, DomainIncluded S rho b0 r → domain S.E S.hc r .g2 ≤ b1 + S.E.Δ →
      RoundInvariant S rho b0 Pn r)
    (hframes : PreBoundaryFrames S rho b0 s Pn.erase)
    (w : V) (hw : w ∈ rho.honest) (u : Time)
    (hlo : formationConfirmationTime S (s + 1) ≤ u) (hhi : u ≤ b0) :
    Block.Preceq Pn.erase
        (NamedRun.readAt S rho (domain S.E S.hc (clockRoundAt S u) .g1) w).st.core.F ∨
      ∃ raw : Block V,
        (DecoupledConsensusModel.Protocol.readFrame
            (NamedRun.readAt S rho (domain S.E S.hc (clockRoundAt S u) .g1) w).cache
            (NamedRun.readAt S rho (domain S.E S.hc (clockRoundAt S u) .g1) w).st.core.toHealing
            (clockRoundAt S u)).g2 = some (some raw) ∧ Block.Preceq Pn.erase raw := by
  have hopen1 : opening S.E S.hc (s + 1) ≤ u :=
    (opening_lt_formation S (s + 1)).le.trans hlo
  have hq : s + 1 ≤ clockRoundAt S u := succ_le_clockRound_of_opening S (s + 1) u hopen1
  by_cases hpb : b0 ≤ S.a (clockRoundAt S u)
  · obtain ⟨-, hb01, hb1⟩ := hexec.interval
    have hu0 : (0 : Time) ≤ u := (base_opening_nonneg S (s + 1)).trans hopen1
    have hopen : opening S.E S.hc (clockRoundAt S u) ≤ u := opening_le_clockRound S u hu0
    have hg2lt : domain S.E S.hc (clockRoundAt S u) .g2 <
        opening S.E S.hc (clockRoundAt S u) := by
      have hd : domain S.E S.hc (clockRoundAt S u) .g2
          = opening S.E S.hc (clockRoundAt S u) + (-1) * S.E.Δ := rfl
      rw [hd]
      exact ip_sub_delta_lt _ _ S.E.Δ_pos
    have hdi : DomainIncluded S rho b0 (clockRoundAt S u) := by
      refine ⟨Nat.lt_of_lt_of_le (Nat.succ_pos s) hq, hpb, ?_⟩
      rw [domain_g1_eq_opening]
      exact hopen.trans ((hhi.trans hb01).trans hb1)
    have hb1r : domain S.E S.hc (clockRoundAt S u) .g2 ≤ b1 + S.E.Δ :=
      hg2lt.le.trans (hopen.trans ((hhi.trans hb01).trans
        (ip_le_add_delta _ _ S.E.Δ_pos)))
    exact (hinv (clockRoundAt S u) hdi hb1r).sg w hw
  · exact hframes w hw (clockRoundAt S u) hq (not_le.mp hpb)

#print axioms sg_before_boundary

/-! ## 7c. The prepared read

`confirmationReadAt S rho w u` is not the `readAt` of any time: it sets the clock
to the cutoff slot and runs one cache preparation. The preparation aligns the
cache to the read's OWN clock round and completes only pending slots, at their
own domain; it never rewrites a slot that is already saved, and it clips against
the same finalized block the strict read already clipped against. `setClock`
writes only `t` and `s`, which no fork-choice projection reads. So every saved
slot of the read's own round survives the staging unchanged.

This is `FrameForward.frame_phase_checkpoint_eq`'s argument at a general time
instead of at `S.a r`. Its cache algebra is private there, so it is copied. -/

private theorem ip_clip_compatible (g F : Block V) :
    Block.compatible (clipGrade g F) F = true := by
  induction g with
  | genesis => simp [clipGrade, Block.compatible, Protocol.preceq_genesis]
  | node p s root gv gsv ats v ih =>
    simp only [clipGrade]
    split
    · assumption
    · exact ih

private theorem ip_compatible_ancestors {A B C D : Block V}
    (hAB : Block.Preceq A B) (hCD : Block.Preceq C D)
    (hBD : Block.compatible B D = true) : Block.compatible A C = true := by
  simp only [Block.compatible, Bool.or_eq_true] at hBD
  rcases hBD with hBD | hDB
  · exact Block.compatible_of_preceq_common (Block.preceq_trans hAB hBD) hCD
  · exact Block.compatible_of_preceq_common hAB (Block.preceq_trans hCD hDB)

private theorem ip_clip_after_advance (B F G : Block V) (hFG : Block.Preceq F G) :
    clipGrade (clipGrade B F) G = clipGrade B G := by
  apply Block.preceq_antisymm
  · apply (q10_retained_prefix B G _ (ip_clip_compatible (clipGrade B F) G)).mpr
    exact Block.preceq_trans (q10_clip_preceq (clipGrade B F) G) (q10_clip_preceq B F)
  · apply (q10_retained_prefix (clipGrade B F) G _ (ip_clip_compatible B G)).mpr
    apply (q10_retained_prefix B F _ ?_).mpr
    · exact q10_clip_preceq B G
    · exact ip_compatible_ancestors (Block.preceq_self _) hFG (ip_clip_compatible B G)

private theorem ip_clip_result_advance (F G : Block V) (hFG : Block.Preceq F G)
    (x : Option (Option (Block V))) : clipResult G (clipResult F x) = clipResult G x := by
  cases x with
  | none => rfl
  | some root =>
    cases root with
    | none => rfl
    | some B =>
      simp only [clipResult, Option.map_some]
      exact congrArg (fun C => some (some C)) (ip_clip_after_advance B F G hFG)

private theorem ip_phase_clip_frame (F : Block V) (f : Frame V) (p : Phase) :
    phaseResult (clipFrame F f) p = clipResult F (phaseResult f p) := by
  cases p <;> rfl

private theorem ip_cacheAtRound_clip (F : Block V) (c : Cache V) (r : Round) :
    cacheAtRound (clipCache F c) r = clipFrame F (cacheAtRound c r) := by
  unfold cacheAtRound clipCache
  split_ifs <;> rfl

private theorem ip_phase_clip (F : Block V) (c : Cache V) (r : Round) (p : Phase) :
    phaseResult (cacheAtRound (clipCache F c) r) p =
      clipResult F (phaseResult (cacheAtRound c r) p) := by
  rw [ip_cacheAtRound_clip, ip_phase_clip_frame]

private theorem ip_cacheAtRound_align_self (c : Cache V) (r : Round) :
    cacheAtRound (alignRound c r) r = cacheAtRound c r := by
  by_cases h1 : r = c.round
  · rw [show alignRound c r = c by unfold alignRound; rw [if_pos h1]]
  · by_cases h2 : r = c.round + 1
    · rw [show alignRound c r = ⟨r, c.next, pendingFrame⟩ by
        unfold alignRound; rw [if_neg h1, if_pos h2]]
      subst h2
      simp [cacheAtRound]
    · rw [show alignRound c r = ⟨r, pendingFrame, pendingFrame⟩ by
        unfold alignRound; rw [if_neg h1, if_neg h2]]
      simp [cacheAtRound, h1, h2]

private theorem ip_complete_one_other (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) (t : Time) (p q : Phase) (f : Frame V) (h : q ≠ p) :
    phaseResult (completeOne E hc st r t p f) q = phaseResult f q := by
  unfold completeOne
  split
  · rfl
  · split
    · cases p <;> cases q <;> simp_all only [putPhase, phaseResult, ne_eq, not_true_eq_false]
    · rfl

private theorem ip_complete_one_some (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) (t : Time) (p q : Phase) (f : Frame V)
    (h : phaseResult f p ≠ none) :
    phaseResult (completeOne E hc st r t q f) p = phaseResult f p := by
  by_cases hpq : p = q
  · subst hpq
    unfold completeOne
    split
    · rfl
    · rename_i hnone
      exact absurd hnone h
  · exact ip_complete_one_other E hc st r t q p f hpq

private theorem ip_complete_frame_some (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) (t : Time) (p : Phase) (f : Frame V)
    (h : phaseResult f p ≠ none) :
    phaseResult (completeFrame E hc st r t f) p = phaseResult f p := by
  have h2 := ip_complete_one_some E hc st r t p .g2 f h
  have h2' : phaseResult (completeOne E hc st r t .g2 f) p ≠ none := by
    rw [h2]; exact h
  have h1 := ip_complete_one_some E hc st r t p .g1 _ h2'
  have h1' : phaseResult (completeOne E hc st r t .g1
      (completeOne E hc st r t .g2 f)) p ≠ none := by
    rw [h1, h2]; exact h
  have h0 := ip_complete_one_some E hc st r t p .g0 _ h1'
  unfold completeFrame
  rw [h0, h1, h2]

private theorem ip_phase_completed_cache (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (c : Cache V) (t : Time) (r : Round) (p : Phase)
    (h : phaseResult (cacheAtRound c r) p ≠ none) :
    phaseResult (cacheAtRound ⟨c.round, completeFrame E hc st c.round t c.current,
        completeFrame E hc st (c.round + 1) t c.next⟩ r) p =
      phaseResult (cacheAtRound c r) p := by
  by_cases h1 : r = c.round
  · have e1 : cacheAtRound ⟨c.round, completeFrame E hc st c.round t c.current,
        completeFrame E hc st (c.round + 1) t c.next⟩ r =
        completeFrame E hc st c.round t c.current := by
      simp [cacheAtRound, h1]
    have e2 : cacheAtRound c r = c.current := by simp [cacheAtRound, h1]
    rw [e2] at h
    rw [e1, e2]
    exact ip_complete_frame_some E hc st c.round t p c.current h
  · by_cases h2 : r = c.round + 1
    · have e1 : cacheAtRound ⟨c.round, completeFrame E hc st c.round t c.current,
          completeFrame E hc st (c.round + 1) t c.next⟩ r =
          completeFrame E hc st (c.round + 1) t c.next := by
        simp [cacheAtRound, h2]
      have e2 : cacheAtRound c r = c.next := by simp [cacheAtRound, h2]
      rw [e2] at h
      rw [e1, e2]
      exact ip_complete_frame_some E hc st (c.round + 1) t p c.next h
    · have e1 : cacheAtRound ⟨c.round, completeFrame E hc st c.round t c.current,
          completeFrame E hc st (c.round + 1) t c.next⟩ r = pendingFrame := by
        simp [cacheAtRound, h1, h2]
      have e2 : cacheAtRound c r = pendingFrame := by simp [cacheAtRound, h1, h2]
      rw [e1, e2]

/-- **The staged read keeps every saved slot of its own clock round.** -/
theorem frame_phase_prepared_eq (S : Setup V) (rho : NamedRun V) (v : V) (r : Round)
    (p : Phase) (u : Time) (hround : S.hc.round_of (S.E.slotOf u) = r)
    (root : Option (Block V))
    (hbase : phaseResult (DecoupledConsensusModel.Protocol.readFrame
        (NamedRun.stateBeforeTime S rho u v).cache
        (NamedRun.stateBeforeTime S rho u v).st.core.toHealing r) p = some root) :
    phaseResult (DecoupledConsensusModel.Protocol.readFrame (confirmationReadAt S rho v u).cache
      (confirmationReadAt S rho v u).st.core.toHealing r) p = some root := by
  set before := NamedRun.stateBeforeTime S rho u v with hbefore
  have hclipped := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho u v).2.2
  have hraw : phaseResult (cacheAtRound before.cache r) p = some root := by
    rw [← hbase]
    change _ = phaseResult (clipFrame before.st.core.F (cacheAtRound before.cache r)) p
    rw [← ip_cacheAtRound_clip, hclipped]
  have hsome : phaseResult (cacheAtRound before.cache r) p ≠ none := by
    rw [hraw]; exact Option.some_ne_none _
  have hprep : phaseResult (cacheAtRound (preparedCache S before u) r) p =
      clipResult before.st.core.F (phaseResult (cacheAtRound before.cache r) p) := by
    unfold preparedCache NamedActionReads.preparedCache onPhaseTick
    rw [hround]
    set al := alignRound before.cache r with hal
    have halign : cacheAtRound al r = cacheAtRound before.cache r :=
      ip_cacheAtRound_align_self before.cache r
    have hsome' : phaseResult (cacheAtRound al r) p ≠ none := by
      rw [halign]; exact hsome
    change phaseResult (cacheAtRound (clipCache before.st.core.F
      ⟨al.round, completeFrame S.E S.hc before.st.core.toHealing al.round u al.current,
        completeFrame S.E S.hc before.st.core.toHealing (al.round + 1) u al.next⟩) r) p = _
    rw [ip_phase_clip,
      ip_phase_completed_cache S.E S.hc before.st.core.toHealing al u r p hsome', halign]
  have key : phaseResult (cacheAtRound before.cache r) p =
      clipResult before.st.core.F (phaseResult (cacheAtRound before.cache r) p) := by
    conv_lhs => rw [← hclipped]
    exact ip_phase_clip _ _ _ _
  rw [hraw] at key
  change phaseResult (clipFrame before.st.core.F
    (cacheAtRound (preparedCache S before u) r)) p = some root
  rw [ip_phase_clip_frame, hprep, hraw, ip_clip_result_advance _ _ (Block.preceq_self _)]
  exact key.symm

/-- The staged read's own clock round is the cutoff slot's round: `setClock`
writes the slot outright. -/
theorem readRound_confirmationReadAt (S : Setup V) (rho : NamedRun V) (v : V) (u : Time) :
    readRound S (confirmationReadAt S rho v u) = clockRoundAt S u := rfl

/-- `setClock` writes only the clock, which no fork-choice projection reads. -/
theorem prepared_tree_eq (S : Setup V) (rho : NamedRun V) (v : V) (u : Time) :
    Protocol.get_filtered_block_tree
        (confirmationReadAt S rho v u).st.core.toHealing.toFG =
      Protocol.get_filtered_block_tree
        (NamedRun.stateBeforeTime S rho u v).st.core.toHealing.toFG := rfl

theorem prepared_root_eq (S : Setup V) (rho : NamedRun V) (v : V) (u : Time) :
    Protocol.get_fg_root (confirmationReadAt S rho v u).st.core.toHealing.toFG =
      Protocol.get_fg_root
        (NamedRun.stateBeforeTime S rho u v).st.core.toHealing.toFG := rfl

#print axioms frame_phase_prepared_eq



/-- **A read of the straddling round is before the first included round's
action.** That round is the least one acting at or after `b0`, so it is strictly
above the read's clock round, and the read is strictly before the next opening,
which is at or before that round's action. No inclusion condition and no
retention bound are involved — L4's band and entry history at that round come
from `NamedFirstCheckpoint`'s own `hentry0` and
`NamedConflictingCarrierBand.intrinsic_conflicting_carrier_band`, neither of
which needs the round invariant. -/
theorem lt_a_of_preBoundary (S : Setup V) (b0 : Time) (r0 : Round) (hb : b0 ≤ S.a r0)
    (t : Time) (hstr : S.a (clockRoundAt S t) < b0) : t < S.a r0 := by
  have hq : clockRoundAt S t < r0 := by
    by_contra hc
    exact absurd (le_trans hb (a_mono S (Nat.le_of_not_lt hc))) (not_le.mpr hstr)
  refine lt_of_lt_of_le (clockRound_lt_opening_succ S t)
    (le_trans (ip_opening_mono S (Nat.succ_le_of_lt hq)) ?_)
  rw [← domain_g1_eq_opening]
  exact FrameForward.domain_le_a S r0 .g1


/-- **No round is domain-included once the horizon open items short of the first
one.** `hmin` puts every candidate at or above ``, and round openings are
monotone, so ``'s opening being past the horizon rules them all out. This is
what makes the round-invariant hypothesis of L11 vacuously available on a run
that ends before the outage's first round opens. -/
theorem domainIncluded_false_of_short (S : Setup V) (rho : NamedRun V) (b0 : Time)
    (r0 : Round) (hmin : ∀ q : Round, 0 < q → b0 ≤ S.a q → r0 ≤ q)
    (hshort : ¬ domain S.E S.hc r0 .g1 ≤ rho.horizon) (r : Round)
    (hr : DomainIncluded S rho b0 r) : False := by
  refine hshort (le_trans ?_ hr.2.2)
  rw [domain_g1_eq_opening, domain_g1_eq_opening]
  exact ip_opening_mono S (hmin r hr.1 hr.2.1)

#print axioms lt_a_of_preBoundary
#print axioms domainIncluded_false_of_short


/-- **Arm 1 of the `sg` field, forward.** Addendum 34 14 exempts a reader
by its FINALIZED block instead of by its FG root. The finalized block IS
monotone along one node's run (`Proofs.NamedRuntime.stateBefore_F_mono`), and anything
at or below it is at or below the FG root
(`NonInterference.preceq_fg_root_of_preceq_F`, which spends P6: the FG root is
`J` under the cascade gate and `F` otherwise, and `F ⪯ J`). -/
theorem preceq_fg_root_of_preceq_F_fwd (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (v : V) (P : Block V) (c0 c1 : Time)
    (hc : c0 ≤ c1) (h : Block.Preceq P (NamedRun.stateBeforeTime S rho c0 v).st.core.F) :
    Block.Preceq P (Protocol.get_fg_root
      (NamedRun.stateBeforeTime S rho c1 v).st.core.toHealing.toFG) := by
  refine preceq_fg_root_of_preceq_F S rho c1 v P (Block.preceq_trans h ?_)
  rw [strict_read_eq_index S rho sch.sorted c0, strict_read_eq_index S rho sch.sorted c1]
  exact Proofs.NamedRuntime.stateBefore_F_mono S rho v (strict_lengths_mono rho hc)


/-- **Arm 1 of the `sg` field, forward, in the FINALIZED-block form.** The same
monotonicity step as `preceq_fg_root_of_preceq_F_fwd`, blocked one step earlier:
the stable output compares against the reader's own finalized block, not against
its FG root. -/
theorem preceq_F_fwd (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (v : V) (P : Block V) (c0 c1 : Time)
    (hc : c0 ≤ c1) (h : Block.Preceq P (NamedRun.stateBeforeTime S rho c0 v).st.core.F) :
    Block.Preceq P (NamedRun.stateBeforeTime S rho c1 v).st.core.F := by
  refine Block.preceq_trans h ?_
  rw [strict_read_eq_index S rho sch.sorted c0, strict_read_eq_index S rho sch.sorted c1]
  exact Proofs.NamedRuntime.stateBefore_F_mono S rho v (strict_lengths_mono rho hc)

#print axioms preceq_fg_root_of_preceq_F_fwd
#print axioms preceq_F_fwd



/-! ### Arm 2, forward from the opening read -/

/-- **Arm 2, forward.** The round-`r` G2 slot the invariant sees at the round's
opening read is still there at every later read of the same round, clipped, and
still covers the protected prefix. -/
theorem strict_g2_of_opening (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) (w : V) (hw : w ∈ rho.honest)
    (r : Round) (hr : 0 < r) (P : Block V) (T : Time)
    (hopen : opening S.E S.hc r < T) (hstrict : T ≤ opening S.E S.hc (r + 1))
    (hhor : opening S.E S.hc r ≤ rho.horizon) (raw : Block V)
    (hg2 : (DecoupledConsensusModel.Protocol.readFrame
        (NamedRun.readAt S rho (domain S.E S.hc r .g1) w).cache
        (NamedRun.readAt S rho (domain S.E S.hc r .g1) w).st.core.toHealing r).g2 =
      some (some raw))
    (hPraw : Block.Preceq P raw)
    (hcompat : Block.compatible P (NamedRun.stateBeforeTime S rho T w).st.core.F = true) :
    ∃ raw' : Block V,
      (DecoupledConsensusModel.Protocol.readFrame (NamedRun.stateBeforeTime S rho T w).cache
          (NamedRun.stateBeforeTime S rho T w).st.core.toHealing r).g2 =
        some (some raw') ∧ Block.Preceq P raw' := by
  have hg1open : domain S.E S.hc r .g1 = opening S.E S.hc r := domain_g1_eq_opening S r
  have hg2dom : domain S.E S.hc r .g2 < opening S.E S.hc r := by
    have hd : domain S.E S.hc r .g2 = opening S.E S.hc r + (-1) * S.E.Δ := rfl
    rw [hd]
    exact ip_sub_delta_lt _ _ S.E.Δ_pos
  have hhor2 : domain S.E S.hc r .g2 ≤ rho.horizon := le_trans hg2dom.le hhor
  have hopenlt : opening S.E S.hc r + 1 ≤ opening S.E S.hc (r + 1) :=
    le_trans (ip_succ_le_of_lt _ _ hopen) hstrict
  have eo := FrameCompleted.frame_g2_completed_in_round S rho core w hw r hr
    (opening S.E S.hc r + 1) (ip_lt_succ_of_lt _ _ hg2dom) hopenlt hhor2
  have et := FrameCompleted.frame_g2_completed_in_round S rho core w hw r hr T
    (lt_trans hg2dom hopen) hstrict hhor2
  rw [readAt_eq_succ, hg1open, eo] at hg2
  obtain ⟨raw0, hraw0, hclip⟩ := Option.map_eq_some_iff.mp (Option.some_inj.mp hg2)
  have hPraw0 : Block.Preceq P raw0 :=
    Block.preceq_trans hPraw (hclip ▸ clip_preceq raw0 _)
  refine ⟨clipGrade raw0 (NamedRun.stateBeforeTime S rho T w).st.core.F, ?_, ?_⟩
  · rw [et, hraw0]
    rfl
  · exact clip_retains _ _ _ hcompat hPraw0


/-- **Conjuncts 1 and 2 at a read, from the `sg` disjunction at its own clock
round.** The round invariant is not needed here — only the disjunction, which
the ladder supplies inside the window and 15's `PreBoundaryFrames`
supplies on the straddling round. -/
theorem read_conjuncts_of_sg (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) (w : V) (hw : w ∈ rho.honest)
    (P : Block V) (r : Round) (hr : 0 < r) (t : Time) (ht0 : (0 : Time) ≤ t)
    (hopen : opening S.E S.hc r ≤ t) (hstrict : t + 1 ≤ opening S.E S.hc (r + 1))
    (hhor : t ≤ rho.horizon)
    (hsg : Block.Preceq P
        (NamedRun.readAt S rho (domain S.E S.hc r .g1) w).st.core.F ∨
      ∃ raw : Block V,
        (DecoupledConsensusModel.Protocol.readFrame
            (NamedRun.readAt S rho (domain S.E S.hc r .g1) w).cache
            (NamedRun.readAt S rho (domain S.E S.hc r .g1) w).st.core.toHealing r).g2 =
          some (some raw) ∧ Block.Preceq P raw)
    (hfg : Block.Preceq P (Protocol.get_fg_root
        (NamedRun.readAt S rho t w).st.core.toHealing.toFG) ∨
      P ∈ Protocol.get_filtered_block_tree
        (NamedRun.readAt S rho t w).st.core.toHealing.toFG)
    (hcompat : Block.compatible P (NamedRun.readAt S rho t w).st.core.F = true) :
    (Block.Preceq P (Protocol.get_fg_root
        (NamedRun.readAt S rho t w).st.core.toHealing.toFG) ∨
      ∃ G, activeG2 S (NamedRun.readAt S rho t w) = some G ∧ Block.Preceq P G) ∧
    Block.Preceq P (sgRoot S (NamedRun.readAt S rho t w)) := by
  have hround : readRound S (NamedRun.readAt S rho t w) = r := by
    rw [readRound_readAt S rho core.toNamedScheduleWellFormed w hw t ht0 hhor]
    exact clockRoundAt_eq S t r ht0 hopen (ip_lt_of_succ_le _ _ hstrict)
  have hfrt : readFrameAt S (NamedRun.readAt S rho t w) =
      DecoupledConsensusModel.Protocol.readFrame (NamedRun.readAt S rho t w).cache
        (NamedRun.readAt S rho t w).st.core.toHealing r := by
    show DecoupledConsensusModel.Protocol.readFrame _ _ (readRound S (NamedRun.readAt S rho t w)) = _
    rw [hround]
  rcases hfg with hroot | hmem
  · exact ⟨Or.inl hroot, preceq_sgRoot_of_fg_root S _ hroot⟩
  rcases hsg with hopenF | ⟨raw, hg2, hPrawo⟩
  · rw [readAt_eq_succ, domain_g1_eq_opening] at hopenF
    have hroot : Block.Preceq P (Protocol.get_fg_root
        (NamedRun.readAt S rho t w).st.core.toHealing.toFG) := by
      rw [readAt_eq_succ]
      exact preceq_fg_root_of_preceq_F_fwd S rho core.toNamedScheduleWellFormed w P _ _
        (ip_succ_le_succ_of_le _ _ hopen) hopenF
    exact ⟨Or.inl hroot, preceq_sgRoot_of_fg_root S _ hroot⟩
  have hcompat' : Block.compatible P
      (NamedRun.stateBeforeTime S rho (t + 1) w).st.core.F = true := by
    rw [← readAt_eq_succ]; exact hcompat
  obtain ⟨raw', hg2', hPraw'⟩ := strict_g2_of_opening S rho core w hw r hr P (t + 1)
    (ip_lt_succ_of_le _ _ hopen) hstrict (hopen.trans hhor) raw hg2 hPrawo hcompat'
  have hg2read : (DecoupledConsensusModel.Protocol.readFrame (NamedRun.readAt S rho t w).cache
      (NamedRun.readAt S rho t w).st.core.toHealing r).g2 = some (some raw') := by
    rw [readAt_eq_succ]; exact hg2'
  have hmem' : P ∈ Protocol.get_filtered_block_tree
      (NamedRun.stateBeforeTime S rho (t + 1) w).st.core.toHealing.toFG := by
    rw [← readAt_eq_succ]; exact hmem
  have hhorg1 : domain S.E S.hc r .g1 ≤ rho.horizon := by
    rw [domain_g1_eq_opening]; exact hopen.trans hhor
  obtain ⟨root1, hg1, hProot1⟩ := q10_g1_slot_of_g2_slot S rho core w hw r hr (t + 1)
    (by rw [domain_g1_eq_opening]; exact ip_lt_succ_of_le _ _ hopen) hstrict hhorg1
    hg2' hPraw' hmem'
  refine ⟨Or.inr ?_, ?_⟩
  · refine activeG2_covers S (NamedRun.readAt S rho t w) ?_ hmem hPraw'
    rw [hfrt]; exact hg2read
  · refine preceq_sgRoot_of_g1 S (NamedRun.readAt S rho t w) ?_ hmem hProot1
    rw [hfrt, readAt_eq_succ]; exact hg1

#print axioms strict_g2_of_opening
#print axioms read_conjuncts_of_sg

/-- The active G2 candidate is a member of the reader's filtered tree. -/
private theorem ip_activeG2_mem (S : Setup V) (n : NamedNodeState V) {G : Block V}
    (hG : activeG2 S n = some G) :
    G ∈ Protocol.get_filtered_block_tree n.st.core.toHealing.toFG := by
  rw [activeG2_eq] at hG
  obtain ⟨raw, _, hA⟩ := Option.bind_eq_some_iff.mp hG
  exact NamedProposalParent.activePrefix_mem _ raw G hA

/-- **The same two conjuncts at a STAGED support-cutoff read.** The staged read's
`g1` and `g2` slots are the strict read's (`frame_phase_prepared_eq`), and its
fork-choice projections are the strict read's (`prepared_tree_eq`,
`prepared_root_eq`). -/
theorem candidate_at_cutoff_of_sg (S : Setup V) (rho : NamedRun V)
    (core : NamedAdmissibleCore S rho) (w : V) (hw : w ∈ rho.honest)
    (P : Block V) (r : Round) (hr : 0 < r) (u : Time) (hround : clockRoundAt S u = r)
    (hopen : opening S.E S.hc r < u) (hstrict : u ≤ opening S.E S.hc (r + 1))
    (hhor : opening S.E S.hc r ≤ rho.horizon)
    (hsg : Block.Preceq P
        (NamedRun.readAt S rho (domain S.E S.hc r .g1) w).st.core.F ∨
      ∃ raw : Block V,
        (DecoupledConsensusModel.Protocol.readFrame
            (NamedRun.readAt S rho (domain S.E S.hc r .g1) w).cache
            (NamedRun.readAt S rho (domain S.E S.hc r .g1) w).st.core.toHealing r).g2 =
          some (some raw) ∧ Block.Preceq P raw)
    (hfg : Block.Preceq P (Protocol.get_fg_root
        (NamedRun.stateBeforeTime S rho u w).st.core.toHealing.toFG) ∨
      P ∈ Protocol.get_filtered_block_tree
        (NamedRun.stateBeforeTime S rho u w).st.core.toHealing.toFG)
    (hcompat : Block.compatible P (NamedRun.stateBeforeTime S rho u w).st.core.F = true) :
    Block.Preceq P (sgRoot S (confirmationReadAt S rho w u)) ∧
    ∀ G, activeG2 S (confirmationReadAt S rho w u) = some G → Block.Preceq P G := by
  have hfrp : readFrameAt S (confirmationReadAt S rho w u) =
      DecoupledConsensusModel.Protocol.readFrame (confirmationReadAt S rho w u).cache
        (confirmationReadAt S rho w u).st.core.toHealing r := by
    show DecoupledConsensusModel.Protocol.readFrame _ _ (readRound S (confirmationReadAt S rho w u)) = _
    rw [readRound_confirmationReadAt, hround]
  have hrootcase : Block.Preceq P (Protocol.get_fg_root
      (NamedRun.stateBeforeTime S rho u w).st.core.toHealing.toFG) →
      Block.Preceq P (sgRoot S (confirmationReadAt S rho w u)) ∧
      ∀ G, activeG2 S (confirmationReadAt S rho w u) = some G → Block.Preceq P G := by
    intro hroot
    have hroot' : Block.Preceq P (Protocol.get_fg_root
        (confirmationReadAt S rho w u).st.core.toHealing.toFG) := by
      rw [prepared_root_eq]; exact hroot
    refine ⟨preceq_sgRoot_of_fg_root S _ hroot', ?_⟩
    intro G hG
    exact Block.preceq_trans hroot'
      (Proofs.Records.preceq_get_fg_root_of_mem_filtered (ip_activeG2_mem S _ hG))
  rcases hfg with hroot | hmem
  · exact hrootcase hroot
  rcases hsg with hopenF | ⟨raw, hg2, hPrawo⟩
  · refine hrootcase ?_
    rw [readAt_eq_succ, domain_g1_eq_opening] at hopenF
    exact preceq_fg_root_of_preceq_F_fwd S rho core.toNamedScheduleWellFormed w P _ _
      (ip_succ_le_of_lt _ _ hopen) hopenF
  obtain ⟨raw', hg2', hPraw'⟩ := strict_g2_of_opening S rho core w hw r hr P u hopen
    hstrict hhor raw hg2 hPrawo hcompat
  have hhorg1 : domain S.E S.hc r .g1 ≤ rho.horizon := by
    rw [domain_g1_eq_opening]; exact hhor
  obtain ⟨root1, hg1, hProot1⟩ := q10_g1_slot_of_g2_slot S rho core w hw r hr u
    (by rw [domain_g1_eq_opening]; exact hopen) hstrict hhorg1 hg2' hPraw' hmem
  have hmemp : P ∈ Protocol.get_filtered_block_tree
      (confirmationReadAt S rho w u).st.core.toHealing.toFG := by
    rw [prepared_tree_eq]; exact hmem
  have hg1p := frame_phase_prepared_eq S rho w r .g1 u hround _ hg1
  have hg2p := frame_phase_prepared_eq S rho w r .g2 u hround _ hg2'
  refine ⟨?_, ?_⟩
  · refine preceq_sgRoot_of_g1 S (confirmationReadAt S rho w u) ?_ hmemp hProot1
    rw [hfrp]; exact hg1p
  · intro G' hG'
    obtain ⟨G'', hG'', hPG''⟩ := activeG2_covers S (confirmationReadAt S rho w u)
      (by rw [hfrp]; exact hg2p) hmemp hPraw'
    rw [hG''] at hG'
    rw [← Option.some_inj.mp hG']
    exact hPG''

#print axioms candidate_at_cutoff_of_sg



/-- The `sg` disjunction at the read's own clock round, from the ladder when the
round is included and from `PreBoundaryFrames` when it is the straddling one. -/
theorem sg_at_clockRound (S : Setup V) (rho : NamedRun V) (b0 b1 cap : Time)
    (s : Round) (Pn : NamedBlock V) (hmargin : FormationMargin S s b0)
    (hinv : ∀ r : Round, DomainIncluded S rho b0 r → domain S.E S.hc r .g2 ≤ b1 + S.E.Δ →
      RoundInvariant S rho b0 Pn r)
    (hframes : PreBoundaryFrames S rho b0 s Pn.erase)
    (hcapb1 : cap ≤ b1 + S.E.Δ) (w : V) (hw : w ∈ rho.honest) (t : Time)
    (hb0 : b0 ≤ t) (hcap : t ≤ cap) (hhor : t ≤ rho.horizon) :
    Block.Preceq Pn.erase
        (NamedRun.readAt S rho (domain S.E S.hc (clockRoundAt S t) .g1) w).st.core.F ∨
      ∃ raw : Block V,
        (DecoupledConsensusModel.Protocol.readFrame
            (NamedRun.readAt S rho (domain S.E S.hc (clockRoundAt S t) .g1) w).cache
            (NamedRun.readAt S rho (domain S.E S.hc (clockRoundAt S t) .g1) w).st.core.toHealing
            (clockRoundAt S t)).g2 = some (some raw) ∧ Block.Preceq Pn.erase raw := by
  have hb0pos : 6 * S.E.Δ < b0 := six_delta_lt_b0 S s b0 hmargin
  by_cases hpb : b0 ≤ S.a (clockRoundAt S t)
  · obtain ⟨hinc, hb1r⟩ := domainIncluded_clockRound S rho b0 b1 cap t hb0pos hb0 hcap
      hcapb1 hhor hpb
    exact (hinv (clockRoundAt S t) hinc hb1r).sg w hw
  · 
    -- now, so the straddling round needs no projection at all.
    exact hframes w hw (clockRoundAt S t)
      (succ_le_clockRound S s b0 t hmargin hb0) (not_le.mp hpb)

#print axioms sg_at_clockRound

/-- **Obligation C, discharged.** The two frame conjuncts at every staged
support-cutoff read of the window. -/
theorem candidateReadCoverage_of_invariant
    (S : Setup V) (rho : NamedRun V) (b0 b1 cap : Time) (s : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hmargin : FormationMargin S s b0) (hsleep : OutageSleepyThroughout S rho)
    (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hheld0 : ∀ w ∈ rho.honest, Pn ∈ (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (hinv : ∀ r : Round, DomainIncluded S rho b0 r → domain S.E S.hc r .g2 ≤ b1 + S.E.Δ →
      RoundInvariant S rho b0 Pn r)
    (hframes : PreBoundaryFrames S rho b0 s Pn.erase)
    (hcapb1 : cap ≤ b1 + S.E.Δ)
    (hanchor : ∀ t : Time, b0 ≤ t → t ≤ cap → t ≤ rho.horizon →
      S.a (clockRoundAt S t) < b0 →
        ∃ r : Round, IntrinsicConflictingCarrierBand S rho Pn r ∧
          IntrinsicHighEntryHistory S rho Pn r ∧ t < S.a r) :
    CandidateReadCoverage S rho b0 cap Pn.erase := by
  intro w hw u hb0 hcap hhor _hpos hcut
  have hb0pos : 6 * S.E.Δ < b0 := six_delta_lt_b0 S s b0 hmargin
  have hu0 : (0 : Time) ≤ u :=
    le_trans (ip_nonneg_of_six_lt _ _ S.E.Δ_pos hb0pos) hb0
  have hsg := sg_at_clockRound S rho b0 b1 cap s Pn hmargin hinv hframes hcapb1 w hw u
    hb0 hcap hhor
  -- L4 at the cutoff read.
  have hL4 : Pn ∈ (NamedRun.stateBeforeTime S rho u w).st.bodies ∧
      (Block.Preceq Pn.erase (Protocol.get_fg_root
          (NamedRun.stateBeforeTime S rho u w).st.core.toHealing.toFG) ∨
        Pn.erase ∈ Protocol.get_filtered_block_tree
          (NamedRun.stateBeforeTime S rho u w).st.core.toHealing.toFG) ∧
      Block.compatible Pn.erase (NamedRun.stateBeforeTime S rho u w).st.core.F = true := by
    by_cases hpb : b0 ≤ S.a (clockRoundAt S u)
    · obtain ⟨hinc, hb1r⟩ := domainIncluded_clockRound S rho b0 b1 cap u hb0pos hb0 hcap
        hcapb1 hhor hpb
      have hI := hinv (clockRoundAt S u) hinc hb1r
      exact fg_noninterference_after_boundary S rho b0 b1 s (clockRoundAt S u + 1) Pn
        hexec hslash hmargin hsleep hscope hno
        (band_step S rho b0 b1 s (clockRoundAt S u) Pn hexec hslash hmargin hsleep hno hI)
        (entry_history_step S rho b0 b1 s (clockRoundAt S u) Pn hexec hslash hmargin
          hsleep hno hI) hheld0 w hw u hb0 (le_of_lt (lt_a_succ_clockRound S u))
    · obtain ⟨rL, hbandL, hentryL, hult⟩ := hanchor u hb0 hcap hhor (not_le.mp hpb)
      exact fg_noninterference_after_boundary S rho b0 b1 s rL Pn hexec hslash hmargin
        hsleep hscope hno hbandL hentryL hheld0 w hw u hb0 (le_of_lt hult)
  refine candidate_at_cutoff_of_sg S rho hexec.core w hw Pn.erase (clockRoundAt S u) ?_ u
    rfl (opening_lt_support_cutoff S u hu0 hcut)
    (le_of_lt (clockRound_lt_opening_succ S u))
    (le_trans (opening_le_clockRound S u hu0) hhor) hsg hL4.2.1 hL4.2.2
  exact Nat.lt_of_lt_of_le (Nat.succ_pos s) (succ_le_clockRound S s b0 u hmargin hb0)

#print axioms candidateReadCoverage_of_invariant

/-- **L11.** -/
theorem entryPrefixOutputs_upTo_of_invariant
    (S : Setup V) (rho : NamedRun V) (b0 b1 cap : Time) (s : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hmargin : FormationMargin S s b0) (hsleep : OutageSleepyThroughout S rho)
    (hscope : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hheld0 : ∀ w ∈ rho.honest, Pn ∈ (NamedRun.stateBeforeTime S rho b0 w).st.bodies)
    (hinv : ∀ r : Round, DomainIncluded S rho b0 r → domain S.E S.hc r .g2 ≤ b1 + S.E.Δ →
      RoundInvariant S rho b0 Pn r)
    (hframes : PreBoundaryFrames S rho b0 s Pn.erase)
    (hcapb1 : cap ≤ b1 + S.E.Δ)
    (hanchor : ∀ t : Time, b0 ≤ t → t ≤ cap → t ≤ rho.horizon →
      S.a (clockRoundAt S t) < b0 →
        ∃ r : Round, IntrinsicConflictingCarrierBand S rho Pn r ∧
          IntrinsicHighEntryHistory S rho Pn r ∧ t < S.a r)
    (hstabcov : ReadStableCoverage S rho b0 cap Pn.erase)
    (hcandcov : CandidateReadCoverage S rho b0 cap Pn.erase) :
    EntryPrefixOutputsUpTo S rho b0 cap Pn.erase := by
  intro w hw t hb0 hcap hhor
  have hb0pos : 6 * S.E.Δ < b0 := six_delta_lt_b0 S s b0 hmargin
  have ht0 : (0 : Time) ≤ t :=
    le_trans (ip_nonneg_of_six_lt _ _ S.E.Δ_pos hb0pos) hb0
  have hsg := sg_at_clockRound S rho b0 b1 cap s Pn hmargin hinv hframes hcapb1 w hw t
    hb0 hcap hhor
  -- L4 at the read.
  have hL4 : Pn ∈ (NamedRun.readAt S rho t w).st.bodies ∧
      (Block.Preceq Pn.erase (Protocol.get_fg_root
          (NamedRun.readAt S rho t w).st.core.toHealing.toFG) ∨
        Pn.erase ∈ Protocol.get_filtered_block_tree
          (NamedRun.readAt S rho t w).st.core.toHealing.toFG) ∧
      Block.compatible Pn.erase (NamedRun.readAt S rho t w).st.core.F = true := by
    by_cases hpb : b0 ≤ S.a (clockRoundAt S t)
    · obtain ⟨hinc, hb1r⟩ := domainIncluded_clockRound S rho b0 b1 cap t hb0pos hb0 hcap
        hcapb1 hhor hpb
      have hI := hinv (clockRoundAt S t) hinc hb1r
      exact fg_noninterference_after_boundary_readAt S rho b0 b1 s (clockRoundAt S t + 1)
        Pn hexec hslash hmargin hsleep hscope hno
        (band_step S rho b0 b1 s (clockRoundAt S t) Pn hexec hslash hmargin hsleep hno hI)
        (entry_history_step S rho b0 b1 s (clockRoundAt S t) Pn hexec hslash hmargin
          hsleep hno hI) hheld0 w hw t hb0 (lt_a_succ_clockRound S t)
    · obtain ⟨rL, hbandL, hentryL, htlt⟩ := hanchor t hb0 hcap hhor (not_le.mp hpb)
      exact fg_noninterference_after_boundary_readAt S rho b0 b1 s rL Pn hexec hslash
        hmargin hsleep hscope hno hbandL hentryL hheld0 w hw t hb0 htlt
  have hmain := read_conjuncts_of_sg S rho hexec.core w hw Pn.erase (clockRoundAt S t)
    (Nat.lt_of_lt_of_le (Nat.succ_pos s) (succ_le_clockRound S s b0 t hmargin hb0)) t ht0
    (opening_le_clockRound S t ht0)
    (ip_succ_le_of_lt _ _ (clockRound_lt_opening_succ S t)) hhor hsg hL4.2.1 hL4.2.2
  -- Conjunct 3, from the boundary stable record and its retention.
  have hstable3 : Block.Preceq Pn.erase
      (Protocol.get_stable (NamedRun.readAt S rho t w).st.core) :=
    preceq_get_stable_of_cases _ (hstabcov w hw t hb0 hcap hhor) hL4.2.2
  refine ⟨hmain.1, hmain.2, hstable3, ?_⟩
  -- Conjunct 4.
  intro u hb0u hut B hcw
  obtain ⟨i, he, hpos, hcut, hcand⟩ := hcw
  have hprefix : NamedRun.stateBefore S rho i w = NamedRun.stateBeforeTime S rho u w :=
    Proofs.NamedRuntime.tick_prefix_eq_strict S rho hexec.core.sorted hexec.core.nodup he
  rw [hprefix] at hcand
  have hcov := hcandcov w hw u hb0u (le_trans hut hcap) (le_trans hut hhor) hpos hcut
  exact candidate_covers S (confirmationReadAt S rho w u) (S.E.slotOf u - 1) hcand
    hcov.1 hcov.2

#print axioms entryPrefixOutputs_upTo_of_invariant

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
