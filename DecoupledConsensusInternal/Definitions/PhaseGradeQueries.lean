module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.ProposalSources
public import DecoupledConsensusInternal.Definitions.PhaseGrades
public import DecoupledConsensusInternal.Definitions.ActionSources
public import DecoupledConsensusInternal.ModelVocabulary.Execution.NamedAdmissible

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation


namespace DecoupledConsensusModel.Internal.PhaseGrades
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol Execution Proofs.HealingSurface
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Shared premises -/


/-- Honest validators with an interpreted (body-ready) input in the window
by `cutoff` at this reader. The cutoff is the phase cutoff the query needs
: the LATE cutoff of a phase for exclusion arguments (honest
late-present voters with aligned heads all oppose an off-chain block), the
EARLY cutoff for a supporter argument (an honest early-present voter is a
supporter or an opponent, so support above opposition forces an honest
supporter). Presence by an earlier cutoff implies presence by a later one. -/
def honestPresent (hc : Protocol.HealConfig) (gv : Protocol.GradeView V)
    (F : Block V) (Hon : Finset V) (r : Round) (cutoff : Time) : Finset V :=
  Hon.filter fun v =>
    (DecoupledConsensusModel.Protocol.interpretedInputs gv F hc.η_SG r cutoff v).Nonempty

/-- Faulty weight below honest present weight at `cutoff` (the reader-level
form of the awake-window majority). Replaces `HonestWeightMajority`, `E.m`
and `3f < W`. -/
def WindowMajorityAt (E : Env V) (hc : Protocol.HealConfig) (gv : Protocol.GradeView V)
    (F : Block V) (Hon : Finset V) (r : Round) (cutoff : Time) : Prop :=
  E.electorate.weightOf (Finset.univ \ Hon) <
    E.electorate.weightOf (honestPresent hc gv F Hon r cutoff)

/-- Every honest interpreted head by `cutoff` is compatible with `B`
(replaces `BatchCompatible`). -/
def BatchCompatibleAt (hc : Protocol.HealConfig) (gv : Protocol.GradeView V)
    (F : Block V) (Hon : Finset V) (r : Round) (cutoff : Time) (B : Block V) : Prop :=
  ∀ v ∈ Hon, ∀ u ∈ DecoupledConsensusModel.Protocol.interpretedInputs gv F hc.η_SG r cutoff v,
    ∀ head, u.confirmed = some head.root → Block.find? gv.T head.root = some head →
      Block.compatible B head = true


/-- The latest honest interpreted head by `cutoff` that is in the reader's tree
is below `Can` (replaces `BatchAligned`; the pre-rewrite `rootOnCan` scope at the
author's latest input). -/
def BatchAlignedAt (hc : Protocol.HealConfig) (gv : Protocol.GradeView V)
    (F : Block V) (Hon : Finset V) (r : Round) (cutoff : Time) (Can : Block V) : Prop :=
  ∀ v ∈ Hon, ∀ u ∈ DecoupledConsensusModel.Protocol.interpretedInputs gv F hc.η_SG r cutoff v,
    (∀ u' ∈ DecoupledConsensusModel.Protocol.interpretedInputs gv F hc.η_SG r cutoff v, u'.round ≤ u.round) →
    ∀ head, u.confirmed = some head.root → Block.find? gv.T head.root = some head →
      Block.Preceq head Can

/-- The cutoff that governs every saved root of round `r` at once: the G0
cutoff `T − 3Δ` is the earliest of the three, so presence there implies
presence at every phase cutoff. Node-level queries over anchor, Q2 and
clear together use it. -/
abbrev allPhasesCutoff (E : Env V) (hc : Protocol.HealConfig) (r : Round) : Time :=
  late E hc r .g0

/-- Reader shorthand. -/
abbrev readAt (S : Setup V) (rho : Run V) (t : Time) (v : V) : NamedNodeState V :=
  NamedRun.stateBeforeTime S rho t v

abbrev filteredTree (n : NamedNodeState V) : Finset (Block V) :=
  Protocol.get_filtered_block_tree n.st.core.toHealing.toFG

/-! ## Store-level grade facts (rows 1, 3, 5, 6, 7, 8, 9, 20, 25, 32) -/

/-- Row 1 (`grade_eq_false_off_can`): with honest heads aligned at `Can` and a
window majority, a block off `Can` has no grade in any phase. -/
def Q1_grade_eq_false_off_can (S : Setup V) : Prop :=
  ∀ (gv : Protocol.GradeView V) (F : Block V) (Hon : Finset V) (r : Round)
    (Can D : Block V) (p : Phase),
    BatchAlignedAt S.hc gv F Hon r (late S.E S.hc r p) Can →
    WindowMajorityAt S.E S.hc gv F Hon r (late S.E S.hc r p) →
    Block.preceq D Can = false → phaseGrade S.E S.hc gv F r p D = false


/-- Row 3 (`g0_clear_of_preceq`): a block below the aligned `Can` is clear at a
node whose G0 root came from that batch. Stated at the node read. -/
def Q3_g0_clear_of_preceq (S : Setup V) (rho : Run V) : Prop :=
  ∀ (v : V) (t : Time) (Hon : Finset V) (r : Round) (Can B : Block V),
    let n := readAt S rho t v
    BatchAlignedAt S.hc n.st.core.toHealing.gradeView n.st.core.F Hon r
      (allPhasesCutoff S.E S.hc r) Can →
    WindowMajorityAt S.E S.hc n.st.core.toHealing.gradeView n.st.core.F Hon r
      (allPhasesCutoff S.E S.hc r) →
    Block.preceq B Can = true → nodeClear S n r B = true

/-- Row 5 (`G2_imp_G1`): at one store the G2 grade implies the G1 grade
(early window grows, late window shrinks). Pure. -/
def Q5_G2_imp_G1 (E : Env V) (hc : Protocol.HealConfig) : Prop :=
  ∀ (gv : Protocol.GradeView V) (F : Block V) (r : Round) (B : Block V),
    phaseGrade E hc gv F r .g2 B = true → phaseGrade E hc gv F r .g1 B = true

/-- Row 6 (`G1_G2_compatible`): two graded blocks at one store are compatible.
Pure: a validator is a supporter of at most one of two conflicting blocks and
an opponent of the other. -/
def Q6_G1_G2_compatible (E : Env V) (hc : Protocol.HealConfig) : Prop :=
  ∀ (gv : Protocol.GradeView V) (F : Block V) (r : Round) (B B' : Block V),
    phaseGrade E hc gv F r .g1 B = true → phaseGrade E hc gv F r .g2 B' = true →
    Block.compatible B B' = true


/-- Row 7 (`grade_eq_false_of_conflicts_of_faulty_lt_m`): a block conflicting
with a batch-compatible `B` under a window majority has no grade. -/
def Q7_grade_eq_false_of_conflicts (E : Env V) (hc : Protocol.HealConfig) : Prop :=
  ∀ (gv : Protocol.GradeView V) (F : Block V) (Hon : Finset V) (r : Round)
    (B B' : Block V) (p : Phase),
    BatchCompatibleAt hc gv F Hon r (late E hc r p) B →
    WindowMajorityAt E hc gv F Hon r (late E hc r p) →
    Block.conflicts B' B = true → phaseGrade E hc gv F r p B' = false


/-- Rows 8 and 9 (`g0_clear_of_batchCompatible[_of_faulty_lt_m]`): the G0 root
of a batch-compatible reader is compatible with `B`, so `B` is clear. One query
replaces both; the `3f < W` and `E.m` premises become the window majority. -/
def Q8_g0_clear_of_batchCompatible (S : Setup V) (rho : Run V) : Prop :=
  ∀ (v : V) (t : Time) (Hon : Finset V) (r : Round) (B : Block V),
    let n := readAt S rho t v
    BatchCompatibleAt S.hc n.st.core.toHealing.gradeView n.st.core.F Hon r
      (allPhasesCutoff S.E S.hc r) B →
    WindowMajorityAt S.E S.hc n.st.core.toHealing.gradeView n.st.core.F Hon r
      (allPhasesCutoff S.E S.hc r) →
    nodeClear S n r B = true

/-- Rows 20 and 25 (`G1_honest_named_supporter`, `G2_honest_supporter`): a graded
block has an honest window voter whose interpreted head covers it, with that
input inside the phase's early window. One query over the phase. -/
def Q20_graded_has_honest_supporter (E : Env V) (hc : Protocol.HealConfig) : Prop :=
  ∀ (gv : Protocol.GradeView V) (F : Block V) (Hon : Finset V) (r : Round)
    (B : Block V) (p : Phase),
    WindowMajorityAt E hc gv F Hon r (early E hc r p) → phaseGrade E hc gv F r p B = true →
    ∃ v ∈ Hon, ∃ u ∈ DecoupledConsensusModel.Protocol.interpretedInputs gv F hc.η_SG r (early E hc r p) v,
      ∃ head : Block V, u.confirmed = some head.root ∧
        Block.find? gv.T head.root = some head ∧ Block.Preceq B head

/-- Row 32 (`g0_clear_of_direct_support`): a block whose G0-phase supporters
outweigh its opponents is clear at the node whose G0 root came from that view. -/
def Q32_g0_clear_of_support (S : Setup V) (rho : Run V) : Prop :=
  ∀ (v : V) (t : Time) (r : Round) (B : Block V),
    let n := readAt S rho t v
    phaseGrade S.E S.hc n.st.core.toHealing.gradeView n.st.core.F r .g0 B = true →
    nodeClear S n r B = true

/-! ## Selector facts at a node (rows 2, 4, 10, 11, 17, 19, 26, 30, 31, 33, 34) -/

/-- Row 2 (`fresh_anchor_preceq`): with honest heads aligned at `Can`, a window
majority and the FG root below `Can`, the anchor is below `Can`. -/
def Q2_anchor_preceq (S : Setup V) (rho : Run V) : Prop :=
  ∀ (v : V) (t : Time) (Hon : Finset V) (r : Round) (Can : Block V),
    let n := readAt S rho t v
    BatchAlignedAt S.hc n.st.core.toHealing.gradeView n.st.core.F Hon r
      (allPhasesCutoff S.E S.hc r) Can →
    WindowMajorityAt S.E S.hc n.st.core.toHealing.gradeView n.st.core.F Hon r
      (allPhasesCutoff S.E S.hc r) →
    Block.Preceq (Protocol.get_fg_root n.st.core.toHealing.toFG) Can →
    Block.Preceq (nodeAnchor S n r) Can

/-- Row 4 (`get_sg_root_preceq_of_aligned`): same premises give the SG root below `Can`. -/
def Q4_sgRoot_preceq_of_aligned (S : Setup V) (rho : Run V) : Prop :=
  ∀ (v : V) (t : Time) (Hon : Finset V) (r : Round) (Can : Block V),
    let n := readAt S rho t v
    BatchAlignedAt S.hc n.st.core.toHealing.gradeView n.st.core.F Hon r
      (allPhasesCutoff S.E S.hc r) Can →
    WindowMajorityAt S.E S.hc n.st.core.toHealing.gradeView n.st.core.F Hon r
      (allPhasesCutoff S.E S.hc r) →
    Block.Preceq (Protocol.get_fg_root n.st.core.toHealing.toFG) Can →
    Block.Preceq (Protocol.get_sg_root_with (NamedProfile.gradeContract n.cache)
      S.E S.hc n.st.core.toHealing r) Can

/-- Row 10 (`grade2_preceq_fresh_anchor`): the active G2 candidate is below the anchor. -/
def Q10_Q2_preceq_anchor (S : Setup V) (rho : Run V) : Prop :=
  ∀ (v : V) (t : Time) (r : Round) (Q : Block V),
    let n := readAt S rho t v
    nodeQ2 S n r = some Q → Block.preceq Q (nodeAnchor S n r) = true


/-- Row 11 (`activeG2_preceq_sgVote`): the active G2 candidate is below the SG
vote. Tightened at.

the prior form quantified over an arbitrary validator at an arbitrary read time,
which the cache cannot support. The selector walks up from the anchor, so the
row rests on `Q2 ⪯ anchor`, which is row Q10; row Q10 reads the round's G1 and
G2 frame slots, and those are `some` only at an honest node, only for a
positive round, only after the G1 domain tick has actually happened, and only
while the run still reaches that tick. The frame stays addressable only up to
the round action, which fixes the upper bound on `t`.

Nothing here is cross-tick stability. Both slots are read at the one store `t`,
and `q10_g1_of_g2_freeze` carries the node's own G2 freeze to its own G1 tick.
The premises are exactly `grade2_preceq_anchor_at_read`'s. -/
def Q11_Q2_preceq_sgVote (S : Setup V) (rho : Run V) : Prop :=
  NamedAdmissibleCore S rho →
  ∀ (v : V) (t : Time) (r : Round) (Q : Block V), v ∈ rho.honest → 0 < r →
    domain S.E S.hc r .g1 < t → t ≤ S.a r →
    domain S.E S.hc r .g1 ≤ rho.horizon →
    let n := readAt S rho t v
    nodeQ2 S n r = some Q → Block.preceq Q (nodeSGVote S n r) = true


/-- Row 17 (`graded_value_lifts_source`): a block G2-graded at the reader's
strict G2-domain read (the store the frame freezes from) and still active at
a later read of the same round, once all three phases are closed, sits below
the FG source of that later read. The G2 root is the deepest graded block of
the capture store (rows 22, 23), the frame persists up to clipping (row 21),
and the source is that root or a clear block above it. Corrected at 
: the prior form graded the later store itself. -/
def Q17_graded_lifts_source (S : Setup V) (rho : Run V) : Prop :=
  NamedScheduleWellFormed S rho →
  ∀ (v : V) (t : Time) (r : Round) (C Q : Block V), v ∈ rho.honest → 0 < r →
    domain S.E S.hc r .g0 ≤ t → t < opening S.E S.hc (r + 1) → t ≤ rho.horizon →
    let n := NamedRun.readAt S rho t v
    C ∈ filteredTree n →
    storeGrade S.E S.hc (readAt S rho (domain S.E S.hc r .g2) v).st r .g2 C = true →
    nodeFGSource S n r = some Q → Block.preceq C Q = true

/-- Row 19 (`recoveryActionCarrier_compatible_of_g0`): a clear active block is
compatible with the SG vote. -/
def Q19_clear_compatible_sgVote (S : Setup V) (rho : Run V) : Prop :=
  ∀ (v : V) (t : Time) (r : Round) (A : Block V),
    let n := readAt S rho t v
    A ∈ filteredTree n → nodeClear S n r A = true →
    Block.compatible A (nodeSGVote S n r) = true

/-- Row 26 (`selectedActionG2_G1_at_read_of_active`): a source's active G2
candidate at its action is G1-graded at every honest reader from the G1 domain
on, when active there. Instance of graded delivery. -/
def Q26_actionQ2_G1_at_reader (S : Setup V) (rho : Run V) : Prop :=
  NamedAdmissibleCore S rho → NamedHealthyPrefixDelivery S rho rho.horizon →
  ∀ (r : Round) (p w : V), p ∈ rho.honest → w ∈ rho.honest →
    ∀ (Q : Block V) (read : Time), domain S.E S.hc r .g1 ≤ read →
      nodeQ2 S (actionReadAt S rho p r) r = some Q →
      Q ∈ filteredTree (readAt S rho read w) →
      storeGrade S.E S.hc (readAt S rho read w).st r .g1 Q = true


/-- Row 30 (`seedGradedBlock_preceq_actionCarrier_at_store`): a block graded G2
at an honest node's own G2-domain read, and still active at that node's action
read, is below the action's SG vote. Tightened at  on two counts.

First, the vocabulary. the prior form graded `P` at the action read's own live
`gradeView` and `F`, seven delays after the G2 cutoff, while `actionSGBlockAt`
consumes the root the cache froze at that cutoff. That mismatch is what made
the row look like a cross-tick stability problem, and it was an artifact of the
retired raw-grade vocabulary. Grading at the G2-domain read is the Q17
vocabulary of and removes it: the grade and the freeze then read
one store, and `q10_freeze_of_graded` closes the step outright.

Second, soundness. the prior form carried no honesty, admissibility or round
premise, and with none of them the row is not merely unproved. An adversarial
delivery that lands a supporting vote strictly after the G2 freeze tick, still
dated before `late (.g2)`, grades `P` at the later live read while the frozen
root never saw it. Honesty, `0 < r` and the horizon bound are what rule that
out, by making the node's own domain ticks happen.

Two premises beyond the list, both forced by the runtime. `P` must be a
processed block at the G2-domain read, because the frozen root is the deepest
graded member of the tree that tick saw and a block absent from that tree need
not sit below it; callers holding the filtered-tree form get this from the FG
filter's own membership clause. And the horizon bound is at the round action,
`RoundIncluded`'s third part rather than `DomainIncluded`'s: `grade2Block`
returns `none` until `allClosed` holds, whose binding phase is `g0` at
`opening r + Δ`, and the `Q2 ⪯ anchor` step is row Q10 at the round checkpoint,
which is stated under `RoundIncluded`. A row about the round action needs the
run to reach the round action; `FrameForward.domain_le_a` recovers each phase
domain bound from it. -/
def Q30_graded_preceq_actionSGBlock (S : Setup V) (rho : Run V) : Prop :=
  NamedAdmissibleCore S rho →
  ∀ (w : V) (r : Round) (P : Block V), w ∈ rho.honest → 0 < r →
    S.a r ≤ rho.horizon →
    P ∈ (readAt S rho (domain S.E S.hc r .g2) w).st.core.T →
    storeGrade S.E S.hc (readAt S rho (domain S.E S.hc r .g2) w).st r .g2 P = true →
    P ∈ filteredTree (actionReadAt S rho w r) →
    Block.Preceq P (actionSGBlockAt S rho w r)

/-- Row 31 (`actionSGBlockAt_tiers`): the action's SG vote is one of the four
arms of `selectedSGVote`: deepest clear block above the anchor and below
`live_confirmed`; the active G2 candidate; the FG root when raw G2 exists
but no active candidate; the anchor. -/
def Q31_actionSGBlock_tiers (S : Setup V) (rho : Run V) : Prop :=
  ∀ (v : V) (r : Round),
    let n := actionReadAt S rho v r
    let A := nodeAnchor S n r
    (Block.Preceq A (actionSGBlockAt S rho v r) ∧
      Block.Preceq (actionSGBlockAt S rho v r) n.st.core.live_confirmed ∧
      nodeClear S n r (actionSGBlockAt S rho v r) = true) ∨
    (∃ Q, nodeQ2 S n r = some Q ∧ actionSGBlockAt S rho v r = Q) ∨
    (nodeQ2 S n r = none ∧ nodeRawG2 S n r ∧
      actionSGBlockAt S rho v r = Protocol.get_fg_root n.st.core.toHealing.toFG) ∨
    (nodeQ2 S n r = none ∧ ¬ nodeRawG2 S n r ∧ actionSGBlockAt S rho v r = A)

/-- Rows 33 and 34 (`g0_clear_grade2_block`, `g0_clear_get_sg_vote_of_grade2`):
the active G2 candidate and the SG vote are clear. -/
def Q33_Q2_and_sgVote_clear (S : Setup V) (rho : Run V) : Prop :=
  ∀ (v : V) (t : Time) (r : Round) (Q : Block V),
    let n := readAt S rho t v
    nodeQ2 S n r = some Q →
      nodeClear S n r Q = true ∧ nodeClear S n r (nodeSGVote S n r) = true

/-! ## Graded delivery instances (rows 13, 14, 16) -/


/-- The single public graded-delivery query, parameterised by
the delivery cut: the healthy prefix is `cut`, the post-GST global case is
`cut = rho.horizon` after GST (bridge lemma). Source phase `p`, reader phase
`p'`, with `p' ` the next lower phase (g2 → g1, g1 → g0). -/
def GradedDelivery (S : Setup V) (rho : Run V) (cut : Time) (p p' : Phase) : Prop :=
  NamedAdmissibleCore S rho → NamedHealthyPrefixDelivery S rho cut →
  ∀ r, domain S.E S.hc r p' ≤ cut →
    ∀ (src w : V), src ∈ rho.honest → w ∈ rho.honest → ∀ B : Block V,
      storeGrade S.E S.hc (readAt S rho (domain S.E S.hc r p) src).st r p B = true →
      B ∈ filteredTree (readAt S rho (domain S.E S.hc r p') w) →
      storeGrade S.E S.hc (readAt S rho (domain S.E S.hc r p') w).st r p' B = true

/-- Rows 13 and 14: source G2 to reader G1, both reads (the guard-read form is
the same statement at `read ≥ domain g1`, obtained through row 21). -/
def Q13_G2_source_imp_G1_reader (S : Setup V) (rho : Run V) : Prop :=
  GradedDelivery S rho rho.horizon .g2 .g1

/-- Row 16: source G1 to reader G0. -/
def Q16_G1_source_imp_G0_reader (S : Setup V) (rho : Run V) : Prop :=
  GradedDelivery S rho rho.horizon .g1 .g0



/-- The saved frame of round `q` at an inclusive read, as the contract reads
it: the cached frame clipped against the read store's F (`readFrame`,
FrameContract.lean:16). -/
abbrev savedFrame (S : Setup V) (rho : Run V) (t : Time) (v : V) (q : Round) : Frame V :=
  DecoupledConsensusModel.Protocol.readFrame (NamedRun.readAt S rho t v).cache
    (NamedRun.readAt S rho t v).st.core.toHealing q

/-- Rows 21 and 24 (persistence): between the G0 domain of `q` (all three
phases closed) and the opening of `q + 1`, the saved frame changes only by
clipping against the later `F`. -/
def Q21_frame_persists_up_to_clip (S : Setup V) (rho : Run V) : Prop :=
  NamedScheduleWellFormed S rho →
  ∀ (v : V), v ∈ rho.honest → ∀ (q : Round) (t₁ t₂ : Time),
    domain S.E S.hc q .g0 ≤ t₁ → t₁ ≤ t₂ → t₂ < opening S.E S.hc (q + 1) →
    t₂ ≤ rho.horizon →
    savedFrame S rho t₂ v q =
      clipFrame (NamedRun.readAt S rho t₂ v).st.core.F (savedFrame S rho t₁ v q)

/-- Rows 22 and 23 (reflection): at the inclusive read of phase `p`'s domain,
the saved result of `p` is the frozen raw root of the strict read before that
tick, clipped first against that strict read's `F` (phase completion) and
then against the post-tick `F` (`NamedNode.tick` re-clips after the duties,
which may self-process the node's own block at the opening). -/
def Q22_frame_reflects_frozen_root (S : Setup V) (rho : Run V) : Prop :=
  NamedScheduleWellFormed S rho →
  ∀ (v : V), v ∈ rho.honest → ∀ (q : Round) (p : Phase),
    0 < q → domain S.E S.hc q p ≤ rho.horizon →
    let before := NamedRun.stateBeforeTime S rho (domain S.E S.hc q p) v
    let after := NamedRun.readAt S rho (domain S.E S.hc q p) v
    phaseResult (savedFrame S rho (domain S.E S.hc q p) v q) p =
      some ((storeRoot S.E S.hc before.st q p).map
        (fun B => DecoupledConsensusModel.Protocol.clipGrade
          (DecoupledConsensusModel.Protocol.clipGrade B before.st.core.F) after.st.core.F))

/-- Rows 22 and 23, projection form: once all three phases are closed, the
contract read is a function of the saved frame and the current store only:
anchor = active prefix of the saved G1 root (FG-root fallback), Q2 = active
prefix of the saved G2 root, clear = compatibility with the saved G0 root. -/
def Q23_read_is_frame_projection (S : Setup V) (rho : Run V) : Prop :=
  NamedScheduleWellFormed S rho →
  ∀ (v : V), v ∈ rho.honest → ∀ (q : Round) (t : Time),
    0 < q → domain S.E S.hc q .g0 ≤ t → t < opening S.E S.hc (q + 1) → t ≤ rho.horizon →
    let n := NamedRun.readAt S rho t v
    let f := savedFrame S rho t v q
    allClosed f = true ∧
    nodeAnchor S n q = anchor S.E S.hc n.st.core.toHealing q f.g1 ∧
    nodeQ2 S n q = grade2Block n.st.core.toHealing f ∧
    (∀ B, nodeClear S n q B = clear f B)

/-- Q24: every phase domain is a public time, so `NamedScheduleWellFormed.
tick_total` supplies the completion tick that Q21 to Q23 rely on. A schedule
fact about the adopted offsets, proved once; not a premise of the others. -/
def Q24_phase_domains_public (S : Setup V) : Prop :=
  ∀ (q : Round) (p : Phase), 0 < q → PublicTime S (domain S.E S.hc q p)

/-! ## Structures (rows 12, 28, 29): re-typed fields -/

/-- Row 12: the two fields of `FixedHeightRootOpeningParentRun` over the named
reads. Other fields of rows 28 and 29 keep their text through the facade; the
grade-touching fields are restated with the same two shapes below. -/
structure FixedHeightRootOpeningParentQuery (S : Setup V) (rho : Run V) (q : Round) : Prop where
  actionTargetParent : ∀ v ∈ rho.honest,
    Block.Preceq (actionSGBlockAt S rho v (q - 1))
      (Proofs.HealingSurface.proposedParent S rho (S.hc.opening_slot q))
  liveG1Parent : ∀ w ∈ rho.honest, ∀ B,
    storeGrade S.E S.hc (readAt S rho (domain S.E S.hc q .g1) w).st q .g1 B = true →
    Block.Preceq B (Proofs.HealingSurface.proposedParent S rho (S.hc.opening_slot q))


/-- Rows 28 and 29: the grade-touching fields of `SGProposalLifecycleInputs`
and `SGProposalLifecyclePacket`, restated. `proposalAnchor` and
`proposalAnchorG1` collapse to the proposer's anchor at its duty read;
`actionBatchAligned` uses the new `BatchAligned`; `g0ClearAtAction` uses
`nodeClear`. All remaining fields are unchanged text. -/
structure SGProposalLifecycleGradeFields (S : Setup V) (rho : Run V) (r : Round)
    (s : Slot) (A B : Block V) : Prop where
  proposalAnchor : nodeAnchor S (proposerReadAt S rho (s + 1)) (r + 1) = A
  liveG1Parent : ∀ w ∈ rho.honest, ∀ X,
    storeGrade S.E S.hc (readAt S rho (domain S.E S.hc (r + 1) .g1) w).st (r + 1) .g1 X = true →
    Block.Preceq X (Proofs.HealingSurface.proposedParent S rho (s + 1))
  actionBatchAligned : ∀ v ∈ rho.honest,
    let n := actionReadAt S rho v (r + 1)
    BatchAlignedAt S.hc n.st.core.toHealing.gradeView n.st.core.F rho.honest (r + 1)
      (allPhasesCutoff S.E S.hc (r + 1)) B
  g0ClearAtAction : ∀ v ∈ rho.honest,
    nodeClear S (actionReadAt S rho v (r + 1)) (r + 1) B = true

/-! ## Row 27 (`actionCarriersCover_of_liveFloor_batchCompatible_sgRootFloor`) -/

/-- Same shape; `BatchCompatible` is the new one and `BelowOneThird` becomes
the window majority at every honest action read (weaker under full
participation). `ActionCarriersCover` keeps its text through the facade. -/
def Q27_actionCarriersCover (S : Setup V) (rho : Run V) : Prop :=
  ∀ (r : Round) (A : Block V),
    (∀ v ∈ rho.honest, Block.Preceq A (actionReadAt S rho v r).st.core.live_confirmed) →
    (∀ v ∈ rho.honest,
      let n := actionReadAt S rho v r
      Block.Preceq (Protocol.get_sg_root_with (NamedProfile.gradeContract n.cache)
        S.E S.hc n.st.core.toHealing r) A) →
    (∀ v ∈ rho.honest,
      let n := actionReadAt S rho v r
      BatchCompatibleAt S.hc n.st.core.toHealing.gradeView n.st.core.F rho.honest r
        (allPhasesCutoff S.E S.hc r) A) →
    (∀ v ∈ rho.honest,
      let n := actionReadAt S rho v r
      WindowMajorityAt S.E S.hc n.st.core.toHealing.gradeView n.st.core.F rho.honest r
        (allPhasesCutoff S.E S.hc r)) →
    ActionCarriersCover S rho r A

/-! ## Row 18 (`proposedParent_preceq_of_proposerG1`) -/

/-- A block G1-graded and active at the proposer's duty read is below the
proposed parent (the parent is the proposer's anchor or above it). -/
def Q18_proposedParent_preceq_of_proposerG1 (S : Setup V) (rho : Run V) : Prop :=
  ∀ (q : Round) (P : Block V),
    let n := proposerReadAt S rho (S.hc.opening_slot q)
    P ∈ filteredTree n →
    storeGrade S.E S.hc n.st q .g1 P = true →
    Block.Preceq P (Proofs.HealingSurface.proposedParent S rho (S.hc.opening_slot q))

end DecoupledConsensusModel.Internal.PhaseGrades

end
