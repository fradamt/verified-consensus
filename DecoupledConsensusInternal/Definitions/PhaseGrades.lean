module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusModel.Execution.Node
public import DecoupledConsensusModel.Protocol.Grades

@[expose] public section

/-!
# Phase-grade vocabulary for the height cone 

One vocabulary replaces the prior absolute predicates `Protocol.G2/G1/G0` and
the prior selectors `fresh_anchor`, `grade2_block`, `g0_clear`, `get_sg_vote`,
`fg_source` in every restated statement of the cone:

* `phaseGrade E hc gv F r p B`: the executable relative grade of `B` in phase
  `p` of round `r` at the reader whose grade view is `gv` and finalized chain
  is `F`, with that phase's early and late cutoffs of the adopted schedule
  (G2 = (T−5Δ, T−Δ), G1 = (T−4Δ, T−2Δ), G0 = (T−3Δ, T−3Δ)).
* `phaseRoot`: the frozen raw root of that phase (deepest graded block of the
  processed tree), before clipping.
* node-level reads through the contract the actual duty uses: `nodeAnchor`,
  `nodeQ2`, `nodeClear`, `nodeRawG2`, `nodeSGVote`, `nodeFGSource`.

the prior absolute-majority grade implies the relative grade at the same
inputs; the prior lemma layer is restated against this vocabulary (see the
records README, table "36 restatements").
-/


namespace DecoupledConsensusModel.Internal.PhaseGrades
open Execution DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Executable relative grade of `B` in phase `p` of round `r`. -/
def phaseGrade (E : Env V) (hc : Protocol.HealConfig) (gv : Protocol.GradeView V)
    (F : Block V) (r : Round) (p : Phase) (B : Block V) : Bool :=
  gradeBool E gv F hc.η_SG r (early E hc r p) (late E hc r p) B

/-- Frozen raw root of phase `p`: the deepest graded block of the tree. -/
def phaseRoot (E : Env V) (hc : Protocol.HealConfig) (gv : Protocol.GradeView V)
    (F : Block V) (r : Round) (p : Phase) : Option (Block V) :=
  freezeRoot E gv F hc.η_SG r (early E hc r p) (late E hc r p)

/-- Positive supporters of `B` in phase `p` (the `Pos` side). -/
def phaseSupporters (E : Env V) (hc : Protocol.HealConfig) (gv : Protocol.GradeView V)
    (F : Block V) (r : Round) (p : Phase) (B : Block V) : Finset V :=
  Finset.univ.filter fun v => positive gv F hc.η_SG r (early E hc r p) (late E hc r p) v B = true

/-- Opponents of `B` in phase `p` (the `Opp` side). -/
def phaseOpponents (E : Env V) (hc : Protocol.HealConfig) (gv : Protocol.GradeView V)
    (F : Block V) (r : Round) (p : Phase) (B : Block V) : Finset V :=
  Finset.univ.filter fun v => opposing gv F hc.η_SG r (early E hc r p) (late E hc r p) v B = true

/-- Store-level grade at a named store's own view and finalized chain. -/
def storeGrade (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (r : Round) (p : Phase) (B : Block V) : Bool :=
  phaseGrade E hc st.core.toHealing.gradeView st.core.F r p B

def storeRoot (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (r : Round) (p : Phase) : Option (Block V) :=
  phaseRoot E hc st.core.toHealing.gradeView st.core.F r p

/-- The contract read the actual duty performs on a prepared node. -/
def nodeRead (S : Setup V) (n : NamedNodeState V) (r : Round) : Protocol.GradeRead V :=
  (NamedProfile.gradeContract n.cache).read S.E S.hc n.st.core.toHealing r

/-- The deepest completed G1 block (FG-root fallback); always a block. -/
def nodeAnchor (S : Setup V) (n : NamedNodeState V) (r : Round) : Block V :=
  (nodeRead S n r).anchor

/-- The completed, clipped, active G2 candidate, if any. -/
def nodeQ2 (S : Setup V) (n : NamedNodeState V) (r : Round) : Option (Block V) :=
  (nodeRead S n r).Q2

/-- Clearance against the completed G0 root. -/
def nodeClear (S : Setup V) (n : NamedNodeState V) (r : Round) (B : Block V) : Bool :=
  (nodeRead S n r).clear B

def nodeRawG2 (S : Setup V) (n : NamedNodeState V) (r : Round) : Prop :=
  (nodeRead S n r).rawG2

/-- The SG vote and FG source the actual duty computes from the same read. -/
def nodeSGVote (S : Setup V) (n : NamedNodeState V) (r : Round) : Block V :=
  Protocol.get_sg_vote_with (NamedProfile.gradeContract n.cache) S.E S.hc
    n.st.core.toHealing r
    (Protocol.grade2_block_with (NamedProfile.gradeContract n.cache) S.E S.hc
      n.st.core.toHealing r)

def nodeFGSource (S : Setup V) (n : NamedNodeState V) (r : Round) : Option (Block V) :=
  Protocol.fg_source_with (NamedProfile.gradeContract n.cache) S.E S.hc
    n.st.core.toHealing r
    (Protocol.grade2_block_with (NamedProfile.gradeContract n.cache) S.E S.hc
      n.st.core.toHealing r)


/-- Honest batch alignment for the relative rule: every honest validator awake
in the window has its latest interpreted head covering `Can`. This replaces
`Optimistic.BatchAligned` / `BatchCompatible` in the G3 restatements. -/
def BatchCovers (E : Env V) (hc : Protocol.HealConfig) (gv : Protocol.GradeView V)
    (F : Block V) (Hon : Finset V) (r : Round) (Can : Block V) : Prop :=
  ∀ v ∈ Hon, ∀ u ∈ DecoupledConsensusModel.Protocol.interpretedInputs gv F hc.η_SG r (late E hc r .g2) v,
    localCovers gv u.confirmed Can = true

end DecoupledConsensusModel.Internal.PhaseGrades

end
