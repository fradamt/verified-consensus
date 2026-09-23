module
public import DecoupledConsensusModel.Protocol.ForkChoice.Goldfish
public import DecoupledConsensusModel.Protocol.ValidatorClient

@[expose] public section

/-!
# `DecoupledConsensusModel/Protocol/Grades.lean`

Purpose: Section 7, block 2b — the round schedule Gamma, the grade view over the store, resolved_votes, supports, opposes, relative_majority, grade, graded_block, active_prefix, G0_compatible, update_grades, the saved grades and their clip.
Paper: `docs/PROTOCOL.md` `sec:complete-store`; algorithm block: `alg:grades`.

Defines: HealConfig, round_of, opening_slot, a, GradeView, head_covers, Store, gradeView, chain_up, chain_of, deepest_clear, GradeRead, ConfirmationSGCandidate, GradeContract, currentSGVote, clipGrade, rawInputs, bodyReady, interpretedInputs, Token, CleanFrom, Supports, Opposes, token, supportsDecidable, opposesDecidable, rawView, readyView, localCovers, positive, opposing, gradeBool, freezeRoot, activePrefix, anchor, Frame, allClosed, grade2Block, clear, Phase, Phase.earlyOffset, Phase.lateOffset, Phase.domainOffset, opening, early, late, domain, pendingFrame, emptyFrame, phaseResult, putPhase, completeOne, completeFrame, clipResult, clipFrame, Cache, initialCache, alignRound, cacheAtRound, clipCache, onPhaseTick, readFrame, frameGradeRead, frameSGCandidate, frameStableRoot, frameContract.

Read after: `DecoupledConsensusModel.Protocol.ForkChoice.Goldfish`, `DecoupledConsensusModel.Protocol.ValidatorClient`
Read next: `DecoupledConsensusModel.Protocol.Handlers`.

State read: the protocol environment, schedule, store layers, and the view inputs named by the definitions.
State written: the returned store, chain state, record, or view value; pure readers write no state.

Representation notes: Typed Lean records, finite collections, and projections preserve the executable protocol representation. This module states no proof theorem.
MODEL_MAP rows: HealConfig, round_of, opening_slot, a, GradeView, head_covers, Store, gradeView, chain_up, chain_of, deepest_clear, GradeRead, ConfirmationSGCandidate, GradeContract, currentSGVote, clipGrade, rawInputs, bodyReady, interpretedInputs, Token, CleanFrom, Supports, Opposes, token, supportsDecidable, opposesDecidable, rawView, readyView, localCovers, positive, opposing, gradeBool, freezeRoot, activePrefix, anchor, Frame, allClosed, grade2Block, clear, Phase, Phase.earlyOffset, Phase.lateOffset, Phase.domainOffset, opening, early, late, domain, pendingFrame, emptyFrame, phaseResult, putPhase, completeOne, completeFrame, clipResult, clipFrame, Cache, initialCache, alignRound, cacheAtRound, clipCache, onPhaseTick, readFrame, frameGradeRead, frameSGCandidate, frameStableRoot, frameContract.
-/

-- ── from Healing/Schedule.lean ──
section
/-!
# §6.1 Round schedule — `sec:healing-schedule` (PROTOCOL.md `sec:healing-schedule`)

`R ≥ 3`, the opening slot, and the action time `a_r = t_{rR} + 6Δ`.

The selected schedule fixes §3's free timing parameter. `HealConfig` carries
the selected `R ≥ 3` and `η_SG`; `round_of`, `opening_slot`, and `a` are the
retained schedule vocabulary. The grade-runtime cache supplies the saved phase
data consumed by the named protocol.
-/

namespace DecoupledConsensusModel
namespace Protocol

/-- §6.1 the parameters of the graded layer: the round length and the expiry
window (PROTOCOL.md `sec:healing-schedule`, `def:majority-fork-choice`).

`R ≥ 3` is the selected schedule's standing assumption. It is load-bearing:
with `R ≥ 3` the action time
`a_r = t_{rR} + 6Δ` falls in slot `rR + 1`, still inside round `r`, so
`round(Σ.s) = r` holds inside `attest`; and `Γ_r^{−1} = t_{rR} − Δ` is at least
`Δ` after `a_{r−1}`.

`η_SG` is the SG lookback used by `rawInputs` through `latest_window`, and by
`freezeRoot` through `completeOne`; one structure fixes the whole round
schedule. -/
structure HealConfig where
/-- §6.1 `R ≥ 3`: round `r` is the slots `rR … rR+R−1`
  (PROTOCOL.md `sec:sg-schedule`). -/
  R : Nat
  /-- `R ≥ 3`: the support-phase G2
  window opens `5Δ` before a round, and a round-`r` action token delivered
  within `Δ` lands inside round `r+1`'s window only when rounds are at least
  `12Δ` long. The selected schedule uses `R ≥ 3`. -/
  R_ge_three : 3 ≤ R
  /-- §3.3 `η_SG ≥ 1`: the expiry window of the relative rule
  (PROTOCOL.md `def:majority-fork-choice`). Grades ignore it. -/
  η_SG : Round
  /-- §3.3 `η_SG ≥ 1` (PROTOCOL.md `def:majority-fork-choice`). -/
  η_SG_ge_one : 1 ≤ η_SG

namespace HealConfig

variable (hc : HealConfig)

/-- §3.1 `round(s) = ⌊s/R⌋` (PROTOCOL.md `sec:sg-schedule`). The same rule as
`Protocol.round_of`, stated on this layer's parameters. -/
def round_of (s : Slot) : Round :=
  s / hc.R

/-- §3.1 the opening slot `rR` of round `r` (PROTOCOL.md `sec:sg-schedule`). -/
def opening_slot (r : Round) : Slot :=
  r * hc.R

/-- §6.1 `a_r = t_{rR} + 6Δ` (PROTOCOL.md `sec:healing-schedule`): the action time, which is
the opening slot's confirmation evaluation. This is the value §3 left free. -/
def a (Δ : Time) (r : Round) : Time :=
  slotStart Δ (hc.opening_slot r) + 6 * Δ

end HealConfig

section Alignment

variable {V : Type} [DecidableEq V] [Fintype V]

end Alignment

end Protocol
end DecoupledConsensusModel
end

-- ── from Healing/Grades.lean ──
section
/-!
# Grade view substrate

The selected protocol reads a small projection of the store. `GradeView` keeps
that projection independent of the store representation, and `head_covers`
resolves a named head against the processed block tree.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Protocol (SGVote)

structure GradeView (V : Type) where
  /-- The processed block tree serves to resolve block roots. -/
  T : Finset (Block V)
  /-- Receipt times for blocks in the processed tree. -/
  timestamp_block : TimestampMap (Block V)
  /-- The currently filtered block tree. -/
  tree : Finset (Block V)
  /-- The projected strong-gadget vote pool. -/
  sg_votes : Round → Finset (SGVote V)
  /-- Receipt times for projected strong-gadget votes. -/
  timestamp_sg_vote : TimestampMap (SGVote V)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Resolved-head coverage -/

/-- Whether a resolved head names a descendant of `B` in the processed tree. -/
def head_covers (T : Finset (Block V)) (B : Block V) (H : Option BlockId) : Bool :=
  match H with
  | none => false
  | some root =>
    match Block.find? T root with
    | some head => Block.preceq B head
    | none => false

end Protocol
end DecoupledConsensusModel
end

-- ── from Healing/Anchor.lean ──
section
/-!
# The §6 store projection

The selected protocol keeps the §6 store as a thin wrapper over the finality
gadget store. Its grade view is computed when a reader needs it.
-/

namespace DecoupledConsensusModel
namespace Protocol

/-! ## The store -/

structure HealingStore (V : Type) extends toFG : Protocol.FGStore V

namespace HealingStore

variable {V : Type} [DecidableEq V]

/-- The store projected to the fields used by grade-runtime readers. -/
def gradeView (st : HealingStore V) : GradeView V where
  T := st.T
  timestamp_block := st.timestamp_block
  tree := Protocol.get_filtered_block_tree st.toFG
  sg_votes := st.sg_votes
  timestamp_sg_vote := st.timestamp_sg_vote

end HealingStore

end Protocol
end DecoupledConsensusModel
end

-- ── from Healing/GradeContract.lean ──
section
/-!
# Executable grade interfaces

The selected protocol supplies saved phase reads through
`DecoupledConsensusModel.Protocol.frameContract`. The contract is parameterised so the
runtime can use the appropriate phase data at each read.
-/

namespace DecoupledConsensusModel
namespace Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The ancestors of `B`, deepest first, under a fuel bound. -/
def chain_up : Nat → Block V → List (Block V)
  | 0, B => [B]
  | n + 1, B =>
    B :: (match B.parent? with
      | none => []
      | some p => chain_up n p)

/-- The structural ancestor chain used by both clear walks. -/
def chain_of (B : Block V) : List (Block V) :=
  chain_up B.depth B

/-- The deepest clear ancestor in the segment from `floor` to `C`. -/
def deepest_clear (floor : Option (Block V)) (C : Block V)
    (test : Block V → Bool) : Option (Block V) :=
  Block.deepest? ((chain_of C).toFinset.filter (fun B =>
    floor.elim true (fun anchor => Block.preceq anchor B) = true ∧ test B = true))

/-- One local grade read. Decidability is data, not a validity hypothesis. -/
structure GradeRead (V : Type) where
  anchor : Block V
  Q2 : Option (Block V)
  clear : Block V → Bool
  rawG2 : Prop
  rawG2_decidable : Decidable rawG2

/-- The optional SG candidate. The caller keeps every successful Goldfish write
and invokes this selector only when Goldfish eligibility fails. -/
inductive ConfirmationSGCandidate (V : Type) [DecidableEq V] [Fintype V] where
  | optional (select : Env V → HealConfig → HealingStore V → Slot → Option (Block V))

/-- The replaceable parts of the selected grade runtime. -/
structure GradeContract (V : Type) [DecidableEq V] [Fintype V] where
  read : Env V → HealConfig → HealingStore V → Round → GradeRead V
  sgVote : HealingStore V → GradeRead V → Block V
  confirmationSG : ConfirmationSGCandidate V
  /-- The round's stable-record root. -/
  stableRoot : Env V → HealConfig → HealingStore V → Round → Option (Block V)

/-- The shared SG walk and its three fallbacks, on one supplied grade read. -/
def currentSGVote (st : HealingStore V) (grades : GradeRead V) : Block V :=
  letI := grades.rawG2_decidable
  match deepest_clear (some grades.anchor) st.live_confirmed grades.clear with
  | some B => B
  | none =>
    match grades.Q2 with
    | some q => q
    | none =>
      if grades.rawG2 then Protocol.get_fg_root st.toFG else grades.anchor

end Protocol
end DecoupledConsensusModel
end

-- ── from Execution/GradeRuntime/Clipping.lean ──
section
/-! Support/opposition runtime definitions for the selected named frame contract.
Protocol namespaces provide the shared grade vocabulary. -/

namespace DecoupledConsensusModel.Protocol
open DecoupledConsensusModel
variable {V : Type} [DecidableEq V]

def clipGrade (g F : Block V) : Block V :=
  match g with
  | .genesis => .genesis
  | .node p s root gv gsv ats v =>
      if Block.compatible (.node p s root gv gsv ats v) F then
        .node p s root gv gsv ats v
      else clipGrade p F

end DecoupledConsensusModel.Protocol
end

-- ── from Execution/GradeRuntime/Inputs.lean ──
section
/-! Support/opposition runtime definitions for the selected named frame contract.
Protocol namespaces provide the shared grade vocabulary. -/

namespace DecoupledConsensusModel.Protocol
open DecoupledConsensusModel
variable {V : Type} [DecidableEq V] [Fintype V]

def rawInputs (gv : Protocol.GradeView V) (eta r : Round) (cutoff : Time) (sender : V) :
    Finset (Protocol.SGVote V) :=
  ((Protocol.latest_window eta r).toFinset.biUnion gv.sg_votes).filter fun u =>
    u.val_index = sender ∧ occurrenceBefore (gv.timestamp_sg_vote u) cutoff = true

/-- The body condition uses only the phase's retained tree and finalized root.
A finalized ancestor keeps its original head. An unknown root is not ready. -/
def bodyReady (gv : Protocol.GradeView V) (F : Block V) (cutoff : Time)
    (u : Protocol.SGVote V) : Bool :=
  match u.confirmed with
  | none => true
  | some root => match Block.find? gv.T root with
    | none => false
    | some H => stampedBefore gv.timestamp_block cutoff H && Block.compatible H F

def interpretedInputs (gv : Protocol.GradeView V) (F : Block V)
    (eta r : Round) (cutoff : Time) (sender : V) : Finset (Protocol.SGVote V) :=
  (rawInputs gv eta r cutoff sender).filter fun u => bodyReady gv F cutoff u = true

end DecoupledConsensusModel.Protocol
end

-- ── from Execution/GradeRuntime/Algebra.lean ──
section
/-! Support/opposition runtime definitions for the selected named frame contract.
Protocol namespaces provide the shared grade vocabulary. -/

namespace DecoupledConsensusModel.Protocol

structure Token (Key : Type*) where
  round : Nat
  key : Key
deriving DecidableEq

variable {Key : Type*} {Block : Type*}

def CleanFrom (raw : Finset (Token Key)) (k : Nat) : Prop :=
  ∀ x ∈ raw, ∀ y ∈ raw, k ≤ x.round → x.round = y.round → x.key = y.key

/-- `early` and `late` contain evidence-ready tokens. `raw` also contains
signed roots whose evidence is incomplete. Thus equivocation needs no body. -/
def Supports (covers : Key → Block → Prop)
    (early late raw : Finset (Token Key)) (B : Block) : Prop :=
  ∃ u ∈ early,
    (∀ x ∈ early, x.round ≤ u.round) ∧
    covers u.key B ∧
    CleanFrom raw u.round ∧
    ∀ x ∈ late, u.round < x.round → covers x.key B
def Opposes (covers : Key → Block → Prop)
    (early late raw : Finset (Token Key)) (B : Block) : Prop :=
  (∃ x ∈ late, (∀ u ∈ early, u.round ≤ x.round) ∧ ¬ covers x.key B) ∨
  ∃ x ∈ raw, ∃ y ∈ raw, (∀ u ∈ early, u.round ≤ x.round) ∧
    x.round = y.round ∧ x.key ≠ y.key

end DecoupledConsensusModel.Protocol

namespace DecoupledConsensusModel.Protocol
open DecoupledConsensusModel
variable {V : Type} [DecidableEq V] [Fintype V]

open DecoupledConsensusModel.Protocol (Token)

def token (u : Protocol.SGVote V) : Token (Option BlockId) := ⟨u.round, u.confirmed⟩

end DecoupledConsensusModel.Protocol
end

-- ── from Execution/GradeRuntime/Selectors.lean ──
section
/-! Support/opposition runtime definitions for the selected named frame contract.
Protocol namespaces provide the shared grade vocabulary. -/

namespace DecoupledConsensusModel.Protocol
open DecoupledConsensusModel
variable {V : Type} [DecidableEq V] [Fintype V]

open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol (Token)

section DecidableGrades
variable {Key B : Type*} [DecidableEq Key]

instance supportsDecidable (covers : Key → B → Bool)
    (early late raw : Finset (Token Key)) (b : B) :
    Decidable (DecoupledConsensusModel.Protocol.Supports (fun k x => covers k x = true) early late raw b) := by
  unfold DecoupledConsensusModel.Protocol.Supports DecoupledConsensusModel.Protocol.CleanFrom
  infer_instance

instance opposesDecidable (covers : Key → B → Bool)
    (early late raw : Finset (Token Key)) (b : B) :
    Decidable (DecoupledConsensusModel.Protocol.Opposes (fun k x => covers k x = true) early late raw b) := by
  unfold DecoupledConsensusModel.Protocol.Opposes
  infer_instance

end DecidableGrades

def rawView (gv : Protocol.GradeView V) (eta r : Round) (cutoff : Time) (v : V) :=
  (rawInputs gv eta r cutoff v).image token

def readyView (gv : Protocol.GradeView V) (F : Block V)
    (eta r : Round) (cutoff : Time) (v : V) :=
  (interpretedInputs gv F eta r cutoff v).image token

def localCovers (gv : Protocol.GradeView V) (key : Option BlockId) (B : Block V) : Bool :=
  Protocol.head_covers gv.T B key

def positive (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    (early late : Time) (v : V) (B : Block V) : Bool :=
  decide (DecoupledConsensusModel.Protocol.Supports (fun k b => localCovers gv k b = true)
    (readyView gv F eta r early v) (readyView gv F eta r late v) (rawView gv eta r late v) B)

def opposing (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    (early late : Time) (v : V) (B : Block V) : Bool :=
  decide (DecoupledConsensusModel.Protocol.Opposes (fun k b => localCovers gv k b = true)
    (readyView gv F eta r early v) (readyView gv F eta r late v) (rawView gv eta r late v) B)

/-- An executable local grade. Only current tree lookup and finite token
sets are used; the proof-wide RootCovers relation is not executed. -/
def gradeBool (E : Env V) (gv : Protocol.GradeView V) (F : Block V) (eta r : Round)
    (early late : Time) (B : Block V) : Bool :=
  decide (E.electorate.weightOf
    (Finset.univ.filter fun v => opposing gv F eta r early late v B = true) <
    E.electorate.weightOf
      (Finset.univ.filter fun v => positive gv F eta r early late v B = true))

/-- Freeze the raw phase grade over the processed tree before clipping.
The FG activity filter is applied only when the saved root is consumed. -/
def freezeRoot (E : Env V) (gv : Protocol.GradeView V) (F : Block V)
    (eta r : Round) (early late : Time) : Option (Block V) :=
  Block.deepest? (gv.T.filter fun B => gradeBool E gv F eta r early late B = true)

/-- A completed root names its graded prefix family. -/
def activePrefix (tree : Finset (Block V)) (root : Block V) : Option (Block V) :=
  Block.deepest? (tree.filter fun B => Block.preceq B root = true)

/-- Adopted shifted schedule: current G1 completes before the opening
proposal. Pending and completed-empty G1 use only the FG-root fallback.
No instantaneous selector or previous-round G1 is consulted. -/
def anchor (_E : Env V) (_hc : Protocol.HealConfig) (st : Protocol.HealingStore V) (_r : Round)
    (g1 : Option (Option (Block V))) : Block V :=
  match g1 with
  | some (some root) =>
    (activePrefix (Protocol.get_filtered_block_tree st.toFG) root).getD
      (Protocol.get_fg_root st.toFG)
  | _ => Protocol.get_fg_root st.toFG

/-- All phase results must be complete before a height source is evaluated.
Scheduled attestations occur at T+6Delta, after all three fixed phase times. -/
structure Frame (V : Type) where
  g0 : Option (Option (Block V))
  g1 : Option (Option (Block V))
  g2 : Option (Option (Block V))

def allClosed (frame : Frame V) : Bool :=
  frame.g0.isSome && frame.g1.isSome && frame.g2.isSome

def grade2Block (st : Protocol.HealingStore V) (frame : Frame V) : Option (Block V) :=
  if allClosed frame then
    (frame.g2.bind id).bind (activePrefix (Protocol.get_filtered_block_tree st.toFG))
  else none

def clear (frame : Frame V) (B : Block V) : Bool :=
  match frame.g0 with
  | some (some root) => Block.compatible B root
  | _ => true

end DecoupledConsensusModel.Protocol
end

-- ── from Execution/GradeRuntime/Cache.lean ──
section
/-! Support/opposition runtime definitions for the selected named frame contract.
Protocol namespaces provide the shared grade vocabulary. -/

namespace DecoupledConsensusModel.Protocol
open DecoupledConsensusModel
variable {V : Type} [DecidableEq V] [Fintype V]

open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

inductive Phase where
  | g0 | g1 | g2
  deriving DecidableEq

def Phase.earlyOffset : Phase → Int
  | .g0 => -3 | .g1 => -4 | .g2 => -5

def Phase.lateOffset : Phase → Int
  | .g0 => -3 | .g1 => -2 | .g2 => -1

def Phase.domainOffset : Phase → Int
  | .g0 => 1 | .g1 => 0 | .g2 => -1

def opening (E : Env V) (hc : Protocol.HealConfig) (r : Round) : Time :=
  Protocol.proposal_time E (hc.opening_slot r)

def early (E : Env V) (hc : Protocol.HealConfig) (r : Round) (p : Phase) : Time :=
  opening E hc r + p.earlyOffset * E.Δ

def late (E : Env V) (hc : Protocol.HealConfig) (r : Round) (p : Phase) : Time :=
  opening E hc r + p.lateOffset * E.Δ

def domain (E : Env V) (hc : Protocol.HealConfig) (r : Round) (p : Phase) : Time :=
  opening E hc r + p.domainOffset * E.Δ

def pendingFrame : Frame V := ⟨none, none, none⟩
def emptyFrame : Frame V := ⟨some none, some none, some none⟩

def phaseResult (f : Frame V) : Phase → Option (Option (Block V))
  | .g0 => f.g0 | .g1 => f.g1 | .g2 => f.g2

def putPhase (f : Frame V) (p : Phase) (result : Option (Block V)) : Frame V :=
  match p with
  | .g0 => { f with g0 := some result }
  | .g1 => { f with g1 := some result }
  | .g2 => { f with g2 := some result }

/-- A completed result is never recalculated, including completed-empty.
Only an exact domain-time tick can change a pending result. -/
def completeOne (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (r : Round) (t : Time) (p : Phase) (f : Frame V) : Frame V :=
  match phaseResult f p with
  | some _ => f
  | none =>
    if t = domain E hc r p then
      putPhase f p (freezeRoot E st.gradeView st.F hc.η_SG r (early E hc r p) (late E hc r p))
    else f

def completeFrame (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (r : Round) (t : Time) (f : Frame V) : Frame V :=
  completeOne E hc st r t .g0
    (completeOne E hc st r t .g1 (completeOne E hc st r t .g2 f))

def clipResult (F : Block V) (result : Option (Option (Block V))) :
    Option (Option (Block V)) :=
  result.map (fun root => root.map (fun B => DecoupledConsensusModel.Protocol.clipGrade B F))

def clipFrame (F : Block V) (f : Frame V) : Frame V :=
  ⟨clipResult F f.g0, clipResult F f.g1, clipResult F f.g2⟩

/-- G2 for the next round completes before that round opens. Both labels
must coexist until the opening rotates the cache. Storage is bounded. -/
structure Cache (V : Type) where
  round : Round
  current : Frame V
  next : Frame V

def initialCache : Cache V := ⟨0, emptyFrame, pendingFrame⟩

/-- A skipped round starts pending. Advancing one round carries only the
already saved next-round frame; it never reconstructs missed phase results. -/
def alignRound (c : Cache V) (r : Round) : Cache V :=
  if r = c.round then c
  else if r = c.round + 1 then ⟨r, c.next, pendingFrame⟩
  else ⟨r, pendingFrame, pendingFrame⟩

def cacheAtRound (c : Cache V) (r : Round) : Frame V :=
  if r = c.round then c.current
  else if r = c.round + 1 then c.next
  else pendingFrame

def clipCache (F : Block V) (c : Cache V) : Cache V :=
  ⟨c.round, clipFrame F c.current, clipFrame F c.next⟩

/-- The caller supplies the store strictly before this tick. Same-time
objects pass through the object handler only after this operation. -/
def onPhaseTick (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.HealingStore V)
    (t : Time) (c : Cache V) : Cache V :=
  let c := alignRound c (hc.round_of (E.slotOf t))
  clipCache st.F ⟨c.round, completeFrame E hc st c.round t c.current,
    completeFrame E hc st (c.round + 1) t c.next⟩

end DecoupledConsensusModel.Protocol
end

-- ── from Execution/GradeRuntime/FrameContract.lean ──
section
/-! Pure cache-indexed grade contracts shared by the named protocol and the
retained runtime. These definitions do not depend on an execution or wire type. -/

namespace DecoupledConsensusModel.Protocol
open DecoupledConsensusModel
variable {V : Type} [DecidableEq V] [Fintype V]

open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

def readFrame (c : Cache V) (st : Protocol.HealingStore V) (r : Round) : Frame V :=
  clipFrame st.F (cacheAtRound c r)

def frameGradeRead (c : Cache V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) : Protocol.GradeRead V where
  anchor := DecoupledConsensusModel.Protocol.anchor E hc st r (readFrame c st r).g1
  Q2 := grade2Block st (readFrame c st r)
  clear := DecoupledConsensusModel.Protocol.clear (readFrame c st r)
  rawG2 := ((readFrame c st r).g2.bind id).isSome = true
  rawG2_decidable := inferInstance

def frameSGCandidate (c : Cache V) (_E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (_slot : Slot) : Option (Block V) :=
  ((readFrame c st (hc.round_of st.s)).g2.bind id).bind
    (activePrefix (Protocol.get_filtered_block_tree st.toFG))

/-- The round's stable-record root under CONFIRMATION'S OWN viability rule: the
frozen slot projected onto the candidate tree, or the FG root when that
projection is empty.

This is `frameSGCandidate`'s body, read at the round argument instead of the
store's own clock round. The two coincide: the stable
record and the confirmation record then sit on one chain by construction, and
the confirmation duty floors the second on the first.

The stable write never empties. If the projection is empty, the FG root is
written; `advance_confirmed` keeps the prior record when that root is its
ancestor, so the fallback never retracts the record.

The projection reads the CONSUMING store, not the freezing one, and no frozen
root moves: viability and the root descent are store-local and time-varying,
and the record is written at the confirmation duty, which is where the node has
to be able to walk to the root. Putting the restriction inside `freezeRoot`
instead would move the anchor and the clear with it, since that is the one
freeze of all three phases. -/
def frameStableRoot (c : Cache V) (_E : Env V) (_hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round) : Option (Block V) :=
  match ((readFrame c st r).g2.bind id).bind
      (activePrefix (Protocol.get_filtered_block_tree st.toFG)) with
  | some G => some G
  | none => some (Protocol.get_fg_root st.toFG)

/-- Exactly the four grade components are replaced. The SG arm uses the
existing generic walk and fallbacks on the supplied frame read. -/
def frameContract (c : Cache V) : Protocol.GradeContract V where
  read := frameGradeRead c
  sgVote := Protocol.currentSGVote
  confirmationSG := .optional (frameSGCandidate c)
  stableRoot := frameStableRoot c

end DecoupledConsensusModel.Protocol
end

end
