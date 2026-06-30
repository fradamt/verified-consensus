# Model annotation — paper ↔ Lean correspondence

A map from the reference paper to this Lean 4 / mathlib formalization. For each paper object
(definition, algorithm, lemma, theorem) the paper statement is shown **rendered** from the LaTeX
source, immediately followed by the corresponding **Lean** declaration (verbatim from the source,
syntax-highlighted; proofs elided as `:= by ...`).

**Reference paper:** `height_filter_and_timeouts.tex` (the "height filter and timeouts"
shared-finality protocol) — §"Model and definitions" (`sec:model`), §"Accountable safety"
(`sec:safety`), §"Fork-choice store" (`sec:store`). The paper's custom macros are expanded to
readable names and unicode math. The public theorem statements live in `State/TheoremStatements.lean`
and `Store/TheoremStatements.lean`; their proved facades in the matching `ProvenTheorems.lean`.

**Faithfulness legend** (the *Faithfulness* note under each pair):
- *faithful* — models the paper object as-is.
- *documented deviation* — a deliberate, disclosed modeling choice. The recurring ones:
  **`n = 3f + 1` exact** (the paper allows `n ≥ 3f + 1`); the slashable count `f + 1` realizes the
  paper's `n/3 + 1 > f` quorum overlap; **scoped id-injectivity** (`Block.IdInjectiveOnAncestors`)
  in place of a global hash-collision-freedom assumption; finality **height carried as certificate
  data**, not protocol state; **`LiveEquivalent`** (live view rooted at finality) for replay
  order-independence rather than full-store equality; `getConfirmed` as the **finite list of all
  candidate outputs** rather than an oracle-`Ω`-selected single block.
- *proof-internal* — the Lean counterpart is a `Store.Proof`/`State.Proof` lemma, not part of the
  public `TheoremStatements`/`ProvenTheorems` surface.
- *coverage gap* — a paper remark/lemma with no standalone Lean statement (realized inside a proof).

## Contents

- [Model and definitions (sec:model)](#model-and-definitions-secmodel)
- [Accountable safety (sec:safety)](#accountable-safety-secsafety)
- [Fork-choice store (sec:store)](#forkchoice-store-secstore)

## Model and definitions (sec:model)

### Definition: Height · `def:height`

**Paper** — `height_filter_and_timeouts.tex:155-158`

<b>Definition (Height).</b> <i>Height</i> is the finality-gadget counter, separate from slot. The genesis state-height is 1 (with <code>genesis</code> treated as pre-justified and pre-finalized at height 0); height advances by exactly 1 via fixed-target justification (Definition, fixed-target justification) or a timeout (Definition, timeout).

**Lean** — `State.h (field) / State.genesis` · `DecoupledConsensus/State/Model/StateMachine.lean:20,34`

```lean
structure State (n : ℕ) where
  L : Block n -- chain head
  s : ℕ -- current slot
  h : ℕ -- current height
  sh : ℕ -- slot whose processing last advanced `h`
  targets : Validator n → Option (Block n) -- per-validator target at height `h`
  timeouts : Validator n → Bool -- per-validator timeout marker at height `h`
  J : Block n -- most recently justified block
  hj : ℕ -- height at which `J` was justified
  F : Block n -- most recently finalized block
  P : Finset (Validator n) -- validators committing to finalize `J` at `hj`

def genesis (n : ℕ) : State n where
  L        := Block.genesis
  s        := 0
  h        := 1
  sh       := 0
  targets  := fun _ => none
  timeouts := fun _ => false
  J        := Block.genesis
  hj       := 0
  F        := Block.genesis
  P        := ∅
```

> **Faithfulness:** No standalone `Height` definition; height is the `h : ℕ` field of `State`. Genesis state has h=1, hj=0 mirroring "genesis pre-justified/finalized at height 0, state-height 1". The +1 increment is realized in processHeightEvents (h := h+1).

---

### Definition: Block · `def:block`

**Paper** — `height_filter_and_timeouts.tex:160-164`

<b>Definition (Block).</b> A <i>block</i> has a <i>parent</i> block, a <i>slot</i> field, and a set of votes (Definition, vote). The <i>genesis block</i> <code>genesis</code> has no parent and slot 0. Slots strictly increase along parent links: B.<code>slot</code> &gt; B.<code>parent</code>.<code>slot</code> for every non-genesis B.

**Lean** — `Block` · `DecoupledConsensus/State/Model/Blocks.lean:13-16`

```lean
inductive Block (n : ℕ) : Type
  | genesis : Block n
  | mk (id : BlockId) (parent : Block n) (slot : ℕ) (votes : List (Vote n)) : Block n
  deriving DecidableEq
```

> **Faithfulness:** Lean blocks additionally carry an explicit `id : BlockId` (hash idealization; genesis id 0); paper identifies a block with its hash implicitly. Slot-monotonicity is the separate `WellFormed` predicate (and is enforced at the type level by `Chain.extend`'s hSlot), not baked into the inductive. Votes are a `List`, paper says "set".

---

### Definition: Chain + ≼/≺/∼ · `def:chain`

**Paper** — `height_filter_and_timeouts.tex:166-171`

<b>Definition (Chain).</b> A <i>chain</i> is a path from <code>genesis</code> to some block B via parent links. Chains are in bijection with their tips, and we identify the two. Blocks form a tree rooted at <code>genesis</code>; we write B ≼ B′ when B is an ancestor of B′ (or B = B′), B ≺ B′ for strict ancestry, and B ∼ B′ (<i>compatible</i>) when B ≼ B′ or B′ ≼ B. Two chains <i>conflict</i> when their tips are not compatible.

**Lean** — `Block.Ancestor (≼) / isStrictAncestorOf / Block.Compatible (~) / Chain` · `DecoupledConsensus/State/Model/Blocks.lean:58,73,100; StateMachine.lean:204`

```lean
inductive Ancestor : Block n → Block n → Prop
  | refl (B : Block n) : Ancestor B B
  | step {B C : Block n} {bid s : ℕ} {vs : List (Vote n)}
      (h : Ancestor B C) : Ancestor B (mk bid C s vs)

scoped infix:50 " ≼ " => Block.Ancestor

def isStrictAncestorOf (B C : Block n) : Bool :=
  isAncestorOf B C && decide (B ≠ C)

def Compatible (B C : Block n) : Prop := B ≼ C ∨ C ≼ B

scoped infix:50 " ~ " => Block.Compatible

inductive Chain (n : ℕ) : Block n → Type where
  | genesis : Chain n Block.genesis
  | extend {parent : Block n}
           (c : Chain n parent)
           (bid : BlockId)
           (newSlot : ℕ)
           (votes : List (Vote n))
           (hSlot : newSlot > parent.slot) :
      Chain n (Block.mk bid parent newSlot votes)
```

> **Faithfulness:** ≼ is `Block.Ancestor` (Prop, parent-pointer, no slot check); ≺ has no dedicated Prop — only the Bool `isStrictAncestorOf` (used as `T.slot &lt; σ.L.slot` in processVoteCore). ∼ is `Compatible`. `Chain` is an indexed inductive identified with its tip block (matching "chains in bijection with tips"); `extend` enforces slot monotonicity. "Conflict" = ¬Compatible has no named def.

---

### Definition: Vote · `def:vote`

**Paper** — `height_filter_and_timeouts.tex:173-182`

<b>Definition (Vote).</b> A <i>vote</i> is a signed tuple (<code>validator</code>, <code>height</code>, <code>target</code>, <code>finalizeHeight</code>, <code>finalizeTarget</code>), where <code>validator</code> is the signer, <code>height</code> is a height, and <code>target</code> ∈ {⊥} ∪ Blocks. A vote with <code>target</code> = ⊥ is a <i>timeout vote</i>; a vote with <code>target</code> ≠ ⊥ is a <i>justification vote</i>. The pair (<code>finalizeHeight</code>, <code>finalizeTarget</code>) is either both ⊥ or a commitment to finalize a block at a height. A vote included on a chain must reference a target (and finalize target, when present) that already exists on that chain when non-⊥; in particular, a block cannot include a vote that names the block itself, since naming it requires its hash.

**Lean** — `Vote` · `DecoupledConsensus/State/Model/Primitives.lean:40-45`

```lean
structure Vote (n : ℕ) where
  validator : Validator n
  height : ℕ
  target : Option BlockId -- `none` represents `⊥`, a timeout vote
  finalize : Option (ℕ × BlockId) -- optional `(height, target-id)` finalize commitment
  deriving DecidableEq
```

> **Faithfulness:** Paper's 5-tuple is packed into 4 Lean fields: (finalizeHeight, finalizeTarget) become one `finalize : Option (ℕ × BlockId)` (the "both ⊥ or both present" constraint is enforced by Option). `target`/`finalize` name block **ids** (hashes), not Block values — matching "naming requires its hash"; the "target/finalize target already on chain" constraint is realized at processing time via `findById` plus a strict-ancestor slot check in processVoteCore and the P-gate's `voteReferencesKnown` guard.

---

### Structure: State tuple σ[B] (10 components) + genesis state

**Paper** — `height_filter_and_timeouts.tex:184-206`

<b>State.</b> The <i>state after block B</i>, written σ[B], is the tuple<br>σ[B] = (L, s, h, s<sub>h</sub>, targets, timeouts, J, h<sub>j</sub>, F, P),<br>with components:<ul><li>L: the <i>chain head</i> (L = B after processing B).</li><li>s: the <i>current slot</i>, incremented once per slot by <code>processSlot</code> (Figure, state machine).</li><li>h: the <i>current height</i>.</li><li>s<sub>h</sub>: the slot of the block whose processing last advanced h on this chain (0 if no advance has occurred).</li><li>targets[1..n]: for each validator i, the target of i's justification vote at the current height (⊥ if none processed).</li><li>timeouts[1..n]: for each i, a boolean that is <code>true</code> iff i's vote at the current height set the timeout marker — either a timeout vote (<code>target</code> = ⊥) or a height-fresh justification vote on this chain.</li><li>J, h<sub>j</sub>: the most recently justified block and its height.</li><li>F: the most recently finalized block.</li><li>P ⊆ {1, …, n}: validators who have cast a vote with <code>finalizeHeight</code> = h<sub>j</sub> and <code>finalizeTarget</code> = J.</li></ul>The genesis state is<br>σ<sub>gen</sub> := (<code>genesis</code>, 0, 1, 0, ⊥ⁿ, false<sup>n</sup>, <code>genesis</code>, 0, <code>genesis</code>, ∅),<br>with σ[<code>genesis</code>] := σ<sub>gen</sub>: <code>genesis</code> is treated as pre-justified and pre-finalized at height 0, so the genesis state-height is 1 and h<sub>j</sub> = 0 records the genesis-justification. When unambiguous we drop the chain prefix and write L, s, h, etc. for the components of σ[L].

**Lean** — `State / State.genesis` · `DecoupledConsensus/State/Model/StateMachine.lean:18-44`

```lean
structure State (n : ℕ) where
  L : Block n -- chain head
  s : ℕ -- current slot
  h : ℕ -- current height
  sh : ℕ -- slot whose processing last advanced `h`
  targets : Validator n → Option (Block n) -- per-validator target at height `h`
  timeouts : Validator n → Bool -- per-validator timeout marker at height `h`
  J : Block n -- most recently justified block
  hj : ℕ -- height at which `J` was justified
  F : Block n -- most recently finalized block
  P : Finset (Validator n) -- validators committing to finalize `J` at `hj`

def genesis (n : ℕ) : State n where
  L        := Block.genesis
  s        := 0
  h        := 1
  sh       := 0
  targets  := fun _ => none
  timeouts := fun _ => false
  J        := Block.genesis
  hj       := 0
  F        := Block.genesis
  P        := ∅
```

> **Faithfulness:** Exact 10-field correspondence (sh = s_h, hj = h_j). `targets` stores actual `Block n` values, not ids (paper writes T). genesis state matches σ_gen field-for-field. No finalized-height field: the height at which F was set is carried by `FinalizedCertificate`, not stored in `State`.

---

### Definition: State-height · `def:sheight`

**Paper** — `height_filter_and_timeouts.tex:208-210`

<b>Definition (State-height).</b> The <i>state-height</i> of a block B is σ[B].h: the height after processing B on its own chain.

**Lean** — `(stateOf chain).h` · `DecoupledConsensus/State/Model/StateMachine.lean:217`

```lean
def stateOf {n : ℕ} {B : Block n} (chain : Chain n B) :
    State n :=
  match chain with
  | .genesis => State.genesis n
  | @Chain.extend _ parent c bid newSlot votes _ =>
      stateTransition (stateOf c) (Block.mk bid parent newSlot votes)
```

> **Faithfulness:** No standalone `stateHeight` def; expressed inline as `(stateOf chain).h` throughout (e.g. used in FinalizedCertificate: `(stateOf (chain.subchain hC)).h = h_f`). `stateOf` is the Lean analogue of σ[B] and depends only on the tip since votes are embedded in blocks.

---

### Paragraph: Height freshness

**Paper** — `height_filter_and_timeouts.tex:212-219`

<b>Height freshness.</b> A justification vote v (i.e., v.<code>target</code> = T ≠ ⊥) is <i>fresh</i> on a chain with head state σ[L] iff<br>σ[L].h = v.<code>height</code> ∧ T ≺ L ∧ T.<code>slot</code> ≥ σ[L].s<sub>h</sub>:<br>the chain is at v's height, T is a strict ancestor on this chain, and T's slot is no earlier than where the chain's current height began. A timeout vote (v.<code>target</code> = ⊥) is fresh on the chain iff σ[L].h = v.<code>height</code>. Intuitively, a fresh justification vote attests that its signer saw T as a chain of height v.<code>height</code>.

**Lean** — `processVoteCore (inline freshness condition)` · `DecoupledConsensus/State/Model/StateMachine.lean:122-137`

```lean
def processVoteCore (σ : State n) (v : Vote n) : State n :=
  if voteReferencesKnown σ v then
    match v.target with
    | none =>
        if v.height = σ.h then
          { σ with timeouts := Function.update σ.timeouts v.validator true }
        else σ
    | some bid =>
        match σ.L.findById bid with
        | none => σ
        | some T =>
            if v.height = σ.h ∧ T.slot ≥ σ.sh ∧ T.slot < σ.L.slot then
              { σ with targets  := Function.update σ.targets v.validator (some T)
                       timeouts := Function.update σ.timeouts v.validator true }
            else σ
  else σ
```

> **Faithfulness:** Freshness is not a named predicate; it is the inner `if` guard in processVoteCore after the vote-reference well-formedness check. Paper's `T ≺ L` becomes `T.slot &lt; σ.L.slot` after resolving bid via `findById` on σ.L (so T is on the chain by construction and strictly before the head). Timeout-vote freshness is `v.height = σ.h`. Order of conjuncts differs but is equivalent.

---

### Definition: Fixed-target justification · `def:justification`

**Paper** — `height_filter_and_timeouts.tex:228-234`

<b>Definition (Fixed-target justification).</b> A block T is <i>justified at height h</i> on a chain with state σ[L] with σ[L].h = h iff<br>|{i : targets[i] = T}| ≥ 2n/3.<br>Only votes with target exactly T contribute.

**Lean** — `Justified` · `DecoupledConsensus/State/Model/StateMachine.lean:60-61`

```lean
def Justified (σ : State n) (T : Block n) : Prop :=
  IsQuorumStrict n (targetedSet σ T)
```

> **Faithfulness:** 2n/3 quorum is `IsQuorumStrict n` (`0 < n ∧ 3 * card ≥ 2n`, the integer `ceil(2n/3)` threshold for a nonempty committee). Executable mirror `justifiedBool`. "target exactly T" matches `targetedSet`'s `= some T` filter.

---

### Definition: Timeout · `def:timeout`

**Paper** — `height_filter_and_timeouts.tex:236-244`

<b>Definition (Timeout).</b> On a chain with head state σ[L] at height h, a <i>timeout</i> fires iff<br>|{i : timeouts[i] = true}| ≥ 2n/3.<br>A timeout has no associated target block. Both timeout votes and height-fresh justification votes (with target ≺ L at the chain's current height) set timeouts[i] = true, so a justification quorum implies a timeout quorum. The two height-advance branches are checked in order, justification first (Figure, state machine).

**Lean** — `TimeoutFires` · `DecoupledConsensus/State/Model/StateMachine.lean:64-65`

```lean
def TimeoutFires (σ : State n) : Prop :=
  IsQuorumStrict n (timedOutSet σ)
```

> **Faithfulness:** Executable mirror `timeoutFiresBool`. The "justification sets timeouts too" invariant is realized in processVoteCore (the fresh-justification branch updates both `targets` and `timeouts`); branch ordering is enforced in processHeightEvents (justification matched before the timeout `if`).

---

### Definition: Finality · `def:finality`

**Paper** — `height_filter_and_timeouts.tex:246-248`

<b>Definition (Finality).</b> The justified block J is <i>finalized at height h<sub>j</sub></i> once |P| ≥ 2n/3.

**Lean** — `CurrentlyFinal` · `DecoupledConsensus/State/Model/StateMachine.lean:68-69`

```lean
def CurrentlyFinal (σ : State n) : Prop :=
  IsQuorumStrict n σ.P
```

> **Faithfulness:** Executable mirror `currentlyFinalBool`; the actual `F ← J` write is `applyFinality`. The external finality height h_j is not stored after the fact (no finalized-height field); it is recorded as certificate data in `FinalizedCertificate`.

---

### Definition: Slashing rule E1 · `def:slashing`

**Paper** — `height_filter_and_timeouts.tex:250-257`

<b>Definition (Slashing, rule E1).</b> A validator is <i>slashable</i> if it signed two votes a, b (possibly a = b) with<br>b.<code>finalizeTarget</code> ≠ ⊥ ∧ a.<code>height</code> = b.<code>finalizeHeight</code> ∧ a.<code>target</code> ≠ b.<code>finalizeTarget</code>.<br>That is, a validator committing (<code>finalizeHeight</code>, <code>finalizeTarget</code>) = (h<sub>f</sub>, T<sub>f</sub>) must not sign any vote at height h<sub>f</sub> with target ≠ T<sub>f</sub>. Note that timeout votes (a.<code>target</code> = ⊥) are themselves in conflict with any commitment b.<code>finalizeTarget</code> ≠ ⊥ at the same height, since ⊥ ≠ b.<code>finalizeTarget</code>.

**Lean** — `Vote.slashConflict / Vote.Slashable` · `DecoupledConsensus/State/Model/Primitives.lean:52-60`

```lean
def slashConflict (a b : Vote n) : Prop :=
  ∃ hf Tf, b.finalize = some (hf, Tf) ∧
        a.height = hf ∧
        a.target ≠ some Tf

def Slashable (a b : Vote n) : Prop :=
  a.validator = b.validator ∧ (slashConflict a b ∨ slashConflict b a)
```

> **Faithfulness:** `slashConflict a b` is the one-sided E1 predicate (b commits, a conflicts); `Slashable` symmetrizes it and adds same-validator. Matches `finalizeConflict`/`isSlashable` from the figure. `a.target ≠ some Tf` correctly captures both wrong-target and timeout (a.target=none) conflicts.

---

### Algorithm: stateTransition · `alg:state-machine`

**Paper** — `height_filter_and_timeouts.tex:285-292`

<pre>stateTransition(σ, B):                 // Per-block entry point
  while σ.s &lt; B.slot:                  // Advance through intervening slots
    σ ← processSlot(σ)
  σ ← processBlock(σ, B)
  σ ← processHeight(σ)                 // Close events enabled by B's votes
  return σ</pre>

**Lean** — `stateTransition` · `DecoupledConsensus/State/Model/StateMachine.lean:229-230`

```lean
def stateTransition (σ : State n) (B : Block n) : State n :=
  processHeight (processBlock (iterateProcessSlot σ (B.slot - σ.s)) B)
```

> **Faithfulness:** The paper's `while σ.s &lt; B.slot` loop is realized as `iterateProcessSlot σ (B.slot - σ.s)` (helper `iterateProcessSlot` folds processSlot k times). On a well-formed chain B.slot ≥ σ.s so the count is exact; truncating subtraction gives 0 otherwise (never on a Chain).

---

### Algorithm: processSlot · `alg:state-machine`

**Paper** — `height_filter_and_timeouts.tex:295-301`

<pre>processSlot(σ):
  if σ.L.slot &lt; σ.s:                   // The current slot is empty on this chain
    σ ← processHeight(σ)
  σ.s ← σ.s + 1
  return σ</pre>

**Lean** — `processSlot` · `DecoupledConsensus/State/Model/StateMachine.lean:195-199`

```lean
def processSlot (σ : State n) : State n :=
  if σ.L.slot < σ.s then
    { processHeight σ with s := σ.s + 1 }
  else
    { σ with s := σ.s + 1 }
```

> **Faithfulness:** Faithful. Empty-slot guard `σ.L.slot &lt; σ.s` and the unconditional `s := s+1` both match.

---

### Algorithm: processBlock · `alg:state-machine`

**Paper** — `height_filter_and_timeouts.tex:304-309`

<pre>processBlock(σ, B):
  assert σ.s = B.slot                  // Precondition: caller advanced σ.s
  σ.L ← B
  for each vote v in B:
    σ ← processVote(σ, v)
  return σ</pre>

**Lean** — `processBlock` · `DecoupledConsensus/State/Model/StateMachine.lean:204-205`

```lean
def processBlock (σ : State n) (B : Block n) : State n :=
  B.votes.foldl processVote { σ with L := B }
```

> **Faithfulness:** Faithful. The `assert σ.s = B.slot` precondition is the caller's responsibility (no runtime assert); satisfied by stateTransition's iterateProcessSlot. L ← B then `foldl processVote` over B.votes.

---

### Algorithm: processVote · `alg:state-machine`

**Paper** — `height_filter_and_timeouts.tex:312-329`

<pre>processVote(σ, v):
  i ← v.validator
  if v.target = ⊥:                     // Timeout vote
    if v.height = σ.h:
      σ.timeouts[i] ← true
  else:                               // Justification vote: apply height freshness
    fresh ← (v.height = σ.h) ∧ (v.target ≺ σ.L) ∧ (v.target.slot ≥ σ.s_h)
    if fresh:
      σ.targets[i] ← v.target
      σ.timeouts[i] ← true
  if v.finalizeHeight = σ.h_j and v.finalizeTarget = σ.J:
    σ.P ← σ.P ∪ {i}
  return σ</pre>

**Lean** — `processVote (with processVoteCore)` · `DecoupledConsensus/State/Model/StateMachine.lean:99-155`

```lean
def blockReferenceKnown (σ : State n) (bid : BlockId) : Bool :=
  match σ.L.findById bid with
  | none => false
  | some T => decide (T.slot < σ.L.slot)

def voteReferencesKnown (σ : State n) (v : Vote n) : Bool :=
  let targetKnown :=
    match v.target with
    | none => true
    | some bid => blockReferenceKnown σ bid
  let finalizeKnown :=
    match v.finalize with
    | none => true
    | some (_, bid) => blockReferenceKnown σ bid
  targetKnown && finalizeKnown

def processVoteCore (σ : State n) (v : Vote n) : State n :=
  if voteReferencesKnown σ v then
    match v.target with
    | none =>
        if v.height = σ.h then
          { σ with timeouts := Function.update σ.timeouts v.validator true }
        else σ
    | some bid =>
        match σ.L.findById bid with
        | none => σ
        | some T =>
            if v.height = σ.h ∧ T.slot ≥ σ.sh ∧ T.slot < σ.L.slot then
              { σ with targets  := Function.update σ.targets v.validator (some T)
                       timeouts := Function.update σ.timeouts v.validator true }
            else σ
  else σ

def finalizeGate (σ : State n) (v : Vote n) : Bool :=
  voteReferencesKnown σ v && decide (v.finalize = some (σ.hj, σ.J.id))

def processVote (σ : State n) (v : Vote n) : State n :=
  let σ' := processVoteCore σ v
  if finalizeGate σ' v then
    { σ' with P := insert v.validator σ'.P }
  else σ'
```

> **Faithfulness:** Split into processVoteCore (targets/timeouts) + the P-gate. P-gate compares against `(σ'.hj, σ'.J.id)` — i.e. id-level, matching paper's (h_j, J) — after `voteReferencesKnown` checks that every non-⊥ target/finalize id resolves to an already-existing strict ancestor of the current head. `v.target ≺ L` is resolved by `findById bid` then `T.slot &lt; σ.L.slot`, which also prevents a block from counting votes that name the block itself. P-gate independence of freshness matches the paper note; unresolved or self-referential vote references do not count.

---

### Algorithm: processHeight · `alg:state-machine`

**Paper** — `height_filter_and_timeouts.tex:332-336`

<pre>processHeight(σ):
  σ ← processHeightEvents(σ)
  return σ</pre>

**Lean** — `processHeight` · `DecoupledConsensus/State/Model/StateMachine.lean:188-189`

```lean
def processHeight (σ : State n) : State n :=
  processHeightEvents σ
```

> **Faithfulness:** Faithful 1:1 wrapper. Comment notes the TeX leak extension wraps this; accountable-safety model keeps it = processHeightEvents.

---

### Algorithm: processHeightEvents · `alg:state-machine`

**Paper** — `height_filter_and_timeouts.tex:338-354`

<pre>processHeightEvents(σ):
  if |σ.P| ≥ 2n/3:                                          // Finality
    σ.F ← σ.J
  T ← argmax over T′ ∈ {σ.targets[i] : σ.targets[i] ≠ ⊥} of |{i : σ.targets[i] = T′}|
                                                           // T ← ⊥ if the set is empty
  if T ≠ ⊥ and |{i : σ.targets[i] = T}| ≥ 2n/3:            // Justification
    σ.J ← T,  σ.h_j ← σ.h,  σ.P ← ∅
    σ.h ← σ.h + 1,  σ.s_h ← σ.s
    reset targets, timeouts
    return σ
  if |{i : σ.timeouts[i] = true}| ≥ 2n/3:                  // Timeout
    σ.h ← σ.h + 1,  σ.s_h ← σ.s
    reset targets, timeouts
  return σ</pre>

**Lean** — `applyFinality / processHeightEvents` · `DecoupledConsensus/State/Model/StateMachine.lean:159-183`

```lean
def applyFinality (σ : State n) : State n :=
  if currentlyFinalBool σ then { σ with F := σ.J } else σ

def processHeightEvents (σ : State n) : State n :=
  let σ1 := applyFinality σ
  match firstJustifiedTarget σ1 with
  | some T =>
    { σ1 with J        := T
              hj       := σ1.h
              P        := ∅
              h        := σ1.h + 1
              sh       := σ1.s
              targets  := fun _ => none
              timeouts := fun _ => false }
  | none =>
      if timeoutFiresBool σ1 then
        { σ1 with h        := σ1.h + 1
                  sh       := σ1.s
                  targets  := fun _ => none
                  timeouts := fun _ => false }
      else σ1
```

> **Faithfulness:** KEY DEVIATION: paper selects T via `argmax_{T'} |targets=T'|` then checks ≥2n/3; Lean uses `firstJustifiedTarget` — a first-index-scan over validators returning the first target that is already justifiedBool (≥2n/3). These agree because under a 2n/3 quorum at most one target can have a quorum (any two quorums overlap &gt;f), so argmax-with-quorum and first-quorum-found select the same block. Finality branch factored as `applyFinality`. Branch order finality→justification→timeout preserved.

---

### Algorithm: finalizeConflict · `alg:state-machine`

**Paper** — `height_filter_and_timeouts.tex:357-359`

<pre>finalizeConflict(v₁, v₂):   // Does v₁ conflict with v₂'s finalize commitment?
  return v₂.finalizeTarget ≠ ⊥ ∧ v₁.height = v₂.finalizeHeight ∧ v₁.target ≠ v₂.finalizeTarget</pre>

**Lean** — `Vote.slashConflict` · `DecoupledConsensus/State/Model/Primitives.lean:52-55`

```lean
def slashConflict (a b : Vote n) : Prop :=
  ∃ hf Tf, b.finalize = some (hf, Tf) ∧
        a.height = hf ∧
        a.target ≠ some Tf
```

> **Faithfulness:** Direct counterpart of finalizeConflict (a=v1, b=v2). Paper's separate finalizeHeight/finalizeTarget are destructured from the single `b.finalize = some (hf, Tf)` via the existential.

---

### Algorithm: isSlashable · `alg:state-machine`

**Paper** — `height_filter_and_timeouts.tex:362-365`

<pre>isSlashable(v₁, v₂):
  return v₁.validator = v₂.validator
         ∧ (finalizeConflict(v₁, v₂) ∨ finalizeConflict(v₂, v₁))</pre>

**Lean** — `Vote.Slashable` · `DecoupledConsensus/State/Model/Primitives.lean:59-60`

```lean
def Slashable (a b : Vote n) : Prop :=
  a.validator = b.validator ∧ (slashConflict a b ∨ slashConflict b a)
```

> **Faithfulness:** Direct counterpart. The history-scoped aggregates `IsSlashableBetween` / `AtLeastFThirdSlashableBetween` (Certificates.lean:65-78) lift this to chains for the safety conclusion; `IsSlashable`/`AtLeastFThirdSlashable` (Certificates.lean:87-95) are the unscoped existential hypotheses.

---

### Note: n ≥ 3f+1 and quorum thresholds

**Paper** — `height_filter_and_timeouts.tex:151-153`

We consider a system of n validators of which at most f are adversarial, where n ≥ 3f + 1. A <i>quorum</i> is any set of at least 2n/3 validators. Any two quorums overlap in at least n/3 + 1 &gt; f validators, so their intersection contains at least one honest validator.

**Lean** — `IsQuorum / IsQuorumStrict / IsQuorumStrictBool` · `DecoupledConsensus/State/Model/Primitives.lean:18-33`

```lean
abbrev IsQuorum (f : ℕ) (Q : Finset (Validator n)) : Prop :=
  Q.card ≥ 2 * f + 1

abbrev IsQuorumStrict (n : ℕ) (Q : Finset (Validator n)) : Prop :=
  0 < n ∧ 3 * Q.card ≥ 2 * n

def isQuorumStrictBool (n : ℕ) (Q : Finset (Validator n)) : Bool :=
  decide (0 < n) && Nat.ble (2 * n) (3 * Q.card)
```

> **Faithfulness:** The executable state-machine threshold matches the paper's integer interpretation of "at least 2n/3" as `ceil(2n/3)` for nonempty committees. Documented theorem-surface specialization: the public statement layer still fixes n = 3f+1 EXACT (so IsQuorum `2f+1` ≡ IsQuorumStrict), whereas the paper allows n ≥ 3f+1. The state machine uses the f-free form IsQuorumStrict to avoid threading f. Validators are `Fin n` (`Validator n`). The `n/3+1 = f+1` overlap bound is the `f+1` in AtLeastFThirdSlashable (the `FThird` name).

---

## Accountable safety (sec:safety)

### Lemma: Height progression · `lem:heightprog`

**Paper** — `height_filter_and_timeouts.tex:374-380`

<b>Lemma (Height progression).</b> <code>processHeight</code> increments h by at most 1 per invocation, and each increment is gated by a ≥ 2n/3 justification or timeout quorum.

**Lean** — `height_progression` · `DecoupledConsensus/State/Proof/Facts.lean:641`

```lean
lemma height_progression (σ : State n) :
    ((processHeight σ).h = σ.h ∨ (processHeight σ).h = σ.h + 1) ∧
    ((processHeight σ).h = σ.h + 1 →
      (∃ T, Justified σ T) ∨ TimeoutFires σ) := by
  ...
```

> **Faithfulness:** faithful; internal proof lemma (not in TheoremStatements). The '≥2n/3 quorum' is encoded by `Justified σ T` / `TimeoutFires σ`, which are defined via `IsQuorumStrict`. Stated about pre-state σ because the advance branches reset targets/timeouts.

---

### Lemma: Freshness via target state-height · `lem:fresh-equiv`

**Paper** — `height_filter_and_timeouts.tex:382-397`

<b>Lemma (Freshness via target state-height).</b> For any chain head L and ancestor T ≼ L,<br>T.<code>slot</code> ≥ σ[L].s<sub>h</sub>　⟺　σ[T].h = σ[L].h .

**Lean** — `PrefixHeightInv` · `DecoupledConsensus/State/Proof/TargetHeight.lean:47`

```lean
def PrefixHeightInv {B : Block n} (chain : Chain n B) (σ : State n) : Prop :=
  ∀ {T : Block n} (hT : T ≼ B),
    σ.sh ≤ T.slot → (stateOf (chain.subchain hT)).h = σ.h
```

> **Faithfulness:** The Lean side formalizes the load-bearing (⇒) direction only, as a chain-relative invariant `PrefixHeightInv` (with companions `StrictHeightInv`/`TargetsHeightInv`/`JTargetHeightInv`), preserved through each transition and established by `chain_height_target_invs` (TargetHeight.lean:466). The reverse direction (σ[T].h = σ[L].h ⇒ slot ≥ s_h) is not stated as a single iff; the safety proof only needs `sh ≤ T.slot → σ[T].h = σ.h`. Paper's `s_h` = Lean `σ.sh`.

---

### Lemma: Checkpoint monotonicity · `lem:slotmono`

**Paper** — `height_filter_and_timeouts.tex:399-413`

<b>Lemma (Checkpoint monotonicity).</b> On any chain, the fields s, h, h<sub>j</sub>, s<sub>h</sub>, F, J are non-decreasing along ≼, with F ≼ J at all times. J and h<sub>j</sub> advance only on justification events, and s<sub>h</sub> only on height-advances, with s<sub>h</sub> set to the slot boundary where the height advance fires.

**Lean** — `stateOf_subchain_h_le / chain_J_monotone_step` · `DecoupledConsensus/State/Proof/Facts.lean:972`

```lean
lemma stateOf_subchain_h_le {B : Block n} (chain : Chain n B) :
    ∀ {B' : Block n} (h_anc : B' ≼ B),
    (stateOf (chain.subchain h_anc)).h ≤ (stateOf chain).h := by
  ...

lemma chain_J_monotone_step {parent : Block n} (c : Chain n parent)
    (bid : BlockId) (newSlot : ℕ) (votes : List (Vote n))
    (hSlot : newSlot > parent.slot) :
    (stateOf c).J ≼ (stateOf (Chain.extend c bid newSlot votes hSlot)).J := by
  ...
```

> **Faithfulness:** Deliberately NOT proved as the paper's single all-seven-conjunct statement. The two safety-load-bearing pieces are split: state-height monotonicity along ≼ (`stateOf_subchain_h_le`) and J-monotonicity in one-step extension form (`chain_J_monotone_step`, built on `stateTransition_J_monotone`). See Facts.lean:696-709 comment documenting this split. The s_h-set-to-boundary fact is carried separately inside the height-invariant machinery (TargetHeight.lean).

---

### Definition: Slashable (finalize-conflict) vote pair

**Paper** — `height_filter_and_timeouts.tex:360-365`

<b>finalizeConflict(v<sub>1</sub>, v<sub>2</sub>):</b> // Does v<sub>1</sub> conflict with v<sub>2</sub>'s finalize commitment?<br>return v<sub>2</sub>.<code>finalizeTarget</code> ≠ ⊥ ∧ v<sub>1</sub>.<code>height</code> = v<sub>2</sub>.<code>finalizeHeight</code> ∧ v<sub>1</sub>.<code>target</code> ≠ v<sub>2</sub>.<code>finalizeTarget</code><br><br><b>isSlashable(v<sub>1</sub>, v<sub>2</sub>):</b><br>return v<sub>1</sub>.<code>validator</code> = v<sub>2</sub>.<code>validator</code> ∧ (finalizeConflict(v<sub>1</sub>, v<sub>2</sub>) ∨ finalizeConflict(v<sub>2</sub>, v<sub>1</sub>))

**Lean** — `Vote.Slashable` · `DecoupledConsensus/State/Model/Primitives.lean:57`

```lean
def Slashable (a b : Vote n) : Prop :=
  a.validator = b.validator ∧ (slashConflict a b ∨ slashConflict b a)
```

> **Faithfulness:** faithful: `slashConflict` = paper `finalizeConflict`, `Slashable` = paper `isSlashable`. Lives in the Model layer; lifted to histories by `IsSlashableBetween` (Certificates.lean:65).

---

### Structure: History-scoped slashability vocabulary

**Paper** — `height_filter_and_timeouts.tex:415-445`

<b>Lemma (Any chain past a finalized height contains the finalized block).</b> Unless ≥ n/3 validators are slashable: if C is finalized at height h, then C ≼ B for every block B with σ[B].h &gt; h.<br><br><i>The slashability vocabulary used across these safety results:</i><ul><li>A vote pair is slashable when both votes come from the same validator and one finalize-conflicts with the other (see isSlashable / finalizeConflict).</li><li>finalizeConflict(a, b) holds when b carries a finalize commitment (b.<code>finalizeTarget</code> ≠ ⊥) at the same height as a (a.<code>height</code> = b.<code>finalizeHeight</code>) but to a different target (a.<code>target</code> ≠ b.<code>finalizeTarget</code>).</li><li>The safety statements are accountable: each is conditioned on fewer than n/3 validators being slashable (equivalently, they fail only if ≥ n/3 are slashable).</li><li>Quorum intersection of two ≥ 2n/3 quorums yields an overlap of ≥ n/3, from which a non-slashable witness validator v is selected; non-slashability of v then rules out a finalizeConflict between its two contributing votes.</li></ul>

**Lean** — `IsSlashableBetween / AtLeastFThirdSlashableBetween / IsSlashable / AtLeastFThirdSlashable` · `DecoupledConsensus/State/Model/Certificates.lean:65`

```lean
def IsSlashableBetween {B₁ B₂ : Block n}
    (chain₁ : Chain n B₁) (chain₂ : Chain n B₂)
    (i : Validator n) : Prop :=
  ∃ a ∈ votesIncluded chain₁, ∃ b ∈ votesIncluded chain₂,
    a.validator = i ∧ b.validator = i ∧ Vote.Slashable a b

def AtLeastFThirdSlashableBetween {B₁ B₂ : Block n}
    (chain₁ : Chain n B₁) (chain₂ : Chain n B₂) (f : ℕ) : Prop :=
  ∃ S : Finset (Validator n), S.card ≥ f + 1 ∧
    ∀ i ∈ S, IsSlashableBetween chain₁ chain₂ i

def IsSlashable (i : Validator n) : Prop :=
  ∃ B₁ : Block n, ∃ chain₁ : Chain n B₁,
  ∃ B₂ : Block n, ∃ chain₂ : Chain n B₂,
    IsSlashableBetween chain₁ chain₂ i

def AtLeastFThirdSlashable (f : ℕ) : Prop :=
  ∃ S : Finset (Validator n), S.card ≥ f + 1 ∧ ∀ i ∈ S, IsSlashable i
```

> **Faithfulness:** Count: Lean `S.card ≥ f + 1` ↔ paper `≥ n/3` (since n/3+1 &gt; f, and under n = 3f+1 the n/3+1 quorum-overlap count equals f+1). The `Between` (history-scoped) family is the accountability *conclusion* (names the offending histories); the unscoped family is the *hypothesis* form used by Store statements. Paper does not separate these — a Lean modeling refinement, documented in the doc-comments.

---

### Lemma: Any chain past a finalized height contains the finalized block · `lem:mainsafety`

**Paper** — `height_filter_and_timeouts.tex:415-425`

<b>Lemma (Any chain past a finalized height contains the finalized block).</b> Unless ≥ n/3 validators are slashable: if C is finalized at height h, then C ≼ B for every block B with σ[B].h &gt; h.

**Lean** — `MainSafetyStatement (proved by main_safety_theorem)` · `DecoupledConsensus/State/TheoremStatements.lean:49`

```lean
def MainSafetyStatement (n f : ℕ) : Prop :=
  n = 3 * f + 1 →
    ∀ {B₁ B₂ C : Block n} {h_f : ℕ},
      Block.IdInjectiveOnAncestors B₁ B₂ →
        (chain₁ : Chain n B₁) →
          IsFinalizedOn chain₁ C h_f →
          (chain₂ : Chain n B₂) →
            (stateOf chain₂).h > h_f →
              AtLeastFThirdSlashableBetween chain₁ chain₂ f ∨ C ≼ B₂

theorem main_safety_theorem {f : ℕ} :
    MainSafetyStatement n f :=
  proof_main_safety_theorem
```

> **Faithfulness:** faithful, with two Lean-explicit hypotheses: (1) `n = 3*f + 1` fixes the exact-threshold instance (paper states the bound generically as ≥ n/3); (2) `Block.IdInjectiveOnAncestors B₁ B₂` — a scoped collision-resistance assumption (hashes injective on ancestors of the two compared tips), a Lean-added local hypothesis with no paper counterpart (the paper treats hash(C) as a faithful identifier). Conclusion-disjunct `AtLeastFThirdSlashableBetween` is the contrapositive of 'unless ≥ n/3 slashable'.

---

### Lemma: Finalized blocks form a chain · `lem:finchain`

**Paper** — `height_filter_and_timeouts.tex:427-442`

<b>Lemma (Finalized blocks form a chain).</b> Unless ≥ n/3 validators are slashable: any two finalized checkpoints (C, h), (C′, h′) are compatible, with C ≼ C′ whenever h ≤ h′.

**Lean** — `FinalizedBlocksFormChainStatement (proved by finalized_blocks_form_chain_theorem)` · `DecoupledConsensus/State/TheoremStatements.lean:65`

```lean
def FinalizedBlocksFormChainStatement (n f : ℕ) : Prop :=
  n = 3 * f + 1 →
    ∀ {B₁ B₂ C C' : Block n} {h_f h_f' : ℕ},
      Block.IdInjectiveOnAncestors B₁ B₂ →
        (chain₁ : Chain n B₁) →
          IsFinalizedOn chain₁ C h_f →
          (chain₂ : Chain n B₂) →
            IsFinalizedOn chain₂ C' h_f' →
            h_f ≤ h_f' →
              AtLeastFThirdSlashableBetween chain₁ chain₂ f ∨ C ≼ C'

theorem finalized_blocks_form_chain_theorem {f : ℕ} :
    FinalizedBlocksFormChainStatement n f :=
  proof_finalized_blocks_form_chain_theorem
```

> **Faithfulness:** faithful; same n=3f+1 and IdInjectiveOnAncestors caveats as MainSafetyStatement. Lean states the ordered form (C ≼ C' under h_f ≤ h_f'), which subsumes 'compatible' by symmetry; finality is the chain-scoped `IsFinalizedOn` predicate carrying the FinalizedCertificate evidence.

---

### Theorem: Accountable safety · `thm:safety`

**Paper** — `height_filter_and_timeouts.tex:444-450`

<b>Theorem (Accountable safety).</b> Unless ≥ n/3 validators are slashable, no two conflicting blocks can be finalized.

**Lean** — `AccountableSafetyStatement (proved by accountable_safety_theorem)` · `DecoupledConsensus/State/TheoremStatements.lean:81`

```lean
def AccountableSafetyStatement (n f : ℕ) : Prop :=
  n = 3 * f + 1 →
    ∀ {B₁ B₂ C C' : Block n} {h_f h_f' : ℕ},
      Block.IdInjectiveOnAncestors B₁ B₂ →
        (chain₁ : Chain n B₁) →
          IsFinalizedOn chain₁ C h_f →
          (chain₂ : Chain n B₂) →
            IsFinalizedOn chain₂ C' h_f' →
            AtLeastFThirdSlashableBetween chain₁ chain₂ f ∨ C ~ C'

theorem accountable_safety_theorem {f : ℕ} :
    AccountableSafetyStatement n f :=
  proof_accountable_safety_theorem
```

> **Faithfulness:** faithful; `C ~ C'` is block compatibility (comparable under ≼). Same n=3f+1 and IdInjectiveOnAncestors scoped-collision-resistance caveats. Drops the h_f ≤ h_f' ordering of lem:finchain since only compatibility is asserted. Proved facade is axiom-clean (no sorry/admit).

---

## Fork-choice store (sec:store)

### Definition: Store Σ · `def:store`

**Paper** — `height_filter_and_timeouts.tex:458-474`

<b>Definition (Store).</b> A node maintains a <i>store</i> Σ = (σ, T, F, J, h<sub>j</sub>, h<sub>max</sub>), where:<ul><li>σ is the <i>state map</i>, assigning each accepted block its per-chain post-state (Section: model);</li><li>T is the <i>block tree</i>, the set of accepted blocks;</li><li>F is the <i>store-finalized block</i>;</li><li>J is the <i>store root</i>: the block of the highest-key justification ever observed;</li><li>h<sub>j</sub> is the height component of that justification key;</li><li>h<sub>max</sub> ∈ ℕ is the maximum state-height σ[B].h over B ∈ T.</li></ul>The genesis store has T = {genesis}, F = J = genesis, h<sub>j</sub> = 0, h<sub>max</sub> = 1 (matching σ[genesis].h = 1 from the height definition). Section: healing discusses recovery-only metadata for witness tracking and activation; the base store and normal fork-choice are unchanged.

**Lean** — `Store` · `DecoupledConsensus/Store/Model/Basic.lean:56-72`

```lean
structure Store (n : ℕ) where
  entries : List (StoreEntry n)
  F : Block n
  J : Block n
  hj : ℕ
  hmax : ℕ
```

> **Faithfulness:** Faithful. The paper's σ partial map is realized indirectly: each StoreEntry carries the block plus a `Chain` witness, and σ[B] = stateOf chain (StoreEntry.state); this keeps the executable model from admitting inconsistent block-state maps. `entries` is a List (finite tree); duplicate-freedom is a reachability fact, not baked into the raw structure. Genesis matches the paper exactly (hmax=1, hj=0).

---

### Definition: Viable subtree · `def:viable`

**Paper** — `height_filter_and_timeouts.tex:483-492`

<b>Definition (Viable subtree).</b> A <i>leaf</i> of Σ.T is a block with no proper descendant in Σ.T. Define <i>viability</i> recursively:<ul><li>a leaf B is <i>viable</i> iff σ[B].h ≥ Σ.h<sub>max</sub> − 1;</li><li>an internal block B is viable iff some descendant of B in Σ.T is viable.</li></ul>The <i>viable subtree</i> is <code>viableTree</code>(Σ) := {B ∈ Σ.T : B is viable}. Equivalently, B ∈ <code>viableTree</code>(Σ) iff some leaf L ≽ B has σ[L].h ≥ Σ.h<sub>max</sub> − 1.

**Lean** — `Viable` · `DecoupledConsensus/Store/Model/Basic.lean:130-139`

```lean
def Viable (S : Store n) (B : Block n) : Prop :=
  Contains S B ∧
    ∃ D : Block n,
      Contains S D ∧ B ≼ D ∧ HasHeightAtLeast S D S.heightThreshold
```

> **Faithfulness:** Uses the high-descendant form (some accepted descendant D ≽ B meets the height filter) rather than the leaf-recursive form. Equivalent on valid stores by state-height monotonicity along ≼ (any high descendant extends to a leaf of ≥ height); the Lean docstring documents this choice, made to keep the executable filter simple and avoid a maximal-leaf search in getConfirmed. viableTree is a finite List acting as the set under reachable no-duplicate stores.

---

### Algorithm: Store and fork-choice root (genesis, onBlock, updateJustified, updateFinalized, getConfirmed) · `alg:store`

**Paper** — `height_filter_and_timeouts.tex:516-563`

<b>Algorithm (Store and fork-choice root).</b><pre>Genesis store Σ:
    Σ.T ← {genesis},  Σ.F ← genesis,  Σ.J ← genesis,
    Σ.h_j ← 0,  Σ.h_max ← 1,
    Σ.σ[genesis] ← σ_gen

onBlock(Σ, B):
    assert B.parent ∈ Σ.T
    assert Σ.F ≼ B
    Σ.T ← Σ.T ∪ {B}
    σ' ← stateTransition(Σ.σ[B.parent], B)
    Σ.σ[B] ← σ'
    Σ.h_max ← max(Σ.h_max, σ'.h)
    Σ ← updateJustified(Σ, σ'.J, σ'.h_j)
    Σ ← updateFinalized(Σ, σ'.F)
    return Σ

updateJustified(Σ, J', h'):      // F-filter, then running max
    if Σ.F ≼ J' and (h', hash(J')) > (Σ.h_j, hash(Σ.J)):
        Σ.J ← J';  Σ.h_j ← h'
    return Σ

updateFinalized(Σ, F'):
    if F' ≻ Σ.F and F' ≼ Σ.J and F' ∈ viableTree(Σ):
        Σ.F ← F'
    return Σ

getConfirmed(Σ, Ω):
    R ← Σ.J if Σ.h_max = Σ.h_j + 1 else Σ.F   // Σ.J is at the frontier
    return B ∈ viableTree(Σ) with B ≽ R and σ[B].h ≥ Σ.h_max − 1, depending on Ω</pre>

**Lean** — `acceptBlock?` · `DecoupledConsensus/Store/Model/Basic.lean:151-238`

```lean
def genesis (n : ℕ) : Store n where
  entries := [StoreEntry.genesis n]
  F := Block.genesis
  J := Block.genesis
  hj := 0
  hmax := 1

def acceptBlock? (S : Store n) (B : Block n) : Option (Store n) :=
  if S.containsBlockBool B then
    some S
  else
    match B with
    | Block.genesis => none
    | Block.mk bid parent newSlot votes =>
        match S.findChain? parent with
        | none => none
        | some parentChain =>
            if hSlot : newSlot > parent.slot then
              let child := Block.mk bid parent newSlot votes
              if Block.isAncestorOf S.F child then
                let entry : StoreEntry n :=
                  { block := child
                    chain := Chain.extend parentChain bid newSlot votes hSlot }
                let σ' := entry.state
                let S1 := S.addEntry entry
                let S2 := S1.updateJustified σ'.J σ'.hj
                some (S2.updateFinalized σ'.F)
              else
                none
            else
              none

def onBlock (S : Store n) (B : Block n) : Store n :=
  match S.acceptBlock? B with
  | some S' => S'
  | none => S

def updateJustified (S : Store n) (J' : Block n) (h' : ℕ) : Store n :=
  if S.shouldUpdateJustified J' h' then
    { S with J := J', hj := h' }
  else
    S

def updateFinalized (S : Store n) (F' : Block n) : Store n :=
  if S.shouldUpdateFinalized F' then
    { S with F := F' }
  else
    S

def getConfirmed (S : Store n) : List (Block n) :=
  S.entries.filterMap fun e =>
    if S.isConfirmedCandidateEntryBool e then some e.block else none
```

> **Faithfulness:** Faithful. updateJustified F-filter + lex-key running max, and updateFinalized's three guards (strict-descendant of F, ≼ J, viable) match exactly. onBlock is split into acceptBlock? (returns none on assertion failure) + onBlock (no-op on rejection); it also requires newSlot &gt; parent.slot (chain extension) where the paper's stateTransition advances slots. getConfirmed is the FINITE LIST of all candidate outputs (no oracle Ω selection); the paper's Ω disambiguation is modeled as the whole candidate set. confirmationRoot encodes the hmax=hj+1 cascade gate.

---

### Lemma: h_j monotonicity · `lem:Rs-key-monotone`

**Paper** — `height_filter_and_timeouts.tex:571-577`

<b>Lemma (h<sub>j</sub> monotonicity).</b> Σ.h<sub>j</sub> is non-decreasing over time, and the justification key (Σ.h<sub>j</sub>, hash(Σ.J)) is non-decreasing in lex order.

**Lean** — `future_hj_mono / future_key_mono` · `DecoupledConsensus/Store/Proof/Invariants.lean:828-844`

```lean
theorem future_hj_mono {S T : Store n}
    (hFuture : Future S T) : S.hj ≤ T.hj := by
  ...

theorem future_key_mono {S T : Store n}
    (hFuture : Future S T) : KeyLE S.hj S.J T.hj T.J := by
  ...
```

> **Faithfulness:** Faithful, proof-internal (under Store.Proof, not in TheoremStatements/ProvenTheorems public facade). Split into the height component (future_hj_mono) and the full lex key (future_key_mono over KeyLE). Stated over the Future relation rather than a temporal 'over time' quantifier.

---

### Theorem: Local irreversibility of finality · `thm:finperm`

**Paper** — `height_filter_and_timeouts.tex:579-585`

<b>Theorem (Local irreversibility of finality).</b> Once a node sets Σ.F = F, Σ.F descends from F at all future times.

**Lean** — `finality_irreversibility_theorem (FinalityIrreversibilityStatement)` · `DecoupledConsensus/Store/TheoremStatements.lean:180-181 ; DecoupledConsensus/Store/ProvenTheorems.lean:20-22`

```lean
def FinalityIrreversibilityStatement (n : ℕ) : Prop :=
  ∀ {S T : Store n}, Future S T → S.F ≼ T.F

theorem finality_irreversibility_theorem :
    FinalityIrreversibilityStatement n :=
  proof_finality_irreversibility_theorem
```

> **Faithfulness:** Faithful. 'At all future times' is the Future relation; conclusion S.F ≼ T.F is exactly Σ.F descending from the earlier F. Unconditional (no slashable hypothesis), matching the paper.

---

### Theorem: F ≼ J · `thm:fleqr`

**Paper** — `height_filter_and_timeouts.tex:587-601`

<b>Theorem (F ≼ J).</b> The store maintains Σ.F ≼ Σ.J at all times.

**Lean** — `f_ancestor_j_theorem (FAncestorJStatement)` · `DecoupledConsensus/Store/TheoremStatements.lean:184-185 ; DecoupledConsensus/Store/ProvenTheorems.lean:24-25`

```lean
def FAncestorJStatement (n : ℕ) : Prop :=
  ∀ {S : Store n}, Reachable S → S.F ≼ S.J

theorem f_ancestor_j_theorem : FAncestorJStatement n :=
  proof_f_ancestor_j_theorem
```

> **Faithfulness:** Faithful. 'At all times' is rendered as a Reachable-store invariant. Unconditional, matching the paper.

---

### Remark: Store-finalized invariant · `rem:fs-invariant`

**Paper** — `height_filter_and_timeouts.tex:603-606`

<b>Remark (Store-finalized invariant).</b> At all times Σ.F is either genesis or a block that was finalized on some chain; moreover, whenever a justification with target J⋆ has fired at height h⋆ on some chain processed by the node, the justification (J⋆, h⋆) was offered to <code>updateJustified</code> once J⋆ ≽ Σ.F at the moment of offering. Σ.F only advances via <code>updateFinalized</code> to F' = σ[B].F, and σ[B].F ≠ genesis requires the finality branch of <code>processHeightEvents</code> to have fired on B's chain, so F' is a block finalized on that chain.

**Lean** — ``

*(no standalone Lean statement — its content is realized inside a proof)*

> **Faithfulness:** Coverage gap as a named public statement: this is a proof-supporting remark, not separately exported. Its content is realized in Lean via the ProcessedCheckpoint premise (TheoremStatements.lean:72-73) carrying that a descriptor (C,h) appears in entries, and is consumed inside Store.Proof.Conditional (e.g. the noHigh / upgrade lemma chain). No standalone def/theorem mirrors the remark verbatim.

---

### Remark: viableTree shrinks only when hmax grows · `rem:viable-monotone`

**Paper** — `height_filter_and_timeouts.tex:608-612`

<b>Remark (viableTree shrinks only when Σ.h<sub>max</sub> grows).</b> Adding a block to Σ.T never removes any block from <code>viableTree</code>(Σ) unless the addition also increases Σ.h<sub>max</sub>. The viability threshold Σ.h<sub>max</sub> − 1 depends only on Σ.h<sub>max</sub>; while it is fixed, every previously viable leaf remains viable and every previously viable internal block retains its viable leaf witness, so <code>viableTree</code>(Σ) can only grow. Only an Σ.h<sub>max</sub> bump can disqualify leaves whose σ-height falls below the new threshold.

**Lean** — ``

*(no standalone Lean statement — its content is realized inside a proof)*

> **Faithfulness:** Coverage gap as a named public statement: a proof-supporting remark, used inside the F-viability induction (onBlock_F_viableBool in Store/Proof/Invariants.lean around line 426). Not exported as its own def/theorem in TheoremStatements/ProvenTheorems.

---

### Lemma: Σ.F is always viable · `lem:F-viable`

**Paper** — `height_filter_and_timeouts.tex:614-623`

<b>Lemma (Σ.F is always viable).</b> Σ.F ∈ <code>viableTree</code>(Σ) at all times.

**Lean** — `reachable_F_viableBool` · `DecoupledConsensus/Store/Proof/Invariants.lean:578-585`

```lean
theorem reachable_F_viableBool {S : Store n}
    (hS : Reachable S) : S.isViableBool S.F = true := by
  ...
```

> **Faithfulness:** Faithful, proof-internal (under Store.Proof). 'At all times' = Reachable invariant. Unconditional. Stated with the executable isViableBool = true rather than Prop-level Viable; equivalent on reachable stores.

---

### Corollary: getConfirmed is total · `cor:getConfirmed-total`

**Paper** — `height_filter_and_timeouts.tex:625-632`

<b>Corollary (getConfirmed is total).</b> For every store Σ and auxiliary Ω, <code>getConfirmed</code>(Σ, Ω) returns a block in <code>viableTree</code>(Σ) at σ-height ≥ Σ.h<sub>max</sub> − 1.

**Lean** — `getConfirmed_total_theorem (GetConfirmedTotalStatement)` · `DecoupledConsensus/Store/TheoremStatements.lean:190-193 ; DecoupledConsensus/Store/ProvenTheorems.lean:27-28`

```lean
def GetConfirmedTotalStatement (n : ℕ) : Prop :=
  ∀ {S : Store n}, Reachable S →
    (∃ B : Block n, B ∈ S.getConfirmed) ∧
      ∀ {B : Block n}, B ∈ S.getConfirmed → ConfirmedCandidate S B

theorem getConfirmed_total_theorem : GetConfirmedTotalStatement n :=
  proof_getConfirmed_total_theorem
```

> **Faithfulness:** Faithful, with totality made explicit as set nonemptiness (∃ B ∈ getConfirmed) since getConfirmed is the finite candidate List rather than an Ω-selected single output. The second conjunct certifies every output satisfies ConfirmedCandidate (viable, σ-height ≥ hmax−1, descends from confirmationRoot). Restricted to Reachable stores (the paper says 'every store Σ' but the proof needs F-viability, an invariant).

---

### Theorem: Fork-choice consistency · `thm:fcconsistency`

**Paper** — `height_filter_and_timeouts.tex:634-641`

<b>Theorem (Fork-choice consistency).</b> Once a node sets Σ.F = F, <code>getConfirmed</code>(Σ, Ω) returns a block descending from F at all future times, for every Ω.

**Lean** — `forkChoice_consistency_theorem (ForkChoiceConsistencyStatement)` · `DecoupledConsensus/Store/TheoremStatements.lean:197-199 ; DecoupledConsensus/Store/ProvenTheorems.lean:30-32`

```lean
def ForkChoiceConsistencyStatement (n : ℕ) : Prop :=
  ∀ {S T : Store n} {B : Block n},
    Reachable S → Future S T → B ∈ T.getConfirmed → S.F ≼ B

theorem forkChoice_consistency_theorem :
    ForkChoiceConsistencyStatement n :=
  proof_forkChoice_consistency_theorem
```

> **Faithfulness:** Faithful. 'For every Ω' becomes 'for every output B in the future getConfirmed set'. 'At all future times' is the Future relation. Unconditional, matching the paper.

---

### Lemma: Justification chain · `lem:certchain`

**Paper** — `height_filter_and_timeouts.tex:645-654`

<b>Lemma (Justification chain).</b> Unless ≥ n/3 validators are slashable: if F is finalized at height h<sub>f</sub> and a justification (C, h) has fired on any chain processed by the node with h ≥ h<sub>f</sub>, then F and C are compatible, with F ≺ C when h > h<sub>f</sub>.

**Lean** — `certchain_compatible` · `DecoupledConsensus/Store/Proof/Conditional.lean:80-101`

```lean
theorem certchain_compatible {f : ℕ} (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {Bf Bj F C : Block n} {h_f h : ℕ}
    (hId : Block.IdInjectiveOnAncestors Bf Bj)
    (chainF : Chain n Bf) {hFanc : F ≼ Bf}
    (hFstate : (stateOf chainF).F = F)
    (hFCert : FinalizedCertificate chainF F h_f hFanc)
    (chainJ : Chain n Bj)
    (hJ : (stateOf chainJ).J = C)
    (hhj : (stateOf chainJ).hj = h)
    (hle : h_f ≤ h) :
    F ~ C := by
  ...
```

> **Faithfulness:** Faithful, proof-internal. The paper's 'unless ≥ n/3 slashable' is n = 3f+1 (exact, not n≥3f+1) plus ¬AtLeastFThirdSlashable. Compatibility F ~ C is the conclusion; the strict F ≺ C for h&gt;h_f case is the separate certchain_record_strict_of_positive (Conditional.lean:179). Carries scoped id-injectivity IdInjectiveOnAncestors instead of a global hash-collision-freedom assumption.

---

### Lemma: Upgrade property · `lem:upgrade`

**Paper** — `height_filter_and_timeouts.tex:656-667`

<b>Lemma (Upgrade property).</b> Unless ≥ n/3 validators are slashable: if F is finalized at height h<sub>f</sub> and some block B with σ[B].J = F and σ[B].h<sub>j</sub> = h<sub>f</sub> has been processed by the node, then Σ.J ≽ F at all future times.

**Lean** — `upgrade_of_processed` · `DecoupledConsensus/Store/Proof/Conditional.lean:956-971`

```lean
theorem upgrade_of_processed {f : ℕ}
    (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {S T : Store n} (hS : Reachable S) (hFuture : Future S T)
    {F : Block n} {h_f : ℕ}
    (rF : FinalizationRecord F h_f)
    (hProc : ProcessedJustification S F h_f)
    (hId : rF.IdInjectiveAgainstStore T) :
    F ≼ T.J := by
  ...
```

> **Faithfulness:** Faithful, proof-internal. n=3f+1 exact + ¬AtLeastFThirdSlashable. The paper's 'block B with σ[B].J=F, σ[B].hj=h_f processed' is ProcessedCheckpoint S F h_f. 'At all future times' = Future S T. Scoped IdInjectiveAgainstStore in place of global collision-freedom.

---

### Lemma: Finalized blocks are viable · `lem:viable-finalized`

**Paper** — `height_filter_and_timeouts.tex:669-677`

<b>Lemma (Finalized blocks are viable).</b> Unless ≥ n/3 validators are slashable: if F is finalized at height h<sub>f</sub> and some block B with σ[B].J = F and σ[B].h<sub>j</sub> = h<sub>f</sub> has been processed by the node, then F ∈ <code>viableTree</code>(Σ) at all future times.

**Lean** — `future_finalized_viableBool_of_processedJustification` · `DecoupledConsensus/Store/Proof/Conditional.lean:292-302`

```lean
theorem future_finalized_viableBool_of_processedJustification {f : ℕ}
    (hn : n = 3 * f + 1)
    (hNoSlash : ¬ @AtLeastFThirdSlashable n f)
    {S T : Store n} (hS : Reachable S) (hFuture : Future S T)
    {Bf F : Block n} {h_f : ℕ}
    (hIdStore : IdInjectiveAgainstStore Bf T)
    (chainF : Chain n Bf) {hFanc : F ≼ Bf}
    (hFstate : (stateOf chainF).F = F)
    (hFCert : FinalizedCertificate chainF F h_f hFanc)
    (hProc : ProcessedJustification S F h_f) :
    T.isViableBool F = true := by
  ...
```

> **Faithfulness:** Faithful, proof-internal. n=3f+1 exact + ¬AtLeastFThirdSlashable. 'At all future times' = Future S T; conclusion in executable isViableBool = true (≡ viable-tree membership). Single-store form finalized_viableBool_of_processedJustification at Conditional.lean:274. Scoped id-injectivity.

---

### Theorem: Local acceptance of finality updates · `thm:finlive`

**Paper** — `height_filter_and_timeouts.tex:679-689`

<b>Theorem (Local acceptance of finality updates).</b> Unless ≥ n/3 validators are slashable: if a block B is processed by <code>onBlock</code> and σ[B].F = F', then after processing Σ.F ≽ F'.

**Lean** — `local_finality_update_theorem (LocalFinalityUpdateStatement)` · `DecoupledConsensus/Store/TheoremStatements.lean:204-213 ; DecoupledConsensus/Store/ProvenTheorems.lean:34-36`

```lean
def LocalFinalityUpdateStatement (n f : ℕ) : Prop :=
  n = 3 * f + 1 →
    ¬ @AtLeastFThirdSlashable n f →
      ∀ {S S' : Store n} {B : Block n} {σB : State n},
        Reachable S →
          S.containsBlockBool B = false →
          S.acceptBlock? B = some S' →
          AcceptedBlockState S' B σB →
          IdInjectiveAgainstStore B S' →
          σB.F ≼ S'.F

theorem local_finality_update_theorem {f : ℕ} :
    LocalFinalityUpdateStatement n f :=
  proof_local_finality_update_theorem
```

> **Faithfulness:** Faithful, public. n=3f+1 exact + ¬AtLeastFThirdSlashable as explicit hypotheses. Stated at the onBlock/acceptBlock? transition with a fresh block (containsBlockBool B = false) and σB = σ[B] (AcceptedBlockState). Scoped IdInjectiveAgainstStore; the comparability between the prior store finality and σB.F is derived internally, as in the paper proof.

---

### Theorem: Lock-in · `thm:lockin`

**Paper** — `height_filter_and_timeouts.tex:691-699`

<b>Theorem (Lock-in).</b> Unless ≥ n/3 validators are slashable: if block F is finalized at height h<sub>f</sub> on any chain, and some block B with σ[B].J = F and σ[B].h<sub>j</sub> = h<sub>f</sub> has been processed by the node, then Σ.J ≽ F at all future times, F ∈ <code>viableTree</code>(Σ) at all future times, and <code>getConfirmed</code>(Σ, Ω) always returns a descendant of F, for every Ω.

**Lean** — `lockIn_theorem (LockInStatement)` · `DecoupledConsensus/Store/TheoremStatements.lean:219-228 ; DecoupledConsensus/Store/ProvenTheorems.lean:38-40`

```lean
def LockInStatement (n f : ℕ) : Prop :=
  n = 3 * f + 1 →
    ¬ @AtLeastFThirdSlashable n f →
      ∀ {S T : Store n},
        Reachable S → Future S T →
          ∀ {F B : Block n} {h_f : ℕ},
            FinalizedWithStoreIds F h_f T →
            ProcessedCheckpoint S F h_f →
            B ∈ T.getConfirmed →
            F ≼ T.J ∧ T.isViableBool F = true ∧ F ≼ B

theorem lockIn_theorem {f : ℕ} :
    LockInStatement n f :=
  proof_lockIn_theorem
```

> **Faithfulness:** Faithful, public. n=3f+1 exact + ¬AtLeastFThirdSlashable. Three conjuncts F ≼ T.J, T viable for F, F ≼ B match the paper's three conclusions. FinalizedWithStoreIds packages the external finality certificate + scoped id-injectivity; ProcessedCheckpoint is the processed-descriptor premise. 'For every Ω' = for every output B in the future getConfirmed set.

---

### Theorem: Order independence · `thm:orderindep`

**Paper** — `height_filter_and_timeouts.tex:701-734`

<b>Theorem (Order independence).</b> Unless ≥ n/3 validators are slashable: the observable store view after folding the same available set of blocks through <code>onBlock</code> in any parent-first order depends only on that set, not on the order. In particular, two nodes with the same available blocks agree on (F, J, h<sub>j</sub>, h<sub>max</sub>), on the accepted subtree rooted at F, and hence on the possible outputs of <code>getConfirmed</code>. They need not agree on blocks outside the subtree of F: a block conflicting with the final F may have been accepted before finality moved at one node, while another node that first moved F would reject it.

**Lean** — `parentFirstReplay_liveEquivalent_theorem + parentFirstReplay_getConfirmed_theorem (ParentFirstReplayLiveEquivalentStatement, ParentFirstReplayGetConfirmedStatement)` · `DecoupledConsensus/Store/TheoremStatements.lean:234-268 ; DecoupledConsensus/Store/ProvenTheorems.lean:42-48`

```lean
def ParentFirstReplayLiveEquivalentStatement (n f : ℕ) : Prop :=
  n = 3 * f + 1 →
    ¬ @AtLeastFThirdSlashable n f →
      ∀ {input₁ input₂ : List (StoreEntry n)} {S T : Store n},
        ReplayEntriesOf input₁ S →
          ReplayEntriesOf input₂ T →
          ParentFirstEntries input₁ →
          ParentFirstEntries input₂ →
          (input₁.map StoreEntry.block).Nodup →
          (input₂.map StoreEntry.block).Nodup →
          Block.genesis ∉ input₁.map StoreEntry.block →
          Block.genesis ∉ input₂.map StoreEntry.block →
          InputIdInjective input₁ →
          InputBlockEquivalent input₁ input₂ →
          LiveEquivalent S T

def ParentFirstReplayGetConfirmedStatement (n f : ℕ) : Prop :=
  n = 3 * f + 1 →
    ¬ @AtLeastFThirdSlashable n f →
      ∀ {input₁ input₂ : List (StoreEntry n)} {S T : Store n} {B : Block n},
        ReplayEntriesOf input₁ S →
          ReplayEntriesOf input₂ T →
          ParentFirstEntries input₁ →
          ParentFirstEntries input₂ →
          (input₁.map StoreEntry.block).Nodup →
          (input₂.map StoreEntry.block).Nodup →
          Block.genesis ∉ input₁.map StoreEntry.block →
          Block.genesis ∉ input₂.map StoreEntry.block →
          InputIdInjective input₁ →
          InputBlockEquivalent input₁ input₂ →
          (B ∈ S.getConfirmed ↔ B ∈ T.getConfirmed)

theorem parentFirstReplay_liveEquivalent_theorem {f : ℕ} :
    ParentFirstReplayLiveEquivalentStatement n f :=
  proof_parentFirstReplay_liveEquivalent_theorem

theorem parentFirstReplay_getConfirmed_theorem {f : ℕ} :
    ParentFirstReplayGetConfirmedStatement n f :=
  proof_parentFirstReplay_getConfirmed_theorem
```

> **Faithfulness:** DEVIATION (documented in the Lean file header): the Lean replay result is stated as LiveEquivalent — agreement on (F,J,hj,hmax) plus entries IN the subtree rooted at the final F — rather than the paper's full-store claim. The paper explicitly notes nodes need NOT agree outside F's subtree (a pre-finality-accepted conflicting block may stay in entries on one node), which the executable store cannot retract; LiveEquivalent scopes equivalence to the observable live view, matching exactly the paper's caveat. Split into the store-view form (LiveEquivalent) and the getConfirmed-set form. n=3f+1 exact + ¬AtLeastFThirdSlashable. Requires Nodup, genesis ∉ input (genesis implicit from Store.genesis), and InputIdInjective (scoped collision-freedom).

---

### Lemma: Justifications stay at or below Σ.h_j (no-high-just) · `lem:no-high-just`

**Paper** — `height_filter_and_timeouts.tex:736-747`

<b>Lemma (Justifications stay at or below Σ.h<sub>j</sub>).</b> Unless ≥ n/3 validators are slashable, every justification (C, h) that has fired on any chain processed by the node satisfies h ≤ Σ.h<sub>j</sub> at all subsequent times.

**Lean** — `no_high_justifications / reachable_noHighJustifications` · `DecoupledConsensus/Store/Proof/Conditional.lean:665-687 (def NoHighJustifications: TheoremStatements.lean:99-100)`

```lean
def NoHighJustifications (S : Store n) : Prop :=
  ∀ {C : Block n} {h : ℕ}, ProcessedCheckpoint S C h → h ≤ S.hj

theorem reachable_noHighJustifications {S : Store n}
    (hS : Reachable S) : NoHighJustifications S := by
  ...
```

> **Faithfulness:** Faithful, proof-internal (NoHighJustifications def lives in TheoremStatements but is documented as a proof-internal helper consumed by the LockIn chain, not a public theorem). Conditional on n=3f+1 + ¬AtLeastFThirdSlashable inside the proof. 'At all subsequent times' is covered by future_no_high_justification over the Future relation. ProcessedCheckpoint is the 'justification (C,h) fired on a processed chain' premise.

---
