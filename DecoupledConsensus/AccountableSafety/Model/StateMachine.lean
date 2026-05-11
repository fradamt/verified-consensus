import DecoupledConsensus.AccountableSafety.Model.Blocks

namespace AccountableSafety

/-! # Accountable Safety Model: state machine

Protocol state, executable transition functions, valid chains, and `σ[B]`.
Proofs about these definitions live under `AccountableSafety.Proof`. -/

variable {n : ℕ}

open scoped Block

/-! ## State -/

/-- The state after some block on some chain. Mirrors the paper's tuple
    `(L, s, h, s_h, targets, timeouts, J, h_j, F, P)`. -/
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

namespace State

/-- The genesis state. Genesis is treated as pre-justified and pre-finalized
    at height 0; the genesis state-height is 1. -/
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

end State

/-! ## Justification, timeout, finality -/

/-- Convenience: validators who set their target to `T` in `σ.targets`. -/
def targetedSet (σ : State n) (T : Block n) : Finset (Validator n) :=
  Finset.univ.filter (fun i => σ.targets i = some T)

/-- Convenience: validators with their timeout marker set in `σ`. -/
def timedOutSet (σ : State n) : Finset (Validator n) :=
  Finset.univ.filter (fun i => σ.timeouts i = true)

/-- Justification: target `T` has a quorum of per-validator targets.
    Internal state-machine predicate; uses the strict 2/3 form for parsimony. -/
def Justified (σ : State n) (T : Block n) : Prop :=
  IsQuorumStrict n (targetedSet σ T)

/-- Timeout cert: quorum on timeout markers. -/
def TimeoutFires (σ : State n) : Prop :=
  IsQuorumStrict n (timedOutSet σ)

/-- Finality of the current `J` at height `hj`: `P` is a quorum. -/
def CurrentlyFinal (σ : State n) : Prop :=
  IsQuorumStrict n σ.P

/-- Executable justification test corresponding to `Justified`. -/
def justifiedBool (σ : State n) (T : Block n) : Bool :=
  isQuorumStrictBool n (targetedSet σ T)
/-- Executable timeout test corresponding to `TimeoutFires`. -/
def timeoutFiresBool (σ : State n) : Bool :=
  isQuorumStrictBool n (timedOutSet σ)

/-- Executable finality test corresponding to `CurrentlyFinal`. -/
def currentlyFinalBool (σ : State n) : Bool :=
  isQuorumStrictBool n σ.P


/-! ### Deterministic justified-target selection -/
/-- Deterministic replacement for the old classical `choose`: scan validators
    in index order and return as soon as a currently justified target appears. -/
def firstJustifiedTarget (σ : State n) : Option (Block n) :=
  (List.finRange n).findSome? fun i =>
    match σ.targets i with
    | none => none
    | some T => if justifiedBool σ T then some T else none


/-! ## Height freshness for an incoming vote -/

namespace Vote

/-- A justification vote with target `T` is fresh on a chain with state `σ`
    iff the target id resolves to a strict ancestor of `σ.L` with
    `σ.h = v.height ∧ T.slot ≥ σ.sh`.
    A timeout vote (`v.target = none`) is fresh iff `σ.h = v.height`. -/
def Fresh (σ : State n) (v : Vote n) : Prop :=
  match v.target with
  | none   => σ.h = v.height
  | some bid =>
      ∃ T, σ.L.findById bid = some T ∧
        σ.h = v.height ∧ T.slot ≥ σ.sh ∧ T.slot < σ.L.slot

end Vote

/-! ## State machine transitions -/

/-- The targets/timeouts core of vote processing — no `P` update. Splits
    out the inner state-machine update (Figure 1, the part above the
    `P`-gate) into its own definition so that case analysis about
    `targets` and `timeouts` is straightforward. -/
def processVoteCore (σ : State n) (v : Vote n) : State n :=
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

/-- Process a single vote against the current state.
    Implements `processVote` from Figure 1 (state machine):
    first apply `processVoteCore` (targets/timeouts update), then the
    finalize-commitment `P`-gate. -/
def processVote (σ : State n) (v : Vote n) : State n :=
  let σ' := processVoteCore σ v
  if v.finalize = some (σ'.hj, σ'.J.id) then
    { σ' with P := insert v.validator σ'.P }
  else σ'

/-- The finality micro-step: if `P` is a quorum, set `F ← J`. Otherwise no change.
    Splitting this out makes `processHeight` easier to reason about. -/
def applyFinality (σ : State n) : State n :=
  if currentlyFinalBool σ then { σ with F := σ.J } else σ

/-- The event body of one `processHeight`: finality, then justification (if any
    target has a quorum), else timeout (if a timeout quorum is set), else
    nothing. Justification uses `firstJustifiedTarget`, a deterministic scan
    over validators' current targets, so this transition is executable. -/
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

/-- `processHeight` is a wrapper around the height-event body. The TeX leak
    extension wraps this function, while the accountable-safety model keeps it
    equal to `processHeightEvents`. -/
def processHeight (σ : State n) : State n :=
  processHeightEvents σ

/-- `processSlot σ`: close an empty slot if the current slot has no block on
    this chain, then advance `s` to the next slot. Non-empty block slots are
    closed by `stateTransition` after `processBlock`, so this avoids double
    processing the same slot. -/
def processSlot (σ : State n) : State n :=
  if σ.L.slot < σ.s then
    { processHeight σ with s := σ.s + 1 }
  else
    { σ with s := σ.s + 1 }

/-- `processBlock σ B`: set head to `B`, then fold `processVote` over the
    votes embedded in `B`. Precondition `σ.s = B.slot` is the caller's
    responsibility. -/
def processBlock (σ : State n) (B : Block n) : State n :=
  B.votes.foldl processVote { σ with L := B }

/-! ## Chains and state-along-chain

We model a chain as an *indexed inductive type* `Chain : Block n → Type`,
where `Chain B` represents a valid history producing the chain whose tip is
`B`. The `extend` constructor encodes well-formedness — slot strictly greater
than the parent's slot — directly in the type. Blocks carry their own ids and
vote payloads, so the state at a block is determined by the block tree itself.

`stateTransition σ B` is the per-block transition: run `processSlot` enough
times to advance `σ.s` from its current value to `B.slot`, run `processBlock σ B`,
and then close the height events enabled by B's votes with `processHeight`. -/

/-- Iterate `processSlot` k times. -/
def iterateProcessSlot (σ : State n) : ℕ → State n
  | 0     => σ
  | k + 1 => iterateProcessSlot (processSlot σ) k

/-- Per-block transition. Advances slots from `σ.s` to `B.slot`, then runs
    `processBlock`. When `B.slot ≥ σ.s` (true on a well-formed chain) the
    iteration count is `B.slot - σ.s`; otherwise the truncating subtraction
    gives `0` and the precondition `σ.s = B.slot` may fail (but on a chain
    this case never arises). -/
def stateTransition (σ : State n) (B : Block n) : State n :=
  processHeight (processBlock (iterateProcessSlot σ (B.slot - σ.s)) B)

/-- A valid chain ending at block `B`. The `extend` constructor enforces slot
    monotonicity (`newSlot > parent.slot`) at the type level. The new block's
    id and votes are payloads of the block itself. -/
inductive Chain (n : ℕ) : Block n → Type where
  | genesis : Chain n Block.genesis
  | extend {parent : Block n}
           (c : Chain n parent)
           (bid : BlockId)
           (newSlot : ℕ)
           (votes : List (Vote n))
           (hSlot : newSlot > parent.slot) :
      Chain n (Block.mk bid parent newSlot votes)

/-- The state at the tip of a chain — the analogue of the paper's `σ[B]`.
    Since votes are embedded in blocks, `stateOf` depends only on the tip
    block `B` (modulo proof irrelevance on slot inequalities). -/
def stateOf {n : ℕ} {B : Block n} (chain : Chain n B) :
    State n :=
  match chain with
  | .genesis => State.genesis n
  | @Chain.extend _ parent c bid newSlot votes _ =>
      stateTransition (stateOf c) (Block.mk bid parent newSlot votes)

/-! ### Subchain extraction -/

private theorem ancestor_genesis_eq {B' : Block n}
    (h : B' ≼ Block.genesis) : B' = Block.genesis := by
  cases h with
  | refl => rfl

private theorem ancestor_mk_cases {B' parent : Block n} {bid s : ℕ} {vs : List (Vote n)}
    (h : B' ≼ Block.mk bid parent s vs) :
    B' = Block.mk bid parent s vs ∨ B' ≼ parent := by
  cases h with
  | refl => exact Or.inl rfl
  | step h' => exact Or.inr h'

/-- Extract the subchain ending at `B' ≼ B`. -/
def Chain.subchain {n : ℕ} :
    ∀ {B : Block n}, Chain n B → ∀ {B' : Block n}, B' ≼ B → Chain n B'
  | _, .genesis, B', h =>
      have hEq : B' = Block.genesis := ancestor_genesis_eq h
      hEq ▸ .genesis
  | _, @Chain.extend _ parent c bid newSlot votes hSlot, B', h =>
      if hEq : B' = Block.mk bid parent newSlot votes then
        hEq ▸ Chain.extend c bid newSlot votes hSlot
      else
        Chain.subchain c (by
          rcases ancestor_mk_cases h with hRefl | hStep
          · exact absurd hRefl hEq
          · exact hStep)


end AccountableSafety
