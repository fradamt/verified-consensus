import DecoupledConsensus.State.Model

namespace DecoupledConsensus

/-! # State Statements

Proof-free statement layer for the Section 2 accountable-safety results.

The executable definitions and certificate predicates live under
`State.Model`. This file contains only the public `Prop`-valued statements
that should be checked against the paper surface. Concrete proofs live under
`State.Proof`; `State.Properties` gives the proved facade.
-/

open scoped Block

namespace State

/-! ## Finality Vocabulary -/

/-- Chain-scoped finalization evidence. This is the preferred public predicate
    for accountability statements because it keeps the offending history
    available for slashable-witness extraction. -/
def IsFinalizedOn {B : Block n} (chain : Chain n B)
    (C : Block n) (h_f : ℕ) : Prop :=
  ∃ hC : C ≼ B,
    (stateOf chain).F = C ∧
      FinalizedCertificate chain C h_f hC

/-- Tip-scoped finalization evidence, retaining the old existential surface for
    callers that do not need the witnessing history. -/
def IsFinalized (C : Block n) (h_f : ℕ) (B : Block n) : Prop :=
  ∃ chain : Chain n B, IsFinalizedOn chain C h_f

/-! ## Accountable-Safety Statements -/

/-- **Main safety**. If `C` is finalized at height `h_f`,
    then every chain whose tip-state has advanced above `h_f` contains `C` as
    an ancestor of the tip, unless at least `f + 1` validators are slashable.

    The hash/id injectivity assumption is scoped to ancestors of the two chain
    tips being compared. -/
def MainSafetyStatement (n f : ℕ) : Prop :=
  n = 3 * f + 1 →
    ∀ {B₁ B₂ C : Block n} {h_f : ℕ},
      Block.IdInjectiveOnAncestors B₁ B₂ →
        (chain₁ : Chain n B₁) →
          IsFinalizedOn chain₁ C h_f →
          (chain₂ : Chain n B₂) →
            (stateOf chain₂).h > h_f →
              AtLeastFThirdSlashableBetween chain₁ chain₂ f ∨ C ≼ B₂

/-- **Finalized blocks form a chain**. Any two finalized
    checkpoints `(C, h_f)` and `(C', h_f')` with `h_f ≤ h_f'` are ordered as
    `C ≼ C'`, unless at least `f + 1` validators are slashable.

    The hash/id injectivity assumption is scoped to ancestors of the two chain
    tips being compared. -/
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

/-- **Accountable safety**. No two conflicting blocks
    can both be finalized unless at least `f + 1` validators are slashable.

    The hash/id injectivity assumption is scoped to ancestors of the two chain
    tips being compared. -/
def AccountableSafetyStatement (n f : ℕ) : Prop :=
  n = 3 * f + 1 →
    ∀ {B₁ B₂ C C' : Block n} {h_f h_f' : ℕ},
      Block.IdInjectiveOnAncestors B₁ B₂ →
        (chain₁ : Chain n B₁) →
          IsFinalizedOn chain₁ C h_f →
          (chain₂ : Chain n B₂) →
            IsFinalizedOn chain₂ C' h_f' →
            AtLeastFThirdSlashableBetween chain₁ chain₂ f ∨ C ~ C'

end State

end DecoupledConsensus
