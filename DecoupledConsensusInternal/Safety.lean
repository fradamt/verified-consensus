module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.Evidence
public import DecoupledConsensusInternal.Invariants
public import DecoupledConsensusInternal.Definitions.NamedEvidence

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # P1 accountable safety (design note P1; PROTOCOL.md#the-complete-protocol)
Two finalizations either agree, or the attestations the two chains carry convict
at least `2q − W` of weight.
The statement is unconditional and assumption-free: no synchrony, no honest
majority, no fault bound, no store, no reachability. It is a property of the
transition and the two chains alone, which is why §6 and §7 cannot weaken it —
they change honest emission, never the transition or the evidence
(`the design note:11`).
Four shapes are settled by the archaeology

).
* **Chain level, over two block tips.** the previous repo quantifies over two chains
  and their tips; here `Block` carries its parent, so the chain *is* the tip and
  `derived_state` is a function of it. The previous `Chain`, `Chain.subchain` and
  `chain_unique` all disappear.
* **The conclusion is a disjunction, not an implication.** `evidence ∨
  compatible`, so a caller that knows the two finalizations conflict receives the
  evidence, rather than having to supply a conflict proof to a hypothesis.
* **The finalization hypothesis is a plain state predicate.** `h_F` is a
  `ChainState` field here, so the previous `FinalizedCertificate` hypothesis is not
  needed in the statement; it becomes a derived invariant on the proof side.
* **The height/target pair binds outside the signer set.** See
  `HasE1WeightAt` — this ordering is the whole content of the sharp claim, and
  getting it wrong was the defect the weighted repo's first review caught.
Mechanism stays out: no grades, no SG internals, no fork choice. The only model
objects named are the chain state's `F`/`h_F` fields, the carried attestations,
and E1/E2.
-/

namespace DecoupledConsensusModel
namespace Internal

open Protocol (HeightConfig)
open Protocol (HealConfig)
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- **P1, chain-level accountable safety** (design note P1; PROTOCOL.md#the-complete-protocol).

Two derived states that finalize `T₁` and `T₂` either agree — `T₁` and `T₂` are
compatible — or at least `2q − W` of weight is slashable between the two chains'
carried attestations.

The heights are quantified separately and unrelated: the three height-order
cases run different counting arguments, but the statement makes no case
distinction — that belongs to the proof.

`RootInjectiveOnAncestors` is the one hypothesis, and it is not an assumption
about the execution: it is the hash idealization the transition's root
comparisons need (modeling-choices rows 12, 4.1, P1.1), scoped to the two chains
rather than stated globally. -/
def ChainAccountableSafety (E : Env V) (cfg : HeightConfig) : Prop :=
  ∀ (B₁ B₂ : NamedBlock V) (T₁ T₂ : Block V) (h₁ h₂ : Height),
    RootInjectiveOnAncestors B₁.erase B₂.erase →
    NamedFinalizedAt E cfg B₁ T₁ h₁ → NamedFinalizedAt E cfg B₂ T₂ h₂ →
    HasSlashableWeightBetween E (chain_attestations B₁.erase) (chain_attestations B₂.erase) ∨
      Block.compatible T₁ T₂ = true

/-- **P1 sharp**: the same, with the evidence pinned to a single finality pair
and to E1 alone (PROTOCOL.md#the-complete-protocol).

Both counting arguments produce evidence against one common `⟨h, T⟩`, and
neither the unweighted nor the weighted repo's proof ever uses E2, so this is
the form the proof shape actually delivers. `ChainAccountableSafety` follows
from it by weakening E1 to `Slashable` and forgetting the pair — the conversion
is `Proofs.hasE1WeightAt_toSlashableWeight`.

**The pool order is free, and that is the correction.** `E1EvidenceForPair`
draws the finality pair from its *first* pool and the conflicting height pair
from its *second*, while the two hypotheses are symmetric in `B₁` and `B₂`. Which
chain supplies the finality pair is decided by the height order — the counting
argument runs from the **lower** finalized height, and the other chain is the one
that crossed it — so a form that fixes the orientation is false whenever
`h₂ < h₁`. `ChainAccountableSafetySharpOriented` below is that form, and
`Protocol.Counterexample` refutes it outright. The headline
`ChainAccountableSafety` is unaffected either way, because `Slashable` tests both
orientations (`Protocol.e1Fields`).

Prove this one; derive the headline. -/
def ChainAccountableSafetySharp (E : Env V) (cfg : HeightConfig) : Prop :=
  ∀ (B₁ B₂ : NamedBlock V) (T₁ T₂ : Block V) (h₁ h₂ : Height),
    RootInjectiveOnAncestors B₁.erase B₂.erase →
    NamedFinalizedAt E cfg B₁ T₁ h₁ → NamedFinalizedAt E cfg B₂ T₂ h₂ →
    (∃ p : FinalityPair,
        HasE1WeightAt E p (chain_attestations B₁.erase) (chain_attestations B₂.erase) ∨
          HasE1WeightAt E p (chain_attestations B₂.erase) (chain_attestations B₁.erase)) ∨
      Block.compatible T₁ T₂ = true

/-- P1 sharp with the evidence **orientation fixed** — the form the statement
surface carried before the review pass, kept because it is refuted by an actual
witness rather than merely unproved (PROTOCOL.md#the-complete-protocol).

`Protocol.Counterexample.not_chainAccountableSafetySharpOriented` exhibits
two chains finalizing at heights 3 and 2 whose only E1 evidence sits in the pool
order `(B₂, B₁)`. `Protocol.chainAccountableSafetySharp_of_le` is as much of
it as is true: it holds under `h₁ ≤ h₂`. -/
def ChainAccountableSafetySharpOriented (E : Env V) (cfg : HeightConfig) : Prop :=
  ∀ (B₁ B₂ : NamedBlock V) (T₁ T₂ : Block V) (h₁ h₂ : Height),
    RootInjectiveOnAncestors B₁.erase B₂.erase →
    NamedFinalizedAt E cfg B₁ T₁ h₁ → NamedFinalizedAt E cfg B₂ T₂ h₂ →
    (∃ p : FinalityPair,
        HasE1WeightAt E p (chain_attestations B₁.erase) (chain_attestations B₂.erase)) ∨
      Block.compatible T₁ T₂ = true

end Internal
end DecoupledConsensusModel

end
