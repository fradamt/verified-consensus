module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Assumptions.Weight
public import DecoupledConsensusInternal.Legacy.Definitions.NamedEvidenceInternal

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Pure and whole-run finality safety

The primary public claim is pure quorum intersection over two named chains.
Run-level corollaries transport it to run blocks and honest stores. They are
independent of GST, delivery, authenticity, and liveness premises. Transport
needs only event sorting and collision-free block roots; run agreement also
needs `SlashableBound`.
-/

namespace DecoupledConsensusModel
namespace Internal

open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Pure accountable finality safety. No run or execution premise. The scoped
root-injectivity premise is the collision-free hash idealization.

The lower finalization certificate and the other chain's height-crossing quorum
intersect in weight at least `2q - W`. If their entry roots are equal, root
injectivity makes the finalized targets compatible; if they differ, the
intersection supplies E1 evidence. -/
def PureAccountableFinalitySafety (S : Setup V) : Prop :=
  ∀ (B₁ B₂ : NamedBlock V) (T₁ T₂ : Block V) (h₁ h₂ : Height),
    RootInjectiveOnAncestors B₁.erase B₂.erase →
    NamedFinalizedAt S.E S.cfg B₁ T₁ h₁ →
    NamedFinalizedAt S.E S.cfg B₂ T₂ h₂ →
    HasSlashableWeightBetween S.E
        (chain_attestations B₁.erase) (chain_attestations B₂.erase) ∨
      Block.compatible T₁ T₂ = true

/-- Pure finality agreement is accountable safety with the slashable-evidence
branch excluded. It has no run, schedule, synchrony, or participation premise;
root injectivity is the collision-free hash idealization. -/
def PureFinalityAgreement (S : Setup V) : Prop :=
  ∀ (B₁ B₂ : NamedBlock V) (T₁ T₂ : Block V) (h₁ h₂ : Height),
    RootInjectiveOnAncestors B₁.erase B₂.erase →
    NamedFinalizedAt S.E S.cfg B₁ T₁ h₁ →
    NamedFinalizedAt S.E S.cfg B₂ T₂ h₂ →
    ¬ HasSlashableWeightBetween S.E
        (chain_attestations B₁.erase) (chain_attestations B₂.erase) →
      Block.compatible T₁ T₂ = true

/-- Conflicting finalizations have slashable evidence, without assuming that
the accountable bound holds. Chain evidence and store-pool evidence retain
their distinct scopes. Both event-prefix and time-indexed stores are covered. -/
structure WholeRunAccountableFinalitySafety (S : Setup V) (rho : Run V) : Prop where
  chains : ∀ (B₁ B₂ : NamedBlock V) T₁ T₂ h₁ h₂,
    RunBlock S rho B₁ → RunBlock S rho B₂ →
    NamedFinalizedAt S.E S.cfg B₁ T₁ h₁ → NamedFinalizedAt S.E S.cfg B₂ T₂ h₂ →
    HasSlashableWeightBetween S.E (chain_attestations B₁.erase)
      (chain_attestations B₂.erase) ∨
      Block.compatible T₁ T₂ = true
  eventPrefixes : ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ i j,
    HasSlashableWeightBetween S.E
        (store_attestations (rho.stateBefore S i u).st.core)
        (store_attestations (rho.stateBefore S j v).st.core) ∨
      Block.compatible (rho.stateBefore S i u).st.F (rho.stateBefore S j v).st.F = true
  reads : ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t',
    HasSlashableWeightBetween S.E
        (store_attestations (rho.storeAt S u t).core)
        (store_attestations (rho.storeAt S v t').core) ∨
      Block.compatible (rho.storeAt S u t).F (rho.storeAt S v t').F = true

/-- Unconditional finality safety over one complete run.

The first clause compares targets finalized by arbitrary run blocks. The second
compares finalized roots held by arbitrary honest stores at arbitrary
instants. -/
def WholeRunFinalitySafety (S : Setup V) (rho : Run V) : Prop :=
  (∀ (B₁ B₂ : NamedBlock V) T₁ T₂ h₁ h₂,
    RunBlock S rho B₁ → RunBlock S rho B₂ →
    NamedFinalizedAt S.E S.cfg B₁ T₁ h₁ →
    NamedFinalizedAt S.E S.cfg B₂ T₂ h₂ →
    Block.compatible T₁ T₂ = true) ∧
  (∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t',
      Block.compatible (rho.storeAt S u t).F (rho.storeAt S v t').F = true)

/-- The exact execution premises used by the whole-run finality proofs.

This record does not include delivery, authenticity, or synchrony. Those are
not needed for accountable finality safety. -/
structure FinalityExecution (S : Setup V) (rho : Run V) : Prop where
  sorted : rho.events.Pairwise (fun e f => NamedEvent.key e ≤ NamedEvent.key f)
  rootCollisionFree : RootCollisionFree S rho

/-- Finality's primary public claim is pure quorum intersection: the lower
finalization certificate intersects the other chain's height-crossing quorum
in weight at least `2q - W`; equal entry roots imply compatibility by the
collision-free hash idealization, and different roots give E1 evidence.

The run-level clauses only transport this result to honest stores and reads.
That transport needs event sorting and collision-free roots, but no other
schedule field and no delivery, authenticity, synchrony, recovery, or liveness
premise. -/
structure FinalitySafety (S : Setup V) : Prop where
  accountable : PureAccountableFinalitySafety S
  agreement : PureFinalityAgreement S
  runAccountable : ∀ rho, FinalityExecution S rho →
    WholeRunAccountableFinalitySafety S rho
  runAgreement : ∀ rho, FinalityExecution S rho → SlashableBound S rho →
    WholeRunFinalitySafety S rho

end Internal
end DecoupledConsensusModel

end
