module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.ModelVocabulary.Execution.Run
public import DecoupledConsensusInternal.Legacy.Interface

@[expose] public section

/-! # Standard vocabulary of the public bundle

The public bundle is indexed by time. Protocol schedule rounds appear only in
regime premises and in constants whose meaning is inherently round-based.
-/

namespace DecoupledConsensusModel
namespace Internal

open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A user-facing output: a getter on the node store. -/
abbrev Output (V : Type) := Protocol.Store V → Block V

/-- The output `g` read at node `v` and time `t`. -/
def readAt (S : Setup V) (rho : Run V) (g : Output V) (v : V) (t : Time) : Block V :=
  g (rho.storeAt S v t).core

/-- Two outputs do not conflict across honest reads from `t₀` to the horizon. -/
def ConsistentFrom (S : Setup V) (rho : Run V) (g₁ g₂ : Output V) (t₀ : Time) : Prop :=
  ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t' : Time,
    t₀ ≤ t → t ≤ rho.horizon → t₀ ≤ t' → t' ≤ rho.horizon →
    Block.compatible (readAt S rho g₁ u t) (readAt S rho g₂ v t') = true

/-- No two honest reads of `g` conflict from `t₀` on. -/
def AgreeFrom (S : Setup V) (rho : Run V) (g : Output V) (t₀ : Time) : Prop :=
  ConsistentFrom S rho g g t₀

/-- Each honest node's reads of `g` only extend from `t₀` on. -/
def MonotoneFrom (S : Setup V) (rho : Run V) (g : Output V) (t₀ : Time) : Prop :=
  ∀ v ∈ rho.honest, ∀ t t' : Time, t₀ ≤ t → t ≤ t' → t' ≤ rho.horizon →
    Block.Preceq (readAt S rho g v t) (readAt S rho g v t')

/-- Agreement and monotonicity for one output from `t₀`. -/
structure SafeFrom (S : Setup V) (rho : Run V) (g : Output V) (t₀ : Time) : Prop where
  agree : AgreeFrom S rho g t₀
  monotone : MonotoneFrom S rho g t₀

/-- Compatible output reads, or slashable evidence in the two stores. -/
def AccountablyConsistentFrom (S : Setup V) (I : Statements.Interface V) (rho : Run V)
    (g₁ g₂ : Output V) (t₀ : Time) : Prop :=
  ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t' : Time,
    t₀ ≤ t → t ≤ rho.horizon → t₀ ≤ t' → t' ≤ rho.horizon →
    Block.compatible (readAt S rho g₁ u t) (readAt S rho g₂ v t') = true ∨
      I.slashable (rho.storeAt S u t).core (rho.storeAt S v t').core

/-- One output is below another at every node and time. -/
def Prefix (S : Setup V) (rho : Run V) (g₁ g₂ : Output V) : Prop :=
  ∀ v t, Block.Preceq (readAt S rho g₁ v t) (readAt S rho g₂ v t)

/-- Block `P` is in every honest read of `g` at time `t`. -/
def InBy (S : Setup V) (rho : Run V) (g : Output V) (P : Block V) (t : Time) : Prop :=
  ∀ v ∈ rho.honest, Block.Preceq P (readAt S rho g v t)

/-- The honest proposal of slot `s` is `B`, through the interface. -/
def HonestProposalAt (I : Statements.Interface V) (rho : Run V) (s : Slot)
    (B : NamedBlock V) : Prop :=
  I.proposer s ∈ rho.honest ∧ I.proposedBlock rho s = some B

/-- Every honest proposal after `t₀` is included within `delay`. -/
def Included (S : Setup V) (I : Statements.Interface V) (rho : Run V) (g : Output V)
    (t₀ delay : Time) : Prop :=
  ∀ s : Slot, t₀ < I.proposalTime s → I.proposer s ∈ rho.honest →
    I.proposalTime s + delay ≤ rho.horizon →
    ∃ B : NamedBlock V, HonestProposalAt I rho s B ∧
      InBy S rho g B.erase (I.proposalTime s + delay)

/-- From any time `t ≥ t₀`, a provenance block is strictly above the reads at
`t` and is in every honest read by `t + D`. -/
def Growth (S : Setup V) (rho : Run V) (g : Output V) (t₀ D : Time)
    (prov : Time → NamedBlock V → Prop) : Prop :=
  ∀ t : Time, t₀ ≤ t → t + D ≤ rho.horizon →
    ∃ B : NamedBlock V, prov t B ∧
      (∀ v ∈ rho.honest, Block.Prec (readAt S rho g v t) B.erase) ∧
      InBy S rho g B.erase (t + D)

/-- A block proposed by an honest proposer strictly after `t`. -/
def honestAfter (I : Statements.Interface V) (rho : Run V) (t : Time)
    (B : NamedBlock V) : Prop :=
  ∃ s : Slot, t < I.proposalTime s ∧ HonestProposalAt I rho s B

/-- Provenance for finality: a named block of the run. -/
def runBlock (S : Setup V) (rho : Run V) (_t : Time) (B : NamedBlock V) : Prop :=
  NamedRun.blockInRun S rho B

end Internal
end DecoupledConsensusModel

end
