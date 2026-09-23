module
public import DecoupledConsensusStatements.Generic.Interface

@[expose] public section

/-!
# Generic output properties

Purpose: define the safety, liveness, inclusion, persistence, and ordering
properties used by the review bundle.
An auditor checks that these predicates state output behavior only and do not
import proof implementations or concrete fixtures.

Defines: output observations, `SafeFrom`, `AccountablySafeFrom`, `LiveFrom`,
`IncludedFrom`, `PersistsFrom`, and `OutputOrder` with their helpers.
Read after: `Interface` and `Constants`.
Read next: `Conditions`.
-/

namespace DecoupledConsensusModel.Statements.Generic

open DecoupledConsensusModel

variable {V : Type} {P : DecoupledConsensusModel.Generic.ProtocolSpec V} [DecidableEq V]

/-- Two outputs do not conflict across honest reads from `t₀` to the horizon. -/
def ConsistentFrom (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) (g₁ g₂ : Output P)
    (t₀ : Time) : Prop :=
  ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t' : Time,
    t₀ ≤ t → t ≤ rho.horizon → t₀ ≤ t' → t' ≤ rho.horizon →
    Block.Compatible (readAt P rho g₁ u t) (readAt P rho g₂ v t')

/-- No two honest reads of `g` conflict from `t₀` on. -/
def AgreeFrom (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) (g : Output P)
    (t₀ : Time) : Prop :=
  ConsistentFrom P rho g g t₀

/-- Each honest node's reads of `g` only extend from `t₀` on. -/
def MonotoneFrom (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) (g : Output P)
    (t₀ : Time) : Prop :=
  ∀ v ∈ rho.honest, ∀ t t' : Time, t₀ ≤ t → t ≤ t' → t' ≤ rho.horizon →
    Block.Preceq (readAt P rho g v t) (readAt P rho g v t')

/-- Safety of `g` from `t₀`: honest reads never conflict and each honest node's reads only extend. -/
structure SafeFrom (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) (g : Output P)
    (t₀ : Time) : Prop where
  agree : AgreeFrom P rho g t₀
  monotone : MonotoneFrom P rho g t₀

/-- Compatible output reads, or slashable evidence in the two states. -/
def AccountablyConsistentFrom
    (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (I : Interface P) (rho : DecoupledConsensusModel.Generic.Run V P.Object)
    (g₁ g₂ : Output P) (t₀ : Time) : Prop :=
  ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t' : Time,
    t₀ ≤ t → t ≤ rho.horizon → t₀ ≤ t' → t' ≤ rho.horizon →
    Block.Compatible (readAt P rho g₁ u t) (readAt P rho g₂ v t') ∨
      I.slashable
        (DecoupledConsensusModel.Generic.Run.readAt P rho t u)
        (DecoupledConsensusModel.Generic.Run.readAt P rho t' v)

/-- Accountable safety of `g` from `t₀`: honest reads are compatible, or the two read states hold
slashable evidence. -/
def AccountablySafeFrom
    (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (I : Interface P) (rho : DecoupledConsensusModel.Generic.Run V P.Object)
    (g : Output P) (t₀ : Time) : Prop :=
  AccountablyConsistentFrom P I rho g g t₀

/-- One output is below another at every node and time. -/
def Prefix (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) (g₁ g₂ : Output P) : Prop :=
  ∀ v t, Block.Preceq (readAt P rho g₁ v t) (readAt P rho g₂ v t)

/-- The finalized, stable, and confirmed outputs are ordered by prefix. -/
structure OutputOrder (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (I : Interface P) (rho : DecoupledConsensusModel.Generic.Run V P.Object) : Prop where
  finalizedBelowStable : Prefix P rho I.finalized I.stable
  stableBelowConfirmed : Prefix P rho I.stable I.confirmed

/-- Block `B` is in every honest read of `g` at time `t`. -/
def InBy (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) (g : Output P)
    (B : Block V) (t : Time) : Prop :=
  ∀ v ∈ rho.honest, Block.Preceq B (readAt P rho g v t)

/-- The honest proposal of slot `s` is `B`, through the interface. -/
def HonestProposalAt (I : Interface P)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) (s : Slot)
    (B : Block V) : Prop :=
  I.proposer s ∈ rho.honest ∧ I.proposedBlock rho s = some B

/-- A block proposed by an honest proposer strictly after `t`. -/
def honestAfter (I : Interface P)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) (t : Time)
    (B : Block V) : Prop :=
  ∃ s : Slot, t < I.proposalTime s ∧ HonestProposalAt I rho s B

/-- Liveness of `g` from `t₀`: from every time `t ≥ t₀`, some block proposed by an honest proposer
after `t` is strictly above every honest read at `t` and in every honest read by `t + D`. -/
def LiveFrom (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (I : Interface P) (rho : DecoupledConsensusModel.Generic.Run V P.Object)
    (g : Output P) (t₀ D : Time) : Prop :=
  ∀ t : Time, t₀ ≤ t → t + D ≤ rho.horizon →
    ∃ B : Block V, honestAfter I rho t B ∧
      (∀ v ∈ rho.honest, Block.Prec (readAt P rho g v t) B) ∧ InBy P rho g B (t + D)

/-- Inclusion into `g` from `t₀`: every block proposed by an honest proposer after `t₀` is in every
honest read within `D` of its proposal. -/
def IncludedFrom (P : DecoupledConsensusModel.Generic.ProtocolSpec V) (I : Interface P)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) (g : Output P)
    (t₀ D : Time) : Prop :=
  ∀ s : Slot, t₀ < I.proposalTime s → I.proposer s ∈ rho.honest →
    I.proposalTime s + D ≤ rho.horizon →
    ∃ B : Block V, HonestProposalAt I rho s B ∧
      InBy P rho g B (I.proposalTime s + D)

/-- Persistence of `g`: every block in an honest read of `g` at `T` is in every honest read of `g`
at every time from `b₀` to the horizon. -/
def PersistsFrom (P : DecoupledConsensusModel.Generic.ProtocolSpec V)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) (g : Output P)
    (T b₀ : Time) : Prop :=
  ∀ v ∈ rho.honest, ∀ B, Block.Preceq B (readAt P rho g v T) →
    ∀ t, b₀ ≤ t → t ≤ rho.horizon → InBy P rho g B t

/-- A proposed block is in no honest read before its proposal time. -/
def NoFutureRead (P : DecoupledConsensusModel.Generic.ProtocolSpec V) (I : Interface P)
    (rho : DecoupledConsensusModel.Generic.Run V P.Object) (g : Output P) : Prop :=
  ∀ v ∈ rho.honest, ∀ t (s : Slot) (B : Block V),
    HonestProposalAt I rho s B → t < I.proposalTime s →
    ¬ Block.Preceq B (readAt P rho g v t)

end DecoupledConsensusModel.Statements.Generic

end
