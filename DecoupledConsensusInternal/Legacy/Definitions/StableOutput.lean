module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.ModelVocabulary.Execution.Run
public import DecoupledConsensusModel.Protocol.Handlers
public import DecoupledConsensusInternal.Legacy.Definitions.ProposalSourcesInternal

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Public stable output: its record, its exposed value, and the regime bundle

Addendum 34 rulings 22 and 26. The store exposes three
nested tips, `F ⪯ get_stable ⪯ get_confirmed` (`NestedOutputs`). The stable
record `latest_stable` is written at the confirmation duty from the round's
G2 root projected onto the FG-root-filtered tree, the confirmation's own
candidate rule; `get_stable` reads it when finality reaches it and finality
otherwise. The predicates here are the stable-record twins of the
confirmation-record predicates in `Definitions/Confirmation.lean` and of the
confirmed-output predicates in `Definitions/ConfirmedOutput.lean`, plus the
canonicity bundle proved under each safety regime. -/



namespace DecoupledConsensusModel
namespace Internal

open Execution Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The stable chain exposed by a node at a run observation. -/
def stableOutputAt (S : Setup V) (rho : Run V) (v : V) (t : Time) : Block V :=
  Protocol.get_stable (rho.storeAt S v t).core

/-- Monotonicity of one node's stable record in a safe interval. -/
def StableRecordMonotoneFrom (S : Setup V) (rho : Run V) (t0 : Time) : Prop :=
  ∀ v ∈ rho.honest, ∀ t t', t0 ≤ t → t ≤ t' → t' ≤ rho.horizon →
    Block.Preceq (rho.storeAt S v t).latest_stable
      (rho.storeAt S v t').latest_stable

/-- Agreement of the stable records across honest nodes. -/
def StableRecordCompatibleFrom (S : Setup V) (rho : Run V) (t0 : Time) : Prop :=
  ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t', t0 ≤ t → t0 ≤ t' →
    t ≤ rho.horizon → t' ≤ rho.horizon →
    Block.compatible (rho.storeAt S u t).latest_stable
      (rho.storeAt S v t').latest_stable = true

/-- Stable records stay compatible with finality across honest nodes and
times, so a record that finality has not yet reached is never clipped by a
conflicting finalized block. -/
def StableRecordFinalityCompatibleFrom (S : Setup V) (rho : Run V) (t0 : Time) :
    Prop :=
  ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t', t0 ≤ t → t0 ≤ t' →
    t ≤ rho.horizon → t' ≤ rho.horizon →
    Block.compatible (rho.storeAt S u t).latest_stable
      (rho.storeAt S v t').F = true


/-- The stable record's canonicity bundle ( 26): the record only
extends, agrees across honest nodes, and stays on the finalized branch. A
THEOREM under each safety regime, from SG-root canonicity (every G2 root at
every honest node lies on the one SG chain, and finality lies on it); it feeds
the stable-output conclusions of the safety bundles. The ordering of the two
records, `latest_stable ⪯ latest_confirmed`, is not here: the confirmation
duty floors the confirmation record on the stable record at write time, so it
is a run invariant (`Protocol.StableBelowConfirmed`). -/
structure StableRecordCanonicalFrom (S : Setup V) (rho : Run V) (t0 : Time) :
    Prop where
  monotone : StableRecordMonotoneFrom S rho t0
  agree : StableRecordCompatibleFrom S rho t0
  finality : StableRecordFinalityCompatibleFrom S rho t0


/-- Stable-record growth from `start` with gap `gap`: in every round r from
`start`, some block B proposed by an honest proposer after round r's opening
lies strictly above every honest node's round-r stable record and is in every
honest node's stable record, and stable output, from round r+gap on. The stable
record lags the confirmation record (it is the G2 root, 22/26), so no
exact-equality clause is stated. -/
def StableRecordGrowthFrom (S : Setup V) (rho : Run V) (start : Slot) (gap : Round) : Prop :=
  ∀ r : Round, start ≤ S.hc.opening_slot r →
    S.a (r + gap) ≤ rho.horizon →
    ∃ B : NamedBlock V,
      (∃ s : Slot, S.hc.opening_slot r < s ∧ S.E.proposer s ∈ rho.honest ∧
        proposedBlockAt S rho s = some B) ∧
      ∀ v ∈ rho.honest,
        Block.Prec (rho.storeAt S v (S.a r)).latest_stable B.erase ∧
        ∀ t : Time, S.a (r + gap) ≤ t → t ≤ rho.horizon →
          Block.Preceq B.erase (rho.storeAt S v t).latest_stable ∧
          Block.Preceq B.erase (stableOutputAt S rho v t)

end Internal
end DecoupledConsensusModel

end
