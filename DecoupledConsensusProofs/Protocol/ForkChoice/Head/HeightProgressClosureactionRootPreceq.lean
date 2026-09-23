module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.NamedLifecycle
public import DecoupledConsensusProofs.Objects.ActionRound

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Height-progress closure: the pinned `actionRootPreceq` premise

`fixedHeightJustificationRoot_boundedProposalLifecycle_of_proposerRecurrence_of_faultBound`
(`FixedHeightRootClaimFourOuterRun.lean:74`) carries the pinned premise

```
_of_actionRootPreceq: ∀ (q: Round) (P: NamedBlock V),
  proposedBlockAt S rho (S.hc.opening_slot q) = some P →
  ∀ v ∈ rho.honest,
    let n:= actionReadAt S rho v q
    Block.Preceq
      (Protocol.get_sg_root_with (NamedProfile.gradeContract n.cache)
        S.E S.hc n.st.core.toHealing q) P.erase
```

The earlier tree derives exactly this fact (`hactionRoot`,
`FixedHeightRootClaimFourOuterRun.lean:420-437` in
`decoupled-consensus-model`) from the round's confirmation read, not from the
public hypotheses: the action store is the confirmation store after the
confirmation duty, the duty does not move the prepared anchor, and the
confirmation read's own `anchor` field supplies the order. The pin's binder
hoists that fact out of the round it was proved at and quantifies it over
EVERY round, which the protocol does not give: at a round whose proposer read
is behind an honest reader's finalized root, the reader's prepared anchor is
already deeper than the block the proposal duty computes on that read.

This module therefore ports earlier's step in its two reusable forms. The
pointwise form is the exact analogue of earlier's `hactionRoot`; the pin form has
the pinned conclusion verbatim over the single residual premise
`NamedSGOpeningConfirmationRead`, which the consumer already holds at its own
round (`FixedHeightRootClaimFourOuterRun.lean:478`, `hconfirmation`).
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.NamedRecoveryRead

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The confirmation duty writes only `live_confirmed`, `latest_stable` and
`latest_confirmed`; the prepared anchor reads the finality projection and the
clipped frame, so it is unchanged. earlier's `getSgRoot_updateConfirmation`. -/
private theorem getSgRootWith_updateConfirmation
    (c : DecoupledConsensusModel.Protocol.Cache V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.NamedStore V) (s : Slot) (r : Round) :
    Protocol.get_sg_root_with (NamedProfile.gradeContract c) E hc
        (Protocol.NamedDuties.update_confirmation_with
          (NamedProfile.gradeContract c) E hc st s).core.toHealing r =
      Protocol.get_sg_root_with (NamedProfile.gradeContract c) E hc
        st.core.toHealing r := rfl

#print axioms getSgRootWith_updateConfirmation

/-- earlier's `hactionRoot` step, pointwise in the round, the reader and the
proposal: the prepared SG root at an honest reader's round-`q` action read is
the one its confirmation read of the opening slot already holds, so the
confirmation read's `anchor` field orders it below the proposal. -/
theorem actionRootPreceq_of_namedConfirmationRead
    (S : Setup V) {rho : Run V} {q : Round} {v : V} {P : NamedBlock V}
    (hconf : NamedSGOpeningConfirmationRead S rho (S.hc.opening_slot q) v P) :
    Block.Preceq
      (Protocol.get_sg_root_with
        (NamedProfile.gradeContract (actionReadAt S rho v q).cache)
        S.E S.hc (actionReadAt S rho v q).st.core.toHealing q) P.erase := by
  have hct : Protocol.confirmation_time S.E (S.hc.opening_slot q) = S.a q :=
    (Protocol.a_eq_confirmation_time S.hc S.E q).symm
  have hread : confirmationInputRead S rho v (S.hc.opening_slot q) =
      NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBeforeTime S rho (S.a q) v) (S.a q) := by
    simp only [confirmationInputRead, NamedActionReads.confirmationReadAt, hct]
  have hanchor := hconf.anchor
  rw [hread] at hanchor
  have hs : (NamedActionReads.confirmationReadFrom S
      (NamedRun.stateBeforeTime S rho (S.a q) v) (S.a q)).st.core.s =
      S.E.slotOf (S.a q) := rfl
  rw [hs, Proofs.HealingLemmas.ActionRound.round_of_slotOf_a] at hanchor
  have hcache : (actionReadAt S rho v q).cache =
      (NamedActionReads.confirmationReadFrom S
        (NamedRun.stateBeforeTime S rho (S.a q) v) (S.a q)).cache := rfl
  have hst : (actionReadAt S rho v q).st =
      Protocol.NamedDuties.update_confirmation_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadFrom S
            (NamedRun.stateBeforeTime S rho (S.a q) v) (S.a q)).cache)
        S.E S.hc
        (NamedActionReads.confirmationReadFrom S
          (NamedRun.stateBeforeTime S rho (S.a q) v) (S.a q)).st
        (S.E.slotOf (S.a q) - 1) := rfl
  rw [hcache, hst, getSgRootWith_updateConfirmation]
  exact hanchor

#print axioms actionRootPreceq_of_namedConfirmationRead





end HealingSurface
end Proofs
end DecoupledConsensusModel

end
