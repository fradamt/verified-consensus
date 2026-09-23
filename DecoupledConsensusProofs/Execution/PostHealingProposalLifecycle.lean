module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.ProposalLifecycleCore
public import DecoupledConsensusProofs.Generic.CanonicalSuffix
public import DecoupledConsensusProofs.Protocol.Schedule.CandidateSafety
public import DecoupledConsensusProofs.Protocol.Handlers.UserConfirmationRecovery

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Exact post-healing proposal lifecycle

This file consumes the produced proposal-chain suffix at one honest proposal
slot. The suffix identifies the exact honest vote outputs. The internal
execution projection supplies only the local confirmation-store facts needed by
`live_confirmed_eq`; no fixed canonical chain or whole-prefix history is used.

**Named-runtime proof (design note).** 
quantifies the proposal at every proposal-facing site: the retired total
`proposedBlock S rho s` becomes an explicit named witness `B` bound by
`hB: Statements.Instantiation.proposedBlockAt S rho s = some B`, with `B.erase` in
every geometric position; `DecoupledConsensusModel.Proofs.HealingSurface.proposedBlockAt_isSome` supplies
that witness unconditionally where a caller needs one. The moving endpoint
`End` (`CanonicalSuffixAtIndex`) is `Nat → NamedBlock V`; every
endpoint use below reads `.erase`. `Proofs.Optimistic.HonestVotesName` is
`Proofs.HealingSurface.NamedHonestVotesName` (`NamedLifecycle.lean`). The
`Admissible.toScheduleWellFormed` projection is gone: a bundled
`ScheduleWellFormed` argument is `adm.toNamedAdmissibleCore
.toNamedScheduleWellFormed`, while a single flattened field
(`adm.tick_total`) still resolves directly.

**Retired (no cone consumer).** `confirmationLatestDispositionAt_of_dutyExecution`
had no consumer anywhere in the union cone. Its old proof rewrote through
`Protocol.CandidateSafety.latest_confirmed_eq_update` and
`update_confirmation_latest_disposition`; the contract-carrying analogue of
the second step is not a mechanical restatement (it needs
`Protocol.Main.update_confirmation_with_live_confirmed`, from a module
this one does not otherwise import, and reproduces
`Protocol.CandidateSafety.confirmationAbsorbedAtEvaluation`'s own
argument rather than reusing it). Byte-exact original archived at
`the compatibility layer`
.

**Open (class d), — frozen public boundary.**
`honestProposalLifecycleFrom_of_canonicalSuffixExecution` remains absent. The
restored `UserConfirmationRecoveryRun` producer now supplies the exact named
record equality. No live caller exists in this selection module. The next public
statement has no head-premise field:

```lean
def HonestProposalLifecycleFrom
    (S: Setup V) (rho: Run V) (t0: Time): Prop:=
  ∀ s: Slot, 0 < s →
    t0 < Protocol.proposal_time S.E s →
    S.E.proposer s ∈ rho.honest →
    Protocol.confirmation_time S.E s ≤ rho.horizon →
      ∃ B: NamedBlock V, proposedBlockAt S rho s = some B ∧
      rho.emits S (S.E.proposer s) (NamedObject.block B)
          (Protocol.proposal_time S.E s) ∧
        ∀ v ∈ rho.honest,
          (rho.storeAt S v (Protocol.confirmation_time S.E s)).live_confirmed = B.erase ∧
            (rho.storeAt S v (Protocol.confirmation_time S.E s)).latest_confirmed = B.erase
```

earlier carries the corresponding handover field:

```lean
retainedStableBelowHead: RetainedStableBelowHeadFrom S rho
  (strongHeadsThreshold S rho (fixedPostGSTRound S) gap extra)
```

The statement layer is frozen. This is a, not a proof-layer
change.
-/



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]



/-- The exact public proposal block is the object emitted by its honest
proposal handler (: `B` is the named witness from `hB`, not a total
reader). -/
theorem proposedBlock_emitted_of_admissible
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hs : 0 < s)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E s ≤ rho.horizon)
    {B : NamedBlock V} (hB : Statements.Instantiation.proposedBlockAt S rho s = some B) :
    rho.emits S (S.E.proposer s) (Object.block B)
      (Protocol.proposal_time S.E s) :=
  (Proofs.Optimistic.proposalTick S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
    s hs hprop hhor hB).2





end Protocol
end DecoupledConsensusModel

end
