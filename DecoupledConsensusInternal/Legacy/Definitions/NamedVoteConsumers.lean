module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Definitions.NamedHeadReads
public import DecoupledConsensusInternal.Legacy.Assumptions.Regimes

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Vote-head, continuation and confirmation consumers 

Replacement bodies under the existing public names for `voteDutyHead`
(VoteHead.lean), `HonestProposalsConfirmedFrom` (Liveness.lean) and the seed
of `WeakVoteContinuation` (VoteSafety.lean). The vote head is the named
observation `voterHeadAt`; the honest proposal is the named duty's block,
its existence concluded and its emission stated on the named block; the
continuation's seed is the strong run's actual named proposal, whose
existence is part of the chosen round.
-/


namespace DecoupledConsensusModel
open Internal Execution Proofs.HealingSurface
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Replacement body for `Protocol.voteDutyHead`, same name and
type: the named vote-duty head observation. -/
def Protocol.voteDutyHead (S : Setup V) (rho : Run V) (v : V) (s : Slot) : Block V :=
  Internal.voterHeadAt S rho v s

/-- Replacement body for `Statements.HonestProposalsConfirmedFrom`: each later
honest proposal exists, is emitted as a named block at its proposal time, and
becomes exactly both confirmation fields at every honest confirmation duty. -/
def Statements.HonestProposalsConfirmedFrom (S : Setup V) (rho : Run V) (start : Slot) : Prop :=
  ∀ s, start < s → Protocol.confirmation_time S.E s ≤ rho.horizon →
    S.E.proposer s ∈ rho.honest →
    ∃ B : NamedBlock V, proposedBlockAt S rho s = some B ∧
      NamedRun.emits S rho (S.E.proposer s) (.block B) (Protocol.proposal_time S.E s) ∧
      ∀ v ∈ rho.honest,
        (rho.storeAt S v (Protocol.confirmation_time S.E s)).live_confirmed = B.erase ∧
        (rho.storeAt S v (Protocol.confirmation_time S.E s)).latest_confirmed = B.erase

/-- Replacement for the seed clause of `Statements.WeakVoteContinuation`
(VoteSafety.lean:65): the chosen round `m` carries the strong run's actual
named proposal at its opening slot, and the continuation's vote sources are
safe for its erased form. Splice as the body of the inner `∃ m` clause. -/
def Statements.WeakVoteContinuationSeed (S : Setup V) (rho : Run V) (cut gap : Round)
    (Continue : Round → Block V → Prop) : Prop :=
  ∃ m : Round, cut ≤ m ∧ m ≤ cut + gap ∧
    ∃ P : NamedBlock V, proposedBlockAt S rho (S.hc.opening_slot m) = some P ∧
      Continue m P.erase

/-- Replacement body for `Statements.BoundedSafetyRecovery` (Safety.lean:18):
the bounded round `m` is chosen together with the ORIGINAL run's actual named
proposal at its opening slot, once, before the universal continuation
clause; every continuation is then judged against that same erased seed.
No default block, no extra continuation premise. -/
def Statements.BoundedSafetyRecovery (S : Setup V) : Prop :=
  ∀ rho rGST gap extra n, Statements.StrongRecoveryPrefix S rho rGST gap extra n →
    ∃ m, n ≤ m ∧ m ≤ n + gap ∧ n + gap ≤ m + gap ∧
      ∃ P : NamedBlock V, proposedBlockAt S rho (S.hc.opening_slot m) = some P ∧
        ∀ rho', Statements.WeakContinuation S rho rho' (n + gap) →
          PhaseShiftSafety S rho' n (S.hc.opening_slot m) P.erase

end DecoupledConsensusModel

end
