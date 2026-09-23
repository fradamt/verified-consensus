module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Assumptions.Regimes
public import DecoupledConsensusInternal.Legacy.Definitions.VoteSafety
public import DecoupledConsensusInternal.Legacy.Definitions.ValidatorVoteSafety
public import DecoupledConsensusInternal.Legacy.Definitions.NamedVoteConsumers
public import DecoupledConsensusInternal.Legacy.Definitions.StableOutput

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Safety contracts, separate from liveness -/

namespace DecoupledConsensusModel
namespace Statements
open Internal Execution
variable {V : Type} [DecidableEq V] [Fintype V]


/-- A bounded strong prefix supplies safety for all later actual SG, FG and
Goldfish vote sources. `Admissible` exposes execution validity, partial
synchrony, and full participation as separate fields. The continuation exposes
execution validity and partial synchrony separately and needs only the stated
weak-participation conditions.

 (user): the temporary head premise is not public.

Internal safety contract (SG, FG and Goldfish vote sources): not
the user-facing claim, which is `StableRecordSafety`. -/
def VoteSafetyAfterRecovery (S : Setup V) : Prop :=
  ∀ extra, TimeoutDelayBound S extra → ∀ gap,
    ∃ cutScale, 0 < cutScale ∧
      ∀ rho rGST, Admissible S rho →
        Execution.HonestCommittees S rho.honest →
        BelowOneThird S rho.honest → S.E.t_GST ≤ S.a rGST →
        ProposerOpeningCarrierRecurrence S rho gap →
        WeakVoteContinuation S rho rGST gap cutScale


/-- User-facing safety of the stable record (rulings 22/26/29): at every
honest node the stable record is monotone, honest nodes' stable records are
pairwise compatible, and each is compatible with every honest node's finalized
block (`StableRecordCanonicalFrom`) — from genesis under weak participation, or
from the healing boundary of a bounded strong prefix. -/
structure StableRecordSafety (S : Setup V) : Prop where
  gstZero : ∀ rho, WeakGenesis S rho → StableRecordCanonicalFrom S rho 0
  /-- The continuation's `covered` premise reaches
  `healingBoundaryTime S (n + gap)` before the stable-record conclusion is
  required. -/
  afterGST : ∀ rho rGST gap extra n,
    StrongRecoveryPrefix S rho rGST gap extra n →
    ∃ m, n ≤ m ∧ m ≤ n + gap ∧
      ∀ rho', WeakContinuation S rho rho' (n + gap) →
        StableRecordCanonicalFrom S rho' (healingBoundaryTime S m)

end Statements
end DecoupledConsensusModel

end
