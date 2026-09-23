module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.HandoverPreparedV3

@[expose] public section

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

structure SettledBootstrapPreparedV4 (S : Setup V) (rho : Run V)
    (fresh base : Round) (start : Slot) (P : NamedBlock V) (cap : Height) : Prop where
  settled : S.hc.opening_slot (base + S.hc.η_SG) ≤ start
  basePost : S.E.t_GST ≤ S.a base
  seed : ProtectedVoteSlotCommittee S rho start P.erase
  seedAll : ∀ w ∈ rho.honest, Block.Preceq P.erase (voterHeadAt S rho w start)
  confirmationSeedPrepared : ∀ v ∈ rho.honest,
    (Protocol.update_confirmation_with
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v start).cache)
      S.E S.hc (confStore S rho v start) start).live_confirmed = P.erase
  runBlock : RunBlock S rho P
  oldRows : WeakJoint.OldHeightRowsBounded S rho fresh cap
  heightCap : cap ≤ (Protocol.derive_named S.E S.cfg P).h
  frontierSeed : fresh = 0 ∨ ∀ w ∈ rho.honest,
    cap + 1 < (rho.storeBeforeTime S w
      (min (S.a (base + S.hc.η_SG)) (Protocol.vote_time S.E start))).h_max
  sgBoot : ∀ r, base ≤ r → r < base + S.hc.η_SG → ∀ w ∈ rho.honest,
    NamedRun.emits S rho w
      (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
      Block.Preceq (actionSGBlockAt S rho w r) P.erase
  confBoot : ∀ q, S.hc.opening_slot (base + S.hc.η_SG) ≤ q → q < start →
    ∀ w ∈ rho.honest, ∀ B,
    GenuineConfirmationWith
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
      S.E S.hc (confStore S rho w q) q B →
      Block.Preceq B P.erase
  fgAll : WeakJoint.FGWitnessesBelow S rho fresh base P.erase

/-- The latest-confirmed half of the prepared opening seed. It is separate
from the V4 bootstrap because its no-return proof needs the stronger seed
window. -/
def SettledBootstrapPreparedV4.LatestSeed (S : Setup V) (rho : Run V)
    (start : Slot) (P : NamedBlock V) : Prop :=
  ∀ v ∈ rho.honest,
    (Protocol.update_confirmation_with
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v start).cache)
      S.E S.hc (confStore S rho v start) start).latest_confirmed = P.erase

#print axioms SettledBootstrapPreparedV4
#print axioms SettledBootstrapPreparedV4.LatestSeed

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
