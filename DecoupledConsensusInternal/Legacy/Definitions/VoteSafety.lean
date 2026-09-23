module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Definitions.ActionSources
public import DecoupledConsensusInternal.Legacy.Definitions.SafetyRegimes
public import DecoupledConsensusInternal.Legacy.Definitions.NamedVoteConsumers

@[expose] public section

/-! # Safety of actual consensus sources

These conclusions refer to protocol duties, not to arbitrary calls to a head
function. An FG source retains its checkpoint witness even if the validator
client emits a timeout. The time guards include the last actual vote in a run.
-/

namespace DecoupledConsensusModel
namespace Statements

open Internal Execution Protocol Proofs.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Confirmation, SG, and FG sources stay below subsequent Goldfish vote heads.
The final field identifies the roots in the actual emitted Goldfish votes. -/
structure VoteSourcesSafeAt (S : Setup V) (rho : Run V)
    (cut : Round) (d : Slot) (P : Block V) : Prop where
  seed : ∀ v ∈ rho.honest, Block.Preceq P (voteDutyHead S rho v d)
  live : ∀ q, S.hc.opening_slot cut ≤ q → q < d →
    Protocol.confirmation_time S.E q ≤ rho.horizon →
    ∀ w ∈ rho.honest, ∀ v ∈ rho.honest,
      Block.Preceq (rho.storeAt S w (Protocol.confirmation_time S.E q)).live_confirmed
        (voteDutyHead S rho v d)
  actions : ∀ r, cut ≤ r → S.a r < Protocol.vote_time S.E (d + 1) →
    S.a r ≤ rho.horizon → ∀ w ∈ rho.honest, ∀ v ∈ rho.honest,
      Block.Preceq (Protocol.get_fg_root (actionStoreAt S rho w r).toHealing.toFG)
        (voteDutyHead S rho v d) ∧
      Block.Preceq (actionStoreAt S rho w r).live_confirmed (voteDutyHead S rho v d) ∧
      (rho.emits S w (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
        Block.Preceq (actionSGBlockAt S rho w r) (voteDutyHead S rho v d)) ∧
      (∀ T, fgConfirmationWitness S (actionStoreAt S rho w r) = some T →
        Block.Preceq T (voteDutyHead S rho v d))
  votes : ∀ v ∈ rho.honest, ∀ u : GoldfishVote V, ∀ t,
    rho.emits S v (Object.gfVote u) t → u.slot = d →
      u.head = (voteDutyHead S rho v d).root

/-- The safety cut has an explicit constant bound from the post-GST round.
The bound does not depend on the run horizon or the early height frontier. -/
noncomputable def safetyCutBound (S : Setup V) (rho : Run V)
    (rGST progressLag : Round) : Round :=
  rGST + 1 + (1 + (S.cfg.D + S.cfg.K + 5) * progressLag) +
    2 * progressLag + 1 + S.hc.η_SG


/-- A finite strong run supplies a bounded cut for safety of later votes.
The continuation can use dynamic participation and its own honest set. Its
four execution-validity families and partial synchrony are separate premises.

 (user): the temporary head premise is not public. -/
def WeakVoteContinuation (S : Setup V) (rho : Run V)
    (rGST gap progressLag : Round) : Prop :=
  ∃ cut : Round, rGST ≤ cut ∧ cut ≤ safetyCutBound S rho rGST progressLag ∧
    (Protocol.confirmation_time S.E (S.hc.opening_slot (cut + gap)) ≤ rho.horizon →
      WeakVoteContinuationSeed S rho cut gap (fun m P =>
        ∀ rho', ExecutionValid S rho' → PartialSynchrony S rho' →
          Execution.HonestCommittees S rho'.honest →
          Execution.SlashableBound S rho' →
          AgreesUntil rho rho' (Protocol.confirmation_time S.E (S.hc.opening_slot m)) →
          (∀ r, cut ≤ r → S.a (r - 1) ≤ rho'.horizon →
            AwakeWindowMajority S.E (fun v => (S.node v).awake)
              rho'.honest S.hc.η_SG r) →
          ∀ d, S.hc.opening_slot m ≤ d → Protocol.vote_time S.E d ≤ rho'.horizon →
            VoteSourcesSafeAt S rho' cut d P))

end Statements
end DecoupledConsensusModel

end
