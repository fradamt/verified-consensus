module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Definitions.NamedEvidenceInternal
public import DecoupledConsensusInternal.Legacy.Definitions.NamedDutyReads
public import DecoupledConsensusInternal.Legacy.Definitions.ConfirmedOutput
public import DecoupledConsensusInternal.Legacy.Definitions.Confirmation

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Restated liveness and confirmation statements 

Replacement bodies, same public names, for `UserProposalsConfirmedAfter`,
`RecurringFinalityFrom` and `HonestProposalFinalityFrom`. Two changes only:
the honest proposal is the named duty's block, whose existence is part of
the conclusion (no default and no vacuous `none` case), and every chain
height is read through `derive_named` on a named block in run scope, never
through the prior erased derivation.
-/


namespace DecoupledConsensusModel.Internal
open Execution Proofs.HealingSurface Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every honest proposal after `start` is the recorded confirmation of every
honest node at its confirmation time, and stays below every later
finality-aware user output. Existence of the proposal is concluded. -/
def UserProposalsConfirmedAfter (S : Setup V) (rho : Run V) (start : Slot) : Prop :=
  ∀ s, start < s → Protocol.confirmation_time S.E s ≤ rho.horizon →
    S.E.proposer s ∈ rho.honest →
    ∃ B : NamedBlock V, proposedBlockAt S rho s = some B ∧
      (∀ v ∈ rho.honest,
        (rho.storeAt S v (Protocol.confirmation_time S.E s)).latest_confirmed = B.erase) ∧
      (∀ v ∈ rho.honest, ∀ t,
        Protocol.confirmation_time S.E s ≤ t → t ≤ rho.horizon →
        Block.Preceq B.erase (confirmedOutputAt S rho v t))

/-- Recurring finality: any common checkpoint and finalized-height lower bound
advance by a constant round deadline to a new common checkpoint that is a
named run block of strictly larger named height. -/
def RecurringFinalityFrom (S : Setup V) (rho : Run V) (q0 : Round)
    (deadline : Round) : Prop :=
  ∀ (r : Round) (B : Block V) (h : Height), q0 ≤ r →
    (∀ v ∈ rho.honest,
      Block.Preceq B (rho.storeAt S v (S.a r)).F ∧
        h ≤ (rho.storeAt S v (S.a r)).core.finalized_height) →
    S.a (r + deadline) ≤ rho.horizon →
      ∃ (P : NamedBlock V) (h' : Height) (t : Time),
        NamedRun.blockInRun S rho P ∧
        Block.Preceq B P.erase ∧
          h < h' ∧
          (derive_named S.E S.cfg P).h = h' ∧
          S.a r ≤ t ∧
          t ≤ S.a (r + deadline) ∧
          ∀ v ∈ rho.honest,
            Block.Preceq P.erase (rho.storeAt S v t).F ∧
              h' ≤ (rho.storeAt S v t).core.finalized_height

/-- A strictly post-boundary honest proposal exists and lies below every honest
finalized checkpoint by a constant deadline relative to its own slot round. -/
def HonestProposalFinalityFrom (S : Setup V) (rho : Run V) (q : Round)
    (proposalDeadline : Round) : Prop :=
  ∀ s : Slot, 0 < s →
    healingBoundaryTime S q < Protocol.proposal_time S.E s →
    S.E.proposer s ∈ rho.honest →
    ∃ B : NamedBlock V, proposedBlockAt S rho s = some B ∧
      let due := S.hc.round_of s + 1 + proposalDeadline
      (S.a due ≤ rho.horizon →
        ∃ t : Time,
          Protocol.confirmation_time S.E s ≤ t ∧
            t ≤ S.a due ∧
            ∀ v ∈ rho.honest,
              Block.Preceq B.erase (rho.storeAt S v t).F)

end DecoupledConsensusModel.Internal

end
