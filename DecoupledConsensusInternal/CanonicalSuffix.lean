module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Internal.Observations
public import DecoupledConsensusInternal.Internal.ProposalLifecycle
public import DecoupledConsensusInternal.Definitions.FinalityLiveness
public import DecoupledConsensusInternal.Definitions.Confirmation
public import DecoupledConsensusInternal.Availability

@[expose] public section

/-!
# Post-healing canonical suffix contracts

This Props-only layer names the event-indexed observations made by an honest
`on_tick_emit` call. The observation stages follow the handler order exactly:
proposal parent, proposed block, vote head, confirmation output, then action
head. The moving endpoint orders only proposal-chain stages: proposal parent,
proposed block, and an honest-proposer vote head. Confirmation and action remain
exact raw observations for separate lifecycle proofs.
-/

namespace DecoupledConsensusModel
namespace Internal

open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Exact `on_tick_emit` stores -/

/-! ## Exact staged block values -/

/-! ## Moving canonical suffix -/
/-- A moving endpoint for the proposal-chain observation suffix.

Every endpoint has run provenance and moves monotonically. Each proposal-chain
observation is between the endpoint before and after its event. `ordered` adds
the intra-event order for those stages. Raw confirmation and action observations
are intentionally outside both claims. -/
structure CanonicalSuffixAtIndex
    (S : Setup V) (rho : Run V) (n0 : Nat)
    (End : Nat → NamedBlock V) : Prop where
  endpointRun : ∀ i, n0 ≤ i → RunBlock S rho (End i)
  endpointMono : ∀ i, n0 ≤ i → Block.Preceq (End i).erase (End (i + 1)).erase
  sandwich : ∀ i stage B, n0 ≤ i → ProposalChainStage stage →
    HonestCanonicalObservationAtIndex S rho i stage B →
      Block.Preceq (End i).erase B ∧ Block.Preceq B (End (i + 1)).erase
  ordered : ∀ i stage B j laterStage C,
    n0 ≤ i → n0 ≤ j →
    ProposalChainStage stage → ProposalChainStage laterStage →
    HonestCanonicalObservationAtIndex S rho i stage B →
    HonestCanonicalObservationAtIndex S rho j laterStage C →
    (i < j ∨ (i = j ∧ stage ≤ laterStage)) →
      Block.Preceq B C

/-- Existence of an event-indexed proposal-chain suffix after a named boundary
vote. The index and moving endpoint are existential proof witnesses. -/
def CanonicalSuffixFrom
    (S : Setup V) (rho : Run V) (t0 : Time) : Prop :=
  ∃ (n0 : Nat) (End : Nat → NamedBlock V),
    SuffixStartsAfterBoundaryVote S rho t0 n0 ∧
      CanonicalSuffixAtIndex S rho n0 End

/-! ## Exact honest-proposal lifecycle -/


/-- prior local disposition at the proposal's confirmation read. The exact
user-record equality in the current lifecycle implies its first branch. -/
def ConfirmationLatestDispositionAt
    (S : Setup V) (rho : Run V) (v : V) (s : Slot) (B : Block V) : Prop :=
  let latestBefore := (confirmationInputStore S rho v s).latest_confirmed
  let latestAfter :=
    (rho.storeAt S v (Protocol.confirmation_time S.E s)).latest_confirmed
  Block.Preceq B latestAfter ∨
    (latestAfter = latestBefore ∧
      Block.compatible latestBefore B = false)

/-! ## Recurring and proposal-relative finality -/

end Internal
end DecoupledConsensusModel

end
