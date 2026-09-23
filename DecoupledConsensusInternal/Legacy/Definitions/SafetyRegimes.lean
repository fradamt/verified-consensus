module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Definitions.NamedHeadReads
public import DecoupledConsensusInternal.Legacy.Definitions.FinalitySafety
public import DecoupledConsensusInternal.Legacy.Assumptions.AwakeWindow
public import DecoupledConsensusInternal.Legacy.Assumptions.PrefixAgreement
public import DecoupledConsensusInternal.Legacy.Assumptions.Recurrence
public import DecoupledConsensusInternal.Legacy.Definitions.ConfirmedOutput
public import DecoupledConsensusInternal.Legacy.Definitions.NamedLivenessStatements

@[expose] public section

/-!
# Public safety under genesis and bounded phase-shift assumptions

The prefix clause names the client-facing `get_confirmed` output. The other
confirmation clauses name actual protocol reads and stored confirmation fields.
The strong phase ends at a specified recovery-search endpoint. Later awake
windows are the only participation premise of its continuation. The finite
handoff proves an exact user-record refresh. Agreement, monotonicity, and
honest-proposal inclusion then hold for the finality-aware user output.
-/

namespace DecoupledConsensusModel
namespace Internal

open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A record contains an actual live value selected in the safe slot interval. -/
def PostCutSelection (S : Setup V) (rho : Run V) (cut : Round) (B : Block V) : Prop :=
  ∃ v ∈ rho.honest, ∃ q, S.hc.opening_slot cut ≤ q ∧
    Protocol.confirmation_time S.E q ≤ rho.horizon ∧
    B = (rho.storeAt S v (Protocol.confirmation_time S.E q)).live_confirmed

/-- Safety once the guarded latest record contains a post-cut selection. -/
structure RefreshedLatestSafety (S : Setup V) (rho : Run V)
    (cut : Round) (start : Slot) : Prop where
  compatible : ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t t',
    t ≤ rho.horizon → t' ≤ rho.horizon →
    PostCutSelection S rho cut (rho.storeAt S u t).latest_confirmed →
    PostCutSelection S rho cut (rho.storeAt S v t').latest_confirmed →
    Block.compatible (rho.storeAt S u t).latest_confirmed
      (rho.storeAt S v t').latest_confirmed = true
  finalityRoot : ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t,
    Protocol.confirmation_time S.E start ≤ t → t ≤ rho.horizon →
    PostCutSelection S rho cut (rho.storeBeforeTime S u t).latest_confirmed →
    Block.compatible (rho.storeBeforeTime S u t).latest_confirmed
      (Protocol.get_fg_root (rho.storeBeforeTime S v t).toHealing.toFG) = true

/-- Genesis confirmation and historical-record guarantees under weak participation. -/
structure GSTZeroGuarantees (S : Setup V) (rho : Run V) : Prop where
  availableChain : AvailableChainFrom S rho 0
  availableConfirmations : AvailableConfirmationsFrom S rho 0
  selectionChain : ∀ v ∈ rho.honest, ∀ i B, ActualConfirmationSelection S rho v i B →
    ∀ w ∈ rho.honest, ∀ j C, ActualConfirmationSelection S rho w j C →
    Block.compatible B C = true
  confirmationFields : ∀ last, Protocol.confirmation_time S.E last ≤ rho.horizon →
    ∀ t u, t ≤ Protocol.confirmation_time S.E last →
    u ≤ Protocol.confirmation_time S.E last → ∀ v ∈ rho.honest, ∀ w ∈ rho.honest,
    Block.compatible (rho.storeAt S v t).latest_confirmed
      (rho.storeAt S w u).latest_confirmed = true ∧
    Block.compatible (rho.storeAt S v t).live_confirmed
      (rho.storeAt S w u).live_confirmed = true ∧
    Block.compatible (rho.storeAt S v t).latest_confirmed
      (rho.storeAt S w u).live_confirmed = true
  latestAtProposal : LatestAtProposalField S rho 0
  liveMonotone : ∀ v ∈ rho.honest, ∀ t t', t ≤ t' →
    Block.Preceq (rho.storeAt S v t).live_confirmed (rho.storeAt S v t').live_confirmed
  liveAtConfirmation : ∀ s, 0 < s → Protocol.confirmation_time S.E s ≤ rho.horizon →
    ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t,
    t < Protocol.confirmation_time S.E s →
    Block.Preceq (rho.storeAt S u t).live_confirmed
      (rho.storeAt S v (Protocol.confirmation_time S.E s)).live_confirmed
  proposalReads : ∀ s, 0 < s → Protocol.confirmation_time S.E s ≤ rho.horizon →
    S.E.proposer s ∈ rho.honest → HonestProposalReadSafety S rho s
  outputCompatible : ConfirmedOutputCompatibleFrom S rho 0
  outputMonotone : ConfirmedOutputMonotoneFrom S rho 0
  userProposals : UserProposalsConfirmedAfter S rho 0

/-- User-facing confirmation guarantees from the actual bounded healing handoff.
The seed is refreshed at the handoff, without a premise about a later proposer. -/
structure UserConfirmationAfterHealing (S : Setup V) (rho : Run V)
    (start : Slot) (P : Block V) : Prop where
  refreshed : ∀ v ∈ rho.honest,
    (rho.storeAt S v (Protocol.confirmation_time S.E start)).latest_confirmed = P
  latestCompatible : ConfirmationCompatibleFrom S rho (Protocol.confirmation_time S.E start)
  latestMonotone : ConfirmationMonotoneFrom S rho (Protocol.confirmation_time S.E start)
  outputCompatible : ConfirmedOutputCompatibleFrom S rho (Protocol.confirmation_time S.E start)
  outputMonotone : ConfirmedOutputMonotoneFrom S rho (Protocol.confirmation_time S.E start)
  proposals : UserProposalsConfirmedAfter S rho start
  seedConfirmed : ∀ v ∈ rho.honest, ∀ t,
    Protocol.confirmation_time S.E start ≤ t → t ≤ rho.horizon →
    Block.Preceq P (confirmedOutputAt S rho v t)

/-- Public confirmation, vote, proposal, and finality safety after the strong phase. -/
structure PhaseShiftSafety (S : Setup V) (rho : Run V)
    (cut : Round) (start : Slot) (P : Block V) : Prop where
  finality : WholeRunFinalitySafety S rho
  userConfirmation : UserConfirmationAfterHealing S rho start P
  refreshedLatest : RefreshedLatestSafety S rho cut start
  liveMonotone : ∀ v ∈ rho.honest, ∀ t t',
    Protocol.confirmation_time S.E start ≤ t → t ≤ t' →
    Block.Preceq (rho.storeAt S v t).live_confirmed (rho.storeAt S v t').live_confirmed
  liveCompatible : ∀ last, Protocol.confirmation_time S.E last ≤ rho.horizon →
    start ≤ last + 1 → ∀ t u, S.a cut ≤ t → S.a cut ≤ u →
    t ≤ Protocol.confirmation_time S.E last → u ≤ Protocol.confirmation_time S.E last →
    ∀ v ∈ rho.honest, ∀ w ∈ rho.honest,
    Block.compatible (rho.storeAt S v t).live_confirmed
      (rho.storeAt S w u).live_confirmed = true
  genuine : ∀ s, start ≤ s → Protocol.confirmation_time S.E s ≤ rho.horizon →
    ∀ v ∈ rho.honest, GenuineConfirmationAt S rho v s
  liveAtConfirmation : ∀ s, start ≤ s →
    Protocol.confirmation_time S.E s ≤ rho.horizon →
    ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t,
    S.a cut ≤ t → t < Protocol.confirmation_time S.E s →
    Block.Preceq (rho.storeAt S u t).live_confirmed
      (rho.storeAt S v (Protocol.confirmation_time S.E s)).live_confirmed
  seedAtVote : SeedAtVoteField S rho start P
  liveAtVote : LiveAtVoteField S rho cut start
  honestProposalLive : HonestProposalLiveField S rho start
  honestProposalReads : ∀ s, start < s → Protocol.confirmation_time S.E s ≤ rho.horizon →
    S.E.proposer s ∈ rho.honest → HonestProposalReadSafety S rho s

/-- The start of the bounded seed search, at a constant lag from the post-GST
round. The strong phase ends `gap` rounds later. This equality fixes the
endpoint; it cannot be chosen arbitrarily to make the horizon condition false. -/
def BoundedPhaseStart (S : Setup V) (rho : Run V)
    (rGST gap : Round) (delayExtra : Nat) (n : Round) : Prop :=
  let lag := (4 * gap + 12 + 2 * delayExtra) + 3 * gap + 10 + 2 * delayExtra
  n = rGST + 1 + (1 + (S.cfg.D + S.cfg.K + 5) * lag) +
    2 * lag + max (1 + S.hc.η_SG) (gap + 3)

end Internal
end DecoupledConsensusModel

end
