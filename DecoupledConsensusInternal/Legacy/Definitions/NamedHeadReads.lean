module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Definitions.NamedDutyReads
public import DecoupledConsensusInternal.Legacy.Definitions.NamedLivenessStatements

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Named shared-duty head observations 

The three protocol head reads and the confirmation selection, observed on
the prepared named reads through the contract-parametric selectors the
named duties call (`get_head_with`, `get_head_in_tree_with`,
`update_confirmation_with`). No old core selector is re-run on an erased
store. Replacement bodies follow for `ActualConfirmationSelection`,
`HonestProposalReadSafety`, `AvailableChainGrowthFrom`, and the proposal
and vote fields of `GSTZeroGuarantees` and `PhaseShiftSafety`. Rule for every
old total `proposedBlock` occurrence: a SAFETY field quantifies the
witness (`∀ B, proposedBlockAt S rho s = some B → …`), a LIVENESS or
equality conclusion concludes the witness (`∃ B, proposedBlockAt S rho s =
some B ∧ …`); the block appears as `B.erase` in geometric positions.
-/


namespace DecoupledConsensusModel.Internal
open Execution Proofs.HealingSurface NamedRecoveryRead
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The proposer's head at slot `k`: the shared proposal input's parent. -/
def proposerHeadAt (S : Setup V) (rho : Run V) (k : Slot) : Block V :=
  proposedParent S rho k

/-- The voter's head at slot `k`: the contract-parametric in-tree head on the
vote duty read, with the voter views of that read. -/
def voterHeadAt (S : Setup V) (rho : Run V) (v : V) (k : Slot) : Block V :=
  let n := voteDutyRead S rho v k
  let st := n.st.core
  Protocol.get_head_in_tree_with_layer (NamedProfile.gradeContract n.cache) S.E S.hc st.toHealing
    (Protocol.voter_filtered_block_tree S.E st st.s)
    (Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
    (Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s) (st.s - 1)

/-- The action head at round `r`: the contract-parametric head on the action
duty read, over the resolved pool of the read's slot. -/
def actionHeadAt (S : Setup V) (rho : Run V) (v : V) (r : Round) : Block V :=
  let n := actionDutyRead S rho v r
  let st := n.st.core
  Protocol.get_head_with (NamedProfile.gradeContract n.cache) S.E S.hc st.toHealing
    (st.pool st.s) ((st.pool st.s).filter (fun u => Protocol.resolved st.T u = true)) st.s

/-- The named confirmation duty's output on the prepared read at `time`. -/
def confirmationDutyOutput (S : Setup V) (before : NamedNodeState V) (time : Time) :
    Protocol.NamedStore V :=
  let n := NamedActionReads.confirmationReadFrom S before time
  Protocol.NamedDuties.update_confirmation_with (NamedProfile.gradeContract n.cache)
    S.E S.hc n.st (S.E.slotOf time - 1)

/-- Replacement body: a value selected by an actual confirmation tick. -/
def ActualConfirmationSelection (S : Setup V) (rho : Run V) (v : V) (i : Nat)
    (C : Block V) : Prop :=
  ∃ time, rho.events[i]? = some (.tick v time) ∧
    0 < S.E.slotOf time ∧ time = Protocol.support_cutoff S.E (S.E.slotOf time) ∧
    (confirmationDutyOutput S (NamedRun.stateBefore S rho i v) time).core.live_confirmed = C

/-- Replacement body: an honest proposal remains below all three later head reads. -/
structure HonestProposalReadSafety (S : Setup V) (rho : Run V) (s : Slot) : Prop where
  proposal : ∀ B, proposedBlockAt S rho s = some B →
    ∀ k, s < k → Protocol.proposal_time S.E k ≤ rho.horizon →
    S.E.proposer k ∈ rho.honest → Block.Preceq B.erase (proposerHeadAt S rho k)
  vote : ∀ B, proposedBlockAt S rho s = some B →
    ∀ k, s ≤ k → Protocol.vote_time S.E k ≤ rho.horizon →
    ∀ v ∈ rho.honest, Block.Preceq B.erase (voterHeadAt S rho v k)
  action : ∀ B, proposedBlockAt S rho s = some B →
    ∀ r, s ≤ S.hc.opening_slot r + 1 → S.a r ≤ rho.horizon →
    ∀ v ∈ rho.honest, Block.Preceq B.erase (actionHeadAt S rho v r)

/-- Replacement body: bounded strict growth of the user confirmation record,
with the honest proposal's existence concluded. -/
def AvailableChainGrowthFrom (S : Setup V) (rho : Run V) (start : Slot) (gap : Round) : Prop :=
  ∀ r : Round, start ≤ S.hc.opening_slot r →
    S.a (r + gap) ≤ rho.horizon →
    ∃ s : Slot, S.hc.opening_slot r < s ∧
      S.E.proposer s ∈ rho.honest ∧
      Protocol.confirmation_time S.E s ≤ S.a (r + gap) ∧
      ∃ B : NamedBlock V, proposedBlockAt S rho s = some B ∧
        (∀ v ∈ rho.honest,
          (rho.storeAt S v (Protocol.confirmation_time S.E s)).latest_confirmed = B.erase ∧
          Block.Prec (rho.storeAt S v (S.a r)).latest_confirmed B.erase) ∧
        (∀ v ∈ rho.honest, ∀ t : Time,
          Protocol.confirmation_time S.E s ≤ t → t ≤ rho.horizon →
          Block.Preceq B.erase (rho.storeAt S v t).latest_confirmed ∧
          Block.Preceq B.erase (confirmedOutputAt S rho v t))

/-- Replacement fields for `GSTZeroGuarantees.latestAtProposal` and
`PhaseShiftSafety.honestProposalLive` (equality conclusions conclude the witness). -/
def LatestAtProposalField (S : Setup V) (rho : Run V) (lo : Slot) : Prop :=
  ∀ s, lo < s → Protocol.confirmation_time S.E s ≤ rho.horizon →
    S.E.proposer s ∈ rho.honest →
    ∃ B : NamedBlock V, proposedBlockAt S rho s = some B ∧
      ∀ v ∈ rho.honest,
        (rho.storeAt S v (Protocol.confirmation_time S.E s)).latest_confirmed = B.erase

def HonestProposalLiveField (S : Setup V) (rho : Run V) (start : Slot) : Prop :=
  ∀ s, start < s → Protocol.confirmation_time S.E s ≤ rho.horizon →
    S.E.proposer s ∈ rho.honest →
    ∃ B : NamedBlock V, proposedBlockAt S rho s = some B ∧
      ∀ v ∈ rho.honest,
        (rho.storeAt S v (Protocol.confirmation_time S.E s)).live_confirmed = B.erase

/-- Replacement fields for `PhaseShiftSafety.seedAtVote` and `liveAtVote`. -/
def SeedAtVoteField (S : Setup V) (rho : Run V) (start : Slot) (P : Block V) : Prop :=
  ∀ d, start ≤ d → Protocol.vote_time S.E d ≤ rho.horizon →
    ∀ v ∈ rho.honest, Block.Preceq P (voterHeadAt S rho v d)

def LiveAtVoteField (S : Setup V) (rho : Run V) (cut : Round) (start : Slot) : Prop :=
  ∀ d, start ≤ d → Protocol.vote_time S.E d ≤ rho.horizon →
    ∀ u ∈ rho.honest, ∀ v ∈ rho.honest, ∀ t, S.a cut ≤ t → t ≤ rho.horizon →
    t < Protocol.confirmation_time S.E d →
    Block.Preceq (rho.storeAt S u t).live_confirmed (voterHeadAt S rho v d)

end DecoupledConsensusModel.Internal

end
