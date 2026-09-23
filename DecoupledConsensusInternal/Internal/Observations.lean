module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.Confirmation
public import DecoupledConsensusInternal.Legacy.Definitions.NamedHeadReads

@[expose] public section

/-! Indexed records observations for the internal canonical suffix.
These reads start at the actual event-index prefix. No strict-time or
slot-indexed read is substituted for that prefix. Exact named tick
correspondence is a proof obligation at the constructor's active duty time.
-/



namespace DecoupledConsensusModel
namespace Internal

open Execution Protocol

variable {V : Type} [DecidableEq V] [Fintype V]


/-- Indexed twin of the records's clock/cache-prepared duty read. This is the
proposal, vote, and confirmation input only at their respective duty times. -/
def canonicalTickReadAtIndex
    (S : Setup V) (rho : Run V) (i : Nat) (v : V) (t : Time) :
    NamedNodeState V :=
  NamedActionReads.confirmationReadFrom S (NamedRun.stateBefore S rho i v) t

/-- Indexed twin of proposerHeadAt: the shared proposal input's parent.
This read remains defined if the subsequent named-parent lookup fails. -/
def proposalStageHeadAtIndex
    (S : Setup V) (rho : Run V) (i : Nat) (v : V) (t : Time) : Block V :=
  let n := canonicalTickReadAtIndex S rho i v t
  (Protocol.proposal_input_with (NamedProfile.gradeContract n.cache) S.E S.hc
    (S.node v) n.st.core.toHealing).parent

/-- The actual named proposal computation on the indexed prepared read.
A failed parent lookup remains none; no geometry block is invented. -/
def proposalStageBlockAtIndex
    (S : Setup V) (rho : Run V) (i : Nat) (v : V) (t : Time) :
    Option (NamedBlock V) :=
  let n := canonicalTickReadAtIndex S rho i v t
  Protocol.NamedActions.proposal_with (NamedProfile.gradeContract n.cache) .poolAndCarried
    S.E S.hc (S.node v) n.st

/-- Indexed Q-D1 duty output, with the actual prepared cache and named store. -/
def voteStageVoteAtIndex
    (S : Setup V) (rho : Run V) (i : Nat) (v : V) (t : Time) :
    Option (GoldfishVote V) :=
  let n := canonicalTickReadAtIndex S rho i v t
  (Protocol.NamedDuties.goldfish_vote_with (NamedProfile.gradeContract n.cache)
    S.E S.hc (S.node v) n.st).2


/-- Indexed twin of voterHeadAt, with the records's exact selector and views. -/
def voteStageHeadAtIndex
    (S : Setup V) (rho : Run V) (i : Nat) (v : V) (t : Time) : Block V :=
  let n := canonicalTickReadAtIndex S rho i v t
  let st := n.st.core
  Protocol.get_head_in_tree_with_layer (NamedProfile.gradeContract n.cache) S.E S.hc st.toHealing
    (Protocol.voter_filtered_block_tree S.E st st.s)
    (Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
    (Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s) (st.s - 1)


/-- The records already supplies this exact prefix-relative confirmation observer. -/
def confirmationStageOutputAtIndex
    (S : Setup V) (rho : Run V) (i : Nat) (v : V) (t : Time) : Block V :=
  (confirmationDutyOutput S (NamedRun.stateBefore S rho i v) t).core.live_confirmed


/-- Indexed twin of actionHeadAt, on the records's post-confirmation action read.
The action constructor below binds t to this round's actual action time. -/
def actionStageHeadAtIndex
    (S : Setup V) (rho : Run V) (i : Nat) (v : V) (t : Time) : Block V :=
  let r := S.hc.round_of (S.E.slotOf t)
  let n := NamedActionReads.actionReadFrom S (NamedRun.stateBefore S rho i v) r
  let st := n.st.core
  Protocol.get_head_with (NamedProfile.gradeContract n.cache) S.E S.hc st.toHealing
    (st.pool st.s) ((st.pool st.s).filter (fun u => Protocol.resolved st.T u = true)) st.s

/-- Actual block-valued observations of an honest indexed tick.
Stages remain proposal input parent 0, computed named proposal 1, vote head 2,
confirmation output 3, action head 4. A named proposal witness is required
only for the produced block, not for the total proposal input-parent read.
The vote constructor retains the computed Q-D1 vote as witness data. -/
inductive HonestCanonicalObservationAtIndex
    (S : Setup V) (rho : Run V) (i : Nat) : Nat → Block V → Prop where
  | proposalParent {v : V} {t : Time}
      (honest : v ∈ rho.honest)
      (event : rho.events[i]? = some (Event.tick v t))
      (active : 0 < S.E.slotOf t ∧
        t = Protocol.proposal_time S.E (S.E.slotOf t) ∧
        S.E.proposer (S.E.slotOf t) = (S.node v).val_index) :
      HonestCanonicalObservationAtIndex S rho i 0
        (proposalStageHeadAtIndex S rho i v t)
  | proposedBlock {v : V} {t : Time} {B : NamedBlock V}
      (honest : v ∈ rho.honest)
      (event : rho.events[i]? = some (Event.tick v t))
      (active : 0 < S.E.slotOf t ∧
        t = Protocol.proposal_time S.E (S.E.slotOf t) ∧
        S.E.proposer (S.E.slotOf t) = (S.node v).val_index)
      (computed : proposalStageBlockAtIndex S rho i v t = some B) :
      HonestCanonicalObservationAtIndex S rho i 1 B.erase
  | voteHead {v : V} {t : Time} {u : GoldfishVote V}
      (honest : v ∈ rho.honest)
      (event : rho.events[i]? = some (Event.tick v t))
      (active : 0 < S.E.slotOf t ∧
        t = Protocol.vote_time S.E (S.E.slotOf t))
      (proposerHonest : S.E.proposer (S.E.slotOf t) ∈ rho.honest)
      (committee : (S.node v).val_index ∈ S.E.committee (S.E.slotOf t))
      (computed : voteStageVoteAtIndex S rho i v t = some u) :
      HonestCanonicalObservationAtIndex S rho i 2
        (voteStageHeadAtIndex S rho i v t)
  | confirmationOutput {v : V} {t : Time}
      (honest : v ∈ rho.honest)
      (event : rho.events[i]? = some (Event.tick v t))
      (active : 0 < S.E.slotOf t ∧
        t = Protocol.support_cutoff S.E (S.E.slotOf t)) :
      HonestCanonicalObservationAtIndex S rho i 3
        (confirmationStageOutputAtIndex S rho i v t)
  | actionHead {v : V} {t : Time}
      (honest : v ∈ rho.honest)
      (event : rho.events[i]? = some (Event.tick v t))
      (active : t = S.a (S.hc.round_of (S.E.slotOf t))) :
      HonestCanonicalObservationAtIndex S rho i 4
        (actionStageHeadAtIndex S rho i v t)

/-- The observations that belong to the monotone proposal chain. Confirmation
and action stages remain observable but are handled by the lifecycle contract. -/
def ProposalChainStage (stage : Nat) : Prop :=
  stage ≤ 2

/-- The suffix begins immediately after one named honest committee vote event,
not at the strict time prefix before all events at the same instant. The voter,
slot, and event index are existential proof data. -/
def SuffixStartsAfterBoundaryVote
    (S : Setup V) (rho : Run V) (t0 : Time) (n0 : Nat) : Prop :=
  ∃ (v : V) (s : Slot) (i : Nat),
    v ∈ rho.honest ∧
      (S.node v).val_index ∈ S.E.committee s ∧
      0 < s ∧
      t0 = Protocol.vote_time S.E s ∧
      rho.events[i]? = some (Event.tick v t0) ∧
      n0 = i + 1

end Internal
end DecoupledConsensusModel

end
