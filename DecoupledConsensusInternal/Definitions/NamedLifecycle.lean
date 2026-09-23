module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Definitions.PhaseGradeQueries
public import DecoupledConsensusInternal.Legacy.Definitions.NamedHeadReads
public import DecoupledConsensusInternal.Definitions.NamedConfirmationWalk
public import DecoupledConsensusInternal.Definitions.NamedProposalPivot

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Named opening-lifecycle structures, N36 rows 28 and 29 

Named twins of `SGProposalLifecycleInputs`, `SGProposalLifecyclePacket` and
the four nested structures they carry. One named proposal witness `P` is a
structure parameter, bound by the field `proposal`, and threaded through
every field; the prior total `proposedBlock` never appears. Grades are the
phase-grade vocabulary at the G1/G2 domain reads; anchors and SG roots are
the contract reads on the prepared duty reads; run scope is
`NamedRun.blockInRun`. `ProposalPivotSuffixTransfer` and its
walk views are restated in `NamedProposalPivot.lean` with the same bound
witness.
-/


namespace DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal DecoupledConsensusModel.Execution
  DecoupledConsensusModel.Internal.PhaseGrades
  DecoupledConsensusModel.Internal.NamedRecoveryRead DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-- The G1 grade of `B` at reader `w`'s G1-domain read of round `r`
(replaces `Protocol.G1 S.E (gradeViewAt S rho w r) S.hc r B = true`). -/
def namedG1At (S : Setup V) (rho : Run V) (w : V) (r : Round) (B : Block V) : Prop :=
  storeGrade S.E S.hc (readAt S rho (domain S.E S.hc r .g1) w).st r .g1 B = true

/-- Common G2 grade at every honest reader's G2-domain read, with `C` active
there (replaces `GradeFormsAt`). -/
def NamedGradeFormsAt (S : Setup V) (rho : Run V) (r : Round) (C : Block V) : Prop :=
  ∀ v ∈ rho.honest,
    C ∈ filteredTree (readAt S rho (domain S.E S.hc r .g2) v) ∧
      storeGrade S.E S.hc (readAt S rho (domain S.E S.hc r .g2) v).st r .g2 C = true

/-- Every honest slot-`s` committee member emits a vote naming a run block the
cone admits (replaces `HonestVotesCone`; the block is a named run block). -/
def NamedHonestVotesCone (S : Setup V) (rho : Run V) (s : Slot) (tgt : Block V → Prop) : Prop :=
  ∀ x ∈ rho.honest, x ∈ S.E.committee s → ∃ X : NamedBlock V, tgt X.erase ∧
    NamedRun.blockInRun S rho X ∧
    NamedRun.emits S rho x (.gfVote ⟨x, s, X.erase.root⟩) (Protocol.vote_time S.E s)

/-- Every honest slot-`s` committee member emits the vote naming `B`
(replaces `Optimistic.HonestVotesName`). -/
def NamedHonestVotesName (S : Setup V) (rho : Run V) (s : Slot) (B : Block V) : Prop :=
  ∀ v ∈ rho.honest, v ∈ S.E.committee s →
    NamedRun.emits S rho v (.gfVote ⟨v, s, B.root⟩) (Protocol.vote_time S.E s)

/-- Replaces `SGTargetConeCanonicality`. -/
def NamedSGTargetConeCanonicality (S : Setup V) (rho : Run V) (r : Round) (s : Slot) : Prop :=
  ∀ v ∈ rho.honest,
    NamedHonestVotesCone S rho s (fun X => Block.Preceq (actionSGBlockAt S rho v r) X)

/-- Replaces `G1Concentration`. -/
structure NamedG1Concentration (S : Setup V) (rho : Run V) (r : Round) (s : Slot) : Prop where
  supported : ∀ {w : V} {B : Block V}, w ∈ rho.honest → namedG1At S rho w (r + 1) B →
    NamedHonestVotesCone S rho s (fun X => Block.Preceq B X)
  compatible : ∀ {w₁ w₂ : V} {B₁ B₂ : Block V},
    w₁ ∈ rho.honest → w₂ ∈ rho.honest →
    namedG1At S rho w₁ (r + 1) B₁ → namedG1At S rho w₂ (r + 1) B₂ →
    Block.compatible B₁ B₂ = true

/-- The voter's frozen candidate tree at its vote duty read of slot `k`. -/
def voterCandidateTreeAt (S : Setup V) (rho : Run V) (v : V) (k : Slot) : Finset (Block V) :=
  let st := (voteDutyRead S rho v k).st.core
  Protocol.voter_filtered_block_tree S.E st st.s

/-- The voter's anchor at its vote duty read (replaces `healAnchor` on the
old vote duty store: the contract's anchor at the read's round). -/
def voterAnchorAt (S : Setup V) (rho : Run V) (v : V) (k : Slot) : Block V :=
  let n := voteDutyRead S rho v k
  nodeAnchor S n (S.hc.round_of n.st.core.s)

/-- Replaces `SGOpeningConfirmationRead`: the three local facts on the named
confirmation input read. -/
structure NamedSGOpeningConfirmationRead (S : Setup V) (rho : Run V) (s : Slot) (v : V)
    (P : NamedBlock V) : Prop where
  root : Block.Preceq
    (Protocol.get_fg_root (confirmationInputRead S rho v s).st.core.toHealing.toFG) P.erase
  anchor : Block.Preceq
    (Protocol.get_sg_root_with (NamedProfile.gradeContract (confirmationInputRead S rho v s).cache)
      S.E S.hc (confirmationInputRead S rho v s).st.core.toHealing
      (S.hc.round_of (confirmationInputRead S rho v s).st.core.s)) P.erase
  candidate : P.erase ∈ filteredTree (confirmationInputRead S rho v s)

/-- Replaces `SGOpeningFrozenVoteAt`, with the bound proposal `P` at slot
`s + 1` and the voter's named anchor and tree. -/
structure NamedSGOpeningFrozenVoteAt (S : Setup V) (rho : Run V) (s : Slot) (A : Block V)
    (v : V) (P : NamedBlock V) : Prop where
  proposalCandidate : P.erase ∈ voterCandidateTreeAt S rho v (s + 1)
  pivotCandidate : A ∈ (voterCandidateTreeAt S rho v (s + 1)).erase P.erase
  pivotAnchorCompatible : Block.compatible (voterAnchorAt S rho v (s + 1)) A = true
  proposalAnchorCompatible : Block.compatible (voterAnchorAt S rho v (s + 1)) P.erase = true
  pivotPath : Block.Preceq (voterAnchorAt S rho v (s + 1)) A →
    ∀ C : Block V, Block.Preceq (voterAnchorAt S rho v (s + 1)) C →
      C ≠ voterAnchorAt S rho v (s + 1) → Block.Preceq C A →
      C ∈ (voterCandidateTreeAt S rho v (s + 1)).erase P.erase
  suffix : NamedProposalPivotSuffixTransfer S rho (s + 1) A v P
  rawExtra : ∀ u,
    u ∈ Protocol.voter_view S.E (voteDutyRead S rho v (s + 1)).st.core.toHealing.toFG.toSG.toGoldfishStore (s + 1) →
    u ∉ P.erase.gf_votes.toFinset →
    Protocol.equivocates P.erase.gf_votes.toFinset u.val_index = true

/-- Replaces `RawOpeningLifecycleAt`, with the bound proposal witness. -/
structure NamedRawOpeningLifecycleAt (S : Setup V) (rho : Run V) (r : Round)
    (P : NamedBlock V) : Prop where
  roundPositive : 0 < r
  proposal : proposedBlockAt S rho (S.hc.opening_slot r) = some P
  proposerHonest : S.E.proposer (S.hc.opening_slot r) ∈ rho.honest
  proposalInHorizon : Protocol.proposal_time S.E (S.hc.opening_slot r) ≤ rho.horizon
  runBlock : NamedRun.blockInRun S rho P
  liveConfirmed : ∀ v ∈ rho.honest, (actionReadAt S rho v r).st.core.live_confirmed = P.erase
  actionCover : ActionCarriersCover S rho r P.erase
  gradeNext : NamedGradeFormsAt S rho (r + 1) P.erase

/-- Row 28, replaces `SGProposalLifecycleInputs`: the live opening window with
the bound proposal `P` at slot `s + 1`. -/
structure NamedSGProposalLifecycleInputs (S : Setup V) (rho : Run V) (r : Round) (s : Slot)
    (A : Block V) (P : NamedBlock V) : Prop where
  openingSlot : s + 1 = S.hc.opening_slot (r + 1)
  proposal : proposedBlockAt S rho (s + 1) = some P
  postPreviousAction : S.E.t_GST ≤ S.a r
  postProposalSnapshot : S.E.t_GST ≤ Protocol.proposal_time S.E s
  previousSupportInHorizon : Protocol.support_cutoff S.E s ≤ rho.horizon
  actionInHorizon : S.a (r + 1) ≤ rho.horizon
  nextCutoffInHorizon : domain S.E S.hc (r + 1 + 1) .g2 ≤ rho.horizon
  canonical : NamedSGTargetConeCanonicality S rho r s
  concentration : NamedG1Concentration S rho r s
  proposerHonest : S.E.proposer (s + 1) ∈ rho.honest
  proposalAnchor : nodeAnchor S (proposerReadAt S rho (s + 1)) (r + 1) = A
  proposalAnchorG1 : storeGrade S.E S.hc (proposerReadAt S rho (s + 1)).st (r + 1) .g1 A = true
  actionTargetParent : ∀ v ∈ rho.honest,
    Block.Preceq (actionSGBlockAt S rho v r) (proposedParent S rho (s + 1))
  liveG1Parent : ∀ w ∈ rho.honest, ∀ B, namedG1At S rho w (r + 1) B →
    Block.Preceq B (proposedParent S rho (s + 1))
  frozenVote : ∀ v ∈ rho.honest, v ∈ S.E.committee (s + 1) →
    NamedSGOpeningFrozenVoteAt S rho s A v P
  confirmationRead : ∀ v ∈ rho.honest, NamedSGOpeningConfirmationRead S rho (s + 1) v P
  actionBatchAligned : ∀ v ∈ rho.honest,
    let n := actionReadAt S rho v (r + 1)
    BatchAlignedAt S.hc n.st.core.toHealing.gradeView n.st.core.F rho.honest (r + 1)
      (allPhasesCutoff S.E S.hc (r + 1)) P.erase
  actionRootPreceq : ∀ v ∈ rho.honest,
    let n := actionReadAt S rho v (r + 1)
    Block.Preceq (Protocol.get_sg_root_with (NamedProfile.gradeContract n.cache) S.E S.hc
      n.st.core.toHealing (r + 1)) P.erase
  nextActive : ∀ v ∈ rho.honest,
    P.erase ∈ filteredTree (readAt S rho (domain S.E S.hc (r + 1 + 1) .g2) v)


/-- Row 29, replaces `SGProposalLifecyclePacket`, with the bound proposal `P`. -/
structure NamedSGProposalLifecyclePacket (S : Setup V) (rho : Run V) (r : Round) (s : Slot)
    (P : NamedBlock V) : Prop where
  openingSlot : s + 1 = S.hc.opening_slot (r + 1)
  proposal : proposedBlockAt S rho (S.hc.opening_slot (r + 1)) = some P
  actionTargetParent : ∀ v ∈ rho.honest,
    Block.Preceq (actionSGBlockAt S rho v r) (proposedParent S rho (S.hc.opening_slot (r + 1)))
  liveG1Parent : ∀ w ∈ rho.honest, ∀ X, namedG1At S rho w (r + 1) X →
    Block.Preceq X (proposedParent S rho (S.hc.opening_slot (r + 1)))
  honestVotes : NamedHonestVotesName S rho (S.hc.opening_slot (r + 1)) P.erase
  genuineConfirmation : ∀ v ∈ rho.honest,
    GenuineConfirmationAt S rho v (S.hc.opening_slot (r + 1)) ∧
    (rho.storeAt S v (Protocol.confirmation_time S.E (S.hc.opening_slot (r + 1)))).live_confirmed
      = P.erase
  g0ClearAtAction : ∀ v ∈ rho.honest,
    nodeClear S (actionReadAt S rho v (r + 1)) (r + 1) P.erase = true
  lifecycle : NamedRawOpeningLifecycleAt S rho (r + 1) P

/-- Replaces `RawExactHeightSeedIn` (RawExactHeightSeedRun.lean:51): the
witness container carries its block as a full named block, the bound
lifecycle, and named derivation for its state fields. No existential lift
from an erased block. -/
structure NamedRawExactHeightSeedIn (S : Setup V) (rho : Run V) (M : Height) (lo hi : Round) :
    Type where
  round : Round
  block : NamedBlock V
  target : BlockId
  roundLower : lo ≤ round
  roundUpper : round ≤ hi
  lifecycle : NamedRawOpeningLifecycleAt S rho round block
  exactHeight : (Protocol.derive_named S.E S.cfg block).h = M
  exactTarget : (Protocol.derive_named S.E S.cfg block).T_h.root = target

end DecoupledConsensusModel.Proofs.HealingSurface

end
