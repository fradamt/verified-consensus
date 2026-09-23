module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedCone
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedActivity
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedViability
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGOpeningFrozenSuffix
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryGenuineClearNextVote
public import DecoupledConsensusProofs.Objects.HealingDirectedHistory
public import DecoupledConsensusProofs.Generic.SuffixHistory
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightProgressClosurescoreEq

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Round ceilings for the gate-off seed

This module isolates the sound round-ceiling argument. A ceiling is an upper
bound for the SG anchors and a lower bound for the preceding Goldfish vote
cone. The Goldfish cone step gives the opening vote cone. Genuine opening
confirmations therefore extend the ceiling and persist through the round.

The successor frontier is selected from the prior ceiling together with the
actual honest opening-confirmation outputs. Root fallbacks are below the prior
ceiling, while genuine outputs extend it. Thus the selection keeps the prior
ceiling when no genuine output exists and otherwise selects a deepest genuine
output.

The successor assembly interface names the complete next-round input records.
`SeedCeilingStepRun` constructs that records from pointwise regime facts by
relaying the preceding honest vote cone. Proposal transfer uses the ceiling
itself as the common frozen pivot, so the ceiling record does not store a
directional ordering between the proposal and vote anchors.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The last slot of round `q`. -/
def seedRoundLastSlot (S : Setup V) (q : Round) : Slot :=
  S.hc.opening_slot (q + 1) - 1


private theorem openingSlot_succ_le_seedRoundLastSlot
    (S : Setup V) (q : Round) :
    S.hc.opening_slot q + 1 ≤ seedRoundLastSlot S q := by
  unfold seedRoundLastSlot Protocol.HealConfig.opening_slot
  have hR : 2 ≤ S.hc.R := S.hc.R_ge_two
  apply Nat.le_sub_of_add_le
  rw [Nat.add_mul]
  simp only [Nat.one_mul]
  omega

private theorem openingSlot_lt_seedRoundLastSlot
    (S : Setup V) (q : Round) :
    S.hc.opening_slot q < seedRoundLastSlot S q :=
  Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (openingSlot_succ_le_seedRoundLastSlot S q)

private theorem openingSlot_le_seedRoundLastSlot_pred
    (S : Setup V) (q : Round) :
    S.hc.opening_slot q ≤ seedRoundLastSlot S q - 1 :=
  Nat.le_pred_of_lt (openingSlot_lt_seedRoundLastSlot S q)

private theorem openingSlot_pred_succ
    (S : Setup V) {q : Round} (hq : 0 < q) :
    S.hc.opening_slot q - 1 + 1 = S.hc.opening_slot q := by
  unfold Protocol.HealConfig.opening_slot
  have hpos : 0 < q * S.hc.R :=
    Nat.mul_pos hq (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  exact Nat.sub_add_cancel (Nat.succ_le_iff.mpr hpos)

private theorem confirmationTime_mono
    (E : Env V) {a b : Slot} (hab : a ≤ b) :
    Protocol.confirmation_time E a ≤ Protocol.confirmation_time E b := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ,
    Protocol.confirmation_time_eq_support_cutoff_succ]
  exact Proofs.Optimistic.support_cutoff_mono E (Nat.add_le_add_right hab 1)

/-- A named block emitted as an honest committee member's vote head. -/
def NamedHonestHead
    (S : Setup V) (rho : Run V) (s : Slot) (head : NamedBlock V) : Prop :=
  ∃ x ∈ rho.honest, x ∈ S.E.committee s ∧ RunBlock S rho head ∧
    rho.emits S x (.gfVote ⟨x, s, head.erase.root⟩)
      (Protocol.vote_time S.E s)

/-- One honest named vote head in a ceiling cone reaches the local `M - 1`
viability boundary. -/
def ThinHonestHeadAt
    (S : Setup V) (rho : Run V) (M : Height) (s : Slot) (C : Block V) : Prop :=
  ∃ head : NamedBlock V,
    NamedHonestHead S rho s head ∧ Block.Preceq C head.erase ∧
      M - 1 ≤ (derive_named S.E S.cfg head).h

/-- A cone whose endpoint is already inside the frontier band contains a thin
honest head. -/
theorem thinHonestHeadAt_of_thin_endpoint
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} {C : NamedBlock V} {M : Height}
    (hCrun : RunBlock S rho C)
    (hCheight : M - 1 ≤ (derive_named S.E S.cfg C).h)
    (hvotes : NamedHonestVotesCone S rho s (fun X => Block.Preceq C.erase X)) :
    ThinHonestHeadAt S rho M s C.erase := by
  have hpositive : 0 < ((S.E.committee s) ∩ rho.honest).card := by
    have hc := hcom s
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpositive
  have hwCommittee : w ∈ S.E.committee s := (Finset.mem_inter.mp hw).1
  have hwHonest : w ∈ rho.honest := (Finset.mem_inter.mp hw).2
  obtain ⟨H, hCH, hHrun, hHemit⟩ := hvotes w hwHonest hwCommittee
  have hnamed : NamedBlock.Preceq C H :=
    Protocol.namedPreceq_of_runBlock_erase_preceq adm hCrun hHrun hCH
  exact ⟨H, ⟨w, hwHonest, hwCommittee, hHrun, hHemit⟩, hCH,
    hCheight.trans
      (Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hnamed)⟩

/-- The ceiling is at or above the selected FG root at every protocol read
owned by round `q`. The boundary confirmation at `opening_slot q - 1`
belongs to the preceding round and is intentionally not included. -/
structure RoundCeilingAboveRootAt
    (S : Setup V) (rho : Run V) (q : Round) (C : Block V) : Prop where
  voteDuty : ∀ d : Slot,
    S.hc.opening_slot q ≤ d → d ≤ seedRoundLastSlot S q →
      ∀ w ∈ rho.honest,
        Block.Preceq
          (Protocol.get_fg_root
            (voteDutyStore S rho w d).toHealing.toFG) C
  confirmation : ∀ s : Slot,
    S.hc.opening_slot q ≤ s → s < seedRoundLastSlot S q →
      ∀ w ∈ rho.honest,
        Block.Preceq (confRoot (confStore S rho w s)) C
  action : ∀ w ∈ rho.honest,
    Block.Preceq
      (Protocol.get_fg_root (healStoreAt S rho w q).toFG) C
  proposer : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest →
    Block.Preceq
      (Protocol.get_fg_root
        (proposerDutyStore S rho (S.hc.opening_slot q)).toHealing.toFG) C

/-- The ceiling is a member of the finality-filtered tree at every protocol
read owned by round `q`. -/
structure RoundCeilingActiveAt
    (S : Setup V) (rho : Run V) (q : Round) (C : Block V) : Prop where
  voteDuty : ∀ d : Slot,
    S.hc.opening_slot q ≤ d → d ≤ seedRoundLastSlot S q →
      ∀ w ∈ rho.honest,
        C ∈ Protocol.get_filtered_block_tree
          (voteDutyStore S rho w d).toHealing.toFG
  confirmation : ∀ s : Slot,
    S.hc.opening_slot q ≤ s → s < seedRoundLastSlot S q →
      ∀ w ∈ rho.honest,
        C ∈ confTree (confStore S rho w s)
  action : ∀ w ∈ rho.honest,
    C ∈ Protocol.get_filtered_block_tree
      (healStoreAt S rho w q).toFG
  proposer : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest →
    C ∈ Protocol.get_filtered_block_tree
      (proposerDutyStore S rho (S.hc.opening_slot q)).toHealing.toFG

/-- A gate-off round ceiling. Every stored read is in round `q`: vote duties
are half-open at `opening_slot (q + 1)`, and slot inputs stop one slot earlier
because `GoldfishConeSlotInputs s` reads the vote duty at `s + 1`.

`openingStepInputs` is the boundary step from the last vote of round `q - 1`
to the opening vote of round `q`. The `gateOff` window starts after the
opening and ends one slot before the end of the round for the same reason. -/
structure RoundCeilingAt
    (S : Setup V) (rho : Run V) (M : Height) (q : Round)
    (C : NamedBlock V) : Prop where
  roundPositive : 0 < q
  run : RunBlock S rho C
  /-- The ceiling has an honest vote head at the boundary slot that reaches
  the local viability boundary. This replaces the previous numeric `M - 1` height
  field: a ceiling may be a revealed low root or a low divergence point. -/
  boundaryThinHead : ThinHonestHeadAt S rho M (S.hc.opening_slot q - 1) C.erase
  aboveRoot : RoundCeilingAboveRootAt S rho q C.erase
  active : RoundCeilingActiveAt S rho q C.erase
  postPreviousVote : S.E.t_GST ≤
    Protocol.vote_time S.E (S.hc.opening_slot q - 1)
  previousConfirmationInHorizon :
    Protocol.confirmation_time S.E (S.hc.opening_slot q - 1) ≤ rho.horizon
  postOpeningProposal : S.E.t_GST ≤
    Protocol.proposal_time S.E (S.hc.opening_slot q)
  postOpeningVote : S.E.t_GST ≤
    Protocol.vote_time S.E (S.hc.opening_slot q)
  roundConfirmationInHorizon :
    Protocol.confirmation_time S.E (seedRoundLastSlot S q - 1) ≤ rho.horizon
  lastVotes : NamedHonestVotesCone S rho (S.hc.opening_slot q - 1)
    (fun X => Block.Preceq C.erase X)
  openingStepInputs : ∀ w ∈ rho.honest, GoldfishConeVoteInputs S rho
    (S.hc.opening_slot q - 1) C.erase w
  roundInputs : ∀ s : Slot,
    S.hc.opening_slot q ≤ s → s < seedRoundLastSlot S q →
      GoldfishConeSlotInputs S rho s C.erase
  voteActive : ∀ d : Slot,
    S.hc.opening_slot q ≤ d → d ≤ seedRoundLastSlot S q →
      ∀ w ∈ rho.honest,
        C.erase ∈ Protocol.get_filtered_block_tree
          (voteDutyStore S rho w d).toHealing.toFG
  actionActive : ∀ w ∈ rho.honest,
    C.erase ∈ Protocol.get_filtered_block_tree (healStoreAt S rho w q).toFG
  voteAnchor : ∀ d : Slot,
    S.hc.opening_slot q ≤ d → d ≤ seedRoundLastSlot S q →
      ∀ w ∈ rho.honest,
        Block.Preceq (voterAnchorAt S rho w d) C.erase
  confirmationAnchor : ∀ s : Slot,
    S.hc.opening_slot q - 1 ≤ s → s < seedRoundLastSlot S q →
      ∀ w ∈ rho.honest,
        Block.Preceq (confirmationAnchorAt S rho w s) C.erase
  actionAnchor : ∀ w ∈ rho.honest,
    Block.Preceq
      (PhaseGrades.nodeAnchor S (Internal.NamedRecoveryRead.actionDutyRead S rho w q) q) C.erase
  proposerAnchorCeiling : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest →
    Block.Preceq
      (PhaseGrades.nodeAnchor S
        (Internal.NamedRecoveryRead.proposalDutyRead S rho (S.hc.opening_slot q)) q) C.erase
  proposerActive : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest →
    C.erase ∈ Protocol.get_filtered_block_tree
      (proposerDutyStore S rho (S.hc.opening_slot q)).toHealing.toFG
  previousCarriers : ∀ v ∈ rho.honest,
    Block.Preceq (actionSGBlockAt S rho v (q - 1)) C.erase
  gateOff : GateOffSeedConeWindowAt S rho M
    (S.hc.opening_slot q) (seedRoundLastSlot S q - 1)
  genuineRun : ∀ w ∈ rho.honest, ∀ D : Block V,
    GenuineConfirmationWith
        (NamedProfile.gradeContract
          (Internal.NamedRecoveryRead.confirmationInputRead S rho w (S.hc.opening_slot q)).cache)
        S.E S.hc (confStore S rho w (S.hc.opening_slot q))
          (S.hc.opening_slot q) D →
      ∃ Dn : NamedBlock V, Dn.erase = D ∧ RunBlock S rho Dn

/-- Existing cone inputs construct the explicit root-order and activity
fields of a round ceiling. -/
theorem roundCeiling_readSupport_of_inputs
    (S : Setup V) {rho : Run V} {q : Round} {C : Block V}
    (hq : 0 < q)
    (hopening : ∀ w ∈ rho.honest, GoldfishConeVoteInputs S rho
      (S.hc.opening_slot q - 1) C w)
    (hround : ∀ s : Slot,
      S.hc.opening_slot q ≤ s → s < seedRoundLastSlot S q →
        GoldfishConeSlotInputs S rho s C)
    (haction : ∀ w ∈ rho.honest,
      C ∈ Protocol.get_filtered_block_tree
        (healStoreAt S rho w q).toFG)
    (hproposer : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest →
      C ∈ Protocol.get_filtered_block_tree
        (proposerDutyStore S rho (S.hc.opening_slot q)).toHealing.toFG) :
    RoundCeilingAboveRootAt S rho q C ∧
      RoundCeilingActiveAt S rho q C := by
  have hvote : ∀ d : Slot,
      S.hc.opening_slot q ≤ d → d ≤ seedRoundLastSlot S q →
        ∀ w ∈ rho.honest,
          GoldfishConeVoteInputs S rho (d - 1) C w := by
    intro d hdlo hdhi w hw
    by_cases heq : d = S.hc.opening_slot q
    · subst d
      exact hopening w hw
    · have hdlt : S.hc.opening_slot q < d :=
        lt_of_le_of_ne hdlo (Ne.symm heq)
      have hpredLo : S.hc.opening_slot q ≤ d - 1 := Nat.le_pred_of_lt hdlt
      have hdpos : 0 < d := lt_of_lt_of_le
        (by
          unfold Protocol.HealConfig.opening_slot
          exact Nat.mul_pos hq
            (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)) hdlo
      have hpredLt : d - 1 < seedRoundLastSlot S q :=
        lt_of_lt_of_le (Nat.sub_lt hdpos Nat.zero_lt_one) hdhi
      have hin := (hround (d - 1) hpredLo hpredLt).vote w hw
      simpa only [Nat.sub_add_cancel (Nat.succ_le_iff.mpr hdpos)] using hin
  have hactive : RoundCeilingActiveAt S rho q C :=
    { voteDuty := by
        intro d hdlo hdhi w hw
        have hdpos : 0 < d := lt_of_lt_of_le
          (by
            unfold Protocol.HealConfig.opening_slot
            exact Nat.mul_pos hq
              (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)) hdlo
        exact frozenVoterCandidateTree_subset_filtered S.E _
          (by simpa only [Nat.sub_add_cancel (Nat.succ_le_iff.mpr hdpos)] using
            (hvote d hdlo hdhi w hw).candidate)
      confirmation := by
        intro s hslo hshi w hw
        exact ((hround s hslo hshi).confirmation w hw).candidate
      action := haction
      proposer := hproposer }
  refine ⟨?_, hactive⟩
  exact
    { voteDuty := by
        intro d hdlo hdhi w hw
        have hdpos : 0 < d := lt_of_lt_of_le
          (by
            unfold Protocol.HealConfig.opening_slot
            exact Nat.mul_pos hq
              (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)) hdlo
        simpa only [Nat.sub_add_cancel (Nat.succ_le_iff.mpr hdpos)] using
          (hvote d hdlo hdhi w hw).root
      confirmation := by
        intro s hslo hshi w hw
        exact ((hround s hslo hshi).confirmation w hw).root
      action := by
        intro w hw
        exact Proofs.Records.preceq_get_fg_root_of_mem_filtered (haction w hw)
      proposer := by
        intro hp
        exact Proofs.Records.preceq_get_fg_root_of_mem_filtered (hproposer hp) }

/-! ## Opening and in-round Goldfish cones -/

/-- The honest vote emission of a frozen duty head. -/
theorem seedVoteDutyHead_emits
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {d : Slot} (hd : 0 < d)
    (hwCommittee : w ∈ S.E.committee d)
    (hhor : Protocol.vote_time S.E d ≤ rho.horizon) :
    rho.emits S w (Object.gfVote ⟨w, d, (voteDutyHead S rho w d).root⟩)
      (Protocol.vote_time S.E d) := by
  let read := Internal.NamedRecoveryRead.voteDutyRead S rho w d
  have hslot : read.st.core.s = d := voteDutyRead_slot S rho w d
  have hout :
      (Protocol.NamedDuties.goldfish_vote_with
        (NamedProfile.gradeContract read.cache)
        S.E S.hc (S.node w) read.st).2 =
          some ⟨(S.node w).val_index, read.st.core.s,
            (voterHeadAt S rho w d).root⟩ := by
    simp only [Protocol.NamedDuties.goldfish_vote_with,
      Protocol.goldfish_vote_with]
    rw [if_pos]
    · rfl
    · rw [S.node_val_index, hslot]
      exact hwCommittee
  have ho : Object.gfVote
      ⟨(S.node w).val_index, read.st.core.s, (voterHeadAt S rho w d).root⟩ ∈
      (on_tick_emit S w
        (rho.stateBeforeTime S (Protocol.vote_time S.E d) w)
        (Protocol.vote_time S.E d)).2 := by
    exact on_tick_emit_vote_mem S w
      (rho.stateBeforeTime S (Protocol.vote_time S.E d) w) d hd hout
  have hem := emits_of_on_tick_emit S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hw
    (publicTime_vote_time S d) (vote_time_nonneg S.E d) hhor
      ho
  simpa only [S.node_val_index, hslot, voteDutyHead] using hem

/-- The prepared vote-duty head has a retained named body in the run. -/
theorem seedVoteDutyHead_runBlock
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) (d : Slot) :
    ∃ H : NamedBlock V,
      H.erase = voterHeadAt S rho w d ∧ RunBlock S rho H := by
  let read := Internal.NamedRecoveryRead.voteDutyRead S rho w d
  let st := read.st.core
  let tree := voterCandidateTreeAt S rho w d
  let H := voterHeadAt S rho w d
  have hinvPre : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (rho.stateBeforeTime S (Protocol.vote_time S.E d) w).st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
      (Protocol.vote_time S.E d) w).1
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg read.st := by
    simpa only [read, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt] using
      Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ _ hinvPre
  have hroot : Protocol.get_fg_root st.toHealing.toFG ∈ st.T :=
    Proofs.NamedStoreRoots.fg_root_mem read.st hinv.1.2
  have hanchor : voterAnchorAt S rho w d ∈ st.T := by
    exact Proofs.NamedConfirmationMembership.runtime_anchor_mem read.cache
      S.E S.hc st.toHealing (S.hc.round_of st.s) hroot
  have htree : tree ⊆ st.T := by
    intro D hD
    have hprocessed := Proofs.Records.get_filtered_block_tree_from_subset
      st.toHealing.toFG
      (Protocol.voter_processed_block_tree S.E st.toHealing.toFG.toSG.toGoldfishStore st.s) hD
    exact (Finset.mem_filter.mp hprocessed).1
  have hHmem : H ∈ st.T := by
    rw [show H = Protocol.ghost (voterAnchorAt S rho w d) tree
        (Protocol.goldfish_score S.E st.T
          (Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (st.s - 1))
        (Protocol.goldfish_eligible S.E st.σ st.h_max st.T st.s
          (Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s)
          (st.s - 1)) by rfl]
    exact Proofs.Records.ghost_mem_of _ _ hanchor htree
  have hHpre : H ∈
      (rho.stateBeforeTime S (Protocol.vote_time S.E d) w).st.core.T := by
    simpa only [read, st, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using hHmem
  exact Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hw
      (Protocol.vote_time S.E d) hHpre

/-- With the frozen cone input of the preceding slot and the local anchor
below the cone target, every honest vote head of the next slot reaches the
local viability boundary. -/
theorem seedHeadThin_of_voteInputs
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {M : Height} {s : Slot} {C : Block V}
    (hhor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    (hinputs : ∀ w ∈ rho.honest, GoldfishConeVoteInputs S rho s C w)
    (hanchor : ∀ w ∈ rho.honest,
      Block.Preceq (voterAnchorAt S rho w (s + 1)) C)
    (hfrontier : ∀ w ∈ rho.honest,
      (voteDutyStore S rho w (s + 1)).h_max = M)
    {X : NamedBlock V} (hX : NamedHonestHead S rho (s + 1) X) :
    M - 1 ≤ (derive_named S.E S.cfg X).h := by
  obtain ⟨w, hw, hwCommittee, hXrun, hXemit⟩ := hX
  have hYemit :=
    seedVoteDutyHead_emits S adm hw (Nat.succ_pos s) hwCommittee hhor
  have hrootEq : X.erase.root = (voterHeadAt S rho w (s + 1)).root :=
    congrArg GoldfishVote.head
      (emits_gfVote_unique S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hXemit hYemit rfl)
  obtain ⟨H, hHerase, hHrun, hfloor⟩ :=
    voteDutyHead_height_ge_frontier_sub_one_of_candidate
      S adm hw (hinputs w hw) (hanchor w hw)
  have hrootNamed : X.root = H.root := by
    rw [← Proofs.NamedWire.erase_root X, ← Proofs.NamedWire.erase_root H, hHerase]
    exact hrootEq
  have hXH : X = H :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      X H hXrun hHrun X H (Or.inl (Proofs.NamedAncestry.named_self X))
      (Or.inr (Proofs.NamedAncestry.named_self H)) hrootNamed
  rw [hXH]
  simpa only [hfrontier w hw] using hfloor

/-- The same, packaged as a thin honest head for an arbitrary cone target of
the next slot. -/
theorem seedThinHead_of_voteInputs
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {M : Height} {s : Slot} {C E : Block V}
    (hhor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    (hinputs : ∀ w ∈ rho.honest, GoldfishConeVoteInputs S rho s C w)
    (hanchor : ∀ w ∈ rho.honest,
      Block.Preceq (voterAnchorAt S rho w (s + 1)) C)
    (hfrontier : ∀ w ∈ rho.honest,
      (voteDutyStore S rho w (s + 1)).h_max = M)
    (hcone : NamedHonestVotesCone S rho (s + 1) (fun X => Block.Preceq E X)) :
    ThinHonestHeadAt S rho M (s + 1) E := by
  have hpositive : 0 < ((S.E.committee (s + 1)) ∩ rho.honest).card := by
    have hc := hcom (s + 1)
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpositive
  have hwCommittee : w ∈ S.E.committee (s + 1) := (Finset.mem_inter.mp hw).1
  have hwHonest : w ∈ rho.honest := (Finset.mem_inter.mp hw).2
  obtain ⟨X, hEX, hXrun, hXemit⟩ := hcone w hwHonest hwCommittee
  have hX : NamedHonestHead S rho (s + 1) X :=
    ⟨w, hwHonest, hwCommittee, hXrun, hXemit⟩
  exact ⟨X, hX, hEX,
    seedHeadThin_of_voteInputs S adm hhor hinputs hanchor hfrontier hX⟩

/-- Every vote duty owned by the round has the ceiling's cone input. The
opening duty uses the boundary step input; all later duties use the in-round
slot inputs. -/
theorem roundCeiling_voteInputs
    (S : Setup V) {rho : Run V} {M : Height} {q : Round} {C : NamedBlock V}
    (h : RoundCeilingAt S rho M q C)
    {d : Slot} (hdlo : S.hc.opening_slot q ≤ d)
    (hdhi : d ≤ seedRoundLastSlot S q)
    {w : V} (hw : w ∈ rho.honest) :
    GoldfishConeVoteInputs S rho (d - 1) C.erase w := by
  by_cases heq : d = S.hc.opening_slot q
  · subst d
    exact h.openingStepInputs w hw
  · have hdlt : S.hc.opening_slot q < d := lt_of_le_of_ne hdlo (Ne.symm heq)
    have hpredLo : S.hc.opening_slot q ≤ d - 1 := Nat.le_pred_of_lt hdlt
    have hdpos : 0 < d := lt_of_lt_of_le
      (by
        unfold Protocol.HealConfig.opening_slot
        exact Nat.mul_pos h.roundPositive
          (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)) hdlo
    have hpredLt : d - 1 < seedRoundLastSlot S q :=
      lt_of_lt_of_le (Nat.sub_lt hdpos Nat.zero_lt_one) hdhi
    exact (h.roundInputs (d - 1) hpredLo hpredLt).vote w hw

/-- The vote read of any slot owned by the round is inside the horizon. -/
theorem roundCeiling_voteInHorizon
    (S : Setup V) {rho : Run V} {M : Height} {q : Round} {C : NamedBlock V}
    (h : RoundCeilingAt S rho M q C)
    {d : Slot} (hdhi : d ≤ seedRoundLastSlot S q) :
    Protocol.vote_time S.E d ≤ rho.horizon := by
  have hlastPos : 0 < seedRoundLastSlot S q :=
    Nat.zero_lt_of_lt (openingSlot_lt_seedRoundLastSlot S q)
  have hpred : seedRoundLastSlot S q - 1 + 1 = seedRoundLastSlot S q :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hlastPos)
  have hlastToConf : Protocol.vote_time S.E (seedRoundLastSlot S q) ≤
      Protocol.confirmation_time S.E (seedRoundLastSlot S q - 1) := by
    rw [← hpred,
      ← Protocol.vote_time_succ_add_delta_eq_confirmation_time]
    exact le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)
  exact (Protocol.vote_time_mono_slots S.E hdhi).trans
    (hlastToConf.trans h.roundConfirmationInHorizon)

/-- Every honest Goldfish vote head at a slot owned by the round reaches the
local viability boundary. This is the activity witness that replaces the previous
numeric height field of the ceiling. -/
theorem roundCeiling_headThin
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {M : Height} {q : Round} {C : NamedBlock V}
    (h : RoundCeilingAt S rho M q C)
    {d : Slot} (hdlo : S.hc.opening_slot q ≤ d)
    (hdhi : d ≤ seedRoundLastSlot S q)
    {X : NamedBlock V} (hX : NamedHonestHead S rho d X) :
    M - 1 ≤ (derive_named S.E S.cfg X).h := by
  obtain ⟨w, hw, hwCommittee, hXrun, hXemit⟩ := hX
  have hdpos : 0 < d := lt_of_lt_of_le
    (by
      unfold Protocol.HealConfig.opening_slot
      exact Nat.mul_pos h.roundPositive
        (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)) hdlo
  have hpred : d - 1 + 1 = d := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hdpos)
  have hlastPos : 0 < seedRoundLastSlot S q :=
    Nat.zero_lt_of_lt (openingSlot_lt_seedRoundLastSlot S q)
  have hlastPred : seedRoundLastSlot S q - 1 + 1 = seedRoundLastSlot S q :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hlastPos)
  have hvoteHor : Protocol.vote_time S.E d ≤ rho.horizon :=
    roundCeiling_voteInHorizon S h hdhi
  have hYemit := seedVoteDutyHead_emits S adm hw hdpos hwCommittee hvoteHor
  have hrootEq : X.erase.root = (voterHeadAt S rho w d).root :=
    congrArg GoldfishVote.head
      (emits_gfVote_unique S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hXemit hYemit rfl)
  obtain ⟨H, hHerase, hHrun, hfloor⟩ :=
    voteDutyHead_height_ge_frontier_sub_one_of_candidate
      S adm hw (roundCeiling_voteInputs S h hdlo hdhi hw)
      (by simpa only [hpred] using h.voteAnchor d hdlo hdhi w hw)
  have hrootNamed : X.root = H.root := by
    rw [← Proofs.NamedWire.erase_root X, ← Proofs.NamedWire.erase_root H, hHerase]
    simpa only [hpred] using hrootEq
  have hXH : X = H :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      X H hXrun hHrun X H (Or.inl (Proofs.NamedAncestry.named_self X))
      (Or.inr (Proofs.NamedAncestry.named_self H)) hrootNamed
  have hfrontier := h.gateOff.voteFrontier d hdlo
    (by simpa only [hlastPred] using hdhi) w hw
  rw [hXH]
  simpa only [hpred, hfrontier] using hfloor

/-- Any cone at a slot owned by the round has a thin honest head. -/
theorem roundCeiling_thinHead_of_cone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {M : Height} {q : Round} {C : NamedBlock V} {E : Block V}
    (h : RoundCeilingAt S rho M q C)
    {d : Slot} (hdlo : S.hc.opening_slot q ≤ d)
    (hdhi : d ≤ seedRoundLastSlot S q)
    (hcone : NamedHonestVotesCone S rho d (fun X => Block.Preceq E X)) :
    ThinHonestHeadAt S rho M d E := by
  have hpositive : 0 < ((S.E.committee d) ∩ rho.honest).card := by
    have hc := hcom d
    omega
  obtain ⟨w, hw⟩ := Finset.card_pos.mp hpositive
  have hwCommittee : w ∈ S.E.committee d := (Finset.mem_inter.mp hw).1
  have hwHonest : w ∈ rho.honest := (Finset.mem_inter.mp hw).2
  obtain ⟨X, hEX, hXrun, hXemit⟩ := hcone w hwHonest hwCommittee
  have hX : NamedHonestHead S rho d X :=
    ⟨w, hwHonest, hwCommittee, hXrun, hXemit⟩
  exact ⟨X, hX, hEX, roundCeiling_headThin S adm h hdlo hdhi hX⟩

/-- The opening vote cone from the boundary cone data alone. No anchor field
and no ceiling record are used, so a first-ceiling producer can instantiate it
with the common FG root in the role of the previous ceiling. -/
theorem seedOpeningVotes_of_cone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {q : Round} (hq : 0 < q) {C : Block V}
    (hpostPrev : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot q - 1))
    (hprevConfHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot q - 1) ≤ rho.horizon)
    (hlastVotes : NamedHonestVotesCone S rho (S.hc.opening_slot q - 1)
      (fun X => Block.Preceq C X))
    (hopeningStepInputs : ∀ w ∈ rho.honest, GoldfishConeVoteInputs S rho
      (S.hc.opening_slot q - 1) C w) :
    NamedHonestVotesCone S rho (S.hc.opening_slot q)
      (fun X => Block.Preceq C X) := by
  have hs : 0 < S.hc.opening_slot q - 1 := by
    unfold Protocol.HealConfig.opening_slot
    have hR : 2 ≤ S.hc.R := S.hc.R_ge_two
    have hqOne : 1 ≤ q := Nat.succ_le_iff.mpr hq
    have hopenTwo : 2 ≤ q * S.hc.R := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul hqOne hR
    exact lt_of_lt_of_le Nat.zero_lt_one
      (Nat.le_sub_of_add_le hopenTwo)
  intro w hw hwcommittee
  let s := S.hc.opening_slot q - 1
  have hhead : Block.Preceq C (voterHeadAt S rho w (s + 1)) :=
    goldfishCone_step S adm hcom hs hpostPrev hprevConfHor hlastVotes hw
      (hopeningStepInputs w hw)
  obtain ⟨X, hXerase, hXrun⟩ :=
    seedVoteDutyHead_runBlock S adm hw (s + 1)
  refine ⟨X, ?_, hXrun, ?_⟩
  · rw [hXerase]
    exact hhead
  have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
    apply le_trans (le_of_lt ?_) hprevConfHor
    rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E s]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  have heq : s + 1 = S.hc.opening_slot q := by
    simpa only [s] using openingSlot_pred_succ S hq
  have hem := seedVoteDutyHead_emits S adm (d := S.hc.opening_slot q) hw
    (by
      unfold Protocol.HealConfig.opening_slot
      exact Nat.mul_pos hq
        (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two))
    hwcommittee (by simpa only [← heq] using hvoteHor)
  simpa only [hXerase, heq] using hem

/-- Every genuine honest opening confirmation is above the protected block, from
the boundary cone data alone. -/
theorem seedOpeningConfirmation_of_cone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {q : Round} (hq : 0 < q) {C D : Block V}
    (hpostPrev : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot q - 1))
    (hprevConfHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot q - 1) ≤ rho.horizon)
    (hpostOpening : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot q))
    (hopeningHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hlastVotes : NamedHonestVotesCone S rho (S.hc.opening_slot q - 1)
      (fun X => Block.Preceq C X))
    (hopeningStepInputs : ∀ w ∈ rho.honest, GoldfishConeVoteInputs S rho
      (S.hc.opening_slot q - 1) C w)
    {w : V} (hw : w ∈ rho.honest)
    (hconfInputs : GoldfishConeConfirmationInputs S rho
      (S.hc.opening_slot q) C w)
    (hD : GenuineConfirmationWith
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho w
          (S.hc.opening_slot q)).cache)
      S.E S.hc (confStore S rho w (S.hc.opening_slot q))
        (S.hc.opening_slot q) D) :
    Block.Preceq C D := by
  have hopenPos : 0 < S.hc.opening_slot q := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos hq (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  exact goldfishCone_confirmation S adm hcom hopenPos hpostOpening
    hopeningHor
    (seedOpeningVotes_of_cone S adm hcom hq hpostPrev hprevConfHor
      hlastVotes hopeningStepInputs) hw hconfInputs hD

/-- Every honest opening vote is above the round ceiling. -/
theorem roundCeiling_openingVotes
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {M : Height} {q : Round} {C : NamedBlock V}
    (h : RoundCeilingAt S rho M q C) :
    NamedHonestVotesCone S rho (S.hc.opening_slot q)
      (fun X => Block.Preceq C.erase X) :=
  seedOpeningVotes_of_cone S adm hcom h.roundPositive h.postPreviousVote
    h.previousConfirmationInHorizon h.lastVotes h.openingStepInputs

/- A finalized ceiling supplies an honest vote cone without a Goldfish
induction. Every honest vote head is at height at least `M - 1`; accountable
finality therefore puts it above a finalized block of height at most
`M - 2`. -/



/-- Every genuine honest opening confirmation is above the ceiling. -/
theorem roundCeiling_openingConfirmation
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {M : Height} {q : Round} {C : NamedBlock V} {D : Block V}
    (h : RoundCeilingAt S rho M q C)
    {w : V} (hw : w ∈ rho.honest)
    (hD : GenuineConfirmationWith
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho w
          (S.hc.opening_slot q)).cache)
      S.E S.hc (confStore S rho w (S.hc.opening_slot q))
        (S.hc.opening_slot q) D) :
    Block.Preceq C.erase D := by
  have hopeningHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon :=
    (confirmationTime_mono S.E
      (openingSlot_le_seedRoundLastSlot_pred S q)).trans
      h.roundConfirmationInHorizon
  exact seedOpeningConfirmation_of_cone S adm hcom h.roundPositive
    h.postPreviousVote h.previousConfirmationInHorizon h.postOpeningVote
    hopeningHor h.lastVotes h.openingStepInputs hw
    ((h.roundInputs (S.hc.opening_slot q) (le_refl _)
      (openingSlot_lt_seedRoundLastSlot S q)).confirmation w hw) hD

/-- Genuine opening confirmations selected by two honest readers are
compatible. -/
theorem roundCeiling_openingConfirmationsCompatible
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {M : Height} {q : Round} {C : NamedBlock V} {D E : Block V}
    (h : RoundCeilingAt S rho M q C)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (hD : GenuineConfirmationWith
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v
          (S.hc.opening_slot q)).cache)
      S.E S.hc (confStore S rho v (S.hc.opening_slot q))
        (S.hc.opening_slot q) D)
    (hE : GenuineConfirmationWith
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho w
          (S.hc.opening_slot q)).cache)
      S.E S.hc (confStore S rho w (S.hc.opening_slot q))
        (S.hc.opening_slot q) E) :
    Block.compatible D E = true := by
  have hopeningHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon :=
    (confirmationTime_mono S.E
      (openingSlot_le_seedRoundLastSlot_pred S q)).trans
      h.roundConfirmationInHorizon
  exact Protocol.sameSlot_genuine_compatible_after_gst
    S adm hv hw h.postOpeningProposal hopeningHor hD hE

/-- the previous ceiling itself persists through all Goldfish votes in the round.
The successor opening vote belongs to the next ceiling record. -/
theorem roundCeiling_votesThrough
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {M : Height} {q : Round} {C : NamedBlock V}
    (h : RoundCeilingAt S rho M q C) :
    ∀ s : Slot, S.hc.opening_slot q ≤ s →
      s ≤ seedRoundLastSlot S q →
      NamedHonestVotesCone S rho s (fun X => Block.Preceq C.erase X) := by
  have hopenPos : 0 < S.hc.opening_slot q := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos h.roundPositive
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hlastPredConf : Protocol.confirmation_time S.E
      (seedRoundLastSlot S q - 1) ≤ rho.horizon :=
    h.roundConfirmationInHorizon
  have hfold := goldfishCone_induction
    S adm hcom hopenPos h.postOpeningVote hlastPredConf
      (roundCeiling_openingVotes S adm hcom h)
      (fun s hlo hhi => h.roundInputs s hlo
        (Nat.lt_of_le_of_lt hhi (Nat.sub_lt
          (Nat.zero_lt_of_lt (openingSlot_lt_seedRoundLastSlot S q))
          Nat.zero_lt_one)))
      (s0 := S.hc.opening_slot q) (s1 := seedRoundLastSlot S q - 1)
  intro s hlo hhi
  apply hfold.1 s hlo
  have hlastPos : 0 < seedRoundLastSlot S q :=
    Nat.zero_lt_of_lt (openingSlot_lt_seedRoundLastSlot S q)
  rw [Nat.sub_add_cancel (Nat.succ_le_iff.mpr hlastPos)]
  exact hhi

/- A finalized ceiling gives the same in-round vote cone directly from the
frozen head floor and accountable finality. This proof does not use the
preceding-slot cone after the opening vote. -/




/- Re-base the boundary votes of a round from its current ceiling to a
finalized low descendant. The previous ceiling is only the frozen candidate used
to prove that each boundary head reaches `M - 1`. -/



/-! ## Named vote-duty path -/

/-- The named twin of `Protocol.votePath_of_candidate`: every strict
ancestor between the prepared vote anchor and a frozen candidate remains in
the voter's frozen candidate tree. -/
theorem votePathAt_of_candidate
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot} {C : Block V}
    (hC : C ∈ voterCandidateTreeAt S rho w (s + 1)) :
    ∀ D : Block V,
      Block.Preceq (voterAnchorAt S rho w (s + 1)) D →
      D ≠ voterAnchorAt S rho w (s + 1) → Block.Preceq D C → D ≠ C →
      D ∈ voterCandidateTreeAt S rho w (s + 1) := by
  let duty := voteDutyStore S rho w (s + 1)
  have hCraw : C ∈ voter_candidate_tree S.E duty.toHealing := by
    simpa only [voterCandidateTreeAt, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, duty, voteDutyStore] using hC
  have hCfull : C ∈ Protocol.get_filtered_block_tree duty.toHealing.toFG :=
    frozenVoterCandidateTree_subset_filtered S.E duty.toHealing hCraw
  have hCT : C ∈ duty.T :=
    Proofs.Records.get_filtered_block_tree_subset duty.toHealing.toFG hCfull
  have hpc : ParentClosed duty := by
    simpa only [duty, voteDutyStore, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using
      Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
        (Protocol.vote_time S.E (s + 1)) w
  have hFJ : Block.Preceq duty.F duty.J := by
    simpa only [duty, voteDutyStore, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using
      Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
        (Protocol.vote_time S.E (s + 1)) w
  have hrootAnchor : Block.Preceq
      (Protocol.get_fg_root duty.toHealing.toFG)
      (voterAnchorAt S rho w (s + 1)) := by
    simpa only [duty, voterAnchorAt, Internal.PhaseGrades.nodeAnchor,
      Internal.PhaseGrades.nodeRead,
      Internal.NamedRecoveryRead.voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      fg_root_preceq_get_sg_root_with_frame
        (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).cache S.E S.hc
        duty.toHealing (S.hc.round_of duty.toHealing.s)
  intro D hAD _hDne hDC _hDneC
  have hDT : D ∈ duty.T :=
    Proofs.Records.mem_of_preceq ((parentClosed_iff duty).mp hpc).2 D C hCT hDC
  have hCprocessed : C ∈ Protocol.voter_processed_block_tree S.E
      duty.toHealing.toFG.toSG.toGoldfishStore duty.toHealing.s := by
    have hCdata := hCraw
    simp only [voter_candidate_tree, Protocol.get_filtered_block_tree_from,
      Protocol.viable_tree, Protocol.finalized_descendants,
      Finset.mem_filter] at hCdata
    exact hCdata.1.1.1
  have hDfull : D ∈ Protocol.get_filtered_block_tree duty.toHealing.toFG := by
    apply Proofs.Records.mem_filtered_of_preceq (st := duty.toHealing.toFG)
      hFJ hCfull hDT hDC
    exact Block.preceq_trans hrootAnchor hAD
  have hDprocessed : D ∈ Protocol.voter_processed_block_tree S.E
      duty.toHealing.toFG.toSG.toGoldfishStore duty.toHealing.s := by
    have hDprocessed' := WeakGoldfish.ancestorProcessed_of_voterProcessed
      (S := S) (rho := rho) (w := w) (s := s) (B := C)
      (adm := adm.toNamedAdmissibleCore) hw hCprocessed D hDC
    simpa only [duty] using hDprocessed'
  have hCdata := hCraw
  have hDdata := hDfull
  simp only [voter_candidate_tree, Protocol.get_filtered_block_tree,
    Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq] at hCdata hDdata
  obtain ⟨W, hWprocessed, hCW, hheight⟩ := hCdata.1.2
  have hDcandidate' : D ∈ voter_candidate_tree S.E duty.toHealing := by
    simp only [voter_candidate_tree, Protocol.get_filtered_block_tree_from,
      Protocol.viable_tree, Protocol.finalized_descendants,
      Protocol.viable, Finset.mem_filter, decide_eq_true_eq]
    exact ⟨⟨⟨hDprocessed, hDdata.1.1.2⟩, W, hWprocessed,
      Block.preceq_trans hDC hCW, hheight⟩, hDdata.2⟩
  simpa only [voterCandidateTreeAt, Internal.NamedRecoveryRead.voteDutyRead,
    NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
    Protocol.NamedStore.setClock, duty, voteDutyStore] using hDcandidate'

/-- Relay a preceding honest vote cone to the next vote duty. The cone target
may be below the frontier band: its activity comes from a thin honest head of
the same slot, and the caller supplies the local root ordering. -/
theorem seedRelayVoteFacts
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {s : Slot} (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V} {M : Height}
    (hvotes : NamedHonestVotesCone S rho s (fun X => Block.Preceq C X))
    (hthin : ThinHonestHeadAt S rho M s C)
    {w : V} (hw : w ∈ rho.honest)
    (hfrontier : (voteDutyStore S rho w (s + 1)).h_max = M)
    (hgate : (voteDutyStore S rho w (s + 1)).h_j + 2 ≤ M)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyStore S rho w (s + 1)).toHealing.toFG) C) :
    C ∈ voter_candidate_tree S.E
        (voteDutyStore S rho w (s + 1)).toHealing ∧
      ∀ D : Block V,
        Block.Preceq
          (voterAnchorAt S rho w (s + 1)) D →
        D ≠ voterAnchorAt S rho w (s + 1) →
        Block.Preceq D C → D ≠ C →
        D ∈ voter_candidate_tree S.E
          (voteDutyStore S rho w (s + 1)).toHealing := by
  obtain ⟨H, hHhonest, hCH, hHheight⟩ := hthin
  obtain ⟨x, hxHonest, hxCommittee, hHrun, hHemit⟩ := hHhonest
  have hHhonest' : HonestHead S rho s H.erase :=
    ⟨x, hxHonest, hxCommittee, ⟨H, rfl, hHrun⟩, hHemit⟩
  have hHprocessed := honestHead_voterProcessed_at_nextDuty_of_postHealingCone
    S adm hpost hhor hvotes hHhonest' hw hroot
  have hHmem : H.erase ∈ (rho.storeBeforeTime S w
      (Protocol.vote_time S.E (s + 1))).T := by
    have hdata := hHprocessed
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter] at hdata
    simpa only [voteDutyStore, voteStore, tickStore] using hdata.1
  have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
    apply le_trans (le_of_lt ?_) hhor
    rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E s]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  have hM : 1 ≤ M :=
    (Nat.succ_le_succ (Nat.zero_le 1)).trans
      ((Nat.le_add_left 2 (voteDutyStore S rho w (s + 1)).h_j).trans hgate)
  have hfilteredPre := frontierAncestor_filtered_of_gateOff
    S adm hsb hw hvoteHor hHmem rfl hHrun hCH hHheight hM
      (by simpa only [voteDutyStore, voteStore, tickStore] using hfrontier)
      (by simpa only [voteDutyStore, voteStore, tickStore] using hgate)
      (by simpa only [voteDutyStore, voteStore, tickStore] using hroot)
  have hfiltered : C ∈ Protocol.get_filtered_block_tree
      (voteDutyStore S rho w (s + 1)).toHealing.toFG := by
    simpa only [voteDutyStore, voteStore, tickStore] using hfilteredPre
  have hmax : (voteDutyStore S rho w (s + 1)).h_max ≤
      (derive_named S.E S.cfg H).h + 1 := by
    rw [hfrontier]
    exact Nat.sub_le_iff_le_add.mp hHheight
  have hCcandidate : C ∈ voterCandidateTreeAt S rho w (s + 1) := by
    simpa only [voterCandidateTreeAt, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, voteDutyStore] using
      (namedAncestorCandidate_of_processedDescendant_and_hMax
        S adm hw hHprocessed hHrun hCH hfiltered hmax)
  refine ⟨by
    simpa only [voterCandidateTreeAt, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, voteDutyStore] using hCcandidate, ?_⟩
  intro D hanchor hne hDC hDneC
  have hDfiltered := votePathAt_of_candidate
    S adm hw hCcandidate D hanchor hne hDC hDneC
  have hDfilteredFull : D ∈ Protocol.get_filtered_block_tree
      (voteDutyStore S rho w (s + 1)).toHealing.toFG := by
    simpa only [voterCandidateTreeAt, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, voteDutyStore] using
      frozenVoterCandidateTree_subset_filtered S.E
        (voteDutyStore S rho w (s + 1)).toHealing hDfiltered
  exact namedAncestorCandidate_of_processedDescendant_and_hMax
    S adm hw hHprocessed hHrun (Block.preceq_trans hDC hCH)
      hDfilteredFull hmax

/-- The same relay at the slot-`s` confirmation read. -/
theorem seedRelayConfirmationFacts
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho)
    {s : Slot} (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V} {M : Height}
    (hvotes : NamedHonestVotesCone S rho s (fun X => Block.Preceq C X))
    (hthin : ThinHonestHeadAt S rho M s C)
    {w : V} (hw : w ∈ rho.honest)
    (hfrontier : (confStore S rho w s).h_max = M)
    (hgate : (confStore S rho w s).h_j + 2 ≤ M)
    (hroot : Block.Preceq (confRoot (confStore S rho w s)) C) :
    C ∈ confTree (confStore S rho w s) ∧
      ∀ D : Block V,
        Block.Preceq (confirmationAnchorAt S rho w s) D →
        D ≠ confirmationAnchorAt S rho w s →
        Block.Preceq D C → D ≠ C →
        D ∈ confTree (confStore S rho w s) := by
  obtain ⟨H, hHhonest, hCH, hHheight⟩ := hthin
  obtain ⟨x, hxHonest, hxCommittee, hHrun, hHemit⟩ := hHhonest
  have hHhonest' : HonestHead S rho s H.erase :=
    ⟨x, hxHonest, hxCommittee, ⟨H, rfl, hHrun⟩, hHemit⟩
  have hresolve := headsResolveIn_confStore_of_postHealingCone
    S adm hw hpost ((support_cutoff_le_confirmation_time S.E s).trans hhor)
      hroot hvotes
  have hfind := (hresolve H.erase hHhonest').1
  have hHmem : H.erase ∈ (confStore S rho w s).T :=
    Proofs.HealingLemmas.find?_mem hfind
  have hHpre : H.erase ∈ (rho.storeBeforeTime S w
      (Protocol.confirmation_time S.E s)).T := by
    simpa only [confStore, tickStore] using hHmem
  have hM : 1 ≤ M :=
    (Nat.succ_le_succ (Nat.zero_le 1)).trans
      ((Nat.le_add_left 2 (confStore S rho w s).h_j).trans hgate)
  have hfilteredPre := frontierAncestor_filtered_of_gateOff
    S adm hsb hw hhor hHpre rfl hHrun hCH hHheight hM
      (by simpa only [confStore, tickStore] using hfrontier)
      (by simpa only [confStore, tickStore] using hgate)
      (by simpa only [confRoot, confStore, tickStore] using hroot)
  have hfiltered : C ∈ confTree (confStore S rho w s) := by
    simpa only [confTree, confStore, tickStore] using hfilteredPre
  have hCT : C ∈
      (rho.stateBeforeTime S (Protocol.confirmation_time S.E s) w).st.core.T := by
    have hmem := Proofs.Records.get_filtered_block_tree_subset
      (confStore S rho w s).toHealing.toFG hfiltered
    simpa only [confStore, tickStore] using hmem
  obtain ⟨Cn, _, hCnerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (Protocol.confirmation_time S.E s) w hCT
  have hCnfiltered : Cn.erase ∈ confTree (confStore S rho w s) := by
    rw [hCnerase]
    exact hfiltered
  refine ⟨hfiltered, ?_⟩
  intro D hanchor hne hDC _
  apply Protocol.confPath_of_candidate S hCnfiltered D hanchor hne
  rwa [hCnerase]

/-- Emit the next honest vote cone from one complete vote input. -/
theorem seedHonestVotesCone_succ
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V}
    (hvotes : NamedHonestVotesCone S rho s (fun X => Block.Preceq C X))
    (hinputs : ∀ w ∈ rho.honest, GoldfishConeVoteInputs S rho s C w) :
    NamedHonestVotesCone S rho (s + 1) (fun X => Block.Preceq C X) := by
  intro w hw hwcommittee
  have hhead : Block.Preceq C (voterHeadAt S rho w (s + 1)) :=
    goldfishCone_step S adm hcom hs hpost hhor hvotes hw (hinputs w hw)
  obtain ⟨H, hHerase, hHrun⟩ :=
    seedVoteDutyHead_runBlock S adm hw (s + 1)
  have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
    apply le_trans (le_of_lt ?_) hhor
    rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E s]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  refine ⟨H, ?_, hHrun, ?_⟩
  · rw [hHerase]
    exact hhead
  · simpa only [hHerase] using
      seedVoteDutyHead_emits S adm hw (Nat.succ_pos s) hwcommittee hvoteHor

/-! ## Prepared genuine-confirmation supporter -/

/-- A prepared genuine confirmation has an honest same-slot vote supporter.
This is the ceiling-local twin of the weak confirmation-support producer. -/
theorem genuineConfirmation_exists_honestVoteSupporter_ceiling
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {v : V} (hv : v ∈ rho.honest) {s : Slot} (hs : 0 < s) {B : Block V}
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hgenuine : GenuineConfirmationWith
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).cache)
      S.E S.hc (confStore S rho v s) s B) :
    ∃ x ∈ rho.honest, x ∈ S.E.committee s ∧
      Block.Preceq B (voterHeadAt S rho x s) := by
  let source := confStore S rho v s
  let late := confLate S.E source s
  let votes := confVotes S.E source s
  let supporters := Protocol.goldfishSupporters S.E source.T votes votes s B
  let participants := Protocol.participants S.E late s
  have hN := confNumerator S.E source s
  have hcut := support_cutoff_le_confirmation_time S.E s
  have hvoteHor : Protocol.vote_time S.E s ≤ rho.horizon :=
    (vote_time_le_confirmation_time S.E s).trans hhor
  have hreceipt : ∀ x ∈ S.E.committee s, x ∈ rho.honest →
      (⟨x, s, (voterHeadAt S rho x s).root⟩ : GoldfishVote V) ∈ late := by
    intro x hx hxHon
    have hemit := seedVoteDutyHead_emits S adm hxHon hs hx hvoteHor
    exact Protocol.gfVote_in_cutoff_view_after_gst
      S adm.toNamedAdmissibleCore hxHon hs hpost hemit rfl hv
      _ _ hcut hcut (hcut.trans hhor)
  have hrepresented : (S.E.committee s) ∩ rho.honest ⊆ participants := by
    intro x hx
    have hraw := hreceipt x (Finset.mem_inter.mp hx).1 (Finset.mem_inter.mp hx).2
    simp only [participants, Protocol.participants, Protocol.raw_participants,
      Finset.mem_filter, Finset.mem_univ, true_and, Protocol.participates,
      decide_eq_true_eq]
    apply Finset.card_pos.mpr
    exact ⟨_, Finset.mem_filter.mpr ⟨hraw, rfl⟩⟩
  have hvalid : Protocol.VoteSetValid S.E s late := by
    simpa only [late, source, confStore, tickStore] using
      voteSetValid_confLate_stateBeforeTime S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v
        (Protocol.confirmation_time S.E s) s
  have hsupportRep : supporters ⊆ participants :=
    supporters_subset_participants S.E source.T hN.subset_late s B
  have hex : ∃ x ∈ rho.honest, x ∈ supporters := by
    by_contra hnone
    have hdisjoint : Disjoint ((S.E.committee s) ∩ rho.honest) supporters := by
      apply Finset.disjoint_left.mpr
      intro x hx hsupp
      exact hnone ⟨x, (Finset.mem_inter.mp hx).2, hsupp⟩
    have hsum : ((S.E.committee s) ∩ rho.honest).card + supporters.card ≤
        participants.card := by
      rw [← Finset.card_union_of_disjoint hdisjoint]
      exact Finset.card_le_card (Finset.union_subset hrepresented hsupportRep)
    have hcount : participants.card ≤ (S.E.committee s).card :=
      voters_count_le_committee S.E late s hvalid
    have hmajority := hcom s
    have hgenuine' : GenuineConfirmation
        (contract := NamedProfile.gradeContract
          (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).cache)
        S.E S.hc (confStore S rho v s) s B :=
      ⟨hgenuine.selected, hgenuine.genuine⟩
    have hgate := hgenuine'.eligible
    rw [hN.score_eq_supporters] at hgate
    change participants.card < 2 * supporters.card at hgate
    omega
  obtain ⟨x, hxHon, hxSupport⟩ := hex
  obtain ⟨_, u, hu, hus, htargets⟩ := mem_supporters_iff.mp hxSupport
  have huval : u.val_index = x := (Finset.mem_filter.mp hu).2
  have hul : u ∈ late := hN.subset_late (Finset.mem_filter.mp hu).1
  have hxCommittee : x ∈ S.E.committee s := huval ▸ (hvalid u hul).2
  obtain ⟨H, hfind, hBH⟩ := targets_under_iff.mp htargets
  obtain ⟨n, hn, _⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
    (Protocol.confirmation_time S.E s)
  have hpool : u ∈ (NamedRun.stateBefore S rho n v).st.gf_votes s := by
    have hpool' := (Finset.mem_filter.mp hul).1
    simpa only [late, source, confLate, confStore, tickStore,
      Protocol.NamedStore.pool, Protocol.Store.pool, List.mem_toFinset,
      Run.storeBeforeTime, hn] using hpool'
  obtain ⟨tu, huemit⟩ := Protocol.honestVote_emitted_of_mem_pool_stateBefore
    S adm.toNamedAdmissibleCore v n s hpool (by rw [huval]; exact hxHon)
  rw [huval] at huemit
  have hxemit := seedVoteDutyHead_emits S adm hxHon hs hxCommittee hvoteHor
  have huEq : u = ⟨x, s, (voterHeadAt S rho x s).root⟩ :=
    Proofs.Optimistic.emits_gfVote_unique S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed huemit hxemit hus
  have hroot : H.root = (voterHeadAt S rho x s).root := by
    have h := Proofs.HealingLemmas.find?_root hfind
    simpa only [huEq] using h
  obtain ⟨D, hDerase, hDrun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv
      (Protocol.confirmation_time S.E s) (by
        simpa only [source, confStore, tickStore] using
          Proofs.HealingLemmas.find?_mem hfind)
  obtain ⟨X, hXerase, hXrun⟩ := seedVoteDutyHead_runBlock S adm hxHon s
  have hrootNamed : D.root = X.root := by
    rw [← Proofs.NamedWire.erase_root D, ← Proofs.NamedWire.erase_root X, hDerase, hXerase]
    exact hroot
  have hDX : D = X :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      D X hDrun hXrun D X (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self X)) hrootNamed
  refine ⟨x, hxHon, hxCommittee, ?_⟩
  calc
    Block.Preceq B H := hBH.2
    _ = voterHeadAt S rho x s := by rw [← hDerase, hDX, hXerase]



/-- The complete successor-round assembly records in named-read form. The
prepared anchors are the anchors read by the duty caches, including the
confirmation input and the post-confirmation action read. -/
structure RoundCeilingStepResidualAt
    (S : Setup V) (rho : Run V) (M : Height) (q : Round) (Cstar : Block V) :
    Prop where
  postOpeningProposal : S.E.t_GST ≤
    Protocol.proposal_time S.E (S.hc.opening_slot (q + 1))
  roundConfirmationInHorizon :
    Protocol.confirmation_time S.E (seedRoundLastSlot S (q + 1) - 1) ≤ rho.horizon
  openingStepInputs : ∀ w ∈ rho.honest, GoldfishConeVoteInputs S rho
    (S.hc.opening_slot (q + 1) - 1) Cstar w
  roundInputs : ∀ s : Slot,
    S.hc.opening_slot (q + 1) ≤ s →
      s < seedRoundLastSlot S (q + 1) →
        GoldfishConeSlotInputs S rho s Cstar
  voteActive : ∀ d : Slot,
    S.hc.opening_slot (q + 1) ≤ d →
      d ≤ seedRoundLastSlot S (q + 1) → ∀ w ∈ rho.honest,
        Cstar ∈ Protocol.get_filtered_block_tree
          (voteDutyStore S rho w d).toHealing.toFG
  actionActive : ∀ w ∈ rho.honest,
    Cstar ∈ Protocol.get_filtered_block_tree
      (healStoreAt S rho w (q + 1)).toFG
  voteAnchor : ∀ d : Slot,
    S.hc.opening_slot (q + 1) ≤ d →
      d ≤ seedRoundLastSlot S (q + 1) → ∀ w ∈ rho.honest,
        Block.Preceq (voterAnchorAt S rho w d) Cstar
  confirmationAnchor : ∀ s : Slot,
    S.hc.opening_slot (q + 1) - 1 ≤ s →
      s < seedRoundLastSlot S (q + 1) → ∀ w ∈ rho.honest,
        Block.Preceq (confirmationAnchorAt S rho w s) Cstar
  actionAnchor : ∀ w ∈ rho.honest,
    Block.Preceq
      (PhaseGrades.nodeAnchor
        S (Internal.NamedRecoveryRead.actionDutyRead S rho w (q + 1)) (q + 1)) Cstar
  proposerAnchorCeiling : S.E.proposer (S.hc.opening_slot (q + 1)) ∈ rho.honest →
    Block.Preceq
      (PhaseGrades.nodeAnchor S
        (Internal.NamedRecoveryRead.proposalDutyRead S rho
          (S.hc.opening_slot (q + 1))) (q + 1)) Cstar
  proposerActive : S.E.proposer (S.hc.opening_slot (q + 1)) ∈ rho.honest →
    Cstar ∈ Protocol.get_filtered_block_tree
      (proposerDutyStore S rho (S.hc.opening_slot (q + 1))).toHealing.toFG
  gateOff : GateOffSeedConeWindowAt S rho M
    (S.hc.opening_slot (q + 1)) (seedRoundLastSlot S (q + 1) - 1)
  genuineRun : ∀ w ∈ rho.honest, ∀ D : Block V,
    GenuineConfirmationWith
        (NamedProfile.gradeContract
          (Internal.NamedRecoveryRead.confirmationInputRead S rho w
            (S.hc.opening_slot (q + 1))).cache)
        S.E S.hc
        (confStore S rho w (S.hc.opening_slot (q + 1)))
          (S.hc.opening_slot (q + 1)) D →
      ∃ Dn : NamedBlock V, Dn.erase = D ∧ RunBlock S rho Dn



/-
/-- A genuine opening confirmation persists through every later vote and
genuine confirmation in the round. The confirmation may itself be below the
frontier band: the honest vote heads of the round supply its activity, and the
ceiling's root ordering supplies the local root floor. -/
theorem roundCeiling_persistence
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hsb: SlashableBound S rho)
    {M: Height} {q: Round} {C: NamedBlock V} {D: Block V}
    (h: RoundCeilingAt S rho M q C)
    {v: V} (hv: v ∈ rho.honest)
    (hD: GenuineConfirmationWith
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v
          (S.hc.opening_slot q)).cache)
      S.E S.hc (confStore S rho v (S.hc.opening_slot q))
      (S.hc.opening_slot q) D):
    (∀ s: Slot, S.hc.opening_slot q + 1 ≤ s →
      s ≤ seedRoundLastSlot S q →
        NamedHonestVotesCone S rho s (fun X => Block.Preceq D X)) ∧
    (∀ s: Slot, S.hc.opening_slot q + 1 ≤ s →
      s < seedRoundLastSlot S q →
        GoldfishConeSlotInputs S rho s D) ∧
    (∀ s: Slot, S.hc.opening_slot q + 1 ≤ s →
      s < seedRoundLastSlot S q → ∀ w ∈ rho.honest,
        ∀ E: Block V,
          GenuineConfirmationWith
            (NamedProfile.gradeContract
              (Internal.NamedRecoveryRead.confirmationInputRead S rho w s).cache)
            S.E S.hc (confStore S rho w s) s E →
            Block.Preceq D E):= by
  have hopenPos: 0 < S.hc.opening_slot q:= by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos h.roundPositive
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have holast: S.hc.opening_slot q < seedRoundLastSlot S q:=
    openingSlot_lt_seedRoundLastSlot S q
  have hlastPos: 0 < seedRoundLastSlot S q:= Nat.zero_lt_of_lt holast
  have hlastPred: seedRoundLastSlot S q - 1 + 1 = seedRoundLastSlot S q:=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hlastPos)
  have hosucc: S.hc.opening_slot q + 1 ≤ seedRoundLastSlot S q:=
    Nat.succ_le_iff.mpr holast
  have hCD: Block.Preceq C.erase D:=
    roundCeiling_openingConfirmation S adm hcom h hv hD
  have hopeningHor: Protocol.confirmation_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon:=
    (confirmationTime_mono S.E
      (openingSlot_le_seedRoundLastSlot_pred S q)).trans
      h.roundConfirmationInHorizon
  have hopeningVotes:= roundCeiling_openingVotes S adm hcom h
  obtain ⟨x, hxHonest, hxCommittee, hDH⟩:=
    WeakGoldfish.genuineConfirmation_exists_honestVoteSupporter_after_gst
      S adm.toNamedAdmissibleCore hcom hv hopenPos h.postOpeningVote hopeningHor hD
  have hvoteHor: Protocol.vote_time S.E (S.hc.opening_slot q) ≤ rho.horizon:= by
    apply le_trans (le_of_lt ?_) hopeningHor
    rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time
      S.E (S.hc.opening_slot q)]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  obtain ⟨H, hHerase, hHrun⟩:=
    seedVoteDutyHead_runBlock S adm hxHonest (S.hc.opening_slot q)
  have hHemit:= seedVoteDutyHead_emits S adm hxHonest
    (by
      unfold Protocol.HealConfig.opening_slot
      exact Nat.mul_pos h.roundPositive
        (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)) hxCommittee hvoteHor
  have hH: NamedHonestHead S rho (S.hc.opening_slot q) H:=
    ⟨x, hxHonest, hxCommittee, hHrun, by simpa only [hHerase] using hHemit⟩
  have hDH': Block.Preceq D H.erase:= by
    rw [hHerase]
    exact hDH
  have hHthin: M - 1 ≤ (derive_named S.E S.cfg H).h:=
    roundCeiling_headThin S adm h (le_refl _) (Nat.le_of_lt holast) hH
  have hH': HonestHead S rho (S.hc.opening_slot q) H.erase:=
    ⟨x, hxHonest, hxCommittee, ⟨H, rfl, hHrun⟩, hHemit⟩
  have hseedCandidate: ∀ w ∈ rho.honest,
      w ∈ S.E.committee (S.hc.opening_slot q + 1) →
      D ∈ voter_candidate_tree S.E
        (voteDutyStore S rho w (S.hc.opening_slot q + 1)).toHealing:= by
    intro w hw _
    have hrootC:= h.aboveRoot.voteDuty (S.hc.opening_slot q + 1)
      (Nat.le_succ _) hosucc w hw
    have hrootD: Block.Preceq
        (Protocol.get_fg_root
          (voteDutyStore S rho w
            (S.hc.opening_slot q + 1)).toHealing.toFG) D:=
      Block.preceq_trans hrootC hCD
    have hHprocessed:= honestHead_voterProcessed_at_nextDuty_of_postHealingCone
      S adm h.postOpeningVote hopeningHor hopeningVotes hH' hw hrootC
    have hHmem: H ∈ (rho.storeBeforeTime S w
        (Protocol.vote_time S.E (S.hc.opening_slot q + 1))).T:= by
      have hdata:= hHprocessed
      simp only [Protocol.voter_processed_block_tree,
        Finset.mem_filter] at hdata
      simpa only [voteDutyStore, voteStore, tickStore] using hdata.1
    have hfrontier:= h.gateOff.voteFrontier (S.hc.opening_slot q + 1)
      (Nat.le_succ _) (by simpa only [hlastPred] using hosucc) w hw
    have hgate:= h.gateOff.voteGateOff (S.hc.opening_slot q + 1)
      (Nat.le_succ _) (by simpa only [hlastPred] using hosucc) w hw
    have hM: 1 ≤ M:=
      (Nat.succ_le_succ (Nat.zero_le 1)).trans
        ((Nat.le_add_left 2
          (voteDutyStore S rho w (S.hc.opening_slot q + 1)).h_j).trans hgate)
    have hvoteHor: Protocol.vote_time S.E
        (S.hc.opening_slot q + 1) ≤ rho.horizon:= by
      apply le_trans (le_of_lt ?_) hopeningHor
      rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time
        S.E (S.hc.opening_slot q)]
      exact Int.lt_add_of_pos_right _ S.E.Δ_pos
    have hfilteredPre:= frontierAncestor_filtered_of_gateOff
      S adm hsb hw hvoteHor hHmem rfl hHrun hDH' hHthin hM
        (by simpa only [voteDutyStore, voteStore, tickStore] using hfrontier)
        (by simpa only [voteDutyStore, voteStore, tickStore] using hgate)
        (by simpa only [voteDutyStore, voteStore, tickStore] using hrootD)
    have hfiltered: D ∈ Protocol.get_filtered_block_tree
        (voteDutyStore S rho w
          (S.hc.opening_slot q + 1)).toHealing.toFG:= by
      simpa only [voteDutyStore, voteStore, tickStore] using hfilteredPre
    have hmax: (voteDutyStore S rho w (S.hc.opening_slot q + 1)).h_max ≤
        (derive_named S.E S.cfg H).h + 1:= by
      rw [hfrontier]
      exact Nat.sub_le_iff_le_add.mp hHthin
    exact namedAncestorCandidate_of_processedDescendant_and_hMax
      S adm hw hHprocessed hHrun hDH' hfiltered hmax
  have hseedAnchor: ∀ w ∈ rho.honest,
      w ∈ S.E.committee (S.hc.opening_slot q + 1) →
      Block.Preceq
        (voterAnchorAt S rho w (S.hc.opening_slot q + 1)) D:= by
    intro w hw _
    exact Block.preceq_trans
      (h.voteAnchor (S.hc.opening_slot q + 1) (Nat.le_succ _) hosucc w hw) hCD
  have hconeSucc:=
    honestVotesCone_succ_of_genuineConfirmation_of_frozenVoteReads
      S adm hv h.postOpeningProposal hopeningHor
      (show GenuineConfirmation (contract:=
        NamedProfile.gradeContract
          (Internal.NamedRecoveryRead.confirmationInputRead S rho v
            (S.hc.opening_slot q)).cache)
          S.E S.hc (confStore S rho v (S.hc.opening_slot q))
            (S.hc.opening_slot q) D from ⟨hD.selected, hD.genuine⟩)
      hseedCandidate hseedAnchor
  have hstep: ∀ s: Slot, S.hc.opening_slot q + 1 ≤ s →
      s ≤ seedRoundLastSlot S q - 1 →
      NamedHonestVotesCone S rho s (fun X => Block.Preceq D X) →
      GoldfishConeSlotInputs S rho s D:= by
    intro s hlo hhi hcone
    have hslo: S.hc.opening_slot q ≤ s:= (Nat.le_succ _).trans hlo
    have hsuccHi: s + 1 ≤ seedRoundLastSlot S q:= by
      rw [← hlastPred]
      exact Nat.succ_le_succ hhi
    have hshi: s ≤ seedRoundLastSlot S q:= (Nat.le_succ s).trans hsuccHi
    have hslt: s < seedRoundLastSlot S q:=
      lt_of_lt_of_le (Nat.lt_succ_self s) hsuccHi
    have hthin: ThinHonestHeadAt S rho M s D:=
      roundCeiling_thinHead_of_cone S adm hcom h hslo hshi hcone
    have hpostS: S.E.t_GST ≤ Protocol.vote_time S.E s:=
      h.postOpeningVote.trans (Protocol.vote_time_mono_slots S.E hslo)
    have hhorS: Protocol.confirmation_time S.E s ≤ rho.horizon:=
      (confirmationTime_mono S.E hhi).trans h.roundConfirmationInHorizon
    constructor
    · intro w hw
      have hfrontier:= h.gateOff.voteFrontier (s + 1)
        (hslo.trans (Nat.le_succ s))
        (by simpa only [hlastPred] using hsuccHi) w hw
      have hgate:= h.gateOff.voteGateOff (s + 1)
        (hslo.trans (Nat.le_succ s))
        (by simpa only [hlastPred] using hsuccHi) w hw
      have hrootC:= h.aboveRoot.voteDuty (s + 1)
        (hslo.trans (Nat.le_succ s)) hsuccHi w hw
      have hrootD: Block.Preceq
          (Protocol.get_fg_root
            (voteDutyStore S rho w (s + 1)).toHealing.toFG) D:=
        Block.preceq_trans hrootC hCD
      have hfacts:= seedRelayVoteFacts S adm hsb hpostS hhorS hcone hthin
        hw hfrontier hgate hrootD
      exact
        { candidate:= hfacts.1
          root:= hrootD
          anchor:= by
            simp only [Block.compatible, Bool.or_eq_true]
            exact Or.inl (Block.preceq_trans
              (h.voteAnchor (s + 1) (hslo.trans (Nat.le_succ s))
                hsuccHi w hw) hCD)
          path:= hfacts.2 }
    · intro w hw
      have hfrontier:= h.gateOff.confirmationFrontier s hslo hhi w hw
      have hgate:= h.gateOff.confirmationGateOff s hslo hhi w hw
      have hrootC:= h.aboveRoot.confirmation s hslo hslt w hw
      have hrootD: Block.Preceq (confRoot (confStore S rho w s)) D:=
        Block.preceq_trans hrootC hCD
      have hfacts:= seedRelayConfirmationFacts S adm hsb hpostS hhorS hcone
        hthin hw hfrontier hgate hrootD
      exact
        { candidate:= hfacts.1
          root:= hrootD
          anchor:= by
            simp only [Block.compatible, Bool.or_eq_true]
            exact Or.inl (Block.preceq_trans
              (h.confirmationAnchor s
                ((Nat.sub_le _ _).trans hslo) hslt w hw) hCD)
          path:= hfacts.2 }
  have hfold: ∀ s: Slot, S.hc.opening_slot q + 1 ≤ s →
      s ≤ seedRoundLastSlot S q →
      NamedHonestVotesCone S rho s (fun X => Block.Preceq D X):= by
    intro s hlo
    induction s, hlo using Nat.le_induction with
    | base => intro _; exact hconeSucc
    | succ s hlo ih =>
        intro hsuccHi
        have hshi: s ≤ seedRoundLastSlot S q - 1:=
          Nat.le_pred_of_lt
            (lt_of_lt_of_le (Nat.lt_succ_self s) hsuccHi)
        have hcone:= ih (hshi.trans (Nat.sub_le _ _))
        have hslo: S.hc.opening_slot q ≤ s:= (Nat.le_succ _).trans hlo
        have hsPos: 0 < s:= lt_of_lt_of_le hopenPos hslo
        have hpostS: S.E.t_GST ≤ Protocol.vote_time S.E s:=
          h.postOpeningVote.trans (Protocol.vote_time_mono_slots S.E hslo)
        have hhorS: Protocol.confirmation_time S.E s ≤ rho.horizon:=
          (confirmationTime_mono S.E hshi).trans h.roundConfirmationInHorizon
        have hinputs:= hstep s hlo hshi hcone
        exact seedHonestVotesCone_succ S adm hcom hsPos hpostS hhorS hcone
          (fun w hw => hinputs.vote w hw)
  refine ⟨hfold, ?_, ?_⟩
  · intro s hlo hhi
    exact hstep s hlo (Nat.le_pred_of_lt hhi)
      (hfold s hlo (Nat.le_of_lt hhi))
  intro s hlo hhi w hw E hE
  have hshi: s ≤ seedRoundLastSlot S q - 1:= Nat.le_pred_of_lt hhi
  have hcone:= hfold s hlo (hshi.trans (Nat.sub_le _ _))
  have hslo: S.hc.opening_slot q ≤ s:= (Nat.le_succ _).trans hlo
  have hsPos: 0 < s:= lt_of_lt_of_le hopenPos hslo
  have hpostS: S.E.t_GST ≤ Protocol.vote_time S.E s:=
    h.postOpeningVote.trans (Protocol.vote_time_mono_slots S.E hslo)
  have hhorS: Protocol.confirmation_time S.E s ≤ rho.horizon:=
    (confirmationTime_mono S.E hshi).trans h.roundConfirmationInHorizon
  have hinputs:= hstep s hlo hshi hcone
  exact goldfishCone_confirmation S adm hcom hsPos hpostS hhorS hcone hw
    (hinputs.confirmation w hw) hE

-/

/-! ## The successor frontier -/

/-- The actual confirmation value written immediately before the round action. -/
def roundCeilingOpeningOutput
    (S : Setup V) (rho : Run V) (q : Round) (v : V) : Block V :=
  (actionStoreAt S rho v q).live_confirmed

/-- The finite successor-frontier candidates: the previous ceiling and every
honest opening-confirmation output. -/
def roundCeilingFrontierCandidates
    (S : Setup V) (rho : Run V) (q : Round) (C : NamedBlock V) : Finset (Block V) :=
  insert C.erase (rho.honest.image (roundCeilingOpeningOutput S rho q))

/-- The deepest successor frontier and its useful projections. -/
structure RoundCeilingFrontierAt
    (S : Setup V) (rho : Run V) (q : Round)
    (C Cstar : NamedBlock V) : Prop where
  selected : Block.deepest? (roundCeilingFrontierCandidates S rho q C) =
    some Cstar.erase
  run : RunBlock S rho Cstar
  oldPreceq : Block.Preceq C.erase Cstar.erase
  outputsPreceq : ∀ v ∈ rho.honest,
    Block.Preceq (roundCeilingOpeningOutput S rho q v) Cstar.erase
  source : Cstar = C ∨ ∃ v ∈ rho.honest,
    roundCeilingOpeningOutput S rho q v = Cstar.erase

/-- An honest opening output is either a genuine extension of the previous ceiling
or an FG-root fallback below it. -/
theorem roundCeiling_openingOutput_genuine_or_preceq
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {M : Height} {q : Round} {C : NamedBlock V}
    (h : RoundCeilingAt S rho M q C)
    {v : V} (hv : v ∈ rho.honest) :
    (GenuineConfirmationWith
        (NamedProfile.gradeContract
          (Internal.NamedRecoveryRead.confirmationInputRead S rho v
            (S.hc.opening_slot q)).cache)
        S.E S.hc (confStore S rho v (S.hc.opening_slot q))
          (S.hc.opening_slot q) (roundCeilingOpeningOutput S rho q v) ∧
      Block.Preceq C.erase (roundCeilingOpeningOutput S rho q v)) ∨
    Block.Preceq (roundCeilingOpeningOutput S rho q v) C.erase := by
  rcases actionStoreAt_liveConfirmed_genuine_or_fgRoot S rho v q with
    hgenuine | hroot
  · obtain ⟨D, hD, hDeq⟩ := hgenuine
    left
    have hout : roundCeilingOpeningOutput S rho q v = D := by
      simpa only [roundCeilingOpeningOutput] using hDeq.symm
    have hDinput : GenuineConfirmationWith
        (NamedProfile.gradeContract
          (Internal.NamedRecoveryRead.confirmationInputRead S rho v
            (S.hc.opening_slot q)).cache)
        S.E S.hc (confStore S rho v (S.hc.opening_slot q))
          (S.hc.opening_slot q) D := by
      simpa only [Internal.NamedRecoveryRead.confirmationInputRead,
        Setup.a, Protocol.a_eq_confirmation_time] using hD
    have hDout : GenuineConfirmationWith
        (NamedProfile.gradeContract
          (Internal.NamedRecoveryRead.confirmationInputRead S rho v
            (S.hc.opening_slot q)).cache)
        S.E S.hc (confStore S rho v (S.hc.opening_slot q))
          (S.hc.opening_slot q) (roundCeilingOpeningOutput S rho q v) := by
      rw [hout]
      exact hDinput
    exact ⟨hDout,
      roundCeiling_openingConfirmation S adm hcom h hv hDout⟩
  · obtain ⟨R, hReq, hReeq⟩ := hroot
    right
    have hout : roundCeilingOpeningOutput S rho q v = R := by
      simpa only [roundCeilingOpeningOutput] using hReeq.symm
    rw [hout, hReq]
    have hrootAnchor : Block.Preceq
        (Protocol.get_fg_root
          (confStore S rho v (S.hc.opening_slot q)).toHealing.toFG)
        (confirmationAnchorAt S rho v (S.hc.opening_slot q)) := by
      simpa only [confirmationAnchorAt, namedConfirmationAnchor,
        Internal.NamedRecoveryRead.confirmationInputRead,
        confStore, tickStore, Protocol.NamedStore.setClock] using
        fg_root_preceq_get_sg_root_with_frame
          (Internal.NamedRecoveryRead.confirmationInputRead S rho v
            (S.hc.opening_slot q)).cache S.E S.hc
          (confStore S rho v (S.hc.opening_slot q)).toHealing
          (S.hc.round_of (confStore S rho v
            (S.hc.opening_slot q)).s)
    exact Block.preceq_trans hrootAnchor
      (h.confirmationAnchor (S.hc.opening_slot q) (Nat.sub_le _ _)
        (openingSlot_lt_seedRoundLastSlot S q) v hv)

private theorem roundCeiling_frontierCandidates_compatible
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {M : Height} {q : Round} {C : NamedBlock V}
    (h : RoundCeilingAt S rho M q C) :
    ∀ X ∈ roundCeilingFrontierCandidates S rho q C,
      ∀ Y ∈ roundCeilingFrontierCandidates S rho q C,
        Block.compatible X Y = true := by
  intro X hX Y hY
  simp only [roundCeilingFrontierCandidates, Finset.mem_insert,
    Finset.mem_image] at hX hY
  rcases hX with hXC | hX
  · subst X
    rcases hY with hYC | hY
    · subst Y
      exact Block.compatible_of_preceq_common
        (Block.preceq_self C.erase) (Block.preceq_self C.erase)
    · obtain ⟨v, hv, hvY⟩ := hY
      subst Y
      rcases roundCeiling_openingOutput_genuine_or_preceq
          S adm hcom h hv with hgen | hbelow
      · simp only [Block.compatible, Bool.or_eq_true]
        exact Or.inl hgen.2
      · simp only [Block.compatible, Bool.or_eq_true]
        exact Or.inr hbelow
  · obtain ⟨v, hv, hvX⟩ := hX
    subst X
    rcases hY with hYC | hY
    · subst Y
      exact Protocol.compatible_comm (by
        rcases roundCeiling_openingOutput_genuine_or_preceq
            S adm hcom h hv with hgen | hbelow
        · simp only [Block.compatible, Bool.or_eq_true]
          exact Or.inl hgen.2
        · simp only [Block.compatible, Bool.or_eq_true]
          exact Or.inr hbelow)
    · obtain ⟨w, hw, hwY⟩ := hY
      subst Y
      rcases roundCeiling_openingOutput_genuine_or_preceq
          S adm hcom h hv with hvGen | hvBelow
      · rcases roundCeiling_openingOutput_genuine_or_preceq
            S adm hcom h hw with hwGen | hwBelow
        · exact roundCeiling_openingConfirmationsCompatible
            S adm h hv hw hvGen.1 hwGen.1
        · simp only [Block.compatible, Bool.or_eq_true]
          exact Or.inr (Block.preceq_trans hwBelow hvGen.2)
      · rcases roundCeiling_openingOutput_genuine_or_preceq
            S adm hcom h hw with hwGen | hwBelow
        · simp only [Block.compatible, Bool.or_eq_true]
          exact Or.inl (Block.preceq_trans hvBelow hwGen.2)
        · exact Block.compatible_of_preceq_common hvBelow hwBelow

/-- A deepest successor frontier always exists. It dominates the previous ceiling
and every honest opening output. -/
theorem roundCeiling_existsFrontier
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {M : Height} {q : Round} {C : NamedBlock V}
    (h : RoundCeilingAt S rho M q C) :
    ∃ Cstar : NamedBlock V, RoundCeilingFrontierAt S rho q C Cstar := by
  let candidates := roundCeilingFrontierCandidates S rho q C
  have hcompatible : ∀ X ∈ candidates, ∀ Y ∈ candidates,
      Block.compatible X Y = true := by
    simpa only [candidates] using
      roundCeiling_frontierCandidates_compatible S adm hcom h
  have hnonempty : candidates.Nonempty := by
    exact ⟨C.erase, by simp only [candidates, roundCeilingFrontierCandidates,
      Finset.mem_insert, true_or]⟩
  obtain ⟨CstarRaw, hselected⟩ := Option.isSome_iff_exists.mp
    (deepest?_isSome_of_compatible hcompatible hnonempty)
  have hstarMem : CstarRaw ∈ candidates := Proofs.Engine.deepest?_mem hselected
  have holdMem : C.erase ∈ candidates := by
    simp only [candidates, roundCeilingFrontierCandidates,
      Finset.mem_insert, true_or]
  have hold : Block.Preceq C.erase CstarRaw :=
    deepest?_dominates hselected holdMem
      (hcompatible C.erase holdMem CstarRaw hstarMem)
  have hsource : CstarRaw = C.erase ∨ ∃ v ∈ rho.honest,
      roundCeilingOpeningOutput S rho q v = CstarRaw := by
    simpa only [candidates, roundCeilingFrontierCandidates,
      Finset.mem_insert, Finset.mem_image] using hstarMem
  rcases hsource with hOld | ⟨v, hv, hout⟩
  · subst CstarRaw
    refine ⟨C, ?_⟩
    refine {
      selected := hselected
      run := h.run
      oldPreceq := hold
      outputsPreceq := ?_
      source := Or.inl rfl }
    intro w hw
    have houtMem : roundCeilingOpeningOutput S rho q w ∈ candidates := by
      simp only [candidates, roundCeilingFrontierCandidates,
        Finset.mem_insert, Finset.mem_image]
      exact Or.inr ⟨w, hw, rfl⟩
    exact deepest?_dominates hselected houtMem
      (hcompatible _ houtMem C.erase hstarMem)
  · by_cases hEq : CstarRaw = C.erase
    ·
      refine ⟨C, ?_⟩
      have hselectedOld : Block.deepest?
          (roundCeilingFrontierCandidates S rho q C) = some C.erase := by
        exact hselected.trans (congrArg some hEq)
      have hstarMemOld : C.erase ∈ candidates := by
        have hmem := hstarMem
        rw [hEq] at hmem
        exact hmem
      have holdOld : Block.Preceq C.erase C.erase := by
        simpa only [hEq] using hold
      refine {
        selected := hselectedOld
        run := h.run
        oldPreceq := holdOld
        outputsPreceq := ?_
        source := Or.inl rfl }
      intro w hw
      have houtMem : roundCeilingOpeningOutput S rho q w ∈ candidates := by
        simp only [candidates, roundCeilingFrontierCandidates,
          Finset.mem_insert, Finset.mem_image]
        exact Or.inr ⟨w, hw, rfl⟩
      exact deepest?_dominates hselectedOld houtMem
        (hcompatible _ houtMem C.erase hstarMemOld)
    · rcases roundCeiling_openingOutput_genuine_or_preceq
        S adm hcom h hv with hgen | hroot
      · obtain ⟨Cstar, hCerase, hCrun⟩ := h.genuineRun v hv
          (roundCeilingOpeningOutput S rho q v) hgen.1
        refine ⟨Cstar, ?_⟩
        have hselected' : Block.deepest?
            (roundCeilingFrontierCandidates S rho q C) = some Cstar.erase := by
          exact hselected.trans (congrArg some (hout.symm.trans hCerase.symm))
        have hold' : Block.Preceq C.erase Cstar.erase := by
          rw [hCerase, hout]
          exact hold
        have houtputs : ∀ w ∈ rho.honest,
            Block.Preceq (roundCeilingOpeningOutput S rho q w) Cstar.erase := by
          intro w hw
          have hwMem : roundCeilingOpeningOutput S rho q w ∈ candidates := by
            simp only [candidates, roundCeilingFrontierCandidates,
              Finset.mem_insert, Finset.mem_image]
            exact Or.inr ⟨w, hw, rfl⟩
          have hwBound := deepest?_dominates hselected hwMem
            (hcompatible _ hwMem CstarRaw hstarMem)
          rw [hCerase, hout]
          exact hwBound
        exact {
          selected := hselected'
          run := hCrun
          oldPreceq := hold'
          outputsPreceq := houtputs
          source := Or.inr ⟨v, hv, hCerase.symm⟩ }
      · have hroot' : Block.Preceq CstarRaw C.erase := by
          simpa only [hout] using hroot
        exact (hEq (Block.preceq_antisymm hroot' hold)).elim

/-- If the selected successor frontier is not the previous ceiling, it is an
actual genuine honest opening confirmation. -/
theorem RoundCeilingFrontierAt.genuine_of_ne
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {M : Height} {q : Round} {C Cstar : NamedBlock V}
    (h : RoundCeilingAt S rho M q C)
    (hfrontier : RoundCeilingFrontierAt S rho q C Cstar)
    (hne : Cstar ≠ C) :
    ∃ v ∈ rho.honest,
      GenuineConfirmationWith
        (NamedProfile.gradeContract
          (Internal.NamedRecoveryRead.confirmationInputRead S rho v
            (S.hc.opening_slot q)).cache)
        S.E S.hc (confStore S rho v (S.hc.opening_slot q))
          (S.hc.opening_slot q) Cstar.erase := by
  rcases hfrontier.source with hEq | hout
  · exact (hne hEq).elim
  · obtain ⟨v, hv, hvstar⟩ := hout
    refine ⟨v, hv, ?_⟩
    rcases roundCeiling_openingOutput_genuine_or_preceq
        S adm hcom h hv with hgen | hbelow
    · simpa only [hvstar] using hgen.1
    · have hstarC : Block.Preceq Cstar.erase C.erase := by
        simpa only [hvstar] using hbelow
      have hEqRaw : Cstar.erase = C.erase :=
        Block.preceq_antisymm hstarC hfrontier.oldPreceq
      have hrootEq : Cstar.root = C.root := by
        rw [← Proofs.NamedWire.erase_root Cstar, ← Proofs.NamedWire.erase_root C, hEqRaw]
      have hEq : Cstar = C :=
        adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
          Cstar C hfrontier.run h.run Cstar C
          (Or.inl (Proofs.NamedAncestry.named_self Cstar))
          (Or.inr (Proofs.NamedAncestry.named_self C)) hrootEq
      exact (hne hEq).elim

/- The previous public action-carrier goal remains below. Its prepared Q2-to-anchor
producer needs an admissibility/runtime premise that the original statement
does not carry.
/-- Every honest action SG carrier is below the selected successor frontier.
The proof covers all three selector tiers. It does not assume that a selected
grade-2 block exists. -/
theorem roundCeiling_actionCarriersBelowFrontier
    (S: Setup V) {rho: Run V}
    {M: Height} {q: Round} {C Cstar: NamedBlock V}
    (h: RoundCeilingAt S rho M q C)
    (hfrontier: RoundCeilingFrontierAt S rho q C Cstar):
    ∀ v ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho v q) Cstar.erase:= by
  intro v hv
  set n:= actionReadAt S rho v q with hn
  set ast:= n.st.core.toHealing with hast
  set grades:= DecoupledConsensusModel.Protocol.frameGradeRead n.cache S.E S.hc ast q
    with hgrades
  have hround: S.hc.round_of ast.s = q:=
    Proofs.HealingLemmas.round_of_slotOf_a S q
  have hlive: Block.Preceq ast.live_confirmed Cstar.erase:= by
    have hout:= hfrontier.outputsPreceq v hv
    simpa only [roundCeilingOpeningOutput, actionStoreAt, actionReadAt,
      n, ast] using hout
  have hroot: Block.Preceq (PhaseGrades.nodeAnchor S n q) Cstar.erase:= by
    simpa only [Internal.NamedRecoveryRead.actionDutyRead] using h.actionAnchor v hv
  have hroot': Block.Preceq grades.anchor Cstar.erase:= by
    simpa only [PhaseGrades.nodeAnchor, PhaseGrades.nodeRead,
      n, ast, grades, hgrades] using hroot
  have hsg: actionSGBlockAt S rho v q = Protocol.currentSGVote ast grades:= by
    show Protocol.get_sg_vote_with (NamedProfile.gradeContract n.cache) S.E S.hc ast
        (S.hc.round_of ast.s)
        (Protocol.grade2_block_with (NamedProfile.gradeContract n.cache) S.E S.hc ast
          (S.hc.round_of ast.s)) = Protocol.currentSGVote ast grades
    rw [hround]
    rfl
  rw [hsg]
  unfold Protocol.currentSGVote
  cases hclear: Protocol.deepest_clear (some grades.anchor) ast.live_confirmed
      grades.clear with
  | some B =>
      exact Block.preceq_trans (Proofs.Engine.deepest_clear_preceq hclear) hroot'
  | none =>
      cases hgrade: grades.Q2 with
      | some Q =>
          have hQ2: PhaseGrades.nodeQ2 S n q = some Q:= by
            simpa only [PhaseGrades.nodeQ2, PhaseGrades.nodeRead,
              grades, hgrades] using hgrade
          have hactionHor: S.a q ≤ rho.horizon:= by
            rw [Setup.a, Protocol.a_eq_confirmation_time]
            exact (confirmationTime_mono S.E
              (openingSlot_le_seedRoundLastSlot_pred S q)).trans
              h.roundConfirmationInHorizon
          have hQA:= actionQ2_preceq_actionAnchor S
            adm.toNamedAdmissibleCore hv h.roundPositive hactionHor hQ2
          have hQA': Block.Preceq Q grades.anchor:= by
            simpa only [PhaseGrades.nodeAnchor, PhaseGrades.nodeRead,
              n, ast, grades, hgrades] using hQA
          simp only [hclear, hgrade]
          exact Block.preceq_trans hQA' hroot'
      | none =>
          by_cases hraw: grades.rawG2
          · have hFGanchor: Block.Preceq
                (Protocol.get_fg_root ast.toFG) grades.anchor:= by
              simpa only [PhaseGrades.nodeAnchor, PhaseGrades.nodeRead,
                n, ast, grades, hgrades] using
                fg_root_preceq_get_sg_root_with_frame n.cache S.E S.hc ast q
            simp only [hclear, hgrade, hraw]
            exact Block.preceq_trans hFGanchor hroot'
          · simp only [hclear, hgrade, hraw]
            exact hroot'
-/





/-! ## Proposal transfer through the common ceiling -/

/-- A current-slot full filtered candidate is also in the frozen voter tree.
The only possible processed descendant is the current-slot block itself. -/
private theorem seedCeiling_currentSlot_voterCandidate_of_filtered
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} {s : Slot} {B : Block V}
    (hslot : B.slot = s)
    (hB : B ∈ Protocol.get_filtered_block_tree
      (voteDutyStore S rho v s).toHealing.toFG) :
    B ∈ voter_candidate_tree S.E
      (voteDutyStore S rho v s).toHealing := by
  let duty := voteDutyStore S rho v s
  have hdata := hB
  simp only [Protocol.get_filtered_block_tree,
    Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq] at hdata
  obtain ⟨⟨⟨hBT, hFB⟩, W, hWT, hBW, hheight⟩, hroot⟩ := hdata
  have hWB : W = B :=
    Protocol.voteDutyStore_terminal_of_preceq
      S adm (v := v) (s := s) hslot hWT hBW
  subst W
  have hprocessed : B ∈ Protocol.voter_processed_block_tree
      S.E duty.toHealing.toFG.toSG.toGoldfishStore duty.toHealing.s := by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    refine ⟨hBT, Or.inr ⟨B, ?_, Block.preceq_self B⟩⟩
    refine ⟨hBT, ?_⟩
    simpa only [duty, Proofs.Optimistic.toHealing_slot,
      Proofs.Optimistic.voteDutyStore_slot] using hslot
  simp only [voter_candidate_tree,
    Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq]
  exact ⟨⟨⟨hprocessed, hFB⟩, B, hprocessed,
    Block.preceq_self B, hheight⟩, hroot⟩



/-! ## The proposer-side cone step at the prepared opening read -/

/-- The opening proposal read carries its own round. -/
private theorem seedCeiling_proposerRead_round
    (S : Setup V) (rho : Run V) (q : Round) :
    S.hc.round_of
        (Internal.NamedRecoveryRead.proposalDutyRead S rho
          (S.hc.opening_slot q)).st.core.s = q := by
  simpa only [Internal.NamedRecoveryRead.proposalDutyRead, proposerReadAt,
    NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
    Proofs.Optimistic.slotOf_proposal_time] using round_of_opening_slot_eq S.hc q

/-- The preceding honest named vote cone becomes `ConeSupport` in the next
honest proposer's prepared raw and resolved proposal views.

restated from `FixedHeightRootOpeningParentRun.fixedRoot_preparedProposalConeSupport_of_namedCone`,
which is downstream of this module; the proof uses only facts below it. -/
private theorem seedProposerConeSupport_of_namedCone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) {s : Slot}
    (hs : 0 < s) (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.support_cutoff S.E s ≤ rho.horizon)
    (hprop : S.E.proposer (s + 1) ∈ rho.honest) {T : Block V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.proposalDutyRead S rho (s + 1)).st.core.toHealing.toFG) T)
    (hnames : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq T X)) :
    Proofs.Optimistic.ConeSupport S.E
      (Internal.NamedRecoveryRead.proposalDutyRead S rho (s + 1)).st.core.T
      (Protocol.proposer_view
        (Internal.NamedRecoveryRead.proposalDutyRead S rho (s + 1)).st.core.toHealing.toFG.toSG.toGoldfishStore
        (Internal.NamedRecoveryRead.proposalDutyRead S rho (s + 1)).st.core.s).toFinset
      (Protocol.proposer_support_view
        (Internal.NamedRecoveryRead.proposalDutyRead S rho (s + 1)).st.core.toHealing.toFG.toSG.toGoldfishStore
        (Internal.NamedRecoveryRead.proposalDutyRead S rho (s + 1)).st.core.s).toFinset
      (Protocol.proposer_view
        (Internal.NamedRecoveryRead.proposalDutyRead S rho (s + 1)).st.core.toHealing.toFG.toSG.toGoldfishStore
        (Internal.NamedRecoveryRead.proposalDutyRead S rho (s + 1)).st.core.s).toFinset
      ((Internal.NamedRecoveryRead.proposalDutyRead S rho (s + 1)).st.core.s - 1) rho.honest
      (fun X => Block.Preceq T X) := by
  let n := Internal.NamedRecoveryRead.proposalDutyRead S rho (s + 1)
  let st := n.st.core
  let raw := (Protocol.proposer_view st.toHealing.toFG.toSG.toGoldfishStore st.s).toFinset
  let support :=
    (Protocol.proposer_support_view st.toHealing.toFG.toSG.toGoldfishStore st.s).toFinset
  have hslot : st.s = s + 1 := by
    simpa only [st, n, Internal.NamedRecoveryRead.proposalDutyRead, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      (Proofs.Optimistic.slotOf_proposal_time S.E (s + 1))
  have hprev : st.s - 1 = s := by
    rw [hslot]
    exact Nat.add_sub_cancel s 1
  have hrootDuty : Block.Preceq
      (Protocol.get_fg_root
        (Protocol.proposerDutyStore S rho (s + 1)).toHealing.toFG) T := by
    simpa only [Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
      Internal.NamedRecoveryRead.proposalDutyRead, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      hroot
  have hresolve0 := Protocol.headsResolveIn_proposerDutyStore_of_postHealingCone
    S adm hpost hhor hprop hrootDuty hnames
  have hresolve : Proofs.Optimistic.HeadsResolveIn S rho s st.T st.timestamp_block := by
    simpa only [st, n, Internal.NamedRecoveryRead.proposalDutyRead, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Protocol.proposerDutyStore, Proofs.Optimistic.tickStore] using hresolve0
  have hss : support ⊆ raw := by
    intro u hu
    simp only [support, raw, Protocol.proposer_support_view,
      Protocol.proposer_view, List.mem_toFinset, List.mem_filter] at hu ⊢
    exact hu.1
  obtain ⟨m, hm, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (Protocol.proposal_time S.E (s + 1))
  have hgf : st.gf_votes =
      (rho.stateBefore S m (S.E.proposer (s + 1))).st.core.gf_votes := by
    dsimp only [st, n, Internal.NamedRecoveryRead.proposalDutyRead, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
    exact congrArg (fun z =>
      (z (S.E.proposer (s + 1))).st.core.gf_votes) hm
  have hgfTime : st.gf_votes =
      (NamedRun.stateBeforeTime S rho (Protocol.proposal_time S.E (s + 1))
        (S.E.proposer (s + 1))).st.core.gf_votes := by
    rfl
  have hne : ∀ x ∈ S.E.committee s, x ∈ rho.honest →
      Protocol.equivocates raw x = false := by
    intro x _ hx
    have hno := Proofs.Optimistic.pool_no_honest_equivocation S adm
      (S.E.proposer (s + 1)) m s hx
    simpa only [raw, Protocol.proposer_view, hprev, hgf,
      Protocol.NamedStore.setClock, Protocol.NamedStore.pool,
      Protocol.Store.pool, Protocol.Store.toHealing, List.toFinset] using hno
  have hvote : ∀ x ∈ S.E.committee s, x ∈ rho.honest →
      ∃ X : Block V, Block.Preceq T X ∧
        X.slot ≤ s ∧
        (⟨x, s, X.root⟩ : GoldfishVote V) ∈ support ∧
        Block.find? st.T X.root = some X := by
    intro x hxCommittee hxHonest
    obtain ⟨X, hX, hXrun, hXemit⟩ := hnames x hxHonest hxCommittee
    have hhead : Proofs.Optimistic.HonestHead S rho s X.erase :=
      ⟨x, hxHonest, hxCommittee, ⟨X, rfl, hXrun⟩, hXemit⟩
    obtain ⟨hfind, -⟩ := hresolve X.erase hhead
    have hcut := Protocol.gfVote_in_cutoff_view_after_gst
      S adm.toNamedAdmissibleCore hxHonest hs hpost hXemit rfl hprop
      (Protocol.proposal_time S.E (s + 1))
      (Protocol.proposal_time S.E (s + 1))
      (Protocol.support_cutoff_le_proposal_time_succ S.E s)
      (Protocol.support_cutoff_le_proposal_time_succ S.E s) hhor
    have hcut' := hcut
    rw [beforeCutoff, Finset.mem_filter] at hcut'
    have hpool := hcut'.1
    have hpool' : (⟨x, s, X.erase.root⟩ : GoldfishVote V) ∈
        (NamedRun.stateBeforeTime S rho
          (Protocol.proposal_time S.E (s + 1))
          (S.E.proposer (s + 1))).st.core.gf_votes s := by
      simpa only [Run.storeBeforeTime, Protocol.Store.pool,
        List.mem_toFinset] using hpool
    have hraw : (⟨x, s, X.erase.root⟩ : GoldfishVote V) ∈ raw := by
      dsimp only [raw]
      change (⟨x, s, X.erase.root⟩ : GoldfishVote V) ∈
        (st.gf_votes (st.s - 1)).toFinset
      rw [hprev, hgfTime]
      exact List.mem_toFinset.mpr hpool'
    have hfind' : Block.find? st.toHealing.T
        (⟨x, s, X.erase.root⟩ : GoldfishVote V).head = some X.erase := by
      simpa only [st, n] using hfind
    have hXmem : X.erase ∈
        (rho.storeBeforeTime S (S.E.proposer (s + 1))
          (Protocol.proposal_time S.E (s + 1))).T := by
      simpa only [st, n, Internal.NamedRecoveryRead.proposalDutyRead,
        Statements.Instantiation.proposerReadAt,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
        (Proofs.HealingLemmas.find?_mem hfind)
    have hXslot : X.erase.slot ≤ s :=
      Proofs.Optimistic.emitted_vote_head_slot_le_of_store_mem S
        adm.toNamedAdmissibleCore hxHonest hprop hXemit rfl hXmem (by rfl)
    have hsupport : (⟨x, s, X.erase.root⟩ : GoldfishVote V) ∈ support := by
      simp only [support, Protocol.proposer_support_view,
        List.mem_toFinset, List.mem_filter, hprev]
      refine ⟨?_, ?_⟩
      · simpa only [Protocol.proposer_view, hprev,
          Protocol.Store.toHealing] using List.mem_toFinset.mp hraw
      · change decide (Protocol.resolved st.toHealing.T
          (⟨x, s, X.erase.root⟩ : GoldfishVote V) = true) = true
        simp [Protocol.resolved, hfind', hXslot]
    exact ⟨X.erase, hX, hXslot, hsupport, hfind⟩
  have hcone := Proofs.Optimistic.coneSupport_of_named_votes (E := S.E) (T := st.T)
    (votes := raw) (support := support) (late := raw) (s := s)
    (Hon := rho.honest) (tgt := fun X => Block.Preceq T X)
    (hcom s) (subset_refl _) hss hne hvote
  simpa only [raw, support, st, n, hslot, hprev] using hcone


/-- A post-GST honest named vote cone whose target is active in the opening
proposal read is captured by that proposal's canonical parent.

This is the named twin of `SGProposalLifecycleRun.coneTarget_preceq_nextProposedParent`
(blocked on the selection): same premises, with `NamedHonestVotesCone` for the
cone, the prepared contract anchor for the compatibility premise, and the
prepared `get_head_in_tree_with` split for the walk's endpoint. -/
theorem coneTarget_preceq_nextProposedParent_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.support_cutoff S.E s ≤ rho.horizon)
    (hprop : S.E.proposer (s + 1) ∈ rho.honest)
    {T : Block V}
    (hcone : NamedHonestVotesCone S rho s (fun X => Block.Preceq T X))
    (hactive : T ∈ Protocol.get_filtered_block_tree
      (Protocol.proposerDutyStore S rho (s + 1)).toHealing.toFG)
    (hcompat : Block.compatible
      (PhaseGrades.nodeAnchor S
        (Internal.NamedRecoveryRead.proposalDutyRead S rho (s + 1))
        (S.hc.round_of
          (Internal.NamedRecoveryRead.proposalDutyRead S rho (s + 1)).st.core.s))
      T = true) :
    Block.Preceq T (proposedParent S rho (s + 1)) := by
  let n := Internal.NamedRecoveryRead.proposalDutyRead S rho (s + 1)
  let st := n.st.core
  let gc := NamedProfile.gradeContract n.cache
  let tree := Protocol.get_filtered_block_tree st.toHealing.toFG
  let votes := (Protocol.proposer_view st.toHealing.toFG.toSG.toGoldfishStore st.s).toFinset
  let support :=
    (Protocol.proposer_support_view st.toHealing.toFG.toSG.toGoldfishStore st.s).toFinset
  have hactive' : T ∈ tree := by
    simpa only [tree, st, n, Internal.NamedRecoveryRead.proposalDutyRead,
      proposerReadAt, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Protocol.proposerDutyStore, Proofs.Optimistic.tickStore] using hactive
  have hroot : Block.Preceq (Protocol.get_fg_root st.toHealing.toFG) T :=
    Proofs.Records.preceq_get_fg_root_of_mem_filtered hactive'
  have hsupport := seedProposerConeSupport_of_namedCone S adm hcom hs hpost
    hhor hprop (by simpa only [st, n] using hroot) hcone
  have hcone' : Proofs.Optimistic.ConeSupport S.E st.T votes support votes
      (st.s - 1) rho.honest (fun X => Block.Preceq T X) := by
    simpa only [st, n, votes, support] using hsupport
  have hvalid : Protocol.VoteSetValid S.E (st.s - 1) votes := by
    simpa only [st, n, votes, Internal.NamedRecoveryRead.proposalDutyRead,
      proposerReadAt, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Protocol.proposerDutyStore, Proofs.Optimistic.tickStore] using
      Protocol.proposerDutyStore_proposer_view_valid S adm (s + 1)
  have hpc : ParentClosed st := by
    have hpc0 := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
      (Protocol.proposal_time S.E (s + 1)) (S.E.proposer (s + 1))
    change ParentClosed st at hpc0
    exact hpc0
  have hFJ : Block.Preceq st.F st.J :=
    Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
      (Protocol.proposal_time S.E (s + 1)) (S.E.proposer (s + 1))
  have hTT : T ∈ st.T :=
    Proofs.Records.get_filtered_block_tree_subset _ hactive'
  have hpath : ∀ C : Block V,
      Block.Preceq (Protocol.get_sg_root_with gc S.E S.hc st.toHealing
        (S.hc.round_of st.s)) C →
      C ≠ Protocol.get_sg_root_with gc S.E S.hc st.toHealing
        (S.hc.round_of st.s) →
      Block.Preceq C T → C ∈ tree := by
    intro C hAC _ hCT
    have hCmem : C ∈ st.T :=
      Proofs.Records.mem_of_preceq ((parentClosed_iff st).mp hpc).2 C T hTT hCT
    have hfgsg := fg_root_preceq_get_sg_root_with_frame
      n.cache S.E S.hc st.toHealing (S.hc.round_of st.s)
    have hrootC : Block.Preceq
        (Protocol.get_fg_root st.toHealing.toFG) C :=
      Block.preceq_trans hfgsg hAC
    exact Proofs.Records.mem_filtered_of_preceq hFJ hactive' hCmem hCT hrootC
  have hhead := Protocol.goldfish_fork_choice_captures_supporter_majority
    S.E st.σ st.h_max st.T tree st.s votes support (st.s - 1)
    (Proofs.Optimistic.ConeSupport.sub hcone')
    (Protocol.supporterMajority_of_cone S.E hcone' hvalid)
    hcompat (fun _ => hpath)
  have hfinal : Block.Preceq T
      (Protocol.get_head_with gc S.E S.hc st.toHealing votes support
        (st.s - 1)) := by
    rw [show Protocol.get_head_with gc S.E S.hc st.toHealing votes support
          (st.s - 1) =
        Protocol.get_head_in_tree_with_layer gc S.E S.hc st.toHealing tree votes
          support (st.s - 1) from rfl,
      Proofs.Optimistic.get_head_in_tree_split_with]
    simpa only [tree, votes, support] using hhead
  simpa only [proposedParent, proposalInputAt,
    Internal.NamedRecoveryRead.proposalDutyRead, n, st, gc, tree, votes, support,
    DutyInputDefaults.proposal_input_parent] using hfinal

/-! ## Common-ceiling opening alignment -/

/-- The erased named proposal records the shared proposal parent. -/
private theorem seedCeiling_erase_parent
    (S : Setup V) (rho : Run V) (s : Slot) {P : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P) :
    P.erase.parent? = some (proposedParent S rho s) := by
  obtain ⟨p, hp, hparent⟩ := proposedBlockAt_parent S rho s hP
  rw [← hparent]
  cases P with
  | genesis => simp only [NamedBlock.parent?, reduceCtorEq] at hp
  | node parent slot root votes support rows proposer =>
      simp only [NamedBlock.parent?, Option.some.injEq] at hp
      subst hp
      rfl

/-- The named proposal parent is above its own named proposal's parent
reading. -/
private theorem seedCeiling_proposedParent_preceq
    (S : Setup V) (rho : Run V) (s : Slot) {P : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P) :
    Block.Preceq (proposedParent S rho s) P.erase :=
  Protocol.preceq_of_parent? (seedCeiling_erase_parent S rho s hP)

/-- The alignment facts that remain after removing the unnecessary directional
ordering between the proposal and vote anchors. Both prepared anchors are
below the same ceiling, and the ceiling is below the proposal parent. The
proposal walk can therefore use the ceiling itself as its frozen pivot. -/
structure OpeningCeilingAlignedAt
    (S : Setup V) (rho : Run V) (q : Round) (C : Block V) : Prop where
  sourceBelowCeiling : Block.Preceq
    (PhaseGrades.nodeAnchor S
      (Internal.NamedRecoveryRead.proposalDutyRead S rho
        (S.hc.opening_slot q)) q) C
  voteBelowCeiling : ∀ v ∈ rho.honest,
    Block.Preceq (voterAnchorAt S rho v (S.hc.opening_slot q)) C
  ceilingBelowParent : Block.Preceq C
    (proposedParent S rho (S.hc.opening_slot q))
  confirmationBelowProposal : ∀ v ∈ rho.honest,
    ∀ P : NamedBlock V,
      proposedBlockAt S rho (S.hc.opening_slot q) = some P →
      Block.Preceq (confirmationAnchorAt S rho v (S.hc.opening_slot q))
        P.erase
  previousCarriersBelowParent : ∀ v ∈ rho.honest,
    Block.Preceq (actionSGBlockAt S rho v (q - 1))
      (proposedParent S rho (S.hc.opening_slot q))

/-- A round ceiling gives common-ceiling opening alignment. The proposal
parent comes from the preceding honest named vote cone; no
proposal-anchor-to-vote-anchor ordering is assumed.

The cone step at the proposer's prepared read is
`coneTarget_preceq_nextProposedParent_named` above. -/
theorem openingAnchorsAligned_of_roundCeiling
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {M : Height} {q : Round} {C : NamedBlock V}
    (hcarrier : ProposerCarrierAt S rho q)
    (h : RoundCeilingAt S rho M q C) :
    OpeningCeilingAlignedAt S rho q C.erase := by
  have hsourceAnchor := h.proposerAnchorCeiling hcarrier.1
  have hpriorSucc : S.hc.opening_slot q - 1 + 1 = S.hc.opening_slot q :=
    openingSlot_pred_succ S h.roundPositive
  have hpriorPos : 0 < S.hc.opening_slot q - 1 := by
    unfold Protocol.HealConfig.opening_slot
    have hR : 2 ≤ S.hc.R := S.hc.R_ge_two
    have hqOne : 1 ≤ q := Nat.succ_le_iff.mpr h.roundPositive
    have hopenTwo : 2 ≤ q * S.hc.R := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul hqOne hR
    exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_sub_of_add_le hopenTwo)
  have hsupportHor : Protocol.support_cutoff S.E
      (S.hc.opening_slot q - 1) ≤ rho.horizon :=
    (Protocol.support_cutoff_le_confirmation_time S.E _).trans
      h.previousConfirmationInHorizon
  have hparent : Block.Preceq C.erase
      (proposedParent S rho (S.hc.opening_slot q)) := by
    have hout := coneTarget_preceq_nextProposedParent_named S adm hcom
      (s := S.hc.opening_slot q - 1) hpriorPos h.postPreviousVote hsupportHor
      (by rw [hpriorSucc]; exact hcarrier.1) h.lastVotes
      (by rw [hpriorSucc]; exact h.proposerActive hcarrier.1)
      (by
        rw [hpriorSucc, seedCeiling_proposerRead_round S rho q]
        exact Block.compatible_of_preceq_common hsourceAnchor
          (Block.preceq_self C.erase))
    simpa only [hpriorSucc] using hout
  exact
    { sourceBelowCeiling := hsourceAnchor
      voteBelowCeiling := by
        intro v hv
        exact h.voteAnchor (S.hc.opening_slot q) (le_refl _)
          (Nat.le_of_lt (openingSlot_lt_seedRoundLastSlot S q)) v hv
      ceilingBelowParent := hparent
      confirmationBelowProposal := by
        intro v hv P hP
        exact Block.preceq_trans
          (h.confirmationAnchor (S.hc.opening_slot q) (Nat.sub_le _ _)
            (openingSlot_lt_seedRoundLastSlot S q) v hv)
          (Block.preceq_trans hparent
            (seedCeiling_proposedParent_preceq S rho _ hP))
      previousCarriersBelowParent := by
        intro v hv
        exact Block.preceq_trans (h.previousCarriers v hv) hparent }

/-- The preceding honest named vote cone makes the proposal-free voter walk
pass through the common ceiling. The named proposal is erased from this walk;
every block on the anchor-to-ceiling path is older than that proposal. -/
private theorem roundCeiling_targetWalkPasses
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {M : Height} {q : Round} {C P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot q) = some P)
    (h : RoundCeilingAt S rho M q C)
    (haligned : OpeningCeilingAlignedAt S rho q C.erase)
    {v : V} (hv : v ∈ rho.honest) :
    Block.Preceq C.erase
      (Protocol.ghost (voterAnchorAt S rho v (S.hc.opening_slot q))
        (namedWalkTargetTree S rho (S.hc.opening_slot q) v P)
        (namedWalkTargetScore S rho (S.hc.opening_slot q) v)
        (namedWalkTargetEligible S rho (S.hc.opening_slot q) v)) := by
  let s := S.hc.opening_slot q
  let read := Internal.NamedRecoveryRead.voteDutyRead S rho v s
  let st := read.st.core
  let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  have hpriorPos : 0 < s - 1 := by
    show 0 < S.hc.opening_slot q - 1
    unfold Protocol.HealConfig.opening_slot
    have hR : 2 ≤ S.hc.R := S.hc.R_ge_two
    have hqOne : 1 ≤ q := Nat.succ_le_iff.mpr h.roundPositive
    have hopenTwo : 2 ≤ q * S.hc.R := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul hqOne hR
    exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_sub_of_add_le hopenTwo)
  have hpriorSucc : s - 1 + 1 = s :=
    openingSlot_pred_succ S h.roundPositive
  have hinputs : GoldfishConeVoteInputs S rho (s - 1) C.erase v :=
    h.openingStepInputs v hv
  have hwalk := goldfishCone_pathEligible S adm hcom hpriorPos
    h.postPreviousVote h.previousConfirmationInHorizon h.lastVotes hv hinputs
  have hcone : Proofs.Optimistic.ConeSupport S.E st.T votes support votes
      (st.s - 1) rho.honest (fun X => Block.Preceq C.erase X) := by
    simpa only [s, read, st, votes, support, hpriorSucc] using hwalk.1
  have hmajority : Protocol.voters_count S.E votes (st.s - 1) <
      2 * (Protocol.goldfishSupporters S.E st.T votes support (st.s - 1)
        C.erase).card := by
    simpa only [s, read, st, votes, support, hpriorSucc] using hwalk.2.1
  have hCcand : C.erase ∈ voterCandidateTreeAt S rho v s := by
    simpa only [s, hpriorSucc] using hinputs.candidate
  have hanchor : Block.compatible (voterAnchorAt S rho v s) C.erase = true := by
    simpa only [s, hpriorSucc] using hinputs.anchor
  have hHP : Block.Preceq (proposedParent S rho s) P.erase :=
    seedCeiling_proposedParent_preceq S rho s hP
  have hPne : C.erase ≠ P.erase := by
    intro heq
    have hPH : Block.Preceq P.erase (proposedParent S rho s) := by
      rw [← heq]
      exact haligned.ceilingBelowParent
    have hEq : P.erase = proposedParent S rho s :=
      Block.preceq_antisymm hPH hHP
    have hparent : P.erase.parent? = some (proposedParent S rho s) :=
      seedCeiling_erase_parent S rho s hP
    rw [hEq] at hparent
    have hdepth := depth_of_parent? hparent
    omega
  have hCtarget : C.erase ∈ namedWalkTargetTree S rho s v P := by
    simp only [namedWalkTargetTree]
    exact Finset.mem_erase.mpr ⟨hPne,
      by simpa only [voterCandidateTreeAt] using hCcand⟩
  have hpath : Block.Preceq (voterAnchorAt S rho v s) C.erase →
      ∀ D : Block V,
        Block.Preceq (voterAnchorAt S rho v s) D →
        D ≠ voterAnchorAt S rho v s →
        Block.Preceq D C.erase →
        D ∈ namedWalkTargetTree S rho s v P := by
    intro _ D hAD hDne hDC
    have hDcandidate : D ∈ voterCandidateTreeAt S rho v s := by
      by_cases hEq : D = C.erase
      · subst D
        exact hCcand
      · simpa only [s, hpriorSucc] using
          hinputs.path D (by simpa only [s, hpriorSucc] using hAD)
            (by simpa only [s, hpriorSucc] using hDne) hDC hEq
    simp only [namedWalkTargetTree]
    refine Finset.mem_erase.mpr ⟨?_,
      by simpa only [voterCandidateTreeAt] using hDcandidate⟩
    intro hDP
    subst D
    exact hPne
      (Block.preceq_antisymm
        (Block.preceq_trans haligned.ceilingBelowParent hHP) hDC)
  have hhead := Protocol.goldfish_fork_choice_captures_supporter_majority
    S.E st.σ st.h_max st.T (namedWalkTargetTree S rho s v P)
      st.s votes support (st.s - 1) (Proofs.Optimistic.ConeSupport.sub hcone)
      hmajority hanchor hpath
  simpa only [Protocol.goldfish_fork_choice, namedWalkTargetScore,
    namedWalkTargetEligible, s, read, st, votes, support] using hhead

/-- Under the gate-off opening window, the honest named proposal is a frozen
candidate at every honest vote duty.

The gate-off window record lives downstream of this module, so its seven
fields appear here as explicit inputs; `hheight` is the named height the
window's erased `parentHeight` field cannot supply under. -/
private theorem seedCeiling_proposalCandidateAtVote
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {q : Round} {P : NamedBlock V} {v : V}
    (hq : 0 < q)
    (hcarrier : ProposerCarrierAt S rho q)
    (hP : proposedBlockAt S rho (S.hc.opening_slot q) = some P)
    (hnextActionHor : S.a (q + 1) ≤ rho.horizon)
    (hheight : M - 1 ≤ (derive_named S.E S.cfg P).h)
    (hM : 1 ≤ M)
    (hv : v ∈ rho.honest)
    (hproposalAtVote :
      P.erase ∈ (voteDutyStore S rho v (S.hc.opening_slot q)).T)
    (hvoteFrontier :
      (voteDutyStore S rho v (S.hc.opening_slot q)).h_max = M)
    (hvoteGateOff :
      (voteDutyStore S rho v (S.hc.opening_slot q)).h_j + 2 ≤ M) :
    P.erase ∈ Protocol.get_filtered_block_tree
        (voteDutyStore S rho v (S.hc.opening_slot q)).toHealing.toFG ∧
      P.erase ∈ voterCandidateTreeAt S rho v (S.hc.opening_slot q) := by
  have hs : 0 < S.hc.opening_slot q := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos hq (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest := hcarrier.1
  have hactionHor : S.a q ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_succ q)).trans hnextActionHor
  have hconfHor :
      Protocol.confirmation_time S.E (S.hc.opening_slot q) ≤ rho.horizon := by
    simpa only [Protocol.a_eq_confirmation_time] using hactionHor
  have hvoteHor :
      Protocol.vote_time S.E (S.hc.opening_slot q) ≤ rho.horizon :=
    (Protocol.vote_time_le_confirmation_time S.E _).trans hconfHor
  have hproposalHor :
      Protocol.proposal_time S.E (S.hc.opening_slot q) ≤ rho.horizon :=
    (Protocol.proposal_time_le_confirmation_time S.E _).trans hconfHor
  have hrun : RunBlock S rho P :=
    proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
      (S.hc.opening_slot q) hs hprop hproposalHor hP
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hfiltered : P.erase ∈ Protocol.get_filtered_block_tree
      (voteDutyStore S rho v (S.hc.opening_slot q)).toHealing.toFG := by
    simpa only [voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using
      frontierBlock_filtered_of_gateOff S adm hsb hv hvoteHor
        (by simpa only [voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore] using hproposalAtVote)
        rfl hrun hheight hM
        (by simpa only [voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore] using hvoteFrontier)
        (by simpa only [voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore] using hvoteGateOff)
  have hslot : P.erase.slot = S.hc.opening_slot q := by
    rw [Proofs.NamedWire.erase_slot]
    exact proposedBlockAt_slot S rho (S.hc.opening_slot q) hP
  exact ⟨hfiltered,
    seedCeiling_currentSlot_voterCandidate_of_filtered S adm hslot hfiltered⟩

/-- A round ceiling transfers the selected honest opening proposal to every
honest voter without a proposal-anchor-to-vote-anchor premise. The common
ceiling is the frozen pivot, and the preceding honest named vote cone proves
that the proposal-free target walk reaches that pivot in either anchor
orientation.

The retired `HonestProposalWalksTransferred` is replaced by its named twin
`Protocol.VoteStoresExtend` on the bound proposal, the form the vote-name
producer consumes. The gate-off window record lives outside this module's
import cone, so the window's fields appear as explicit inputs.

The frozen suffix transfer is `namedProposalPivotSuffixTransfer_of_frozenProposalNoRise`
on a `NamedFrozenProposalSuffixInputs` record built here from the ceiling and
the window. Nothing is pinned. -/
theorem proposalWalkTransferred_of_roundCeiling
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {q : Round} {C P : NamedBlock V}
    (hcarrier : ProposerCarrierAt S rho q)
    (hP : proposedBlockAt S rho (S.hc.opening_slot q) = some P)
    (h : RoundCeilingAt S rho M q C)
    (haligned : OpeningCeilingAlignedAt S rho q C.erase)
    (hnextActionHor : S.a (q + 1) ≤ rho.horizon)
    (hheight : M - 1 ≤ (derive_named S.E S.cfg P).h)
    (hM : 1 ≤ M)
    (hproposalAtVote : ∀ v ∈ rho.honest,
      P.erase ∈ (voteDutyStore S rho v (S.hc.opening_slot q)).T)
    (hvoteFrontier : ∀ v ∈ rho.honest,
      (voteDutyStore S rho v (S.hc.opening_slot q)).h_max = M)
    (hvoteGateOff : ∀ v ∈ rho.honest,
      (voteDutyStore S rho v (S.hc.opening_slot q)).h_j + 2 ≤ M)
    (hpostFrozenSnapshot : S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q - 1))
    (hproposerFrontier :
      (proposerDutyStore S rho (S.hc.opening_slot q)).h_max = M) :
    Protocol.VoteStoresExtend S rho (S.hc.opening_slot q) P := by
  have hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest := hcarrier.1
  have hpriorSucc : S.hc.opening_slot q - 1 + 1 = S.hc.opening_slot q :=
    openingSlot_pred_succ S h.roundPositive
  have hs : 0 < S.hc.opening_slot q := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos h.roundPositive
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hactionHor : S.a q ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_succ q)).trans hnextActionHor
  have hconfHor :
      Protocol.confirmation_time S.E (S.hc.opening_slot q) ≤ rho.horizon := by
    simpa only [Protocol.a_eq_confirmation_time] using hactionHor
  have hvoteHor :
      Protocol.vote_time S.E (S.hc.opening_slot q) ≤ rho.horizon :=
    (Protocol.vote_time_le_confirmation_time S.E _).trans hconfHor
  have hproposalHor :
      Protocol.proposal_time S.E (S.hc.opening_slot q) ≤ rho.horizon :=
    (Protocol.proposal_time_le_confirmation_time S.E _).trans hconfHor
  have hHP : Block.Preceq
      (proposedParent S rho (S.hc.opening_slot q)) P.erase :=
    seedCeiling_proposedParent_preceq S rho (S.hc.opening_slot q) hP
  have hround : S.hc.round_of
      (proposerReadAt S rho (S.hc.opening_slot q)).st.core.s = q := by
    simpa only [proposerReadAt, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.slotOf_proposal_time] using round_of_opening_slot_eq S.hc q
  have hsourcePivot : Block.Preceq
      (Protocol.get_sg_root_with
        (NamedProfile.gradeContract
          (proposerReadAt S rho (S.hc.opening_slot q)).cache)
        S.E S.hc
        (proposerReadAt S rho (S.hc.opening_slot q)).st.core.toHealing
        (S.hc.round_of
          (proposerReadAt S rho (S.hc.opening_slot q)).st.core.s))
      C.erase := by
    rw [hround]
    exact haligned.sourceBelowCeiling
  intro v hv _hcommittee
  refine ⟨namedWalkTargetTree S rho (S.hc.opening_slot q) v P,
    proposedParent S rho (S.hc.opening_slot q), ?_⟩
  obtain ⟨hfiltered, hcandidate⟩ :=
    seedCeiling_proposalCandidateAtVote S adm hfb h.roundPositive hcarrier hP
      hnextActionHor hheight hM hv (hproposalAtVote v hv)
      (hvoteFrontier v hv) (hvoteGateOff v hv)
  have hrawExtra := voter_raw_extra_equivocates_proposal_afterGST S adm
    (s := S.hc.opening_slot q) hs
    (by simpa only [hpriorSucc] using hpostFrozenSnapshot) hprop hv
      hproposalHor hP hfiltered
  have hscore : ∀ D : Block V,
      D ∈ namedWalkSourceTree S rho (S.hc.opening_slot q) →
      D ∈ namedWalkTargetTree S rho (S.hc.opening_slot q) v P →
      namedWalkTargetScore S rho (S.hc.opening_slot q) v D =
        namedWalkSourceScore S rho (S.hc.opening_slot q) D := by
    have hout := namedWalkScore_target_eq_source_of_proposalCandidate adm
      (s := S.hc.opening_slot q - 1) (P := P)
      (by rw [hpriorSucc]; exact hP) hpostFrozenSnapshot
      (by rw [hpriorSucc]; exact hprop)
      (by rw [hpriorSucc]; exact hvoteHor)
      (by rw [hpriorSucc]; exact hproposalHor)
      hv (by rw [hpriorSucc]; exact hcandidate)
      (by rw [hpriorSucc]; exact hrawExtra)
    simpa only [hpriorSucc] using hout
  have hAP : Block.Preceq
      (voterAnchorAt S rho v (S.hc.opening_slot q)) P.erase :=
    Block.preceq_trans (haligned.voteBelowCeiling v hv)
      (Block.preceq_trans haligned.ceilingBelowParent hHP)
  have hcompat : Block.compatible
      (voterAnchorAt S rho v (S.hc.opening_slot q)) P.erase = true :=
    Block.compatible_of_preceq_common hAP (Block.preceq_self P.erase)
  have hCcand : C.erase ∈ voterCandidateTreeAt S rho v
      (S.hc.opening_slot q) := by
    simpa only [hpriorSucc] using (h.openingStepInputs v hv).candidate
  have hCanchor : Block.compatible
      (voterAnchorAt S rho v (S.hc.opening_slot q)) C.erase = true := by
    simpa only [hpriorSucc] using (h.openingStepInputs v hv).anchor
  have hsuffixInputs : NamedFrozenProposalSuffixInputs S rho
      (S.hc.opening_slot q) C.erase v P :=
    { sourceAnchor := hsourcePivot
      pivotTarget :=
        frozenVoterCandidateTree_subset_filtered S.E
          (Internal.NamedRecoveryRead.voteDutyRead S rho v
            (S.hc.opening_slot q)).st.core.toHealing hCcand
      proposalCandidate := hcandidate
      pivotAnchorCompatible := hCanchor
      proposalAnchorCompatible := hcompat
      sameHMax := hproposerFrontier.trans (hvoteFrontier v hv).symm }
  have hsuffix : NamedProposalPivotSuffixTransfer S rho
      (S.hc.opening_slot q) C.erase v P :=
    namedProposalPivotSuffixTransfer_of_frozenProposalNoRise S adm hs
      hpostFrozenSnapshot hprop hv hvoteHor hP hsuffixInputs
  have htargetPasses := roundCeiling_targetWalkPasses S adm hcom hP h haligned hv
  exact Protocol.namedProposalWalkTransferred_of_frozenCompatiblePivot
    S adm hP hprop hv hcandidate hcompat hsourcePivot
      haligned.ceilingBelowParent htargetPasses
      hsuffix hscore

#print axioms thinHonestHeadAt_of_thin_endpoint
#print axioms roundCeiling_readSupport_of_inputs
#print axioms seedVoteDutyHead_emits
#print axioms seedVoteDutyHead_runBlock
#print axioms seedHeadThin_of_voteInputs
#print axioms seedThinHead_of_voteInputs
#print axioms roundCeiling_voteInputs
#print axioms roundCeiling_voteInHorizon
#print axioms roundCeiling_headThin
#print axioms roundCeiling_thinHead_of_cone
#print axioms seedOpeningVotes_of_cone
#print axioms seedOpeningConfirmation_of_cone
#print axioms roundCeiling_openingVotes
#print axioms roundCeiling_openingConfirmation
#print axioms roundCeiling_openingConfirmationsCompatible
#print axioms roundCeiling_votesThrough
#print axioms seedRelayVoteFacts
#print axioms seedRelayConfirmationFacts
#print axioms seedHonestVotesCone_succ
#print axioms genuineConfirmation_exists_honestVoteSupporter_ceiling
#print axioms roundCeiling_existsFrontier
#print axioms RoundCeilingFrontierAt.genuine_of_ne
#print axioms seedCeiling_currentSlot_voterCandidate_of_filtered
#print axioms coneTarget_preceq_nextProposedParent_named
#print axioms openingAnchorsAligned_of_roundCeiling
#print axioms roundCeiling_targetWalkPasses
#print axioms seedCeiling_proposalCandidateAtVote
#print axioms proposalWalkTransferred_of_roundCeiling

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
