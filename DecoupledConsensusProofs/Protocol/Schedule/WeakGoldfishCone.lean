module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ExcludesRefute
public import DecoupledConsensusProofs.Execution.WeakBlockAdmission
public import DecoupledConsensusProofs.Execution.WeakGoldfishExecution
public import DecoupledConsensusProofs.Protocol.Grades.GoldfishConePersistence
public import DecoupledConsensusProofs.Protocol.ChainState.FGRootWitness
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FGWitnessCandidate
public import DecoupledConsensusProofs.Protocol.Schedule.WeakProcessedTree
public import DecoupledConsensusProofs.Protocol.Schedule.WeakConfirmationTransport
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryHandoffCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.VoteViewValidity
public import DecoupledConsensusProofs.Execution.PreparedReadBridge
public import DecoupledConsensusProofs.Protocol.Handlers.ConfirmationMembership
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.Grades.HealthyHeadReady

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Goldfish cone propagation under core admissibility

Open (class d, design note): this module is an unported weak-runtime
family. It uses retired dep-reachability, erased stores and erased heads, the
barred bare head equality `emittedHead_mem_voteDutyStore`, and retired
`Proofs.Optimistic.HonestVotesCone`. The named replacement is
`NamedHonestVotesCone`; the named Goldfish-vote pool and post-healing cone
producers are not sufficient to prove this old family.

The earlier and selection files have no statement/proof diff. First diagnostics:

  WeakGoldfishConeRun.lean:33:19: `Protocol.get_head_in_tree` receives a
  `NamedStore` where the erased route expects a `Store`.
  WeakGoldfishConeRun.lean:46:4: Unknown identifier
  `Proofs.Bridges.depReachable_stateBeforeTime`.
  WeakGoldfishConeRun.lean:285:14: Unknown identifier
  `Proofs.Optimistic.HonestVotesCone`.

The exact declaration inventory is retained as the Open record:
`voteDutyHead_runBlock`, `emittedHead_mem_voteDutyStore`,
`headsResolveIn_storeBeforeTime_of_availableBefore_at`,
`headsResolveIn_voteDutyStore_succ_of_availableBefore`,
`finalized_preceq_at_delivery_of_voteDutyRoot_preceq`,
`honestHeadsAvailableBefore_of_postHealingCone_atVoteDuty`,
`headsResolveIn_voteDutyStore_succ_of_postHealingCone`,
`goldfishCone_pathEligible`, `goldfishCone_step`, `goldfishCone_step'`, and
`goldfishCone_succ`.
-/

/-!
# Goldfish cone propagation under core admissibility

The prior honest vote cone gives timely head availability through block
relay. The next reader's FG root supplies the local finalized-ancestor
guard. Exact head resolution then gives majority support in the frozen
view. Compatible anchors and candidate paths preserve the next head.

The candidate path and anchor facts remain the joint induction's inputs.
No full attestation participation, grade, accountable bound, or shared
frontier is assumed. The existing strong theorem interfaces are unchanged.
-/











namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakGoldfish

open Internal Execution
open Internal.NamedRecoveryRead
open Proofs.Optimistic Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem coreCarriedSupportSubset
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (w : V) (n : Nat) {B : Block V}
    (hB : B ∈ (NamedRun.stateBefore S rho n w).st.core.T) :
    ∀ u ∈ B.gf_support_votes, u ∈ B.gf_votes := by
  obtain ⟨D, hD, hDB⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n w hB
  have hDsub : ∀ u ∈ D.gf_support_votes, u ∈ D.gf_votes := by
    rcases Proofs.Bridges.processes_block_of_mem_T S rho w n D hD with
      rfl | ⟨j, e, -, -, hproc⟩
    · intro u hu
      exact absurd hu (by simp [NamedBlock.gf_support_votes])
    · rcases hproc with hem | ⟨i, hi⟩
      · obtain ⟨i, hi, hmem⟩ := hem
        obtain ⟨-, hproposal⟩ := block_mem_on_tick_emit S w
          (NamedRun.stateBefore S rho i w) e.time hmem
        have hproposal' : Protocol.NamedActions.proposal_with
            (NamedProfile.gradeContract
              (NamedActionReads.confirmationReadFrom S
                (NamedRun.stateBefore S rho i w) e.time).cache)
            .poolAndCarried S.E S.hc (S.node w)
            (NamedActionReads.confirmationReadFrom S
              (NamedRun.stateBefore S rho i w) e.time).st = some D := by
          unfold Protocol.NamedDuties.propose_block_with at hproposal
          split at hproposal
          · cases hproposal
          · cases hproposal
            assumption
        simp only [Protocol.NamedActions.proposal_with,
          Protocol.with_proposal_input, Option.map_eq_some_iff] at hproposal'
        obtain ⟨parent, -, hDeq⟩ := hproposal'
        rw [← hDeq]
        intro u hu
        exact (List.mem_filter.mp hu).1
      · have hwire := adm.toNamedDeliveryWellFormed.wire
          i w (Object.block D) e.time hi
        simp only [Object.wellFormed, NamedReceipt.wellFormed,
          Bool.and_eq_true] at hwire
        have hsupport := hwire.1.2
        simp only [Protocol.carried_support_well_formed, List.all_eq_true,
          decide_eq_true_eq] at hsupport
        simpa only [Proofs.NamedWire.erase_goldfish_support,
          Proofs.NamedWire.erase_goldfish_votes] using hsupport
  intro u hu
  have hu' : u ∈ D.gf_support_votes := by
    rw [← Proofs.NamedWire.erase_goldfish_support, hDB]
    exact hu
  have := hDsub u hu'
  rw [← hDB, Proofs.NamedWire.erase_goldfish_votes]
  exact this

private theorem coreCarriedVoteCommittee
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (w : V) (n : Nat) {B : Block V}
    (hB : B ∈ (rho.stateBefore S n w).st.T) :
    ∀ u ∈ B.gf_votes, u.val_index ∈ S.E.committee u.slot := by
  obtain ⟨D, hD, hDB⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n w hB
  have hDcommittee :
      ∀ u ∈ D.gf_votes, u.val_index ∈ S.E.committee u.slot := by
    rcases Proofs.Bridges.processes_block_of_mem_T S rho w n D hD with
      rfl | ⟨j, e, -, -, hproc⟩
    · intro u hu
      exact absurd hu (by simp [NamedBlock.gf_votes])
    · rcases hproc with hem | ⟨i, hi⟩
      · obtain ⟨i, hi, hmem⟩ := hem
        let beforeState := NamedRun.stateBefore S rho i w
        let gc := DecoupledConsensusModel.Protocol.frameContract
          (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc
            beforeState.st.core.toHealing e.time beforeState.cache)
        let before := Protocol.NamedStore.setClock S.E beforeState.st e.time
        have hproposal : Protocol.NamedDuties.propose_block_with gc
            S.E S.hc S.cfg (S.node w) before =
            (Protocol.NamedAdmission.on_block_with .alsoCarried
              S.E S.hc S.cfg before D, some D) := by
          simpa only [gc, before, beforeState] using
            (Proofs.NamedReceiptCallsBase.self_proposal_call S rho hi hmem)
        have hproposal' : Protocol.NamedActions.proposal_with gc
            .poolAndCarried S.E S.hc (S.node w) before = some D := by
          have hoption := congrArg Prod.snd hproposal
          cases hp : Protocol.NamedActions.proposal_with gc
              .poolAndCarried S.E S.hc (S.node w) before with
          | none =>
              have hbad : (none : Option (NamedBlock V)) = some D := by
                simpa only [Protocol.NamedDuties.propose_block_with, hp]
                  using hoption
              cases hbad
          | some C =>
              have hC : C = D := by
                apply Option.some.inj
                simpa only [Protocol.NamedDuties.propose_block_with, hp]
                  using hoption
              simpa only [hC] using hp
        have hgf := Proofs.Optimistic.proposal_with_gf_votes gc .poolAndCarried
          S.E S.hc (S.node w) before hproposal'
        intro u hu
        rw [hgf] at hu
        have hu' : u ∈ (rho.stateBefore S i w).st.core.gf_votes
            (S.E.slotOf e.time - 1) := by
          simpa only [NamedActionReads.confirmationReadFrom,
            Protocol.NamedStore.setClock] using hu
        have hslot := (poolStamps_stateBefore S
          adm.toNamedScheduleWellFormed w i).slot
          (S.E.slotOf e.time - 1) u hu'
        rw [hslot]
        exact CommitteePools.stateBefore S rho w i
          (S.E.slotOf e.time - 1) u hu'
      · have hwire := adm.toNamedDeliveryWellFormed.wire
          i w (Object.block D) e.time hi
        simp only [NamedReceipt.wellFormed, Bool.and_eq_true] at hwire
        have hcommittee := hwire.2
        simp only [List.all_eq_true, decide_eq_true_eq] at hcommittee
        simpa only [Proofs.NamedWire.erase_goldfish_votes] using hcommittee
  intro u hu
  have hu' : u ∈ D.gf_votes := by
    rw [← Proofs.NamedWire.erase_goldfish_votes, hDB]
    exact hu
  exact hDcommittee u hu'

private def CoreVoteVisible
    (S : Setup V) (rho : Run V) (w : V) (n : Nat)
    (u : GoldfishVote V) : Prop :=
  (∃ k : Slot, u ∈ (NamedRun.stateBefore S rho n w).st.gf_votes k) ∨
    ∃ B ∈ (NamedRun.stateBefore S rho n w).st.core.T, u ∈ B.gf_votes

private theorem coreEmitsOfVoteVisible
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (w : V) (n : Nat) {u : GoldfishVote V}
    (hu : CoreVoteVisible S rho w n u)
    (hx : u.val_index ∈ rho.honest) :
    ∃ t : Time, NamedRun.emits S rho u.val_index (Object.gfVote u) t := by
  have hblock : ∀ B : NamedBlock V,
      B ∈ (NamedRun.stateBefore S rho n w).st.bodies →
      u ∈ B.gf_votes →
      ∃ t : Time, NamedRun.emits S rho u.val_index (Object.gfVote u) t := by
    intro B hB hmem
    rcases Proofs.Bridges.processes_block_of_mem_T S rho w n B hB with
      rfl | ⟨j, e, -, -, hproc⟩
    · exact absurd hmem (by simp [NamedBlock.gf_votes])
    · exact (adm.toNamedUnforgeable.carried_gf w B e.time hproc u hmem hx).imp
        fun _ ht => ht.2
  rcases hu with ⟨k, hk⟩ | ⟨B, hB, hmem⟩
  · obtain ⟨j, e, -, -, hproc⟩ :=
      processes_gfVote_of_mem_pool S rho w n k u hk
    rcases hproc with hbare | ⟨B, hprocB, hmem⟩
    · exact (adm.toNamedUnforgeable.unforgeable w (Object.gfVote u)
        e.time hbare u.val_index hx rfl).imp fun _ ht => ht.2
    · exact (adm.toNamedUnforgeable.carried_gf w B e.time hprocB u hmem hx).imp
        fun _ ht => ht.2
  · obtain ⟨B', hB', hB'eq⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n w hB
    have hmem' : u ∈ B'.gf_votes := by
      rw [← Proofs.NamedWire.erase_goldfish_votes, hB'eq]
      exact hmem
    exact hblock B' hB' hmem'

private theorem coreVoteVisibleUnique
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (w : V) (n : Nat) {u₁ u₂ : GoldfishVote V}
    (h₁ : CoreVoteVisible S rho w n u₁)
    (h₂ : CoreVoteVisible S rho w n u₂)
    (hx : u₁.val_index ∈ rho.honest)
    (hval : u₂.val_index = u₁.val_index)
    (hslot : u₁.slot = u₂.slot) : u₁ = u₂ := by
  obtain ⟨t₁, he₁⟩ := coreEmitsOfVoteVisible S adm w n h₁ hx
  obtain ⟨t₂, he₂⟩ := coreEmitsOfVoteVisible S adm w n h₂ (by
    rw [hval]
    exact hx)
  rw [hval] at he₂
  exact emits_gfVote_unique S adm.toNamedScheduleWellFormed he₁ he₂ hslot

private theorem coreVoterViewNoHonestEquivocation
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (w : V) (n : Nat) (gst : Protocol.GoldfishStore V)
    (hgf : ∀ (k : Slot) (u : GoldfishVote V), u ∈ gst.gf_votes k →
      u ∈ (NamedRun.stateBefore S rho n w).st.gf_votes k)
    (hT : ∀ B ∈ gst.T,
      B ∈ (NamedRun.stateBefore S rho n w).st.core.T)
    {x : V} (hx : x ∈ rho.honest) (s : Slot) :
    Protocol.equivocates (Protocol.voter_view S.E gst s) x = false := by
  have hview : ∀ u ∈ Protocol.voter_view S.E gst s,
      CoreVoteVisible S rho w n u ∧ u.slot = s - 1 := by
    intro u hu
    rw [Protocol.voter_view, Finset.mem_union] at hu
    rcases hu with hu | hu
    · rw [beforeCutoff, Finset.mem_filter, Protocol.GoldfishStore.pool,
        List.mem_toFinset] at hu
      have hmem := hgf (s - 1) u hu.1
      exact ⟨Or.inl ⟨s - 1, hmem⟩,
        (poolStamps_stateBefore S adm.toNamedScheduleWellFormed w n).slot
          _ u hmem⟩
    · rw [Finset.mem_biUnion] at hu
      obtain ⟨B, hB, hmem⟩ := hu
      rw [Finset.mem_filter] at hB hmem
      have hBT : B ∈ (NamedRun.stateBefore S rho n w).st.core.T :=
        hT B hB.1
      exact ⟨Or.inr ⟨B, hBT, List.mem_toFinset.mp hmem.1⟩, hmem.2⟩
  rw [Protocol.equivocates, decide_eq_false_iff_not, Nat.not_le]
  refine Nat.lt_succ_of_le (Finset.card_le_one.mpr ?_)
  intro u₁ hu₁ u₂ hu₂
  rw [Protocol.votes_by, Finset.mem_filter] at hu₁ hu₂
  obtain ⟨hv₁, hs₁⟩ := hview u₁ hu₁.1
  obtain ⟨hv₂, hs₂⟩ := hview u₂ hu₂.1
  exact coreVoteVisibleUnique S adm w n hv₁ hv₂
    (by rw [hu₁.2]; exact hx)
    (by rw [hu₂.2, hu₁.2]) (by rw [hs₁, hs₂])

private theorem corePreparedVoteViewValid
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (w : V) (s : Slot) :
    Protocol.VoteSetValid S.E
      ((voteDutyRead S rho w s).st.core.s - 1)
      (Protocol.voter_view S.E
        (voteDutyRead S rho w s).st.core.toHealing.toFG.toSG.toGoldfishStore
        (voteDutyRead S rho w s).st.core.s) := by
  let t := Protocol.vote_time S.E s
  let read := voteDutyRead S rho w s
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedScheduleWellFormed t
  have hpool := voteSetValid_pool_stateBefore S
    adm.toNamedScheduleWellFormed w n (read.st.core.s - 1)
  have hcarried : ∀ B ∈ (rho.stateBefore S n w).st.core.T,
      ∀ u ∈ B.gf_votes, u.val_index ∈ S.E.committee u.slot := by
    intro B hB u hu
    exact coreCarriedVoteCommittee S adm w n hB u hu
  have hvalid := voteSetValid_voter_view_of_carried
    (E := S.E) (st := (rho.stateBefore S n w).st.core)
    (s := read.st.core.s) hpool hcarried
  simpa only [read, t, voteDutyRead, NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock, hn]
    using hvalid

private theorem coreVoterHeadRunBlock
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) (d : Slot) :
    ∃ H : NamedBlock V, H.erase = voterHeadAt S rho w d ∧
      H.erase ∈ (voteDutyRead S rho w d).st.core.T ∧
      NamedRun.blockInRun S rho H := by
  let read := voteDutyRead S rho w d
  let st := read.st.core
  let tree := voterCandidateTreeAt S rho w d
  let H := voterHeadAt S rho w d
  have hinvPre : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (NamedRun.stateBeforeTime S rho
        (Protocol.vote_time S.E d) w).st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
      (Protocol.vote_time S.E d) w).1
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg read.st := by
    simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt] using
      Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ _ hinvPre
  have hroot : Protocol.get_fg_root st.toHealing.toFG ∈ st.T :=
    Proofs.NamedStoreRoots.fg_root_mem read.st hinv.1.2
  have hanchor : voterAnchorAt S rho w d ∈ st.T :=
    Proofs.NamedConfirmationMembership.runtime_anchor_mem read.cache
      S.E S.hc st.toHealing (S.hc.round_of st.s) hroot
  have htree : tree ⊆ st.T := by
    intro D hD
    have hp := Proofs.Records.get_filtered_block_tree_from_subset
      st.toHealing.toFG
      (Protocol.voter_processed_block_tree S.E
        st.toHealing.toFG.toSG.toGoldfishStore st.s) hD
    exact (Finset.mem_filter.mp hp).1
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
  have hHpre : H ∈ (NamedRun.stateBeforeTime S rho
      (Protocol.vote_time S.E d) w).st.core.T := by
    simpa only [read, st, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hHmem
  obtain ⟨H', hH'erase, hHrun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
      adm.toNamedScheduleWellFormed hw (Protocol.vote_time S.E d) hHpre
  refine ⟨H', hH'erase, ?_, hHrun⟩
  simpa only [hH'erase, read, st] using hHmem

private theorem coreEmittedHeadMem
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {x : V} (hx : x ∈ rho.honest) {s : Slot} {C : NamedBlock V}
    (hCrun : NamedRun.blockInRun S rho C)
    (hemit : NamedRun.emits S rho x
      (.gfVote ⟨x, s, C.erase.root⟩) (Protocol.vote_time S.E s)) :
    C.erase ∈ (voteDutyRead S rho x s).st.core.T := by
  obtain ⟨i, hi, hmem⟩ := hemit
  change Object.gfVote ⟨x, s, C.erase.root⟩ ∈
    (on_tick_emit S x (rho.stateBefore S i x)
      (Protocol.vote_time S.E s)).2 at hmem
  rw [stateBefore_tick_eq_stateBeforeTime
    S adm.toNamedScheduleWellFormed hi] at hmem
  have hduty := (gfVote_emitted_shape S x
    (rho.stateBeforeTime S (Protocol.vote_time S.E s) x)
    (Protocol.vote_time S.E s) hmem).2.2.1
  have hduty' :
      (Protocol.NamedDuties.goldfish_vote_with
        (NamedProfile.gradeContract (voteDutyRead S rho x s).cache)
        S.E S.hc (S.node x) (voteDutyRead S rho x s).st).2 =
        some ⟨x, s, C.erase.root⟩ := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt] using hduty
  have hroot : (voterHeadAt S rho x s).root = C.erase.root := by
    simp only [Protocol.NamedDuties.goldfish_vote_with,
      Protocol.goldfish_vote_with] at hduty'
    split at hduty'
    · simpa only [voterHeadAt, voterCandidateTreeAt, voteDutyRead] using
        congrArg GoldfishVote.head (Option.some.inj hduty')
    · simp at hduty'
  obtain ⟨H, hHerase, hHmem, hHrun⟩ :=
    coreVoterHeadRunBlock S adm hx s
  have hrootNamed : H.root = C.root := by
    rw [← Proofs.NamedWire.erase_root H, ← Proofs.NamedWire.erase_root C, hHerase]
    exact hroot
  have hHC : H = C :=
    adm.toNamedRootCollisionFree.root_injective H C hHrun hCrun H C
      (Or.inl (Proofs.NamedAncestry.named_self H))
      (Or.inr (Proofs.NamedAncestry.named_self C)) hrootNamed
  simpa only [hHC] using hHmem

private theorem coreFindEmittedHead
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {x : V} (hx : x ∈ rho.honest) {s : Slot} {C : NamedBlock V}
    (hCrun : NamedRun.blockInRun S rho C)
    (hmem : C.erase ∈ (voteDutyRead S rho x s).st.core.T) :
    Block.find? (voteDutyRead S rho x s).st.core.T C.erase.root =
      some C.erase := by
  apply find?_eq_some_of_unique hmem
  intro Y hY hroot
  have hYpre : Y ∈ (NamedRun.stateBeforeTime S rho
      (Protocol.vote_time S.E s) x).st.core.T := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
      using hY
  obtain ⟨D, hDerase, hDrun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
      adm.toNamedScheduleWellFormed hx (Protocol.vote_time S.E s) hYpre
  have hrootNamed : D.root = C.root := by
    rw [← Proofs.NamedWire.erase_root D, ← Proofs.NamedWire.erase_root C, hDerase]
    exact hroot
  have hDC : D = C :=
    adm.toNamedRootCollisionFree.root_injective D C hDrun hCrun D C
      (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self C)) hrootNamed
  rw [← hDerase, hDC]

private theorem coreVoterHeadEmits
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot}
    (hs : 0 < s) (hcommittee : w ∈ S.E.committee s)
    (hhor : Protocol.vote_time S.E s ≤ rho.horizon) :
    ∃ C : NamedBlock V, C.erase = voterHeadAt S rho w s ∧
      NamedRun.blockInRun S rho C ∧
      NamedRun.emits S rho w
        (Object.gfVote ⟨w, s, C.erase.root⟩)
        (Protocol.vote_time S.E s) := by
  obtain ⟨C, hChead, -, hCrun⟩ := coreVoterHeadRunBlock S adm hw s
  let read := voteDutyRead S rho w s
  have hslot : read.st.core.s = s := voteDutyRead_slot S rho w s
  have hcommittee' :
      (S.node w).val_index ∈ S.E.committee read.st.core.s := by
    rw [S.node_val_index, hslot]
    exact hcommittee
  have hout :
      (Protocol.NamedDuties.goldfish_vote_with
        (NamedProfile.gradeContract read.cache)
        S.E S.hc (S.node w) read.st).2 =
        some ⟨(S.node w).val_index, read.st.core.s,
          (voterHeadAt S rho w s).root⟩ := by
    simp only [Protocol.NamedDuties.goldfish_vote_with,
      Protocol.goldfish_vote_with]
    rw [if_pos]
    · rfl
    · exact hcommittee'
  have ho : Object.gfVote
      ⟨(S.node w).val_index, read.st.core.s,
        (voterHeadAt S rho w s).root⟩ ∈
      (on_tick_emit S w
        (NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E s) w)
        (Protocol.vote_time S.E s)).2 := by
    exact on_tick_emit_vote_mem S w
      (NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E s) w)
      s hs hout
  have hem := emits_of_on_tick_emit S adm.toNamedScheduleWellFormed hw
    (publicTime_vote_time S s) (vote_time_nonneg S.E s) hhor ho
  refine ⟨C, hChead, hCrun, ?_⟩
  simpa only [S.node_val_index, hslot, hChead] using hem


private theorem coreOnBlockWithBodies
    (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig)
    (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedAdmission.on_block_with
      .alsoCarried E hc cfg st B).bodies =
      (Protocol.NamedStore.process_block_core E hc cfg st B).bodies := by
  unfold Protocol.NamedAdmission.on_block_with
    Protocol.NamedAdmission.admit_carried
  split_ifs
  · exact (admit_rows_bodies_and_core_T hc B.attestations _).1
  · rfl

private theorem coreHandlerInserts
    (S : Setup V) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st)
    (hp : B.parent ∈ st.bodies) (hfresh : B.erase ∉ st.core.T)
    (hslot : B.erase.slot ≤ st.core.s)
    (hF : Block.Preceq st.core.F B.erase)
    (hproposer : B.erase.proposer? =
      some (S.E.proposer B.erase.slot))
    (hparent : B.erase.parent.slot < B.erase.slot)
    (hcarried :
      Protocol.carried_attestations_admissible S.hc B.erase = true) :
    B ∈ (Protocol.NamedAdmission.on_block_with
      .alsoCarried S.E S.hc S.cfg st B).bodies := by
  have hparentTree : B.erase.parent ∈ st.core.T := by
    rw [Proofs.NamedWire.erase_parent, hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hp
  have hfirst : ¬ (st.core.s < B.erase.slot ∨
      B.erase ∈ st.core.T ∨ B.erase.parent ∉ st.core.T) := by
    simp only [not_or]
    exact ⟨Nat.not_lt.mpr hslot, hfresh, not_not.mpr hparentTree⟩
  have hfinal : (!Block.preceq st.core.F B.erase) = false := by
    rw [hF]
    rfl
  have hafter : B.erase ∈ (Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using S.E current B.erase
        (fun parentState =>
          Protocol.named_transition S.E S.cfg parentState B))
      S.hc st.core B.erase).T := by
    simp [Protocol.on_block_checked_using, hcarried,
      Protocol.on_block_using, hfirst, hfinal, hproposer, hparent,
      Proofs.update_finality_T, Proofs.foldl_on_goldfish_vote_checked_T S.E]
  rw [coreOnBlockWithBodies]
  unfold Protocol.NamedStore.process_block_core
  rw [if_neg (not_not.mpr hp)]
  unfold Protocol.NamedStore.commitBlock
  rw [if_pos ⟨hfresh, hafter⟩]
  exact Finset.mem_insert_self _ _

omit [Fintype V] in
private theorem coreNamedPreceqSelf
    (B : NamedBlock V) : NamedBlock.Preceq B B := by
  cases B <;> simp [NamedBlock.Preceq, NamedBlock.preceq]

private theorem coreNoGeometryAlias
    (S : Setup V) (rho : Run V)
    (roots : NamedRootCollisionFree S rho) (i : Nat) (v : V)
    (hv : v ∈ rho.honest) (B : NamedBlock V)
    (hB : NamedRun.blockInRun S rho B)
    (hnot : B ∉ (NamedRun.stateBefore S rho i v).st.bodies) :
    B.erase ∉ (NamedRun.stateBefore S rho i v).st.core.T := by
  intro hgeom
  have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho i v).1.1.1
  rw [hcoh.1] at hgeom
  obtain ⟨C, hC, he⟩ := Finset.mem_image.mp hgeom
  have hCscope := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hC)
  have hroot : C.root = B.root :=
    (Proofs.NamedWire.erase_root C).symm.trans
      ((congrArg Block.root he).trans (Proofs.NamedWire.erase_root B))
  have hCB : C = B := roots.root_injective C B hCscope hB C B
    (Or.inl (coreNamedPreceqSelf C))
    (Or.inr (coreNamedPreceqSelf B)) hroot
  exact hnot (by simpa only [hCB] using hC)

private theorem coreStateBeforeSlotClock
    (S : Setup V) (rho : Run V) (i : Nat) (v : V) :
    (NamedRun.stateBefore S rho i v).st.core.s =
      S.E.slotOf (NamedRun.stateBefore S rho i v).st.core.t := by
  induction i with
  | zero =>
      simp [Proofs.NamedRuntime.stateBefore_zero, NamedWorld.init,
        NamedNode.initial, Protocol.NamedStore.initial,
        Protocol.Store.init, Env.slotOf, slotOfTime]
  | succ i ih =>
      rw [Proofs.NamedRuntime.stateBefore_succ]
      cases he : rho.events[i]? with
      | none => simpa only [Option.toList_none, List.foldl_nil] using ih
      | some e =>
          change (NamedWorld.step S
              (NamedRun.stateBefore S rho i) e v).st.core.s =
            S.E.slotOf (NamedWorld.step S
              (NamedRun.stateBefore S rho i) e v).st.core.t
          by_cases hv : e.node = v
          · cases e with
            | tick u t =>
                change u = v at hv
                subst u
                rw [Proofs.NamedRuntime.step_tick]
                rw [(Proofs.NamedNode.tick_clock S v _ t).1,
                  (Proofs.NamedNode.tick_clock S v _ t).2]
            | deliver u o t =>
                change u = v at hv
                subst u
                rw [Proofs.NamedRuntime.step_deliver]
                rw [(Proofs.NamedNode.process_clock S _ o).1,
                  (Proofs.NamedNode.process_clock S _ o).2]
                exact ih
          · rw [Proofs.NamedRuntime.step_other S _ e v (Ne.symm hv)]
            exact ih

private theorem coreProposalTimeLeOfAccepts
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} {i : Nat} {B : NamedBlock V} {t : Time}
    (hacc : NamedRun.acceptsAt S rho i v (.block B) t) :
    Protocol.proposal_time S.E B.erase.slot ≤ t := by
  obtain ⟨e, he, -, ht⟩ := hacc.1.2
  rcases hacc.1.1 with ⟨t', htick, hB⟩ | ⟨t', hdeliver⟩
  · have heq : e = Event.tick v t' := Option.some.inj (he.symm.trans htick)
    have ht' : t' = t := by
      rw [heq] at ht
      exact ht
    have hemit : Run.emits S rho v (.block B) t' := ⟨i, htick, hB⟩
    have hshape := emits_block_shape S rho hemit
    rw [Proofs.NamedWire.erase_slot]
    exact (hshape.2.1.symm.trans ht').le
  · have heq : e = Event.deliver v (.block B) t' :=
      Option.some.inj (he.symm.trans hdeliver)
    have ht' : t' = t := by
      rw [heq] at ht
      exact ht
    have hi : rho.events[i]? = some (Event.deliver v (.block B) t) :=
      ht' ▸ hdeliver
    have hfuture := (delivery_guards_of_acceptsAt_block S hacc hi).1
    rw [coreStateBeforeSlotClock S rho i v] at hfuture
    have hmono : Protocol.proposal_time S.E B.erase.slot ≤
        Protocol.proposal_time S.E
          (S.E.slotOf (NamedRun.stateBefore S rho i v).st.core.t) :=
      proposal_time_mono S.E (Nat.not_lt.mp hfuture)
    refine le_trans hmono (le_trans
      (proposal_time_slotOf_le S.E
        (stateBefore_store_time_nonneg S adm.toNamedScheduleWellFormed v i)) ?_)
    exact store_time_le_event_time S adm.toNamedScheduleWellFormed hi v

private theorem coreNotFutureOfDelivery
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} (hv : v ∈ rho.honest) {i : Nat} {B : NamedBlock V} {t : Time}
    (hi : rho.events[i]? = some (Event.deliver v (.block B) t))
    (hlo : Protocol.proposal_time S.E B.erase.slot ≤ t) :
    ¬ (NamedRun.stateBefore S rho i v).st.core.s < B.erase.slot := by
  have htick : Event.tick v (Protocol.proposal_time S.E B.erase.slot) ∈
      rho.events :=
    adm.toNamedScheduleWellFormed.tick_total v hv _
      (publicTime_proposal_time S B.erase.slot)
      (proposal_time_nonneg S.E B.erase.slot)
      (le_trans hlo
        (adm.toNamedScheduleWellFormed.in_horizon _
          (List.mem_of_getElem? hi)).2)
  have hclock : Protocol.proposal_time S.E B.erase.slot ≤
      (NamedRun.stateBefore S rho i v).st.core.t :=
    tick_le_store_time S adm.toNamedScheduleWellFormed hi htick hlo
  rw [coreStateBeforeSlotClock S rho i v]
  exact Nat.not_lt.mpr (slot_le_slotOf_of_proposal_time_le S.E hclock)

private theorem coreAcceptsAtDeliveryGuards
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} {i : Nat} {B : NamedBlock V} {t : Time}
    (hi : rho.events[i]? = some (Event.deliver v (Object.block B) t))
    (hslot : ¬ (NamedRun.stateBefore S rho i v).st.core.s < B.erase.slot)
    (hF : Block.Preceq
      (NamedRun.stateBefore S rho i v).st.core.F B.erase)
    (hproposer : B.erase.proposer? =
      some (S.E.proposer B.erase.slot))
    (hparentSlot : B.erase.parent.slot < B.erase.slot)
    (hattestations :
      Protocol.carried_attestations_admissible S.hc B.erase = true) :
    NamedRun.acceptsAt S rho i v (Object.block B) t := by
  have hparent : B.parent ∈
      (NamedRun.stateBefore S rho i v).st.bodies := by
    have hdeps := adm.toNamedDeliveryWellFormed.deps
      i v (Object.block B) t hi
    simpa only [NamedReceipt.depsPresent, decide_eq_true_eq] using hdeps
  have hfresh : B ∉ (NamedRun.stateBefore S rho i v).st.bodies := by
    have hf := adm.toNamedDeliveryWellFormed.fresh
      i v (Object.block B) t hi
    simpa only [NamedReceipt.processed, decide_eq_false_iff_not] using hf
  have hv : v ∈ rho.honest := by
    have h := adm.toNamedScheduleWellFormed.honest_only _
      (List.mem_of_getElem? hi)
    simpa only [NamedEvent.node] using h
  have hscope := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_delivery S rho hi)
  have hlegacyFresh :
      B.erase ∉ (NamedRun.stateBefore S rho i v).st.core.T :=
    coreNoGeometryAlias S rho adm.toNamedRootCollisionFree i v hv B hscope
      hfresh
  have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho i v).1.1.1
  have hnew := coreHandlerInserts S
    (NamedRun.stateBefore S rho i v).st B hcoh hparent hlegacyFresh
    (Nat.not_lt.mp hslot) hF hproposer hparentSlot hattestations
  refine ⟨⟨Or.inr ⟨t, hi⟩, Event.deliver v (Object.block B) t,
    hi, rfl, rfl⟩, ?_, ?_⟩
  · simpa only [NamedReceipt.processed, decide_eq_false_iff_not]
      using hfresh
  · have hstate : (NamedRun.stateBefore S rho (i + 1) v).st =
        NamedReceipt.process S (NamedRun.stateBefore S rho i v).st
          (Object.block B) :=
      Proofs.NamedReceiptCallsBase.delivery_result S rho hi
    rw [hstate]
    simpa only [NamedReceipt.process, NamedReceipt.processed,
      decide_eq_true_eq] using hnew

private theorem coreAcceptsAtProposedBlock
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} (hs : 0 < s)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E s ≤ rho.horizon)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B) :
    ∃ i : Nat, NamedRun.acceptsAt S rho i (S.E.proposer s)
      (.block B) (Protocol.proposal_time S.E s) := by
  obtain ⟨B0, hB0, -, i₁, hi₁, hemem⟩ :=
    proposedBlockAt_emits_of_honest S adm.toNamedScheduleWellFormed
      s hs hprop hhor
  have hBeq : B0 = B := proposedBlockAt_unique S rho s hB0 hB
  subst hBeq
  have hadmit := proposedBlockAt_admit S adm s hs hB
  obtain ⟨i₂, hi₂, hmem⟩ := proposedBlockAt_mem_bodies_after_tick S
    adm.toNamedScheduleWellFormed s hs hprop hhor hB hadmit
  have hij : i₁ = i₂ :=
    index_unique_of_nodup adm.toNamedScheduleWellFormed.nodup hi₁ hi₂
  subst hij
  refine ⟨i₁, ⟨Or.inl ⟨Protocol.proposal_time S.E s, hi₁, hemem⟩,
    ⟨Event.tick (S.E.proposer s) (Protocol.proposal_time S.E s),
      hi₁, rfl, rfl⟩⟩, ?_, ?_⟩
  · simp only [NamedReceipt.processed, decide_eq_false_iff_not]
    have hstateEq :
        NamedRun.stateBefore S rho i₁ (S.E.proposer s) =
        NamedRun.stateBeforeTime S rho (Protocol.proposal_time S.E s)
          (S.E.proposer s) :=
      stateBefore_tick_eq_stateBeforeTime S
        adm.toNamedScheduleWellFormed hi₁
    rw [hstateEq]
    intro hmemB
    have htree : (proposerReadAt S rho s).st.core.T =
        (proposerReadAt S rho s).st.bodies.image NamedBlock.erase :=
      (proposerReadAt_invariant S rho s).1.1
    exact proposedBlockErased_fresh_at_tick S adm s hs hB
      (htree ▸ Finset.mem_image_of_mem NamedBlock.erase hmemB)
  · simp only [NamedReceipt.processed, decide_eq_true_eq]
    exact hmem

private theorem coreBlockAdmittedAfterCutoff
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {p w : V} (hp : p ∈ rho.honest) (hw : w ∈ rho.honest)
    {i : Nat} {B : NamedBlock V} {t GammaIn GammaOut : Time}
    (hBpos : 0 < B.slot)
    (hacc : NamedRun.acceptsAt S rho i p (Object.block B) t)
    (htIn : t < GammaIn) (hgst : S.E.t_GST ≤ GammaIn)
    (hhop : GammaIn + S.E.Δ = GammaOut)
    (hhor : GammaOut ≤ rho.horizon)
    (hFhist : BlockFinalizedBelowAtDeliveriesBefore
      S rho w B GammaOut) :
    AdmittedBefore S rho w B.erase GammaOut := by
  have hinOut : GammaIn < GammaOut := by
    rw [← hhop]
    exact lt_add_of_pos_right GammaIn S.E.Δ_pos
  have hacceptCutoff : t < GammaOut := lt_trans htIn hinOut
  have hmax : max t S.E.t_GST ≤ GammaIn :=
    max_le (le_of_lt htIn) hgst
  have hrelayCutoff : max t S.E.t_GST + S.E.Δ ≤ GammaOut := by
    calc
      max t S.E.t_GST + S.E.Δ ≤ GammaIn + S.E.Δ := by
        simpa only [add_comm] using add_le_add_right hmax S.E.Δ
      _ = GammaOut := hhop
  have hrelayHorizon :
      max t S.E.t_GST + S.E.Δ ≤ rho.horizon :=
    hrelayCutoff.trans hhor
  by_cases halready : NamedReceipt.processed
      (rho.stateBefore S (i + 1) w).st (Object.block B) = true
  · rcases acceptsAt_block_of_processed S rho w (i + 1) B halready with
      hgen | ⟨j, hj, t', hacc'⟩
    · have hzero : B.slot = 0 := by rw [hgen]; rfl
      exact False.elim ((Nat.ne_of_gt hBpos) hzero)
    · obtain ⟨-, e', he', -, ht'⟩ := hacc'.1
      obtain ⟨-, e, he, -, ht⟩ := hacc.1
      have ht'le : t' ≤ t := by
        rw [← ht', ← ht]
        have hji : j ≤ i := Nat.le_of_lt_succ hj
        rcases hji.lt_or_eq with hlt | rfl
        · exact Proofs.Bridges.time_le_of_key_le
            (key_le_of_index_lt S adm.toNamedScheduleWellFormed hlt he' he)
        · have heq : e' = e := Option.some.inj (he'.symm.trans he)
          rw [heq]
      exact ⟨B, rfl, j, t', hacc', lt_of_le_of_lt ht'le hacceptCutoff⟩
  · have halreadyFalse : NamedReceipt.processed
        (rho.stateBefore S (i + 1) w).st (Object.block B) = false :=
      Bool.eq_false_of_not_eq_true halready
    have hFdeadline : Block.Preceq
        (rho.stateBeforeTime S (max t S.E.t_GST + S.E.Δ) w).st.core.F B.erase := by
      change Block.Preceq
        (NamedRun.stateBeforeTime S rho (max t S.E.t_GST + S.E.Δ) w).st.core.F B.erase
      rw [stateBeforeTime_eq_stateBefore_filter_length S rho
        adm.toNamedScheduleWellFormed.sorted]
      exact hFhist _ (strict_filter_length_mono rho hrelayCutoff)
    have hguard := not_excludes_of_F_preceq_later_time S rho
      adm.toNamedScheduleWellFormed.sorted le_rfl hFdeadline
    obtain ⟨t', htt', ht'hi, j, hproc⟩ :=
      adm.toNamedSynchrony.relay_block p hp i B t hacc w hw
        halreadyFalse hrelayHorizon hguard
    have ht'cutoff : t' < GammaOut :=
      lt_of_lt_of_le ht'hi hrelayCutoff
    obtain ⟨hidx, e, hej, heNode, heTime⟩ := hproc
    rcases hidx with ⟨ttick, htick, hmem⟩ | ⟨tdeliv, hdeliv⟩
    · have heTickEq : e = Event.tick w ttick :=
        Option.some.inj (hej.symm.trans htick)
      have httickEq : ttick = t' := by
        rw [heTickEq] at heTime
        exact heTime
      rw [httickEq] at htick hmem
      have hemit : Run.emits S rho w (Object.block B) t' :=
        ⟨j, htick, hmem⟩
      have hshape := emits_block_shape S rho hemit
      have hwProp : S.E.proposer B.slot ∈ rho.honest := by
        rw [hshape.2.2]
        exact hw
      have ht'hor : t' ≤ rho.horizon :=
        (adm.toNamedScheduleWellFormed.in_horizon _
          (List.mem_of_getElem? htick)).2
      have hproposalHor :
          Protocol.proposal_time S.E B.slot ≤ rho.horizon := by
        rw [← hshape.2.1]
        exact ht'hor
      obtain ⟨B', hB'⟩ := proposedBlockAt_isSome S rho B.slot
      have htick2 := proposalTick S adm.toNamedScheduleWellFormed
        B.slot hBpos hwProp hproposalHor hB'
      rw [hshape.2.2] at htick2
      obtain ⟨hB'slot, hemit'⟩ := htick2
      have hBB' : B = B' :=
        emits_block_unique S adm.toNamedScheduleWellFormed
          hemit hemit' hB'slot.symm
      have hBproposed : proposedBlockAt S rho B.slot = some B :=
        hB'.trans (congrArg some hBB'.symm)
      obtain ⟨jP, hself⟩ := coreAcceptsAtProposedBlock S adm hBpos
        hwProp hproposalHor hBproposed
      rw [hshape.2.2] at hself
      refine ⟨B, rfl, jP, Protocol.proposal_time S.E B.slot, ?_, ?_⟩
      · exact hself
      · rw [← hshape.2.1]
        exact ht'cutoff
    · have heDelivEq : e = Event.deliver w (Object.block B) tdeliv :=
        Option.some.inj (hej.symm.trans hdeliv)
      have htdelivEq : tdeliv = t' := by
        rw [heDelivEq] at heTime
        exact heTime
      rw [htdelivEq] at hdeliv
      have hproposalLe : Protocol.proposal_time S.E B.slot ≤ t' := by
        have h := coreProposalTimeLeOfAccepts S adm hacc
        rw [Proofs.NamedWire.erase_slot] at h
        exact h.trans htt'
      have hslot :
          ¬ (rho.stateBefore S j w).st.core.s < B.erase.slot :=
        coreNotFutureOfDelivery S adm hw hdeliv (by
          rw [Proofs.NamedWire.erase_slot]
          exact hproposalLe)
      have haccept := coreAcceptsAtDeliveryGuards S adm hdeliv hslot
        (hFhist j (Nat.le_trans (Nat.le_succ j)
          (index_succ_le_strict_filter_length rho
            adm.toNamedScheduleWellFormed.sorted GammaOut hdeliv
            (by simpa only [Event.time] using ht'cutoff))))
        (proposer_eq_of_acceptsAt_block S hacc)
        (parent_slot_lt_of_acceptsAt_block S hacc)
        (carried_attestations_admissible_of_acceptsAt_block S hacc)
      exact ⟨B, rfl, j, t', haccept, ht'cutoff⟩

private theorem coreFinalizedPreceqAtDelivery
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} {v : V} {B : Block V} {X : NamedBlock V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho v (s + 1)).st.core.toHealing.toFG) B)
    {i : Nat} {t : Time}
    (hi : rho.events[i]? = some (Event.deliver v (Object.block X) t))
    (hlt : t < Protocol.view_freeze S.E s) :
    Block.Preceq (rho.stateBefore S i v).st.F B := by
  let Gamma := Protocol.vote_time S.E (s + 1)
  let n := (rho.events.filter (fun e => decide (e.time < Gamma))).length
  have hiN : i < n := by
    by_contra hnot
    have hni : n ≤ i := Nat.le_of_not_gt hnot
    have hGamma : Gamma ≤ t :=
      le_time_of_index_ge S adm.toNamedScheduleWellFormed
        (t := Gamma) (j := i) (e := Event.deliver v (Object.block X) t)
        (by simpa only [n] using hni) hi
    exact (not_le_of_gt
      (lt_trans hlt (view_freeze_lt_vote_time_succ S.E s))) hGamma
  let pre := rho.storeBeforeTime S v Gamma
  have hmono : Block.Preceq (rho.stateBefore S i v).st.F pre.F := by
    have hprefix := stateBefore_F_mono S rho v (Nat.le_of_lt hiN)
    have hstore : pre = (rho.stateBefore S n v).st :=
      congrArg NamedNodeState.st
        (congrFun (stateBeforeTime_eq_take S
          adm.toNamedScheduleWellFormed Gamma) v)
    simpa only [hstore] using hprefix
  have hFJ : Block.Preceq pre.F pre.J :=
    Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
      S rho Gamma v
  have hFroot : Block.Preceq pre.F
      (Protocol.get_fg_root pre.toHealing.toFG) :=
    Proofs.Records.preceq_get_fg_root_of_F (st := pre.toHealing.toFG) hFJ
  have hroot' : Block.Preceq
      (Protocol.get_fg_root pre.toHealing.toFG) B := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, pre, Gamma] using hroot
  exact Block.preceq_trans hmono (Block.preceq_trans hFroot hroot')

private theorem coreFinalizedPreceqAtDelivery_of_confRoot
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} {v : V} {B : Block V} {X : NamedBlock V}
    (hroot : Block.Preceq
      (confRoot (Proofs.Optimistic.confStore S rho v s)) B)
    {i : Nat}
    {t : Time}
    (hi : rho.events[i]? = some (Event.deliver v (Object.block X) t))
    (hlt : t < Protocol.support_cutoff S.E s) :
    Block.Preceq (rho.stateBefore S i v).st.F B := by
  let Gamma := Protocol.confirmation_time S.E s
  let n := (rho.events.filter (fun e => decide (e.time < Gamma))).length
  have hiN : i < n := by
    by_contra hnot
    have hni : n ≤ i := Nat.le_of_not_gt hnot
    have hGamma : Gamma ≤ t :=
      le_time_of_index_ge S adm.toNamedScheduleWellFormed
        (t := Gamma) (j := i)
        (e := Event.deliver v (Object.block X) t)
        (by simpa only [n] using hni) hi
    exact (not_le_of_gt
      (lt_of_lt_of_le hlt
        (support_cutoff_le_confirmation_time S.E s))) hGamma
  let pre := rho.storeBeforeTime S v Gamma
  have hmono : Block.Preceq (rho.stateBefore S i v).st.F pre.F := by
    have hprefix := stateBefore_F_mono S rho v (Nat.le_of_lt hiN)
    have hstore : pre = (rho.stateBefore S n v).st := by
      change (rho.stateBeforeTime S Gamma v).st = _
      rw [congrArg NamedNodeState.st
        (congrFun (stateBeforeTime_eq_take S
          adm.toNamedScheduleWellFormed Gamma) v)]
    simpa only [hstore] using hprefix
  have hFJ : Block.Preceq pre.F pre.J :=
    Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
      S rho Gamma v
  have hFroot : Block.Preceq pre.F
      (Protocol.get_fg_root pre.toHealing.toFG) :=
    Proofs.Records.preceq_get_fg_root_of_F (st := pre.toHealing.toFG) hFJ
  have hroot' : Block.Preceq
      (Protocol.get_fg_root pre.toHealing.toFG) B := by
    simpa only [confRoot, Proofs.Optimistic.confStore,
      Proofs.Optimistic.tickStore, pre, Gamma] using hroot
  exact Block.preceq_trans hmono (Block.preceq_trans hFroot hroot')

private theorem coreHonestHeadsAvailable_of_confRoot
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} {v : V} (hv : v ∈ rho.honest)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.support_cutoff S.E s ≤ rho.horizon)
    {B : Block V}
    (hroot : Block.Preceq
      (confRoot (Proofs.Optimistic.confStore S rho v s)) B)
    (hvotes : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq B X)) :
    ∀ X : Block V, HonestHead S rho s X →
      X = Block.genesis ∨ AdmittedBefore S rho v X
        (Protocol.support_cutoff S.E s) := by
  intro X hhead
  by_cases hgen : X = Block.genesis
  · exact Or.inl hgen
  right
  obtain ⟨x, hx, hcommittee, ⟨C, hCX, hCrun⟩, hXemit⟩ := hhead
  obtain ⟨Y, hBY, hYrun, hYemit⟩ := hvotes x hx hcommittee
  have hvoteEq : (⟨x, s, X.root⟩ : GoldfishVote V) =
      ⟨x, s, Y.erase.root⟩ :=
    emits_gfVote_unique S adm.toNamedScheduleWellFormed
      hXemit hYemit rfl
  have hrootEq : X.root = Y.erase.root :=
    congrArg GoldfishVote.head hvoteEq
  have hCY : C = Y := by
    apply adm.toNamedRootCollisionFree.root_injective C Y hCrun hYrun
      C Y (Or.inl (Proofs.NamedAncestry.named_self C))
      (Or.inr (Proofs.NamedAncestry.named_self Y))
    rw [← Proofs.NamedWire.erase_root C, ← Proofs.NamedWire.erase_root Y, hCX]
    exact hrootEq
  have hBX : Block.Preceq B X := by
    simpa only [← hCY, hCX] using hBY
  have hXemit' : NamedRun.emits S rho x
      (.gfVote ⟨x, s, C.erase.root⟩) (Protocol.vote_time S.E s) := by
    simpa only [hCX] using hXemit
  have hmem := coreEmittedHeadMem S adm hx hCrun hXemit'
  have hmemPre : C.erase ∈
      (rho.storeBeforeTime S x (Protocol.vote_time S.E s)).T := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
      using hmem
  rcases block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTime S
      adm.toNamedScheduleWellFormed x (Protocol.vote_time S.E s) hmemPre with
    hgenC | ⟨D, i, ta, hDeq, hacc, hta⟩
  · have hXgen : X = Block.genesis := by
      rw [← hCX, hgenC]
    exact False.elim (hgen hXgen)
  · have hDpos : 0 < D.slot := by
      rw [← Proofs.NamedWire.erase_slot D]
      exact Nat.zero_lt_of_lt (parent_slot_lt_of_acceptsAt_block S hacc)
    have hFhist : BlockFinalizedBelowAtDeliveriesBefore S rho v D
        (Protocol.support_cutoff S.E s) := by
      intro q hq
      have hqGamma := hq.trans (strict_filter_length_mono rho
        (support_cutoff_le_confirmation_time S.E s))
      have hroot' : Block.Preceq
          (Protocol.get_fg_root
            (rho.storeBeforeTime S v (Protocol.confirmation_time S.E s)).toHealing.toFG) B := by
        simpa only [confRoot, Proofs.Optimistic.confStore,
          Proofs.Optimistic.tickStore] using hroot
      have hFD := finalized_preceq_at_prefix_of_storeBeforeRoot_preceq
        S rho adm.toNamedScheduleWellFormed.sorted hroot' hqGamma
      have hDX : D.erase = X := hDeq.trans hCX
      have hFDX : Block.Preceq (rho.stateBefore S q v).st.F X :=
        Block.preceq_trans hFD hBX
      simpa only [hDX] using hFDX
    have hadmit := coreBlockAdmittedAfterCutoff S adm hx hv hDpos
      hacc hta hpost (by rw [← vote_time_add_delta]) hhor hFhist
    simpa only [hDeq.trans hCX] using hadmit

theorem headsResolveIn_confStore_of_postHealingCone
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} {v : V} (hv : v ∈ rho.honest)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.support_cutoff S.E s ≤ rho.horizon)
    {B : Block V}
    (hroot : Block.Preceq
      (confRoot (Proofs.Optimistic.confStore S rho v s)) B)
    (hnames : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq B X)) :
    HeadsResolveIn S rho s (Proofs.Optimistic.confStore S rho v s).T
      (Proofs.Optimistic.confStore S rho v s).timestamp_block := by
  let cutoff := Protocol.support_cutoff S.E s
  have havailable := coreHonestHeadsAvailable_of_confRoot
    S adm hv hpost hhor hroot hnames
  have htransport : ∀ X : Block V, HonestHead S rho s X →
      X ∈ (Proofs.Optimistic.confStore S rho v s).T ∧
        stampedBefore (Proofs.Optimistic.confStore S rho v s).timestamp_block
          cutoff X = true := by
    intro X hX
    rcases havailable X hX with rfl | hadmit
    · exact genesis_mem_and_stamp_storeBeforeTime S
        adm.toNamedScheduleWellFormed v
        (Protocol.confirmation_time S.E s) cutoff
    · have hmem := admittedBefore_mem_and_stamp_at S
        adm.toNamedScheduleWellFormed hadmit
        (support_cutoff_le_confirmation_time S.E s)
      simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using hmem
  let n := (rho.events.filter (fun e => decide
    (e.time < Protocol.confirmation_time S.E s))).length
  have hstore : rho.storeBeforeTime S v
      (Protocol.confirmation_time S.E s) =
      (rho.stateBefore S n v).st := by
    change (NamedRun.stateBeforeTime S rho
      (Protocol.confirmation_time S.E s) v).st = _
    exact congrArg NamedNodeState.st
      (congrFun (stateBeforeTime_eq_take S
        adm.toNamedScheduleWellFormed _) v)
  apply Proofs.Optimistic.headsResolveIn_of S rho s
  · intro X hX
    exact (htransport X hX).1
  · intro X Y hX hY hrootXY
    have hXstate : X ∈ (rho.stateBefore S n v).st.core.T := by
      simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore, hstore]
        using hX
    have hYstate : Y ∈ (rho.stateBefore S n v).st.core.T := by
      simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore, hstore]
        using hY
    obtain ⟨XN, hXNbody, hXNerase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n v hXstate
    obtain ⟨YN, hYNbody, hYNerase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho n v hYstate
    have hXNrun := Proofs.NamedRuntime.blockInRun_of_direct S rho
      (Proofs.NamedRuntime.directBlock_of_prefix S rho hv n hXNbody)
    have hYNrun := Proofs.NamedRuntime.blockInRun_of_direct S rho
      (Proofs.NamedRuntime.directBlock_of_prefix S rho hv n hYNbody)
    have hrootNamed : XN.root = YN.root := by
      rw [← Proofs.NamedWire.erase_root XN, ← Proofs.NamedWire.erase_root YN,
        hXNerase, hYNerase]
      exact hrootXY
    have hXYNamed := adm.toNamedRootCollisionFree.root_injective
      XN YN hXNrun hYNrun XN YN
      (Or.inl (Proofs.NamedAncestry.named_self XN))
      (Or.inr (Proofs.NamedAncestry.named_self YN)) hrootNamed
    rw [← hXNerase, ← hYNerase, hXYNamed]
  · intro X hX
    exact (htransport X hX).2

private theorem corePoolNoHonestEquivocation
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (w : V) (n : Nat) (k : Slot) {x : V} (hx : x ∈ rho.honest) :
    Protocol.equivocates
      ((NamedRun.stateBefore S rho n w).st.pool k) x = false := by
  have hps := Protocol.poolStamps_stateBefore
    S adm.toNamedScheduleWellFormed w n
  rw [Protocol.equivocates, decide_eq_false_iff_not, Nat.not_le]
  refine Nat.lt_succ_of_le (Finset.card_le_one.mpr ?_)
  intro u₁ hu₁ u₂ hu₂
  simp only [Protocol.votes_by, Finset.mem_filter,
    Protocol.NamedStore.pool, Protocol.Store.pool,
    List.mem_toFinset] at hu₁ hu₂
  have hu₁hon : u₁.val_index ∈ rho.honest := by
    simpa only [hu₁.2] using hx
  have hu₂hon : u₂.val_index ∈ rho.honest := by
    simpa only [hu₂.2] using hx
  obtain ⟨t₁, he₁⟩ := Protocol.honestVote_emitted_of_mem_pool_stateBefore
    S adm w n k hu₁.1 hu₁hon
  obtain ⟨t₂, he₂⟩ := Protocol.honestVote_emitted_of_mem_pool_stateBefore
    S adm w n k hu₂.1 hu₂hon
  have he₁' : NamedRun.emits S rho x
      (Object.gfVote u₁) t₁ := by
    simpa only [hu₁.2] using he₁
  have he₂' : NamedRun.emits S rho x
      (Object.gfVote u₂) t₂ := by
    simpa only [hu₂.2] using he₂
  exact Proofs.Optimistic.emits_gfVote_unique S adm.toNamedScheduleWellFormed
    he₁' he₂' (by
      rw [hps.slot k u₁ hu₁.1, hps.slot k u₂ hu₂.1])

/-- Every honest post-GST vote in a resolved confirmation store is counted. -/
theorem canonicalSuffixHonestVoteCounted_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (v : V) (hv : v ∈ rho.honest) (u : GoldfishVote V)
    (hus : u.slot = s) (hval : u.val_index ∈ rho.honest)
    (hemit : NamedRun.emits S rho u.val_index (Object.gfVote u)
      (Protocol.vote_time S.E s))
    (harr : Proofs.Optimistic.HeadArrivesBefore
      (Proofs.Optimistic.confStore S rho v s).T
      (Proofs.Optimistic.confStore S rho v s).timestamp_block
      (Protocol.support_cutoff S.E s) u) :
    u ∈ confVotes S.E (Proofs.Optimistic.confStore S rho v s) s := by
  have hle : Protocol.support_cutoff S.E s ≤
      Protocol.confirmation_time S.E s :=
    support_cutoff_le_confirmation_time S.E s
  obtain ⟨n, hn, -⟩ :=
    Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedScheduleWellFormed (Protocol.confirmation_time S.E s)
  have hstore : rho.storeBeforeTime S v
      (Protocol.confirmation_time S.E s) =
      (rho.stateBefore S n v).st := by
    change (NamedRun.stateBeforeTime S rho
      (Protocol.confirmation_time S.E s) v).st =
      (NamedRun.stateBefore S rho n v).st
    exact congrArg (fun world => (world v).st) hn
  obtain ⟨H, hfind, hH⟩ := harr
  have hHmem : H ∈
      (rho.storeBeforeTime S v (Protocol.confirmation_time S.E s)).T := by
    simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using
      (Proofs.HealingLemmas.find?_mem hfind)
  have hHslot : H.slot ≤ u.slot :=
    Proofs.Optimistic.emitted_vote_head_slot_le_of_store_mem S adm hval hv hemit hus
      hHmem (Proofs.HealingLemmas.find?_root hfind)
  have hrecv : u ∈ beforeCutoff
      (Proofs.Optimistic.confStore S rho v s).timestamp_vote
      (Protocol.support_cutoff S.E s)
      ((Proofs.Optimistic.confStore S rho v s).pool s) :=
    Protocol.gfVote_in_cutoff_view_after_gst S adm hval hs hpost hemit hus hv
      _ _ hle (le_refl _) (le_trans hle hhor)
  have hearly : u ∈ confEarly S.E
      (Proofs.Optimistic.confStore S rho v s) s :=
    Proofs.Optimistic.mem_tau_cutoff_of hrecv hfind hHslot hH
  rw [confVotes, Finset.mem_filter]
  refine ⟨hearly, ?_⟩
  simp only [Protocol.no_second_vote_in, decide_eq_true_eq]
  intro x hx
  by_cases hxv : x.val_index = u.val_index
  · refine Or.inl ?_
    have hxpool : x ∈
        (rho.stateBefore S n v).st.gf_votes s := by
      have h := (Finset.mem_filter.mp hx).1
      rw [Proofs.Optimistic.confStore, Protocol.Store.pool, List.mem_toFinset] at h
      rw [← hstore]
      exact h
    have hupool : u ∈
        (rho.stateBefore S n v).st.gf_votes s := by
      have h := (Finset.mem_filter.mp hearly).1
      rw [Proofs.Optimistic.confStore, Protocol.Store.pool, List.mem_toFinset] at h
      rw [← hstore]
      exact h
    have hno := corePoolNoHonestEquivocation S adm v n s hval
    rw [Protocol.equivocates, decide_eq_false_iff_not] at hno
    have hlt : (Protocol.votes_by
        ((NamedRun.stateBefore S rho n v).st.pool s) u.val_index).card < 2 :=
      Nat.lt_of_not_ge hno
    have hcard : (Protocol.votes_by
        ((NamedRun.stateBefore S rho n v).st.pool s) u.val_index).card ≤ 1 :=
      Nat.le_of_lt_succ (by simpa using hlt)
    have hxpool' : x ∈
        (NamedRun.stateBefore S rho n v).st.pool s := by
      simpa only [Protocol.NamedStore.pool, Protocol.Store.pool,
        List.mem_toFinset] using hxpool
    have hupool' : u ∈
        (NamedRun.stateBefore S rho n v).st.pool s := by
      simpa only [Protocol.NamedStore.pool, Protocol.Store.pool,
        List.mem_toFinset] using hupool
    have hxmem : x ∈ Protocol.votes_by
        ((NamedRun.stateBefore S rho n v).st.pool s) u.val_index := by
      rw [Protocol.votes_by, Finset.mem_filter]
      exact ⟨hxpool', hxv⟩
    have humem : u ∈ Protocol.votes_by
        ((NamedRun.stateBefore S rho n v).st.pool s) u.val_index := by
      rw [Protocol.votes_by, Finset.mem_filter]
      exact ⟨hupool', rfl⟩
    exact Finset.card_le_one.mp hcard x hxmem u humem
  · exact Or.inr hxv

private theorem coreHonestHeadsAvailable
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} {v : V} (hv : v ∈ rho.honest)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.support_cutoff S.E s ≤ rho.horizon)
    {B : Block V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho v (s + 1)).st.core.toHealing.toFG) B)
    (hvotes : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq B X)) :
    ∀ X : Block V, HonestHead S rho s X →
      X = Block.genesis ∨ AdmittedBefore S rho v X
        (Protocol.support_cutoff S.E s) := by
  intro X hhead
  by_cases hgen : X = Block.genesis
  · exact Or.inl hgen
  right
  obtain ⟨x, hx, hcommittee, ⟨C, hCX, hCrun⟩, hXemit⟩ := hhead
  obtain ⟨Y, hBY, hYrun, hYemit⟩ := hvotes x hx hcommittee
  have hvoteEq : (⟨x, s, X.root⟩ : GoldfishVote V) =
      ⟨x, s, Y.erase.root⟩ :=
    emits_gfVote_unique S adm.toNamedScheduleWellFormed
      hXemit hYemit rfl
  have hrootEq : X.root = Y.erase.root :=
    congrArg GoldfishVote.head hvoteEq
  have hCY : C = Y := by
    apply adm.toNamedRootCollisionFree.root_injective C Y hCrun hYrun
      C Y (Or.inl (Proofs.NamedAncestry.named_self C))
      (Or.inr (Proofs.NamedAncestry.named_self Y))
    rw [← Proofs.NamedWire.erase_root C, ← Proofs.NamedWire.erase_root Y, hCX]
    exact hrootEq
  have hBX : Block.Preceq B X := by
    simpa only [← hCY, hCX] using hBY
  have hXemit' : NamedRun.emits S rho x
      (.gfVote ⟨x, s, C.erase.root⟩) (Protocol.vote_time S.E s) := by
    simpa only [hCX] using hXemit
  have hmem := coreEmittedHeadMem S adm hx hCrun hXemit'
  have hmemPre : C.erase ∈
      (rho.storeBeforeTime S x (Protocol.vote_time S.E s)).T := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
      using hmem
  rcases block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTime S
      adm.toNamedScheduleWellFormed x (Protocol.vote_time S.E s) hmemPre with
    hgenC | ⟨D, i, ta, hDeq, hacc, hta⟩
  · have hXgen : X = Block.genesis := by
      rw [← hCX, hgenC]
    exact False.elim (hgen hXgen)
  · have hDpos : 0 < D.slot := by
      rw [← Proofs.NamedWire.erase_slot D]
      exact Nat.zero_lt_of_lt (parent_slot_lt_of_acceptsAt_block S hacc)
    have hFhist : BlockFinalizedBelowAtDeliveriesBefore S rho v D
        (Protocol.support_cutoff S.E s) := by
      intro q hq
      have hqVote := hq.trans (strict_filter_length_mono rho
        ((support_cutoff_lt_view_freeze S.E s).le.trans
          (view_freeze_lt_vote_time_succ S.E s).le))
      have hroot' : Block.Preceq
          (Protocol.get_fg_root
            (rho.storeBeforeTime S v (Protocol.vote_time S.E (s + 1))).toHealing.toFG) B := by
        simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
          Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore] using hroot
      have hFD := finalized_preceq_at_prefix_of_storeBeforeRoot_preceq
        S rho adm.toNamedScheduleWellFormed.sorted hroot' hqVote
      have hDX : D.erase = X := hDeq.trans hCX
      have hFDX : Block.Preceq (rho.stateBefore S q v).st.F X :=
        Block.preceq_trans hFD hBX
      simpa only [hDX] using hFDX
    have hadmit := coreBlockAdmittedAfterCutoff S adm hx hv hDpos
      hacc hta hpost (by rw [← vote_time_add_delta]) hhor hFhist
    simpa only [hDeq.trans hCX] using hadmit


/-- **Public: an honest named cone and the next duty root prove timely block
availability.**

The `coreHonestHeadsAvailable` theorem supplies the core availability fact.
This result uses `NamedHonestVotesCone` and the prepared vote duty read. -/
theorem honestHeadsAvailableBefore_of_postHealingCone_atVoteDuty
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} {v : V} (hv : v ∈ rho.honest)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.support_cutoff S.E s ≤ rho.horizon)
    {B : Block V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho v (s + 1)).st.core.toHealing.toFG) B)
    (hvotes : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq B X)) :
    HonestHeadsAvailableBefore S rho s v (Protocol.support_cutoff S.E s) :=
  coreHonestHeadsAvailable S adm hv hpost hhor hroot hvotes

/-- Delivery-parametric twin of
`honestHeadsAvailableBefore_of_postHealingCone_atVoteDuty`. -/
theorem honestHeadsAvailableBefore_of_delivery_atVoteDuty
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {cap : Time} (hdelivery : HonestDeliveryBefore S rho cap)
    {s : Slot} {v : V} (hv : v ∈ rho.honest)
    (hcap : Protocol.support_cutoff S.E s ≤ cap)
    {B : Block V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho v (s + 1)).st.core.toHealing.toFG) B)
    (hvotes : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq B X)) :
    HonestHeadsAvailableBefore S rho s v (Protocol.support_cutoff S.E s) := by
  intro X hhead
  by_cases hgen : X = Block.genesis
  · exact Or.inl hgen
  right
  obtain ⟨x, hx, hcommittee, ⟨C, hCX, hCrun⟩, hXemit⟩ := hhead
  obtain ⟨Y, hBY, hYrun, hYemit⟩ := hvotes x hx hcommittee
  have hvoteEq : (⟨x, s, X.root⟩ : GoldfishVote V) =
      ⟨x, s, Y.erase.root⟩ :=
    emits_gfVote_unique S adm.toNamedScheduleWellFormed hXemit hYemit rfl
  have hrootEq : X.root = Y.erase.root := congrArg GoldfishVote.head hvoteEq
  have hCY : C = Y := by
    apply adm.toNamedRootCollisionFree.root_injective C Y hCrun hYrun
      C Y (Or.inl (Proofs.NamedAncestry.named_self C))
      (Or.inr (Proofs.NamedAncestry.named_self Y))
    rw [← Proofs.NamedWire.erase_root C, ← Proofs.NamedWire.erase_root Y, hCX]
    exact hrootEq
  have hBX : Block.Preceq B X := by
    simpa only [← hCY, hCX] using hBY
  have hXemit' : NamedRun.emits S rho x
      (.gfVote ⟨x, s, C.erase.root⟩) (Protocol.vote_time S.E s) := by
    simpa only [hCX] using hXemit
  have hmem := coreEmittedHeadMem S adm hx hCrun hXemit'
  have hmemPre : C.erase ∈
      (rho.storeBeforeTime S x (Protocol.vote_time S.E s)).T := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
      using hmem
  have hCbody : C ∈
      (NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E s) x).st.bodies := by
    have hinv := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
      (Protocol.vote_time S.E s) x).1.1.1
    have hmemPre' : C.erase ∈
        (NamedRun.stateBeforeTime S rho
          (Protocol.vote_time S.E s) x).st.core.T := by
      simpa only [Run.storeBeforeTime] using hmemPre
    rw [hinv.1] at hmemPre'
    obtain ⟨D, hDbody, hDe⟩ := Finset.mem_image.mp hmemPre'
    obtain ⟨n, hread, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
      adm.toNamedScheduleWellFormed.sorted (Protocol.vote_time S.E s)
    rw [hread] at hDbody
    have hDrun := Proofs.NamedRuntime.blockInRun_of_direct S rho
      (Proofs.NamedRuntime.directBlock_of_prefix S rho hx n hDbody)
    have hDC : D = C := by
      apply adm.toNamedRootCollisionFree.root_injective D C hDrun hCrun
        D C (Or.inl (Proofs.NamedAncestry.named_self D))
        (Or.inr (Proofs.NamedAncestry.named_self C))
      rw [← Proofs.NamedWire.erase_root D, ← Proofs.NamedWire.erase_root C, hDe]
    rw [hread]
    simpa only [hDC] using hDbody
  let target := Protocol.support_cutoff S.E s
  let next := Protocol.vote_time S.E (s + 1)
  have htargetNext : target ≤ next := support_cutoff_le_vote_time_succ S.E s
  have hFmono : Block.Preceq
      (NamedRun.stateBeforeTime S rho target v).st.core.F
      (NamedRun.stateBeforeTime S rho next v).st.core.F := by
    rw [NamedOutageClosure.strict_read_eq_index S rho
      adm.toNamedScheduleWellFormed.sorted target,
      NamedOutageClosure.strict_read_eq_index S rho
        adm.toNamedScheduleWellFormed.sorted next]
    exact Proofs.NamedRuntime.stateBefore_F_mono S rho v
      (NamedOutageClosure.strict_lengths_mono rho htargetNext)
  have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
    S rho next v
  have hFroot : Block.Preceq
      (NamedRun.stateBeforeTime S rho next v).st.core.F
      (Protocol.get_fg_root
        (voteDutyRead S rho v (s + 1)).st.core.toHealing.toFG) := by
    have h := Proofs.Records.preceq_get_fg_root_of_F
      (st := (NamedRun.stateBeforeTime S rho next v).st.core.toHealing.toFG) hFJ
    simpa only [next, voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using h
  have hFC : Block.Preceq
      (NamedRun.stateBeforeTime S rho target v).st.core.F C.erase := by
    exact Block.preceq_trans hFmono
      (Block.preceq_trans hFroot
        (Block.preceq_trans hroot (by simpa only [hCX] using hBX)))
  obtain ⟨hheld, -, -⟩ := NamedHealthyHeadReady.healthy_head_body_at_read
    S rho adm cap hdelivery x hx v hv C
    (Protocol.vote_time S.E s) target target hCbody
    (by rw [Proofs.Optimistic.vote_time_add_delta]) le_rfl hcap hFC
  rcases block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTime S
      adm.toNamedScheduleWellFormed v target
      (by
        have hinv := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho target v).1.1.1
        have hcore : C.erase ∈
            (NamedRun.stateBeforeTime S rho target v).st.core.T := by
          rw [hinv.1]
          exact Finset.mem_image_of_mem NamedBlock.erase hheld
        simpa only [Run.storeBeforeTime] using hcore) with
    hgenC | ⟨D, i, ta, hDeq, hacc, hta⟩
  · have hXgen : X = Block.genesis := by rw [← hCX, hgenC]
    exact False.elim (hgen hXgen)
  · exact ⟨D, hDeq.trans hCX, i, ta, hacc, hta⟩

#print axioms honestHeadsAvailableBefore_of_delivery_atVoteDuty


/-- **Public: the prepared vote-duty head is a named run block and is the head
the honest voter emits.** `coreVoterHeadEmits` supplies a
`NamedHonestVotesCone` witness. -/
theorem voterHead_runBlock_and_emits
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot}
    (hs : 0 < s) (hcommittee : w ∈ S.E.committee s)
    (hhor : Protocol.vote_time S.E s ≤ rho.horizon) :
    ∃ C : NamedBlock V, C.erase = voterHeadAt S rho w s ∧
      NamedRun.blockInRun S rho C ∧
      NamedRun.emits S rho w
        (Object.gfVote ⟨w, s, C.erase.root⟩)
        (Protocol.vote_time S.E s) :=
  coreVoterHeadEmits S adm hw hs hcommittee hhor


private theorem coreGoldfishConePathEligible_of_transport
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} (hs : 0 < s)
    {C : Block V}
    (hvotes : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq C X))
    {w : V} (hw : w ∈ rho.honest)
    (havailable : HonestHeadsAvailableBefore S rho s w
      (Protocol.support_cutoff S.E s))
    (hcutoff : ∀ {x : V}, x ∈ rho.honest → ∀ {X : NamedBlock V},
      NamedRun.emits S rho x
        (.gfVote ⟨x, s, X.erase.root⟩) (Protocol.vote_time S.E s) →
      (⟨x, s, X.erase.root⟩ : GoldfishVote V) ∈ beforeCutoff
        (Run.storeBeforeTime S rho w
          (Protocol.vote_time S.E (s + 1))).timestamp_vote
        (Protocol.view_freeze S.E s)
        ((Run.storeBeforeTime S rho w
          (Protocol.vote_time S.E (s + 1))).pool s))
    (hinputs : GoldfishConeVoteInputs S rho s C w) :
    let read := voteDutyRead S rho w (s + 1)
    let st := read.st.core
    let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
    let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
    let tree := voterCandidateTreeAt S rho w (s + 1)
    ConeSupport S.E st.T votes support votes (st.s - 1)
        rho.honest (fun X => Block.Preceq C X) ∧
      Protocol.voters_count S.E votes (st.s - 1) <
        2 * (Protocol.goldfishSupporters S.E st.T votes support
          (st.s - 1) C).card ∧
      ∀ D : Block V,
        Block.Preceq (voterAnchorAt S rho w (s + 1)) D →
        D ≠ voterAnchorAt S rho w (s + 1) →
        Block.Preceq D C →
        D ∈ tree ∧
          ((st.σ D.parent).h < st.h_max - 1 ∨
            Protocol.voters_count S.E votes (st.s - 1) <
              2 * Protocol.goldfish_score S.E st.T votes support
                (st.s - 1) D) ∧
          Protocol.goldfish_eligible S.E st.σ st.h_max st.T st.s
            votes support (st.s - 1) D = true := by
  let read := voteDutyRead S rho w (s + 1)
  let st := read.st.core
  let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  let tree := voterCandidateTreeAt S rho w (s + 1)
  have hslot : st.s = s + 1 := by
    simpa only [st, read] using voteDutyRead_slot S rho w (s + 1)
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedScheduleWellFormed (Protocol.vote_time S.E (s + 1))
  have hcone : ConeSupport S.E st.T votes support votes (st.s - 1)
      rho.honest (fun X => Block.Preceq C X) := by
    apply coneSupport_of_named_votes (by simpa only [hslot] using hcom s)
      (subset_refl _) (voter_support_view_subset S.E _ _ ?_) ?_ ?_
    · intro B hB u hu
      apply coreCarriedSupportSubset S adm w n
      simpa only [st, read, voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock, hn] using hB
      exact hu
    · intro x hxCommittee hxHonest
      apply coreVoterViewNoHonestEquivocation S adm w n
        st.toHealing.toFG.toSG.toGoldfishStore
      · intro k u hu
        simpa only [st, read, voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock, hn] using hu
      · intro B hB
        simpa only [st, read, voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock, hn] using hB
      · exact hxHonest
    · intro x hxCommittee hxHonest
      obtain ⟨X, hCX, hXrun, hXemit⟩ :=
        hvotes x hxHonest (by simpa only [hslot] using hxCommittee)
      have hhead : HonestHead S rho s X.erase :=
        ⟨x, hxHonest, by simpa only [hslot] using hxCommittee,
          ⟨X, rfl, hXrun⟩, hXemit⟩
      have hvisible : X.erase ∈
          (rho.storeBeforeTime S w (Protocol.vote_time S.E (s + 1))).T ∧
          stampedBefore
            (rho.storeBeforeTime S w
              (Protocol.vote_time S.E (s + 1))).timestamp_block
            (Protocol.view_freeze S.E s) X.erase = true := by
        rcases havailable X.erase hhead with hgen | hadmit
        · simpa only [hgen] using
            (genesis_mem_and_stamp_storeBeforeTime S
              adm.toNamedScheduleWellFormed w
              (Protocol.vote_time S.E (s + 1))
              (Protocol.view_freeze S.E s))
        · have hvis := admittedBefore_mem_and_stamp_at S
            adm.toNamedScheduleWellFormed hadmit
            (support_cutoff_le_vote_time_succ S.E s)
          refine ⟨hvis.1, ?_⟩
          rw [stampedBefore_eq_occurrenceBefore] at hvis ⊢
          exact occurrenceBefore_mono
            (le_of_lt (support_cutoff_lt_view_freeze S.E s)) hvis.2
      have hXmem : X.erase ∈ (voteDutyRead S rho w (s + 1)).st.core.T := by
        simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock] using hvisible.1
      have hfind := coreFindEmittedHead S adm hw hXrun hXmem
      have hcut := hcutoff hxHonest hXemit
      have hXslot : X.erase.slot ≤ s :=
        Proofs.Optimistic.emitted_vote_head_slot_le_of_store_mem S adm
          hxHonest hw hXemit rfl hvisible.1 (by rfl)
      have hXslot' : X.erase.slot ≤ st.s - 1 := by
        simpa only [hslot, Nat.add_sub_cancel] using hXslot
      refine ⟨X.erase, hCX, hXslot', ?_, ?_⟩
      · apply mem_voter_support_view_of_pool
        rw [beforeCutoff, Finset.mem_filter] at hcut ⊢
        have hpool : (⟨x, s, X.erase.root⟩ : GoldfishVote V) ∈
            st.toHealing.toFG.toSG.toGoldfishStore.pool s := by
          simpa only [st, read, voteDutyRead,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom,
            Protocol.NamedStore.setClock] using hcut.1
        have hreceipt : stampedBefore st.toHealing.toFG.toSG.toGoldfishStore.timestamp_vote
            (Protocol.view_freeze S.E s)
            (⟨x, s, X.erase.root⟩ : GoldfishVote V) = true := by
          simpa only [st, read, voteDutyRead,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom,
            Protocol.NamedStore.setClock] using hcut.2
        have hblock : stampedBefore st.toHealing.toFG.toSG.toGoldfishStore.timestamp_block
            (Protocol.view_freeze S.E s) X.erase = true := by
          simpa only [st, read, voteDutyRead,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom,
            Protocol.NamedStore.setClock] using hvisible.2
        have hresolution :=
          Protocol.stampedBefore_resolution_of hfind hXslot hreceipt hblock
        simpa only [hslot, Nat.add_sub_cancel] using
          And.intro hpool hresolution
      · simpa only [st, read] using hfind
  have hvalid := corePreparedVoteViewValid S adm w (s + 1)
  have hmajority : Protocol.voters_count S.E votes (st.s - 1) <
      2 * (Protocol.goldfishSupporters S.E st.T votes support
        (st.s - 1) C).card :=
    supporterMajority_of_cone S.E hcone (by
      simpa only [votes, st, read] using hvalid)
  refine ⟨hcone, hmajority, ?_⟩
  intro D hAD hDne hDC
  have hDmem : D ∈ tree := by
    by_cases hEq : D = C
    · subst D
      exact hinputs.candidate
    · exact hinputs.path D hAD hDne hDC hEq
  have hDmajority : Protocol.voters_count S.E votes (st.s - 1) <
      2 * Protocol.goldfish_score S.E st.T votes support
        (st.s - 1) D :=
    eligible_of_supporter_majority hmajority hDC
  refine ⟨hDmem, Or.inr hDmajority, ?_⟩
  rw [goldfish_eligible_iff]
  exact Or.inr (Or.inl hDmajority)

private theorem coreGoldfishConePathEligible
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V}
    (hvotes : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq C X))
    {w : V} (hw : w ∈ rho.honest)
    (hinputs : GoldfishConeVoteInputs S rho s C w) :
    let read := voteDutyRead S rho w (s + 1)
    let st := read.st.core
    let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
    let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
    let tree := voterCandidateTreeAt S rho w (s + 1)
    ConeSupport S.E st.T votes support votes (st.s - 1)
        rho.honest (fun X => Block.Preceq C X) ∧
      Protocol.voters_count S.E votes (st.s - 1) <
        2 * (Protocol.goldfishSupporters S.E st.T votes support
          (st.s - 1) C).card ∧
      ∀ D : Block V,
        Block.Preceq (voterAnchorAt S rho w (s + 1)) D →
        D ≠ voterAnchorAt S rho w (s + 1) →
        Block.Preceq D C →
        D ∈ tree ∧
          ((st.σ D.parent).h < st.h_max - 1 ∨
            Protocol.voters_count S.E votes (st.s - 1) <
              2 * Protocol.goldfish_score S.E st.T votes support
                (st.s - 1) D) ∧
          Protocol.goldfish_eligible S.E st.σ st.h_max st.T st.s
            votes support (st.s - 1) D = true := by
  apply coreGoldfishConePathEligible_of_transport S adm hcom hs hvotes hw
  · exact coreHonestHeadsAvailable S adm hw hpost
      ((support_cutoff_le_confirmation_time S.E s).trans hhor)
      hinputs.root hvotes
  · intro x hx X hXemit
    exact Protocol.gfVote_in_cutoff_view_after_gst S adm hx hs hpost
      hXemit rfl hw
      (Protocol.vote_time S.E (s + 1)) (Protocol.view_freeze S.E s)
      (support_cutoff_le_vote_time_succ S.E s)
      (le_of_lt (support_cutoff_lt_view_freeze S.E s))
      ((support_cutoff_le_confirmation_time S.E s).trans hhor)
  · exact hinputs

private theorem coreGoldfishConePathEligible_of_delivery
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {cap : Time} (hdelivery : HonestDeliveryBefore S rho cap)
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} (hs : 0 < s)
    (hcap : Protocol.confirmation_time S.E s ≤ cap)
    {C : Block V}
    (hvotes : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq C X))
    {w : V} (hw : w ∈ rho.honest)
    (hinputs : GoldfishConeVoteInputs S rho s C w) :
    let read := voteDutyRead S rho w (s + 1)
    let st := read.st.core
    let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
    let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
    let tree := voterCandidateTreeAt S rho w (s + 1)
    ConeSupport S.E st.T votes support votes (st.s - 1)
        rho.honest (fun X => Block.Preceq C X) ∧
      Protocol.voters_count S.E votes (st.s - 1) <
        2 * (Protocol.goldfishSupporters S.E st.T votes support
          (st.s - 1) C).card ∧
      ∀ D : Block V,
        Block.Preceq (voterAnchorAt S rho w (s + 1)) D →
        D ≠ voterAnchorAt S rho w (s + 1) →
        Block.Preceq D C →
        D ∈ tree ∧
          ((st.σ D.parent).h < st.h_max - 1 ∨
            Protocol.voters_count S.E votes (st.s - 1) <
              2 * Protocol.goldfish_score S.E st.T votes support
                (st.s - 1) D) ∧
          Protocol.goldfish_eligible S.E st.σ st.h_max st.T st.s
            votes support (st.s - 1) D = true := by
  apply coreGoldfishConePathEligible_of_transport S adm hcom hs hvotes hw
  · exact honestHeadsAvailableBefore_of_delivery_atVoteDuty S adm hdelivery hw
      ((support_cutoff_le_confirmation_time S.E s).trans hcap)
      hinputs.root hvotes
  · intro x hx X hXemit
    exact Protocol.gfVote_in_cutoff_view_of_delivery S adm hdelivery hx hs
      hXemit rfl hw
      (Protocol.vote_time S.E (s + 1)) (Protocol.view_freeze S.E s)
      (support_cutoff_le_vote_time_succ S.E s)
      (le_of_lt (support_cutoff_lt_view_freeze S.E s))
      ((support_cutoff_le_confirmation_time S.E s).trans hcap)
  · exact hinputs

/-- The core-admissible named root-side Goldfish step. -/
theorem goldfishCone_step'
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {C : Block V}
    (hvotes : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq C X))
    {w : V} (hw : w ∈ rho.honest)
    (hinputs : GoldfishConeVoteInputs' S rho s C w) :
    Block.Preceq C (voterHeadAt S rho w (s + 1)) := by
  rcases hinputs.rootSide with hrootBelow | hbelowRoot
  · let read := voteDutyRead S rho w (s + 1)
    let st := read.st.core
    let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
    let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
    have hwalk := coreGoldfishConePathEligible S adm hcom hs hpost hhor
      hvotes hw
      { candidate := hrootBelow.2.1
        root := hrootBelow.1
        anchor := hinputs.anchor
        path := hrootBelow.2.2 }
    have hhead := goldfish_fork_choice_captures_supporter_majority
      S.E st.σ st.h_max st.T (voterCandidateTreeAt S rho w (s + 1))
      st.s votes support (st.s - 1) (ConeSupport.sub hwalk.1)
      hwalk.2.1 hinputs.anchor
      (fun _ D hAD hDne hDC => (hwalk.2.2 D hAD hDne hDC).1)
    change Block.Preceq C
      (Protocol.get_head_in_tree_with_layer
        (NamedProfile.gradeContract read.cache) S.E S.hc st.toHealing
        (voterCandidateTreeAt S rho w (s + 1)) votes support
        (st.s - 1))
    simpa only [get_head_in_tree_eq_voterHeadAt_of_anchor, read, st]
      using hhead
  · let read := voteDutyRead S rho w (s + 1)
    let st := read.st.core
    let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
    let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
    have hhead := get_head_in_tree_with_of_preceq_fgRoot
      read.cache S.E S.hc st.toHealing
      (voterCandidateTreeAt S rho w (s + 1)) C votes support
      (st.s - 1) hbelowRoot
    change Block.Preceq C
      (Protocol.get_head_in_tree_with_layer
        (NamedProfile.gradeContract read.cache) S.E S.hc st.toHealing
        (voterCandidateTreeAt S rho w (s + 1)) votes support
        (st.s - 1))
    simpa only [get_head_in_tree_eq_voterHeadAt_of_anchor, read, st]
      using hhead

/-- Delivery-parametric twin of `goldfishCone_step'`. -/
theorem goldfishCone_step_of_delivery
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {cap : Time} (hdelivery : HonestDeliveryBefore S rho cap)
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} (hs : 0 < s)
    (hcap : Protocol.confirmation_time S.E s ≤ cap)
    {C : Block V}
    (hvotes : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq C X))
    {w : V} (hw : w ∈ rho.honest)
    (hinputs : GoldfishConeVoteInputs' S rho s C w) :
    Block.Preceq C (voterHeadAt S rho w (s + 1)) := by
  rcases hinputs.rootSide with hrootBelow | hbelowRoot
  · let read := voteDutyRead S rho w (s + 1)
    let st := read.st.core
    let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
    let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
    have hwalk := coreGoldfishConePathEligible_of_delivery
      S adm hdelivery hcom hs hcap hvotes hw
      { candidate := hrootBelow.2.1
        root := hrootBelow.1
        anchor := hinputs.anchor
        path := hrootBelow.2.2 }
    have hhead := goldfish_fork_choice_captures_supporter_majority
      S.E st.σ st.h_max st.T (voterCandidateTreeAt S rho w (s + 1))
      st.s votes support (st.s - 1) (ConeSupport.sub hwalk.1)
      hwalk.2.1 hinputs.anchor
      (fun _ D hAD hDne hDC => (hwalk.2.2 D hAD hDne hDC).1)
    change Block.Preceq C
      (Protocol.get_head_in_tree_with_layer
        (NamedProfile.gradeContract read.cache) S.E S.hc st.toHealing
        (voterCandidateTreeAt S rho w (s + 1)) votes support
        (st.s - 1))
    simpa only [get_head_in_tree_eq_voterHeadAt_of_anchor, read, st]
      using hhead
  · let read := voteDutyRead S rho w (s + 1)
    let st := read.st.core
    let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
    let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
    have hhead := get_head_in_tree_with_of_preceq_fgRoot
      read.cache S.E S.hc st.toHealing
      (voterCandidateTreeAt S rho w (s + 1)) C votes support
      (st.s - 1) hbelowRoot
    change Block.Preceq C
      (Protocol.get_head_in_tree_with_layer
        (NamedProfile.gradeContract read.cache) S.E S.hc st.toHealing
        (voterCandidateTreeAt S rho w (s + 1)) votes support
        (st.s - 1))
    simpa only [get_head_in_tree_eq_voterHeadAt_of_anchor, read, st]
      using hhead

#print axioms goldfishCone_step_of_delivery

private theorem coreNamedAncestorBodyMem {st : Protocol.NamedStore V}
    (hpc : NamedStore.NamedParentClosed st) {A B : NamedBlock V}
    (hB : B ∈ st.bodies) (hAB : NamedBlock.Preceq A B) :
    A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq,
        decide_eq_true_eq] at hAB
      exact hAB ▸ hB
  | node parent slot root votes support rows proposer ih =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hparent
      · exact hB
      · exact ih (hpc.2 _ hB) hparent

private theorem coreActionStoreCoherent
    (S : Setup V) {rho : Run V} (v : V) (r : Round) :
    Proofs.NamedStore.Coherent S.E S.cfg (actionStoreAt S rho v r).st := by
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (actionStoreAt S rho v r).st := by
    apply Proofs.NamedConfirmationMembership.invariant_update
    exact Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ (S.a r)
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a r) v).1
  exact hinv.1.1

private theorem coreActionBodyRunBlock
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionStoreAt S rho v r).st.bodies) :
    RunBlock S rho D := by
  have hDpre : D ∈ (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hD
  obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedScheduleWellFormed.sorted (S.a r)
  have hDi : D ∈ (rho.stateBefore S i v).st.bodies := by
    change D ∈ (NamedRun.stateBefore S rho i v).st.bodies
    rw [← hi]
    exact hDpre
  exact Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hDi)

private theorem coreNamedPreceq_of_runBlock_erase_preceq
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {X B : NamedBlock V} (hXrun : RunBlock S rho X)
    (hBrun : RunBlock S rho B)
    (h : Block.Preceq X.erase B.erase) :
    NamedBlock.Preceq X B := by
  obtain ⟨A, hAB, hAerase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B h
  have hArun : RunBlock S rho A :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hBrun hAB
  have hrootEq : A.root = X.root := by
    rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root X, hAerase]
  have hAX : A = X :=
    adm.toNamedRootCollisionFree.root_injective A X hArun hXrun A X
      (Or.inl (Proofs.NamedAncestry.named_self A))
      (Or.inr (Proofs.NamedAncestry.named_self X)) hrootEq
  rw [← hAX]
  exact hAB

private theorem coreActionNamedCheckpoint
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionStoreAt S rho v r).st.bodies) :
    ∃ K : NamedBlock V,
      K ∈ (actionStoreAt S rho v r).st.bodies ∧
      K.erase = (Protocol.derive_named S.E S.cfg D).T_h ∧
      (Protocol.derive_named S.E S.cfg K).h =
        (Protocol.derive_named S.E S.cfg D).h ∧
      NamedBlock.Preceq K D ∧ RunBlock S rho K := by
  obtain ⟨K, hKD, hKentry, hKh⟩ :=
    Proofs.NamedEntryHeight.entry_ancestor_same_height S.E S.cfg D
  have hcoh := coreActionStoreCoherent (rho := rho) S v r
  have hK : K ∈ (actionStoreAt S rho v r).st.bodies :=
    coreNamedAncestorBodyMem hcoh.2.2.1 hD hKD
  exact ⟨K, hK, hKentry, hKh, hKD,
    coreActionBodyRunBlock S adm hv hK⟩

private theorem coreEmittedAttestationEq
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {a : NamedAttestation V} {ta : Time}
    (hemit : NamedRun.emits S rho a.val_index (Object.attest a) ta) :
    a = actionAttestationAt S rho a.val_index a.round := by
  have htime : ta = S.a a.round := (emits_attest_shape S hemit).2
  subst ta
  obtain ⟨i, hi, hduty⟩ := emits_attest_duty S hemit
  rw [Proofs.NamedRuntime.tick_prefix_eq_strict S rho adm.sorted adm.nodup hi]
    at hduty
  simpa only [actionAttestationAt, actionReadAt,
    NamedActionReads.actionReadAt] using hduty.symm

private theorem coreHonestEmittedHeightRowWitness
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {a : NamedAttestation V} {ta : Time} {h : Height}
    (hemit : NamedRun.emits S rho a.val_index (Object.attest a) ta)
    (hh : a.height_pair.erase.height? = some h) :
    ∃ D : NamedBlock V, ∃ J : Block V,
      ta = S.a a.round ∧
      a = actionAttestationAt S rho a.val_index a.round ∧
      actionFGSource S (actionStoreAt S rho a.val_index a.round) =
        some D.erase ∧
      D ∈ (actionStoreAt S rho a.val_index a.round).st.bodies ∧
      ((actionStoreAt S rho a.val_index a.round).st.core.σ D.erase).h = h ∧
      (Protocol.derive_named S.E S.cfg D).h = h ∧
      J = (Protocol.derive_named S.E S.cfg D).T_h ∧
      (a.height_pair.erase = HeightPair.target h J.root ∨
        a.height_pair.erase = HeightPair.timeout h) := by
  have htime : ta = S.a a.round := (emits_attest_shape S hemit).2
  have haEq := coreEmittedAttestationEq S adm hemit
  rw [haEq] at hh
  generalize hp :
      (actionAttestationAt S rho a.val_index a.round).height_pair = q
      at hh
  cases q with
  | empty => cases hh
  | vote h' entry timeout =>
      have hh' : h' = h := by
        cases timeout <;>
          simpa [NamedHeightPair.erase, HeightPair.height?] using hh
      subst h'
      obtain ⟨Cfg, hCfg, hCfgHeight, hCfgRoot⟩ :=
        NamedActionSources.action_source S rho a.val_index a.round
          h entry timeout hp
      obtain ⟨D, hD, hDerase, hDderive, -⟩ :=
        NamedActionSources.action_witness S rho a.val_index a.round
          Cfg hCfg
      let J := (Protocol.derive_named S.E S.cfg D).T_h
      have hsource : actionFGSource S
          (actionStoreAt S rho a.val_index a.round) = some D.erase := by
        simpa only [actionStoreAt, hDerase] using hCfg
      have hheight :
          ((actionStoreAt S rho a.val_index a.round).st.core.σ
            D.erase).h = h := by
        simpa only [actionStoreAt, hDerase] using hCfgHeight
      have hnamedHeight :
          (Protocol.derive_named S.E S.cfg D).h = h := by
        simpa only [hDderive, actionStoreAt, hDerase] using hheight
      have hJroot : J.root = entry := by
        dsimp only [J]
        simpa only [hDderive] using hCfgRoot
      refine ⟨D, J, htime, haEq, hsource, hD, hheight,
        hnamedHeight, rfl, ?_⟩
      cases timeout with
      | false =>
          left
          rw [haEq, hp]
          simp [NamedHeightPair.erase, hJroot]
      | true =>
          right
          rw [haEq, hp]
          simp [NamedHeightPair.erase]

private theorem coreHonestHeightRowConfirmationWitness
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {a : NamedAttestation V} {ta : Time} {h : Height}
    (haHon : a.val_index ∈ rho.honest)
    (hemit : NamedRun.emits S rho a.val_index (Object.attest a) ta)
    (hh : a.height_pair.erase.height? = some h) :
    ∃ D K : NamedBlock V,
      fgConfirmationWitness S
          (actionStoreAt S rho a.val_index a.round) =
        some (Protocol.derive_named S.E S.cfg K).T_h ∧
      D ∈ (actionStoreAt S rho a.val_index a.round).st.bodies ∧
      actionFGSource S (actionStoreAt S rho a.val_index a.round) =
        some D.erase ∧
      (Protocol.derive_named S.E S.cfg D).h = h ∧
      K ∈ (actionStoreAt S rho a.val_index a.round).st.bodies ∧
      K.erase = (Protocol.derive_named S.E S.cfg D).T_h ∧
      (Protocol.derive_named S.E S.cfg K).h = h ∧
      Block.Preceq K.erase D.erase ∧
      (a.height_pair.erase = HeightPair.target h K.erase.root ∨
        a.height_pair.erase = HeightPair.timeout h) := by
  obtain ⟨D, J, -, -, hsource, hD, -, hnamedHeight, hJ, hrow⟩ :=
    coreHonestEmittedHeightRowWitness S adm hemit hh
  obtain ⟨K, hK, hKentry, hKheight, hKpre, -⟩ :=
    coreActionNamedCheckpoint S adm haHon hD
  have hKheight' : (Protocol.derive_named S.E S.cfg K).h = h :=
    hKheight.trans hnamedHeight
  have hDderive :
      (actionStoreAt S rho a.val_index a.round).st.core.σ D.erase =
        Protocol.derive_named S.E S.cfg D :=
    (coreActionStoreCoherent S a.val_index a.round).2.2.2.2 D hD
  have hfg' : fgConfirmationWitness S
      (actionStoreAt S rho a.val_index a.round) =
      some (Protocol.derive_named S.E S.cfg D).T_h := by
    unfold fgConfirmationWitness
    rw [hsource, Option.map_some, hDderive]
  have hKtarget :
      (Protocol.derive_named S.E S.cfg K).T_h = K.erase :=
    (Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hKpre hKheight).trans
      hKentry.symm
  have hfgK : fgConfirmationWitness S
      (actionStoreAt S rho a.val_index a.round) =
      some (Protocol.derive_named S.E S.cfg K).T_h := by
    rw [hfg']
    congr 1
    exact (hKtarget.trans hKentry).symm
  have hJroot : J.root = K.erase.root := by
    rw [hJ, ← hKentry]
  refine ⟨D, K, hfgK, hD, hsource, hnamedHeight, hK, hKentry,
    hKheight', Proofs.NamedWire.erase_preceq hKpre, ?_⟩
  simpa only [hJroot] using hrow

private theorem coreFrontierQuorumWitness
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hmajority : HonestWeightMajority S rho.honest)
    {t : Time} {v : V}
    (hlarge : 1 < (rho.storeBeforeTime S v t).h_max) :
    ∃ W : NamedBlock V,
      W ∈ (rho.storeBeforeTime S v t).bodies ∧
      ∃ Q : Finset V, ∃ X : NamedBlock V,
      ∃ a : NamedAttestation V, ∃ ta,
        (rho.storeBeforeTime S v t).core.h_max ≤
            (Protocol.derive_named S.E S.cfg W).h ∧
          S.E.electorate.IsQuorum Q ∧ NamedBlock.Preceq X W ∧
          a.erase ∈ chain_attestations W.erase ∧
          a.val_index ∈ rho.honest ∧
          NamedRun.emits S rho a.val_index (.attest a) ta ∧ ta < t ∧
          a.height_pair.erase.height? =
            some ((rho.storeBeforeTime S v t).core.h_max - 1) := by
  let pre := (rho.stateBeforeTime S t v).st
  have hlarge' : 1 < pre.core.h_max := by
    simpa only [pre, Run.storeBeforeTime] using hlarge
  obtain ⟨W, hW, hmaxW⟩ :=
    Proofs.NamedStoreBridge.maximum_carrier_stateBeforeTime S rho t v
  have hcross : pre.core.h_max - 1 <
      (Protocol.derive_named S.E S.cfg W).h := by
    rw [hmaxW]
    exact Nat.sub_lt (Nat.zero_lt_of_lt hlarge') (by decide)
  have hpositive : 1 ≤ pre.core.h_max - 1 :=
    Nat.le_sub_of_add_le (Nat.succ_le_iff.mpr hlarge')
  obtain ⟨X, hX, hXheight, Q, hQ, hwit⟩ :=
    NamedFinalityCertificates.height_crossing S.E S.cfg W
      (pre.core.h_max - 1) hpositive hcross
  obtain ⟨signer, hsignerQ, hsignerHonest⟩ :=
    HonestWeightMajority.exists_honest_member_of_quorum hmajority hQ
  obtain ⟨carrier, a, hcarrier, ha, hsigner, hmatch⟩ :=
    hwit signer hsignerQ
  have haHonest : a.val_index ∈ rho.honest := by
    rw [hsigner]
    exact hsignerHonest
  obtain ⟨n, hread, hbefore⟩ :=
    Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
      adm.toNamedScheduleWellFormed.sorted t
  have hWn : W ∈ (NamedRun.stateBefore S rho n v).st.bodies := by
    simpa only [hread] using hW
  obtain ⟨j, hj, received, hacc, hsend, hemit⟩ :=
    NamedOutageProvenance.honest_held_ancestor_row_emission S rho
      adm.toNamedUnforgeable n v hWn hcarrier ha haHonest
  obtain ⟨e, he, -, het⟩ := hacc.1.2
  have hreceived : received < t := by
    simpa only [het] using hbefore j e hj he
  have hta : S.a a.round < t := hsend.trans_lt hreceived
  have hheight :
      a.height_pair.erase.height? = some (pre.core.h_max - 1) := by
    cases hpair : a.height_pair with
    | empty =>
        have : False := by
          simpa only [hpair, NamedHeightPair.matchesEntry,
            Bool.false_eq_true] using hmatch
        exact this.elim
    | vote height entry timeout =>
        have hfields : height = pre.core.h_max - 1 ∧ entry = X.root := by
          simpa only [hpair, NamedHeightPair.matchesEntry,
            decide_eq_true_eq] using hmatch
        cases timeout <;>
          simp [hpair, NamedHeightPair.erase, HeightPair.height?, hfields.1]
  refine ⟨W, hW, Q, X, a, S.a a.round, hmaxW.symm.le, hQ, hX,
    ?_, haHonest, hemit, hta, hheight⟩
  exact Proofs.Bridges.erase_mem_chain_attestations W carrier hcarrier a ha

private theorem coreFrontierConfirmationWitness
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hmajority : HonestWeightMajority S rho.honest)
    {v : V} {time : Time}
    (hlarge : 1 < (rho.storeBeforeTime S v time).h_max) :
    ∃ (a : NamedAttestation V) (ta : Time) (D K : NamedBlock V),
      a.val_index ∈ rho.honest ∧
      NamedRun.emits S rho a.val_index (Object.attest a) ta ∧
      ta < time ∧
      a.height_pair.erase.height? =
        some ((rho.storeBeforeTime S v time).core.h_max - 1) ∧
      fgConfirmationWitness S
          (actionStoreAt S rho a.val_index a.round) =
        some (Protocol.derive_named S.E S.cfg K).T_h ∧
      D ∈ (actionStoreAt S rho a.val_index a.round).st.bodies ∧
      K ∈ (actionStoreAt S rho a.val_index a.round).st.bodies ∧
      K.erase = (Protocol.derive_named S.E S.cfg D).T_h ∧
      RunBlock S rho K ∧
      (Protocol.derive_named S.E S.cfg K).h =
        (rho.storeBeforeTime S v time).core.h_max - 1 ∧
      (Protocol.derive_named S.E S.cfg K).T_h = K.erase := by
  obtain ⟨W, hW, Q, X, a, ta, hmaxW, hQ, hXW, haW, haHon,
      hemit, hta, hheight⟩ :=
    coreFrontierQuorumWitness S adm hmajority hlarge
  obtain ⟨D, K, hfg, hD, -, hDheight, hK, hKentry,
      hKheight, hKpre, -⟩ :=
    coreHonestHeightRowConfirmationWitness S adm haHon hemit hheight
  have hKrun := coreActionBodyRunBlock S adm haHon hK
  have hDrun := coreActionBodyRunBlock S adm haHon hD
  have hKpreNamed := coreNamedPreceq_of_runBlock_erase_preceq
    S adm hKrun hDrun hKpre
  have hKtarget : (Protocol.derive_named S.E S.cfg K).T_h = K.erase := by
    exact (Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hKpreNamed
      (hKheight.trans hDheight.symm)).trans hKentry.symm
  exact ⟨a, ta, D, K, haHon, hemit, hta, hheight, hfg, hD, hK,
    hKentry, hKrun, hKheight, hKtarget⟩

private theorem coreHonestHeadProcessedAtNextDuty
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {s : Slot} (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {C H : Block V}
    (hvotes : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq C X))
    (hH : HonestHead S rho s H)
    {w : V} (hw : w ∈ rho.honest)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) C) :
    H ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s := by
  let duty := Proofs.Optimistic.voteDutyStore S rho w (s + 1)
  have hcutHor : Protocol.support_cutoff S.E s ≤ rho.horizon :=
    (support_cutoff_le_confirmation_time S.E s).trans hhor
  have havailable := coreHonestHeadsAvailable S adm hw hpost hcutHor
    hroot hvotes
  have hslot : duty.toHealing.s = s + 1 := by
    simpa only [duty, Proofs.Optimistic.toHealing_slot] using
      voteDutyStore_slot S rho w (s + 1)
  rcases havailable H hH with hgen | hadmit
  · subst H
    have hgenesis := genesis_mem_and_stamp_storeBeforeTime S
      adm.toNamedScheduleWellFormed w
      (Protocol.vote_time S.E (s + 1)) (Protocol.view_freeze S.E s)
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    rw [hslot, Nat.add_sub_cancel]
    exact ⟨by
      simpa only [duty, Proofs.Optimistic.voteDutyStore,
        Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore,
        Protocol.Store.toHealing] using hgenesis.1,
      Or.inl (by
        simpa only [duty, Proofs.Optimistic.voteDutyStore,
          Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore,
          Protocol.Store.toHealing] using hgenesis.2)⟩
  · have hvisible := admittedBefore_mem_and_stamp_at S
      adm.toNamedScheduleWellFormed hadmit
      (le_trans (le_of_lt (support_cutoff_lt_view_freeze S.E s))
        (le_of_lt (view_freeze_lt_vote_time_succ S.E s)))
    have hstampCut : stampedBefore duty.toHealing.toFG.toSG.toGoldfishStore.timestamp_block
        (Protocol.support_cutoff S.E s) H = true := by
      simpa only [duty, Proofs.Optimistic.voteDutyStore,
        Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore,
        Protocol.Store.toHealing] using hvisible.2
    have hstampFreeze :
        stampedBefore duty.toHealing.toFG.toSG.toGoldfishStore.timestamp_block
          (Protocol.view_freeze S.E s) H = true := by
      rw [stampedBefore_eq_occurrenceBefore] at hstampCut ⊢
      exact occurrenceBefore_mono
        (le_of_lt (support_cutoff_lt_view_freeze S.E s)) hstampCut
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    rw [hslot, Nat.add_sub_cancel]
    exact ⟨by
      simpa only [duty, Proofs.Optimistic.voteDutyStore,
        Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore,
        Protocol.Store.toHealing] using hvisible.1, Or.inl hstampFreeze⟩

private theorem coreHonestHeadProcessedAtNextDuty_of_delivery
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {cap : Time} (hdelivery : HonestDeliveryBefore S rho cap)
    {s : Slot} (hcap : Protocol.confirmation_time S.E s ≤ cap)
    {C H : Block V}
    (hvotes : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq C X))
    (hH : HonestHead S rho s H)
    {w : V} (hw : w ∈ rho.honest)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) C) :
    H ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s := by
  let duty := Proofs.Optimistic.voteDutyStore S rho w (s + 1)
  have havailable := honestHeadsAvailableBefore_of_delivery_atVoteDuty
    S adm hdelivery hw
      ((support_cutoff_le_confirmation_time S.E s).trans hcap) hroot hvotes
  have hslot : duty.toHealing.s = s + 1 := by
    simpa only [duty, Proofs.Optimistic.toHealing_slot] using
      voteDutyStore_slot S rho w (s + 1)
  rcases havailable H hH with hgen | hadmit
  · subst H
    have hgenesis := genesis_mem_and_stamp_storeBeforeTime S
      adm.toNamedScheduleWellFormed w
      (Protocol.vote_time S.E (s + 1)) (Protocol.view_freeze S.E s)
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    rw [hslot, Nat.add_sub_cancel]
    exact ⟨by
      simpa only [duty, Proofs.Optimistic.voteDutyStore,
        Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore,
        Protocol.Store.toHealing] using hgenesis.1,
      Or.inl (by
        simpa only [duty, Proofs.Optimistic.voteDutyStore,
          Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore,
          Protocol.Store.toHealing] using hgenesis.2)⟩
  · have hvisible := admittedBefore_mem_and_stamp_at S
      adm.toNamedScheduleWellFormed hadmit
      (le_trans (le_of_lt (support_cutoff_lt_view_freeze S.E s))
        (le_of_lt (view_freeze_lt_vote_time_succ S.E s)))
    have hstampCut : stampedBefore duty.toHealing.toFG.toSG.toGoldfishStore.timestamp_block
        (Protocol.support_cutoff S.E s) H = true := by
      simpa only [duty, Proofs.Optimistic.voteDutyStore,
        Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore,
        Protocol.Store.toHealing] using hvisible.2
    have hstampFreeze : stampedBefore duty.toHealing.toFG.toSG.toGoldfishStore.timestamp_block
        (Protocol.view_freeze S.E s) H = true := by
      rw [stampedBefore_eq_occurrenceBefore] at hstampCut ⊢
      exact occurrenceBefore_mono
        (le_of_lt (support_cutoff_lt_view_freeze S.E s)) hstampCut
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    rw [hslot, Nat.add_sub_cancel]
    exact ⟨by
      simpa only [duty, Proofs.Optimistic.voteDutyStore,
        Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore,
        Protocol.Store.toHealing] using hvisible.1, Or.inl hstampFreeze⟩

private theorem coreOpeningNextLeOfActionBeforeNextVote
    (S : Setup V) {r : Round} {s : Slot}
    (h : S.a r < Protocol.vote_time S.E (s + 1)) :
    S.hc.opening_slot r + 1 ≤ s := by
  change S.hc.a S.E.Δ r < Protocol.vote_time S.E (s + 1) at h
  rw [Protocol.a_eq_support_cutoff_succ S.hc S.E r] at h
  by_contra hn
  have hs : s + 1 ≤ S.hc.opening_slot r + 1 :=
    Nat.succ_le_of_lt (Nat.lt_of_not_ge hn)
  have hvote : Protocol.vote_time S.E (s + 1) <
      Protocol.support_cutoff S.E (s + 1) := by
    rw [← vote_time_add_delta]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  exact (not_lt_of_ge (le_of_lt h))
    (hvote.trans_le (support_cutoff_mono S.E hs))

private theorem coreActionLeSupportCutoff
    (S : Setup V) {r : Round} {s : Slot}
    (h : S.a r < Protocol.vote_time S.E (s + 1)) :
    S.a r ≤ Protocol.support_cutoff S.E s := by
  change S.hc.a S.E.Δ r ≤ Protocol.support_cutoff S.E s
  rw [Protocol.a_eq_support_cutoff_succ S.hc S.E r]
  exact support_cutoff_mono S.E
    (coreOpeningNextLeOfActionBeforeNextVote S h)

private theorem coreActionBlockProcessedAtNextDuty
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {u w : V} (hu : u ∈ rho.honest) (hw : w ∈ rho.honest)
    {r : Round} {s : Slot} {T : NamedBlock V}
    (hmem : T ∈ (actionStoreAt S rho u r).st.bodies)
    (haction : S.a r < Protocol.vote_time S.E (s + 1))
    (hpost : S.E.t_GST ≤ Protocol.support_cutoff S.E s)
    (hhor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG)
      T.erase) :
    T.erase ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s := by
  let action := actionStoreAt S rho u r
  let pre := rho.storeBeforeTime S u (S.a r)
  have htree : action.st.core.T = pre.core.T := by
    change (Protocol.update_confirmation_with
      (NamedProfile.gradeContract action.cache) S.E S.hc pre.core
      (S.E.slotOf (S.a r) - 1)).T = pre.core.T
    rfl
  have hpre : T.erase ∈ pre.core.T := by
    rw [← htree, (coreActionStoreCoherent S u r).1]
    exact Finset.mem_image.mpr ⟨T, hmem, rfl⟩
  have hcut := coreActionLeSupportCutoff S haction
  have hfreezeVote :=
    le_of_lt (view_freeze_lt_vote_time_succ S.E s)
  have hrelay : T.erase = Block.genesis ∨
      AdmittedBefore S rho w T.erase (Protocol.view_freeze S.E s) := by
    rcases block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTime S
        adm.toNamedScheduleWellFormed u (S.a r) hpre with
      hgen | ⟨D, i, t, hDeq, hacc, ht⟩
    · exact Or.inl hgen
    · right
      have hrootD : Block.Preceq
          (Protocol.get_fg_root
            (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG)
          D.erase := by
        simpa only [hDeq] using hroot
      have hFhist : BlockFinalizedBelowAtDeliveriesBefore S rho w D
          (Protocol.view_freeze S.E s) := by
        intro j hj
        have hjVote := hj.trans (strict_filter_length_mono rho
          (le_of_lt (view_freeze_lt_vote_time_succ S.E s)))
        have hroot' : Block.Preceq
            (Protocol.get_fg_root
              (rho.storeBeforeTime S w (Protocol.vote_time S.E (s + 1))).toHealing.toFG)
              D.erase := by
          simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
            Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
            Proofs.Optimistic.tickStore] using hrootD
        exact finalized_preceq_at_prefix_of_storeBeforeRoot_preceq
          S rho adm.toNamedScheduleWellFormed.sorted hroot' hjVote
      have hadmit := coreBlockAdmittedAfterCutoff S adm hu hw
        (by
          rw [← Proofs.NamedWire.erase_slot D]
          exact Nat.zero_lt_of_lt
            (parent_slot_lt_of_acceptsAt_block S hacc))
        hacc (ht.trans_le hcut) hpost
        (support_cutoff_add_delta_eq_view_freeze S.E s)
        (hfreezeVote.trans hhor) hFhist
      simpa only [hDeq] using hadmit
  have hvis : T.erase ∈
      (rho.storeBeforeTime S w (Protocol.vote_time S.E (s + 1))).T ∧
      stampedBefore
        (rho.storeBeforeTime S w
          (Protocol.vote_time S.E (s + 1))).timestamp_block
        (Protocol.view_freeze S.E s) T.erase = true := by
    rcases hrelay with hgen | hadmit
    · simpa only [hgen] using
        (genesis_mem_and_stamp_storeBeforeTime S
          adm.toNamedScheduleWellFormed w
          (Protocol.vote_time S.E (s + 1))
          (Protocol.view_freeze S.E s))
    · exact admittedBefore_mem_and_stamp_at S
        adm.toNamedScheduleWellFormed hadmit hfreezeVote
  have hslot :
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s = s + 1 :=
    voteDutyStore_slot S rho w (s + 1)
  simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
  rw [hslot, Nat.add_sub_cancel]
  exact ⟨by
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hvis.1,
    Or.inl (by
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hvis.2)⟩

private theorem coreActionBlockProcessedAtNextDuty_of_delivery
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {cap : Time} (hdelivery : HonestDeliveryBefore S rho cap)
    {u w : V} (hu : u ∈ rho.honest) (hw : w ∈ rho.honest)
    {r : Round} {s : Slot} {T : NamedBlock V}
    (hmem : T ∈ (actionStoreAt S rho u r).st.bodies)
    (haction : S.a r < Protocol.vote_time S.E (s + 1))
    (hcap : Protocol.confirmation_time S.E s ≤ cap)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG)
      T.erase) :
    T.erase ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s := by
  have hpre : T ∈
      (NamedRun.stateBeforeTime S rho (S.a r) u).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hmem
  let early := Protocol.view_freeze S.E s
  let target := Protocol.vote_time S.E (s + 1)
  have hdeadline : S.a r + S.E.Δ ≤ early := by
    have hcut := coreActionLeSupportCutoff S haction
    have := Int.add_le_add_right hcut S.E.Δ
    rw [support_cutoff_add_delta_eq_view_freeze S.E s] at this
    exact this
  have horder : early ≤ target :=
    (view_freeze_lt_vote_time_succ S.E s).le
  have hhealthy : early ≤ cap := by
    apply horder.trans
    apply le_trans ?_ hcap
    dsimp only [target]
    rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
    exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
  have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
    S rho target w
  have hFroot : Block.Preceq
      (NamedRun.stateBeforeTime S rho target w).st.core.F
      (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) := by
    have h := Proofs.Records.preceq_get_fg_root_of_F
      (st := (NamedRun.stateBeforeTime S rho target w).st.core.toHealing.toFG) hFJ
    simpa only [target, voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using h
  obtain ⟨hheld, hstamp, -⟩ := NamedHealthyHeadReady.healthy_head_body_at_read
    S rho adm cap hdelivery u hu w hw T (S.a r) early target hpre
    hdeadline horder hhealthy (Block.preceq_trans hFroot hroot)
  have hslot :
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s = s + 1 :=
    voteDutyStore_slot S rho w (s + 1)
  simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
  rw [hslot, Nat.add_sub_cancel]
  exact ⟨by
    have hinv := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho target w).1.1.1
    have hcore : T.erase ∈
        (NamedRun.stateBeforeTime S rho target w).st.core.T := by
      rw [hinv.1]
      exact Finset.mem_image_of_mem NamedBlock.erase hheld
    simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, Run.storeBeforeTime, Protocol.Store.toHealing] using hcore,
    Or.inl (by
      simpa only [target, early, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime,
        Protocol.Store.toHealing] using hstamp)⟩

/-- A named action body below the next vote-duty FG root is processed under
bounded healthy-prefix delivery. -/
theorem actionBlockProcessedAtNextDuty_of_delivery
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {cap : Time} (hdelivery : HonestDeliveryBefore S rho cap)
    {u w : V} (hu : u ∈ rho.honest) (hw : w ∈ rho.honest)
    {r : Round} {s : Slot} {T : NamedBlock V}
    (hmem : T ∈ (actionStoreAt S rho u r).st.bodies)
    (haction : S.a r < Protocol.vote_time S.E (s + 1))
    (hcap : Protocol.confirmation_time S.E s ≤ cap)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG)
      T.erase) :
    T.erase ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s :=
  coreActionBlockProcessedAtNextDuty_of_delivery
    S adm hdelivery hu hw hmem haction hcap hroot

#print axioms actionBlockProcessedAtNextDuty_of_delivery

private theorem coreStoredHeightAtVoteDuty
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot} {X : NamedBlock V}
    (hXrun : RunBlock S rho X)
    (hXmem : X.erase ∈ (voteDutyRead S rho w s).st.core.T) :
    ((voteDutyRead S rho w s).st.core.σ X.erase).h =
      (Protocol.derive_named S.E S.cfg X).h := by
  obtain ⟨X', hX', hX'erase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (Protocol.vote_time S.E s) w (by
        simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock] using hXmem)
  have hX'run : RunBlock S rho X' := by
    obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
      adm.toNamedScheduleWellFormed.sorted (Protocol.vote_time S.E s)
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw
    change X' ∈ (NamedRun.stateBefore S rho i w).st.bodies
    rw [← hi]
    exact hX'
  have hX'eq : X' = X :=
    adm.toNamedRootCollisionFree.root_injective X' X hX'run hXrun X' X
      (Or.inl (Proofs.NamedAncestry.named_self X'))
      (Or.inr (Proofs.NamedAncestry.named_self X)) (by
        rw [← Proofs.NamedWire.erase_root X', ← Proofs.NamedWire.erase_root X,
          hX'erase])
  have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime
    S rho (Protocol.vote_time S.E s) w X (by
      simpa only [hX'eq] using hX')
  simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom,
    Protocol.NamedStore.setClock] using congrArg (fun st => st.h) hview

private theorem coreCandidatePathOfBandDescendant
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot} {C D : Block V}
    (hCD : Block.Preceq C D)
    (hDprocessed : D ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s)
    (hband : (voteDutyRead S rho w (s + 1)).st.core.h_max - 1 ≤
      ((voteDutyRead S rho w (s + 1)).st.core.σ D).h)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) C) :
    C ∈ voterCandidateTreeAt S rho w (s + 1) ∧
      ∀ B : Block V,
        Block.Preceq (voterAnchorAt S rho w (s + 1)) B →
        B ≠ voterAnchorAt S rho w (s + 1) →
        Block.Preceq B C → B ≠ C →
        B ∈ voterCandidateTreeAt S rho w (s + 1) := by
  let read := voteDutyRead S rho w (s + 1)
  have hDread : D ∈ Protocol.voter_processed_block_tree S.E
      read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s := by
    simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
      Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hDprocessed
  have hancestor : ∀ B : Block V, Block.Preceq B D →
      B ∈ Protocol.voter_processed_block_tree S.E
        read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s := by
    intro B hBD
    have hanc := ancestorProcessed_of_voterProcessed S adm hw
      (s := s) (B := D) hDprocessed B hBD
    simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
      Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hanc
  have hFroot : Block.Preceq read.st.core.F
      (Protocol.get_fg_root read.st.core.toHealing.toFG) :=
    Proofs.Records.preceq_get_fg_root_of_F (st := read.st.core.toHealing.toFG) (by
      simpa only [read, voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock] using
          (Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
            S rho (Protocol.vote_time S.E (s + 1)) w))
  have hmem : ∀ B : Block V,
      Block.Preceq
        (Protocol.get_fg_root read.st.core.toHealing.toFG) B →
      Block.Preceq B C →
      B ∈ voterCandidateTreeAt S rho w (s + 1) := by
    intro B hrootB hBC
    change B ∈ Protocol.get_filtered_block_tree_from
      read.st.core.toHealing.toFG
      (Protocol.voter_processed_block_tree S.E
        read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
    simp only [Protocol.get_filtered_block_tree_from,
      Protocol.viable_tree, Protocol.finalized_descendants,
      Protocol.viable, Finset.mem_filter, decide_eq_true_eq]
    exact ⟨⟨⟨hancestor B (Block.preceq_trans hBC hCD),
      Block.preceq_trans hFroot hrootB⟩,
      D, hDread, Block.preceq_trans hBC hCD, hband⟩, hrootB⟩
  refine ⟨hmem C hroot (Block.preceq_self C), ?_⟩
  intro B hAB _ hBC _
  have hrootAnchor : Block.Preceq
      (Protocol.get_fg_root read.st.core.toHealing.toFG)
      (voterAnchorAt S rho w (s + 1)) :=
    NamedOutageClosure.fg_root_preceq_anchor S.E S.hc
      read.st.core.toHealing (S.hc.round_of read.st.core.s)
      (DecoupledConsensusModel.Protocol.readFrame read.cache read.st.core.toHealing
        (S.hc.round_of read.st.core.s)).g1
  exact hmem B (Block.preceq_trans hrootAnchor hAB) hBC


private theorem coreConeBandDescendant_of_processed
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    (hmajority : HonestWeightMajority S rho.honest)
    {s : Slot} {C : Block V}
    (hvotes : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq C X))
    {w : V} (hw : w ∈ rho.honest)
    (hwitnesses : ∀ {C' : NamedBlock V}, C'.erase = C →
      (Protocol.derive_named S.E S.cfg C').h <
        (voteDutyRead S rho w (s + 1)).st.core.h_max - 1 →
      RunBlock S rho C' →
      (∀ (a : NamedAttestation V) (ta : Time) (K : NamedBlock V),
        a.val_index ∈ rho.honest →
        NamedRun.emits S rho a.val_index (Object.attest a) ta →
        ta < Protocol.vote_time S.E (s + 1) →
        a.height_pair.erase.height? =
          some ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).h_max - 1) →
        fgConfirmationWitness S
          (actionStoreAt S rho a.val_index a.round) =
          some (Protocol.derive_named S.E S.cfg K).T_h →
        RunBlock S rho K →
        Block.compatible C'.erase
          (Protocol.derive_named S.E S.cfg K).T_h = true))
    (hheadProcessed : ∀ {X : Block V}, HonestHead S rho s X →
      X ∈ Protocol.voter_processed_block_tree S.E
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s)
    (hblockProcessed : ∀ {u : V}, u ∈ rho.honest →
      ∀ {r : Round} {T : NamedBlock V},
      T ∈ (actionStoreAt S rho u r).st.bodies →
      S.a r < Protocol.vote_time S.E (s + 1) →
      Block.Preceq
        (Protocol.get_fg_root
          (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG)
        T.erase →
      T.erase ∈ Protocol.voter_processed_block_tree S.E
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) C) :
    ∃ D : Block V, Block.Preceq C D ∧
      D ∈ Protocol.voter_processed_block_tree S.E
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s ∧
      (voteDutyRead S rho w (s + 1)).st.core.h_max - 1 ≤
        ((voteDutyRead S rho w (s + 1)).st.core.σ D).h := by
  let read := voteDutyRead S rho w (s + 1)
  have hpositive : 0 < ((S.E.committee s) ∩ rho.honest).card := by
    have hc := hcom s
    omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpositive
  have huHon : u ∈ rho.honest := (Finset.mem_inter.mp hu).2
  have huCommittee : u ∈ S.E.committee s :=
    (Finset.mem_inter.mp hu).1
  obtain ⟨X, hCX, hXrun, hXemit⟩ :=
    hvotes u huHon huCommittee
  obtain ⟨Cn, hCnX, hCnErase⟩ :=
    Proofs.NamedAncestry.erased_ancestor_lift X hCX
  have hCnrun : RunBlock S rho Cn :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hXrun hCnX
  by_cases hband : read.st.core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg Cn).h
  · have hhead : HonestHead S rho s X.erase :=
      ⟨u, huHon, huCommittee, ⟨X, rfl, hXrun⟩, hXemit⟩
    have hprocessed := hheadProcessed hhead
    have hXmem : X.erase ∈ read.st.core.T := by
      have hmem := (Finset.mem_filter.mp hprocessed).1
      simpa only [read, voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
        Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hmem
    have hheight := coreStoredHeightAtVoteDuty S adm hw
      (s := s + 1) (X := X) hXrun hXmem
    have hheightCX :=
      Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hCnX
    refine ⟨X.erase, hCX, hprocessed, ?_⟩
    change read.st.core.h_max - 1 ≤
      (read.st.core.σ X.erase).h
    have hheight' : (read.st.core.σ X.erase).h =
        (Protocol.derive_named S.E S.cfg X).h := by
      simpa only [read] using hheight
    rw [hheight']
    exact hband.trans hheightCX
  · have hhigh : (Protocol.derive_named S.E S.cfg Cn).h <
        read.st.core.h_max - 1 := Nat.lt_of_not_ge hband
    have hlarge : 1 < (rho.storeBeforeTime S w
        (Protocol.vote_time S.E (s + 1))).core.h_max := by
      by_contra hn
      have hzero :
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).h_max - 1 = 0 :=
        Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hn)
      have hhighOld : (Protocol.derive_named S.E S.cfg Cn).h <
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).h_max - 1 := by
        simpa only [read, voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
          Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hhigh
      rw [hzero] at hhighOld
      exact Nat.not_lt_zero _ hhighOld
    obtain ⟨a, ta, D, K, ha, hemit, hta, hrow, hselected,
        hDmem, hKmem, hKentry, hKrun, hKheight, hKtarget⟩ :=
      coreFrontierConfirmationWitness S adm hmajority hlarge
    have hrawCompatible : Block.compatible Cn.erase K.erase = true := by
      simpa only [hCnErase, hKtarget] using
        ((hwitnesses hCnErase hhigh hCnrun) a ta K ha hemit hta hrow hselected hKrun)
    have hcompatible : NamedBlock.compatible Cn K = true :=
      by
        have hcases : Block.Preceq Cn.erase K.erase ∨
            Block.Preceq K.erase Cn.erase := by
          simpa only [Block.compatible, Bool.or_eq_true] using hrawCompatible
        rcases hcases with hCK | hKC
        · have hnamed := coreNamedPreceq_of_runBlock_erase_preceq
            S adm hCnrun hKrun hCK
          simpa only [NamedBlock.compatible, Bool.or_eq_true] using
            (Or.inl hnamed)
        · have hnamed := coreNamedPreceq_of_runBlock_erase_preceq
            S adm hKrun hCnrun hKC
          simpa only [NamedBlock.compatible, Bool.or_eq_true] using
            (Or.inr hnamed)
    have hCnK : NamedBlock.Preceq Cn K := by
      have hcases : NamedBlock.Preceq Cn K ∨
          NamedBlock.Preceq K Cn := by
        simpa only [NamedBlock.compatible, Bool.or_eq_true]
          using hcompatible
      rcases hcases with hCK | hKC
      · exact hCK
      · have hmono :=
          Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hKC
        rw [hKheight] at hmono
        exact False.elim ((Nat.not_le_of_gt hhigh) hmono)
    have hprocessed := hblockProcessed ha hKmem
      (by simpa only [(emits_attest_shape S hemit).2] using hta)
      (Block.preceq_trans hroot (by
        simpa only [hCnErase] using Proofs.NamedWire.erase_preceq hCnK))
    have hKmemRead : K.erase ∈ read.st.core.T := by
      have hmem := (Finset.mem_filter.mp hprocessed).1
      simpa only [read, voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
        Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hmem
    have hheight := coreStoredHeightAtVoteDuty S adm hw
      (s := s + 1) (X := K) hKrun hKmemRead
    have hCK : Block.Preceq C K.erase := by
      simpa only [hCnErase] using Proofs.NamedWire.erase_preceq hCnK
    refine ⟨K.erase, hCK, hprocessed, ?_⟩
    change read.st.core.h_max - 1 ≤
      (read.st.core.σ K.erase).h
    have hheight' : (read.st.core.σ K.erase).h =
        (Protocol.derive_named S.E S.cfg K).h := by
      simpa only [read] using hheight
    rw [hheight']
    simpa only [read, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
      Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hKheight.ge














private theorem coreConeBandDescendant_of_runFrontier
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    (hmajority : HonestWeightMajority S rho.honest)
    {s : Slot} {C : Block V}
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hvotes : NamedHonestVotesCone S rho s (fun X => Block.Preceq C X))
    {w : V} (hw : w ∈ rho.honest)
    (hwitnesses : ∀ {C' : NamedBlock V}, C'.erase = C →
      (Protocol.derive_named S.E S.cfg C').h <
        (voteDutyRead S rho w (s + 1)).st.core.h_max - 1 →
      RunBlock S rho C' →
      (∀ (a : NamedAttestation V) (ta : Time) (K : NamedBlock V),
        a.val_index ∈ rho.honest →
        NamedRun.emits S rho a.val_index (Object.attest a) ta →
        ta < Protocol.vote_time S.E (s + 1) →
        a.height_pair.erase.height? =
          some ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).h_max - 1) →
        fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
          some (Protocol.derive_named S.E S.cfg K).T_h →
        RunBlock S rho K →
        Block.compatible C'.erase
          (Protocol.derive_named S.E S.cfg K).T_h = true))
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) C) :
    ∃ D : Block V, Block.Preceq C D ∧
      D ∈ Protocol.voter_processed_block_tree S.E
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s ∧
      (voteDutyRead S rho w (s + 1)).st.core.h_max - 1 ≤
        ((voteDutyRead S rho w (s + 1)).st.core.σ D).h := by
  apply coreConeBandDescendant_of_processed
    S adm hcom hmajority hvotes hw hwitnesses
  · intro X hhead
    exact coreHonestHeadProcessedAtNextDuty S adm hpost hhor
      hvotes hhead hw hroot
  · intro u hu r T hmem haction hrootT
    have hpostSupport : S.E.t_GST ≤ Protocol.support_cutoff S.E s := by
      apply hpost.trans (le_of_lt ?_)
      rw [← vote_time_add_delta]
      exact Int.lt_add_of_pos_right _ S.E.Δ_pos
    have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
      apply le_trans (le_of_lt ?_) hhor
      rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
      exact Int.lt_add_of_pos_right _ S.E.Δ_pos
    exact coreActionBlockProcessedAtNextDuty S adm hu hw hmem haction
      hpostSupport hvoteHor hrootT
  · exact hroot

private theorem coreConeBandDescendant_of_runFrontier_of_delivery
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {cap : Time} (hdelivery : HonestDeliveryBefore S rho cap)
    (hcom : HonestCommittees S rho.honest)
    (hmajority : HonestWeightMajority S rho.honest)
    {s : Slot} {C : Block V}
    (hcap : Protocol.confirmation_time S.E s ≤ cap)
    (hvotes : NamedHonestVotesCone S rho s (fun X => Block.Preceq C X))
    {w : V} (hw : w ∈ rho.honest)
    (hwitnesses : ∀ {C' : NamedBlock V}, C'.erase = C →
      (Protocol.derive_named S.E S.cfg C').h <
        (voteDutyRead S rho w (s + 1)).st.core.h_max - 1 →
      RunBlock S rho C' →
      (∀ (a : NamedAttestation V) (ta : Time) (K : NamedBlock V),
        a.val_index ∈ rho.honest →
        NamedRun.emits S rho a.val_index (Object.attest a) ta →
        ta < Protocol.vote_time S.E (s + 1) →
        a.height_pair.erase.height? =
          some ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).h_max - 1) →
        fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
          some (Protocol.derive_named S.E S.cfg K).T_h →
        RunBlock S rho K →
        Block.compatible C'.erase
          (Protocol.derive_named S.E S.cfg K).T_h = true))
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) C) :
    ∃ D : Block V, Block.Preceq C D ∧
      D ∈ Protocol.voter_processed_block_tree S.E
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s ∧
      (voteDutyRead S rho w (s + 1)).st.core.h_max - 1 ≤
        ((voteDutyRead S rho w (s + 1)).st.core.σ D).h := by
  apply coreConeBandDescendant_of_processed
    S adm hcom hmajority hvotes hw hwitnesses
  · intro X hhead
    exact coreHonestHeadProcessedAtNextDuty_of_delivery
      S adm hdelivery hcap hvotes hhead hw hroot
  · intro u hu r T hmem haction hrootT
    exact coreActionBlockProcessedAtNextDuty_of_delivery
      S adm hdelivery hu hw hmem haction hcap hrootT
  · exact hroot

/- A named frontier callback only needs to cover named blocks that are in the
   run. The core band proof supplies that fact for the selected frontier, so
   this is the additive bridge from raw recent-source compatibility. -/
theorem goldfishCone_succ_of_runFrontierWitnesses
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    (hmajority : HonestWeightMajority S rho.honest)
    {s : Slot} {C : Block V} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hvotes : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq C X))
    (hwitnesses : ∀ w ∈ rho.honest, ∀ {C' : NamedBlock V},
      C'.erase = C →
      (Protocol.derive_named S.E S.cfg C').h <
        (voteDutyRead S rho w (s + 1)).st.core.h_max - 1 →
      RunBlock S rho C' →
      (∀ (a : NamedAttestation V) (ta : Time) (K : NamedBlock V),
        a.val_index ∈ rho.honest →
        NamedRun.emits S rho a.val_index (Object.attest a) ta →
        ta < Protocol.vote_time S.E (s + 1) →
        a.height_pair.erase.height? =
          some ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).h_max - 1) →
        fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
          some (Protocol.derive_named S.E S.cfg K).T_h →
        RunBlock S rho K →
        Block.compatible C'.erase
          (Protocol.derive_named S.E S.cfg K).T_h = true))
    (hroots : ∀ w ∈ rho.honest, Block.compatible
      (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) C = true)
    (hanchors : ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w (s + 1)) C = true) :
    (∀ w ∈ rho.honest,
      Block.Preceq C (voterHeadAt S rho w (s + 1))) ∧
      NamedHonestVotesCone S rho (s + 1)
        (fun X => Block.Preceq C X) := by
  have hinputs : ∀ w ∈ rho.honest,
      GoldfishConeVoteInputs' S rho s C w := by
    intro w hw
    refine { rootSide := ?_, anchor := hanchors w hw }
    have hcases :
        Block.Preceq
            (Protocol.get_fg_root
              (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) C ∨
          Block.Preceq C
            (Protocol.get_fg_root
              (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) := by
      simpa only [Block.compatible, Bool.or_eq_true] using hroots w hw
    rcases hcases with hroot | habove
    · obtain ⟨D, hCD, hprocessed, hband⟩ :=
        coreConeBandDescendant_of_runFrontier S adm hcom hmajority hpost hhor
          hvotes hw
          (fun hCerase hCheight hCrun a ta K ha hemit hta hrow hselected hKrun =>
            (hwitnesses w hw hCerase hCheight hCrun a ta K ha hemit hta hrow
              hselected hKrun)) hroot
      exact Or.inl ⟨hroot,
        coreCandidatePathOfBandDescendant S adm hw hCD hprocessed
          hband hroot⟩
    · exact Or.inr habove
  have hheads : ∀ w ∈ rho.honest,
      Block.Preceq C (voterHeadAt S rho w (s + 1)) := fun w hw =>
    goldfishCone_step' S adm hcom hs hpost hhor hvotes hw
      (hinputs w hw)
  refine ⟨hheads, ?_⟩
  have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
    apply le_trans (le_of_lt ?_) hhor
    rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  intro w hw hcommittee
  obtain ⟨X, hXe, hXrun, hXemit⟩ :=
    coreVoterHeadEmits S adm hw (Nat.succ_pos s)
      hcommittee hvoteHor
  exact ⟨X, hXe ▸ hheads w hw, hXrun, hXemit⟩

#print axioms goldfishCone_succ_of_runFrontierWitnesses

/-- Delivery-parametric twin of
`goldfishCone_succ_of_runFrontierWitnesses`. -/
theorem goldfishCone_succ_of_runFrontierWitnesses_of_delivery
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {cap : Time} (hdelivery : HonestDeliveryBefore S rho cap)
    (hcom : HonestCommittees S rho.honest)
    (hmajority : HonestWeightMajority S rho.honest)
    {s : Slot} {C : Block V} (hs : 0 < s)
    (hcap : Protocol.confirmation_time S.E s ≤ cap)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hvotes : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq C X))
    (hwitnesses : ∀ w ∈ rho.honest, ∀ {C' : NamedBlock V},
      C'.erase = C →
      (Protocol.derive_named S.E S.cfg C').h <
        (voteDutyRead S rho w (s + 1)).st.core.h_max - 1 →
      RunBlock S rho C' →
      (∀ (a : NamedAttestation V) (ta : Time) (K : NamedBlock V),
        a.val_index ∈ rho.honest →
        NamedRun.emits S rho a.val_index (Object.attest a) ta →
        ta < Protocol.vote_time S.E (s + 1) →
        a.height_pair.erase.height? =
          some ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).h_max - 1) →
        fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
          some (Protocol.derive_named S.E S.cfg K).T_h →
        RunBlock S rho K →
        Block.compatible C'.erase
          (Protocol.derive_named S.E S.cfg K).T_h = true))
    (hroots : ∀ w ∈ rho.honest, Block.compatible
      (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) C = true)
    (hanchors : ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w (s + 1)) C = true) :
    (∀ w ∈ rho.honest,
      Block.Preceq C (voterHeadAt S rho w (s + 1))) ∧
      NamedHonestVotesCone S rho (s + 1)
        (fun X => Block.Preceq C X) := by
  have hinputs : ∀ w ∈ rho.honest,
      GoldfishConeVoteInputs' S rho s C w := by
    intro w hw
    refine { rootSide := ?_, anchor := hanchors w hw }
    have hcases :
        Block.Preceq
            (Protocol.get_fg_root
              (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) C ∨
          Block.Preceq C
            (Protocol.get_fg_root
              (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) := by
      simpa only [Block.compatible, Bool.or_eq_true] using hroots w hw
    rcases hcases with hroot | habove
    · obtain ⟨D, hCD, hprocessed, hband⟩ :=
        coreConeBandDescendant_of_runFrontier_of_delivery
          S adm hdelivery hcom hmajority hcap hvotes hw
          (fun hCerase hCheight hCrun a ta K ha hemit hta hrow hselected hKrun =>
            hwitnesses w hw hCerase hCheight hCrun a ta K ha hemit hta hrow
              hselected hKrun) hroot
      exact Or.inl ⟨hroot,
        coreCandidatePathOfBandDescendant S adm hw hCD hprocessed
          hband hroot⟩
    · exact Or.inr habove
  have hheads : ∀ w ∈ rho.honest,
      Block.Preceq C (voterHeadAt S rho w (s + 1)) := fun w hw =>
    goldfishCone_step_of_delivery S adm hdelivery hcom hs hcap
      hvotes hw (hinputs w hw)
  refine ⟨hheads, ?_⟩
  have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
    apply le_trans (le_of_lt ?_) hhor
    rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  intro w hw hcommittee
  obtain ⟨X, hXe, hXrun, hXemit⟩ :=
    coreVoterHeadEmits S adm hw (Nat.succ_pos s)
      hcommittee hvoteHor
  exact ⟨X, hXe ▸ hheads w hw, hXrun, hXemit⟩

#print axioms goldfishCone_succ_of_runFrontierWitnesses_of_delivery






#print axioms goldfishCone_step'
#print axioms headsResolveIn_confStore_of_postHealingCone
#print axioms canonicalSuffixHonestVoteCounted_core

end WeakGoldfish
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
