module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ExcludesRefute
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.WeakConfirmationSupport
public import DecoupledConsensusProofs.Protocol.Schedule.WeakConfirmationTransport
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.WeakFrontierCandidate
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FGWitnessCandidate
public import DecoupledConsensusProofs.Protocol.Schedule.WeakGoldfishCone
public import DecoupledConsensusProofs.Execution.PreparedReadBridge
public import DecoupledConsensusProofs.Protocol.Grades.WeakConfirmationAdoption
public import DecoupledConsensusProofs.Protocol.Grades.SafetySlotInduction

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakGoldfish

open Internal Execution
open Internal.NamedRecoveryRead
open Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem candidatePath_of_processedBandDescendant_local
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
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using
      hDprocessed
  have hancestor : ∀ B : Block V, Block.Preceq B D →
      B ∈ Protocol.voter_processed_block_tree S.E
        read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s := by
    intro B hBD
    have hanc := ancestorProcessed_of_voterProcessed S adm hw
      (s := s) (B := D) hDprocessed B hBD
    simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using
      hanc
  have hFroot : Block.Preceq read.st.core.F
      (Protocol.get_fg_root read.st.core.toHealing.toFG) :=
    Proofs.Records.preceq_get_fg_root_of_F (st := read.st.core.toHealing.toFG) (by
      simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
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

private theorem namedHeight_at_voteDuty
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot} {X : NamedBlock V}
    (hXrun : NamedRun.blockInRun S rho X)
    (hXmem : X.erase ∈ (voteDutyRead S rho w s).st.core.T) :
    ((voteDutyRead S rho w s).st.core.σ X.erase).h =
      (Protocol.derive_named S.E S.cfg X).h := by
  obtain ⟨X', hX', hX'erase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (Protocol.vote_time S.E s) w (by
        simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
          hXmem)
  have hX'run : NamedRun.blockInRun S rho X' := by
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
  have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho
    (Protocol.vote_time S.E s) w X (by
      simpa only [hX'eq] using hX')
  simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
    congrArg (fun st => st.h) hview

private theorem get_head_in_tree_with_captures_of_confirmation
    (contract : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (target : Protocol.HealingStore V)
    (sourceTree tree : Finset (Block V))
    (sourceEarly sourceLate sourceVotes targetVotes targetSupport :
      Finset (GoldfishVote V)) (s : Slot) {B : Block V}
    (hN : Numerator sourceEarly sourceLate sourceVotes)
    (hT : AdoptionTransport sourceTree target.T sourceVotes sourceLate
      targetVotes targetSupport B)
    (heligible : Protocol.voters_count E sourceLate s <
      2 * Protocol.goldfish_score E sourceTree sourceVotes sourceVotes s B)
    (hsub : targetSupport ⊆ targetVotes)
    (hcompatible : Block.compatible
      ((contract.read E hc target (hc.round_of target.s)).anchor) B = true)
    (hpath : Block.Preceq (contract.read E hc target (hc.round_of target.s)).anchor B →
      ∀ C : Block V,
        Block.Preceq (contract.read E hc target (hc.round_of target.s)).anchor C →
        C ≠ (contract.read E hc target (hc.round_of target.s)).anchor →
        Block.Preceq C B → C ∈ tree) :
    Block.Preceq B
      (Protocol.get_head_in_tree_with_layer contract E hc target tree targetVotes
        targetSupport s) := by
  rw [Proofs.Optimistic.get_head_in_tree_split_with]
  exact Protocol.goldfish_fork_choice_captures_of_confirmation
    E target.σ target.h_max sourceTree target.T tree target.s
    sourceEarly sourceLate sourceVotes targetVotes targetSupport s hN hT
    heligible hsub hcompatible hpath

private theorem finalized_preceq_at_delivery_local
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

private theorem voterHeadMem_of_core
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
      (NamedRun.stateBeforeTime S rho (Protocol.vote_time S.E d) w).st :=
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
      (NamedRun.stateBeforeTime S rho
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

omit [Fintype V] in
private theorem namedPreceqSelf_local
    (B : NamedBlock V) : NamedBlock.Preceq B B := by
  cases B <;> simp [NamedBlock.Preceq, NamedBlock.preceq]

private theorem noGeometryAlias_local
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
    (Or.inl (namedPreceqSelf_local C))
    (Or.inr (namedPreceqSelf_local B)) hroot
  exact hnot (by simpa only [hCB] using hC)

private theorem stateBeforeSlotClock_local
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

private theorem proposalTimeLeOfAccepts_local
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
    rw [stateBeforeSlotClock_local S rho i v] at hfuture
    have hmono : Protocol.proposal_time S.E B.erase.slot ≤
        Protocol.proposal_time S.E
          (S.E.slotOf (NamedRun.stateBefore S rho i v).st.core.t) :=
      proposal_time_mono S.E (Nat.not_lt.mp hfuture)
    refine le_trans hmono (le_trans
      (proposal_time_slotOf_le S.E
        (stateBefore_store_time_nonneg S adm.toNamedScheduleWellFormed v i)) ?_)
    exact store_time_le_event_time S adm.toNamedScheduleWellFormed hi v

private theorem notFutureOfDelivery_local
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
  rw [stateBeforeSlotClock_local S rho i v]
  exact Nat.not_lt.mpr (slot_le_slotOf_of_proposal_time_le S.E hclock)

private theorem onBlockWithBodies_local
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

private theorem handlerInserts_local
    (S : Setup V) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st)
    (hp : B.parent ∈ st.bodies) (hfresh : B.erase ∉ st.core.T)
    (hslot : B.erase.slot ≤ st.core.s)
    (hF : Block.Preceq st.core.F B.erase)
    (hproposer : B.erase.proposer? = some (S.E.proposer B.erase.slot))
    (hparent : B.erase.parent.slot < B.erase.slot)
    (hcarried : Protocol.carried_attestations_admissible S.hc B.erase = true) :
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
  rw [onBlockWithBodies_local]
  unfold Protocol.NamedStore.process_block_core
  rw [if_neg (not_not.mpr hp)]
  unfold Protocol.NamedStore.commitBlock
  rw [if_pos ⟨hfresh, hafter⟩]
  exact Finset.mem_insert_self _ _

private theorem acceptsAtDeliveryGuards_local
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} {i : Nat} {B : NamedBlock V} {t : Time}
    (hi : rho.events[i]? = some (Event.deliver v (Object.block B) t))
    (hslot : ¬ (NamedRun.stateBefore S rho i v).st.core.s < B.erase.slot)
    (hF : Block.Preceq
      (NamedRun.stateBefore S rho i v).st.core.F B.erase)
    (hproposer : B.erase.proposer? = some (S.E.proposer B.erase.slot))
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
    noGeometryAlias_local S rho adm.toNamedRootCollisionFree i v hv B hscope
      hfresh
  have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho i v).1.1.1
  have hnew := handlerInserts_local S
    (NamedRun.stateBefore S rho i v).st B hcoh hparent hlegacyFresh
    (Nat.not_lt.mp hslot) hF hproposer hparentSlot hattestations
  refine ⟨⟨Or.inr ⟨t, hi⟩, Event.deliver v (Object.block B) t,
    hi, rfl, rfl⟩, ?_, ?_⟩
  · simpa only [NamedReceipt.processed, decide_eq_false_iff_not]
      using hfresh
  · have hstate : (NamedRun.stateBefore S rho (i + 1) v).st =
        NamedReceipt.process S (NamedRun.stateBefore S rho i v).st
          (Object.block B) := Proofs.NamedReceiptCallsBase.delivery_result S rho hi
    rw [hstate]
    simpa only [NamedReceipt.process, NamedReceipt.processed,
      decide_eq_true_eq] using hnew

private theorem acceptsAtProposedBlock_local
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
          (S.E.proposer s) := stateBefore_tick_eq_stateBeforeTime S
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

private theorem block_admittedBefore_of_accepted_after_cutoff_local
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
  have hrelayHorizon : max t S.E.t_GST + S.E.Δ ≤ rho.horizon :=
    hrelayCutoff.trans hhor
  by_cases halready : NamedReceipt.processed
      (rho.stateBefore S (i + 1) w).st (Object.block B) = true
  · rcases acceptsAt_block_of_processed S rho w (i + 1) B halready with
      hgen | ⟨j, hj, t', hacc'⟩
    · have hzero : B.slot = 0 := by
        rw [hgen]
        rfl
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
      have hproposalHor : Protocol.proposal_time S.E B.slot ≤ rho.horizon := by
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
      obtain ⟨jP, hself⟩ := acceptsAtProposedBlock_local S adm hBpos
        hwProp hproposalHor hBproposed
      rw [hshape.2.2] at hself
      exact ⟨B, rfl, jP, Protocol.proposal_time S.E B.slot, hself,
        by rw [← hshape.2.1]; exact ht'cutoff⟩
    · have heDelivEq : e = Event.deliver w (Object.block B) tdeliv :=
        Option.some.inj (hej.symm.trans hdeliv)
      have htdelivEq : tdeliv = t' := by
        rw [heDelivEq] at heTime
        exact heTime
      rw [htdelivEq] at hdeliv
      have hproposalLe : Protocol.proposal_time S.E B.slot ≤ t' := by
        have h := proposalTimeLeOfAccepts_local S adm hacc
        rw [Proofs.NamedWire.erase_slot] at h
        exact h.trans htt'
      have hslot : ¬ (NamedRun.stateBefore S rho j w).st.core.s <
          B.erase.slot :=
        notFutureOfDelivery_local S adm hw hdeliv (by
          rw [Proofs.NamedWire.erase_slot]
          exact hproposalLe)
      have haccept := acceptsAtDeliveryGuards_local S adm hdeliv hslot
        (hFhist j (Nat.le_trans (Nat.le_succ j)
          (index_succ_le_strict_filter_length rho
            adm.toNamedScheduleWellFormed.sorted GammaOut hdeliv
            (by simpa only [Event.time] using ht'cutoff))))
        (proposer_eq_of_acceptsAt_block S hacc)
        (parent_slot_lt_of_acceptsAt_block S hacc)
        (carried_attestations_admissible_of_acceptsAt_block S hacc)
      exact ⟨B, rfl, j, t', haccept, ht'cutoff⟩

private theorem voterHeadProcessed_of_supporter
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {x : V} (hx : x ∈ rho.honest) {s : Slot} (hs : 0 < s)
    (hcommittee : x ∈ S.E.committee s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) {B : Block V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) B)
    (hBX : Block.Preceq B (voterHeadAt S rho x s)) :
    voterHeadAt S rho x s ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s := by
  obtain ⟨X, hXhead, hXmem, hXrun⟩ := voterHeadMem_of_core S adm hx s
  have hslot :
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s = s + 1 := by
    simpa only [Proofs.Optimistic.toHealing_slot] using
      Proofs.Optimistic.voteDutyStore_slot S rho w (s + 1)
  have hBX' : Block.Preceq B X.erase := by
    simpa only [hXhead] using hBX
  have hXpre : X.erase ∈
      (rho.storeBeforeTime S x (Protocol.vote_time S.E s)).T := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      hXmem
  rcases block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTime S
      adm.toNamedScheduleWellFormed x (Protocol.vote_time S.E s) hXpre with
    hgen | ⟨D, i, t, hDeq, hacc, ht⟩
  · have hgen' : voterHeadAt S rho x s = Block.genesis := by
      rw [← hXhead, hgen]
    have hgenesis := genesis_mem_and_stamp_storeBeforeTime S
      adm.toNamedScheduleWellFormed w
      (Protocol.vote_time S.E (s + 1)) (Protocol.view_freeze S.E s)
    have hprocessed : Block.genesis ∈ Protocol.voter_processed_block_tree S.E
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s := by
      simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
      rw [hslot, Nat.add_sub_cancel]
      exact ⟨by
        simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hgenesis.1,
        Or.inl (by
          simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
            Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hgenesis.2)⟩
    simpa only [hgen'] using hprocessed
  · have hDpos : 0 < D.slot := by
      rw [← Proofs.NamedWire.erase_slot D]
      exact Nat.zero_lt_of_lt
        (parent_slot_lt_of_acceptsAt_block S hacc)
    have hBXD : Block.Preceq B D.erase := by
      simpa only [hDeq] using hBX'
    have hFhist : BlockFinalizedBelowAtDeliveriesBefore S rho w D
        (Protocol.view_freeze S.E s) := by
      intro j hj
      have hjVote := hj.trans (strict_filter_length_mono rho
        (le_of_lt (view_freeze_lt_vote_time_succ S.E s)))
      have hroot' : Block.Preceq
          (Protocol.get_fg_root
            (rho.storeBeforeTime S w (Protocol.vote_time S.E (s + 1))).toHealing.toFG) B := by
        simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
          Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore] using hroot
      exact Block.preceq_trans
        (finalized_preceq_at_prefix_of_storeBeforeRoot_preceq
          S rho adm.toNamedScheduleWellFormed.sorted hroot' hjVote) hBXD
    have htSupport : t < Protocol.support_cutoff S.E s := by
      exact lt_trans ht (by
        rw [← Proofs.Optimistic.vote_time_add_delta]
        exact Int.lt_add_of_pos_right _ S.E.Δ_pos)
    have hpostCut : S.E.t_GST ≤ Protocol.support_cutoff S.E s := by
      apply hpost.trans
      rw [← Proofs.Optimistic.vote_time_add_delta]
      exact le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)
    have hfreezeHor : Protocol.view_freeze S.E s ≤ rho.horizon := by
      apply le_trans _ hhor
      exact le_of_lt (lt_trans
        (Int.lt_add_of_pos_right _ S.E.Δ_pos)
        (view_freeze_add_delta_lt_confirmation_time S.E s))
    have hadmit : AdmittedBefore S rho w D.erase
        (Protocol.view_freeze S.E s) := by
      apply block_admittedBefore_of_accepted_after_cutoff_local
        S adm hx hw hDpos hacc htSupport hpostCut
        (support_cutoff_add_delta_eq_view_freeze S.E s) hfreezeHor
      exact hFhist
    have hvis := admittedBefore_mem_and_stamp_at S
      adm.toNamedScheduleWellFormed hadmit
      (le_of_lt (view_freeze_lt_vote_time_succ S.E s))
    have hprocessedD : D.erase ∈ Protocol.voter_processed_block_tree S.E
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s := by
      simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
      rw [hslot, Nat.add_sub_cancel]
      exact ⟨by
        simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hvis.1,
        Or.inl (by
          simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
            Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hvis.2)⟩
    simpa only [hXhead, hDeq] using hprocessedD

private theorem namedAncestorBodyMem_local {st : Protocol.NamedStore V}
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
      simp only [NamedBlock.Preceq, NamedBlock.preceq,
        Bool.or_eq_true, decide_eq_true_eq] at hAB
      rcases hAB with rfl | hparent
      · exact hB
      · exact ih (hpc.2 _ hB) hparent

private theorem actionStoreCoherent_local
    (S : Setup V) {rho : Run V} (v : V) (r : Round) :
    Proofs.NamedStore.Coherent S.E S.cfg (actionStoreAt S rho v r).st := by
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (actionStoreAt S rho v r).st := by
    apply Proofs.NamedConfirmationMembership.invariant_update
    exact Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ (S.a r)
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a r) v).1
  exact hinv.1.1

private theorem actionBodyRunBlock_local
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionStoreAt S rho v r).st.bodies) :
    RunBlock S rho D := by
  have hDpre : D ∈
      (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hD
  obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedScheduleWellFormed.sorted (S.a r)
  have hDi : D ∈ (NamedRun.stateBefore S rho i v).st.bodies := by
    change D ∈ (NamedRun.stateBefore S rho i v).st.bodies
    rw [← hi]
    exact hDpre
  exact Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hDi)

private theorem namedPreceq_of_runBlock_erase_preceq_local
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

private theorem actionNamedCheckpoint_local
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
  have hcoh := actionStoreCoherent_local (rho := rho) S v r
  have hK : K ∈ (actionStoreAt S rho v r).st.bodies :=
    namedAncestorBodyMem_local hcoh.2.2.1 hD hKD
  exact ⟨K, hK, hKentry, hKh, hKD,
    actionBodyRunBlock_local S adm hv hK⟩

private theorem emittedAttestationEq_local
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

private theorem honestEmittedHeightRowWitness_local
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
  have haEq := emittedAttestationEq_local S adm hemit
  rw [haEq] at hh
  generalize hp :
      (actionAttestationAt S rho a.val_index a.round).height_pair = q at hh
  cases q with
  | empty => cases hh
  | vote height entry timeout =>
      have hh' : height = h := by
        cases timeout <;>
          simpa [NamedHeightPair.erase, HeightPair.height?] using hh
      subst height
      obtain ⟨Cfg, hCfg, hCfgHeight, hCfgRoot⟩ :=
        NamedActionSources.action_source S rho a.val_index a.round
          h entry timeout hp
      obtain ⟨D, hD, hDerase, hDderive, -⟩ :=
        NamedActionSources.action_witness S rho a.val_index a.round Cfg hCfg
      let J := (Protocol.derive_named S.E S.cfg D).T_h
      have hsource : actionFGSource S
          (actionStoreAt S rho a.val_index a.round) = some D.erase := by
        simpa only [actionStoreAt, hDerase] using hCfg
      have hheight :
          ((actionStoreAt S rho a.val_index a.round).st.core.σ D.erase).h = h := by
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

private theorem honestHeightRowConfirmationWitness_local
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {a : NamedAttestation V} {ta : Time} {h : Height}
    (haHon : a.val_index ∈ rho.honest)
    (hemit : NamedRun.emits S rho a.val_index (Object.attest a) ta)
    (hh : a.height_pair.erase.height? = some h) :
    ∃ D K : NamedBlock V,
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
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
  obtain ⟨D, J, htime, haEq, hsource, hD, hheight,
      hnamedHeight, hJ, hrow⟩ :=
    honestEmittedHeightRowWitness_local S adm hemit hh
  obtain ⟨K, hK, hKentry, hKheight, hKpre, -⟩ :=
    actionNamedCheckpoint_local S adm haHon hD
  have hKheight' : (Protocol.derive_named S.E S.cfg K).h = h :=
    hKheight.trans hnamedHeight
  have hDderive :
      (actionStoreAt S rho a.val_index a.round).st.core.σ D.erase =
        Protocol.derive_named S.E S.cfg D :=
    (actionStoreCoherent_local S a.val_index a.round).2.2.2.2 D hD
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

private theorem frontierQuorumWitness_local
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
        have hfalse : False := by
          simpa only [hpair, NamedHeightPair.matchesEntry,
            Bool.false_eq_true] using hmatch
        exact hfalse.elim
    | vote height entry timeout =>
        have hfields : height = pre.core.h_max - 1 ∧ entry = X.root := by
          simpa only [hpair, NamedHeightPair.matchesEntry,
            decide_eq_true_eq] using hmatch
        cases timeout <;>
          simp [hpair, NamedHeightPair.erase, HeightPair.height?, hfields.1]
  refine ⟨W, hW, Q, X, a, S.a a.round, hmaxW.symm.le, hQ, hX,
    ?_, haHonest, hemit, hta, hheight⟩
  exact Proofs.Bridges.erase_mem_chain_attestations W carrier hcarrier a ha

private theorem frontierConfirmationWitness_local
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
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
        some (Protocol.derive_named S.E S.cfg K).T_h ∧
      D ∈ (actionStoreAt S rho a.val_index a.round).st.bodies ∧
      K ∈ (actionStoreAt S rho a.val_index a.round).st.bodies ∧
      K.erase = (Protocol.derive_named S.E S.cfg D).T_h ∧
      RunBlock S rho K ∧
      (Protocol.derive_named S.E S.cfg K).h =
        (rho.storeBeforeTime S v time).core.h_max - 1 ∧
      (Protocol.derive_named S.E S.cfg D).h =
        (rho.storeBeforeTime S v time).core.h_max - 1 ∧
      Block.Preceq K.erase D.erase := by
  obtain ⟨W, hW, Q, X, a, ta, hmaxW, hQ, hXW, haW, haHon,
      hemit, hta, hheight⟩ := frontierQuorumWitness_local S adm hmajority hlarge
  obtain ⟨D, K, hfg, hD, -, hDheight, hK, hKentry,
      hKheight, hKpre, -⟩ :=
    honestHeightRowConfirmationWitness_local S adm haHon hemit hheight
  have hKrun := actionBodyRunBlock_local S adm haHon hK
  exact ⟨a, ta, D, K, haHon, hemit, hta, hheight, hfg, hD, hK,
    hKentry, hKrun, hKheight, hDheight, hKpre⟩

private theorem openingNextLeOfActionBeforeNextVote_local
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
    rw [← Proofs.Optimistic.vote_time_add_delta]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  exact (not_lt_of_ge (le_of_lt h))
    (hvote.trans_le (support_cutoff_mono S.E hs))

private theorem actionLeSupportCutoff_local
    (S : Setup V) {r : Round} {s : Slot}
    (h : S.a r < Protocol.vote_time S.E (s + 1)) :
    S.a r ≤ Protocol.support_cutoff S.E s := by
  change S.hc.a S.E.Δ r ≤ Protocol.support_cutoff S.E s
  rw [Protocol.a_eq_support_cutoff_succ S.hc S.E r]
  exact support_cutoff_mono S.E
    (openingNextLeOfActionBeforeNextVote_local S h)

private theorem actionBlockProcessedAtNextDuty_local
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {u w : V} (hu : u ∈ rho.honest) (hw : w ∈ rho.honest)
    {r : Round} {s : Slot} {T : NamedBlock V}
    (hmem : T ∈ (actionStoreAt S rho u r).st.bodies)
    (haction : S.a r < Protocol.vote_time S.E (s + 1))
    (hpost : S.E.t_GST ≤ Protocol.support_cutoff S.E s)
    (hhor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) T.erase) :
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
    rw [← htree, (actionStoreCoherent_local S u r).1]
    exact Finset.mem_image.mpr ⟨T, hmem, rfl⟩
  have hcut := actionLeSupportCutoff_local S haction
  have hfreezeVote := le_of_lt (view_freeze_lt_vote_time_succ S.E s)
  have hrelay : T.erase = Block.genesis ∨
      AdmittedBefore S rho w T.erase (Protocol.view_freeze S.E s) := by
    rcases block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTime S
        adm.toNamedScheduleWellFormed u (S.a r) hpre with
      hgen | ⟨D, i, t, hDeq, hacc, ht⟩
    · exact Or.inl hgen
    · right
      have hrootD : Block.Preceq
          (Protocol.get_fg_root
            (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) D.erase := by
        simpa only [hDeq] using hroot
      have hDpos : 0 < D.slot := by
        rw [← Proofs.NamedWire.erase_slot D]
        exact Nat.zero_lt_of_lt
          (parent_slot_lt_of_acceptsAt_block S hacc)
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
      have htSupport : t < Protocol.support_cutoff S.E s :=
        lt_of_lt_of_le ht hcut
      have hfreezeHor : Protocol.view_freeze S.E s ≤ rho.horizon :=
        (view_freeze_lt_vote_time_succ S.E s).le.trans hhor
      have hadmit := block_admittedBefore_of_accepted_after_cutoff_local
        S adm hu hw hDpos hacc htSupport hpost
        (support_cutoff_add_delta_eq_view_freeze S.E s) hfreezeHor hFhist
      simpa only [hDeq] using hadmit
  have hvis := relayedWitness_mem_and_stamp S
    adm.toNamedScheduleWellFormed hfreezeVote hrelay
  have hslot :
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s = s + 1 := by
    simpa only [Proofs.Optimistic.toHealing_slot] using
      Proofs.Optimistic.voteDutyStore_slot S rho w (s + 1)
  have hprocessed : T.erase ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s := by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    rw [hslot, Nat.add_sub_cancel]
    exact ⟨by
      simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hvis.1,
      Or.inl (by
        simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hvis.2)⟩
  exact hprocessed

private theorem voterHeadEmits_of_core_local
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot}
    (hs : 0 < s) (hcommittee : w ∈ S.E.committee s)
    (hhor : Protocol.vote_time S.E s ≤ rho.horizon) :
    ∃ C : NamedBlock V, C.erase = voterHeadAt S rho w s ∧
      NamedRun.blockInRun S rho C ∧
      NamedRun.emits S rho w
        (Object.gfVote ⟨w, s, C.erase.root⟩)
        (Protocol.vote_time S.E s) := by
  obtain ⟨C, hChead, -, hCrun⟩ := voterHeadMem_of_core S adm hw s
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

theorem genuineConfirmationWith_preceq_nextVoterHead_of_frontierWitnesses
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    (hmajority : HonestWeightMajority S rho.honest)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {s : Slot} (hs : 0 < s) {B : Block V}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hgenuine : GenuineConfirmationWith
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).cache)
      S.E S.hc (confStore S rho v s) s B)
    (hwitnesses : ∀ {C : NamedBlock V},
      C.erase = B →
      (Protocol.derive_named S.E S.cfg C).h <
        (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.h_max - 1 →
      RunBlock S rho C →
      ∀ (a : NamedAttestation V) (ta : Time) (K : NamedBlock V),
        a.val_index ∈ rho.honest →
        NamedRun.emits S rho a.val_index (Object.attest a) ta →
        ta < Protocol.vote_time S.E (s + 1) →
        a.height_pair.erase.height? =
          some ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).h_max - 1) →
        fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
          some (Protocol.derive_named S.E S.cfg K).T_h →
        RunBlock S rho K →
        Block.compatible C.erase
          (Protocol.derive_named S.E S.cfg K).T_h = true)
    (hroot : Block.compatible
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) B = true)
    (hanchor : Block.compatible (voterAnchorAt S rho w (s + 1)) B = true) :
    Block.Preceq B (voterHeadAt S rho w (s + 1)) := by
  let read := Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)
  let target := read.st.core.toHealing
  let contract := NamedProfile.gradeContract read.cache
  have hslot : read.st.core.s = s + 1 := by
    simpa only [read] using
      Proofs.Optimistic.voteDutyRead_slot S rho w (s + 1)
  have hslotHealing : read.st.core.toHealing.s = s + 1 := by
    simpa only [Protocol.Store.toHealing] using hslot
  have hDwalk : B = confWalkWith
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).cache)
      S.E S.hc (confStore S rho v s) s := by
    rw [← hgenuine.selected, update_confirmation_with_live_confirmed,
      if_pos hgenuine.genuine]
  have hEligible : Protocol.voters_count S.E
      (confLate S.E (confStore S rho v s) s) s <
      2 * Protocol.goldfish_score S.E (confStore S rho v s).T
        (confVotes S.E (confStore S rho v s) s)
        (confVotes S.E (confStore S rho v s) s) s B := by
    have h := hgenuine.genuine
    rw [← hDwalk] at h
    simpa only [confEligible, confCount, confScore,
      decide_eq_true_eq] using h
  have hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E s := by
    apply le_trans hpost
    exact (proposal_time_lt_vote_time S.E s).le
  have hcases : Block.Preceq
      (Protocol.get_fg_root read.st.core.toHealing.toFG) B ∨
      Block.Preceq B (Protocol.get_fg_root read.st.core.toHealing.toFG) := by
    simpa only [Block.compatible, Bool.or_eq_true] using hroot
  rcases hcases with hrootBelow | hbelowRoot
  · have hpathData : B ∈ voterCandidateTreeAt S rho w (s + 1) ∧
        ∀ C : Block V,
          Block.Preceq (voterAnchorAt S rho w (s + 1)) C →
          C ≠ voterAnchorAt S rho w (s + 1) →
          Block.Preceq C B → C ≠ B →
          C ∈ voterCandidateTreeAt S rho w (s + 1) := by
      obtain ⟨x, hxHonest, hxCommittee, hBX⟩ :=
        genuineConfirmation_exists_honestVoteSupporter_after_gst S adm hcom hv hs
          hpostVote hhor hgenuine
      have hBprocessed := voterHeadProcessed_of_supporter S adm hxHonest hs
        hxCommittee hpostVote hhor
        hw hrootBelow hBX
      have hBprocessed' := ancestorProcessed_of_voterProcessed S adm hw
        hBprocessed B hBX
      have hBread : B ∈ read.st.core.T := by
        have h := (Finset.mem_filter.mp hBprocessed').1
        simpa only [read, voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
          Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using h
      by_cases hband : read.st.core.h_max - 1 ≤ (read.st.core.σ B).h
      · exact candidatePath_of_processedBandDescendant_local S adm hw
          (Block.preceq_self B) hBprocessed' hband hrootBelow
      · have hBpre : B ∈
            (NamedRun.stateBeforeTime S rho
              (Protocol.vote_time S.E (s + 1)) w).st.core.T := by
          simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
            hBread
        obtain ⟨C, hCbody, hCB⟩ :=
          Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
            (Protocol.vote_time S.E (s + 1)) w hBpre
        have hCrun : NamedRun.blockInRun S rho C := by
          obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
            adm.toNamedScheduleWellFormed.sorted
              (Protocol.vote_time S.E (s + 1))
          apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw
          change C ∈ (NamedRun.stateBefore S rho i w).st.bodies
          rw [← hi]
          exact hCbody
        have hCmem : C.erase ∈ read.st.core.T := by
          simpa only [hCB] using hBread
        have hCheight := namedHeight_at_voteDuty S adm hw hCrun hCmem
        have hhigh : (Protocol.derive_named S.E S.cfg C).h <
            read.st.core.h_max - 1 := by
          apply Nat.lt_of_not_ge
          intro h
          apply hband
          rw [← hCB, hCheight]
          exact h
        have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
          apply le_trans (le_of_lt ?_) hhor
          rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
          exact Int.lt_add_of_pos_right _ S.E.Δ_pos
        have hpostSupport : S.E.t_GST ≤ Protocol.support_cutoff S.E s := by
          apply hpost.trans
          unfold Protocol.proposal_time Protocol.support_cutoff
          exact le_add_of_nonneg_right
            (Int.mul_nonneg (by norm_num) (le_of_lt S.E.Δ_pos))
        have hlargeRead : 1 < read.st.core.h_max :=
          Nat.sub_pos_iff_lt.mp ((Nat.zero_le _).trans_lt hhigh)
        have hlarge : 1 < (rho.storeBeforeTime S w
            (Protocol.vote_time S.E (s + 1))).h_max := by
          simpa only [read, voteDutyRead,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom,
            Protocol.NamedStore.setClock, Run.storeBeforeTime] using hlargeRead
        obtain ⟨a, ta, D, K, ha, hemit, hta, hrow, hselected,
            hDmem, hKmem, hKentry, hKrun, hKheight, hDheight, hKpre⟩ :=
          frontierConfirmationWitness_local S adm hmajority hlarge
        have hDrun := actionBodyRunBlock_local S adm ha hDmem
        have hKpreNamed := namedPreceq_of_runBlock_erase_preceq_local
          S adm hKrun hDrun hKpre
        have hKtarget : (Protocol.derive_named S.E S.cfg K).T_h = K.erase := by
          exact (Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hKpreNamed
            (hKheight.trans hDheight.symm)).trans hKentry.symm
        have hcompatible : NamedBlock.compatible C K = true := by
          have hrawCompatible : Block.compatible C.erase K.erase = true := by
            simpa only [hKtarget] using
              ((hwitnesses hCB (by
                simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt,
                  NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
                  Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore]
                using hhigh) hCrun) a ta K ha hemit hta hrow hselected hKrun)
          have hcompatCases : Block.Preceq C.erase K.erase ∨
              Block.Preceq K.erase C.erase := by
            simpa only [Block.compatible, Bool.or_eq_true] using hrawCompatible
          rcases hcompatCases with hCK | hKC
          · have hnamed := namedPreceq_of_runBlock_erase_preceq_local
              S adm hCrun hKrun hCK
            simpa only [NamedBlock.compatible, Bool.or_eq_true] using
              (Or.inl hnamed)
          · have hnamed := namedPreceq_of_runBlock_erase_preceq_local
              S adm hKrun hCrun hKC
            simpa only [NamedBlock.compatible, Bool.or_eq_true] using
              (Or.inr hnamed)
        have hCK : NamedBlock.Preceq C K := by
          have hcompatCases : NamedBlock.Preceq C K ∨
              NamedBlock.Preceq K C := by
            simpa only [NamedBlock.compatible, Bool.or_eq_true] using hcompatible
          rcases hcompatCases with hCK | hKC
          · exact hCK
          · have hmono := Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hKC
            have hKheightCore : (Protocol.derive_named S.E S.cfg K).h =
                read.st.core.h_max - 1 := by
              simpa only [read, voteDutyRead,
                NamedActionReads.confirmationReadAt,
                NamedActionReads.confirmationReadFrom,
                Protocol.NamedStore.setClock, Run.storeBeforeTime] using hKheight
            rw [hKheightCore] at hmono
            exact False.elim ((Nat.not_le_of_gt hhigh) hmono)
        have hKprocessed := actionBlockProcessedAtNextDuty_local S adm ha hw
          hKmem (by simpa only [(Proofs.Optimistic.emits_attest_shape S hemit).2] using hta)
          hpostSupport hvoteHor (by
            have hBK : Block.Preceq B K.erase := by
              simpa only [hCB] using Proofs.NamedWire.erase_preceq hCK
            exact Block.preceq_trans hrootBelow hBK)
        have hKmemRead : K.erase ∈ read.st.core.T := by
          have h := (Finset.mem_filter.mp hKprocessed).1
          simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
            Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
            Proofs.Optimistic.tickStore] using h
        have hKheightRead := namedHeight_at_voteDuty S adm hw hKrun hKmemRead
        have hBK : Block.Preceq B K.erase := by
          simpa only [hCB] using Proofs.NamedWire.erase_preceq hCK
        have hpathK := candidatePath_of_processedBandDescendant_local S adm hw
          hBK hKprocessed
          (by rw [hKheightRead]; exact hKheight.ge) hrootBelow
        exact hpathK
    have hcompatible : Block.compatible
        (Protocol.get_sg_root_with contract S.E S.hc target
          (S.hc.round_of target.s)) B = true := by
      change Block.compatible (voterAnchorAt S rho w (s + 1)) B = true
      exact hanchor
    have htransportRead : AdoptionTransport
        (confStore S rho v s).T read.st.core.toHealing.T
        (confVotes S.E (confStore S rho v s) s)
        (confLate S.E (confStore S rho v s) s)
        (Protocol.voter_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
        (Protocol.voter_support_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s) B := by
      rw [hslot]
      change AdoptionTransport (confStore S rho v s).T
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).T
        (confVotes S.E (confStore S rho v s) s)
        (confLate S.E (confStore S rho v s) s)
        (Protocol.voter_view S.E
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore (s + 1))
        (Protocol.voter_support_view S.E
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore (s + 1)) B
      exact adoptionTransport_B_after_gst S adm hv hw hpost hhor hrootBelow
    have hsubRead :
        Protocol.voter_support_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s ⊆
          Protocol.voter_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s := by
      rw [hslot]
      change Protocol.voter_support_view S.E
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore (s + 1) ⊆
        Protocol.voter_view S.E
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore (s + 1)
      exact voter_support_subset_voter_view_voteDuty S adm w (s + 1)
    have hhead := get_head_in_tree_with_captures_of_confirmation
      (NamedProfile.gradeContract read.cache) S.E S.hc target
      (confStore S rho v s).T
      (voterCandidateTreeAt S rho w (s + 1))
      (confEarly S.E (confStore S rho v s) s)
      (confLate S.E (confStore S rho v s) s)
      (confVotes S.E (confStore S rho v s) s)
      (Protocol.voter_view S.E target.toFG.toSG.toGoldfishStore target.s)
      (Protocol.voter_support_view S.E target.toFG.toSG.toGoldfishStore target.s)
      s (confNumerator S.E (confStore S rho v s) s)
      htransportRead
      (by simpa only [hDwalk] using hEligible)
      hsubRead
      (by
        change Block.compatible (voterAnchorAt S rho w (s + 1)) B = true
        exact hanchor)
      (by
        intro _ C hAC hCne hCB'
        by_cases hEq : C = B
        · subst C
          exact hpathData.1
        · exact hpathData.2 C hAC hCne hCB' hEq)
    rw [voterHeadAt_eq_get_head_with_anchor S rho w (s + 1)]
    simpa only [target, read, hslot, hslotHealing, Nat.add_sub_cancel] using hhead
  · have hhead := get_head_in_tree_with_of_preceq_fgRoot read.cache S.E S.hc
      read.st.core.toHealing (voterCandidateTreeAt S rho w (s + 1)) B
      (Protocol.voter_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
      (Protocol.voter_support_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
      (read.st.core.s - 1) hbelowRoot
    rw [voterHeadAt_eq_get_head_with_anchor S rho w (s + 1)]
    simpa only [read, hslot, Nat.add_sub_cancel] using hhead

#print axioms genuineConfirmationWith_preceq_nextVoterHead_of_frontierWitnesses
theorem genuineConfirmationWith_preceq_nextVoterHead_of_frontierWitnesses_of_delivery
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {cap : Time} (hdelivery : HonestDeliveryBefore S rho cap)
    (hcom : HonestCommittees S rho.honest)
    (hmajority : HonestWeightMajority S rho.honest)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {s : Slot} (hs : 0 < s) {B : Block V}
    (hcap : Protocol.confirmation_time S.E s ≤ cap)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hgenuine : GenuineConfirmationWith
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).cache)
      S.E S.hc (confStore S rho v s) s B)
    (hwitnesses : ∀ {C : NamedBlock V},
      C.erase = B →
      (Protocol.derive_named S.E S.cfg C).h <
        (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.h_max - 1 →
      RunBlock S rho C →
      ∀ (a : NamedAttestation V) (ta : Time) (K : NamedBlock V),
        a.val_index ∈ rho.honest →
        NamedRun.emits S rho a.val_index (Object.attest a) ta →
        ta < Protocol.vote_time S.E (s + 1) →
        a.height_pair.erase.height? =
          some ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).h_max - 1) →
        fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
          some (Protocol.derive_named S.E S.cfg K).T_h →
        RunBlock S rho K →
        Block.compatible C.erase
          (Protocol.derive_named S.E S.cfg K).T_h = true)
    (hroot : Block.compatible
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) B = true)
    (hanchor : Block.compatible (voterAnchorAt S rho w (s + 1)) B = true) :
    Block.Preceq B (voterHeadAt S rho w (s + 1)) := by
  let read := Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)
  let target := read.st.core.toHealing
  let contract := NamedProfile.gradeContract read.cache
  have hslot : read.st.core.s = s + 1 := by
    simpa only [read] using
      Proofs.Optimistic.voteDutyRead_slot S rho w (s + 1)
  have hslotHealing : read.st.core.toHealing.s = s + 1 := by
    simpa only [Protocol.Store.toHealing] using hslot
  have hDwalk : B = confWalkWith
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).cache)
      S.E S.hc (confStore S rho v s) s := by
    rw [← hgenuine.selected, update_confirmation_with_live_confirmed,
      if_pos hgenuine.genuine]
  have hEligible : Protocol.voters_count S.E
      (confLate S.E (confStore S rho v s) s) s <
      2 * Protocol.goldfish_score S.E (confStore S rho v s).T
        (confVotes S.E (confStore S rho v s) s)
        (confVotes S.E (confStore S rho v s) s) s B := by
    have h := hgenuine.genuine
    rw [← hDwalk] at h
    simpa only [confEligible, confCount, confScore,
      decide_eq_true_eq] using h
  have hcases : Block.Preceq
      (Protocol.get_fg_root read.st.core.toHealing.toFG) B ∨
      Block.Preceq B (Protocol.get_fg_root read.st.core.toHealing.toFG) := by
    simpa only [Block.compatible, Bool.or_eq_true] using hroot
  rcases hcases with hrootBelow | hbelowRoot
  · have hpathData : B ∈ voterCandidateTreeAt S rho w (s + 1) ∧
        ∀ C : Block V,
          Block.Preceq (voterAnchorAt S rho w (s + 1)) C →
          C ≠ voterAnchorAt S rho w (s + 1) →
          Block.Preceq C B → C ≠ B →
          C ∈ voterCandidateTreeAt S rho w (s + 1) := by
      have hBprocessed' :=
        voterProcessedTarget_of_genuineConfirmation_of_delivery
          S adm hdelivery hv hw hcap hhor
            ⟨hgenuine.selected, hgenuine.genuine⟩ hrootBelow
      have hBread : B ∈ read.st.core.T := by
        have h := (Finset.mem_filter.mp hBprocessed').1
        simpa only [read, voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
          Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using h
      by_cases hband : read.st.core.h_max - 1 ≤ (read.st.core.σ B).h
      · exact candidatePath_of_processedBandDescendant_local S adm hw
          (Block.preceq_self B) hBprocessed' hband hrootBelow
      · have hBpre : B ∈
            (NamedRun.stateBeforeTime S rho
              (Protocol.vote_time S.E (s + 1)) w).st.core.T := by
          simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
            hBread
        obtain ⟨C, hCbody, hCB⟩ :=
          Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
            (Protocol.vote_time S.E (s + 1)) w hBpre
        have hCrun : NamedRun.blockInRun S rho C := by
          obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
            adm.toNamedScheduleWellFormed.sorted
              (Protocol.vote_time S.E (s + 1))
          apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw
          change C ∈ (NamedRun.stateBefore S rho i w).st.bodies
          rw [← hi]
          exact hCbody
        have hCmem : C.erase ∈ read.st.core.T := by
          simpa only [hCB] using hBread
        have hCheight := namedHeight_at_voteDuty S adm hw hCrun hCmem
        have hhigh : (Protocol.derive_named S.E S.cfg C).h <
            read.st.core.h_max - 1 := by
          apply Nat.lt_of_not_ge
          intro h
          apply hband
          rw [← hCB, hCheight]
          exact h
        have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
          apply le_trans (le_of_lt ?_) hhor
          rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
          exact Int.lt_add_of_pos_right _ S.E.Δ_pos
        have hlargeRead : 1 < read.st.core.h_max :=
          Nat.sub_pos_iff_lt.mp ((Nat.zero_le _).trans_lt hhigh)
        have hlarge : 1 < (rho.storeBeforeTime S w
            (Protocol.vote_time S.E (s + 1))).h_max := by
          simpa only [read, voteDutyRead,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom,
            Protocol.NamedStore.setClock, Run.storeBeforeTime] using hlargeRead
        obtain ⟨a, ta, D, K, ha, hemit, hta, hrow, hselected,
            hDmem, hKmem, hKentry, hKrun, hKheight, hDheight, hKpre⟩ :=
          frontierConfirmationWitness_local S adm hmajority hlarge
        have hDrun := actionBodyRunBlock_local S adm ha hDmem
        have hKpreNamed := namedPreceq_of_runBlock_erase_preceq_local
          S adm hKrun hDrun hKpre
        have hKtarget : (Protocol.derive_named S.E S.cfg K).T_h = K.erase := by
          exact (Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hKpreNamed
            (hKheight.trans hDheight.symm)).trans hKentry.symm
        have hcompatible : NamedBlock.compatible C K = true := by
          have hrawCompatible : Block.compatible C.erase K.erase = true := by
            simpa only [hKtarget] using
              ((hwitnesses hCB (by
                simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt,
                  NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
                  Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore]
                using hhigh) hCrun) a ta K ha hemit hta hrow hselected hKrun)
          have hcompatCases : Block.Preceq C.erase K.erase ∨
              Block.Preceq K.erase C.erase := by
            simpa only [Block.compatible, Bool.or_eq_true] using hrawCompatible
          rcases hcompatCases with hCK | hKC
          · have hnamed := namedPreceq_of_runBlock_erase_preceq_local
              S adm hCrun hKrun hCK
            simpa only [NamedBlock.compatible, Bool.or_eq_true] using
              (Or.inl hnamed)
          · have hnamed := namedPreceq_of_runBlock_erase_preceq_local
              S adm hKrun hCrun hKC
            simpa only [NamedBlock.compatible, Bool.or_eq_true] using
              (Or.inr hnamed)
        have hCK : NamedBlock.Preceq C K := by
          have hcompatCases : NamedBlock.Preceq C K ∨
              NamedBlock.Preceq K C := by
            simpa only [NamedBlock.compatible, Bool.or_eq_true] using hcompatible
          rcases hcompatCases with hCK | hKC
          · exact hCK
          · have hmono := Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hKC
            have hKheightCore : (Protocol.derive_named S.E S.cfg K).h =
                read.st.core.h_max - 1 := by
              simpa only [read, voteDutyRead,
                NamedActionReads.confirmationReadAt,
                NamedActionReads.confirmationReadFrom,
                Protocol.NamedStore.setClock, Run.storeBeforeTime] using hKheight
            rw [hKheightCore] at hmono
            exact False.elim ((Nat.not_le_of_gt hhigh) hmono)
        have hKprocessed := actionBlockProcessedAtNextDuty_of_delivery S adm hdelivery ha hw
          hKmem (by simpa only [(Proofs.Optimistic.emits_attest_shape S hemit).2] using hta)
          hcap (by
            have hBK : Block.Preceq B K.erase := by
              simpa only [hCB] using Proofs.NamedWire.erase_preceq hCK
            exact Block.preceq_trans hrootBelow hBK)
        have hKmemRead : K.erase ∈ read.st.core.T := by
          have h := (Finset.mem_filter.mp hKprocessed).1
          simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
            Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
            Proofs.Optimistic.tickStore] using h
        have hKheightRead := namedHeight_at_voteDuty S adm hw hKrun hKmemRead
        have hBK : Block.Preceq B K.erase := by
          simpa only [hCB] using Proofs.NamedWire.erase_preceq hCK
        have hpathK := candidatePath_of_processedBandDescendant_local S adm hw
          hBK hKprocessed
          (by rw [hKheightRead]; exact hKheight.ge) hrootBelow
        exact hpathK
    have hcompatible : Block.compatible
        (Protocol.get_sg_root_with contract S.E S.hc target
          (S.hc.round_of target.s)) B = true := by
      change Block.compatible (voterAnchorAt S rho w (s + 1)) B = true
      exact hanchor
    have htransportRead : AdoptionTransport
        (confStore S rho v s).T read.st.core.toHealing.T
        (confVotes S.E (confStore S rho v s) s)
        (confLate S.E (confStore S rho v s) s)
        (Protocol.voter_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
        (Protocol.voter_support_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s) B := by
      rw [hslot]
      change AdoptionTransport (confStore S rho v s).T
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).T
        (confVotes S.E (confStore S rho v s) s)
        (confLate S.E (confStore S rho v s) s)
        (Protocol.voter_view S.E
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore (s + 1))
        (Protocol.voter_support_view S.E
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore (s + 1)) B
      exact adoptionTransport_B_of_delivery S adm hdelivery hv hw hcap hhor hrootBelow
    have hsubRead :
        Protocol.voter_support_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s ⊆
          Protocol.voter_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s := by
      rw [hslot]
      change Protocol.voter_support_view S.E
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore (s + 1) ⊆
        Protocol.voter_view S.E
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore (s + 1)
      exact voter_support_subset_voter_view_voteDuty S adm w (s + 1)
    have hhead := get_head_in_tree_with_captures_of_confirmation
      (NamedProfile.gradeContract read.cache) S.E S.hc target
      (confStore S rho v s).T
      (voterCandidateTreeAt S rho w (s + 1))
      (confEarly S.E (confStore S rho v s) s)
      (confLate S.E (confStore S rho v s) s)
      (confVotes S.E (confStore S rho v s) s)
      (Protocol.voter_view S.E target.toFG.toSG.toGoldfishStore target.s)
      (Protocol.voter_support_view S.E target.toFG.toSG.toGoldfishStore target.s)
      s (confNumerator S.E (confStore S rho v s) s)
      htransportRead
      (by simpa only [hDwalk] using hEligible)
      hsubRead
      (by
        change Block.compatible (voterAnchorAt S rho w (s + 1)) B = true
        exact hanchor)
      (by
        intro _ C hAC hCne hCB'
        by_cases hEq : C = B
        · subst C
          exact hpathData.1
        · exact hpathData.2 C hAC hCne hCB' hEq)
    rw [voterHeadAt_eq_get_head_with_anchor S rho w (s + 1)]
    simpa only [target, read, hslot, hslotHealing, Nat.add_sub_cancel] using hhead
  · have hhead := get_head_in_tree_with_of_preceq_fgRoot read.cache S.E S.hc
      read.st.core.toHealing (voterCandidateTreeAt S rho w (s + 1)) B
      (Protocol.voter_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
      (Protocol.voter_support_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
      (read.st.core.s - 1) hbelowRoot
    rw [voterHeadAt_eq_get_head_with_anchor S rho w (s + 1)]
    simpa only [read, hslot, Nat.add_sub_cancel] using hhead

#print axioms genuineConfirmationWith_preceq_nextVoterHead_of_frontierWitnesses_of_delivery


theorem protectedVoteSlot_succ_of_genuineConfirmationWith
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    (hmajority : HonestWeightMajority S rho.honest)
    {v : V} (hv : v ∈ rho.honest)
    {s : Slot} (hs : 0 < s) {B : Block V}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hgenuine : GenuineConfirmationWith
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).cache)
      S.E S.hc (confStore S rho v s) s B)
    (hwitnesses : ∀ w ∈ rho.honest, ∀ {C : NamedBlock V},
      C.erase = B →
      (Protocol.derive_named S.E S.cfg C).h <
        (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.h_max - 1 →
      RunBlock S rho C →
      ∀ (a : NamedAttestation V) (ta : Time) (K : NamedBlock V),
        a.val_index ∈ rho.honest →
        NamedRun.emits S rho a.val_index (Object.attest a) ta →
        ta < Protocol.vote_time S.E (s + 1) →
        a.height_pair.erase.height? =
          some ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).h_max - 1) →
        fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
          some (Protocol.derive_named S.E S.cfg K).T_h →
        RunBlock S rho K →
        Block.compatible C.erase
          (Protocol.derive_named S.E S.cfg K).T_h = true)
    (hroots : ∀ w ∈ rho.honest, Block.compatible
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) B = true)
    (hanchors : ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w (s + 1)) B = true) :
    ProtectedVoteSlot S rho (s + 1) B := by
  have hheads : ∀ w ∈ rho.honest,
      Block.Preceq B (voterHeadAt S rho w (s + 1)) := by
    intro w hw
    exact genuineConfirmationWith_preceq_nextVoterHead_of_frontierWitnesses
      S adm hcom hmajority hv hw hs hpost hhor hgenuine
      (hwitnesses w hw) (hroots w hw) (hanchors w hw)
  refine ⟨hheads, ?_⟩
  have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
    apply le_trans (le_of_lt ?_) hhor
    rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  intro w hw hcommittee
  obtain ⟨X, hXe, hXrun, hXemit⟩ := voterHeadEmits_of_core_local S adm hw
    (s := s + 1) (Nat.succ_pos s) hcommittee hvoteHor
  exact ⟨X, hXe ▸ hheads w hw, hXrun, hXemit⟩

#print axioms protectedVoteSlot_succ_of_genuineConfirmationWith
theorem protectedVoteSlot_succ_of_genuineConfirmationWith_of_delivery
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {cap : Time} (hdelivery : HonestDeliveryBefore S rho cap)
    (hcom : HonestCommittees S rho.honest)
    (hmajority : HonestWeightMajority S rho.honest)
    {v : V} (hv : v ∈ rho.honest)
    {s : Slot} (hs : 0 < s) {B : Block V}
    (hcap : Protocol.confirmation_time S.E s ≤ cap)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hgenuine : GenuineConfirmationWith
      (NamedProfile.gradeContract
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).cache)
      S.E S.hc (confStore S rho v s) s B)
    (hwitnesses : ∀ w ∈ rho.honest, ∀ {C : NamedBlock V},
      C.erase = B →
      (Protocol.derive_named S.E S.cfg C).h <
        (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.h_max - 1 →
      RunBlock S rho C →
      ∀ (a : NamedAttestation V) (ta : Time) (K : NamedBlock V),
        a.val_index ∈ rho.honest →
        NamedRun.emits S rho a.val_index (Object.attest a) ta →
        ta < Protocol.vote_time S.E (s + 1) →
        a.height_pair.erase.height? =
          some ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).h_max - 1) →
        fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
          some (Protocol.derive_named S.E S.cfg K).T_h →
        RunBlock S rho K →
        Block.compatible C.erase
          (Protocol.derive_named S.E S.cfg K).T_h = true)
    (hroots : ∀ w ∈ rho.honest, Block.compatible
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) B = true)
    (hanchors : ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w (s + 1)) B = true) :
    ProtectedVoteSlot S rho (s + 1) B := by
  have hheads : ∀ w ∈ rho.honest,
      Block.Preceq B (voterHeadAt S rho w (s + 1)) := by
    intro w hw
    exact genuineConfirmationWith_preceq_nextVoterHead_of_frontierWitnesses_of_delivery
      S adm hdelivery hcom hmajority hv hw hs hcap hhor hgenuine
      (hwitnesses w hw) (hroots w hw) (hanchors w hw)
  refine ⟨hheads, ?_⟩
  have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
    apply le_trans (le_of_lt ?_) hhor
    rw [← vote_time_succ_add_delta_eq_confirmation_time S.E s]
    exact Int.lt_add_of_pos_right _ S.E.Δ_pos
  intro w hw hcommittee
  obtain ⟨X, hXe, hXrun, hXemit⟩ := voterHeadEmits_of_core_local S adm hw
    (s := s + 1) (Nat.succ_pos s) hcommittee hvoteHor
  exact ⟨X, hXe ▸ hheads w hw, hXrun, hXemit⟩

#print axioms protectedVoteSlot_succ_of_genuineConfirmationWith_of_delivery


end WeakGoldfish
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
