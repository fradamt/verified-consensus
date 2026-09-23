module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.W4GSTZeroOpeningLifecycle
public import DecoupledConsensusProofs.Protocol.Grades.W4LaterRoundGrade
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.W4StableRecordGrowthFrom
public import DecoupledConsensusProofs.Generic.GSTZeroHealthy

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

namespace DecoupledConsensusModel
namespace Proofs

open Internal Execution Statements
open Proofs.HealingSurface
open Internal.NamedRecoveryRead Internal.PhaseGrades DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Prepared confirmation-write activity

The GST-zero grade step needs the proposal at the action read only in the
`FGRoot ⪯ P` arm. The confirmation write keeps its live value in the
prepared filtered tree. These are additive copies of the private activity
helpers in `HealingSurface/SeedFrontierRun.lean`; that module is not imported
because its moving frontier tail is outside this leaf's dependency cone. -/

private theorem w4_seedFrameAnchor_mem_filtered
    (cache : DecoupledConsensusModel.Protocol.Cache V) (E : Env V) (hc : Protocol.HealConfig)
    (st : Protocol.HealingStore V) (r : Round)
    (hroot : Protocol.get_fg_root st.toFG ∈
      Protocol.get_filtered_block_tree st.toFG) :
    Protocol.get_sg_root_with (DecoupledConsensusModel.Protocol.frameContract cache)
        E hc st r ∈ Protocol.get_filtered_block_tree st.toFG := by
  change DecoupledConsensusModel.Protocol.anchor E hc st r
    (DecoupledConsensusModel.Protocol.readFrame cache st r).g1 ∈
    Protocol.get_filtered_block_tree st.toFG
  cases hframe : (DecoupledConsensusModel.Protocol.readFrame cache st r).g1 with
  | none => exact hroot
  | some opt =>
    cases opt with
    | none => exact hroot
    | some root =>
      cases hactive : DecoupledConsensusModel.Protocol.activePrefix
          (Protocol.get_filtered_block_tree st.toFG) root with
      | none =>
        simpa only [DecoupledConsensusModel.Protocol.anchor, hactive,
          Option.getD_none] using hroot
      | some A =>
        simpa only [DecoupledConsensusModel.Protocol.anchor, hactive,
          Option.getD_some] using
          (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).1

private theorem w4_liveConfirmed_mem_filtered_actionStore
    (S : Setup V) (rho : Run V) (v : V) (r : Round) :
    (actionStoreAt S rho v r).live_confirmed ∈
      Protocol.get_filtered_block_tree
        (actionStoreAt S rho v r).toHealing.toFG := by
  let pre := rho.storeBeforeTime S v (S.a r)
  let ast := actionStoreAt S rho v r
  let cst := Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r)
  let confCache :=
    (NamedActionReads.confirmationReadAt S rho v (S.a r)).cache
  let gc := NamedProfile.gradeContract confCache
  have hrootPre : Protocol.get_fg_root pre.core.toHealing.toFG ∈
      Protocol.get_filtered_block_tree pre.core.toHealing.toFG := by
    simpa only [pre, Run.storeBeforeTime] using
      (named_fgRoot_mem_filtered_stateBeforeTime S rho (S.a r) v)
  have hrootAction : Protocol.get_fg_root ast.toHealing.toFG ∈
      Protocol.get_filtered_block_tree ast.toHealing.toFG := by
    rw [Proofs.HealingSurface.actionStoreAt_filteredTree S rho v r,
      Proofs.HealingSurface.actionStoreAt_fgRoot_eq_storeBeforeTime S rho v r]
    exact hrootPre
  have hrootConf : Protocol.get_fg_root cst.toHealing.toFG ∈
      Protocol.get_filtered_block_tree cst.toHealing.toFG := by
    rw [← Proofs.HealingSurface.actionStoreAt_filteredTree_eq_openingConfStore
      S rho v r, ← Proofs.HealingSurface.actionStoreAt_fgRoot_eq_openingConfStore
      S rho v r]
    exact hrootAction
  have hanchorConf : Protocol.get_sg_root_with gc S.E S.hc cst.toHealing
        (S.hc.round_of cst.s) ∈
      Protocol.get_filtered_block_tree cst.toHealing.toFG :=
    w4_seedFrameAnchor_mem_filtered confCache S.E S.hc cst.toHealing
      (S.hc.round_of cst.s) hrootConf
  have hliveUpdate :
      (Protocol.update_confirmation_with gc S.E S.hc cst
        (S.hc.opening_slot r)).live_confirmed ∈
        Protocol.get_filtered_block_tree cst.toHealing.toFG := by
    rw [Protocol.update_confirmation_with_live_confirmed]
    split
    · simpa only [Protocol.confWalkWith, Protocol.confAnchorWith,
        Protocol.confTree] using
        (Proofs.Records.ghost_mem_of _ _ hanchorConf (Finset.Subset.refl _))
    · simpa only [Protocol.confRoot] using hrootConf
  have hactionEq : ast.st.core =
      Protocol.update_confirmation_with gc S.E S.hc cst
        (S.hc.opening_slot r) := by
    change (actionStoreAt S rho v r).st.core =
      Protocol.update_confirmation_with
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadAt S rho v (S.a r)).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot r))
        (S.hc.opening_slot r)
    exact Proofs.HealingSurface.actionStoreAt_eq_update_confirmation_confStore
      S rho v r
  change ast.st.core.live_confirmed ∈
    Protocol.get_filtered_block_tree ast.toHealing.toFG
  rw [hactionEq]
  change (Protocol.update_confirmation_with gc S.E S.hc cst
    (S.hc.opening_slot r)).live_confirmed ∈
      Protocol.get_filtered_block_tree cst.toHealing.toFG
  exact hliveUpdate

theorem w4_proposal_mem_actionFilteredTree_gstZero
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {q : Round} (hq : 0 < q)
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot q) = some P)
    {k : Round} (hqk : q ≤ k) (hhor : S.a k ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (actionReadAt S rho v k).st.core.toHealing.toFG) P.erase) :
    P.erase ∈ PhaseGrades.filteredTree (actionReadAt S rho v k) := by
  have hlive := w4_proposal_preceq_actionLiveConfirmed_gstZero
    S h hq hprop hP hqk hhor v hv
  have hliveFiltered := w4_liveConfirmed_mem_filtered_actionStore S rho v k
  have hpc : ParentClosed (actionStoreAt S rho v k).st.core := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      Protocol.NamedStore.setClock] using
      Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho (S.a k) v
  have hliveTree : (actionStoreAt S rho v k).st.core.live_confirmed ∈
      (actionStoreAt S rho v k).st.core.T :=
    Proofs.Records.get_filtered_block_tree_subset _ hliveFiltered
  have hPtree : P.erase ∈ (actionStoreAt S rho v k).st.core.T :=
    Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2 (P.erase)
      (actionStoreAt S rho v k).st.core.live_confirmed hliveTree hlive
  have hFJ : Block.Preceq (actionStoreAt S rho v k).st.core.F
      (actionStoreAt S rho v k).st.core.J := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      Protocol.NamedStore.setClock] using
      Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
        (S.a k) v
  have hactiveStore : P.erase ∈
      Protocol.get_filtered_block_tree
        (actionStoreAt S rho v k).toHealing.toFG :=
    Proofs.Records.mem_filtered_of_preceq hFJ hliveFiltered hPtree hlive hroot
  simpa only [actionStoreAt, PhaseGrades.filteredTree] using hactiveStore

/-! ## Raw-tree grade bridge

`w4_preceq_nodeQ2_of_domainGrade` is intentionally stronger than the grade
step's natural input: a window carrier gives processed-tree membership, not
filtered-tree membership. Copy the pre-boundary bridge locally and keep the
raw-tree premise visible. -/

private theorem w4_preceq_actionQ2_of_domainGrade_mem
    (S : Setup V) {rho : Run V} (core : NamedAdmissibleCore S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} (hr : 0 < r)
    (hhor : S.a r ≤ rho.horizon) {C : Block V}
    (hmem : C ∈
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) v).st.core.T)
    (hgrade : PhaseGrades.storeGrade S.E S.hc
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) v).st r .g2 C = true)
    (hactive : C ∈ PhaseGrades.filteredTree (actionReadAt S rho v r)) :
    ∃ Q, nodeQ2 S (actionReadAt S rho v r) r = some Q ∧
      Block.Preceq C Q := by
  obtain ⟨raw, hfz, hCraw⟩ := NamedOutageClosure.q10_freeze_of_graded S.E
    (NamedRun.stateBeforeTime S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) v).st.core.toHealing.gradeView
    (NamedRun.stateBeforeTime S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) v).st.core.F
    S.hc.η_SG r (NamedOutageClosure.q10_early_le_late S r .g2)
    hmem hgrade
  have hFC : Block.Preceq (actionReadAt S rho v r).st.core.F C :=
    NamedOutageClosure.q10_filtered_F hactive
  have hcompat : Block.compatible C
      (actionReadAt S rho v r).st.core.F = true := by
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr hFC
  have hCclip : Block.Preceq C
      (DecoupledConsensusModel.Protocol.clipGrade raw
        (actionReadAt S rho v r).st.core.F) :=
    (NamedOutageClosure.q10_retained_prefix raw
      (actionReadAt S rho v r).st.core.F C hcompat).mpr hCraw
  obtain ⟨Q, hQ, hCQ⟩ := NamedOutageClosure.q10_activePrefix_dominates
    hactive hCclip
  refine ⟨Q, ?_, hCQ⟩
  change DecoupledConsensusModel.Protocol.grade2Block
      (actionReadAt S rho v r).st.core.toHealing
      (DecoupledConsensusModel.Protocol.readFrame (actionReadAt S rho v r).cache
        (actionReadAt S rho v r).st.core.toHealing r) = some Q
  unfold DecoupledConsensusModel.Protocol.grade2Block
  rw [if_pos (Proofs.HealingSurface.actionFrame_allClosed S core hv hr hhor),
    Proofs.HealingSurface.actionFrame_g2 S core hv hr hhor,
    show PhaseGrades.storeRoot S.E S.hc
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) v).st r .g2 =
      some raw from hfz]
  exact hQ

private theorem w4_confirmation_time_mono_slots
    (E : Env V) {a b : Slot} (hab : a ≤ b) :
    Protocol.confirmation_time E a ≤ Protocol.confirmation_time E b := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ,
    Protocol.confirmation_time_eq_support_cutoff_succ]
  exact Proofs.Optimistic.support_cutoff_mono E (Nat.add_le_add_right hab 1)


private theorem w4_awakeRound_subset_honestRoundVoters
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {r : Round} (hhor : S.a r ≤ rho.horizon) :
    rho.honest.filter (fun v => (S.node v).awake r = true) ⊆
      Internal.NamedOutageEntry.honestRoundVoters S rho r := by
  intro u hu
  obtain ⟨huHon, huAwake⟩ := Finset.mem_filter.mp hu
  refine (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u r).mpr ?_
  exact ⟨huHon, actionAttestationAt S rho u r,
    (actionAttestationAt_shape S rho u r).1,
    (actionAttestationAt_shape S rho u r).2.1,
    honest_emits_exact_actionAttestationAt_of_awake S sch huHon r huAwake hhor⟩

/-! ## GST-zero window inputs

The source bound is indexed by the grade round `d`, but its last confirmed
slot is the opening slot of `d`. This is the horizon shape needed by the
corrected grade guard `S.a d ≤ rho.horizon`; no future `S.a (d+1)` premise is
introduced. -/

theorem w4_gstZeroWindowCarrier_and_ready
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {q d : Round} (hq : 0 < q) (hd : 0 < d)
    (hspan : q ≤ d - S.hc.η_SG)
    {P : NamedBlock V}
    (hcover : ∀ j : Round, q ≤ j → j < d →
      0 < j → S.a j ≤ rho.horizon →
      Protocol.confirmation_time S.E (S.hc.opening_slot j + 1) ≤
        rho.horizon →
      ∀ u ∈ Internal.NamedOutageEntry.honestRoundVoters S rho j,
        Block.Preceq P.erase (actionSGBlockAt S rho u j))
    (hhor : S.a d ≤ rho.horizon) :
    W4StableWrite.W4WindowCarrierAt S rho d P.erase ∧
      W4StableWrite.W4WindowReadyAt S rho d := by
  have hdelivery : NamedHealthyPrefixDelivery S rho rho.horizon :=
    NamedGSTZeroHealthy.healthyPrefixDelivery_of_gstZero S rho
      h.core h.gstZero
  have hprevHor : S.a (d - 1) ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.sub_le d 1)).trans hhor
  have hawake : AwakeWindowMajority S.E (fun v => (S.node v).awake)
      rho.honest S.hc.η_SG d := h.windows d hd hprevHor
  obtain ⟨x, hx⟩ := Protocol.honest_nonempty_of_honestCommittees
    h.committees
  have hlastHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot d) ≤ rho.horizon := by
    simpa only [Proofs.HealingSurface.opening_confirmation_time_eq_action S d] using
      hhor
  have hdslot : 1 ≤ S.hc.opening_slot d + 1 := by
    exact Nat.succ_le_succ (Nat.zero_le _)
  have hsg : ∀ j, q ≤ j → j < d → ∀ u ∈ rho.honest,
      NamedRun.emits S rho u
        (Object.attest (actionAttestationAt S rho u j)) (S.a j) →
      Block.Preceq (actionSGBlockAt S rho u j)
        (Protocol.voteDutyHead S rho x (S.hc.opening_slot d + 1)) := by
    intro j hqj hjd u hu hemit
    have hact : S.a j < Protocol.vote_time S.E
        (S.hc.opening_slot d + 1 + 1) :=
      lt_of_le_of_lt (Assembly.a_mono S (Nat.le_of_lt hjd))
        (Protocol.action_lt_vote_time_two_after S d)
    exact (WeakGenesis.actionSources_preceq_voteDutyHead_of_gstZero S
      h.core h.committees h.gstZero h.windows hlastHor hdslot
      (Nat.le_refl _) hx j hact).1 u hu hemit
  have hroots : ∀ w ∈ rho.honest,
      Block.Preceq (Protocol.get_fg_root
        (actionStoreAt S rho w d).st.core.toHealing.toFG)
        (Protocol.voteDutyHead S rho x (S.hc.opening_slot d + 1)) := by
    intro w hw
    have hact : S.a d < Protocol.vote_time S.E
        (S.hc.opening_slot d + 1 + 1) :=
      Protocol.action_lt_vote_time_two_after S d
    exact (WeakGenesis.actionSources_preceq_voteDutyHead_of_gstZero S
      h.core h.committees h.gstZero h.windows hlastHor hdslot
      (Nat.le_refl _) hx d hact).2 w hw |>.1
  have hcap : DecoupledConsensusModel.Protocol.domain S.E S.hc d .g2 ≤ rho.horizon :=
    (FrameForward.domain_le_a S d .g2).trans hhor
  have hcover' : ∀ j : Round, d - S.hc.η_SG ≤ j → j < d →
      ∀ u ∈ Internal.NamedOutageEntry.honestRoundVoters S rho j,
        Block.Preceq P.erase (actionSGBlockAt S rho u j) := by
    intro j hjlo hjhi u hu
    have hqj : q ≤ j := hspan.trans hjlo
    have hjpos : 0 < j := Nat.lt_of_lt_of_le hq hqj
    have hjhor : S.a j ≤ rho.horizon :=
      (Assembly.a_mono S (Nat.le_of_lt hjhi)).trans hhor
    have hjslot : S.hc.opening_slot j + 1 ≤
        S.hc.opening_slot (j + 1) := by
      simp only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
      exact Nat.add_le_add_left
        ((by decide : (1 : Nat) ≤ 2).trans S.hc.R_ge_two) (j * S.hc.R)
    have hjnextAction : S.a (j + 1) ≤ rho.horizon :=
      (Assembly.a_mono S (Nat.succ_le_of_lt hjhi)).trans hhor
    have hjnext : Protocol.confirmation_time S.E
        (S.hc.opening_slot j + 1) ≤ rho.horizon := by
      exact (w4_confirmation_time_mono_slots S.E hjslot).trans
        (by simpa only [Proofs.HealingSurface.opening_confirmation_time_eq_action]
          using hjnextAction)
    exact hcover j hqj hjhi hjpos hjhor hjnext u hu
  exact W4StableWrite.w4_windowCarrier_and_ready_of_delivery S h.core
    hdelivery le_rfl hd hspan hawake hsg hroots hcap hcover'

/-! ## Grade-free GST-zero cover step

The selected-Q2 arm in the FG-root write case is already above the FG root:
`actionQ2_mem_filteredTree` and `preceq_get_fg_root_of_mem_filtered` provide
that order. Therefore the cover step is independent of the grade step,
including during the first `η_SG - 1` rounds. -/

theorem w4_persistenceCoverStep_gstZero_of_localReads
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {q : Round} (hq : 0 < q)
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot q) = some P)
    {k : Round} (hk : 0 < k) (hqk : q ≤ k)
    (hhor : S.a k ≤ rho.horizon)
    (hnext : Protocol.confirmation_time S.E
      (S.hc.opening_slot k + 1) ≤ rho.horizon) :
    ∀ u ∈ rho.honest,
      Block.Preceq P.erase (actionSGBlockAt S rho u k) := by
  intro u hu
  have hlive : Block.Preceq P.erase
      (actionStoreAt S rho u k).st.core.live_confirmed :=
    w4_proposal_preceq_actionLiveConfirmed_gstZero S h hq hprop hP hqk hhor
      u hu
  rcases w4_anchor_preceq_liveConfirmed_or_fgRoot S rho u k with hanch | hroot
  · have hvote : actionSGBlockAt S rho u k =
        (actionStoreAt S rho u k).st.core.live_confirmed :=
      w4_actionSGBlockAt_eq_liveConfirmed S rfl (Block.preceq_self _) rfl
        hanch (w4_nodeClear_liveConfirmed_gstZero S h hk hu hhor hnext)
    rw [hvote]
    exact hlive
  · have hBfg : Block.Preceq P.erase
        (Protocol.get_fg_root
          (actionReadAt S rho u k).st.core.toHealing.toFG) := by
      rw [← hroot]
      exact hlive
    have hBanchor : Block.Preceq P.erase
        (nodeAnchor S (actionReadAt S rho u k) k) :=
      Block.preceq_trans hBfg
        (w4_fgRoot_preceq_nodeAnchor S (actionReadAt S rho u k) k)
    rcases Proofs.HealingSurface.actionSGBlockAt_tiers S rho u k with
      ⟨hA, -, -⟩ | ⟨Q, hQ, hvote⟩ | ⟨-, -, hvote⟩ | ⟨-, -, hvote⟩
    · exact Block.preceq_trans hBanchor hA
    · rw [hvote]
      exact Block.preceq_trans hBfg
        (Proofs.Records.preceq_get_fg_root_of_mem_filtered
          (Proofs.HealingSurface.actionQ2_mem_filteredTree S rho u k hQ))
    · rw [hvote]
      exact hBfg
    · rw [hvote]
      exact hBanchor

/-! ## The corrected GST-zero grade step -/

def W4GSTZeroCoverLagged (S : Setup V) (rho : Run V)
    (q : Round) (P : NamedBlock V) (k : Round) : Prop :=
  q ≤ k → 0 < k → S.a k ≤ rho.horizon →
    Protocol.confirmation_time S.E (S.hc.opening_slot k + 1) ≤
      rho.horizon →
    ∀ u ∈ rho.honest,
      Block.Preceq P.erase (actionSGBlockAt S rho u k)

def W4GSTZeroGradeLagged (S : Setup V) (rho : Run V)
    (q : Round) (P : NamedBlock V) (k : Round) : Prop :=
  q + S.hc.η_SG ≤ k → 0 < k → S.a k ≤ rho.horizon →
    ∀ u ∈ rho.honest, ∀ Q : Block V,
      nodeQ2 S (actionReadAt S rho u k) k = some Q →
        Block.Preceq P.erase Q

theorem w4_gstZeroGradeStep
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {q : Round} (hq : 0 < q)
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot q) = some P) :
    ∀ k : Round,
      (∀ j : Round, j < k → W4GSTZeroCoverLagged S rho q P j) →
      (∀ j : Round, j < k → W4GSTZeroGradeLagged S rho q P j) →
      W4GSTZeroGradeLagged S rho q P k := by
  intro k hC _hG hkguard hkpos hhor
  have hspan : q ≤ k - S.hc.η_SG := Nat.le_sub_of_add_le hkguard
  have hcover : ∀ j : Round, q ≤ j → j < k →
      0 < j → S.a j ≤ rho.horizon →
      Protocol.confirmation_time S.E (S.hc.opening_slot j + 1) ≤
        rho.horizon →
      ∀ u ∈ Internal.NamedOutageEntry.honestRoundVoters S rho j,
        Block.Preceq P.erase (actionSGBlockAt S rho u j) := by
    intro j hqj hjk hjpos hjhor hjnext u hu
    exact hC j hjk hqj hjpos hjhor hjnext u
      (((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u j).mp hu).1)
  have hwindow := w4_gstZeroWindowCarrier_and_ready S h hq hkpos hspan
    hcover (P := P) hhor
  have hprevHor : S.a (k - 1) ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.sub_le k 1)).trans hhor
  have hmajority : AwakeWindowMajority S.E (fun v => (S.node v).awake)
      rho.honest S.hc.η_SG k := h.windows k hkpos hprevHor
  have hdomHor : DecoupledConsensusModel.Protocol.domain S.E S.hc k .g2 ≤ rho.horizon :=
    (FrameForward.domain_le_a S k .g2).trans hhor
  intro u hu Q hQ
  have hqk : q ≤ k :=
    (Nat.le_add_right q S.hc.η_SG).trans hkguard
  have hQroot : Block.Preceq
      (Protocol.get_fg_root
        (actionReadAt S rho u k).st.core.toHealing.toFG) Q :=
    Proofs.Records.preceq_get_fg_root_of_mem_filtered
      (Proofs.HealingSurface.actionQ2_mem_filteredTree S rho u k hQ)
  let R := Protocol.get_fg_root
    (actionReadAt S rho u k).st.core.toHealing.toFG
  have hPfg_or_hfgP : Block.Preceq P.erase R ∨
      Block.Preceq R P.erase := by
    rcases w4_anchor_preceq_liveConfirmed_or_fgRoot S rho u k with hanch | hroot
    · have hrootAnchor : Block.Preceq R
          (nodeAnchor S (actionReadAt S rho u k) k) :=
        w4_fgRoot_preceq_nodeAnchor S (actionReadAt S rho u k) k
      have hanchorComp := w4_actionAnchor_compatible_openingProposal_gstZero
        S h hq hprop hP hqk hhor u hu
      rcases (show Block.Preceq
          (nodeAnchor S (actionReadAt S rho u k) k) P.erase ∨
          Block.Preceq P.erase
            (nodeAnchor S (actionReadAt S rho u k) k) by
        simpa only [Block.compatible, Bool.or_eq_true] using hanchorComp) with
      hAP | hPA
      · exact Or.inr (Block.preceq_trans hrootAnchor hAP)
      · have hrootComp : Block.compatible R P.erase = true :=
          Block.compatible_of_preceq_common hrootAnchor hPA
        have hrootComp' : Block.Preceq R P.erase ∨
            Block.Preceq P.erase R := by
          simpa only [Block.compatible, Bool.or_eq_true] using hrootComp
        rcases hrootComp' with hRP | hPR
        · exact Or.inr hRP
        · exact Or.inl hPR
    · have hlive := w4_proposal_preceq_actionLiveConfirmed_gstZero
        S h hq hprop hP hqk hhor u hu
      have hliveR := hlive
      rw [hroot] at hliveR
      exact Or.inl (by simpa only [R] using hliveR)
  rcases hPfg_or_hfgP with hPfg | hfgP
  · exact Block.preceq_trans hPfg hQroot
  · have hactive := w4_proposal_mem_actionFilteredTree_gstZero S h hq hprop
      hP hqk hhor hu hfgP
    have hmem : P.erase ∈
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc k .g2) u).st.core.T := by
      have hne :
          (Execution.honestAwakeWindow (fun x => (S.node x).awake)
            rho.honest S.hc.η_SG k).Nonempty := by
        rcases Finset.eq_empty_or_nonempty
            (Execution.honestAwakeWindow (fun x => (S.node x).awake)
              rho.honest S.hc.η_SG k) with hempty | hsome
        · exfalso
          have hlt := hmajority
          simp only [Execution.AwakeWindowMajority, hempty,
            Electorate.weightOf, Finset.sum_empty] at hlt
          exact Nat.not_lt_zero _ hlt
        · exact hsome
      obtain ⟨u0, hu0⟩ := hne
      obtain ⟨hu0Hon, k0, hk0mem, hk0awake⟩ :=
        WeakSG.mem_honestAwakeWindow_iff.mp hu0
      have hk0lt : k0 < k := mem_latestWindow_lt hk0mem
      have hk0pos : 0 < k0 := Nat.lt_of_lt_of_le hq
        (hspan.trans (WeakSG.mem_latestWindow_lower_bound hk0mem))
      have hk0hor : S.a k0 ≤ rho.horizon :=
        (Assembly.a_mono S (Nat.le_of_lt hk0lt)).trans hhor
      have huVoter : u0 ∈
          Internal.NamedOutageEntry.honestRoundVoters S rho k0 :=
        w4_awakeRound_subset_honestRoundVoters S
          h.core.toNamedScheduleWellFormed hk0hor
          (Finset.mem_filter.mpr ⟨hu0Hon, hk0awake⟩)
      have hk0nextAction : S.a (k0 + 1) ≤ rho.horizon :=
        (Assembly.a_mono S (Nat.succ_le_of_lt hk0lt)).trans hhor
      have hk0slot : S.hc.opening_slot k0 + 1 ≤
          S.hc.opening_slot (k0 + 1) := by
        simp only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
        exact Nat.add_le_add_left
          ((by decide : (1 : Nat) ≤ 2).trans S.hc.R_ge_two)
          (k0 * S.hc.R)
      have hk0next : Protocol.confirmation_time S.E
          (S.hc.opening_slot k0 + 1) ≤ rho.horizon :=
        (w4_confirmation_time_mono_slots S.E hk0slot).trans (by
          simpa only [Proofs.HealingSurface.opening_confirmation_time_eq_action]
            using hk0nextAction)
      have hcov := hcover k0
        (hspan.trans (WeakSG.mem_latestWindow_lower_bound hk0mem))
        hk0lt hk0pos hk0hor hk0next u0 huVoter
      obtain ⟨_, hfind⟩ := hwindow.1 u hu k0
        (by exact WeakSG.mem_latestWindow_lower_bound hk0mem)
        hk0lt u0 huVoter
      have hmemSG := Proofs.Records.mem_of_bind_find?
        (o := some (actionSGBlockAt S rho u0 k0).root) hfind
      have hpc := (parentClosed_iff _).mp
        (Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc k .g2) u)
      exact Proofs.Records.mem_of_preceq hpc.2 P.erase
        (actionSGBlockAt S rho u0 k0) hmemSG hcov
    have hpositive :=
      W4StableWrite.w4_awakeWindow_subset_phaseSupporters_of_windowCarrier
        S h.core hkpos hdomHor hwindow.1 hwindow.2 hu
    have hopposing :=
      W4StableWrite.w4_phaseOpponents_subset_faulty_of_windowCarrier
        S h.core hkpos hdomHor hwindow.1 hu
    have hgrade := W4StableWrite.storeGrade_g2_of_awakeWindowMajority
      S hmajority hpositive hopposing
    obtain ⟨Q', hQ', hPQ'⟩ := w4_preceq_actionQ2_of_domainGrade_mem
      S h.core hu hkpos hhor hmem hgrade hactive
    have hQQ : Q = Q' := Option.some.inj (hQ.symm.trans hQ')
    rw [hQQ]
    exact hPQ'

/-! ## The lagged joint induction and stable write -/

theorem w4_persistenceCover_gstZero_lagged_of_gradeStep
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {q : Round} (hq : 0 < q)
    (hprop : S.E.proposer (S.hc.opening_slot q) ∈ rho.honest)
    {P : NamedBlock V}
    (hP : proposedBlockAt S rho (S.hc.opening_slot q) = some P)
    (hgradeStep : ∀ k : Round,
      (∀ j : Round, j < k → W4GSTZeroCoverLagged S rho q P j) →
      (∀ j : Round, j < k → W4GSTZeroGradeLagged S rho q P j) →
      W4GSTZeroGradeLagged S rho q P k) :
    ∀ k : Round, W4GSTZeroCoverLagged S rho q P k := by
  have hcoverStep : ∀ k : Round,
      (∀ j : Round, j < k → W4GSTZeroCoverLagged S rho q P j) →
      (∀ j : Round, j < k → W4GSTZeroGradeLagged S rho q P j) →
      W4GSTZeroGradeLagged S rho q P k →
      W4GSTZeroCoverLagged S rho q P k := by
    intro k _hC _hG _hGk hqk hkpos hhor hnext
    exact w4_persistenceCoverStep_gstZero_of_localReads S h hq hprop hP
      hkpos hqk hhor hnext
  exact W4CoverGrade.cover_of_steps
    (W4GSTZeroCoverLagged S rho q P)
    (W4GSTZeroGradeLagged S rho q P)
    hgradeStep hcoverStep

theorem w4StableWriteWithinFrom_gstZero
    (S : Setup V) :
    ∀ rho, WeakGenesis S rho → W4StableWrite.W4StableWriteWithinFrom S rho := by
  intro rho h
  apply W4StableWrite.w4StableWriteWithinFrom_of_dutyCover S h.core
    h.core.toNamedScheduleWellFormed
  intro q hq hprop P hP hhor
  have hdpos : 0 < q + S.hc.η_SG := by
    exact Nat.lt_of_lt_of_le hq (Nat.le_add_right q _)
  have hqle : q ≤ q + S.hc.η_SG := Nat.le_add_right q _
  have hqd : q < q + S.hc.η_SG := by
    exact Nat.lt_add_of_pos_right S.hc.η_SG_ge_one
  have hgradeStep : ∀ k : Round,
      (∀ j : Round, j < k → W4GSTZeroCoverLagged S rho q P j) →
      (∀ j : Round, j < k → W4GSTZeroGradeLagged S rho q P j) →
      W4GSTZeroGradeLagged S rho q P k :=
    w4_gstZeroGradeStep S h hq hprop hP
  have hcoverAll := w4_persistenceCover_gstZero_lagged_of_gradeStep
    S h hq hprop hP hgradeStep
  refine ⟨q + S.hc.η_SG, hqd, le_rfl, ?_⟩
  intro v hv
  have hspan : q ≤ (q + S.hc.η_SG) - S.hc.η_SG := by
    simpa only [Nat.add_sub_cancel] using (Nat.le_refl q)
  have hcover : ∀ j : Round, q ≤ j → j < q + S.hc.η_SG →
      0 < j → S.a j ≤ rho.horizon →
      Protocol.confirmation_time S.E (S.hc.opening_slot j + 1) ≤
        rho.horizon →
      ∀ u ∈ Internal.NamedOutageEntry.honestRoundVoters S rho j,
        Block.Preceq P.erase (actionSGBlockAt S rho u j) := by
    intro j hqj hjd hjpos hjhor hjnext u hu
    exact hcoverAll j hqj hjpos hjhor hjnext u
      (((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u j).mp hu).1)
  have hwindow := w4_gstZeroWindowCarrier_and_ready S h hq hdpos hspan
    hcover (P := P) hhor
  have hprevHor : S.a ((q + S.hc.η_SG) - 1) ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.sub_le _ 1)).trans hhor
  have hmajority : AwakeWindowMajority S.E (fun x => (S.node x).awake)
      rho.honest S.hc.η_SG (q + S.hc.η_SG) :=
    h.windows (q + S.hc.η_SG) hdpos hprevHor
  have hdomHor : DecoupledConsensusModel.Protocol.domain S.E S.hc
      (q + S.hc.η_SG) .g2 ≤ rho.horizon :=
    (FrameForward.domain_le_a S (q + S.hc.η_SG) .g2).trans hhor
  have hmem : P.erase ∈
      (NamedRun.stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + S.hc.η_SG) .g2) v).st.core.T := by
    have hne :
        (Execution.honestAwakeWindow (fun x => (S.node x).awake)
          rho.honest S.hc.η_SG (q + S.hc.η_SG)).Nonempty := by
      rcases Finset.eq_empty_or_nonempty
          (Execution.honestAwakeWindow (fun x => (S.node x).awake)
            rho.honest S.hc.η_SG (q + S.hc.η_SG)) with hempty | hsome
      · exfalso
        have hlt := hmajority
        simp only [Execution.AwakeWindowMajority, hempty,
          Electorate.weightOf, Finset.sum_empty] at hlt
        exact Nat.not_lt_zero _ hlt
      · exact hsome
    obtain ⟨u0, hu0⟩ := hne
    obtain ⟨hu0Hon, k0, hk0mem, hk0awake⟩ :=
      WeakSG.mem_honestAwakeWindow_iff.mp hu0
    have hk0lt : k0 < q + S.hc.η_SG := mem_latestWindow_lt hk0mem
    have hk0hor : S.a k0 ≤ rho.horizon :=
      (Assembly.a_mono S (Nat.le_of_lt hk0lt)).trans hhor
    have huVoter : u0 ∈
        Internal.NamedOutageEntry.honestRoundVoters S rho k0 :=
      w4_awakeRound_subset_honestRoundVoters S
        h.core.toNamedScheduleWellFormed hk0hor
        (Finset.mem_filter.mpr ⟨hu0Hon, hk0awake⟩)
    have hcov := hcover k0
      (hspan.trans (WeakSG.mem_latestWindow_lower_bound hk0mem)) hk0lt
      (Nat.lt_of_lt_of_le hq (hspan.trans
        (WeakSG.mem_latestWindow_lower_bound hk0mem))) hk0hor
      (by
        have hslot : S.hc.opening_slot k0 + 1 ≤
            S.hc.opening_slot (k0 + 1) := by
          simp only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul]
          exact Nat.add_le_add_left
            ((by decide : (1 : Nat) ≤ 2).trans S.hc.R_ge_two)
            (k0 * S.hc.R)
        exact (w4_confirmation_time_mono_slots S.E hslot).trans (by
          simpa only [Proofs.HealingSurface.opening_confirmation_time_eq_action]
            using (Assembly.a_mono S (Nat.succ_le_of_lt hk0lt)).trans hhor))
      u0 huVoter
    obtain ⟨_, hfind⟩ := hwindow.1 v hv k0
      (WeakSG.mem_latestWindow_lower_bound hk0mem) hk0lt u0 huVoter
    have hmemSG := Proofs.Records.mem_of_bind_find?
      (o := some (actionSGBlockAt S rho u0 k0).root) hfind
    have hpc := (parentClosed_iff _).mp
      (Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc (q + S.hc.η_SG) .g2) v)
    exact Proofs.Records.mem_of_preceq hpc.2 P.erase
      (actionSGBlockAt S rho u0 k0) hmemSG hcov
  have hpositive :=
    W4StableWrite.w4_awakeWindow_subset_phaseSupporters_of_windowCarrier
      S h.core hdpos hdomHor hwindow.1 hwindow.2 hv
  have hopposing :=
    W4StableWrite.w4_phaseOpponents_subset_faulty_of_windowCarrier
      S h.core hdpos hdomHor hwindow.1 hv
  have hlocal := W4StableWrite.localG2CoverAtDutyRound_of_awakeWindowMajority
    S hdpos hmem hmajority hpositive hopposing
  exact W4StableWrite.dutyCoverAt_of_viable_and_localG2 S
    (w4_proposalViableAtDutyRound_gstZero S h hq hqd hprop hP hhor v hv)
    hlocal

theorem stableRecordGrowth_gstZero_lagged
    (S : Setup V) :
    ∀ rho, WeakGenesis S rho →
      ∀ gap, ProposerOpeningCarrierRecurrence S rho gap →
        StableRecordGrowthFrom S rho 0
          (gap + S.hc.η_SG - 1) := by
  intro rho h gap hrec
  have hsafe : GSTZeroGuarantees S rho :=
    Proofs.HealingSurface.gstZeroGuarantees_of_weakGenesis S rho h
  have hcanon : StableRecordCanonicalFrom S rho 0 :=
    Proofs.HealingSurface.Handover.stableRecordSafety_gstZero_clean S rho h
  have hmono : ConfirmationMonotoneFrom S rho 0 := hsafe.availableChain.2.1
  exact W4StableWrite.stableRecordGrowthFrom_of_openingWriteWithin S h.core
    (Proofs.Optimistic.confirmation_time_nonneg S.E 0) hrec hmono
    hsafe.userProposals hcanon
    (w4StableWriteWithinFrom_gstZero S rho h)

#print axioms w4_proposal_mem_actionFilteredTree_gstZero
#print axioms w4_gstZeroWindowCarrier_and_ready
#print axioms w4_persistenceCoverStep_gstZero_of_localReads
#print axioms w4_gstZeroGradeStep
#print axioms w4_persistenceCover_gstZero_lagged_of_gradeStep
#print axioms w4StableWriteWithinFrom_gstZero
#print axioms stableRecordGrowth_gstZero_lagged

end Proofs
end DecoupledConsensusModel

end
