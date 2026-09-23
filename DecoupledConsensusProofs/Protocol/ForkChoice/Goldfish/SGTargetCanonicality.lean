module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ExcludesRefute
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.AdoptionRun
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryHandoffCore
public import DecoupledConsensusProofs.Protocol.Schedule.PostHealingContinuation
public import DecoupledConsensusProofs.Execution.StoreFinalityCore
public import DecoupledConsensusProofs.Execution.RecoveryActionCarrierG0Compatibility
public import DecoupledConsensusProofs.Execution.ReleasedCertificateHeightProgress
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Execution.RecoveryActionLiveSourceSplit
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryCapturedSlotInterval
public import DecoupledConsensusProofs.Execution.RecoveryCapturedConeFold
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FinalityFilterInterference
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ReaderLocalCone
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HonestMajorityCore
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionHistory
public import DecoupledConsensusProofs.Generic.SuffixHistory
public import DecoupledConsensusProofs.Protocol.Handlers.StoreFinality
public import DecoupledConsensusProofs.Protocol.ChainState.JustificationCertificates
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Protocol.Grades.ProposalParent
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordClean
public import DecoupledConsensusProofs.Generic.EvaluationStore
public import DecoupledConsensusProofs.Objects.EmittedHeightBound
public import DecoupledConsensusProofs.Objects.FixedHeightRootCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoverySelectedActionG2VoteCone
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryFinalityFilterRetainedVoteConeSeed
public import DecoupledConsensusProofs.Objects.SGTargetG1Concentration
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.GoldfishCone
public import DecoupledConsensusProofs.Protocol.Schedule.WeakProcessedTree
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Execution.Wire

@[expose] public section

/-!
# Live-grade canonicality of action SG targets

This file proves the first Roberto claim. The interface supplies the frozen G1
and G0 roots used at each prepared read and finality-filter quietness. A
selected Q2 is below the prepared G1 root. A clear target uses its genuine
confirmed descendant to construct the exact frozen candidate path. The G0
root gives compatibility between the prepared voter anchor and that target.

The source `live_confirmed` split is explicit. A genuine opening confirmation
uses the retained-descendant recurrence. An FG-root fallback makes a clear
target equal to the selected G2. Since live grades select that G2, the raw
anchor fallback of `get_sg_vote` is unreachable. At each Goldfish vote,
live-grade totality makes the `fresh_anchor = none` case impossible.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]



/-
/-- A processed descendant of an exact selected FG root remains in the
filtered block tree when that root is within one height of the local
frontier. -/
theorem mem_filtered_of_mem_tree_of_exactFGRoot_heightCap
    (E: Env V) (hc: Protocol.HealConfig)
    (cfg: Protocol.HeightConfig)
    (nd: Protocol.Node V)
    {st: Protocol.Store V} {J B: Block V}
    (hst: DepReachableStore E hc cfg nd st)
    (hB: B ∈ st.T)
    (hroot:
      Protocol.get_fg_root st.toHealing.toFG = J)
    (hJB: Block.Preceq J B)
    (hcap: st.h_max ≤ (derived_state E cfg J).h + 1):
    B ∈ Protocol.get_filtered_block_tree st.toHealing.toFG:= by
  have hreachable: ReachableStore E hc cfg nd st:=
    Proofs.Bridges.reachableStore_of_depReachableStore
      E hc cfg nd hst
  have hFJ: Block.Preceq st.F st.J:=
    (storeFinality_reachable E hc cfg nd st hreachable).2
  have hFroot: Block.Preceq st.F
      (Protocol.get_fg_root st.toHealing.toFG):=
    Proofs.Records.preceq_get_fg_root_of_F
      (st:= st.toHealing.toFG) hFJ
  have hrootB: Block.Preceq
      (Protocol.get_fg_root st.toHealing.toFG) B:= by
    rw [hroot]
    exact hJB
  have hFB: Block.Preceq st.F B:=
    Block.preceq_trans hFroot hrootB
  have hagree: DerivedStateAgrees E cfg st:=
    derivedStateAgrees_depReachable E hc cfg nd st hst
  have hheight:
      st.h_max - 1 ≤ (st.σ B).h:= by
    rw [hagree B hB]
    exact (Nat.sub_le_iff_le_add.mpr hcap).trans
      (Protocol.derived_h_mono E cfg hJB)
  have hV: B ∈ Protocol.V_tree st.toHealing.toFG:= by
    simp only [Protocol.V_tree, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq, Protocol.Store.toHealing]
    exact ⟨⟨hB, hFB⟩, B, hB, Block.preceq_self B, hheight⟩
  exact Proofs.Records.mem_filtered_of_mem_V_tree hV hrootB


-/

/-! ## Named filtered-tree leaf -/

/-- A retained named descendant of an exact FG root remains in the filtered
block tree under the local one-step height cap. -/
theorem mem_filtered_of_mem_tree_of_exactFGRoot_heightCap
    (S : Setup V) (rho : Run V) (w : V) (read : Time)
    {J B : Block V} {Bn : NamedBlock V}
    (hBn : Bn ∈ (rho.storeBeforeTime S w read).bodies)
    (hB : Bn.erase = B)
    (hroot : Protocol.get_fg_root
      (rho.storeBeforeTime S w read).toHealing.toFG = J)
    (hJB : Block.Preceq J B)
    (hcap : (rho.storeBeforeTime S w read).h_max ≤
      (Protocol.derive_named S.E S.cfg Bn).h + 1) :
    B ∈ Protocol.get_filtered_block_tree
      (rho.storeBeforeTime S w read).toHealing.toFG := by
  let st := rho.storeBeforeTime S w read
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg st := by
    simpa only [st, Run.storeBeforeTime] using
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho read w).1.1.1
  have hBmem : B ∈ st.core.T := by
    rw [hcoh.1, ← hB]
    exact Finset.mem_image_of_mem NamedBlock.erase hBn
  have hFJ : Block.Preceq st.F st.J :=
    Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho read w
  have hFroot : Block.Preceq st.F
      (Protocol.get_fg_root st.toHealing.toFG) :=
    Proofs.Records.preceq_get_fg_root_of_F (st := st.toHealing.toFG) hFJ
  have hrootB : Block.Preceq
      (Protocol.get_fg_root st.toHealing.toFG) B := by
    rw [hroot]
    exact hJB
  have hFB : Block.Preceq st.F B := Block.preceq_trans hFroot hrootB
  have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho read w Bn hBn
  have hσ : st.σ B = Protocol.derive_named S.E S.cfg Bn := by
    simpa only [st, hB] using hview
  have hheight : st.h_max - 1 ≤ (st.σ B).h := by
    rw [hσ]
    exact Nat.sub_le_iff_le_add.mpr hcap
  have hV : B ∈ Protocol.V_tree st.toHealing.toFG := by
    simp only [Protocol.V_tree, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq, Protocol.Store.toHealing]
    exact ⟨⟨hBmem, hFB⟩, B, hBmem, Block.preceq_self B, hheight⟩
  exact Proofs.Records.mem_filtered_of_mem_V_tree hV hrootB






/-
/-- A certified prefix at a common fixed frontier keeps the finality filters
quiet at every caller-selected actual read. -/
theorem finalityFilterQuietOn_of_fixedFrontier_certifiedPrefix
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    (hsb: SlashableBound S rho)
    {H: Height} {C T: Block V}
    (hCrun: RunBlock S rho C)
    (hcert: Certificate S rho (H - 1) C.root)
    (hCT: Block.Preceq C T)
    (hTrun: RunBlock S rho T)
    (hTheight: H ≤ (derived_state S.E S.cfg T).h)
    {IsRead: V → Time → Prop}
    (hreadLe: ∀ w, w ∈ rho.honest → ∀ read, IsRead w read →
      read ≤ rho.horizon)
    (hTmem: ∀ w, w ∈ rho.honest → ∀ read, IsRead w read →
      T ∈ (rho.storeBeforeTime S w read).T)
    (hfrontier: ∀ w, w ∈ rho.honest → ∀ read, IsRead w read →
      (rho.storeBeforeTime S w read).h_max = H):
    FinalityFilterQuietOn S rho T IsRead:= by
  intro w hw read hread
  exact finalityFilterNoninterferenceAtRead_of_fixedFrontier_certifiedPrefix
    S adm hfb hsb hw (hreadLe w hw read hread)
      (hTmem w hw read hread) hTrun hTheight
      (hfrontier w hw read hread) hCrun hcert hCT

/-- A rebased common grade transfers a certified fixed frontier to the exact
SG action target selected by an honest source. -/
theorem getFGRoot_compatible_actionSGBlockAt_of_rebasedGrade_fixedFrontier
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    (hsb: SlashableBound S rho)
    {H: Height} {w₁: V} {read₁: Time} {P₁ P: Block V}
    (h₁: FixedHeightRootInterferenceAtRead S rho H w₁ read₁ P₁)
    (hrebase: Block.Preceq (rho.storeBeforeTime S w₁ read₁).J P)
    {r: Round} (hforms: GradeFormsAt S rho r P)
    (hPheight: H ≤ (derived_state S.E S.cfg P).h)
    {v: V} (hv: v ∈ rho.honest)
    {w: V} (hw: w ∈ rho.honest)
    {read: Time} (hread: read ≤ rho.horizon)
    (hTmem: actionSGBlockAt S rho v r ∈
      (rho.storeBeforeTime S w read).T)
    (hfrontier: (rho.storeBeforeTime S w read).h_max = H):
    Block.compatible
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w read).toHealing.toFG)
      (actionSGBlockAt S rho v r) = true:= by
  have hPT: Block.Preceq P (actionSGBlockAt S rho v r):=
    preceq_actionSGBlockAt_of_gradeFormsAt S hforms hv
  have hTrun: RunBlock S rho (actionSGBlockAt S rho v r):= by
    obtain ⟨i, hi, -⟩:= Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toScheduleWellFormed (S.a r)
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv
    rw [← hi]
    exact actionSGBlockAt_mem_storeBeforeTime_of_gradeFormsAt S adm hforms hv
  exact getFGRoot_compatible_of_fixedFrontier_certifiedPrefix
    S adm hfb hsb hw hread hTmem hTrun
      (hPheight.trans (Protocol.derived_h_mono S.E S.cfg hPT))
      hfrontier h₁.fixedTarget.targetBlock h₁.fixedTarget.certificate
      (Block.preceq_trans hrebase hPT)

/-- A rebased common grade transfers a certified fixed frontier to quietness
of the exact SG action target at every caller-selected actual read. -/
theorem finalityFilterQuietOn_actionSGBlockAt_of_rebasedGrade_fixedFrontier
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    (hsb: SlashableBound S rho)
    {H: Height} {w₁: V} {read₁: Time} {P₁ P: Block V}
    (h₁: FixedHeightRootInterferenceAtRead S rho H w₁ read₁ P₁)
    (hrebase: Block.Preceq (rho.storeBeforeTime S w₁ read₁).J P)
    {r: Round} (hforms: GradeFormsAt S rho r P)
    (hPheight: H ≤ (derived_state S.E S.cfg P).h)
    {v: V} (hv: v ∈ rho.honest)
    {IsRead: V → Time → Prop}
    (hreadLe: ∀ w, w ∈ rho.honest → ∀ read, IsRead w read →
      read ≤ rho.horizon)
    (hTmem: ∀ w, w ∈ rho.honest → ∀ read, IsRead w read →
      actionSGBlockAt S rho v r ∈ (rho.storeBeforeTime S w read).T)
    (hfrontier: ∀ w, w ∈ rho.honest → ∀ read, IsRead w read →
      (rho.storeBeforeTime S w read).h_max = H):
    FinalityFilterQuietOn S rho (actionSGBlockAt S rho v r) IsRead:= by
  have hPT: Block.Preceq P (actionSGBlockAt S rho v r):=
    preceq_actionSGBlockAt_of_gradeFormsAt S hforms hv
  have hTrun: RunBlock S rho (actionSGBlockAt S rho v r):= by
    obtain ⟨i, hi, -⟩:= Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toScheduleWellFormed (S.a r)
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv
    rw [← hi]
    exact actionSGBlockAt_mem_storeBeforeTime_of_gradeFormsAt S adm hforms hv
  exact finalityFilterQuietOn_of_fixedFrontier_certifiedPrefix
    S adm hfb hsb h₁.fixedTarget.targetBlock h₁.fixedTarget.certificate
      (Block.preceq_trans hrebase hPT) hTrun
      (hPheight.trans (Protocol.derived_h_mono S.E S.cfg hPT))
      hreadLe hTmem hfrontier

/-- A fresh anchor selected at an interior vote duty has grade one at the
reader's action-time grade view for that round. -/
theorem interiorVoteFreshAnchor_G1_at_action
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {r: Round} {s: Slot}
    (hslo: S.hc.opening_slot r + 1 ≤ s)
    (hshi: s < S.hc.opening_slot (r + 1))
    {w: V} (hw: w ∈ rho.honest) {A: Block V}
    (hA: Protocol.fresh_anchor S.E S.hc
      (Proofs.Optimistic.voteDutyStore S rho w s).toHealing r = some A):
    Protocol.G1 S.E (gradeViewAt S rho w r) S.hc r A = true:= by
  let duty:= Proofs.Optimistic.voteDutyStore S rho w s
  let read:= Protocol.vote_time S.E s
  have hAcandidate: A ∈
      (Protocol.get_filtered_block_tree duty.toHealing.toFG).filter
        (fun C => Protocol.G1 S.E duty.toHealing.gradeView S.hc r C = true):= by
    simpa only [duty, Protocol.fresh_anchor] using Proofs.Engine.deepest?_mem hA
  have hAG1Duty: Protocol.G1 S.E duty.toHealing.gradeView S.hc r A = true:=
    (Finset.mem_filter.mp hAcandidate).2
  have hAG1Read: Protocol.G1 S.E
      (rho.storeBeforeTime S w read).toHealing.gradeView S.hc r A = true:= by
    simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, read] using hAG1Duty
  have hround: S.hc.round_of s = r:=
    round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc hslo hshi
  have hcut: S.hc.Γ_0 S.E.Δ r ≤ read:= by
    simpa only [read] using Γ_0_le_vote_time_of_round_eq S hround
  rcases le_total read (S.a r) with hbefore | hafter
  · have hAG1Action:= G1_persists_after_cutoff S adm hw hcut hbefore hAG1Read
    simpa only [gradeViewAt, healStoreAt] using hAG1Action
  · exact G1_reflects_to_opening S adm hw hafter hAG1Read

/-- An interior fresh anchor is compatible with an honest action target when a
rebased common grade keeps the action frontier fixed. -/
theorem interiorVoteFreshAnchor_compatible_actionSGBlockAt_of_rebasedGrade_fixedFrontier
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    (hsb: SlashableBound S rho)
    {r: Round} (ready: GradeRoundReady S rho r)
    {H: Height} {w₁: V} {read₁: Time} {P₁ P: Block V}
    (h₁: FixedHeightRootInterferenceAtRead S rho H w₁ read₁ P₁)
    (hrebase: Block.Preceq (rho.storeBeforeTime S w₁ read₁).J P)
    (hforms: GradeFormsAt S rho r P)
    (hPheight: H ≤ (derived_state S.E S.cfg P).h)
    {u: V} (hu: u ∈ rho.honest)
    {s: Slot} (hslo: S.hc.opening_slot r + 1 ≤ s)
    (hshi: s < S.hc.opening_slot (r + 1))
    {w: V} (hw: w ∈ rho.honest) {A: Block V}
    (hA: Protocol.fresh_anchor S.E S.hc
      (Proofs.Optimistic.voteDutyStore S rho w s).toHealing r = some A)
    (haction: S.a r ≤ rho.horizon)
    (hfrontier: (rho.storeBeforeTime S u (S.a r)).h_max = H):
    Block.compatible A (actionSGBlockAt S rho u r) = true:= by
  have hAG1: Protocol.G1 S.E (gradeViewAt S rho w r) S.hc r A = true:=
    interiorVoteFreshAnchor_G1_at_action S adm hslo hshi hw hA
  have hAPorPA: Block.Preceq A P ∨ Block.Preceq P A:= by
    simpa only [Block.compatible, Bool.or_eq_true] using
      G1_G2_compatible S.E hAG1 (hforms w hw).2
  have hPT: Block.Preceq P (actionSGBlockAt S rho u r):=
    preceq_actionSGBlockAt_of_gradeFormsAt S hforms hu
  rcases hAPorPA with hAP | hPA
  · exact Block.compatible_of_preceq_common
      (Block.preceq_trans hAP hPT) (Block.preceq_self _)
  · obtain ⟨hAraw, hAstamp⟩:= G1_rawMem_and_stamp_at_action
      S adm hfb ready hforms hw hAG1 hPA hu
    have hArun: RunBlock S rho A:= by
      obtain ⟨i, hi, -⟩:= Proofs.Bridges.stateBeforeTime_eq_stateBefore S
        adm.toScheduleWellFormed (S.a r)
      apply Proofs.Bridges.runBlock_of_stateBefore_mem S hu
      rw [← hi]
      exact hAraw
    have hAheight: H ≤ (derived_state S.E S.cfg A).h:=
      hPheight.trans (Protocol.derived_h_mono S.E S.cfg hPA)
    have hAnoninterference:
        FinalityFilterNoninterferenceAtRead S rho u (S.a r) A:=
      finalityFilterNoninterferenceAtRead_of_fixedFrontier_certifiedPrefix
        S adm hfb hsb hu haction hAraw hArun hAheight hfrontier
          h₁.fixedTarget.targetBlock h₁.fixedTarget.certificate
          (Block.preceq_trans hrebase hPA)
    have hTmem: actionSGBlockAt S rho u r ∈
        (rho.storeBeforeTime S u (S.a r)).T:=
      actionSGBlockAt_mem_storeBeforeTime_of_gradeFormsAt S adm hforms hu
    have hTroot: Block.compatible
        (Protocol.get_fg_root
          (rho.storeBeforeTime S u (S.a r)).toHealing.toFG)
        (actionSGBlockAt S rho u r) = true:=
      getFGRoot_compatible_actionSGBlockAt_of_rebasedGrade_fixedFrontier
        S adm hfb hsb h₁ hrebase hforms hPheight hu hu haction hTmem
          hfrontier
    rcases hAnoninterference with hARoot | hAfiltered
    · simp only [Block.compatible, Bool.or_eq_true] at hTroot
      rcases hTroot with hRootT | hTRoot
      · exact Block.compatible_of_preceq_common
          (Block.preceq_trans hARoot hRootT) (Block.preceq_self _)
      · rcases Block.preceq_linear hARoot hTRoot with hAT | hTA
        · exact Block.compatible_of_preceq_common hAT (Block.preceq_self _)
        · exact Block.compatible_of_preceq_common (Block.preceq_self _) hTA
    · have hAactive: A ∈ (gradeViewAt S rho u r).tree:= by
        simpa only [gradeViewAt, healStoreAt, Protocol.HealingStore.gradeView,
          Protocol.Store.toHealing] using hAfiltered
      have hAfilteredAction: A ∈ Protocol.get_filtered_block_tree
          (actionStoreAt S rho u r).toHealing.toFG:= by
        rw [actionStoreAt_filteredTree S rho u r]
        simpa only [healStoreAt, Protocol.Store.toHealing] using hAfiltered
      have hAstampAction: stampedBefore
          (actionStoreAt S rho u r).toHealing.gradeView.timestamp_block
          (S.hc.Γ_1 S.E.Δ r) A = true:= by
        change stampedBefore (actionStoreAt S rho u r).timestamp_block
          (S.hc.Γ_1 S.E.Δ r) A = true
        rw [Protocol.actionStoreAt_timestamp_block S rho u r]
        exact hAstamp
      have hAG0: Protocol.G0 S.E (gradeViewAt S rho u r) S.hc r A = true:=
        G1_imp_G0_delivered S.E
          (GradeDeliveryRun.honestGradeDelivery_of_admissible
            S adm ready w hw u hu) hAactive hAG1
      have hAG0Action: Protocol.G0 S.E
          (actionStoreAt S rho u r).toHealing.gradeView S.hc r A = true:= by
        rw [Protocol.actionStoreAt_gradeView_eq_storeBeforeTime S rho u r]
        simpa only [gradeViewAt, healStoreAt] using hAG0
      have hQsome: (Protocol.grade2_block S.E S.hc
          (actionStoreAt S rho u r).toHealing r).isSome = true:= by
        refine deepest?_isSome_of_compatible ?_ ⟨P, ?_⟩
        · intro X hX Y hY
          exact G2_compatible S.E (Finset.mem_filter.mp hX).2
            (Finset.mem_filter.mp hY).2
        · exact Finset.mem_filter.mpr
            (gradeFormsAt_actionStore S hforms hu)
      obtain ⟨Q, hQ⟩:= Option.isSome_iff_exists.mp hQsome
      simpa only [actionSGBlockAt] using
        recoveryActionCarrier_compatible_of_g0 S.E hQ hAfilteredAction
          hAstampAction hAG0Action

/-- The five sound geometric outcomes for a selected G2 block `Q`, its action
target `T`, and one actual read store.

The root-equality disjunct in `rootBelowSelected` is necessary because
`get_fg_root` need not itself survive the height/viability filter. Away from
equality, this branch records the exact filtered-tree activity needed by the
next cone step. -/
inductive SGTargetReadDisposition (st: Protocol.Store V)
    (Q T: Block V): Prop where
  /-- The current finality root already extends the action target. -/
  | targetBelowRoot
      (hTR: Block.Preceq T
        (Protocol.get_fg_root st.toHealing.toFG)):
      SGTargetReadDisposition st Q T
  /-- The finality root is at or below the selected block. Strictly below
  requires `Q` to remain in the actual filtered tree; equality needs no such
  claim. -/
  | rootBelowSelected
      (hRQ: Block.Preceq
        (Protocol.get_fg_root st.toHealing.toFG) Q)
      (hQ: Protocol.get_fg_root st.toHealing.toFG = Q ∨
        Q ∈ Protocol.get_filtered_block_tree st.toHealing.toFG):
      SGTargetReadDisposition st Q T
  /-- The finality root advanced strictly inside the selected-to-target
  interval. -/
  | interiorRootAdvance
      (hQR: Block.Prec Q
        (Protocol.get_fg_root st.toHealing.toFG))
      (hRT: Block.Prec
        (Protocol.get_fg_root st.toHealing.toFG) T):
      SGTargetReadDisposition st Q T
  /-- The actual selected finality root conflicts with the action target. -/
  | fgRootInterference
      (hint: FGRootInterferenceAt st T):
      SGTargetReadDisposition st Q T
  /-- The height/viability filter removes the selected block below the actual
  finality root. -/
  | heightFilterInterference
      (hint: HeightFilterInterferenceAt st Q):
      SGTargetReadDisposition st Q T

/-- Every actual run read has the complete target-local disposition. This is
a purely geometric leaf: it uses only `Q ⪯ T` and the filter result at this
read, with no run-history or quiet-window premise. -/
theorem sgTargetReadDispositionAtRead
    (S: Setup V) (rho: Run V) (w: V) (read: Time)
    {Q T: Block V} (hQT: Block.Preceq Q T):
    SGTargetReadDisposition (rho.storeBeforeTime S w read) Q T:= by
  let st: Protocol.Store V:= rho.storeBeforeTime S w read
  let R: Block V:= Protocol.get_fg_root st.toHealing.toFG
  change SGTargetReadDisposition st Q T
  by_cases hquiet:
      FinalityFilterNoninterferenceAtRead S rho w read Q
  · change Block.Preceq Q R ∨
      Q ∈ Protocol.get_filtered_block_tree st.toHealing.toFG at hquiet
    by_cases hTR: Block.Preceq T R
    · exact.targetBelowRoot hTR
    · rcases hquiet with hQR | hQfiltered
      · by_cases hRT: Block.Preceq R T
        · by_cases hRQ: Block.Preceq R Q
          · exact.rootBelowSelected hRQ
              (Or.inl (Block.preceq_antisymm hRQ hQR))
          · have hQRne: Q ≠ R:= by
              intro hEq
              apply hRQ
              rw [← hEq]
              exact Block.preceq_self Q
            have hRTne: R ≠ T:= by
              intro hEq
              apply hTR
              rw [← hEq]
              exact Block.preceq_self R
            have hQRstrict: Block.Prec Q R:= by
              change Block.prec Q R = true
              simp only [Block.prec, Bool.and_eq_true, Bool.not_eq_true',
                decide_eq_false_iff_not]
              exact ⟨hQRne, hQR⟩
            have hRTstrict: Block.Prec R T:= by
              change Block.prec R T = true
              simp only [Block.prec, Bool.and_eq_true, Bool.not_eq_true',
                decide_eq_false_iff_not]
              exact ⟨hRTne, hRT⟩
            exact.interiorRootAdvance hQRstrict hRTstrict
        · exact.fgRootInterference (by
            change Block.compatible R T = false
            simp only [Block.compatible, Bool.or_eq_false_iff]
            exact ⟨Bool.eq_false_of_not_eq_true hRT,
              Bool.eq_false_of_not_eq_true hTR⟩)
      · have hRQ: Block.Preceq R Q:=
          Proofs.Records.preceq_get_fg_root_of_mem_filtered hQfiltered
        exact.rootBelowSelected hRQ (Or.inr hQfiltered)
  · rcases (not_finalityFilterNoninterferenceAtRead_iff
        S rho w read Q).mp hquiet with hrootQ | hheightQ
    · change Block.compatible R Q = false at hrootQ
      refine.fgRootInterference ?_
      change Block.compatible R T = false
      apply Bool.eq_false_of_not_eq_true
      intro hrootT
      have hrootQTrue: Block.compatible R Q = true:= by
        simp only [Block.compatible, Bool.or_eq_true] at hrootT ⊢
        rcases hrootT with hRT | hTR
        · exact Block.preceq_linear hRT hQT
        · exact Or.inr (Block.preceq_trans hQT hTR)
      rw [hrootQTrue] at hrootQ
      simp at hrootQ
    · refine.heightFilterInterference ?_
      simpa only [st] using hheightQ

-/











/-- The prepared action selector has only its clear and active-G2 branches.
The branch split uses the same frame contract as `actionSGBlockAt`. -/
theorem actionSGBlockAt_clear_or_selectedG2
    (S : Setup V) (rho : Run V) {r : Round} {u : V} {Q : Block V}
    (hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho u r) r = some Q) :
    (∃ T : Block V,
      Protocol.deepest_clear
        (some (PhaseGrades.nodeAnchor S (actionReadAt S rho u r) r))
        (actionReadAt S rho u r).st.core.toHealing.live_confirmed
        (PhaseGrades.nodeClear S (actionReadAt S rho u r) r) = some T ∧
      actionSGBlockAt S rho u r = T) ∨
    actionSGBlockAt S rho u r = Q := by
  set n := actionReadAt S rho u r with hn
  set st := n.st.core.toHealing with hst
  set grades := DecoupledConsensusModel.Protocol.frameGradeRead n.cache S.E S.hc st r with hgrades
  have hk : S.hc.round_of st.s = r :=
    Proofs.HealingLemmas.round_of_slotOf_a S r
  have hQ2 : grades.Q2 = some Q := hQ
  have heq : actionSGBlockAt S rho u r = Protocol.currentSGVote st grades := by
    show Protocol.get_sg_vote_with (NamedProfile.gradeContract n.cache) S.E S.hc st
        (S.hc.round_of st.s)
        (Protocol.grade2_block_with (NamedProfile.gradeContract n.cache) S.E S.hc st
          (S.hc.round_of st.s)) = Protocol.currentSGVote st grades
    rw [hk]
    rfl
  cases hclear : Protocol.deepest_clear (some grades.anchor) st.live_confirmed
      grades.clear with
  | some T =>
      left
      refine ⟨T, ?_, ?_⟩
      · simpa only [PhaseGrades.nodeAnchor, PhaseGrades.nodeRead, n, st,
          grades, hgrades] using hclear
      · rw [heq]
        unfold Protocol.currentSGVote
        rw [hclear]
  | none =>
      right
      rw [heq]
      unfold Protocol.currentSGVote
      rw [hclear, hQ2]



/-
/-- With an actual selected G2, `get_sg_vote` has only the clear and selected-G2
branches. In particular, its raw-anchor fallback is unavailable. -/
theorem actionSGBlockAt_clear_or_selectedG2
    (S: Setup V) (rho: Run V) {r: Round} {u: V} {Q: Block V}
    (hQ: Protocol.grade2_block S.E S.hc
      (actionStoreAt S rho u r).toHealing r = some Q):
    (∃ T: Block V,
      Protocol.deepest_clear
        (some (Protocol.get_sg_root S.E S.hc (actionStoreAt S rho u r).toHealing r))
        (actionStoreAt S rho u r).live_confirmed
        (fun B => Protocol.g0_clear S.E
          (actionStoreAt S rho u r).toHealing.gradeView S.hc r B) = some T ∧
      actionSGBlockAt S rho u r = T) ∨
    actionSGBlockAt S rho u r = Q:= by
  cases hclear: Protocol.deepest_clear
      (some (Protocol.get_sg_root S.E S.hc (actionStoreAt S rho u r).toHealing r))
      (actionStoreAt S rho u r).live_confirmed
      (fun B => Protocol.g0_clear S.E
        (actionStoreAt S rho u r).toHealing.gradeView S.hc r B) with
  | some T =>
      left
      refine ⟨T, rfl, ?_⟩
      have hclear': Protocol.deepest_clear
          (some (Protocol.get_sg_root S.E S.hc
            (actionStoreAt S rho u r).toHealing r))
          (actionStoreAt S rho u r).toHealing.live_confirmed
          (fun B => Protocol.g0_clear S.E
            (actionStoreAt S rho u r).toHealing.gradeView S.hc r B) = some T:= by
        simpa only [Protocol.Store.toHealing] using hclear
      unfold actionSGBlockAt
      rw [Protocol.get_sg_vote.eq_def, hclear']
  | none =>
      right
      have hclear': Protocol.deepest_clear
          (some (Protocol.get_sg_root S.E S.hc
            (actionStoreAt S rho u r).toHealing r))
          (actionStoreAt S rho u r).toHealing.live_confirmed
          (fun B => Protocol.g0_clear S.E
            (actionStoreAt S rho u r).toHealing.gradeView S.hc r B) = none:= by
        simpa only [Protocol.Store.toHealing] using hclear
      unfold actionSGBlockAt
      rw [Protocol.get_sg_vote.eq_def, hclear', hQ]

-/

/-- A genuine confirmation's strict score remains a strict score for every
ancestor on its selected chain. This is the target-local source gate needed
when the action selector returns a clear `T ⪯ C`, rather than `C` itself. -/
theorem ancestorConfirmation_eligible_of_preceq
    (E : Env V) (hc : Protocol.HealConfig) (source : Protocol.Store V)
    (s : Slot) {T C : Block V} {contract : Protocol.GradeContract V}
    (hTC : Block.Preceq T C)
    (hC : GenuineConfirmationWith contract E hc source s C) :
    Protocol.voters_count E (confLate E source s) s <
      2 * Protocol.goldfish_score E source.T
        (confVotes E source s) (confVotes E source s) s T := by
  have hN := confNumerator E source s
  have hsupport := supporters_mono E source.T
    (confVotes E source s) (confVotes E source s) s hTC
  have hcard := Finset.card_le_card hsupport
  have hCg : GenuineConfirmation (contract := contract) E hc source s C :=
    ⟨hC.selected, hC.genuine⟩
  have hCeligible := hCg.eligible
  rw [hN.score_eq_supporters] at hCeligible ⊢
  exact lt_of_lt_of_le hCeligible (Nat.mul_le_mul_left 2 hcard)




/-
/-- A genuine confirmation of `C` seeds the next vote cone for any protected
ancestor `T ⪯ C` once that target's exact local adoption facts are available.
Unlike the ordinary producer, this theorem does not claim that the confirmation
selected `T`; it transports only the monotone strict source score. -/
theorem honestVotesCone_succ_of_ancestorGenuineConfirmation
    (S: Setup V) (rho: Run V) (source: Protocol.Store V)
    (s: Slot) (T: Block V)
    (heligible: Protocol.voters_count S.E (confLate S.E source s) s <
      2 * Protocol.goldfish_score S.E source.T
        (confVotes S.E source s) (confVotes S.E source s) s T)
    (hduty: ∀ w ∈ rho.honest, w ∈ S.E.committee (s + 1) →
      NextVoteAdoption S rho source s T w):
    NamedHonestVotesCone S rho (s + 1)
      (fun X => Block.Preceq T X):= by
  intro w hw hwcommittee
  let st:= Proofs.Optimistic.voteDutyStore S rho w (s + 1)
  have hslot: st.s = s + 1:= Proofs.Optimistic.voteDutyStore_slot S rho w (s + 1)
  have hidx: s + 1 - 1 = s:= by simp
  have hprev: st.s - 1 = s:= by
    rw [hslot]
    exact hidx
  have hcommittee: (S.node w).val_index ∈ S.E.committee st.s:= by
    rw [S.node_val_index, hslot]
    exact hwcommittee
  have hd:= hduty w hw hwcommittee
  let votes:= Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  let support:= Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
  let X:= Protocol.get_head_in_tree S.E S.hc st
    (Protocol.voter_filtered_block_tree S.E st st.s) votes support (st.s - 1)
  have hX: Block.Preceq T X:= by
    change Block.Preceq T
      (Protocol.get_head_in_tree_hc S.E S.hc st.toHealing
        (Protocol.voter_filtered_block_tree S.E st st.s) votes support (st.s - 1))
    have hpath:= hd.path
    rw [← Proofs.Optimistic.voter_candidate_tree_eq_protocol_voter_filtered_block_tree] at hpath ⊢
    rw [hprev]
    exact Protocol.get_head_in_tree_captures_of_confirmation S.E S.hc
      st.toHealing source.T
      (Proofs.Optimistic.voter_candidate_tree S.E st.toHealing)
      (confEarly S.E source s) (confLate S.E source s)
      (confVotes S.E source s) votes support s
      (confNumerator S.E source s) hd.transport heligible
      hd.support_subset hd.anchor hpath
  refine ⟨X, hX, ?_, ?_⟩
  · simpa only [X, st, votes, support] using hd.run
  have hout:
      (Protocol.goldfish_vote S.E S.hc (S.node w) st).2 =
        some ⟨(S.node w).val_index, st.s, X.root⟩:= by
    simp only [Protocol.goldfish_vote, hcommittee, if_true, X, votes, support]
  have hemit:= hd.emit _ hout
  rw [S.node_val_index, hslot] at hemit
  exact hemit

/-- The frozen processed domain of a vote duty is ancestor closed. A block
that the voter processed makes every one of its ancestors processed at the
same duty, through the receipt/current-proposal split. -/
theorem ancestorProcessed_of_voterProcessed
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {w: V} (hw: w ∈ rho.honest) {s: Slot} {B: Block V}
    (hBmem: B ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s):
    ∀ C: Block V, Block.Preceq C B →
      C ∈ Protocol.voter_processed_block_tree S.E
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s:= by
  let duty:= Proofs.Optimistic.voteDutyStore S rho w (s + 1)
  have hBprocessed: B ∈ Protocol.voter_processed_block_tree S.E
      duty.toHealing.toFG.toSG.toGoldfishStore duty.toHealing.s:= hBmem
  have hslot: duty.toHealing.s = s + 1:= by
    simpa only [duty, Proofs.Optimistic.toHealing_slot] using
      Proofs.Optimistic.voteDutyStore_slot S rho w (s + 1)
  obtain ⟨n, hn, -⟩:= Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toScheduleWellFormed (Protocol.vote_time S.E (s + 1))
  have hpc: ParentClosed (rho.stateBefore S n w).st:=
    Proofs.Bridges.parentClosed_of_admissible S adm.toDeliveryWellFormed w n
  intro C hCB
  simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    at hBprocessed ⊢
  rw [hslot, Nat.add_sub_cancel] at hBprocessed ⊢
  rcases hBprocessed with ⟨hBT, hstamp | ⟨P, hP, hBP⟩⟩
  · have hBTn: B ∈ (rho.stateBefore S n w).st.T:= by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn,
        Protocol.Store.toHealing] using hBT
    have hstampn: stampedBefore
        (rho.stateBefore S n w).st.timestamp_block
        (Protocol.view_freeze S.E s) B = true:= by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn,
        Protocol.Store.toHealing] using hstamp
    have hprocessed: (Object.block B).processed
        (rho.stateBefore S n w).st = true:= by
      simpa only [Object.processed, decide_eq_true_eq] using hBTn
    obtain hgen | ⟨i, hin, t, hacc⟩:=
      acceptsAt_block_of_processed S rho w n B hprocessed
    · have hCgen: C = Block.genesis:=
        Block.preceq_antisymm (hgen ▸ hCB) (Protocol.preceq_genesis C)
      subst C
      have hgenesis:= genesis_mem_and_stamp_storeBeforeTime
        S adm.toScheduleWellFormed w
        (Protocol.vote_time S.E (s + 1))
        (Protocol.view_freeze S.E s)
      exact ⟨by
        simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hgenesis.1,
        Or.inl (by
          simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
            Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using
            hgenesis.2)⟩
    · have htFreeze: t < Protocol.view_freeze S.E s:=
        HonestWeightMajority.acceptsAt_block_lt_of_stamp_before
          S adm hw hacc (Nat.succ_le_of_lt hin)
            (publicTime_view_freeze S s) hstampn
      have hvisibleC:= admittedBefore_ancestor_mem_and_stamp_at
        S adm (show AdmittedBefore S rho w B
          (Protocol.view_freeze S.E s) from ⟨i, t, hacc, htFreeze⟩)
        hCB (le_of_lt (view_freeze_lt_vote_time_succ S.E s))
      exact ⟨by
        simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hvisibleC.1,
        Or.inl (by
          simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
            Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using
            hvisibleC.2)⟩
  · have hPT: P ∈ duty.T:= by
      simpa only [Protocol.Store.toHealing] using hP.1
    have hPTn: P ∈ (rho.stateBefore S n w).st.T:= by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn] using hPT
    have hCP: Block.Preceq C P:= Block.preceq_trans hCB hBP
    have hCTn: C ∈ (rho.stateBefore S n w).st.T:=
      Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
        C P hPTn hCP
    exact ⟨by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime, hn,
        Protocol.Store.toHealing] using hCTn,
      Or.inr ⟨P, hP, hCP⟩⟩
-/



private theorem finalized_preceq_at_delivery_of_laterVoteDutyRoot
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {k : Slot} {v : V} {B : Block V} {X : NamedBlock V}
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho v
          (k + 1)).st.core.toHealing.toFG) B)
    {i : Nat} {t : Time}
    (hi : rho.events[i]? = some (Event.deliver v (Object.block X) t))
    (hlt : t < Protocol.view_freeze S.E k) :
    Block.Preceq (rho.stateBefore S i v).st.F B := by
  let Gamma := Protocol.vote_time S.E (k + 1)
  let n := (rho.events.filter (fun e => decide (e.time < Gamma))).length
  have hiN : i < n := by
    by_contra hnot
    have hni : n ≤ i := Nat.le_of_not_gt hnot
    have hGamma : Gamma ≤ t :=
      Proofs.Optimistic.le_time_of_index_ge S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
        (t := Gamma) (j := i) (e := Event.deliver v (Object.block X) t)
        (by simpa only [n] using hni) hi
    exact (not_le_of_gt
      (lt_trans hlt (view_freeze_lt_vote_time_succ S.E k))) hGamma
  let pre := rho.storeBeforeTime S v Gamma
  have hmono : Block.Preceq (rho.stateBefore S i v).st.F pre.F := by
    have hprefix := stateBefore_F_mono S rho v (Nat.le_of_lt hiN)
    have hstore : pre = (rho.stateBefore S n v).st :=
      congrArg NamedNodeState.st
        (congrFun (Proofs.Optimistic.stateBeforeTime_eq_take S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed Gamma) v)
    simpa only [hstore] using hprefix
  have hFJ : Block.Preceq pre.F pre.J :=
    Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
      S rho Gamma v
  have hFroot : Block.Preceq pre.F
      (Protocol.get_fg_root pre.toHealing.toFG) :=
    Proofs.Records.preceq_get_fg_root_of_F (st := pre.toHealing.toFG) hFJ
  have hroot' : Block.Preceq
      (Protocol.get_fg_root pre.toHealing.toFG) B := by
    simpa only [Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore,
      pre, Gamma] using hroot
  exact Block.preceq_trans hmono (Block.preceq_trans hFroot hroot')

/-- A genuine source confirmation persists into any later vote duty once the
source support has one delivery interval before that duty's frozen view. The
proof is the post-GST delivery/store-monotonicity route, not a frozen-tree
assumption. -/
theorem voterProcessedTarget_of_genuineConfirmation_at_laterVoteDuty_after_gst
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {source k : Slot}
    (hsourceNextLe : source + 1 ≤ k)
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E source)
    (hhor : Protocol.vote_time S.E (k + 1) ≤ rho.horizon)
    {B : Block V} {contract : Protocol.GradeContract V}
    (hgenuine : GenuineConfirmation (contract := contract) S.E S.hc
      (Proofs.Optimistic.confStore S rho v source) source B)
    (hroot : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (k + 1)).toHealing.toFG) B) :
    B ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho w (k + 1)).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho w (k + 1)).toHealing.s := by
  have hN := confNumerator S.E (Proofs.Optimistic.confStore S rho v source) source
  have hpositive : 0 <
      (Protocol.goldfishSupporters S.E (Proofs.Optimistic.confStore S rho v source).T
        (confVotes S.E (Proofs.Optimistic.confStore S rho v source) source)
        (confVotes S.E (Proofs.Optimistic.confStore S rho v source) source) source B).card := by
    have heligible := hgenuine.eligible
    rw [hN.score_eq_supporters] at heligible
    by_contra hnot
    have hzero :
        (Protocol.goldfishSupporters S.E (Proofs.Optimistic.confStore S rho v source).T
          (confVotes S.E (Proofs.Optimistic.confStore S rho v source) source)
          (confVotes S.E (Proofs.Optimistic.confStore S rho v source) source) source B).card = 0 :=
      Nat.eq_zero_of_not_pos hnot
    rw [hzero] at heligible
    simp at heligible
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpositive
  rw [mem_supporters_iff] at hu
  obtain ⟨-, u, huBy, -, htargets⟩ := hu
  rw [Protocol.votes_by, Finset.mem_filter] at huBy
  obtain ⟨H, hfind, hBH⟩ := targets_under_iff.mp htargets
  let duty := Proofs.Optimistic.voteDutyStore S rho w (k + 1)
  have hslot : duty.toHealing.s = k + 1 := by
    simpa only [duty, Proofs.Optimistic.toHealing_slot] using
      Proofs.Optimistic.voteDutyStore_slot S rho w (k + 1)
  by_cases hgen : H = Block.genesis
  · subst H
    have hBgen : B = Block.genesis :=
      Block.preceq_antisymm hBH.2 (Protocol.preceq_genesis B)
    subst B
    have hgenesis := genesis_mem_and_stamp_storeBeforeTime
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed w
        (Protocol.vote_time S.E (k + 1))
        (Protocol.view_freeze S.E k)
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    rw [hslot, Nat.add_sub_cancel]
    exact ⟨by
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hgenesis.1,
      Or.inl (by
        simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hgenesis.2)⟩
  · have hHsource : H ∈ (Proofs.Optimistic.confStore S rho v source).T :=
      Proofs.HealingLemmas.find?_mem hfind
    have hearly : u ∈ confEarly S.E (Proofs.Optimistic.confStore S rho v source) source :=
      (Finset.mem_filter.mp huBy.1).1
    have hresolved : stampedBefore
        (Proofs.Optimistic.confStore S rho v source).tau
        (Protocol.support_cutoff S.E source) u = true := by
      rw [confEarly, beforeCutoff, Finset.mem_filter] at hearly
      exact hearly.2
    have hHstamp : stampedBefore
        (Proofs.Optimistic.confStore S rho v source).timestamp_block
        (Protocol.support_cutoff S.E source) H = true :=
      HonestWeightMajority.stampedBefore_block_of_resolution hfind hresolved
    obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
        (Protocol.confirmation_time S.E source)
    have hHn : H ∈ (rho.stateBefore S n v).st.core.T := by
      simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
        Run.storeBeforeTime, hn] using hHsource
    have hstampn : stampedBefore
        (rho.stateBefore S n v).st.core.timestamp_block
        (Protocol.support_cutoff S.E source) H = true := by
      simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore,
        Run.storeBeforeTime, hn] using hHstamp
    obtain hgen' | ⟨D, hDerase, i, hin, t, hacc⟩ :=
      acceptsAt_block_of_processed_erased S rho v n hHn
    · exact False.elim (hgen hgen')
    · have htSupport : t < Protocol.support_cutoff S.E source :=
        Protocol.HonestWeightMajority.acceptsAt_block_lt_of_stamp_before
          S adm hv hacc (Nat.succ_le_of_lt hin)
            (publicTime_support_cutoff S source) (by
              simpa only [hDerase] using hstampn)
      have hDposErase : 0 < D.erase.slot :=
        Nat.zero_lt_of_lt (parent_slot_lt_of_acceptsAt_block S hacc)
      have hDpos : 0 < D.slot := by
        cases D <;> simpa using hDposErase
      have hfreezeHor : Protocol.view_freeze S.E k ≤ rho.horizon :=
        (le_of_lt (view_freeze_lt_vote_time_succ S.E k)).trans hhor
      have hpostCut : S.E.t_GST ≤ Protocol.support_cutoff S.E source := by
        apply le_trans hpost
        unfold Protocol.proposal_time Protocol.support_cutoff
        exact le_add_of_nonneg_right
          (Int.mul_nonneg (by norm_num) (le_of_lt S.E.Δ_pos))
      have hsourceLeK : source ≤ k :=
        le_trans (Nat.le_succ source) hsourceNextLe
      have hcutMono : Protocol.support_cutoff S.E source ≤
          Protocol.support_cutoff S.E k :=
        Proofs.Optimistic.support_cutoff_mono S.E hsourceLeK
      have htSupportK : t < Protocol.support_cutoff S.E k :=
        lt_of_lt_of_le htSupport hcutMono
      have hpostCutK : S.E.t_GST ≤ Protocol.support_cutoff S.E k :=
        hpostCut.trans hcutMono
      have hadmit : AdmittedBefore S rho w H
          (Protocol.view_freeze S.E k) := by
        simpa only [hDerase] using
          (Protocol.block_admittedBefore_of_accepted_after_cutoff
            S adm hv hw hDpos hacc
              htSupportK hpostCutK
            (support_cutoff_add_delta_eq_view_freeze S.E k) hfreezeHor
            (by
              intro j hj
              have hjVote := hj.trans (strict_filter_length_mono rho
                (le_of_lt (view_freeze_lt_vote_time_succ S.E k)))
              have hroot' : Block.Preceq
                  (Protocol.get_fg_root
                    (rho.storeBeforeTime S w
                      (Protocol.vote_time S.E (k + 1))).toHealing.toFG) B := by
                simpa only [Internal.NamedRecoveryRead.voteDutyRead,
                  NamedActionReads.confirmationReadAt,
                  NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
                  Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
                  Proofs.Optimistic.tickStore] using
                    (show Block.Preceq
                      (Protocol.get_fg_root
                        (Internal.NamedRecoveryRead.voteDutyRead S rho w
                          (k + 1)).st.core.toHealing.toFG) B by
                      simpa only [duty] using hroot)
              exact Block.preceq_trans
                (finalized_preceq_at_prefix_of_storeBeforeRoot_preceq
                  S rho adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted
                  hroot' hjVote)
                (by simpa only [hDerase] using hBH.2)))
      have hvisibleB := Proofs.Optimistic.admittedBefore_ancestor_mem_and_stamp_at S
        adm hadmit hBH.2
          (le_of_lt (view_freeze_lt_vote_time_succ S.E k))
      simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
      rw [hslot, Nat.add_sub_cancel]
      exact ⟨by
        simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hvisibleB.1,
        Or.inl (by
          simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
            Proofs.Optimistic.tickStore, Protocol.Store.toHealing] using hvisibleB.2)⟩



/-! ## Named fixed-frontier root lock -/

omit [Fintype V] in
private theorem rootLock_named_preceq_trans {A B C : NamedBlock V}
    (hAB : NamedBlock.Preceq A B) (hBC : NamedBlock.Preceq B C) :
    NamedBlock.Preceq A C := by
  induction C with
  | genesis =>
      have hB : B = .genesis := by
        simpa [NamedBlock.Preceq, NamedBlock.preceq] using hBC
      simpa only [← hB] using hAB
  | node p slot root votes support rows proposer ih =>
      have hBC' : B = .node p slot root votes support rows proposer ∨
          NamedBlock.Preceq B p := by
        simpa only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
          decide_eq_true_eq] using hBC
      rcases hBC' with rfl | hparent
      · exact hAB
      · change (decide (A = .node p slot root votes support rows proposer) ||
          NamedBlock.preceq A p) = true
        simp only [Bool.or_eq_true]
        exact Or.inr (ih hparent)

private theorem rootLock_runBlock_ancestor
    {S : Setup V} {rho : Run V} {A B : NamedBlock V}
    (hB : RunBlock S rho B) (hAB : NamedBlock.Preceq A B) :
    RunBlock S rho A := by
  obtain ⟨C, hC, hCB⟩ := hB
  exact ⟨C, hC, rootLock_named_preceq_trans hAB hCB⟩

omit [Fintype V] in
private theorem rootLock_named_genesis_of_erase_genesis
    {B : NamedBlock V} (hB : B.erase = Block.genesis) :
    B = NamedBlock.genesis := by
  cases B with
  | genesis => rfl
  | node parent slot root votes support rows proposer =>
      simp only [NamedBlock.erase] at hB
      exact absurd hB (by simp)

private theorem rootLock_named_body_of_erased_stateBefore
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {i : Nat} {B : NamedBlock V}
    (hBrun : RunBlock S rho B)
    (hBmem : B.erase ∈ (rho.stateBefore S i v).st.core.T) :
    B ∈ (rho.stateBefore S i v).st.bodies := by
  obtain ⟨D, hD, hDe⟩ := Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore
    S rho i v hBmem
  have hDrun : RunBlock S rho D :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hv hD
  have hroot : D.root = B.root := by
    calc
      D.root = D.erase.root := (Proofs.NamedWire.erase_root D).symm
      _ = B.erase.root := congrArg (fun X : Block V => X.root) hDe
      _ = B.root := Proofs.NamedWire.erase_root B
  have hDB := adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
    D B hDrun hBrun D B (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self B)) hroot
  rw [← hDB]
  exact hD

private theorem rootLock_named_body_of_erased_stateBeforeTime
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) (read : Time) {B : NamedBlock V}
    (hBrun : RunBlock S rho B)
    (hBmem : B.erase ∈ (rho.storeBeforeTime S v read).core.T) :
    B ∈ (rho.storeBeforeTime S v read).bodies := by
  obtain ⟨D, hD, hDe⟩ := Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
    S rho read v hBmem
  obtain ⟨i, hi, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed read
  have hD' : D ∈ (rho.stateBefore S i v).st.bodies := by
    simpa only [Run.storeBeforeTime, hi] using hD
  have hDrun : RunBlock S rho D :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hv hD'
  have hroot : D.root = B.root := by
    calc
      D.root = D.erase.root := (Proofs.NamedWire.erase_root D).symm
      _ = B.erase.root := congrArg (fun X : Block V => X.root) hDe
      _ = B.root := Proofs.NamedWire.erase_root B
  have hDB := adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
    D B hDrun hBrun D B (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self B)) hroot
  rw [← hDB]
  exact hD

private theorem rootLock_runBlock_of_body_stateBeforeTime
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) (read : Time) {B : NamedBlock V}
    (hB : B ∈ (rho.storeBeforeTime S v read).bodies) :
    RunBlock S rho B := by
  obtain ⟨i, hi, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed read
  apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv
  simpa only [Run.storeBeforeTime, hi] using hB

private theorem rootLock_named_height_mono_of_erase_preceq
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {A B : NamedBlock V} (hArun : RunBlock S rho A)
    (hBrun : RunBlock S rho B)
    (hAB : Block.Preceq A.erase B.erase) :
    (Protocol.derive_named S.E S.cfg A).h ≤
      (Protocol.derive_named S.E S.cfg B).h := by
  obtain ⟨A', hA'B, hA'e⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hAB
  have hA'run := rootLock_runBlock_ancestor hBrun hA'B
  have hroot : A'.root = A.root := by
    calc
      A'.root = A'.erase.root := (Proofs.NamedWire.erase_root A').symm
      _ = A.erase.root := congrArg (fun X : Block V => X.root) hA'e
      _ = A.root := Proofs.NamedWire.erase_root A
  have hA'eq := adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
    A' A hA'run hArun A' A (Or.inl (Proofs.NamedAncestry.named_self A'))
      (Or.inr (Proofs.NamedAncestry.named_self A)) hroot
  rw [← hA'eq]
  exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hA'B

omit [Fintype V] in
private theorem rootLock_ancestor_body_mem
    {st : Protocol.NamedStore V} (hpc : NamedStore.NamedParentClosed st)
    {A B : NamedBlock V} (hB : B ∈ st.bodies)
    (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  induction B with
  | genesis =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq,
        decide_eq_true_eq] at hAB
      exact hAB ▸ hB
  | node parent slot root votes support rows proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hparent
      · exact hB
      · exact ih (hpc.2 _ hB) hparent

private theorem rootLock_selectedFGRoot_deriveHeight_lt_hMax
    (S : Setup V) (rho : Run V) (w : V) (read : Time)
    {R : NamedBlock V}
    (hRmem : R ∈ (rho.storeBeforeTime S w read).bodies)
    (hroot : R.erase = Protocol.get_fg_root
      (rho.storeBeforeTime S w read).core.toHealing.toFG)
    (hne : R ≠ NamedBlock.genesis) :
    (Protocol.derive_named S.E S.cfg R).h <
      (rho.storeBeforeTime S w read).core.h_max := by
  let st := rho.storeBeforeTime S w read
  have hRmem' : R ∈ st.bodies := by simpa only [st] using hRmem
  have hroot' : R.erase = Protocol.get_fg_root st.core.toHealing.toFG := by
    simpa only [st] using hroot
  have hco : Proofs.NamedStore.Coherent S.E S.cfg st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho read w).1.1.1
  have hbelow : st.core.h_j < st.core.h_max :=
    NamedJustificationBound.justificationBelowMax_stateBeforeTime S rho read w
  by_cases hgate : st.core.h_max = st.core.h_j + 1
  · have hRJ : R.erase = st.core.J := by
      simpa only [Protocol.get_fg_root, Protocol.Store.toHealing,
        if_pos hgate] using hroot'
    obtain ⟨C, hCmem, hCJ, hChj⟩ :=
      Proofs.Bridges.storeJustificationOnChain_stateBeforeTime S rho read w
    have hCmem' : C ∈ st.bodies := by simpa only [st] using hCmem
    have hCJ' : (Protocol.derive_named S.E S.cfg C).J = st.core.J := by
      simpa only [st] using hCJ
    have hChj' : (Protocol.derive_named S.E S.cfg C).h_j = st.core.h_j := by
      simpa only [st] using hChj
    rcases NamedCheckpointHeights.justified_ancestor_height
        S.E S.cfg C with hz | ⟨J, hJC, hJerase, hJheight⟩
    · have hJgen : st.core.J = Block.genesis := by
        rw [← hCJ']
        exact NamedJustificationCertificates.justified_zero_is_genesis
          S.E S.cfg C hz
      have hRgen : R = NamedBlock.genesis :=
        rootLock_named_genesis_of_erase_genesis (hRJ.trans hJgen)
      exact (hne hRgen).elim
    · have hJmem : J ∈ st.bodies :=
        rootLock_ancestor_body_mem hco.2.2.1 hCmem' hJC
      have hRJerase : R.erase = J.erase :=
        hRJ.trans (hJerase.trans hCJ').symm
      have hRJnamed : R = J := hco.2.1 R hRmem' J hJmem hRJerase
      calc
        (Protocol.derive_named S.E S.cfg R).h =
            (Protocol.derive_named S.E S.cfg J).h := by rw [hRJnamed]
        _ = (Protocol.derive_named S.E S.cfg C).h_j := hJheight
        _ = st.core.h_j := hChj'
        _ < st.core.h_max := hbelow
  · have hRF : R.erase = st.core.F := by
      simpa only [Protocol.get_fg_root, Protocol.Store.toHealing,
        if_neg hgate] using hroot'
    obtain ⟨C, hCmem, hCF, hCFbelow⟩ :=
      Proofs.Bridges.storeFinalizationOnChain_stateBeforeTime S rho read w
    have hCmem' : C ∈ st.bodies := by simpa only [st] using hCmem
    have hCF' : (Protocol.derive_named S.E S.cfg C).F = st.core.F := by
      simpa only [st] using hCF
    have hCFbelow' : (Protocol.derive_named S.E S.cfg C).h_F < st.core.h_max := by
      simpa only [st] using hCFbelow
    rcases NamedCheckpointHeights.finalized_ancestor_height
        S.E S.cfg C with hz | ⟨F, hFC, hFerase, hFheight⟩
    · have hFgen : st.core.F = Block.genesis := by
        rw [← hCF']
        exact NamedFinalityCertificates.finalized_zero_is_genesis S.E S.cfg C hz
      have hRgen : R = NamedBlock.genesis :=
        rootLock_named_genesis_of_erase_genesis (hRF.trans hFgen)
      exact (hne hRgen).elim
    · have hFmem : F ∈ st.bodies :=
        rootLock_ancestor_body_mem hco.2.2.1 hCmem' hFC
      have hRFerase : R.erase = F.erase :=
        hRF.trans (hFerase.trans hCF').symm
      have hRFnamed : R = F := hco.2.1 R hRmem' F hFmem hRFerase
      calc
        (Protocol.derive_named S.E S.cfg R).h =
            (Protocol.derive_named S.E S.cfg F).h := by rw [hRFnamed]
        _ = (Protocol.derive_named S.E S.cfg C).h_F := hFheight
        _ < st.core.h_max := hCFbelow'

/-- At an exact fixed frontier, finality-filter noninterference orients the
opening vote-duty FG root below every protected block at that frontier or
higher. The apparent reverse-root arm is impossible unless the selected root
is genesis: every other reachable selected root has height strictly below the
frontier. -/
theorem openingVoteFGRoot_preceq_of_fixedFrontier_noninterference
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {H : Height} {v : V} (_hv : v ∈ rho.honest)
    {s : Slot} {B : NamedBlock V} (hBrun : RunBlock S rho B)
    (hBheight : H ≤ (Protocol.derive_named S.E S.cfg B).h)
    (hfrontier : (Proofs.Optimistic.voteDutyStore S rho v (s + 1)).h_max = H)
    (hquiet : FinalityFilterNoninterferenceAtRead S rho v
      (Protocol.vote_time S.E (s + 1)) B.erase) :
    Block.Preceq
      (Protocol.get_fg_root
        (Internal.NamedRecoveryRead.voteDutyRead S rho v (s + 1)).st.core.toHealing.toFG)
      B.erase := by
  let read := Protocol.vote_time S.E (s + 1)
  let st := rho.storeBeforeTime S v read
  let root := Protocol.get_fg_root st.core.toHealing.toFG
  have hfrontierPre : st.core.h_max = H := by
    simpa only [st, read, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using hfrontier
  have hquietPre : B.erase ⪯ root ∨ B.erase ∈
      Protocol.get_filtered_block_tree st.core.toHealing.toFG := by
    simpa only [FinalityFilterNoninterferenceAtRead, st, root, read] using hquiet
  have hrootPre : Block.Preceq root B.erase := by
    rcases hquietPre with hBroot | hfiltered
    · by_cases hrootGenesis : root = Block.genesis
      · rw [hrootGenesis]
        exact Protocol.preceq_genesis B.erase
      · have hrootMem : root ∈ st.core.T := by
          unfold root Protocol.get_fg_root
          split_ifs
          · exact Proofs.NamedStoreBridge.justifiedInTree_stateBeforeTime S rho read v
          · exact Proofs.NamedStoreBridge.finalizedInTree_stateBeforeTime S rho read v
        obtain ⟨Rn, hRnMem, hRnErase⟩ :=
          Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho read v hrootMem
        have hRnNe : Rn ≠ NamedBlock.genesis := by
          intro hgen
          apply hrootGenesis
          rw [← hRnErase, hgen]
          rfl
        have hRnRun := rootLock_runBlock_of_body_stateBeforeTime S adm
          _hv read hRnMem
        have hrootHeight :
            (Protocol.derive_named S.E S.cfg Rn).h < st.core.h_max :=
          rootLock_selectedFGRoot_deriveHeight_lt_hMax S rho v read
            hRnMem hRnErase hRnNe
        have hBrootHeight :
            (Protocol.derive_named S.E S.cfg B).h ≤
              (Protocol.derive_named S.E S.cfg Rn).h :=
          rootLock_named_height_mono_of_erase_preceq S adm hBrun hRnRun
            (by simpa only [hRnErase] using hBroot)
        exact ((not_le_of_gt hrootHeight)
          (hfrontierPre ▸ hBheight.trans hBrootHeight)).elim
    · exact Proofs.Records.preceq_get_fg_root_of_mem_filtered hfiltered
  simpa only [root, st, read, Internal.NamedRecoveryRead.voteDutyRead,
    NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
    Protocol.NamedStore.setClock] using hrootPre

private theorem rootLock_commonActionPrefix_preceq
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {K : Height} {r : Round} {s : Slot} {C B : NamedBlock V}
    (hCrun : RunBlock S rho C)
    (hCheight : (Protocol.derive_named S.E S.cfg C).h < K)
    (hCtargets : ∀ u ∈ rho.honest,
      Block.Preceq C.erase (actionSGBlockAt S rho u r))
    (hcanonical : SGTargetConeCanonicality S rho r s)
    (hBrun : RunBlock S rho B)
    (hBheight : K ≤ (Protocol.derive_named S.E S.cfg B).h)
    (hBcone : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq B.erase X)) :
    Block.Preceq C.erase B.erase := by
  have hmajority := hcom s
  have hpos : 0 < ((S.E.committee s) ∩ rho.honest).card := by
    omega
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
  have huHonest : u ∈ rho.honest := (Finset.mem_inter.mp hu).2
  let T := actionSGBlockAt S rho u r
  have hTcone : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq T X) := by
    simpa only [T] using hcanonical u huHonest
  have hCT : Block.Preceq C.erase T := by
    simpa only [T] using hCtargets u huHonest
  have hTBcompatible : Block.compatible T B.erase = true :=
    sgTargetCompatible_of_honestVotesCone S hcom
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      adm.toNamedAdmissibleCore.toNamedRootCollisionFree hTcone hBcone
  simp only [Block.compatible, Bool.or_eq_true] at hTBcompatible
  rcases hTBcompatible with hTB | hBT
  · exact Block.preceq_trans hCT hTB
  · have hCBcompatible : Block.compatible C.erase B.erase = true :=
      compatible_of_common_honest_goldfish_head hCT hBT
    simp only [Block.compatible, Bool.or_eq_true] at hCBcompatible
    rcases hCBcompatible with hCB | hBC
    · exact hCB
    · have hBheightLeC :
          (Protocol.derive_named S.E S.cfg B).h ≤
            (Protocol.derive_named S.E S.cfg C).h :=
        rootLock_named_height_mono_of_erase_preceq S adm hBrun hCrun hBC
      exact ((not_le_of_gt hCheight)
        (hBheight.trans hBheightLeC)).elim

/-- A prefix strictly below the fixed frontier is below every height-qualified
cone target when it is already below all honest action targets. The two cones
give compatibility through Claim 2; the reverse ancestry orientation would
put a height-`K` block below the strictly lower prefix. -/
theorem commonActionPrefix_preceq_heightQualifiedConeTarget
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {K : Height} {r : Round} {s : Slot} {C B : NamedBlock V}
    (hCrun : RunBlock S rho C)
    (hCheight : (Protocol.derive_named S.E S.cfg C).h < K)
    (hCtargets : ∀ u ∈ rho.honest,
      Block.Preceq C.erase (actionSGBlockAt S rho u r))
    (hcanonical : SGTargetConeCanonicality S rho r s)
    (hBrun : RunBlock S rho B)
    (hBheight : K ≤ (Protocol.derive_named S.E S.cfg B).h)
    (hBcone : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq B.erase X)) :
    Block.Preceq C.erase B.erase :=
  rootLock_commonActionPrefix_preceq S adm hcom hCrun hCheight hCtargets
    hcanonical hBrun hBheight hBcone

/-- A height-qualified slot-`s` cone target is processed at every honest
slot-`s + 1` vote read under an exact fixed frontier. The proof relays one
honest emitted cone head, derives every recipient finality guard from the
frontier cap and accountable safety, then uses parent closure to retain the
cone target. -/
theorem heightQualifiedConeTarget_mem_openingVoteRead_of_fixedFrontier
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {K : Height} {s : Slot} {B : NamedBlock V} {v : V}
    (hv : v ∈ rho.honest)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hnextHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    (hBheight : K ≤ (Protocol.derive_named S.E S.cfg B).h)
    (hfrontier : (Proofs.Optimistic.voteDutyStore S rho v (s + 1)).h_max = K)
    (hBcone : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq B.erase X))
    (hBrun : RunBlock S rho B) :
    B ∈ (rho.storeBeforeTime S v
      (Protocol.vote_time S.E (s + 1))).bodies := by
  have hmajority := hcom s
  have hpos : 0 < ((S.E.committee s) ∩ rho.honest).card := by
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  obtain ⟨hxCommittee, hxHonest⟩ := Finset.mem_inter.mp hx
  obtain ⟨X, hBX, hXrun, hXemit⟩ := hBcone x hxHonest hxCommittee
  have hXmem : X.erase ∈
      (Internal.NamedRecoveryRead.voteDutyRead S rho x s).st.core.T :=
    Protocol.emittedHead_mem_voteDutyStore S adm hxHonest hXrun hXemit
  obtain ⟨nX, hnX, hbeforeX⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (Protocol.vote_time S.E s)
  have hXprefix : X.erase ∈ (rho.stateBefore S nX x).st.core.T := by
    simpa only [Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, Run.storeBeforeTime, hnX] using hXmem
  have hXbody : X ∈ (rho.stateBefore S nX x).st.bodies :=
    rootLock_named_body_of_erased_stateBefore S adm hxHonest hXrun hXprefix
  have hXprocessed : Object.processed
      (rho.stateBefore S nX x).st (.block X) = true := by
    simp only [Object.processed, NamedReceipt.processed, decide_eq_true_eq]
    exact hXbody
  rcases Protocol.acceptsAt_block_of_processed S rho x nX X hXprocessed with
    hXgen | ⟨iX, hiX, tX, hXacc⟩
  · have hBgen : B.erase = Block.genesis := by
      have hBXgen : Block.Preceq B.erase Block.genesis := by
        simpa only [hXgen, NamedBlock.erase] using hBX
      exact Block.preceq_antisymm hBXgen (Protocol.preceq_genesis B.erase)
    rw [rootLock_named_genesis_of_erase_genesis hBgen]
    have hcoh : Proofs.NamedStore.Coherent S.E S.cfg
        (rho.storeBeforeTime S v
          (Protocol.vote_time S.E (s + 1))) :=
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
        (Protocol.vote_time S.E (s + 1)) v).1.1.1
    exact hcoh.2.2.1.1
  · obtain ⟨-, eX, heX, -, heXt⟩ := hXacc.1
    have htX : tX < Protocol.vote_time S.E s := by
      rw [← heXt]
      exact hbeforeX iX eX hiX heX
    have hXslotPos : 0 < X.slot := by
      have hXslotPos' : 0 < X.erase.slot :=
        Nat.zero_lt_of_lt (Protocol.parent_slot_lt_of_acceptsAt_block S hXacc)
      simpa only [Proofs.NamedWire.erase_slot] using hXslotPos'
    have hcutRead : Protocol.support_cutoff S.E s ≤
        Protocol.vote_time S.E (s + 1) :=
      Proofs.Optimistic.support_cutoff_le_vote_time_succ S.E s
    have hsupportHor : Protocol.support_cutoff S.E s ≤ rho.horizon :=
      hcutRead.trans hnextHor
    have hfrontierPre :
        (rho.storeBeforeTime S v
          (Protocol.vote_time S.E (s + 1))).core.h_max = K := by
      simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore] using hfrontier
    have hsb : SlashableBound S rho :=
      slashableBound_of_admissible_belowOneThird S adm hfb
    have hFhist : BlockFinalizedBelowAtDeliveriesBefore S rho v X
        (Protocol.support_cutoff S.E s) := by
      intro i hi
      let st := (rho.stateBefore S i v).st
      let n := (rho.events.filter
        (fun e => decide (e.time < Protocol.vote_time S.E (s + 1)))).length
      have hiN : i ≤ n := hi.trans (strict_filter_length_mono rho hcutRead)
      have hstore : rho.storeBeforeTime S v
          (Protocol.vote_time S.E (s + 1)) =
            (rho.stateBefore S n v).st := by
        simpa only [Run.storeBeforeTime, n] using
          congrArg NamedNodeState.st
            (congrArg (fun (world : NamedWorld V) => world v)
              (Proofs.Optimistic.stateBeforeTime_eq_take S
                adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
                (Protocol.vote_time S.E (s + 1))))
      have hstateCap : st.core.h_max ≤ K := by
        have hprefix : st.core.h_max ≤
            (rho.stateBefore S n v).st.core.h_max :=
          stateBefore_hMax_mono S rho v hiN
        apply hprefix.trans
        rw [← hstore]
        exact hfrontierPre.le
      obtain ⟨D, hD, hDF, hDbound⟩ :=
        Proofs.Bridges.storeFinalizationOnChain_stateBefore S rho i v
      have hDrun : RunBlock S rho D :=
        Proofs.Bridges.runBlock_of_stateBefore_mem S hv hD
      have hBXheight :
          (Protocol.derive_named S.E S.cfg B).h ≤
            (Protocol.derive_named S.E S.cfg X).h :=
        rootLock_named_height_mono_of_erase_preceq S adm hBrun hXrun hBX
      have hcrossed : (Protocol.derive_named S.E S.cfg D).h_F <
          (Protocol.derive_named S.E S.cfg X).h := by
        exact lt_of_lt_of_le (hDbound.trans_le hstateCap)
          (hBheight.trans hBXheight)
      have hpreceq := NamedFinalizationBridge.finalized_preceq_of_height_lt
        S rho X D hsb adm.toNamedAdmissibleCore.toNamedRootCollisionFree
          hXrun hDrun hcrossed
      simpa only [hDF] using hpreceq
    have hXadmit : AdmittedBefore S rho v X.erase
        (Protocol.support_cutoff S.E s) :=
      Protocol.block_admittedBefore_of_accepted_after_cutoff
        S adm hxHonest hv hXslotPos hXacc htX hpost
          (Proofs.Optimistic.vote_time_add_delta S.E s) hsupportHor hFhist
    have hXtarget : X.erase ∈
        (rho.storeBeforeTime S v
          (Protocol.vote_time S.E (s + 1))).core.T :=
      (Protocol.admittedBefore_mem_and_stamp_at S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hXadmit hcutRead).1
    have hpcTarget : ParentClosed
        (rho.storeBeforeTime S v
          (Protocol.vote_time S.E (s + 1))).core :=
      Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
        (Protocol.vote_time S.E (s + 1)) v
    have hBtarget : B.erase ∈
        (rho.storeBeforeTime S v
          (Protocol.vote_time S.E (s + 1))).core.T :=
      Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpcTarget).2
        B.erase X.erase hXtarget hBX
    exact rootLock_named_body_of_erased_stateBeforeTime S adm hv
      (Protocol.vote_time S.E (s + 1)) hBrun hBtarget

/-- A fixed-frontier certificate constructs the opening cone-root lock.
Height-qualified cone targets are relayed to every concrete opening read, so
root orientation and finality-filter noninterference need no callback. -/
theorem sgTargetOpeningConeRootLock_of_fixedFrontier_certifiedPrefix
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {K : Height} {r : Round} {s : Slot} {C : NamedBlock V}
    (hcanonical : SGTargetConeCanonicality S rho r s)
    (hCrun : RunBlock S rho C)
    (hcert : Certificate S rho (K - 1) C.root)
    (hCheight : (Protocol.derive_named S.E S.cfg C).h < K)
    (hCtargets : ∀ u ∈ rho.honest,
      Block.Preceq C.erase (actionSGBlockAt S rho u r))
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hreadHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    (hfrontier : ∀ v ∈ rho.honest,
      (Proofs.Optimistic.voteDutyStore S rho v (s + 1)).h_max = K) :
    SGTargetOpeningConeRootLock S rho K r s := by
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  refine ⟨hcanonical, ?_⟩
  intro B hBrun hBheight hBcone v hv
  have hCB : Block.Preceq C.erase B.erase :=
    commonActionPrefix_preceq_heightQualifiedConeTarget
      S adm hcom hCrun hCheight hCtargets hcanonical hBrun hBheight hBcone
  have hBmem := heightQualifiedConeTarget_mem_openingVoteRead_of_fixedFrontier
    S adm hcom hfb hv hpost hreadHor hBheight (hfrontier v hv) hBcone hBrun
  have hBtarget : B.erase ∈
      (rho.storeBeforeTime S v
        (Protocol.vote_time S.E (s + 1))).core.T := by
    have hcoh : Proofs.NamedStore.Coherent S.E S.cfg
        (rho.storeBeforeTime S v
          (Protocol.vote_time S.E (s + 1))) :=
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
        (Protocol.vote_time S.E (s + 1)) v).1.1.1
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hBmem
  have hfrontierPre :
      (rho.storeBeforeTime S v
        (Protocol.vote_time S.E (s + 1))).core.h_max = K := by
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using hfrontier v hv
  have hquiet :=
    finalityFilterNoninterferenceAtRead_of_fixedFrontier_certifiedPrefix
      (C := C.erase) S adm hfb hsb hv hreadHor hBtarget hBmem rfl hBrun hBheight
        hfrontierPre rfl hCrun (by simpa only [Proofs.NamedWire.erase_root] using hcert) hCB
  exact openingVoteFGRoot_preceq_of_fixedFrontier_noninterference
    S adm hv hBrun hBheight (hfrontier v hv) hquiet












#print axioms ancestorConfirmation_eligible_of_preceq
#print axioms actionSGBlockAt_clear_or_selectedG2
#print axioms mem_filtered_of_mem_tree_of_exactFGRoot_heightCap
#print axioms voterProcessedTarget_of_genuineConfirmation_at_laterVoteDuty_after_gst
#print axioms sgTargetOpeningConeRootLock_of_fixedFrontier_certifiedPrefix

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
