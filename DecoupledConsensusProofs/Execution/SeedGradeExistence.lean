module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedOpeningWindow

@[expose] public section

/-!
# Grade existence at one honest store

`GradeFormsAt` is a run-level statement: one block active at EVERY honest
action store. `SeedRoundGradedAt` is weaker and per store — each honest action
store selects some grade-2 block, and the blocks may differ. This module
supplies the per-store producer.

Every step of the run-level chain
(`cleanActionReadFor_of_actionCarriersCover_and_next_active`, then
`cleanGradeReadFor_of_cleanActionRead`, then `G2_of_cleanGradeRead`) is already
pointwise in the reader `w`: the reader's activity hypothesis is used only at
`w` itself. The three proofs are reproduced here with the run-level `active`
field replaced by activity at the one store, which is what lets each store use
its OWN fork-choice root as the graded block.

That is the point of the per-store form. Under the gate-off window
`h_max ≠ h_j + 1`, so `get_fg_root` is the store's finalized block
(`Protocol.get_fg_root`), which is in that store's own filtered tree for
free. The only thing left to ask of the protocol is an ordering: the reader's
own root is at or below the previous round's honest action carriers.
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

variable {V : Type} [DecidableEq V] [Fintype V]

/-- **The reader's own resolved support**, pointwise in the reader. This is
the `resolved_support` field of
`cleanActionReadFor_of_actionCarriersCover_and_next_active`, with the run-level
activity hypothesis replaced by activity at the reader's own store. -/
theorem seedActionRead_resolvedSupport_at_store
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {P : Block V} {w : V} (hw : w ∈ rho.honest)
    {v : V} (hv : v ∈ rho.honest)
    (hPHv : Block.Preceq P (actionSGBlockAt S rho v r))
    (hpost : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hactiveW : P ∈ Protocol.get_filtered_block_tree
      (healStoreAt S rho w (r + 1)).toFG) :
    occurrenceBefore
        (Protocol.sg_resolution_time (gradeViewAt S rho w (r + 1)).T
          (gradeViewAt S rho w (r + 1)).timestamp_block
          (gradeViewAt S rho w (r + 1)).timestamp_sg_vote
          (actionSGVoteAt S rho v r))
        (S.hc.Γ_neg1 S.E.Δ (r + 1)) = true ∧
      Protocol.head_covers (gradeViewAt S rho w (r + 1)).T P
        (actionSGVoteAt S rho v r).confirmed = true := by
  let H := actionSGBlockAt S rho v r
  have hHsource : H ∈ (rho.storeBeforeTime S v (S.a r)).T := by
    simpa only [H] using actionSGBlockAt_mem_storeBeforeTime S rho v r
  have hPH : Block.Preceq P H := by
    simpa only [H] using hPHv
  have hvisible : H ∈
        (rho.storeBeforeTime S w (S.a (r + 1))).T ∧
      stampedBefore
        (rho.storeBeforeTime S w (S.a (r + 1))).timestamp_block
        (S.hc.Γ_neg1 S.E.Δ (r + 1)) H = true := by
    rcases block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTime
        S adm.toNamedScheduleWellFormed v (S.a r) hHsource with
      hgen | ⟨D, i, t, hDerase, hacc, ht⟩
    · simpa only [H, hgen] using
        (Protocol.genesis_mem_and_stamp_storeBeforeTime S
          adm.toNamedScheduleWellFormed w (S.a (r + 1))
          (S.hc.Γ_neg1 S.E.Δ (r + 1)))
    · have hHpos : 0 < D.slot := by
        have hparent := Protocol.parent_slot_lt_of_acceptsAt_block S hacc
        have hslot : D.erase.slot = D.slot := by cases D <;> rfl
        rw [hslot] at hparent
        exact Nat.zero_lt_of_lt hparent
      have hrelayRead : S.a r + S.E.Δ ≤ S.a (r + 1) :=
        le_trans (action_add_delta_le_next_Γ_neg1 S r)
          (le_of_lt (next_Γ_neg1_lt_action S r))
      have hFhist :=
        finalizedBelowAtDeliveriesBefore_of_filteredAtLaterRead
          S adm hrelayRead (by simpa only [healStoreAt] using hactiveW)
            (by rw [hDerase]; exact hPH)
      have hrelayHor : S.a r + S.E.Δ ≤ rho.horizon :=
        le_trans (action_add_delta_le_next_Γ_neg1 S r) hcut
      have hadmit := Protocol.block_admittedBefore_of_accepted_after_cutoff
        S adm hv hw hHpos hacc ht hpost rfl hrelayHor hFhist
      obtain ⟨C, hCerase, j, t', hacc', ht'⟩ := hadmit
      have hadmitNext : Protocol.AdmittedBefore S rho w H
          (S.hc.Γ_neg1 S.E.Δ (r + 1)) :=
        ⟨C, hCerase.trans hDerase, j, t', hacc', lt_of_lt_of_le ht'
          (action_add_delta_le_next_Γ_neg1 S r)⟩
      exact Protocol.admittedBefore_mem_and_stamp_at S
        adm.toNamedScheduleWellFormed hadmitNext
        (le_of_lt (next_Γ_neg1_lt_action S r))
  have hvoteStamp := actionSGVote_stamp_before_next_Γ_neg1
    S adm hv hw r hpost hcut
  have hHmem : H ∈
      (rho.stateBeforeTime S (S.a (r + 1)) w).st.core.T := by
    simpa only [Run.storeBeforeTime, H] using hvisible.1
  obtain ⟨Hn, hHnmem, hHnerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (S.a (r + 1)) w hHmem
  obtain ⟨N, hN, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedScheduleWellFormed.sorted (S.a (r + 1))
  have hHrun : RunBlock S rho Hn := by
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw (i := N)
    simpa only [hN] using hHnmem
  have hfind : Block.find?
      (gradeViewAt S rho w (r + 1)).T H.root = some H := by
    apply Proofs.Optimistic.find?_eq_some_of_unique
    · simpa only [gradeViewAt, healStoreAt, Run.storeBeforeTime,
        Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hvisible.1
    · intro Y hY hroot
      have hYmem : Y ∈
          (rho.stateBeforeTime S (S.a (r + 1)) w).st.core.T := by
        simpa only [gradeViewAt, healStoreAt, Run.storeBeforeTime,
          Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hY
      obtain ⟨Yn, hYnmem, hYnerase⟩ :=
        Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
          (S.a (r + 1)) w hYmem
      have hYrun : RunBlock S rho Yn := by
        apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw (i := N)
        simpa only [hN] using hYnmem
      have hrawRoots : Yn.erase.root = Hn.erase.root := by
        rw [hYnerase, hHnerase]
        exact hroot
      have hroots : Yn.root = Hn.root :=
        (Proofs.NamedWire.erase_root Yn).symm.trans
          (hrawRoots.trans (Proofs.NamedWire.erase_root Hn))
      have heq := adm.toNamedRootCollisionFree.root_injective Yn Hn
        hYrun hHrun Yn Hn (Or.inl (Proofs.NamedAncestry.named_self Yn))
        (Or.inr (Proofs.NamedAncestry.named_self Hn)) hroots
      exact hYnerase.symm.trans ((congrArg NamedBlock.erase heq).trans hHnerase)
  have hblock : occurrenceBefore
      ((gradeViewAt S rho w (r + 1)).timestamp_block H)
      (S.hc.Γ_neg1 S.E.Δ (r + 1)) = true := by
    simpa only [gradeViewAt, healStoreAt, Run.storeBeforeTime,
      Protocol.HealingStore.gradeView, Protocol.Store.toHealing,
      stampedBefore_eq_occurrenceBefore, H] using hvisible.2
  have hfindAction : Block.find? (gradeViewAt S rho w (r + 1)).T
      (actionSGBlockAt S rho v r).root =
        some (actionSGBlockAt S rho v r) := by
    simpa only [H] using hfind
  constructor
  · simp only [Protocol.sg_resolution_time, actionSGVoteAt, hfindAction]
    exact occurrenceBefore_max hvoteStamp hblock
  · simp only [Protocol.head_covers, actionSGVoteAt, hfindAction]
    exact hPHv

/-- **The reader's own honest support summary**, pointwise in the reader. This
is `cleanGradeReadFor_of_cleanActionRead`'s second field at one store. -/
theorem seedGradeRead_honestSupport_at_store
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {P : Block V} {w : V} (hw : w ∈ rho.honest)
    {v : V} (hv : v ∈ rho.honest)
    (hpost : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hresolved :
      occurrenceBefore
          (Protocol.sg_resolution_time (gradeViewAt S rho w (r + 1)).T
            (gradeViewAt S rho w (r + 1)).timestamp_block
            (gradeViewAt S rho w (r + 1)).timestamp_sg_vote
            (actionSGVoteAt S rho v r))
          (S.hc.Γ_neg1 S.E.Δ (r + 1)) = true ∧
        Protocol.head_covers (gradeViewAt S rho w (r + 1)).T P
          (actionSGVoteAt S rho v r).confirmed = true) :
    occurrenceBefore
        (Protocol.summary (gradeViewAt S rho w (r + 1)) (r + 1) v).t_v
        (S.hc.Γ_neg1 S.E.Δ (r + 1)) = true ∧
      Protocol.head_covers (gradeViewAt S rho w (r + 1)).T P
          (Protocol.summary (gradeViewAt S rho w (r + 1)) (r + 1) v).C_v
          = true ∧
        occurrenceAtLeast
          (Protocol.summary (gradeViewAt S rho w (r + 1)) (r + 1) v).e_v
          (S.hc.Γ_2 S.E.Δ (r + 1)) = true := by
  let u := actionSGVoteAt S rho v r
  let gv := gradeViewAt S rho w (r + 1)
  let batch := Protocol.sg_votes_by (Protocol.round_batch gv (r + 1)) v
  let tau := Protocol.sg_resolution_time gv.T
    gv.timestamp_block gv.timestamp_sg_vote
  let headed := batch.filter (fun x =>
    x.confirmed.isSome ∧ Protocol.sg_resolved gv.T x = true)
  have huBatch : u ∈ batch := by
    simpa only [u, batch, gv] using
      (actionSGVote_mem_next_round_batch S adm hv hw r hpost hcut)
  have hut : occurrenceBefore (tau u)
      (S.hc.Γ_neg1 S.E.Δ (r + 1)) = true := by
    simpa only [tau, gv, u] using hresolved.1
  have huResolved : Protocol.sg_resolved gv.T u = true := by
    cases hfind :
        Block.find? gv.T (actionSGBlockAt S rho v r).root with
    | none =>
        simp [tau, u, actionSGVoteAt, Protocol.sg_resolution_time,
          hfind, occurrenceBefore] at hut
    | some H =>
        simp [u, actionSGVoteAt, Protocol.sg_resolved, hfind]
  have huHeaded : u ∈ headed := by
    apply Finset.mem_filter.mpr
    refine ⟨huBatch, ?_⟩
    exact ⟨by simp [u, actionSGVoteAt], huResolved⟩
  have hcard0 := Protocol.roundBatch_card_le_one_stateBeforeTime
    S adm (t := S.a (r + 1)) (w := w) (r := r + 1) (v := v) hv
  have hcard : batch.card ≤ 1 := by
    simpa only [batch, gv, gradeViewAt, healStoreAt, Run.storeBeforeTime,
      Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hcard0
  have hheadedCard : headed.card ≤ 1 :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans hcard
  have hfirst : Protocol.batch_first? tau headed = some u :=
    Proofs.Optimistic.batch_first?_of_card_le_one huHeaded hheadedCard
  have hsummaryC : (Protocol.summary gv (r + 1) v).C_v = u.confirmed := by
    change (Protocol.batch_first? tau headed).bind
      Protocol.SGVote.confirmed = u.confirmed
    rw [hfirst]
    rfl
  have hsummaryT : (Protocol.summary gv (r + 1) v).t_v = tau u := by
    change (Protocol.batch_first? tau headed).elim none tau = tau u
    rw [hfirst]
    simp
  have heNone : (Protocol.summary gv (r + 1) v).e_v = none := by
    rw [Proofs.Optimistic.summary_e_v_eq]
    exact Proofs.Optimistic.equivocation_instant_eq_none hcard
  refine ⟨?_, ?_, ?_⟩
  · rw [hsummaryT]
    exact hut
  · rw [hsummaryC]
    simpa only [gv, u] using hresolved.2
  · rw [heNone]
    rfl

/-- **Grade 2 at one honest store from the previous round's carriers.** The
run-level producer asks for the block to be active at every honest store; this
one asks only at the reader, which is what lets the reader use its own
fork-choice root. -/
theorem seedG2_of_carrierQuorum_at_store
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {P : Block V} {w : V} (hw : w ∈ rho.honest)
    {H : Finset V} (hsub : H ⊆ rho.honest)
    (hweight : S.E.m ≤ S.E.electorate.weightOf H)
    (hcover : ∀ v ∈ H, Block.Preceq P (actionSGBlockAt S rho v r))
    (hpost : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hactiveW : P ∈ Protocol.get_filtered_block_tree
      (healStoreAt S rho w (r + 1)).toFG) :
    Protocol.G2 S.E (gradeViewAt S rho w (r + 1)) S.hc (r + 1) P = true := by
  simp only [Protocol.G2, decide_eq_true_eq]
  unfold Protocol.direct_support
  refine le_trans hweight (S.E.electorate.weightOf_mono ?_)
  intro v hv
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ v, ?_⟩
  exact seedGradeRead_honestSupport_at_store S adm hw (hsub hv) hpost hcut
    (seedActionRead_resolvedSupport_at_store S adm hw (hsub hv) (hcover v hv)
      hpost hcut hactiveW)

/-- The whole-honest-set form of `seedG2_of_carrierQuorum_at_store`. -/
theorem seedG2_of_actionCarriersCover_at_store
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hmajority : HonestWeightMajority S rho.honest)
    {r : Round} {P : Block V} {w : V} (hw : w ∈ rho.honest)
    (hcover : ActionCarriersCover S rho r P)
    (hpost : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hactiveW : P ∈ Protocol.get_filtered_block_tree
      (healStoreAt S rho w (r + 1)).toFG) :
    Protocol.G2 S.E (gradeViewAt S rho w (r + 1)) S.hc (r + 1) P = true :=
  seedG2_of_carrierQuorum_at_store S adm hw (Finset.Subset.refl rho.honest)
    (honestWeight_ge_m hmajority) hcover hpost hcut hactiveW


/-! ## The seed's grade obligation, reduced to one ordering -/




/-
/-- **The seed's grade obligation follows from the ordering.** Each honest
action store grades its OWN fork-choice root: the root is in that store's
filtered tree for free, and the ordering makes the previous round's honest
carriers a grade-2 quorum for it. -/
theorem seedRoundGraded_of_rootBelowPreviousCarriers
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {q: Round} (hq: 2 ≤ q)
    (hpostPrev: S.E.t_GST ≤ S.a (q - 2))
    (hpost: S.E.t_GST ≤ S.a (q - 1))
    (hcutPrev: S.hc.Γ_neg1 S.E.Δ (q - 1) ≤ rho.horizon)
    (hcut: S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon)
    (hprev: SeedRootBelowPreviousCarriersAt S rho (q - 1))
    (hcur: SeedRootBelowPreviousCarriersAt S rho q):
    SeedRoundGradedAt S rho q:= by
  have hq1: 1 ≤ q:= (by decide: (1: Nat) ≤ 2).trans hq
  have hqPred: q - 1 + 1 = q:= Nat.sub_add_cancel hq1
  have hqPred2: q - 2 + 1 = q - 1:= by
    have key: ∀ a: Nat, 2 ≤ a → a - 2 + 1 = a - 1:= by
      intro a h; omega
    exact key q hq
  have hstep: q - 1 - 1 = q - 2:= by
    have key: ∀ a: Nat, a - 1 - 1 = a - 2:= by
      intro a; omega
    exact key q
  refine ⟨?_, ?_⟩
  · intro v hv
    obtain ⟨H, hsub, hweight, hcover⟩:= hprev v hv
    rw [hstep] at hcover
    have hactive:= seedOwnRoot_active S adm (w:= v) (q - 1)
    have hproduced:= seedGrade2Block_isSome_of_carrierQuorum_at_store
      S adm hv hsub hweight hcover hpostPrev
      (by rwa [hqPred2]) (by rwa [hqPred2])
    rwa [hqPred2] at hproduced
  · intro v hv
    obtain ⟨H, hsub, hweight, hcover⟩:= hcur v hv
    have hactive:= seedOwnRoot_active S adm (w:= v) q
    have hproduced:= seedGrade2Block_isSome_of_carrierQuorum_at_store
      S adm hv hsub hweight hcover hpost
      (by rwa [hqPred]) (by rwa [hqPred])
    rwa [hqPred] at hproduced
-/

/-! ## The ordering under the gate-off window -/



end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms seedActionRead_resolvedSupport_at_store
#print axioms seedGradeRead_honestSupport_at_store
#print axioms seedG2_of_carrierQuorum_at_store
#print axioms seedG2_of_actionCarriersCover_at_store
end DecoupledConsensusModel.Proofs.HealingSurface

end
