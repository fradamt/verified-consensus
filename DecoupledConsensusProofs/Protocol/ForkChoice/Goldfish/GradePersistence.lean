module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.PostGSTCarrierAdmissionCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeDelivery
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecoveryTimeout

@[expose] public section

/-!
# Persistence of one common grade through the next Section 7 action

The fixed-cutoff delivery theorem transports the exact SG action vote. This
file supplies the other half of the clean-read producer: when a common grade-2
block remains active at the next read, every honest action vote names a
descendant of that block, and admissibility relays both the vote and its named
block before the next `Gamma[-1]` cutoff.

The remaining recovery boundary is therefore only activity. A finite burn
argument must either keep a common descendant active or charge the transition
that removes it to a conflicting certificate release or a permanent height
crossing. No such transition is assumed here.

 repair: `GradeFormsAt` no longer exists; the common
grade premise is `NamedGradeFormsAt`, the relative G2-domain-read grade
(`ActionSourceCoreRun.lean`). Consuming that grade at the exact action carrier
now needs the additional fact that the graded block is still active at the
reader's own action read (the `hownActive`/`hownActiveAll` hypotheses below):
under the frame runtime, activity at the earlier G2-domain tick does not by
itself persist to the later action read (`ActionSourceCoreRun.preceq_actionQ2
_of_domainGrade`'s two separate membership premises), so the two theorems below
carry it explicitly, following that file's model.

The last hop — producing a *new* `NamedGradeFormsAt` at round `r + 1` from a
`CleanActionReadFor` at round `r` — is a different direction entirely: it goes
from the exact-action-vote's ABSOLUTE resolved quorum to the RELATIVE
G2-domain-read grade, and `GradeBootstrapCoreRun.lean` already records, at
`gradeFormsAt_of_cleanActionRead`, that no such absolute-to-relative bridge
exists in the live tree (: "the surface's own declared open step").
Nothing here reopens that gap, so `gradeFormsAt_succ_of_gradeFormsAt_and_next
_active` and its corollary `gradeFormsAt_of_seed_and_active_suffix` are Open
(class d) and are recorded, not available, below.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]



/-- If the common grade remains active at the next read, the exact block named
by every honest action vote is present there and stamped before the next
earliest grade cutoff.

Statement change: `GradeFormsAt` is retired in favour
of `NamedGradeFormsAt`, the relative grade at the round's own G2-domain read.
Consuming it at validator `v`'s exact action carrier additionally needs `P`
still active at `v`'s own action read (`hownActive`) and `0 < r`
(`ActionSourceCoreRun.preceq_actionSGBlockAt_of_namedGradeFormsAt`'s own
premises); neither is derivable from the surrounding hypotheses, so both are
new explicit premises here. -/
theorem actionSGBlockAt_visible_next_Γ_neg1_of_namedGradeFormsAt
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (hr : 0 < r) {P : Block V} (hforms : NamedGradeFormsAt S rho r P)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    (hpost : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hownActive : P ∈ PhaseGrades.filteredTree (actionReadAt S rho v r))
    (hactive : P ∈ Protocol.get_filtered_block_tree
      (healStoreAt S rho w (r + 1)).toFG) :
    actionSGBlockAt S rho v r ∈
        (rho.storeBeforeTime S w (S.a (r + 1))).T ∧
      stampedBefore
        (rho.storeBeforeTime S w (S.a (r + 1))).timestamp_block
        (S.hc.Γ_neg1 S.E.Δ (r + 1))
        (actionSGBlockAt S rho v r) = true := by
  let H := actionSGBlockAt S rho v r
  have hhor : S.a r ≤ rho.horizon :=
    le_trans (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos))
      (le_trans (action_add_delta_le_next_Γ_neg1 S r) hcut)
  have hHsource : H ∈ (rho.storeBeforeTime S v (S.a r)).T :=
    actionSGBlockAt_mem_storeBeforeTime S rho v r
  have hPH : Block.Preceq P H :=
    preceq_actionSGBlockAt_of_namedGradeFormsAt S adm.toNamedAdmissibleCore hr hhor
      hforms hv hownActive
  rcases block_eq_genesis_or_acceptsBefore_of_mem_storeBeforeTime
      S adm.toNamedScheduleWellFormed v (S.a r) hHsource with
    hgen | ⟨D, i, t, hDerase, hacc, ht⟩
  · simpa only [H, hgen] using
      (Protocol.genesis_mem_and_stamp_storeBeforeTime S
        adm.toNamedScheduleWellFormed w (S.a (r + 1))
        (S.hc.Γ_neg1 S.E.Δ (r + 1)))
  · have hHpos : 0 < D.slot := by
      have hDpar : D.erase.parent.slot < D.erase.slot :=
        Protocol.parent_slot_lt_of_acceptsAt_block S hacc
      have hslotEq : D.erase.slot = D.slot := by cases D <;> rfl
      rw [hslotEq] at hDpar
      exact Nat.zero_lt_of_lt hDpar
    have hrelayRead : S.a r + S.E.Δ ≤ S.a (r + 1) :=
      le_trans (action_add_delta_le_next_Γ_neg1 S r)
        (le_of_lt (next_Γ_neg1_lt_action S r))
    have hFhist := GradeDeliveryRun.finalizedBelowAtDeliveries_of_active
      S adm hrelayRead hactive (by rw [hDerase]; exact hPH)
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

/-! ## Domain-grade persistence to a later strict read -/

/-- A named domain grade keeps its block in every later honest pre-time read.

The domain grade supplies raw-tree membership at the G2 domain. The named
tree then grows to the later action read; no domain-to-action filter transport
is assumed. -/
theorem namedGradeFormsAt_processedAtRead_of_action_le
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} {P : Block V}
    (hforms : NamedGradeFormsAt S rho q P)
    {reader : V} (hreader : reader ∈ rho.honest) {read : Time}
    (hle : S.a q ≤ read) :
    P ∈ (rho.storeBeforeTime S reader read).T := by
  have hsource : P ∈
      (rho.storeBeforeTime S reader
        (DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2)).T := by
    have hfiltered := (hforms reader hreader).1
    have htree := Proofs.Records.get_filtered_block_tree_subset _ hfiltered
    simpa only [PhaseGrades.filteredTree, Run.storeBeforeTime] using htree
  rw [storeBeforeTime_eq_storeAt_sub_one_recovery] at hsource ⊢
  apply StoreFinality.stateAt_T_subset
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed reader ?_ hsource
  exact Int.sub_le_sub_right
    ((FrameForward.domain_le_a S q .g2).trans hle) 1

/-- A retained action read is the filtered-tree activity required by the
named grade consumers. -/
theorem activeAtAction_of_retainedAtRead
    (S : Setup V) {rho : Run V} {v : V} {r : Round} {P : Block V}
    (hretained : P ∈ Protocol.get_filtered_block_tree
      (healStoreAt S rho v r).toFG) :
    P ∈ PhaseGrades.filteredTree (actionReadAt S rho v r) := by
  simpa only [healStoreAt, PhaseGrades.filteredTree, actionReadAt,
    Run.storeBeforeTime] using hretained

/-! ## The one-round persistence theorem -/


/-- A formed common grade persists as a clean common read in the next round as
soon as the same block remains active there. All transport and resolution
facts are consequences of the Section 7 run contract.

Statement change: as above, `GradeFormsAt` becomes `NamedGradeFormsAt`
plus the new `hownActive` premise, here quantified over every honest validator
(the loop the `CleanActionReadFor` obligation ranges over). -/
theorem cleanActionReadFor_of_namedGradeFormsAt_and_next_active
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} (hr : 0 < r) {P : Block V} (hforms : NamedGradeFormsAt S rho r P)
    (hpost : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hownActive : ∀ v ∈ rho.honest,
      P ∈ PhaseGrades.filteredTree (actionReadAt S rho v r))
    (hactive : ∀ w ∈ rho.honest,
      P ∈ Protocol.get_filtered_block_tree
        (healStoreAt S rho w (r + 1)).toFG)
    (hactive_domain : ∀ w ∈ rho.honest,
      P ∈ PhaseGrades.filteredTree (relativeG2Read S rho (r + 1) w)) :
    CleanActionReadFor S rho r P := by
  have hhor : S.a r ≤ rho.horizon :=
    le_trans (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos))
      (le_trans (action_add_delta_le_next_Γ_neg1 S r) hcut)
  refine ⟨hpost, hcut, hactive, hactive_domain, ?_⟩
  intro w hw v hv
  let H := actionSGBlockAt S rho v r
  have hvisible := actionSGBlockAt_visible_next_Γ_neg1_of_namedGradeFormsAt
    S adm hr hforms hv hw hpost hcut (hownActive v hv) (hactive w hw)
  obtain ⟨D, hDerase, hDrun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
      adm.toNamedScheduleWellFormed hw (S.a (r + 1)) hvisible.1
  have hfind : Block.find? (gradeViewAt S rho w (r + 1)).T H.root = some H := by
    apply Proofs.Optimistic.find?_eq_some_of_unique
    · simpa only [gradeViewAt, healStoreAt, Run.storeBeforeTime,
        Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hvisible.1
    · intro Y hY hroot
      have hYmem : Y ∈ (rho.storeBeforeTime S w (S.a (r + 1))).T := by
        simpa only [gradeViewAt, healStoreAt, Run.storeBeforeTime,
          Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hY
      obtain ⟨DY, hDYerase, hDYrun⟩ :=
        Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
          adm.toNamedScheduleWellFormed hw (S.a (r + 1)) hYmem
      have hrootN : DY.root = D.root := by
        rw [← Proofs.NamedWire.erase_root DY, ← Proofs.NamedWire.erase_root D,
          hDYerase, hDerase]
        exact hroot
      have heqN : DY = D :=
        adm.toNamedRootCollisionFree.root_injective DY D hDYrun hDrun DY D
          (Or.inl (Proofs.NamedAncestry.named_self DY))
          (Or.inr (Proofs.NamedAncestry.named_self D)) hrootN
      rw [← hDYerase, heqN]
      exact hDerase
  have hvote := actionSGVote_stamp_before_next_Γ_neg1
    S adm hv hw r hpost hcut
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
    exact occurrenceBefore_max hvote hblock
  · simp only [Protocol.head_covers, actionSGVoteAt, hfindAction]
    exact preceq_actionSGBlockAt_of_namedGradeFormsAt S adm.toNamedAdmissibleCore hr hhor
      hforms hv (hownActive v hv)



/-! ## A seeded post-cutoff suffix -/



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
