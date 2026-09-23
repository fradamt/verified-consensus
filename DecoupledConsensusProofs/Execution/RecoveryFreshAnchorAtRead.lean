module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryFreshGradeProvenance

@[expose] public section

/-!
# A next-round fresh anchor at an arbitrary read

After `Gamma⁻¹ (q + 1)`, every honest reader has the exact round-`q` action
vote in its next-round grade batch. Since the honest slice has cardinality at
most one, direct grade-1 support identifies the supporting vote with one
honest round-`q` action carrier. This transports the action-carrier ceiling to
the fresh anchor at any such read, not only at the next action itself.

The lower timing bound is essential. Before it, a reader can use a round-`q`
store whose round-`q` fresh anchor is graded from the `q - 1` batch; the
round-`q` action-carrier ceiling gives no information about that anchor.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Every fresh round-`(q + 1)` anchor selected at an honest pre-time read
starting at `Gamma⁻¹ (q + 1)` is below any common upper endpoint of the honest
round-`q` action carriers. -/
theorem freshAnchor_preceq_of_previousActionCarriersPreceq_at_read
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {q : Round} (hpost : S.E.t_GST ≤ S.a q)
    (hcut : S.hc.Γ_neg1 S.E.Δ (q + 1) ≤ rho.horizon)
    {B : Block V}
    (hupper : ∀ v ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho v q) B)
    {w : V} (hw : w ∈ rho.honest) {t : Time}
    (ht : S.hc.Γ_neg1 S.E.Δ (q + 1) ≤ t) {A : Block V}
    (hA : Protocol.fresh_anchor S.E S.hc
      (rho.storeBeforeTime S w t).toHealing (q + 1) = some A) :
    Block.Preceq A B := by
  let st := rho.storeBeforeTime S w t
  have hAmem : A ∈
      (Protocol.get_filtered_block_tree st.toHealing.toFG).filter
        (fun C => Protocol.G1 S.E st.toHealing.gradeView
          S.hc (q + 1) C = true) := by
    simpa only [Protocol.fresh_anchor] using (Proofs.Engine.deepest?_mem hA)
  have hG1 : Protocol.G1 S.E st.toHealing.gradeView S.hc (q + 1) A = true :=
    (Finset.mem_filter.mp hAmem).2
  obtain ⟨v, hv, u, hu, head, huHead, hfind, hheadMem, hBhead, -⟩ :=
    G1_honest_named_supporter S.E hfb hG1
  have hdeadline : S.a q + S.E.Δ ≤ rho.horizon :=
    (action_add_delta_le_next_Γ_neg1 S q).trans hcut
  obtain ⟨j, e, hj, hjt, hpool⟩ :=
    actionSGVote_pooled_before_delta S adm hv hw q hpost hdeadline
  have hread : e.time < t :=
    lt_of_lt_of_le hjt ((action_add_delta_le_next_Γ_neg1 S q).trans ht)
  have hactionPool := Protocol.sgVote_mem_stateBeforeTime_of_post
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hj hread hpool
  have hactionBatch : actionSGVoteAt S rho v q ∈
      Protocol.sg_votes_by
        (Protocol.round_batch st.toHealing.gradeView (q + 1)) v := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · simpa only [st, Protocol.round_batch, Nat.succ_ne_zero q,
        Nat.add_sub_cancel, Run.storeBeforeTime,
        Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hactionPool
    · exact (actionSGVoteAt_shape S rho v q).1
  have hcard :
      (Protocol.sg_votes_by
        (Protocol.round_batch st.toHealing.gradeView (q + 1)) v).card ≤ 1 := by
    simpa only [st, Run.storeBeforeTime, Protocol.HealingStore.gradeView,
      Protocol.Store.toHealing] using
      (Protocol.roundBatch_card_le_one_stateBeforeTime
        S adm (t := t) (w := w) (r := q + 1) (v := v) hv)
  have huEq : u = actionSGVoteAt S rho v q :=
    Finset.card_le_one.mp hcard u hu
      (actionSGVoteAt S rho v q) hactionBatch
  let C := actionSGBlockAt S rho v q
  have hheadRoot : head.root = C.root := by
    have hconfirmed : (actionSGVoteAt S rho v q).confirmed = some head.root := by
      simpa only [huEq] using huHead
    simpa only [actionSGVoteAt, C, Option.some.injEq] using hconfirmed.symm
  have hheadMem' : head ∈ (rho.storeBeforeTime S w t).T := by
    simpa only [st, Run.storeBeforeTime, Protocol.HealingStore.gradeView,
      Protocol.Store.toHealing] using hheadMem
  obtain ⟨headNamed, hheadNamed, hheadRun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hw t hheadMem'
  have hCmem : C ∈ (rho.storeBeforeTime S v (S.a q)).T := by
    simpa only [C] using actionSGBlockAt_mem_storeBeforeTime S rho v q
  obtain ⟨CNamed, hCNamed, hCRun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv (S.a q) hCmem
  have hheadRootNamed : headNamed.root = CNamed.root := by
    rw [← Proofs.NamedWire.erase_root headNamed, ← Proofs.NamedWire.erase_root CNamed,
      hheadNamed, hCNamed]
    exact hheadRoot
  have hheadEqNamed : headNamed = CNamed :=
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      headNamed CNamed hheadRun hCRun headNamed CNamed
      (Or.inl (Proofs.NamedAncestry.named_self headNamed))
      (Or.inr (Proofs.NamedAncestry.named_self CNamed)) hheadRootNamed
  have hheadEq : head = C := by
    calc
      head = headNamed.erase := hheadNamed.symm
      _ = CNamed.erase := congrArg NamedBlock.erase hheadEqNamed
      _ = C := hCNamed
  have hAC : Block.Preceq A C := by
    simpa only [hheadEq] using hBhead
  exact Block.preceq_trans hAC (hupper v hv)

#print axioms freshAnchor_preceq_of_previousActionCarriersPreceq_at_read

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
