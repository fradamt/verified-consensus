module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.RecoveryConcentration

@[expose] public section

/-!
# Honest provenance of a fresh recovery grade

A grade-1 block has direct absolute-majority support from the preceding
round's SG votes. Below one-third faults, that support contains an honest
validator. After GST, authenticity and the one-vote-per-round rule identify
the supporting vote with that validator's exact Section 7 action carrier.

This is the fresh-anchor counterpart of the grade-2 provenance edge used by
the pre-confirmation height-cap proof.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Pure direct-support provenance -/

/-- A grade-1 block has an honest preceding-round SG vote whose named and
resolved head descends from it.

`G1_honest_supporter` supplies the same honest-support fact, but its public
conclusion does not retain the equality between the returned vote root and the
returned resolved head. The run-level collision-free-root bridge needs that
equality, so this focused elimination form retains it. -/
theorem G1_honest_named_supporter
    (E : Env V) {gv : Protocol.GradeView V} {hc : Protocol.HealConfig}
    {Hon : Finset V} {r : Round} {B : Block V}
    (hfb : 3 * E.electorate.weightOf (Finset.univ \ Hon) < E.W)
    (hG1 : Protocol.G1 E gv hc r B = true) :
    ∃ v ∈ Hon, ∃ u ∈ Protocol.sg_votes_by (Protocol.round_batch gv r) v,
      ∃ head : Block V,
        u.confirmed = some head.root ∧
          Block.find? gv.T head.root = some head ∧
          head ∈ gv.T ∧ Block.Preceq B head ∧
          occurrenceBefore (Protocol.summary gv r v).t_v
            (hc.Γ_0 E.Δ r) = true := by
  simp only [Protocol.G1, decide_eq_true_eq] at hG1
  obtain ⟨v, hv, ht, hcov⟩ :=
    exists_honest_direct_supporter E hfb hG1
  obtain ⟨root, head, hsummary, hfind, hmem, hBhead⟩ :=
    exists_head_of_head_covers hcov
  have hheadRoot : head.root = root := find?_root hfind
  rcases Proofs.Optimistic.summary_C_v_mem gv r v with
    hnone | ⟨u, hu, hsummaryVote⟩
  · rw [hnone] at hsummary
    exact absurd hsummary (by simp)
  · refine ⟨v, hv, u, hu, head, ?_, ?_, hmem, hBhead, ht⟩
    · exact hsummaryVote.symm.trans
        (hsummary.trans (congrArg some hheadRoot.symm))
    · rw [hheadRoot]
      exact hfind

/-! ## Run-level identification with the exact previous action -/


/-- Every post-GST grade-1 block at round `k + 1` is below one honest
validator's exact round-`k` Section 7 SG action carrier.

The honest direct-support witness can be any vote in the reader's batch.
Post-GST broadcast also puts the exact action vote in that batch slice, and
honest authenticity limits the slice to one vote. Collision-free run roots
then identify the witness head with `actionSGBlockAt` itself. -/
theorem G1_preceq_honestPreviousActionCarrier
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {w : V} (hw : w ∈ rho.honest) (k : Round)
    (hpost : S.E.t_GST ≤ S.a k)
    (hcut : S.hc.Γ_neg1 S.E.Δ (k + 1) ≤ rho.horizon)
    {B : Block V}
    (hG1 : Protocol.G1 S.E (gradeViewAt S rho w (k + 1))
      S.hc (k + 1) B = true) :
    ∃ v ∈ rho.honest, Block.Preceq B (actionSGBlockAt S rho v k) := by
  obtain ⟨v, hv, u, hu, head, huHead, hfind, hheadMem, hBhead, -⟩ :=
    G1_honest_named_supporter S.E hfb hG1
  have hactionMem : actionSGVoteAt S rho v k ∈
      Protocol.sg_votes_by
        (Protocol.round_batch (gradeViewAt S rho w (k + 1)) (k + 1)) v :=
    actionSGVote_mem_next_round_batch S adm hv hw k hpost hcut
  have hcard :
      (Protocol.sg_votes_by
        (Protocol.round_batch (gradeViewAt S rho w (k + 1)) (k + 1)) v).card
          ≤ 1 := by
    simpa only [gradeViewAt, healStoreAt, Run.storeBeforeTime,
      Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using
      (Protocol.roundBatch_card_le_one_stateBeforeTime
        S adm (t := S.a (k + 1)) (w := w) (r := k + 1) hv)
  have huEq : u = actionSGVoteAt S rho v k :=
    Finset.card_le_one.mp hcard u hu (actionSGVoteAt S rho v k) hactionMem
  let C := actionSGBlockAt S rho v k
  have hheadRoot : head.root = C.root := by
    have hconfirmed : (actionSGVoteAt S rho v k).confirmed = some head.root := by
      simpa only [huEq] using huHead
    simpa only [actionSGVoteAt, C, Option.some.injEq] using hconfirmed.symm
  have hheadMem' : head ∈ (rho.storeBeforeTime S w (S.a (k + 1))).T := by
    simpa only [gradeViewAt, healStoreAt, Run.storeBeforeTime,
      Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using hheadMem
  obtain ⟨headNamed, hheadNamed, hheadRun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hw (S.a (k + 1)) hheadMem'
  have hCmem : C ∈ (rho.storeBeforeTime S v (S.a k)).T := by
    simpa only [C] using actionSGBlockAt_mem_storeBeforeTime S rho v k
  obtain ⟨CNamed, hCNamed, hCRun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv (S.a k) hCmem
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
  exact ⟨v, hv, by simpa only [C, hheadEq] using hBhead⟩

end HealingSurface
end Proofs
end DecoupledConsensusModel

#print axioms DecoupledConsensusModel.Proofs.HealingSurface.G1_honest_named_supporter
#print axioms
  DecoupledConsensusModel.Proofs.HealingSurface.G1_preceq_honestPreviousActionCarrier

end
