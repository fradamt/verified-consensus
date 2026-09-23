module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.PostGSTCarrierAdmissionCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Generic.FrontierCoverage
public import DecoupledConsensusProofs.Protocol.ChainState.Main
public import DecoupledConsensusInternal.Execution.Assumptions
public import DecoupledConsensusProofs.Protocol.Handlers.NamedStore
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge
public import DecoupledConsensusProofs.Protocol.ChainState.NjGap
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordFresh
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordTargetHistory
public import DecoupledConsensusProofs.Execution.EmissionShape
public import DecoupledConsensusProofs.Protocol.ChainState.NamedNjGap
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecoveryTimeout
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Generic.RecoveryConcentration
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.StoreFinalityConsequences
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Execution.Wire

@[expose] public section

/-!
# A common recovery grade drives actual Goldfish vote duties

`GradeFormsAt` is a snapshot at the round action. It does not by itself say
what an earlier or later Goldfish vote duty read. The source-carrying input is
`CleanActionReadFor`: every honest preceding action carrier resolves before
the next round's earliest grade cutoff and covers one common block.

This file carries those exact votes and blocks to an honest next-round vote
duty. If the common block is still in that duty's filtered tree, the duty has
an active grade 2. The grade-2 block forces a fresh SG anchor, so the actual
Section 7 `get_head` output and emitted Goldfish vote stay in the common cone.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

-- moved from DecoupledConsensusProofs/HealingSurface/FrozenHeadFloorRun.lean (C1)

/-- Every vote duty in round `r` occurs after that round's opening instant. -/
theorem Γ_0_le_vote_time_of_round_eq
    (S : Setup V) {r : Round} {s : Slot}
    (hround : S.hc.round_of s = r) :
    S.hc.Γ_0 S.E.Δ r ≤ Protocol.vote_time S.E s := by
  have hopen : S.hc.opening_slot r ≤ s := by
    unfold Protocol.HealConfig.round_of at hround
    unfold Protocol.HealConfig.opening_slot
    rw [← hround]
    exact Nat.div_mul_le_self s S.hc.R
  rw [Protocol.Γ_0_eq_proposal_time]
  exact (Protocol.proposal_time_mono S.E hopen).trans
    (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos))

/-! ## Carrier order and transport to a vote duty -/

/-- A clean action read orients every exact preceding action carrier above its
common block. Root collision freedom identifies the block resolved at the
reader with the carrier emitted by the source action. -/
theorem cleanActionRead_preceq_actionSGBlockAt
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {Q : Block V} (hclean : CleanActionReadFor S rho r Q)
    {w v : V} (hw : w ∈ rho.honest) (hv : v ∈ rho.honest) :
    Block.Preceq Q (actionSGBlockAt S rho v r) := by
  let C := actionSGBlockAt S rho v r
  have hcov := (hclean.resolved_support w hw v hv).2
  simp only [Protocol.head_covers, actionSGVoteAt] at hcov
  cases hfind : Block.find? (gradeViewAt S rho w (r + 1)).T C.root with
  | none =>
      rw [hfind] at hcov
      cases hcov
  | some X =>
      rw [hfind] at hcov
      have hXmem : X ∈
          (rho.storeBeforeTime S w (S.a (r + 1))).T := by
        simpa only [gradeViewAt, healStoreAt, Run.storeBeforeTime,
          Protocol.HealingStore.gradeView, Protocol.Store.toHealing] using
          (find?_mem hfind)
      have hCmem : C ∈ (rho.storeBeforeTime S v (S.a r)).T := by
        simpa only [C] using actionSGBlockAt_mem_storeBeforeTime S rho v r
      have hroot : X.root = C.root := find?_root hfind
      obtain ⟨Xn, hXn, hXrun⟩ :=
        Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hw
          (S.a (r + 1)) hXmem
      obtain ⟨Cn, hCn, hCrun⟩ :=
        Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv
          (S.a r) hCmem
      have hrootN : Xn.root = Cn.root := by
        rw [← Proofs.NamedWire.erase_root Xn, ← Proofs.NamedWire.erase_root Cn,
          hXn, hCn, hroot]
      have hXC : Xn = Cn :=
        adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
          Xn Cn hXrun hCrun Xn Cn
          (Or.inl (Proofs.NamedAncestry.named_self Xn))
          (Or.inr (Proofs.NamedAncestry.named_self Cn)) hrootN
      have hXCerase : X = C := by
        calc
          X = Xn.erase := hXn.symm
          _ = Cn.erase := congrArg NamedBlock.erase hXC
          _ = C := hCn
      change Block.Preceq Q C
      rw [hXCerase] at hcov
      exact hcov



/-! ## Timely projected votes and the duty-local grade -/

/-- Every exact preceding action vote is present and stamped before
`Gamma[-1]` in an honest next-round vote duty read at or after `Gamma[0]`. -/
theorem actionSGVote_mem_stamp_voteDuty
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {s : Slot}
    (hpost : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hread : S.hc.Γ_0 S.E.Δ (r + 1) ≤ Protocol.vote_time S.E s)
    {w v : V} (hw : w ∈ rho.honest) (hv : v ∈ rho.honest) :
    actionSGVoteAt S rho v r ∈
        (Proofs.Optimistic.voteDutyStore S rho w s).toHealing.sg_votes r ∧
      occurrenceBefore
        ((Proofs.Optimistic.voteDutyStore S rho w s).timestamp_sg_vote
          (actionSGVoteAt S rho v r))
        (S.hc.Γ_neg1 S.E.Δ (r + 1)) = true := by
  have hdeadline : S.a r + S.E.Δ ≤ rho.horizon :=
    (action_add_delta_le_next_Γ_neg1 S r).trans hcut
  obtain ⟨j, e, hj, heDelta, hrow⟩ :=
    actionAttestationAt_rows_before_delta S adm hv hw r hpost hdeadline
  obtain ⟨-, haRound, -⟩ := actionAttestationAt_shape S rho v r
  have ha' : actionAttestationAt S rho v r ∈
      (rho.stateBefore S (j + 1) w).st.sg_rows
        (actionAttestationAt S rho v r).round := by
    rw [haRound]
    exact hrow
  have heCut : e.time < S.hc.Γ_neg1 S.E.Δ (r + 1) :=
    lt_of_lt_of_le heDelta (action_add_delta_le_next_Γ_neg1 S r)
  have hut := GradeDeliveryRun.timestamp_sg_vote_before_of_mem_post_event
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hj ha' heCut
  rw [sgVote_actionAttestationAt] at hut
  have hu : actionSGVoteAt S rho v r ∈
      (rho.stateBefore S (j + 1) w).st.toHealing.sg_votes r := by
    have hpool := NamedAdmission.pool_view_mem (rho.stateBefore S (j + 1) w).st
      (Proofs.NamedRuntime.stateBefore_invariants S rho (j + 1) w).1.1.1.2.2.2.1 _ ha'
    rw [haRound] at hpool
    have himg := Finset.mem_image_of_mem Protocol.sgVote hpool
    rw [sgVote_actionAttestationAt] at himg
    exact himg
  have hcutRead : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤
      Protocol.vote_time S.E s :=
    (le_of_lt (Proofs.HealingLemmas.Γ_neg1_lt_Γ_0
      S.hc S.E.Δ_pos (r + 1))).trans hread
  have hpostRead := GradeDeliveryRun.projected_vote_mem_stamp_at_read
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hj heCut hcutRead hu hut
  simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
    Proofs.Optimistic.tickStore] using hpostRead



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
