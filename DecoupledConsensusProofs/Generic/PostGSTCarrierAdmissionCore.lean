module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.CarrierAdmissionCore
public import DecoupledConsensusProofs.Execution.ExcludesRefute
public import DecoupledConsensusProofs.Protocol.Handlers.BlockAdmission
public import DecoupledConsensusProofs.Protocol.Handlers.HonestProposalAdmission
public import DecoupledConsensusProofs.Protocol.ValidatorClient.BlockEmission

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Post-GST accepted-block admission

This module contains the fixed-cutoff accepted-block relay. The receiver's
finalized-ancestor history remains an explicit local premise.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A post-GST accepted block reaches an honest target early enough to be
admitted before the output cutoff. The target's finalized-ancestor guard is
the only receiver-local premise. -/
theorem block_admittedBefore_of_accepted_after_cutoff_core
    (S : Setup V) {rho : Run V} (adm : Proofs.AdmissibleCore S rho)
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
      max t S.E.t_GST + S.E.Δ ≤ GammaIn + S.E.Δ :=
        by simpa only [add_comm] using add_le_add_right hmax S.E.Δ
      _ = GammaOut := hhop
  have hrelayHorizon : max t S.E.t_GST + S.E.Δ ≤ rho.horizon :=
    le_trans hrelayCutoff hhor
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
            (Proofs.Optimistic.key_le_of_index_lt S adm.toNamedScheduleWellFormed hlt he' he)
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
      rw [Proofs.stateBeforeTime_eq_stateBefore_filter_length S rho
        adm.toNamedScheduleWellFormed.sorted]
      exact hFhist _ (Proofs.strict_filter_length_mono rho hrelayCutoff)
    have hguard := Proofs.not_excludes_of_F_preceq_later_time S rho
      adm.toNamedScheduleWellFormed.sorted le_rfl hFdeadline
    obtain ⟨t', htt', ht'hi, j, hproc⟩ := adm.relay_block p hp i B t hacc
      w hw halreadyFalse hrelayHorizon hguard
    have ht'cutoff : t' < GammaOut := lt_of_lt_of_le ht'hi hrelayCutoff
    obtain ⟨hidx, e, hej, heNode, heTime⟩ := hproc
    rcases hidx with ⟨ttick, htick, hmem⟩ | ⟨tdeliv, hdeliv⟩
    · have heTickEq : e = Event.tick w ttick := Option.some.inj (hej.symm.trans htick)
      have httickEq : ttick = t' := by
        rw [heTickEq] at heTime
        exact heTime
      rw [httickEq] at htick hmem
      have hemit : Run.emits S rho w (Object.block B) t' := ⟨j, htick, hmem⟩
      have hshape := Proofs.HealingSurface.emits_block_shape S rho hemit
      have hwProp : S.E.proposer B.slot ∈ rho.honest := by
        rw [hshape.2.2]
        exact hw
      have ht'hor : t' ≤ rho.horizon :=
        (adm.in_horizon _ (List.mem_of_getElem? htick)).2
      have hproposalHor : Protocol.proposal_time S.E B.slot ≤ rho.horizon := by
        rw [← hshape.2.1]
        exact ht'hor
      obtain ⟨B', hB'⟩ := DecoupledConsensusModel.Proofs.HealingSurface.proposedBlockAt_isSome S rho B.slot
      have htick2 := Proofs.Optimistic.proposalTick S adm.toNamedScheduleWellFormed B.slot hBpos
        hwProp hproposalHor hB'
      rw [hshape.2.2] at htick2
      obtain ⟨hB'slot, hemit'⟩ := htick2
      have hBB' : B = B' :=
        Proofs.HealingSurface.emits_block_unique S adm.toNamedScheduleWellFormed
          hemit hemit' hB'slot.symm
      have hBproposed : Statements.Instantiation.proposedBlockAt S rho B.slot = some B :=
        hB'.trans (congrArg some hBB'.symm)
      obtain ⟨jP, hself⟩ := acceptsAt_proposedBlock_core S adm hBpos
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
        have h := Proofs.NamedSlotFreshness.proposal_time_le_of_acceptsAt_block S adm hacc
        rw [Proofs.NamedWire.erase_slot] at h
        exact le_trans h htt'
      have hslot : ¬ (rho.stateBefore S j w).st.core.s < B.erase.slot :=
        not_future_of_delivery_after_proposal_core S adm hw hdeliv
          (by rw [Proofs.NamedWire.erase_slot]; exact hproposalLe)
      have hjBound := Proofs.index_succ_le_strict_filter_length rho
        adm.toNamedScheduleWellFormed.sorted GammaOut hdeliv
        (by simpa only [Event.time] using ht'cutoff)
      have haccept := acceptsAt_block_of_delivery_guards_core S adm hdeliv
        hslot (hFhist j (Nat.le_trans (Nat.le_succ j) hjBound))
        (proposer_eq_of_acceptsAt_block S hacc)
        (parent_slot_lt_of_acceptsAt_block S hacc)
        (carried_attestations_admissible_of_acceptsAt_block S hacc)
      exact ⟨B, rfl, j, t', haccept, ht'cutoff⟩

theorem block_admittedBefore_of_accepted_after_cutoff
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {p w : V} (hp : p ∈ rho.honest) (hw : w ∈ rho.honest)
    {i : Nat} {B : NamedBlock V} {t GammaIn GammaOut : Time}
    (hBpos : 0 < B.slot)
    (hacc : NamedRun.acceptsAt S rho i p (Object.block B) t)
    (htIn : t < GammaIn) (hgst : S.E.t_GST ≤ GammaIn)
    (hhop : GammaIn + S.E.Δ = GammaOut)
    (hhor : GammaOut ≤ rho.horizon)
    (hFhist : BlockFinalizedBelowAtDeliveriesBefore
      S rho w B GammaOut) :
    AdmittedBefore S rho w B.erase GammaOut :=
  block_admittedBefore_of_accepted_after_cutoff_core
    S adm.toNamedAdmissibleCore hp hw hBpos hacc htIn hgst hhop hhor hFhist

end Protocol
end DecoupledConsensusModel

end
