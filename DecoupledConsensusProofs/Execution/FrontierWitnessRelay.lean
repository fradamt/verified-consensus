module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.ExcludesRefute
public import DecoupledConsensusProofs.Generic.PostGSTCarrierAdmissionCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Generic.PostGSTCarrierAdmission
public import DecoupledConsensusProofs.Execution.ProgressCanonicality
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ReaderLocalCone
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.RecoveryVoteCone
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsBridge
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusProofs.Protocol.Duties.Proposals.RecoverySourceProgress
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradeBootstrapCore
public import DecoupledConsensusProofs.Execution.BodyRetention

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Relay of an honest frontier witness

This module joins the quorum-backed height frontier to the reader-local cone
witness used by recovery fork choice.

The height pair does not carry the block that supplied its derived height.
Instead, an honest signer already has one processed source block in its action
store. Accepted-block relay transports that block to a later honest reader.
In the reverse root branch `get_fg_root ⪯ P`, the reader's finalized root is
below `P`, so every delivery of a source descendant `W` passes the finality
guard. Derived-state agreement then preserves the source height at the reader.

One full network delay is necessary for this transport. A certificate can be
observed before the signer's source block has reached the reader, so the mere
strict inequality between emission and read times is not sufficient.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]







/-! ## The honest signer's local witness -/


private theorem named_acceptsAt_after_cutoff
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {p w : V} (hp : p ∈ rho.honest) (hw : w ∈ rho.honest)
    {i : Nat} {B : NamedBlock V} {t GammaIn GammaOut : Time}
    (hBpos : 0 < B.slot)
    (hacc : NamedRun.acceptsAt S rho i p (.block B) t)
    (htIn : t < GammaIn) (hgst : S.E.t_GST ≤ GammaIn)
    (hhop : GammaIn + S.E.Δ = GammaOut)
    (hhor : GammaOut ≤ rho.horizon)
    (hFhist : Protocol.BlockFinalizedBelowAtDeliveriesBefore
      S rho w B GammaOut) :
    ∃ j : Nat, ∃ t' : Time,
      NamedRun.acceptsAt S rho j w (.block B) t' ∧ t' < GammaOut := by
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
    le_trans hrelayCutoff hhor
  by_cases halready : NamedReceipt.processed
      (rho.stateBefore S (i + 1) w).st (.block B) = true
  · rcases Protocol.acceptsAt_block_of_processed S rho w (i + 1) B halready with
      hgen | ⟨j, hj, t', hacc'⟩
    · exact False.elim ((Nat.ne_of_gt hBpos) (by rw [hgen]; rfl))
    · obtain ⟨-, e', he', -, ht'⟩ := hacc'.1
      obtain ⟨-, e, he, -, ht⟩ := hacc.1
      have ht'le : t' ≤ t := by
        rw [← ht', ← ht]
        have hji : j ≤ i := Nat.le_of_lt_succ hj
        rcases hji.lt_or_eq with hlt | rfl
        · exact Proofs.Bridges.time_le_of_key_le
            (Proofs.Optimistic.key_le_of_index_lt S
              adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hlt he' he)
        · have heq : e' = e := Option.some.inj (he'.symm.trans he)
          rw [heq]
      exact ⟨j, t', hacc', lt_of_le_of_lt ht'le hacceptCutoff⟩
  · have halreadyFalse : NamedReceipt.processed
        (rho.stateBefore S (i + 1) w).st (.block B) = false :=
      Bool.eq_false_of_not_eq_true halready
    have hFdeadline : Block.Preceq
        (rho.stateBeforeTime S (max t S.E.t_GST + S.E.Δ) w).st.core.F B.erase := by
      change Block.Preceq
        (NamedRun.stateBeforeTime S rho (max t S.E.t_GST + S.E.Δ) w).st.core.F B.erase
      have hFgamma : Block.Preceq
          (NamedRun.stateBeforeTime S rho GammaOut w).st.core.F B.erase := by
        rw [stateBeforeTime_eq_stateBefore_filter_length S rho
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted]
        exact hFhist _ le_rfl
      have hFtime := stateBeforeTime_F_mono_of_le S rho
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted
        (w := w) hrelayCutoff
      exact Block.preceq_trans hFtime hFgamma
    have hguard := not_excludes_of_F_preceq_later_time S rho
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted le_rfl hFdeadline
    obtain ⟨t', htt', ht'hi, j, hproc⟩ :=
      adm.toNamedAdmissibleCore.toNamedSynchrony.relay_block p hp i B t hacc
        w hw halreadyFalse hrelayHorizon hguard
    have ht'cutoff : t' < GammaOut := lt_of_lt_of_le ht'hi hrelayCutoff
    obtain ⟨hidx, e, hej, _, heTime⟩ := hproc
    rcases hidx with ⟨ttick, htick, hmem⟩ | ⟨tdeliv, hdeliv⟩
    · have heTickEq : e = Event.tick w ttick := Option.some.inj (hej.symm.trans htick)
      have httickEq : ttick = t' := by
        rw [heTickEq] at heTime
        exact heTime
      rw [httickEq] at htick hmem
      have hemit : NamedRun.emits S rho w (.block B) t' := ⟨j, htick, hmem⟩
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
      have htick2 := Proofs.Optimistic.proposalTick S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed B.slot hBpos
        hwProp hproposalHor hB'
      rw [hshape.2.2] at htick2
      obtain ⟨hB'slot, hemit'⟩ := htick2
      have hBB' : B = B' := Proofs.HealingSurface.emits_block_unique S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hemit hemit'
          hB'slot.symm
      have hBproposed : Statements.Instantiation.proposedBlockAt S rho B.slot = some B :=
        hB'.trans (congrArg some hBB'.symm)
      obtain ⟨jP, hself⟩ := Protocol.acceptsAt_proposedBlock S adm hBpos
        hwProp hproposalHor hBproposed
      rw [hshape.2.2] at hself
      refine ⟨jP, Protocol.proposal_time S.E B.slot, hself, ?_⟩
      rw [← hshape.2.1]
      exact ht'cutoff
    · have heDelivEq : e = Event.deliver w (.block B) tdeliv :=
        Option.some.inj (hej.symm.trans hdeliv)
      have htdelivEq : tdeliv = t' := by
        rw [heDelivEq] at heTime
        exact heTime
      rw [htdelivEq] at hdeliv
      have hproposalLe : Protocol.proposal_time S.E B.slot ≤ t' := by
        have h := Protocol.proposal_time_le_of_acceptsAt_block S adm hacc
        rw [Proofs.NamedWire.erase_slot] at h
        exact le_trans h htt'
      have hslot : ¬ (rho.stateBefore S j w).st.core.s < B.erase.slot :=
        Protocol.not_future_of_delivery_after_proposal S adm hw hdeliv
          (by rw [Proofs.NamedWire.erase_slot]; exact hproposalLe)
      have hjBound := index_succ_le_strict_filter_length rho
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted GammaOut
        hdeliv (by simpa only [heDelivEq] using ht'cutoff)
      have haccept := Protocol.acceptsAt_block_of_delivery_guards S adm hdeliv
        hslot (hFhist j (Nat.le_trans (Nat.le_succ j) hjBound))
        (Protocol.proposer_eq_of_acceptsAt_block S hacc)
        (Protocol.parent_slot_lt_of_acceptsAt_block S hacc)
        (Protocol.carried_attestations_admissible_of_acceptsAt_block S hacc)
      exact ⟨j, t', haccept, ht'cutoff⟩

/-! ## Transport to a later reader -/

/-- A processed action-store descendant of `P` reaches a later honest reader
after one network delay in the reverse FG-root branch.

The result also transports its derived height. This is the block-level join
that a caller can use for any height pair, independently of how the pair was
found. -/
theorem actionConeWitness_visibleAtReader_after_gst
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {p w : V} (hp : p ∈ rho.honest) (hw : w ∈ rho.honest)
    {P : Block V} {D : NamedBlock V} {h : Height} {read : Time}
    (hDT : D ∈ (actionStoreAt S rho p r).st.bodies)
    (hPD : Block.Preceq P D.erase)
    (hheight : h ≤ (Protocol.derive_named S.E S.cfg D).h)
    (hpost : S.E.t_GST ≤ S.a r)
    (hdelay : S.a r + S.E.Δ ≤ read)
    (hreadHor : read ≤ rho.horizon)
    (hrootP : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w read).toHealing.toFG) P) :
    D ∈ (rho.storeBeforeTime S w read).bodies ∧
      Block.Preceq P D.erase ∧
        h ≤ (Protocol.derive_named S.E S.cfg D).h := by
  let source := actionStoreAt S rho p r
  let target := rho.storeBeforeTime S w read
  let pre := rho.storeBeforeTime S p (S.a r)
  have hDpre : D ∈ (rho.storeBeforeTime S p (S.a r)).bodies := by
    simpa only [source, actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hDT
  obtain ⟨n, hn, hbefore⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted (S.a r)
  have hD_n : D ∈ (rho.stateBefore S n p).st.bodies := by
    have hstate : NamedRun.stateBeforeTime S rho (S.a r) p =
        NamedRun.stateBefore S rho n p := congrFun hn p
    change D ∈ (NamedRun.stateBeforeTime S rho (S.a r) p).st.bodies at hDpre
    rw [hstate] at hDpre
    exact hDpre
  have hprocessed : Object.processed
      (rho.stateBefore S n p).st (.block D) = true := by
    simpa only [Object.processed, NamedReceipt.processed, decide_eq_true_eq] using hD_n
  rcases Protocol.acceptsAt_block_of_processed S rho p n D hprocessed with
    hgen | ⟨i, hi, t, hacc⟩
  · subst D
    have hcohTarget : Proofs.NamedStore.Coherent S.E S.cfg target :=
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho read w).1.1.1
    exact ⟨hcohTarget.2.2.1.1, hPD, hheight⟩
  · obtain ⟨-, e, he, -, het⟩ := hacc.1
    have htIn : t < S.a r := by
      simpa only [het] using hbefore i e hi he
    have hDpos : 0 < D.slot := by
      have hparent := Protocol.parent_slot_lt_of_acceptsAt_block S hacc
      have hslot : D.erase.slot = D.slot := by cases D <;> rfl
      rw [hslot] at hparent
      exact Nat.zero_lt_of_lt hparent
    have hdeadlineHor : S.a r + S.E.Δ ≤ rho.horizon := hdelay.trans hreadHor
    have hFhist : Protocol.BlockFinalizedBelowAtDeliveriesBefore
        S rho w D (S.a r + S.E.Δ) := by
      intro j hj
      have hFj := stateBefore_F_preceq_stateBeforeTime_of_prefix S rho
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted (w := w)
        (d := S.a r + S.E.Δ) hj
      have hFGread := stateBeforeTime_F_mono_of_le S rho
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted
        (w := w) hdelay
      have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        S rho read w
      have hFroot := Proofs.Records.preceq_get_fg_root_of_F
        (st := (rho.storeBeforeTime S w read).toHealing.toFG) hFJ
      exact Block.preceq_trans hFj
        (Block.preceq_trans hFGread
          (Block.preceq_trans hFroot (Block.preceq_trans hrootP hPD)))
    obtain ⟨j, t', hacc', ht'⟩ := named_acceptsAt_after_cutoff S adm hp hw
      hDpos hacc htIn hpost rfl hdeadlineHor hFhist
    have hDtarget : D ∈ target.bodies := by
      let n' := (rho.events.filter (fun e => decide (e.time < read))).length
      have hn' : NamedRun.stateBeforeTime S rho read =
          NamedRun.stateBefore S rho n' :=
        Proofs.Optimistic.stateBeforeTime_eq_take S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed read
      obtain ⟨-, e', he', -, he't⟩ := hacc'.1
      have htRead : e'.time < read := by
        rw [he't]
        exact lt_of_lt_of_le ht' hdelay
      have hjN : j < n' := by
        by_contra hnot
        have hnj : n' ≤ j := Nat.le_of_not_gt hnot
        have hle := Proofs.Optimistic.le_time_of_index_ge S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
          (t := read) (j := j) (e := e') hnj he'
        exact (not_le_of_gt htRead) hle
      have hbodyJ : D ∈ (rho.stateBefore S (j + 1) w).st.bodies := by
        simpa only [Object.processed, NamedReceipt.processed, decide_eq_true_eq] using
          hacc'.2.2
      have hbodyN := NamedBodyRetention.stateBefore_bodies_mono S rho w
        (Nat.succ_le_of_lt hjN) hbodyJ
      have hstate := congrFun hn' w
      change D ∈ (NamedRun.stateBeforeTime S rho read w).st.bodies
      rw [hstate]
      exact hbodyN
    exact ⟨hDtarget, hPD, hheight⟩

/-! ## The complete frontier-to-reader join -/



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
