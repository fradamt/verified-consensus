module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.FGSafetyFrozenSourceNamed
public import DecoupledConsensusProofs.Execution.PreparedReadBridge

@[expose] public section

/-!
# Prepared frozen-candidate paths from the preceding honest head

The prepared read keeps named derivation heights throughout. A lower
ancestor of an honest previous head is either viable in the prepared frozen
tree or is below that read's FG root.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.NamedRecoveryRead
open Protocol Proofs.Optimistic Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

private theorem frozenHead_vote_add_delta_le_nextVote
    (E : Env V) (s : Slot) :
    Protocol.vote_time E s + E.Δ ≤ Protocol.vote_time E (s + 1) := by
  unfold Protocol.vote_time Env.t slotStart
  push_cast
  have hd := E.Δ_pos
  calc
    _ = 4 * E.Δ * (s : Int) + 2 * E.Δ := by ring
    _ ≤ 4 * E.Δ * (s : Int) + 5 * E.Δ :=
      Int.add_le_add_left
        (Int.mul_le_mul_of_nonneg_right (show (2 : Int) ≤ 5 by decide) hd.le) _
    _ = _ := by ring

private theorem frozenHead_runBlock_of_read_body
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {read : Time} {D : NamedBlock V}
    (hD : D ∈ (rho.storeBeforeTime S v read).bodies) :
    RunBlock S rho D := by
  obtain ⟨j, hj, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed read
  have hDj : D ∈ (rho.stateBefore S j v).st.bodies := by
    simpa only [Run.storeBeforeTime, hj] using hD
  exact Proofs.Bridges.runBlock_of_stateBefore_mem S hv hDj

namespace NamedHeightRegimeBaseRun

variable {S : Setup V} {rho : Run V} {r0 : Round} {blocked : Height}
  {first : Nat} {Tprev : NamedBlock V}

/-- A processed ancestor of any honest preceding prepared head is a prepared
next-voter candidate or is below the prepared read's FG root. -/
theorem voterCandidateMem_or_preceq_root_of_honestPreviousHead_named
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (hgst : gstLagged S ≤ S.hc.Γ_neg1 S.E.Δ r0)
    (h : NamedHeightRegimeBaseRun S rho r0 blocked first Tprev)
    {deadline : Round}
    (hdeadline : first ≤ inclusiveEventIndex rho (S.a deadline))
    {s : Slot} (hs : S.hc.opening_slot deadline + 1 ≤ s)
    (hhor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest)
    {C : Block V}
    (hC : Block.Preceq C (voterHeadAt S rho v s))
    (hCmem : C ∈ Protocol.voter_processed_block_tree S.E
      (voteDutyRead S rho u (s + 1)).st.core.toHealing.toFG.toSG.toGoldfishStore (s + 1)) :
    C ∈ voterCandidateTreeAt S rho u (s + 1) ∨
      Block.Preceq C
        (Protocol.get_fg_root
          (voteDutyRead S rho u (s + 1)).st.core.toHealing.toFG) := by
  let read := voteDutyRead S rho u (s + 1)
  let st := read.st.core
  let blocks := Protocol.voter_processed_block_tree S.E
    st.toHealing.toFG.toSG.toGoldfishStore (s + 1)
  have hdeadlineVote : S.a deadline < Protocol.vote_time S.E (s + 1) :=
    (action_lt_vote_time_two_after S deadline).trans_le
      (vote_time_mono_slots S.E (Nat.succ_le_succ hs))
  have hdeadlineFreeze : S.a deadline ≤ Protocol.view_freeze S.E s := by
    simpa only [Nat.add_sub_cancel] using
      (action_lt_previousFreeze_of_lt_vote_named S hdeadlineVote).le
  have hshor := (frozenHead_vote_add_delta_le_nextVote S.E s).trans hhor
  have hrootHead0 := h.fgRoot_preceq_previousHead_after_deadline
    adm hcom hbelow hgst hdeadline hdeadlineVote.le hhor hs
      (le_refl _) hshor hu hv
  have hrootHead : Block.Preceq
      (Protocol.get_fg_root st.toHealing.toFG)
      (voterHeadAt S rho v s) := by
    simpa only [st, read, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Run.storeBeforeTime, Protocol.voteDutyHead] using hrootHead0
  have hcases : Block.Preceq
        (Protocol.get_fg_root st.toHealing.toFG) C ∨
      Block.Preceq C
        (Protocol.get_fg_root st.toHealing.toFG) :=
    Block.preceq_linear hrootHead hC
  rcases hcases with hroot | hroot
  · left
    obtain ⟨i, a, ta, Cfg, T, hreg, ha⟩ :=
      h.exists_regime_before_deadline adm hbelow hgst hdeadline
    have hrootMem0 := named_fgRoot_mem_filtered_stateBeforeTime
      S rho (Protocol.vote_time S.E (s + 1)) u
    have hrootMem : Protocol.get_fg_root st.toHealing.toFG ∈
        Protocol.get_filtered_block_tree st.toHealing.toFG := by
      simpa only [st, read, voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Run.storeBeforeTime] using hrootMem0
    have hFC : Block.Preceq st.F C := Block.preceq_trans
      (GradeDeliveryRun.finalized_preceq_of_mem_filtered_at_read
        S rho hrootMem) hroot
    have hCraw : C ∈ st.T := (Finset.mem_filter.mp hCmem).1
    have hCtime : C ∈
        (NamedRun.stateBeforeTime S rho
          (Protocol.vote_time S.E (s + 1)) u).st.core.T := by
      simpa only [st, read, voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using hCraw
    obtain ⟨Cn, hCnbody, hCnerase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
        S rho (Protocol.vote_time S.E (s + 1)) u hCtime
    have hCnbody' : Cn ∈
        (rho.storeBeforeTime S u
          (Protocol.vote_time S.E (s + 1))).bodies := by
      simpa only [Run.storeBeforeTime] using hCnbody
    have hCnrun : RunBlock S rho Cn :=
      frozenHead_runBlock_of_read_body S adm hu hCnbody'
    have hFCn : Block.Preceq st.F Cn.erase := by
      rw [hCnerase]
      exact hFC
    have hstoredC : (st.σ C).h =
        (Protocol.derive_named S.E S.cfg Cn).h := by
      rw [← hCnerase]
      exact congrArg Protocol.ChainState.h
        (by simpa only [st, read, voteDutyRead,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom,
            Protocol.NamedStore.setClock] using
          (Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho
            (Protocol.vote_time S.E (s + 1)) u Cn hCnbody))
    have hwitness : ∃ Y ∈ blocks, Block.Preceq C Y ∧
        st.h_max - 1 ≤ (st.σ Y).h := by
      by_cases hcap : st.h_max ≤
          (Protocol.derive_named S.E S.cfg Cn).h + 1
      · refine ⟨C, hCmem, Block.preceq_self C, ?_⟩
        rw [hstoredC]
        exact Nat.sub_le_iff_le_add.mpr hcap
      · have hlt : (Protocol.derive_named S.E S.cfg Cn).h + 1 <
            st.h_max := Nat.lt_of_not_le hcap
        have hCH : (Protocol.derive_named S.E S.cfg Cn).h <
            st.h_max - 1 := Nat.lt_sub_of_add_lt hlt
        by_cases hlow : st.h_max - 1 ≤ blocked + 1
        · have hrow : a.height_pair.erase.height? =
              some (blocked + 0 + 1) := by
            rcases hreg.seed.targetOrTimeout with heq | heq <;>
              simp only [heq, HeightPair.height?, Nat.add_zero]
          have hopen : S.hc.opening_slot a.round + 1 ≤ s :=
            (Nat.add_le_add_right
              (Nat.mul_le_mul_right S.hc.R ha) 1).trans hs
          have hCCfg := h.honestFGSource_preceq_of_previousHead
            adm hcom hbelow hgst 0 hreg.seed.signerHonest
              hreg.seed.emitted hrow hreg.seed.exactFGSource hopen hshor hv
              hCnrun (by rw [hCnerase]; exact hC) (hCH.trans_le hlow)
          have haFreeze : S.a a.round ≤ Protocol.view_freeze S.E s :=
            ((action_strictMono S).monotone ha).trans hdeadlineFreeze
          have hCfgFreezeBody := hreg.sourceMem_at_read_named
            adm haFreeze hu
          have hcohFreeze := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
            (Protocol.view_freeze S.E s) u).1.1.1
          have hCfgFreeze : Cfg.erase ∈
              (rho.storeBeforeTime S u (Protocol.view_freeze S.E s)).T := by
            change Cfg.erase ∈
              (NamedRun.stateBeforeTime S rho
                (Protocol.view_freeze S.E s) u).st.core.T
            rw [hcohFreeze.1]
            exact Finset.mem_image_of_mem NamedBlock.erase hCfgFreezeBody
          have hCfgProcessed := voterProcessed_mem_of_mem_previousFreeze_named
            S adm.toNamedScheduleWellFormed
              (Nat.succ_le_succ (Nat.zero_le s))
              (by simpa only [Nat.add_sub_cancel] using hCfgFreeze)
          have hCfgReadBody := hreg.sourceMem_at_read_named adm
            (((action_strictMono S).monotone ha).trans hdeadlineVote.le) hu
          refine ⟨Cfg.erase, hCfgProcessed, ?_, ?_⟩
          · rw [← hCnerase]
            exact hCCfg
          · have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime
              S rho (Protocol.vote_time S.E (s + 1)) u Cfg hCfgReadBody
            change st.h_max - 1 ≤ (st.σ Cfg.erase).h
            rw [show st.σ Cfg.erase =
                Protocol.derive_named S.E S.cfg Cfg by
              simpa only [st, read, voteDutyRead,
                NamedActionReads.confirmationReadAt,
                NamedActionReads.confirmationReadFrom,
                Protocol.NamedStore.setClock, Run.storeBeforeTime] using hview,
              hreg.seed.sourceDerivedHeight]
            exact hlow
        · let n := (st.h_max - 1) - (blocked + 1)
          have heq : blocked + n + 1 = st.h_max - 1 := by
            calc
              _ = n + (blocked + 1) := by ac_rfl
              _ = st.h_max - 1 := Nat.sub_add_cancel
                (Nat.le_of_lt (Nat.lt_of_not_ge hlow))
          obtain ⟨X, hXbody, hXmax⟩ :=
            Proofs.NamedStoreBridge.maximum_carrier_stateBeforeTime
              S rho (Protocol.vote_time S.E (s + 1)) u
          have hXread : X ∈ read.st.bodies := by
            simpa only [read, voteDutyRead,
              NamedActionReads.confirmationReadAt,
              NamedActionReads.confirmationReadFrom,
              Protocol.NamedStore.setClock] using hXbody
          have hmaxPos : st.h_max ≠ 0 := Nat.ne_of_gt
            ((Nat.zero_le
              ((Protocol.derive_named S.E S.cfg Cn).h + 1)).trans_lt hlt)
          obtain ⟨Y, hYrun, hYprocessed, hCY, hYheight⟩ :=
            h.exists_frozen_descendant_at_crossing_of_previousHead_named
              adm hcom hbelow hgst n hhor hshor hu hv hCnrun
                (by rw [hCnerase]; exact hC) (heq.symm ▸ hCH) hXread
                (by
                  rw [heq, hXmax]
                  exact Nat.sub_one_lt hmaxPos)
          have hYraw : Y.erase ∈ st.T :=
            (Finset.mem_filter.mp hYprocessed).1
          have hYtime : Y.erase ∈
              (NamedRun.stateBeforeTime S rho
                (Protocol.vote_time S.E (s + 1)) u).st.core.T := by
            simpa only [st, read, voteDutyRead,
              NamedActionReads.confirmationReadAt,
              NamedActionReads.confirmationReadFrom,
              Protocol.NamedStore.setClock] using hYraw
          obtain ⟨Yn, hYnbody, hYnerase⟩ :=
            Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
              S rho (Protocol.vote_time S.E (s + 1)) u hYtime
          have hYnbody' : Yn ∈
              (rho.storeBeforeTime S u
                (Protocol.vote_time S.E (s + 1))).bodies := by
            simpa only [Run.storeBeforeTime] using hYnbody
          have hYnrun : RunBlock S rho Yn :=
            frozenHead_runBlock_of_read_body S adm hu hYnbody'
          have hYnY : Yn = Y := by
            apply adm.toNamedRootCollisionFree.root_injective
              Yn Y hYnrun hYrun Yn Y
                (Or.inl (Proofs.NamedAncestry.named_self Yn))
                (Or.inr (Proofs.NamedAncestry.named_self Y))
            rw [← Proofs.NamedWire.erase_root Yn, hYnerase,
              Proofs.NamedWire.erase_root]
          subst Yn
          refine ⟨Y.erase, hYprocessed, ?_, ?_⟩
          · rw [← hCnerase]
            exact hCY
          · have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime
              S rho (Protocol.vote_time S.E (s + 1)) u Y hYnbody
            change st.h_max - 1 ≤ (st.σ Y.erase).h
            rw [show st.σ Y.erase =
                Protocol.derive_named S.E S.cfg Y by
              simpa only [st, read, voteDutyRead,
                NamedActionReads.confirmationReadAt,
                NamedActionReads.confirmationReadFrom,
                Protocol.NamedStore.setClock] using hview,
              hYheight, heq]
    have hfiltered : C ∈ Protocol.get_filtered_block_tree_from
        st.toHealing.toFG blocks := by
      simp only [Protocol.get_filtered_block_tree_from,
        Protocol.viable_tree, Protocol.finalized_descendants,
        Protocol.viable, Finset.mem_filter, decide_eq_true_eq]
      exact ⟨⟨⟨hCmem, hFC⟩, hwitness⟩, hroot⟩
    simpa only [voterCandidateTreeAt, Protocol.voter_filtered_block_tree,
      Proofs.Optimistic.voteDutyRead_slot, st, read, blocks] using hfiltered
  · exact Or.inr hroot

end NamedHeightRegimeBaseRun

/-- Direct post-GST prepared split for a processed block below an honest
supporter's previous head. -/
theorem honestPreviousHead_voterCandidateMem_or_preceq_root_after_GST_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {s : Slot}
    (hs : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra) + 1 ≤ s)
    (hhor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest) {C : Block V}
    (hC : Block.Preceq C (voterHeadAt S rho v s))
    (hCmem : C ∈ Protocol.voter_processed_block_tree S.E
      (Internal.NamedRecoveryRead.voteDutyRead S rho u (s + 1)).st.core.toHealing.toFG.toSG.toGoldfishStore
      (s + 1)) :
    C ∈ voterCandidateTreeAt S rho u (s + 1) ∨
      Block.Preceq C
        (Protocol.get_fg_root
          (Internal.NamedRecoveryRead.voteDutyRead S rho u
            (s + 1)).st.core.toHealing.toFG) := by
  have hdeadlineHor :
      S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) ≤
        rho.horizon :=
    ((action_lt_vote_time_two_after S _).le.trans
      (vote_time_mono_slots S.E (Nat.succ_le_succ hs))).trans hhor
  obtain ⟨blocked, first, Tprev, hfirst, hbase⟩ :=
    exists_namedHeightRegimeBaseRun_before_fgSafetyProgressDeadline
      S adm hcom hbelow hrec hdelay hpost hdeadlineHor
  exact hbase.voterCandidateMem_or_preceq_root_of_honestPreviousHead_named
    adm hcom hbelow (gstLagged_le_Γ_neg1_of_gst_le_a S rGST hpost)
      hfirst hs hhor hu hv hC hCmem

#print axioms NamedHeightRegimeBaseRun.voterCandidateMem_or_preceq_root_of_honestPreviousHead_named
#print axioms honestPreviousHead_voterCandidateMem_or_preceq_root_after_GST_named

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
