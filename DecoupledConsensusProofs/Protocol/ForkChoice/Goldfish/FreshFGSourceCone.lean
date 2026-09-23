module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.RelativeSeedK3

@[expose] public section

/-! # Fresh seed FG-source compatibility

The prepared voter anchor is compatible with the exact FG source selected by
an honest action in the same seed round. The source selector has only two
nonempty outcomes: its selected Q2 fallback, or a clear block above Q2.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.PhaseGrades
open Protocol Proofs.HealingLemmas Proofs.Optimistic DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem freshFGSource_mem_filtered_actionStore
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (v : V) (r : Round) {C : Block V}
    (hsource : nodeFGSource S (actionReadAt S rho v r) r = some C) :
    C ∈ Protocol.get_filtered_block_tree
      (actionStoreAt S rho v r).toHealing.toFG := by
  cases hQ : nodeQ2 S (actionReadAt S rho v r) r with
  | none =>
      have hbad := hsource
      simp only [nodeFGSource, nodeQ2, nodeRead] at hbad hQ
      unfold Protocol.grade2_block_with at hbad
      rw [hQ] at hbad
      simp [Protocol.fg_source_with] at hbad
  | some Q =>
      have hQmem : Q ∈ Protocol.get_filtered_block_tree
          (actionStoreAt S rho v r).toHealing.toFG :=
        actionQ2_mem_filteredTree S rho v r hQ
      have hsource' := hsource
      rw [nodeFGSource, Protocol.fg_source_with.eq_def] at hsource'
      have hQ' : Protocol.grade2_block_with
          (NamedProfile.gradeContract (actionReadAt S rho v r).cache)
          S.E S.hc (actionReadAt S rho v r).st.core.toHealing r = some Q := hQ
      rw [hQ'] at hsource'
      cases hwalk : Protocol.deepest_clear (some Q)
          (actionReadAt S rho v r).st.core.toHealing.live_confirmed
          ((NamedProfile.gradeContract (actionReadAt S rho v r).cache).read
            S.E S.hc (actionReadAt S rho v r).st.core.toHealing r).clear with
      | none =>
          simp only [hwalk] at hsource'
          rw [← Option.some_inj.mp hsource']
          exact hQmem
      | some B =>
          simp only [hwalk] at hsource'
          have hCB : C = B := (Option.some_inj.mp hsource').symm
          subst B
          have hmemChain := Proofs.Engine.deepest?_mem hwalk
          obtain ⟨hchain, hQC, -⟩ := Finset.mem_filter.mp hmemChain
          have hCL : Block.Preceq C
              (actionStoreAt S rho v r).live_confirmed :=
            Proofs.Engine.mem_chain_of_preceq (List.mem_toFinset.mp hchain)
          have hQC' : Block.Preceq Q C := by simpa using hQC
          have hLmem := liveConfirmed_mem_filtered_actionStore S adm v r
          have hQmem' := hQmem
          have hLmem' := hLmem
          simp only [Protocol.get_filtered_block_tree,
            Protocol.get_filtered_block_tree_from,
            Protocol.viable_tree, Protocol.finalized_descendants,
            Protocol.viable, Finset.mem_filter, Protocol.Store.toHealing,
            decide_eq_true_eq] at hQmem' hLmem' ⊢
          obtain ⟨⟨⟨-, hFQ⟩, -⟩, hrootQ⟩ := hQmem'
          obtain ⟨⟨⟨hLT, -⟩, W, hWT, hLW, hWh⟩, -⟩ := hLmem'
          have hpc : ParentClosed (actionStoreAt S rho v r).st.core := by
            have hpcPre := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime
              S rho (S.a r) v
            have hT : (actionStoreAt S rho v r).st.core.T =
                (rho.storeBeforeTime S v (S.a r)).core.T := rfl
            simpa only [ParentClosed, Protocol.GoldfishStore.parent_closed, hT] using hpcPre
          refine ⟨⟨⟨?_, ?_⟩, W, hWT,
            Block.preceq_trans hCL hLW, hWh⟩, ?_⟩
          · exact Proofs.Records.mem_of_preceq hpc.2 C _ hLT hCL
          · exact Block.preceq_trans hFQ hQC'
          · exact Block.preceq_trans hrootQ hQC'

/-- An exact prepared FG source has a named body in its action store. -/
theorem freshFGSource_namedSource_witness
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {C : Block V}
    (hsource : nodeFGSource S (actionReadAt S rho v r) r = some C) :
    ∃ Cn : NamedBlock V,
      Cn ∈ (actionStoreAt S rho v r).st.bodies ∧ Cn.erase = C ∧
        RunBlock S rho Cn := by
  have hmem : C ∈ (actionStoreAt S rho v r).st.core.T :=
    Proofs.Records.get_filtered_block_tree_subset _
      (freshFGSource_mem_filtered_actionStore S adm v r hsource)
  have hmemPre : C ∈ (rho.storeBeforeTime S v (S.a r)).core.T := by
    simpa only [actionStoreAt_eq_update_confirmation_confStore,
      Protocol.update_confirmation_with, Run.storeBeforeTime] using hmem
  obtain ⟨Cn, hbodyPre, hCerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho (S.a r) v hmemPre
  have hCrun : RunBlock S rho Cn := by
    obtain ⟨i, hi, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
      S adm.toNamedScheduleWellFormed (S.a r)
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i := i)
    rw [← hi]
    exact hbodyPre
  have hbody : Cn ∈ (actionStoreAt S rho v r).st.bodies := by
    simpa only [actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using hbodyPre
  exact ⟨Cn, hbody, hCerase, hCrun⟩

private theorem freshFGSource_frontierWitness
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} {r : Round} {M : Height} {C : Block V}
    (hsource : nodeFGSource S (actionReadAt S rho v r) r = some C)
    (hfrontier : (rho.storeBeforeTime S v (S.a r)).h_max = M) :
    ∃ W : NamedBlock V,
      W ∈ (actionStoreAt S rho v r).st.bodies ∧ Block.Preceq C W.erase ∧
        M - 1 ≤ (Protocol.derive_named S.E S.cfg W).h := by
  have hfiltered := freshFGSource_mem_filtered_actionStore S adm v r hsource
  simp only [Protocol.get_filtered_block_tree,
    Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq,
    Protocol.Store.toHealing] at hfiltered
  obtain ⟨⟨⟨-, -⟩, W, hWT, hCW, hheight⟩, -⟩ := hfiltered
  have hmax : (actionStoreAt S rho v r).st.core.h_max = M := by
    rw [actionStoreAt_eq_update_confirmation_confStore]
    simp only [Protocol.update_confirmation_with]
    simpa only [Run.storeBeforeTime] using hfrontier
  rw [hmax] at hheight
  have hWTpre : W ∈ (rho.storeBeforeTime S v (S.a r)).core.T := by
    have hWT' := hWT
    rw [actionStoreAt_eq_update_confirmation_confStore] at hWT'
    simpa only [Protocol.update_confirmation_with] using hWT'
  obtain ⟨D, hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho (S.a r) v hWTpre
  have hsig : (actionStoreAt S rho v r).st.core.σ D.erase =
      Protocol.derive_named S.E S.cfg D := by
    rw [actionStoreAt_eq_update_confirmation_confStore]
    simpa only [Protocol.update_confirmation_with, hDerase] using
      (Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho (S.a r) v D hDbody)
  refine ⟨D, hDbody, ?_, ?_⟩
  · simpa only [hDerase] using hCW
  · rw [← congrArg (fun cs => cs.h) hsig]
    simpa only [hDerase] using hheight

set_option maxHeartbeats 400000 in
/-- Every prepared honest seed voter anchor is compatible with the exact FG
source selected by any honest action in the round. -/
theorem preparedAnchor_compatible_freshFGSource_of_gateOff_relative
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {c : Round} (hc : 1 ≤ c)
    (hframe : GateOffFrameAt S rho M (c - 1) (c + 1))
    (hpost : S.E.t_GST ≤ S.a (c - 1))
    (hhorNext : S.a (c + 1) ≤ rho.horizon)
    (ready : GradeRoundReady S rho c)
    {w v : V} (hw : w ∈ rho.honest) (hv : v ∈ rho.honest) {d : Slot}
    (hd1 : S.hc.opening_slot c + 1 ≤ d)
    (hd2 : d ≤ seedRoundLastSlot S c)
    (hround : S.hc.round_of d = c) {C : Block V}
    (hsource : nodeFGSource S (actionReadAt S rho v c) c = some C) :
    Block.compatible (voterAnchorAt S rho w d) C = true := by
  have hcPos : 0 < c := Nat.succ_le_iff.mp hc
  have haPredC : S.a (c - 1) ≤ S.a c := Assembly.a_mono S (Nat.sub_le c 1)
  have haCSucc : S.a c ≤ S.a (c + 1) := Assembly.a_mono S (Nat.le_succ c)
  have hhorC : S.a c ≤ rho.horizon := haCSucc.trans hhorNext
  have hlo : S.hc.opening_slot c ≤ d := (Nat.le_succ _).trans hd1
  have hdNext : d ≤ S.hc.opening_slot (c + 1) :=
    hd2.trans (by unfold seedRoundLastSlot; exact Nat.sub_le _ _)
  have hvoteHi : Protocol.vote_time S.E d ≤ S.a (c + 1) := by
    refine (Protocol.vote_time_le_confirmation_time S.E d).trans ?_
    have hm : Protocol.confirmation_time S.E d ≤
        Protocol.confirmation_time S.E (S.hc.opening_slot (c + 1)) := by
      rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E d,
        ← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E
          (S.hc.opening_slot (c + 1))]
      exact Int.add_le_add_right
        (Protocol.vote_time_mono_slots S.E (Nat.succ_le_succ hdNext)) _
    exact hm.trans (by rw [Setup.a, Protocol.a_eq_confirmation_time])
  have hvoteHor := hvoteHi.trans hhorNext
  have hnext : Protocol.vote_time S.E d ≤ opening S.E S.hc (c + 1) := by
    have hlt : d < S.hc.opening_slot (c + 1) :=
      hd2.trans_lt (Nat.sub_lt (by
        unfold Protocol.HealConfig.opening_slot
        exact Nat.mul_pos (Nat.succ_pos c)
          (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)) Nat.one_pos)
    exact (le_of_lt (by
      simpa only [opening] using
        (show Protocol.vote_time S.E d <
          Protocol.proposal_time S.E (S.hc.opening_slot (c + 1)) from
          (by
            exact (by
              have h := Protocol.proposal_time_mono S.E (Nat.succ_le_of_lt hlt)
              exact (lt_of_lt_of_le
                (by
                  simp only [Protocol.vote_time, Protocol.proposal_time,
                    Env.t, slotStart]
                  push_cast
                  nlinarith [S.E.Δ_pos]) h))))))
  have hprev : ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (c - 1))).h_max = M :=
    fun u hu => (hframe _ le_rfl (haPredC.trans haCSucc) u hu).2
  have hfrontier : ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a c)).h_max = M :=
    fun u hu => (hframe _ haPredC haCSucc u hu).2
  have hgate : ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a c)).h_j + 2 ≤ M :=
    fun u hu => (hframe _ haPredC haCSucc u hu).1
  have hsettled : NamedLiveG1SettledAt S rho c :=
    namedLiveG1SettledAt_of_gateOff S adm hfb hcPos hpost hprev hfrontier hgate hhorC
  have hsb := slashableBound_of_admissible_belowOneThird S adm hfb
  cases hQ : nodeQ2 S (actionReadAt S rho v c) c with
  | none =>
      have hbad := hsource
      simp only [nodeFGSource, nodeQ2, nodeRead] at hbad hQ
      unfold Protocol.grade2_block_with at hbad
      rw [hQ] at hbad
      simp [Protocol.fg_source_with] at hbad
  | some Q =>
      have hQG1 := namedG1At_of_nodeQ2 S adm hcPos hhorC v hv Q hQ
      have hQG2 := selectedQ2_storeGrade_at_g2Domain S adm hQ
      have hsource' := hsource
      rw [nodeFGSource, Protocol.fg_source_with.eq_def] at hsource'
      have hQ' : Protocol.grade2_block_with
          (NamedProfile.gradeContract (actionReadAt S rho v c).cache)
          S.E S.hc (actionReadAt S rho v c).st.core.toHealing c = some Q := hQ
      rw [hQ'] at hsource'
      cases hwalk : Protocol.deepest_clear (some Q)
          (actionReadAt S rho v c).st.core.toHealing.live_confirmed
          ((NamedProfile.gradeContract (actionReadAt S rho v c).cache).read
            S.E S.hc (actionReadAt S rho v c).st.core.toHealing c).clear with
      | none =>
          simp only [hwalk] at hsource'
          have hCQ : C = Q := (Option.some_inj.mp hsource').symm
          subst C
          rcases voterAnchorAt_cases S rho w d with hfgAnchor |
              ⟨root, A, hframeG1, hactive, hanchor⟩
          ·
              have hvoteLo : S.a (c - 1) ≤ Protocol.vote_time S.E d := by
                have hpredLt : c - 1 < c := Nat.sub_lt hcPos Nat.zero_lt_one
                have h1 := action_add_delta_le_openingProposal_of_round_lt S hpredLt
                exact ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h1).trans
                  ((Protocol.proposal_time_mono S.E hlo).trans
                    (le_of_lt (Protocol.proposal_time_lt_vote_time S.E d)))
              have hgateRead := (hframe (Protocol.vote_time S.E d)
                hvoteLo hvoteHi w hw).1
              have hfrontierRead := (hframe (Protocol.vote_time S.E d)
                hvoteLo hvoteHi w hw).2
              have hgateDuty : (voteDutyStore S rho w d).h_j + 2 ≤ M := by
                simpa only [voteDutyStore, voteStore, tickStore] using hgateRead
              have hfrontierDuty : (voteDutyStore S rho w d).h_max = M := by
                simpa only [voteDutyStore, voteStore, tickStore] using hfrontierRead
              obtain ⟨W, hWbody, hQW, hWh⟩ :=
                freshFGSource_frontierWitness S adm hsource (hfrontier v hv)
              have hWpre : W ∈ (rho.storeBeforeTime S v (S.a c)).bodies := by
                simpa only [actionStoreAt, actionReadAt,
                  NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
                  NamedActionReads.confirmationReadFrom,
                  NamedActionReads.preparedCache, NamedRun.stateBeforeTime,
                  Run.storeBeforeTime] using hWbody
              have hWrun : RunBlock S rho W := by
                obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
                  S adm.toNamedScheduleWellFormed (S.a c)
                apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i := n)
                rw [← hn]
                exact hWpre
              have hFW : Block.Preceq
                  (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).core.F W.erase :=
                finalizedRoot_preceq_of_band S adm hfb hw hgateRead hWrun hWh
              rw [hfgAnchor]
              exact Block.compatible_of_preceq_common (by
                change Block.Preceq (Protocol.get_fg_root
                  (voteDutyStore S rho w d).toHealing.toFG) W.erase
                rw [fgRoot_eq_F_of_frame hgateDuty hfrontierDuty]
                simpa only [voteDutyStore, voteStore, tickStore] using hFW) hQW
          ·
              obtain ⟨-, hAG1⟩ := fixedRoot_activeVoterAnchor_g1_data
                S adm hcPos hlo hround hnext hvoteHor hw (by
                  simpa only [Internal.NamedRecoveryRead.voteDutyRead,
                    NamedActionReads.confirmationReadAt,
                    NamedActionReads.confirmationReadFrom,
                    Protocol.NamedStore.setClock, Proofs.Optimistic.slotOf_vote_time,
                    hround] using hframeG1) hactive
              rw [hanchor]
              rcases hsettled v hv Q hQG1 w hw with hQroot | hQactive
              · rcases hsettled w hw A hAG1 w hw with hAroot | hAactive
                · exact Block.compatible_of_preceq_common hAroot hQroot
                · have hrootA := Proofs.Records.preceq_get_fg_root_of_mem_filtered hAactive
                  rw [← actionStoreAt_fgRoot_eq_storeBeforeTime] at hQroot
                  simpa only [Block.compatible, Bool.or_eq_true] using
                    Or.inr (Block.preceq_trans hQroot hrootA)
              · have hQG1w := storeGrade_g1_of_g2_and_targetActionActive
                  S adm hsb hcPos ready hv hw hQG2 (by
                    change Q ∈ Protocol.get_filtered_block_tree
                      (actionStoreAt S rho w c).toHealing.toFG
                    rw [actionStoreAt_filteredTree]
                    exact hQactive)
                exact relativeSeed_sameReaderG1_compatible S rho c w hAG1 hQG1w
      | some B =>
          simp only [hwalk] at hsource'
          have hCB : C = B := (Option.some_inj.mp hsource').symm
          subst B
          have hQC : Block.Preceq Q C := by
            exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hwalk)).2.1
          have hCclear : nodeClear S (actionReadAt S rho v c) c C = true := by
            exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hwalk)).2.2
          rcases voterAnchorAt_cases S rho w d with hfgAnchor |
              ⟨root, A, hframeG1, hactive, hanchor⟩
          ·
              have hvoteLo : S.a (c - 1) ≤ Protocol.vote_time S.E d := by
                have hpredLt : c - 1 < c := Nat.sub_lt hcPos Nat.zero_lt_one
                have h1 := action_add_delta_le_openingProposal_of_round_lt S hpredLt
                exact ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h1).trans
                  ((Protocol.proposal_time_mono S.E hlo).trans
                    (le_of_lt (Protocol.proposal_time_lt_vote_time S.E d)))
              have hgateRead := (hframe (Protocol.vote_time S.E d)
                hvoteLo hvoteHi w hw).1
              have hfrontierRead := (hframe (Protocol.vote_time S.E d)
                hvoteLo hvoteHi w hw).2
              have hgateDuty : (voteDutyStore S rho w d).h_j + 2 ≤ M := by
                simpa only [voteDutyStore, voteStore, tickStore] using hgateRead
              have hfrontierDuty : (voteDutyStore S rho w d).h_max = M := by
                simpa only [voteDutyStore, voteStore, tickStore] using hfrontierRead
              obtain ⟨W, hWbody, hCW, hWh⟩ :=
                freshFGSource_frontierWitness S adm hsource (hfrontier v hv)
              have hWpre : W ∈ (rho.storeBeforeTime S v (S.a c)).bodies := by
                simpa only [actionStoreAt, actionReadAt,
                  NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
                  NamedActionReads.confirmationReadFrom,
                  NamedActionReads.preparedCache, NamedRun.stateBeforeTime,
                  Run.storeBeforeTime] using hWbody
              have hWrun : RunBlock S rho W := by
                obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
                  S adm.toNamedScheduleWellFormed (S.a c)
                apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i := n)
                rw [← hn]
                exact hWpre
              have hFW : Block.Preceq
                  (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).core.F W.erase :=
                finalizedRoot_preceq_of_band S adm hfb hw hgateRead hWrun hWh
              rw [hfgAnchor]
              exact Block.compatible_of_preceq_common (by
                change Block.Preceq (Protocol.get_fg_root
                  (voteDutyStore S rho w d).toHealing.toFG) W.erase
                rw [fgRoot_eq_F_of_frame hgateDuty hfrontierDuty]
                simpa only [voteDutyStore, voteStore, tickStore] using hFW) hCW
          ·
              obtain ⟨-, hAG1⟩ := fixedRoot_activeVoterAnchor_g1_data
                S adm hcPos hlo hround hnext hvoteHor hw (by
                  simpa only [Internal.NamedRecoveryRead.voteDutyRead,
                    NamedActionReads.confirmationReadAt,
                    NamedActionReads.confirmationReadFrom,
                    Protocol.NamedStore.setClock, Proofs.Optimistic.slotOf_vote_time,
                    hround] using hframeG1) hactive
              rw [hanchor]
              rcases hsettled w hw A hAG1 v hv with hAroot | hAactive
              · have hrootQ : Block.Preceq
                    (Protocol.get_fg_root
                      (rho.storeBeforeTime S v (S.a c)).toHealing.toFG) Q := by
                  rw [← actionStoreAt_fgRoot_eq_storeBeforeTime]
                  exact Proofs.Records.preceq_get_fg_root_of_mem_filtered
                    (actionQ2_mem_filteredTree S rho v c hQ)
                exact (show Block.compatible A C = true by
                  simp only [Block.compatible, Bool.or_eq_true]
                  exact Or.inl (Block.preceq_trans hAroot
                    (Block.preceq_trans hrootQ hQC)))
              · have hAaction : A ∈ filteredTree (actionReadAt S rho v c) := by
                  change A ∈ Protocol.get_filtered_block_tree
                    (actionStoreAt S rho v c).toHealing.toFG
                  rw [actionStoreAt_filteredTree]
                  exact hAactive
                have hAG0 := storeGrade_g0_of_g1_and_targetActionActive
                  S adm hsb hcPos ready hw hv hAG1 hAaction
                exact relativeG0_compatible_clearSource S adm hcPos hhorC hv hAG0
                  (storeGrade_g0_mem_domainTree S rho hAG0) hAaction hCclear

#print axioms freshFGSource_namedSource_witness
#print axioms preparedAnchor_compatible_freshFGSource_of_gateOff_relative

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
