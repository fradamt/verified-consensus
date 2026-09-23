module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.WeakConfirmationReadAnchorsNamed
public import DecoupledConsensusProofs.Protocol.ChainState.FGRootWitness
public import DecoupledConsensusProofs.Protocol.Grades.ProposalWalkComposition

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Current proposal band and prepared confirmation candidate -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakGenesis

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem voteDuty_mem_confStore_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} {s : Slot} {C : Block V}
    (hC : C ∈ (Proofs.Optimistic.voteDutyStore S rho w s).T) :
    C ∈ (Proofs.Optimistic.confStore S rho w s).T := by
  have hVotePre : C ∈
      (rho.storeBeforeTime S w (Protocol.vote_time S.E s)).core.T := by
    simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using hC
  have hVoteIndex : C ∈ (rho.stateBefore S
      (strictEventIndex rho (Protocol.vote_time S.E s)) w).st.core.T := by
    rw [← storeBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedScheduleWellFormed w]
    exact hVotePre
  have hConfIndex : C ∈ (rho.stateBefore S
      (strictEventIndex rho (Protocol.confirmation_time S.E s)) w).st.core.T :=
    stateBefore_T_subset S rho w _
      (strictEventIndex_mono rho
        (vote_time_le_confirmation_time S.E s)) hVoteIndex
  have hConfPre : C ∈
      (rho.storeBeforeTime S w (Protocol.confirmation_time S.E s)).core.T := by
    rw [storeBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedScheduleWellFormed w]
    exact hConfIndex
  simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using hConfPre

private theorem actionTime_lt_nextVote_of_lt_confirmation_band
    (S : Setup V) {r : Round} {s : Slot}
    (h : S.a r < Protocol.confirmation_time S.E s) :
    S.a r < Protocol.vote_time S.E (s + 1) := by
  exact (action_time_lt_proposal_of_lt_previous_confirmation
    S (s := s + 1) (Nat.zero_lt_succ s) (by simpa only [Nat.add_sub_cancel] using h)).trans
      (proposal_time_lt_vote_time S.E (s + 1))


/-- Item 16 over the exact pinned later-slot admission producer. -/
theorem proposedBlock_confirmationBandAndCandidate_of_gstZero_of_pins
    (hadmitLater : ∀ (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
      {d : Slot}, 1 ≤ d →
      Protocol.vote_time S.E (d + 1) ≤ rho.horizon →
      S.E.proposer (d + 1) ∈ rho.honest →
      ∀ {B : NamedBlock V}, proposedBlockAt S rho (d + 1) = some B →
      ∀ {v : V}, v ∈ rho.honest →
        AdmittedBefore S rho v B.erase (Protocol.vote_time S.E (d + 1)))
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {s : Slot} (hs : 0 < s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hprop : S.E.proposer s ∈ rho.honest)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B)
    (hstores : ∀ v ∈ rho.honest,
      Proofs.Optimistic.NamedVoteStoreExtends S rho v s
        (namedWalkTargetTree S rho s v B)
        (proposedParent S rho s) B) :
    ∀ v ∈ rho.honest,
      (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).st.core.h_max - 1 ≤
          (Protocol.derive_named S.E S.cfg B).h ∧
        B.erase ∈ confTree (Proofs.Optimistic.confStore S rho v s) := by
  intro v hv
  let conf := Proofs.Optimistic.confStore S rho v s
  have hvoteHor : Protocol.vote_time S.E s ≤ rho.horizon :=
    (vote_time_le_confirmation_time S.E s).trans hhor
  have hhead : voterHeadAt S rho v s = B.erase :=
    Protocol.voterHeadAt_eq_proposedBlockAt_of_namedVoteStoreExtends
      S hB (hstores v hv)
  have hBrun : RunBlock S rho B :=
    proposedBlockAt_blockInRun_of_admissible S h.core s hs hprop
      ((proposal_time_lt_vote_time S.E s).le.trans hvoteHor) hB
  have hBvote : B.erase ∈ (Proofs.Optimistic.voteDutyStore S rho v s).T := by
    by_cases hsOne : s = 1
    · have hcandidate : B.erase ∈ voterCandidateTreeAt S rho v s := by
        have htree := (hstores v hv).tree
        rw [htree]
        exact Finset.mem_insert_self _ _
      have hprocessed := Proofs.Records.get_filtered_block_tree_from_subset
        (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.toFG
        (Protocol.voter_processed_block_tree S.E
          (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.toFG.toSG.toGoldfishStore
          (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.s) (by
            simpa only [voterCandidateTreeAt,
              Internal.NamedRecoveryRead.voteDutyRead,
              NamedActionReads.confirmationReadAt,
              NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
              Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
              Proofs.Optimistic.tickStore] using hcandidate)
      exact (Finset.mem_filter.mp hprocessed).1
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hs)
      have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (by
        intro hd0
        subst d
        exact hsOne rfl)
      have hadmit := hadmitLater S h hd hvoteHor hprop hB hv
      exact (admittedBefore_mem_and_stamp_at S h.core.toNamedScheduleWellFormed
        hadmit (le_refl _)).1
  have hBconf : B.erase ∈ conf.T := by
    exact voteDuty_mem_confStore_core S h.core hBvote
  obtain ⟨B', hB'body, hB'erase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (Protocol.confirmation_time S.E s) v (by
        simpa only [conf, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using hBconf)
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S h.core.toNamedScheduleWellFormed (Protocol.confirmation_time S.E s)
  have hB'prefix : B' ∈ (rho.stateBefore S n v).st.bodies := by
    rw [← congrArg (fun world => (world v).st.bodies) hn]
    exact hB'body
  have hB'run : RunBlock S rho B' :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hv hB'prefix
  have hB'eq : B' = B := by
    apply h.core.toNamedRootCollisionFree.root_injective B' B hB'run hBrun
      B' B (Or.inl (Proofs.NamedAncestry.named_self B'))
        (Or.inr (Proofs.NamedAncestry.named_self B))
    rw [← Proofs.NamedWire.erase_root B', ← Proofs.NamedWire.erase_root B, hB'erase]
  have hBbody : B ∈ (rho.stateBeforeTime S
      (Protocol.confirmation_time S.E s) v).st.bodies := by
    rw [← hB'eq]
    exact hB'body
  have hBview : conf.σ B.erase = Protocol.derive_named S.E S.cfg B := by
    simpa only [conf, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using
      Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho
        (Protocol.confirmation_time S.E s) v B hBbody
  have hband : conf.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg B).h := by
    by_cases hlarge : 1 < conf.h_max
    · have hmajority := honestWeightMajority_of_finiteWindows S h.windows hhor
      obtain ⟨a, ta, D, K, ha, hemit, hat, hrow, hfg, hD, hK,
          hKentry, hKrun, hKheight⟩ := frontier_confirmationWitness_core_entry
        S h.core hmajority (v := v) (time := Protocol.confirmation_time S.E s)
          (by simpa only [conf, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using hlarge)
      have htime : ta = S.a a.round := (emits_attest_shape S hemit).2
      have hactionTime : S.a a.round < Protocol.vote_time S.E (s + 1) :=
        actionTime_lt_nextVote_of_lt_confirmation_band S (by
          rw [← htime]
          exact hat)
      have hsafe : Block.Preceq
          (Protocol.derive_named S.E S.cfg K).T_h
          (voterHeadAt S rho v s) :=
        ((actionSources_preceq_voteDutyHead_of_gstZero
          S h.core h.committees h.gstZero h.windows hhor
            (Nat.succ_le_iff.mpr hs) (Nat.le_succ s) hv
            a.round hactionTime).2 a.val_index ha).2 _ hfg
      have hKB : Block.Preceq K.erase B.erase := by
        rw [hKentry] at hsafe
        simpa only [Protocol.voteDutyHead, hhead] using hsafe
      obtain ⟨K', hK'B, hK'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hKB
      have hK'run : RunBlock S rho K' :=
        Proofs.NamedRuntime.blockInRun_of_ancestor S rho hBrun hK'B
      have hK'eq : K' = K := by
        apply h.core.toNamedRootCollisionFree.root_injective K' K hK'run hKrun
          K' K (Or.inl (Proofs.NamedAncestry.named_self K'))
            (Or.inr (Proofs.NamedAncestry.named_self K))
        rw [← Proofs.NamedWire.erase_root K', ← Proofs.NamedWire.erase_root K, hK'erase]
      have hKBnamed : NamedBlock.Preceq K B := by
        rw [← hK'eq]
        exact hK'B
      have hKheight' : (Protocol.derive_named S.E S.cfg K).h =
          conf.h_max - 1 := by
        simpa only [conf, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using hKheight
      rw [← hKheight']
      exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hKBnamed
    · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hlarge)]
      exact Nat.zero_le _
  have hanchor : Block.Preceq
      (namedConfirmationAnchor S
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v s)) B.erase := by
    rw [← hhead]
    exact preparedConfirmationAnchor_preceq_voterHeadAt_of_gstZero
      S h hs hhor hv hv
  have hroot : Block.Preceq
      (Protocol.get_fg_root conf.toHealing.toFG) B.erase :=
    Block.preceq_trans (by
      simpa only [conf, Proofs.Optimistic.confStore_eq_confirmationInputRead] using
        fg_root_preceq_get_sg_root_with_frame
          (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).cache
          S.E S.hc conf.toHealing (S.hc.round_of conf.s)) hanchor
  have hFJ : Block.Preceq conf.F conf.J := by
    simpa only [conf, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using
      Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        S rho (Protocol.confirmation_time S.E s) v
  have hFB : Block.Preceq conf.F B.erase :=
    Block.preceq_trans
      (Proofs.Records.preceq_get_fg_root_of_F (st := conf.toHealing.toFG) hFJ) hroot
  have hcandidate : B.erase ∈ confTree conf := by
    simp only [confTree, Protocol.get_filtered_block_tree,
      Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq]
    exact ⟨⟨⟨hBconf, hFB⟩, B.erase, hBconf, Block.preceq_self _,
      by
        change conf.h_max - 1 ≤ (conf.σ B.erase).h
        rw [hBview]
        exact hband⟩, hroot⟩
  constructor
  · simpa only [conf, Proofs.Optimistic.confStore_eq_confirmationInputRead] using hband
  · exact hcandidate

#print axioms proposedBlock_confirmationBandAndCandidate_of_gstZero_of_pins

end WeakGenesis
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
