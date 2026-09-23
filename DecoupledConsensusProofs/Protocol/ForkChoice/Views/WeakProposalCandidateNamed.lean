module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.WeakProposalAdmissionNamed
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedViability

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Prepared weak-genesis proposal candidates -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Protocol Proofs.Optimistic Statements

variable {V : Type} [DecidableEq V] [Fintype V]

namespace WeakGenesis

/-- Every later honest weak-genesis proposal is a candidate in each honest
prepared vote read. -/
theorem proposedBlock_voterCandidate_of_gstZero_named
    (S : Setup V) {rho : Run V} (h : WeakGenesis S rho)
    {d : Slot} (hd : 1 ≤ d)
    (hhor : Protocol.vote_time S.E (d + 1) ≤ rho.horizon)
    (hprop : S.E.proposer (d + 1) ∈ rho.honest)
    {B : NamedBlock V} (hB : proposedBlockAt S rho (d + 1) = some B)
    {v : V} (hv : v ∈ rho.honest) :
    B.erase ∈ voterCandidateTreeAt S rho v (d + 1) := by
  let s := d + 1
  let t := Protocol.vote_time S.E s
  let read := Internal.NamedRecoveryRead.voteDutyRead S rho v s
  let st := read.st.core
  have hdPos : 0 < d := lt_of_lt_of_le Nat.zero_lt_one hd
  have hconfHor : Protocol.confirmation_time S.E (d - 1) ≤ rho.horizon :=
    (confirmationTime_lt_nextVote_of_lt S.E
      (Nat.sub_lt hdPos (by decide))).le.trans hhor
  have hupper : d ≤ (d - 1) + 1 := by
    rw [Nat.sub_add_cancel hd]
  have hproposalHor : Protocol.proposal_time S.E s ≤ rho.horizon :=
    (proposal_time_lt_vote_time S.E s).le.trans hhor
  have hBrun : RunBlock S rho B :=
    proposedBlockAt_blockInRun_of_admissible
      S h.core s (Nat.zero_lt_succ d) hprop hproposalHor hB
  have hadmit := proposedBlock_admittedBefore_vote_of_gstZero_named
    S h hd hhor hprop hB hv
  have hBT0 := (admittedBefore_mem_and_stamp_at
    S h.core.toNamedScheduleWellFormed hadmit (le_refl t)).1
  have hBT : B.erase ∈ st.T := by
    simpa only [st, read, t, s, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using hBT0
  have hslot : st.s = s := by
    simpa only [st, read] using voteDutyRead_slot S rho v s
  have hprocessed : B.erase ∈ Protocol.voter_processed_block_tree S.E
      (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.toFG.toSG.toGoldfishStore
      (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.s := by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    refine ⟨?_, Or.inr ⟨B.erase, ?_, Block.preceq_self _⟩⟩
    · simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, st, read, t, s,
        Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock] using hBT
    · refine ⟨?_, ?_⟩
      · simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, st, read, t, s,
          Internal.NamedRecoveryRead.voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock] using hBT
      · rw [Proofs.NamedWire.erase_slot, proposedBlockAt_slot S rho s hB,
          Proofs.Optimistic.toHealing_slot]
        exact (Proofs.Optimistic.voteDutyStore_slot S rho v s).symm
  obtain ⟨B', hB'body, hB'erase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho t v (by
      simpa only [st, read, t, Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
        using hBT)
  obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    h.core.toNamedScheduleWellFormed.sorted t
  have hB'prefix : B' ∈ (NamedRun.stateBefore S rho n v).st.bodies := by
    rw [← congrFun hn v]
    exact hB'body
  have hB'run : RunBlock S rho B' :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hv hB'prefix
  have hB'eq : B' = B := by
    apply h.core.toNamedRootCollisionFree.root_injective B' B hB'run hBrun
      B' B (Or.inl (Proofs.NamedAncestry.named_self B'))
        (Or.inr (Proofs.NamedAncestry.named_self B))
    rw [← Proofs.NamedWire.erase_root B', ← Proofs.NamedWire.erase_root B, hB'erase]
  have hBbody : B ∈ (rho.storeBeforeTime S v t).bodies := by
    rw [← hB'eq]
    exact hB'body
  have hBview : (st.σ B.erase).h =
      (Protocol.derive_named S.E S.cfg B).h := by
    have hvw := Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho t v B hBbody
    simpa only [st, read, t, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      congrArg (fun z => z.h) hvw
  have hparentBlock : Block.Preceq (proposedParent S rho s) B.erase :=
    proposedParent_preceq_proposedBlockAt S rho s hB
  have hbandNamed : st.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg B).h := by
    by_cases hlarge : 1 < st.h_max
    · have hmajority := honestWeightMajority_of_finiteWindows S h.windows hconfHor
      obtain ⟨a, ta, D, K, ha, hemit, hat, -, hfgK, -, -, hKentry,
          hKrun, hKheight⟩ := frontier_confirmationWitness_core_entry
        S h.core hmajority (v := v) (time := t) (by
          simpa only [st, read, t, Internal.NamedRecoveryRead.voteDutyRead,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
            using hlarge)
      have haTime : S.a a.round < Protocol.vote_time S.E s := by
        have htime : ta = S.a a.round := (emits_attest_shape S hemit).2
        rw [← htime]
        exact hat
      have hheadsK : ∀ x ∈ rho.honest,
          Block.Preceq K.erase (voterHeadAt S rho x d) := by
        intro x hx
        have hsafe := ((actionSources_preceq_voteDutyHead_of_gstZero
          S h.core h.committees h.gstZero h.windows hconfHor hd hupper hx
            a.round haTime).2 a.val_index ha).2 _ hfgK
        rw [← hKentry]
        simpa only [voteDutyHead] using hsafe
      have hvotePrev : Protocol.vote_time S.E d ≤ rho.horizon :=
        (vote_time_mono_slots S.E (Nat.le_succ d)).trans hhor
      have hprotectedK : ProtectedVoteSlot S rho d K.erase := by
        refine ⟨hheadsK, ?_⟩
        intro x hx hxCommittee
        obtain ⟨X, hXerase, hXrun, hXemit⟩ :=
          WeakGoldfish.voterHead_runBlock_and_emits
            S h.core hx hdPos hxCommittee hvotePrev
        exact ⟨X, by simpa only [hXerase] using hheadsK x hx, hXrun, hXemit⟩
      have hKparent := protected_preceq_proposedParent_of_gstZero_named
        S h hconfHor hd hupper hproposalHor hprop hprotectedK
      have hKB : Block.Preceq K.erase B.erase :=
        Block.preceq_trans hKparent hparentBlock
      obtain ⟨K', hK'B, hK'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hKB
      have hK'run : RunBlock S rho K' :=
        Proofs.NamedRuntime.blockInRun_of_ancestor S rho hBrun hK'B
      have hK'eq : K' = K := by
        apply h.core.toNamedRootCollisionFree.root_injective K' K hK'run hKrun
          K' K (Or.inl (Proofs.NamedAncestry.named_self K'))
            (Or.inr (Proofs.NamedAncestry.named_self K))
        rw [← Proofs.NamedWire.erase_root K', ← Proofs.NamedWire.erase_root K, hK'erase]
      have hstHmax : st.h_max = (rho.storeBeforeTime S v t).core.h_max := by rfl
      rw [hstHmax, ← hKheight]
      exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg (by
        rw [← hK'eq]
        exact hK'B)
    · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hlarge)]
      exact Nat.zero_le _
  have hband : st.h_max - 1 ≤ (st.σ B.erase).h := by
    rw [hBview]
    exact hbandNamed
  let R := Protocol.get_fg_root st.toHealing.toFG
  have hheadsR : ∀ x ∈ rho.honest,
      Block.Preceq R (voterHeadAt S rho x d) := by
    intro x hx
    simpa only [R, st, read, t, s, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      voteDutyHead] using
      fgRootAtRead_preceq_voteDutyHead_of_gstZero_named
        S h.core h.committees h.gstZero h.windows hconfHor hd hupper
          (t := t) (le_refl _) hv hx
  have hvotePrev : Protocol.vote_time S.E d ≤ rho.horizon :=
    (vote_time_mono_slots S.E (Nat.le_succ d)).trans hhor
  have hprotectedR : ProtectedVoteSlot S rho d R := by
    refine ⟨hheadsR, ?_⟩
    intro x hx hxCommittee
    obtain ⟨X, hXerase, hXrun, hXemit⟩ :=
      WeakGoldfish.voterHead_runBlock_and_emits
        S h.core hx hdPos hxCommittee hvotePrev
    exact ⟨X, by simpa only [hXerase] using hheadsR x hx, hXrun, hXemit⟩
  have hRparent := protected_preceq_proposedParent_of_gstZero_named
    S h hconfHor hd hupper hproposalHor hprop hprotectedR
  have hroot : Block.Preceq
      (Protocol.get_fg_root st.toHealing.toFG) B.erase := by
    simpa only [R] using Block.preceq_trans hRparent hparentBlock
  exact (WeakJoint.namedCandidatePath_of_processedBandDescendant_core
    S h.core hv (s := d) (C := B.erase) (D := B.erase)
      (Block.preceq_self _) hprocessed
      (by simpa only [st, read, s] using hband)
      (by simpa only [st, read, s] using hroot)).1

#print axioms proposedBlock_voterCandidate_of_gstZero_named

end WeakGenesis
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
