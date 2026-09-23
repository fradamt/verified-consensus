module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.PreparedV4ActionHead
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.WeakProposalCandidateNamed
public import DecoupledConsensusProofs.Protocol.Grades.WeakProposalPivotNamed
public import DecoupledConsensusProofs.Execution.WeakGenesisCanonicalProposalDutyPins
public import DecoupledConsensusProofs.Protocol.Schedule.WeakGenesisVoteStoresSuccPins
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.WeakConfirmationReadBandCandidateNamed
public import DecoupledConsensusProofs.Generic.WeakProposalAdmissionNamed

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Prepared V4 canonical proposal duties -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic Statements Proofs.HealingLemmas
open Internal.NamedRecoveryRead Internal.PhaseGrades
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem preparedV4_voteTime_lt_nextProposal_duty
    (E : Env V) (s : Slot) :
    Protocol.vote_time E s < Protocol.proposal_time E (s + 1) := by
  apply lt_trans ?_ (support_cutoff_lt_proposal_time_succ E s)
  rw [← vote_time_add_delta]
  exact Int.lt_add_of_pos_right _ E.Δ_pos

private theorem SettledBootstrapPreparedV4.proposedBlock_admittedBefore_vote_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start d : Slot}
    {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hd : start ≤ d)
    (hhor : Protocol.vote_time S.E (d + 1) ≤ rho.horizon)
    (hprop : S.E.proposer (d + 1) ∈ rho.honest)
    {B : NamedBlock V} (hB : proposedBlockAt S rho (d + 1) = some B)
    {v : V} (hv : v ∈ rho.honest) :
    AdmittedBefore S rho v B.erase (Protocol.vote_time S.E (d + 1)) := by
  have hcutpos : 0 < base + S.hc.η_SG :=
    Nat.zero_lt_of_lt (Nat.add_lt_add_left S.hc.η_SG_ge_one base)
  have hRpos : 0 < S.hc.R :=
    lt_of_lt_of_le (by decide : 0 < 2) S.hc.R_ge_two
  have hdPos : 0 < d :=
    (Nat.mul_pos hcutpos hRpos).trans_le (hboot.settled.trans hd)
  have hconfHor : Protocol.confirmation_time S.E (d - 1) ≤ rho.horizon :=
    (confirmationTime_lt_nextVote_of_lt S.E
      (Nat.sub_lt hdPos (by decide))).le.trans hhor
  have hupper : d ≤ (d - 1) + 1 := by
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hdPos))]
  have hpost : S.E.t_GST ≤ Protocol.proposal_time S.E (d + 1) :=
    hboot.basePost.trans
      ((Assembly.a_mono S (Nat.le_sub_of_add_le
        (Nat.add_le_add_left S.hc.η_SG_ge_one base))).trans
        ((windowSourceTime_le_vote_of_opening_le S hcutpos
          (hboot.settled.trans hd)).trans
            (preparedV4_voteTime_lt_nextProposal_duty S.E d).le))
  let R := Protocol.get_fg_root
    (voteDutyRead S rho v (d + 1)).st.core.toHealing.toFG
  have hread : min (S.a (base + S.hc.η_SG))
      (Protocol.vote_time S.E start) ≤ Protocol.vote_time S.E (d + 1) :=
    (min_le_right _ _).trans
      (vote_time_mono_slots S.E (hd.trans (Nat.le_succ d)))
  have hheads : ∀ x ∈ rho.honest,
      Block.Preceq R (voterHeadAt S rho x d) := by
    intro x hx
    simpa only [R, voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      SettledBootstrapPreparedV4.fgRootAtRead_preceq_voteDutyHead_core
        S adm hcom hboot hawake hfinality hconfHor hd hupper hread
          (le_refl _) hv hx
  have hvotePrev : Protocol.vote_time S.E d ≤ rho.horizon :=
    (vote_time_mono_slots S.E (Nat.le_succ d)).trans hhor
  have hprotected : ProtectedVoteSlot S rho d R := by
    refine ⟨hheads, ?_⟩
    intro x hx hxCommittee
    obtain ⟨X, hXerase, hXrun, hXemit⟩ :=
      WeakGoldfish.voterHead_runBlock_and_emits
        S adm hx hdPos hxCommittee hvotePrev
    exact ⟨X, by simpa only [hXerase] using hheads x hx, hXrun, hXemit⟩
  have hproposalHor : Protocol.proposal_time S.E (d + 1) ≤ rho.horizon :=
    (proposal_time_lt_vote_time S.E (d + 1)).le.trans hhor
  have hparent : Block.Preceq R (proposedParent S rho (d + 1)) :=
    SettledBootstrapPreparedV4.protected_preceq_proposedParent_core
      S adm hcom hboot hawake hfinality hconfHor hd hupper
        hproposalHor hprop hprotected
  have hparentBlock : Block.Preceq (proposedParent S rho (d + 1)) B.erase :=
    proposedParent_preceq_proposedBlockAt S rho (d + 1) hB
  apply WeakGenesis.proposedBlock_admittedBefore_vote_of_fgRootRead_named_core
    S adm (Nat.zero_lt_succ d) hprop hpost hhor hB hv
  simpa only [R, voteDutyRead, NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      Block.preceq_trans hparent hparentBlock

private theorem SettledBootstrapPreparedV4.proposedBlock_voterCandidate_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start d : Slot}
    {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hd : start ≤ d)
    (hhor : Protocol.vote_time S.E (d + 1) ≤ rho.horizon)
    (hprop : S.E.proposer (d + 1) ∈ rho.honest)
    {B : NamedBlock V} (hB : proposedBlockAt S rho (d + 1) = some B)
    {v : V} (hv : v ∈ rho.honest) :
    B.erase ∈ voterCandidateTreeAt S rho v (d + 1) := by
  let s := d + 1
  let t := Protocol.vote_time S.E s
  let read := voteDutyRead S rho v s
  let st := read.st.core
  have hcutpos : 0 < base + S.hc.η_SG :=
    Nat.zero_lt_of_lt (Nat.add_lt_add_left S.hc.η_SG_ge_one base)
  have hRpos : 0 < S.hc.R :=
    lt_of_lt_of_le (by decide : 0 < 2) S.hc.R_ge_two
  have hdPos : 0 < d :=
    (Nat.mul_pos hcutpos hRpos).trans_le (hboot.settled.trans hd)
  have hconfHor : Protocol.confirmation_time S.E (d - 1) ≤ rho.horizon :=
    (confirmationTime_lt_nextVote_of_lt S.E
      (Nat.sub_lt hdPos (by decide))).le.trans hhor
  have hupper : d ≤ (d - 1) + 1 := by
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hdPos))]
  have hproposalHor : Protocol.proposal_time S.E s ≤ rho.horizon :=
    (proposal_time_lt_vote_time S.E s).le.trans hhor
  have hBrun : RunBlock S rho B :=
    proposedBlockAt_blockInRun_of_admissible
      S adm s (Nat.zero_lt_succ d) hprop hproposalHor hB
  have hadmit := SettledBootstrapPreparedV4.proposedBlock_admittedBefore_vote_core
    S adm hcom hboot hawake hfinality hd hhor hprop hB hv
  have hBT0 := (admittedBefore_mem_and_stamp_at
    S adm.toNamedScheduleWellFormed hadmit (le_refl t)).1
  have hBT : B.erase ∈ st.T := by
    simpa only [st, read, t, s, voteDutyRead,
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
        Proofs.Optimistic.tickStore, st, read, t, s, voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock] using hBT
    · refine ⟨?_, ?_⟩
      · simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
          Proofs.Optimistic.tickStore, st, read, t, s, voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom,
          Protocol.NamedStore.setClock] using hBT
      · rw [Proofs.NamedWire.erase_slot, proposedBlockAt_slot S rho s hB,
          Proofs.Optimistic.toHealing_slot]
        exact (Proofs.Optimistic.voteDutyStore_slot S rho v s).symm
  obtain ⟨B', hB'body, hB'erase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho t v (by
      simpa only [st, read, t, voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
        using hBT)
  obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedScheduleWellFormed.sorted t
  have hB'prefix : B' ∈ (NamedRun.stateBefore S rho n v).st.bodies := by
    rw [← congrFun hn v]
    exact hB'body
  have hB'run : RunBlock S rho B' :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hv hB'prefix
  have hB'eq : B' = B := by
    apply adm.toNamedRootCollisionFree.root_injective B' B hB'run hBrun
      B' B (Or.inl (Proofs.NamedAncestry.named_self B'))
        (Or.inr (Proofs.NamedAncestry.named_self B))
    rw [← Proofs.NamedWire.erase_root B', ← Proofs.NamedWire.erase_root B, hB'erase]
  have hBbody : B ∈ (rho.storeBeforeTime S v t).bodies := by
    rw [← hB'eq]
    exact hB'body
  have hBview : (st.σ B.erase).h =
      (Protocol.derive_named S.E S.cfg B).h := by
    have hvw := Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho t v B hBbody
    simpa only [st, read, t, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      congrArg (fun z => z.h) hvw
  have hparentBlock : Block.Preceq (proposedParent S rho s) B.erase :=
    proposedParent_preceq_proposedBlockAt S rho s hB
  have hPparent : Block.Preceq P.erase (proposedParent S rho s) := by
    have hPslot := (SettledBootstrapPreparedV4.protectedVoteSlots_core
      S adm hcom hboot hawake hfinality hconfHor d hd hupper).1
    exact SettledBootstrapPreparedV4.protected_preceq_proposedParent_core
      S adm hcom hboot hawake hfinality hconfHor hd hupper
        hproposalHor hprop hPslot
  have hPB : Block.Preceq P.erase B.erase :=
    Block.preceq_trans hPparent hparentBlock
  obtain ⟨P', hP'B, hP'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hPB
  have hP'run : RunBlock S rho P' :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hBrun hP'B
  have hP'eq : P' = P := by
    apply adm.toNamedRootCollisionFree.root_injective P' P hP'run hboot.runBlock
      P' P (Or.inl (Proofs.NamedAncestry.named_self P'))
        (Or.inr (Proofs.NamedAncestry.named_self P))
    rw [← Proofs.NamedWire.erase_root P', ← Proofs.NamedWire.erase_root P, hP'erase]
  have hPheight : (Protocol.derive_named S.E S.cfg P).h ≤
      (Protocol.derive_named S.E S.cfg B).h := by
    apply Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg
    rw [← hP'eq]
    exact hP'B
  have hbandNamed : st.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg B).h := by
    by_cases hlarge : 1 < st.h_max
    · have hmajority := honestWeightMajority_of_finiteWindowsFrom
        S hawake hcutpos (hboot.settled.trans hd) hupper hconfHor
      obtain ⟨a, ta, D, K, ha, hemit, hat, hrow, hfgK, -, -, hKentry,
          hKrun, hKheight⟩ := frontier_confirmationWitness_core_entry
        S adm hmajority (v := v) (time := t) (by
          simpa only [st, read, t, voteDutyRead,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
            using hlarge)
      have haTime : S.a a.round < Protocol.vote_time S.E s := by
        have htime : ta = S.a a.round := (emits_attest_shape S hemit).2
        rw [← htime]
        exact hat
      by_cases hold : a.round < base + S.hc.η_SG
      · by_cases hpre : a.round < fresh
        · have hbound := hboot.oldRows a ta _ ha hemit hpre hrow
          have hbound' : st.h_max - 1 ≤ cap := by
            simpa only [st, read, t, voteDutyRead,
              NamedActionReads.confirmationReadAt,
              NamedActionReads.confirmationReadFrom,
              Protocol.NamedStore.setClock] using hbound
          exact hbound'.trans (hboot.heightCap.trans hPheight)
        · have hKP := hboot.fgAll a ta _
              (Protocol.derive_named S.E S.cfg K).T_h
              ha hemit hrow (Nat.le_of_not_gt hpre) hold hfgK
          rw [hKentry] at hKP
          have hKB : Block.Preceq K.erase B.erase := Block.preceq_trans hKP hPB
          obtain ⟨K', hK'B, hK'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hKB
          have hK'run : RunBlock S rho K' :=
            Proofs.NamedRuntime.blockInRun_of_ancestor S rho hBrun hK'B
          have hK'eq : K' = K := by
            apply adm.toNamedRootCollisionFree.root_injective K' K hK'run hKrun
              K' K (Or.inl (Proofs.NamedAncestry.named_self K'))
                (Or.inr (Proofs.NamedAncestry.named_self K))
            rw [← Proofs.NamedWire.erase_root K', ← Proofs.NamedWire.erase_root K, hK'erase]
          change (rho.storeBeforeTime S v t).core.h_max - 1 ≤
            (Protocol.derive_named S.E S.cfg B).h
          rw [← hKheight]
          exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg (by
            rw [← hK'eq]
            exact hK'B)
      · have hKheads : ∀ x ∈ rho.honest,
            Block.Preceq K.erase (voterHeadAt S rho x d) := by
          intro x hx
          have hsafe := ((SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_core
            S adm hcom hboot hawake hfinality hconfHor hd hupper hx
              a.round (Nat.le_of_not_gt hold) haTime).2 a.val_index ha).2 _ hfgK
          rw [← hKentry]
          simpa only [voteDutyHead] using hsafe
        have hKprotected : ProtectedVoteSlot S rho d K.erase := by
          refine ⟨hKheads, ?_⟩
          intro x hx hxc
          obtain ⟨Y, hYe, hYrun, hYemit⟩ :=
            WeakGoldfish.voterHead_runBlock_and_emits
              S adm hx hdPos hxc
                ((vote_time_mono_slots S.E (Nat.le_succ d)).trans hhor)
          exact ⟨Y, by simpa only [hYe] using hKheads x hx, hYrun, hYemit⟩
        have hKparent :=
          SettledBootstrapPreparedV4.protected_preceq_proposedParent_core
            S adm hcom hboot hawake hfinality hconfHor hd hupper
              hproposalHor hprop hKprotected
        have hKB : Block.Preceq K.erase B.erase :=
          Block.preceq_trans hKparent hparentBlock
        obtain ⟨K', hK'B, hK'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hKB
        have hK'run : RunBlock S rho K' :=
          Proofs.NamedRuntime.blockInRun_of_ancestor S rho hBrun hK'B
        have hK'eq : K' = K := by
          apply adm.toNamedRootCollisionFree.root_injective K' K hK'run hKrun
            K' K (Or.inl (Proofs.NamedAncestry.named_self K'))
              (Or.inr (Proofs.NamedAncestry.named_self K))
          rw [← Proofs.NamedWire.erase_root K', ← Proofs.NamedWire.erase_root K, hK'erase]
        change (rho.storeBeforeTime S v t).core.h_max - 1 ≤
          (Protocol.derive_named S.E S.cfg B).h
        rw [← hKheight]
        exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg (by
          rw [← hK'eq]
          exact hK'B)
    · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hlarge)]
      exact Nat.zero_le _
  have hband : st.h_max - 1 ≤ (st.σ B.erase).h := by
    rw [hBview]
    exact hbandNamed
  let R := Protocol.get_fg_root st.toHealing.toFG
  have hread : min (S.a (base + S.hc.η_SG))
      (Protocol.vote_time S.E start) ≤ t :=
    (min_le_right _ _).trans
      (vote_time_mono_slots S.E (hd.trans (Nat.le_succ d)))
  have hheadsR : ∀ x ∈ rho.honest,
      Block.Preceq R (voterHeadAt S rho x d) := by
    intro x hx
    simpa only [R, st, read, t, s, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      voteDutyHead] using
      SettledBootstrapPreparedV4.fgRootAtRead_preceq_voteDutyHead_core
        S adm hcom hboot hawake hfinality hconfHor hd hupper hread
          (le_refl _) hv hx
  have hvotePrev : Protocol.vote_time S.E d ≤ rho.horizon :=
    (vote_time_mono_slots S.E (Nat.le_succ d)).trans hhor
  have hprotectedR : ProtectedVoteSlot S rho d R := by
    refine ⟨hheadsR, ?_⟩
    intro x hx hxc
    obtain ⟨Y, hYe, hYrun, hYemit⟩ :=
      WeakGoldfish.voterHead_runBlock_and_emits
        S adm hx hdPos hxc hvotePrev
    exact ⟨Y, by simpa only [hYe] using hheadsR x hx, hYrun, hYemit⟩
  have hRparent := SettledBootstrapPreparedV4.protected_preceq_proposedParent_core
    S adm hcom hboot hawake hfinality hconfHor hd hupper
      hproposalHor hprop hprotectedR
  have hroot : Block.Preceq
      (Protocol.get_fg_root st.toHealing.toFG) B.erase := by
    simpa only [R] using Block.preceq_trans hRparent hparentBlock
  exact (WeakJoint.namedCandidatePath_of_processedBandDescendant_core
    S adm hv (s := d) (C := B.erase) (D := B.erase)
      (Block.preceq_self _) hprocessed
      (by simpa only [st, read, s] using hband)
      (by simpa only [st, read, s] using hroot)).1

private theorem SettledBootstrapPreparedV4.preparedVoterAnchor_preceq_previousHead_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start last d : Slot}
    {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hd : start ≤ d) (hupper : d ≤ last + 1)
    (hvoteHor : Protocol.vote_time S.E (d + 1) ≤ rho.horizon)
    {w x : V} (hw : w ∈ rho.honest) (hx : x ∈ rho.honest) :
    Block.Preceq (voterAnchorAt S rho w (d + 1))
      (voterHeadAt S rho x d) := by
  let s := d + 1
  let t := Protocol.vote_time S.E s
  let read := voteDutyRead S rho w s
  let r := S.hc.round_of s
  have hroundT : S.hc.round_of (S.E.slotOf t) = r := by
    simpa only [t, r, Proofs.Optimistic.slotOf_vote_time]
  have hreadRound : S.hc.round_of read.st.core.s = r := by
    simpa only [read, voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.slotOf_vote_time, r, t]
  have hdomain : domain S.E S.hc r .g1 < t := by
    rw [NamedOutageClosure.domain_g1_eq_opening]
    exact (proposal_time_mono S.E (Nat.div_mul_le_self s S.hc.R)).trans_lt
      (proposal_time_lt_vote_time S.E s)
  have htop : t ≤ opening S.E S.hc (r + 1) := by
    simpa only [NamedOutageClosure.clockRoundAt, hroundT] using
      (NamedOutageClosure.clockRound_lt_opening_succ S t).le
  have hdomainHor : domain S.E S.hc r .g1 ≤ rho.horizon :=
    hdomain.le.trans hvoteHor
  have hRpos : 0 < S.hc.R :=
    lt_of_lt_of_le (by decide : 0 < 2) S.hc.R_ge_two
  have hcutpos : 0 < base + S.hc.η_SG :=
    Nat.zero_lt_of_lt (Nat.add_lt_add_left S.hc.η_SG_ge_one base)
  have hroundCut : base + S.hc.η_SG ≤ r := by
    change base + S.hc.η_SG ≤ s / S.hc.R
    exact (Nat.le_div_iff_mul_le hRpos).2
      ((hboot.settled.trans hd).trans (Nat.le_succ d))
  have hr : 0 < r := hcutpos.trans_le hroundCut
  have hspan : base ≤ r - S.hc.η_SG := Nat.le_sub_of_add_le hroundCut
  have hbasePred : base ≤ r - 1 :=
    hspan.trans (Nat.sub_le_sub_left S.hc.η_SG_ge_one r)
  have hread : min (S.a (base + S.hc.η_SG))
      (Protocol.vote_time S.E start) ≤ t :=
    (min_le_right _ _).trans
      (vote_time_mono_slots S.E (hd.trans (Nat.le_succ d)))
  have hfg : Block.Preceq
      (Protocol.get_fg_root read.st.core.toHealing.toFG)
      (voterHeadAt S rho x d) := by
    simpa only [read, t, s, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      SettledBootstrapPreparedV4.fgRootAtRead_preceq_voteDutyHead_core
        S adm hcom hboot hawake hfinality hhor hd hupper hread
          (le_refl _) hw hx
  rcases voterAnchorAt_cases S rho w s with hanchorFG |
      ⟨raw, A, hframe, hactive, hanchorA⟩
  · rw [show voterAnchorAt S rho w s =
        Protocol.get_fg_root read.st.core.toHealing.toFG by
          simpa only [read] using hanchorFG]
    exact hfg
  · have hanchorA' : voterAnchorAt S rho w s = A := by
      simpa only [read] using hanchorA
    rw [hanchorA']
    have hAraw : Block.Preceq A raw := by
      unfold activePrefix at hactive
      exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).2
    have hframeR := hframe
    change (DecoupledConsensusModel.Protocol.readFrame read.cache read.st.core.toHealing
      (S.hc.round_of read.st.core.s)).g1 = some (some raw) at hframeR
    rw [hreadRound] at hframeR
    have hgrade := WeakSG.phaseGrade_of_preparedFrame_g1
      S rho adm w hw r hr t hroundT hdomain htop hdomainHor
        (raw := raw) (by simpa only [read, voteDutyRead, t] using hframeR)
    have hpostEarly : S.E.t_GST ≤ early S.E S.hc r .g2 := by
      exact hboot.basePost.trans (Assembly.a_mono S hbasePred) |>.trans
        (le_add_of_nonneg_right S.E.Δ_pos.le) |>.trans
          (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
            (Nat.sub_lt hr (by decide)))
    have hdelivery : TwoCutoffDelivery S rho r :=
      twoCutoffDelivery_of_core S adm hpostEarly
    have hprevHor : S.a (r - 1) ≤ rho.horizon := by
      have hprev : S.a (r - 1) + S.E.Δ ≤ early S.E S.hc r .g1 :=
        (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
          (Nat.sub_lt hr (by decide))).trans
          (NamedOutageClosure.q10_early_g2_le_early_g1 S r)
      exact (le_add_of_nonneg_right S.E.Δ_pos.le).trans
        (hprev.trans ((NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1
          S r).trans hdomainHor))
    have hslot := SettledBootstrapPreparedV4.protectedVoteSlots_core
      S adm hcom hboot hawake hfinality hhor d hd hupper
    have hcarrier := relativeGradeCarrierAt_of_awakeWindowMajority
      S adm hr (hawake r hroundCut hprevHor) (p := .g1) (by
        intro y hy u hu k hk huk
        have hklt : k < r := mem_latestWindow_lt hk
        have hbaseK : base ≤ k :=
          hspan.trans (WeakSG.mem_latestWindow_lower_bound hk)
        have hdeadline : S.a k + S.E.Δ ≤ early S.E S.hc r .g1 :=
          (NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three hklt).trans
            (NamedOutageClosure.q10_early_g2_le_early_g1 S r)
        have hactionTime : S.a k < Protocol.vote_time S.E s :=
          (Int.lt_add_of_pos_right _ S.E.Δ_pos).trans_le
            (hdeadline.trans
              ((NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1
                S r).trans hdomain.le))
        have hem := honest_emits_exact_actionAttestationAt_of_awake S
          adm.toNamedScheduleWellFormed hu k huk (by
            exact (le_add_of_nonneg_right S.E.Δ_pos.le).trans
              (hdeadline.trans
                ((NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1
                  S r).trans hdomainHor)))
        have hAhead : Block.Preceq (actionSGBlockAt S rho u k)
            (voterHeadAt S rho x d) := by
          by_cases hold : k < base + S.hc.η_SG
          · exact Block.preceq_trans (hboot.sgBoot k hbaseK hold u hu hem)
              (hslot.1.heads x hx)
          · exact (SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_core
              S adm hcom hboot hawake hfinality hhor hd hupper hx
                k (Nat.le_of_not_gt hold) hactionTime).1 u hu hem
        have hfgY := SettledBootstrapPreparedV4.fgRootAtRead_preceq_voteDutyHead_core
          S adm hcom hboot hawake hfinality hhor hd hupper hread
            (le_refl _) hy hx
        have hFmonoY : Block.Preceq
            (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) y).st.core.F
            (NamedRun.stateBeforeTime S rho t y).st.core.F :=
          NamedOutageClosure.incl_strict_F_mono S rho
            adm.toNamedScheduleWellFormed y hdomain.le
        have hFJY := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
          S rho t y
        have hFrootY : Block.Preceq
            (NamedRun.stateBeforeTime S rho t y).st.core.F
            (Protocol.get_fg_root
              (NamedRun.stateBeforeTime S rho t y).st.core.toHealing.toFG) :=
          Proofs.Records.preceq_get_fg_root_of_F (st :=
            (NamedRun.stateBeforeTime S rho t y).st.core.toHealing.toFG) hFJY
        have hFheadY : Block.Preceq
            (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) y).st.core.F
            (voterHeadAt S rho x d) :=
          Block.preceq_trans hFmonoY (Block.preceq_trans hFrootY hfgY)
        exact NamedOutageClosure.honestRoundVote_interpreted_at_reader_of_twoCutoff_compatible_after
          S rho adm hboot.basePost hdelivery r k hbaseK .g1 hk y hy
            hdomainHor hdeadline
            ((Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u k).mpr
              ⟨hu, actionAttestationAt S rho u k,
                (actionAttestationAt_shape S rho u k).1,
                (actionAttestationAt_shape S rho u k).2.1, hem⟩)
            (Block.compatible_of_preceq_common hFheadY hAhead))
    obtain ⟨k, hk, u, hu, hemit, hraw⟩ := hcarrier w hw raw
      (by simpa only [PhaseGrades.phaseGrade] using hgrade)
    have hklt : k < r := mem_latestWindow_lt hk
    have hbaseK : base ≤ k :=
      hspan.trans (WeakSG.mem_latestWindow_lower_bound hk)
    have hactionTime : S.a k < Protocol.vote_time S.E s := by
      calc
        S.a k < S.a k + S.E.Δ := Int.lt_add_of_pos_right _ S.E.Δ_pos
        _ ≤ early S.E S.hc r .g2 :=
          NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three hklt
        _ ≤ early S.E S.hc r .g1 :=
          NamedOutageClosure.q10_early_g2_le_early_g1 S r
        _ ≤ domain S.E S.hc r .g1 :=
          NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1 S r
        _ < t := hdomain
    by_cases hold : k < base + S.hc.η_SG
    · exact Block.preceq_trans hAraw (Block.preceq_trans hraw
        (Block.preceq_trans (hboot.sgBoot k hbaseK hold u hu hemit)
          (hslot.1.heads x hx)))
    · exact Block.preceq_trans hAraw (Block.preceq_trans hraw
        ((SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_core
          S adm hcom hboot hawake hfinality hhor hd hupper hx
            k (Nat.le_of_not_gt hold) hactionTime).1 u hu hemit))

private theorem SettledBootstrapPreparedV4.exists_protectedProposalPivot_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start d : Slot}
    {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hd : start ≤ d)
    (hhor : Protocol.confirmation_time S.E (d + 1) ≤ rho.horizon)
    (hprop : S.E.proposer (d + 1) ∈ rho.honest)
    {v : V} (hv : v ∈ rho.honest) :
    ∃ A : NamedBlock V, PreparedProtectedProposalPivot S rho d v A := by
  let s := d + 1
  let tp := Protocol.proposal_time S.E s
  let tv := Protocol.vote_time S.E s
  let p := S.E.proposer s
  let source := proposerReadAt S rho s
  let target := voteDutyRead S rho v s
  have hcutpos : 0 < base + S.hc.η_SG :=
    Nat.zero_lt_of_lt (Nat.add_lt_add_left S.hc.η_SG_ge_one base)
  have hRpos : 0 < S.hc.R :=
    lt_of_lt_of_le (by decide : 0 < 2) S.hc.R_ge_two
  have hdPos : 0 < d :=
    (Nat.mul_pos hcutpos hRpos).trans_le (hboot.settled.trans hd)
  have hp : p ∈ rho.honest := by simpa only [p, s] using hprop
  have hvoteHor : tv ≤ rho.horizon := by
    simpa only [tv] using (vote_time_le_confirmation_time S.E s).trans hhor
  have hproposalHor : tp ≤ rho.horizon := by
    simpa only [tp, tv] using
      (proposal_time_lt_vote_time S.E s).le.trans hvoteHor
  have hvotePrev : Protocol.vote_time S.E d ≤ rho.horizon :=
    (vote_time_mono_slots S.E (Nat.le_succ d)).trans hvoteHor
  have hupper : d ≤ (d + 1) + 1 := Nat.le_add_right d 2
  let sourceAnchor := nodeAnchor S source (S.hc.round_of source.st.core.s)
  let targetAnchor := voterAnchorAt S rho v s
  have hsourceHeads : ∀ x ∈ rho.honest,
      Block.Preceq sourceAnchor (voterHeadAt S rho x d) := by
    intro x hx
    simpa only [sourceAnchor, source, s, voteDutyHead] using
      SettledBootstrapPreparedV4.preparedProposalAnchor_preceq_voteDutyHead_core
        S adm hcom hboot hawake hfinality hhor hd hupper
          hproposalHor hprop hx
  have htargetHeads : ∀ x ∈ rho.honest,
      Block.Preceq targetAnchor (voterHeadAt S rho x d) := by
    intro x hx
    exact SettledBootstrapPreparedV4.preparedVoterAnchor_preceq_previousHead_core
      S adm hcom hboot hawake hfinality hhor hd hupper hvoteHor hv hx
  have protected_of_heads {C : Block V}
      (hheads : ∀ x ∈ rho.honest,
        Block.Preceq C (voterHeadAt S rho x d)) :
      ProtectedVoteSlot S rho d C := by
    refine ⟨hheads, ?_⟩
    intro x hx hxCommittee
    obtain ⟨X, hXerase, hXrun, hXemit⟩ :=
      WeakGoldfish.voterHead_runBlock_and_emits
        S adm hx hdPos hxCommittee hvotePrev
    exact ⟨X, by simpa only [hXerase] using hheads x hx, hXrun, hXemit⟩
  have hsource : ProtectedVoteSlot S rho d sourceAnchor :=
    protected_of_heads hsourceHeads
  have htarget : ProtectedVoteSlot S rho d targetAnchor :=
    protected_of_heads htargetHeads
  have hpos : 0 < ((S.E.committee d) ∩ rho.honest).card := by
    have hc := hcom d
    omega
  obtain ⟨x0, hx0⟩ := Finset.card_pos.mp hpos
  have hx0Committee := (Finset.mem_inter.mp hx0).1
  have hx0Honest := (Finset.mem_inter.mp hx0).2
  obtain ⟨G, hG, hmax⟩ := greatest_member_of_common_ancestor_bound
    (ProtectedVoteSlot S rho d) hsource
      (fun C hC => hC.heads x0 hx0Honest)
  obtain ⟨X0, hX0erase, hX0run, hX0emit⟩ :=
    WeakGoldfish.voterHead_runBlock_and_emits
      S adm hx0Honest hdPos hx0Committee hvotePrev
  have hGX0 : Block.Preceq G X0.erase := by
    rw [hX0erase]
    exact hG.heads x0 hx0Honest
  obtain ⟨A, hAX0, hAerased⟩ := Proofs.NamedAncestry.erased_ancestor_lift X0 hGX0
  have hArun : RunBlock S rho A :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hX0run hAX0
  have hAprotected : ProtectedVoteSlot S rho d A.erase := by
    rw [hAerased]
    exact hG
  have hsourceAnchor : Block.Preceq sourceAnchor A.erase := by
    rw [hAerased]
    exact hmax sourceAnchor hsource
  have htargetAnchor : Block.Preceq targetAnchor A.erase := by
    rw [hAerased]
    exact hmax targetAnchor htarget
  have hPslot := (SettledBootstrapPreparedV4.protectedVoteSlots_core
    S adm hcom hboot hawake hfinality hhor d hd hupper).1
  have hPG : Block.Preceq P.erase G := hmax P.erase hPslot
  have hPA : Block.Preceq P.erase A.erase := by
    simpa only [hAerased] using hPG
  obtain ⟨P', hP'A, hP'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift A hPA
  have hP'run : RunBlock S rho P' :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hArun hP'A
  have hP'eq : P' = P := by
    apply adm.toNamedRootCollisionFree.root_injective P' P hP'run hboot.runBlock
      P' P (Or.inl (Proofs.NamedAncestry.named_self P'))
        (Or.inr (Proofs.NamedAncestry.named_self P))
    rw [← Proofs.NamedWire.erase_root P', ← Proofs.NamedWire.erase_root P, hP'erase]
  have hPheight : (Protocol.derive_named S.E S.cfg P).h ≤
      (Protocol.derive_named S.E S.cfg A).h := by
    apply Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg
    rw [← hP'eq]
    exact hP'A
  have availableAt (w : V) (hw : w ∈ rho.honest) :
      HonestHeadsAvailableBefore S rho d w (Protocol.support_cutoff S.E d) := by
    let R := Protocol.get_fg_root
      (voteDutyRead S rho w s).st.core.toHealing.toFG
    have hread : min (S.a (base + S.hc.η_SG))
        (Protocol.vote_time S.E start) ≤ tv :=
      (min_le_right _ _).trans
        (by simpa only [tv, s] using
          vote_time_mono_slots S.E (hd.trans (Nat.le_succ d)))
    have hRheads : ∀ x ∈ rho.honest,
        Block.Preceq R (voterHeadAt S rho x d) := by
      intro x hx
      simpa only [R, s, tv, voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
        SettledBootstrapPreparedV4.fgRootAtRead_preceq_voteDutyHead_core
          S adm hcom hboot hawake hfinality hhor hd hupper hread
            (le_refl _) hw hx
    have hconeR : NamedHonestVotesCone S rho d (fun X => Block.Preceq R X) := by
      intro x hx hxc
      obtain ⟨X, hXe, hXrun, hXemit⟩ :=
        WeakGoldfish.voterHead_runBlock_and_emits
          S adm hx hdPos hxc hvotePrev
      exact ⟨X, by simpa only [hXe] using hRheads x hx, hXrun, hXemit⟩
    have hbaseLt : base < base + S.hc.η_SG :=
      Nat.lt_of_succ_le (Nat.add_le_add_left S.hc.η_SG_ge_one base)
    have hpost : S.E.t_GST ≤ Protocol.vote_time S.E d :=
      hboot.basePost.trans
        ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
          ((action_add_delta_le_openingProposal_of_round_lt S hbaseLt).trans
            ((proposal_time_mono S.E (hboot.settled.trans hd)).trans
              (proposal_time_lt_vote_time S.E d).le)))
    have hcut : Protocol.support_cutoff S.E d ≤ rho.horizon :=
      (support_cutoff_le_vote_time_succ S.E d).trans hvoteHor
    exact honestHeadsAvailableBefore_of_namedPostHealingCone_core
      S adm hw hpost hcut (B := R) (Block.preceq_self R) hconeR
  have bodyAt (w : V) (hw : w ∈ rho.honest) (time : Time)
      (hcutTime : Protocol.support_cutoff S.E d ≤ time) :
      A ∈ (rho.storeBeforeTime S w time).bodies := by
    have hresolve := headsResolveIn_storeBeforeTime_of_availableBefore_at_core
      S adm hw d hcutTime (availableAt w hw)
    have hX0head : HonestHead S rho d X0.erase :=
      ⟨x0, hx0Honest, hx0Committee, ⟨X0, rfl, hX0run⟩, hX0emit⟩
    obtain ⟨hfind, -⟩ := hresolve X0.erase hX0head
    have hX0T : X0.erase ∈ (rho.storeBeforeTime S w time).core.T :=
      Proofs.HealingLemmas.find?_mem hfind
    have hpc := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho time w
    have hAT : A.erase ∈ (rho.storeBeforeTime S w time).core.T :=
      Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
        A.erase X0.erase hX0T (by simpa only [hAerased] using hGX0)
    obtain ⟨A', hA'body, hA'erase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho time w hAT
    obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
      adm.toNamedScheduleWellFormed.sorted time
    have hA'prefix : A' ∈ (NamedRun.stateBefore S rho n w).st.bodies := by
      rw [← congrFun hn w]
      exact hA'body
    have hA'run : RunBlock S rho A' :=
      Proofs.Bridges.runBlock_of_stateBefore_mem S hw hA'prefix
    have hA'eq : A' = A := by
      apply adm.toNamedRootCollisionFree.root_injective A' A hA'run hArun
        A' A (Or.inl (Proofs.NamedAncestry.named_self A'))
          (Or.inr (Proofs.NamedAncestry.named_self A))
      rw [← Proofs.NamedWire.erase_root A', ← Proofs.NamedWire.erase_root A, hA'erase]
    rw [← hA'eq]
    exact hA'body
  have hsourceBody0 := bodyAt p hp tp
    (by simpa only [tp, s] using support_cutoff_le_proposal_time_succ S.E d)
  have hsourceBody : A ∈ source.st.bodies := by
    simpa only [source, proposerReadAt, tp, p, s,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      hsourceBody0
  have htargetBody0 := bodyAt v hv tv
    (by simpa only [tv, s] using support_cutoff_le_vote_time_succ S.E d)
  have htargetBody : A ∈ target.st.bodies := by
    simpa only [target, voteDutyRead, tv, s,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      htargetBody0
  have bandAt (w : V) (hw : w ∈ rho.honest) (time : Time)
      (htime : time ≤ tv) :
      (rho.storeBeforeTime S w time).core.h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg A).h := by
    by_cases hlarge : 1 < (rho.storeBeforeTime S w time).core.h_max
    · have hmajority := honestWeightMajority_of_finiteWindowsFrom
        S hawake hcutpos (hboot.settled.trans hd) hupper hhor
      obtain ⟨a, ta, D, K, ha, hemit, hat, hrow, hfgK, -, -, hKentry,
          hKrun, hKheight⟩ := frontier_confirmationWitness_core_entry
        S adm hmajority hlarge
      have haTime : S.a a.round < Protocol.vote_time S.E s := by
        have hta : ta = S.a a.round := (emits_attest_shape S hemit).2
        rw [← hta]
        exact hat.trans_le htime
      by_cases hold : a.round < base + S.hc.η_SG
      · by_cases hpre : a.round < fresh
        · have hbound := hboot.oldRows a ta _ ha hemit hpre hrow
          exact hbound.trans (hboot.heightCap.trans hPheight)
        · have hKP := hboot.fgAll a ta _
              (Protocol.derive_named S.E S.cfg K).T_h
              ha hemit hrow (Nat.le_of_not_gt hpre) hold hfgK
          rw [hKentry] at hKP
          have hKA : Block.Preceq K.erase A.erase := Block.preceq_trans hKP hPA
          obtain ⟨K', hK'A, hK'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift A hKA
          have hK'run : RunBlock S rho K' :=
            Proofs.NamedRuntime.blockInRun_of_ancestor S rho hArun hK'A
          have hK'eq : K' = K := by
            apply adm.toNamedRootCollisionFree.root_injective K' K hK'run hKrun
              K' K (Or.inl (Proofs.NamedAncestry.named_self K'))
                (Or.inr (Proofs.NamedAncestry.named_self K))
            rw [← Proofs.NamedWire.erase_root K', ← Proofs.NamedWire.erase_root K, hK'erase]
          rw [← hKheight]
          exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg (by
            rw [← hK'eq]
            exact hK'A)
      · have hKheads : ∀ x ∈ rho.honest,
            Block.Preceq K.erase (voterHeadAt S rho x d) := by
          intro x hx
          have hsafe := ((SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_core
            S adm hcom hboot hawake hfinality hhor hd hupper hx
              a.round (Nat.le_of_not_gt hold) haTime).2 a.val_index ha).2 _ hfgK
          rw [← hKentry]
          simpa only [voteDutyHead] using hsafe
        have hKprotected := protected_of_heads hKheads
        have hKG : Block.Preceq K.erase G := hmax K.erase hKprotected
        have hKA : Block.Preceq K.erase A.erase := by
          simpa only [hAerased] using hKG
        obtain ⟨K', hK'A, hK'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift A hKA
        have hK'run : RunBlock S rho K' :=
          Proofs.NamedRuntime.blockInRun_of_ancestor S rho hArun hK'A
        have hK'eq : K' = K := by
          apply adm.toNamedRootCollisionFree.root_injective K' K hK'run hKrun
            K' K (Or.inl (Proofs.NamedAncestry.named_self K'))
              (Or.inr (Proofs.NamedAncestry.named_self K))
          rw [← Proofs.NamedWire.erase_root K', ← Proofs.NamedWire.erase_root K, hK'erase]
        rw [← hKheight]
        exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg (by
          rw [← hK'eq]
          exact hK'A)
    · rw [Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hlarge)]
      exact Nat.zero_le _
  have hsourceBand0 := bandAt p hp tp
    (by simpa only [tp, tv, s] using (proposal_time_lt_vote_time S.E s).le)
  have hsourceBand : source.st.core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg A).h := by
    simpa only [source, proposerReadAt, tp, p, s,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      hsourceBand0
  have htargetBand0 := bandAt v hv tv (le_refl _)
  have htargetBand : target.st.core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg A).h := by
    simpa only [target, voteDutyRead, tv, s,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      htargetBand0
  have hparent := SettledBootstrapPreparedV4.protected_preceq_proposedParent_core
    S adm hcom hboot hawake hfinality hhor hd hupper hproposalHor hprop hAprotected
  exact ⟨A, hAprotected, hsourceAnchor, htargetAnchor,
    hsourceBody, htargetBody, hsourceBand, htargetBand, hparent⟩

private theorem SettledBootstrapPreparedV4.honestVoteStoresExtend_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start d : Slot}
    {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hd : start ≤ d)
    (hhor : Protocol.confirmation_time S.E (d + 1) ≤ rho.horizon)
    (hprop : S.E.proposer (d + 1) ∈ rho.honest)
    {B : NamedBlock V} (hB : proposedBlockAt S rho (d + 1) = some B) :
    ∀ v ∈ rho.honest,
      NamedVoteStoreExtends S rho v (d + 1)
        (namedWalkTargetTree S rho (d + 1) v B)
        (proposedParent S rho (d + 1)) B := by
  intro v hv
  have hvoteHor : Protocol.vote_time S.E (d + 1) ≤ rho.horizon :=
    (vote_time_le_confirmation_time S.E (d + 1)).trans hhor
  have hsupportHor : Protocol.support_cutoff S.E d ≤ rho.horizon :=
    (support_cutoff_le_vote_time_succ S.E d).trans hvoteHor
  have hRpos : 0 < S.hc.R :=
    lt_of_lt_of_le (by decide : 0 < 2) S.hc.R_ge_two
  have hround : base + S.hc.η_SG ≤ S.hc.round_of d := by
    change base + S.hc.η_SG ≤ d / S.hc.R
    exact (Nat.le_div_iff_mul_le hRpos).2 (hboot.settled.trans hd)
  have hbaseLt : base < S.hc.round_of d :=
    Nat.lt_of_succ_le ((Nat.add_le_add_left S.hc.η_SG_ge_one base).trans hround)
  have hdPos : 0 < d :=
    (Nat.mul_pos
      (Nat.zero_lt_of_lt (Nat.add_lt_add_left S.hc.η_SG_ge_one base)) hRpos).trans_le
        (hboot.settled.trans hd)
  have hpostProposal : S.E.t_GST ≤
      Protocol.proposal_time S.E ((d + 1) - 1) := by
    simpa only [Nat.add_sub_cancel] using hboot.basePost.trans
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
        ((action_add_delta_le_openingProposal_of_round_lt S hbaseLt).trans
          (proposal_time_mono S.E (Nat.div_mul_le_self d S.hc.R))))
  have hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E d :=
    hboot.basePost.trans
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
        ((action_add_delta_le_openingProposal_of_round_lt S hbaseLt).trans
          ((proposal_time_mono S.E (Nat.div_mul_le_self d S.hc.R)).trans
            (proposal_time_lt_vote_time S.E d).le)))
  have hcandidate := SettledBootstrapPreparedV4.proposedBlock_voterCandidate_core
    S adm hcom hboot hawake hfinality hd hvoteHor hprop hB hv
  obtain ⟨A, hpivot⟩ :=
    SettledBootstrapPreparedV4.exists_protectedProposalPivot_core
      S adm hcom hboot hawake hfinality hd hhor hprop hv
  have hband := PreparedProtectedProposalPivot.frozenBandInputs
    S adm hB hcandidate hpivot
  have hsuffix := namedProposalPivotSuffixTransfer_of_riseLeOne_core
    S adm (Nat.zero_lt_succ d) hpostProposal hprop hv hvoteHor hB hband
  have htarget := PreparedProtectedProposalPivot.preceq_proposalFreeHead_core
    S adm hcom hdPos hpostVote hsupportHor hv hB hpivot
  have hscore := namedProposalScoreEq_afterGST_core
    S adm (Nat.zero_lt_succ d) hpostProposal hprop hv hvoteHor hB hcandidate
  have hparentProposal : Block.Preceq (proposedParent S rho (d + 1)) B.erase := by
    rw [← proposedBlockErased_parent S rho (d + 1) hB]
    exact preceq_parent B.erase
  have hcompat : Block.compatible (voterAnchorAt S rho v (d + 1)) B.erase = true :=
    Block.compatible_of_preceq_common
      (Block.preceq_trans hpivot.targetAnchor
        (Block.preceq_trans hpivot.parent hparentProposal))
      (Block.preceq_self B.erase)
  apply namedProposalWalkTransferred_of_frozenCompatiblePivot_core
    S adm hB hprop hv hcandidate hcompat
  · simpa only [Internal.PhaseGrades.nodeAnchor, Internal.PhaseGrades.nodeRead,
      Protocol.get_sg_root_with] using hpivot.sourceAnchor
  · exact hpivot.parent
  · exact htarget
  · exact hsuffix
  · exact hscore

/-- Every honest voter uses an honest named proposal as its head in the
proposal's own slot. -/
theorem SettledBootstrapPreparedV4.honestProposal_voterHeadAt_eq_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start d : Slot}
    {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hd : start ≤ d)
    (hhor : Protocol.confirmation_time S.E (d + 1) ≤ rho.horizon)
    (hprop : S.E.proposer (d + 1) ∈ rho.honest)
    {B : NamedBlock V} (hB : proposedBlockAt S rho (d + 1) = some B) :
    ∀ v ∈ rho.honest, voterHeadAt S rho v (d + 1) = B.erase := by
  intro v hv
  exact voterHeadAt_eq_proposedBlockAt_of_namedVoteStoreExtends S hB
    (SettledBootstrapPreparedV4.honestVoteStoresExtend_core
      S adm hcom hboot hawake hfinality hd hhor hprop hB v hv)

private theorem preparedV4_voteDuty_mem_confStore_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} {s : Slot} {C : Block V}
    (hC : C ∈ (Proofs.Optimistic.voteDutyStore S rho w s).T) :
    C ∈ (confStore S rho w s).T := by
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
  simpa only [confStore, Proofs.Optimistic.tickStore] using hConfPre

/-- Every strictly post-cut honest named proposal has the complete canonical
proposal duty. -/
theorem SettledBootstrapPreparedV4.canonicalProposalDuty_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot}
    {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    {s : Slot} (hs : start < s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hprop : S.E.proposer s ∈ rho.honest)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B) :
    CanonicalProposalDutyAt S rho s B := by
  have hsPos : 0 < s := (Nat.zero_le start).trans_lt hs
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hsPos)
  have hd : start ≤ d := Nat.le_of_lt_succ hs
  have hvoteHor : Protocol.vote_time S.E (d + 1) ≤ rho.horizon :=
    (vote_time_le_confirmation_time S.E (d + 1)).trans hhor
  have hstoresAll := SettledBootstrapPreparedV4.honestVoteStoresExtend_core
    S adm hcom hboot hawake hfinality hd hhor hprop hB
  have hstoresPackage : VoteStoresExtend S rho (d + 1) B := by
    intro v hv _hcommittee
    exact ⟨namedWalkTargetTree S rho (d + 1) v B,
      proposedParent S rho (d + 1), hstoresAll v hv⟩
  have hnames := honestVotesName_of_voteStoresExtend_core
    S adm (Nat.zero_lt_succ d) hvoteHor hstoresPackage
  have hrun := proposedBlockAt_blockInRun_of_admissible
    S adm (d + 1) (Nat.zero_lt_succ d) hprop
      ((proposal_time_le_confirmation_time S.E (d + 1)).trans hhor) hB
  have hhead (v : V) (hv : v ∈ rho.honest) :
      voterHeadAt S rho v (d + 1) = B.erase :=
    voterHeadAt_eq_proposedBlockAt_of_namedVoteStoreExtends
      S hB (hstoresAll v hv)
  have hanchor : ∀ v ∈ rho.honest,
      Block.Preceq
        (namedConfirmationAnchor S
          (confirmationInputRead S rho v (d + 1))) B.erase := by
    intro v hv
    have hle := SettledBootstrapPreparedV4.preparedConfirmationAnchor_preceq_voterHeadAt_core
      S adm hcom hboot hawake hfinality (hd.trans (Nat.le_succ d)) hhor hv hv
    rw [hhead v hv] at hle
    exact hle
  have hvalidLate : ∀ v ∈ rho.honest,
      Protocol.VoteSetValid S.E (d + 1)
        (confLate S.E (confStore S rho v (d + 1)) (d + 1)) := by
    intro v _
    simpa only [confStore, Proofs.Optimistic.tickStore] using
      voteSetValid_confLate_stateBeforeTime S adm.toNamedScheduleWellFormed v
        (Protocol.confirmation_time S.E (d + 1)) (d + 1)
  have hcandidate : ∀ v ∈ rho.honest,
      B.erase ∈ confTree (confStore S rho v (d + 1)) := by
    intro v hv
    let conf := confStore S rho v (d + 1)
    have hadmit := SettledBootstrapPreparedV4.proposedBlock_admittedBefore_vote_core
      S adm hcom hboot hawake hfinality hd hvoteHor hprop hB hv
    have hBvote : B.erase ∈ (Proofs.Optimistic.voteDutyStore S rho v (d + 1)).T :=
      (admittedBefore_mem_and_stamp_at S adm.toNamedScheduleWellFormed
        hadmit (le_refl _)).1
    have hBconf : B.erase ∈ conf.T :=
      preparedV4_voteDuty_mem_confStore_core S adm hBvote
    obtain ⟨B', hB'body, hB'erase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
        (Protocol.confirmation_time S.E (d + 1)) v (by
          simpa only [conf, confStore, Proofs.Optimistic.tickStore] using hBconf)
    obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
      S adm.toNamedScheduleWellFormed
        (Protocol.confirmation_time S.E (d + 1))
    have hB'prefix : B' ∈ (rho.stateBefore S n v).st.bodies := by
      rw [← congrArg (fun world => (world v).st.bodies) hn]
      exact hB'body
    have hB'run : RunBlock S rho B' :=
      Proofs.Bridges.runBlock_of_stateBefore_mem S hv hB'prefix
    have hB'eq : B' = B := by
      apply adm.toNamedRootCollisionFree.root_injective B' B hB'run hrun
        B' B (Or.inl (Proofs.NamedAncestry.named_self B'))
          (Or.inr (Proofs.NamedAncestry.named_self B))
      rw [← Proofs.NamedWire.erase_root B', ← Proofs.NamedWire.erase_root B, hB'erase]
    have hBbody : B ∈ (rho.stateBeforeTime S
        (Protocol.confirmation_time S.E (d + 1)) v).st.bodies := by
      rw [← hB'eq]
      exact hB'body
    have hBview : conf.σ B.erase = Protocol.derive_named S.E S.cfg B := by
      simpa only [conf, confStore, Proofs.Optimistic.tickStore] using
        Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho
          (Protocol.confirmation_time S.E (d + 1)) v B hBbody
    have hband := SettledBootstrapPreparedV4.confirmationReadBand_le_voterHeadHeight_core
      S adm hcom hboot hawake hfinality (hd.trans (Nat.le_succ d)) hhor
        (v := v) (x := v) hv (X := B) (by rw [hhead v hv]) hrun
    have hroot : Block.Preceq
        (Protocol.get_fg_root conf.toHealing.toFG) B.erase :=
      Block.preceq_trans (by
        simpa only [conf, Proofs.Optimistic.confStore_eq_confirmationInputRead] using
          fg_root_preceq_get_sg_root_with_frame
            (confirmationInputRead S rho v (d + 1)).cache
            S.E S.hc conf.toHealing (S.hc.round_of conf.s)) (hanchor v hv)
    have hFJ : Block.Preceq conf.F conf.J := by
      simpa only [conf, confStore, Proofs.Optimistic.tickStore] using
        Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
          S rho (Protocol.confirmation_time S.E (d + 1)) v
    have hFB : Block.Preceq conf.F B.erase :=
      Block.preceq_trans
        (Proofs.Records.preceq_get_fg_root_of_F (st := conf.toHealing.toFG) hFJ) hroot
    simp only [confTree, Protocol.get_filtered_block_tree,
      Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq]
    exact ⟨⟨⟨hBconf, hFB⟩, B.erase, hBconf, Block.preceq_self _, by
      change conf.h_max - 1 ≤ (conf.σ B.erase).h
      rw [hBview]
      simpa only [conf, Proofs.Optimistic.confStore_eq_confirmationInputRead] using hband⟩,
      hroot⟩
  have hcone : NamedHonestVotesCone S rho (d + 1)
      (fun X => Block.Preceq B.erase X) :=
    honestVotesCone_preceq S rho (d + 1) hrun hnames
  have hpost : S.E.t_GST ≤ Protocol.vote_time S.E (d + 1) := by
    have hRpos : 0 < S.hc.R :=
      lt_of_lt_of_le (by decide : 0 < 2) S.hc.R_ge_two
    have hround : base + S.hc.η_SG ≤ S.hc.round_of d := by
      change base + S.hc.η_SG ≤ d / S.hc.R
      exact (Nat.le_div_iff_mul_le hRpos).2 (hboot.settled.trans hd)
    have hbaseLt : base < S.hc.round_of d :=
      Nat.lt_of_succ_le
        ((Nat.add_le_add_left S.hc.η_SG_ge_one base).trans hround)
    exact hboot.basePost.trans (((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
      ((action_add_delta_le_openingProposal_of_round_lt S hbaseLt).trans
        (proposal_time_mono S.E (Nat.div_mul_le_self d S.hc.R)))).trans
          ((proposal_time_mono S.E (Nat.le_succ d)).trans
            (proposal_time_lt_vote_time S.E (d + 1)).le))
  have hresolve : ∀ v ∈ rho.honest,
      HeadsResolveIn S rho (d + 1)
        (confStore S rho v (d + 1)).T
        (confStore S rho v (d + 1)).timestamp_block := by
    intro v hv
    let conf := confStore S rho v (d + 1)
    have hroot : Block.Preceq
        (Protocol.get_fg_root conf.toHealing.toFG) B.erase :=
      Block.preceq_trans (by
        simpa only [conf, Proofs.Optimistic.confStore_eq_confirmationInputRead] using
          fg_root_preceq_get_sg_root_with_frame
            (confirmationInputRead S rho v (d + 1)).cache
            S.E S.hc conf.toHealing (S.hc.round_of conf.s)) (hanchor v hv)
    exact WeakGoldfish.headsResolveIn_confStore_of_postHealingCone
      S adm hv hpost
        ((support_cutoff_le_confirmation_time S.E (d + 1)).trans hhor)
        hroot hcone
  exact CanonicalSuffixProposalStoreFacts.duty_core adm
    (Nat.zero_lt_succ d) hpost hhor
      { run := hrun
        names := hnames
        validLate := hvalidLate
        anchor := hanchor
        candidate := hcandidate
        resolve := hresolve }

/-- Closed genuine-confirmation output for a canonical post-cut proposal. -/
theorem SettledBootstrapPreparedV4.honestProposal_genuineConfirmationWith_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    {s : Slot} (hs : start < s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hprop : S.E.proposer s ∈ rho.honest)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B)
    {v : V} (hv : v ∈ rho.honest) :
    GenuineConfirmationWith
      (NamedProfile.gradeContract
        (confirmationInputRead S rho v s).cache)
      S.E S.hc (confStore S rho v s) s B.erase :=
  genuineConfirmation_of_dutyExecution S hcom
    (SettledBootstrapPreparedV4.canonicalProposalDuty_core
      S adm hcom hboot hawake hfinality hs hhor hprop hB) hv

/-- Closed live-confirmed output for a canonical post-cut proposal. -/
theorem SettledBootstrapPreparedV4.honestProposal_liveConfirmed_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    {s : Slot} (hs : start < s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hprop : S.E.proposer s ∈ rho.honest)
    {B : NamedBlock V} (hB : proposedBlockAt S rho s = some B)
    {v : V} (hv : v ∈ rho.honest) :
    (rho.storeAt S v (Protocol.confirmation_time S.E s)).live_confirmed =
      B.erase := by
  rw [live_confirmed_eq_update
    S adm.toNamedScheduleWellFormed hv s hhor]
  exact updateConfirmation_eq_proposedBlock_of_dutyExecution
    S hcom (SettledBootstrapPreparedV4.canonicalProposalDuty_core
      S adm hcom hboot hawake hfinality hs hhor hprop hB) hv

#print axioms SettledBootstrapPreparedV4.honestProposal_voterHeadAt_eq_core
#print axioms SettledBootstrapPreparedV4.canonicalProposalDuty_core
#print axioms SettledBootstrapPreparedV4.honestProposal_genuineConfirmationWith_core
#print axioms SettledBootstrapPreparedV4.honestProposal_liveConfirmed_core

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
