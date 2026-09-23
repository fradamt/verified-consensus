module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.PreparedV4ProtectedVoteSlotsCore
public import DecoupledConsensusProofs.Protocol.Schedule.GSTZeroReorgResilienceCoreNamed

@[expose] public section

/-!
# Prepared V4 protected vote slot at the actual vote horizon

This leaf ports the W5 actual-vote successor to the prepared V4 cut.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Internal.NamedRecoveryRead Protocol Proofs.Optimistic
  HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem postCut_protectedVoteSlot_succ_at_vote_of_inputs
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    (hmajority : HonestWeightMajority S rho.honest)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    {B : Block V} (hB : ProtectedVoteSlot S rho s B)
    (hwitnesses : ∀ w ∈ rho.honest,
      ∀ {C : NamedBlock V}, C.erase = B →
      (Protocol.derive_named S.E S.cfg C).h <
        (voteDutyRead S rho w (s + 1)).st.core.h_max - 1 →
      RunBlock S rho C →
      ∀ (a : NamedAttestation V) (ta : Time) (K : NamedBlock V),
        a.val_index ∈ rho.honest →
        NamedRun.emits S rho a.val_index (Object.attest a) ta →
        ta < Protocol.vote_time S.E (s + 1) →
        a.height_pair.erase.height? =
          some ((voteDutyRead S rho w (s + 1)).st.core.h_max - 1) →
        fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
          some (Protocol.derive_named S.E S.cfg K).T_h →
        RunBlock S rho K →
        Block.compatible C.erase
          (Protocol.derive_named S.E S.cfg K).T_h = true)
    (hroots : ∀ w ∈ rho.honest, Block.compatible
      (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) B = true)
    (hanchors : ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w (s + 1)) B = true) :
    ProtectedVoteSlot S rho (s + 1) B := by
  have hheads : ∀ w ∈ rho.honest,
      Block.Preceq B (voterHeadAt S rho w (s + 1)) := by
    intro w hw
    have hcases : Block.Preceq
          (Protocol.get_fg_root
            (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) B ∨
        Block.Preceq B
          (Protocol.get_fg_root
            (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) := by
      simpa only [Block.compatible, Bool.or_eq_true] using hroots w hw
    rcases hcases with hroot | habove
    · obtain ⟨D, hBD, hprocessed, hband⟩ :=
        Protocol.coneBandDescendant_of_frontierWitnesses_at_vote_core
          S adm hcom hmajority hpost hhor hB.cone hw
            (hwitnesses w hw) hroot
      have hcandidate :=
        WeakJoint.namedCandidatePath_of_processedBandDescendant_core
          S adm hw hBD hprocessed hband hroot
      let read := voteDutyRead S rho w (s + 1)
      let st := read.st.core
      let votes := Protocol.voter_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
      let support := Protocol.voter_support_view S.E st.toHealing.toFG.toSG.toGoldfishStore st.s
      let tree := voterCandidateTreeAt S rho w (s + 1)
      have hcutHor : Protocol.support_cutoff S.E s ≤ rho.horizon :=
        (support_cutoff_le_vote_time_succ S.E s).trans hhor
      have havailable :=
        honestHeadsAvailableBefore_of_namedPostHealingCone_core
          S adm hw hpost hcutHor hroot hB.cone
      have hresolve0 := headsResolveIn_storeBeforeTime_of_availableBefore_at_core
        S adm hw s (support_cutoff_le_vote_time_succ S.E s) havailable
      have hresolve : HeadsResolveIn S rho s st.T st.timestamp_block := by
        simpa only [st, read, voteDutyRead,
          NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
          using hresolve0
      have hbase := canonicalSuffixConeSupportVoterView_core
        S adm hcom hs hpost hcutHor hB.cone hw
          (support_cutoff_le_vote_time_succ S.E s)
          (gst := st.toHealing.toFG.toSG.toGoldfishStore) (by rfl) (by rfl) (by rfl)
          (hresolve.of_eq rfl rfl)
      have hslot : st.s = s + 1 := by
        simpa only [st, read] using voteDutyRead_slot S rho w (s + 1)
      have hcone : ConeSupport S.E st.T votes support votes (st.s - 1)
          rho.honest (fun X => Block.Preceq B X) := by
        simpa only [st, read, votes, support, hslot,
          Protocol.Store.toHealing] using hbase
      have hvalid := Protocol.voteDutyRead_voteViewValid_core
        S adm w (s + 1)
      have hmajor : Protocol.voters_count S.E votes (st.s - 1) <
          2 * (Protocol.goldfishSupporters S.E st.T votes support
            (st.s - 1) B).card :=
        supporterMajority_of_cone S.E hcone hvalid
      have hpath : ∀ D : Block V,
          Block.Preceq (voterAnchorAt S rho w (s + 1)) D →
          D ≠ voterAnchorAt S rho w (s + 1) →
          Block.Preceq D B → D ∈ tree := by
        intro D hAD hDne hDB
        by_cases hEq : D = B
        · simpa only [hEq, tree] using hcandidate.1
        · simpa only [tree] using hcandidate.2 D hAD hDne hDB hEq
      have hhead := goldfish_fork_choice_captures_supporter_majority
        S.E st.σ st.h_max st.T tree st.s votes support (st.s - 1)
          (ConeSupport.sub hcone) hmajor (hanchors w hw)
          (fun _ D hAD hDne hDB => hpath D hAD hDne hDB)
      change Block.Preceq B
        (Protocol.get_head_in_tree_with_layer
          (NamedProfile.gradeContract read.cache) S.E S.hc st.toHealing
          tree votes support (st.s - 1))
      simpa only [get_head_in_tree_eq_voterHeadAt_of_anchor,
        read, st, tree] using hhead
    · exact Block.preceq_trans habove
        (fgRoot_preceq_voterHeadAt S rho w (s + 1))
  refine ⟨hheads, ?_⟩
  intro w hw hcommittee
  obtain ⟨X, hXe, hXrun, hXemit⟩ :=
    WeakGoldfish.voterHead_runBlock_and_emits
      S adm hw (Nat.succ_pos s) hcommittee hhor
  exact ⟨X, hXe ▸ hheads w hw, hXrun, hXemit⟩

/-- Cut-parametric action sources used by the actual-vote successor and by
the public post-cut action-source theorem. -/
theorem SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_aux
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start last d : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hd : start ≤ d) (hupper : d ≤ last + 1)
    {x : V} (hx : x ∈ rho.honest) :
    ∀ r, base + S.hc.η_SG ≤ r →
      S.a r < Protocol.vote_time S.E (d + 1) →
      (∀ w ∈ rho.honest,
        NamedRun.emits S rho w
          (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
        Block.Preceq (actionSGBlockAt S rho w r) (voterHeadAt S rho x d)) ∧
      (∀ w ∈ rho.honest,
        Block.Preceq (Protocol.get_fg_root
          (actionStoreAt S rho w r).st.core.toHealing.toFG)
          (voterHeadAt S rho x d) ∧
        ∀ T, fgConfirmationWitness S (actionStoreAt S rho w r) = some T →
          Block.Preceq T (voterHeadAt S rho x d)) := by
  have hcutpos : 0 < base + S.hc.η_SG :=
    Nat.zero_lt_of_lt (Nat.add_lt_add_left S.hc.η_SG_ge_one base)
  have hstartUpper : start ≤ last + 1 := hd.trans hupper
  have hmajority := honestWeightMajority_of_finiteWindowsFrom
    S hawake hcutpos hboot.settled hstartUpper hhor
  have hslots := SettledBootstrapPreparedV4.protectedVoteSlots_core
    S adm hcom hboot hawake hfinality hhor
  have hslot := hslots d hd hupper
  have hspan : base ≤ base + S.hc.η_SG - S.hc.η_SG :=
    Nat.le_sub_of_add_le (Nat.le_refl _)
  obtain ⟨hlegacyActionRoots, -⟩ :=
    WeakJoint.legacyRootCallbacks_of_finiteBootstrap_complete
      S adm (last := d) hboot.oldRows hfinality
        hboot.frontierSeed hboot.fgAll
  have hsources :=
    WeakJoint.actionSources_preceq_of_priorConfirmations_and_historyCut
      S adm hmajority (base := base) (cut := base + S.hc.η_SG)
        (s := d) (D := voterHeadAt S rho x d) hspan
        (fun r hr hrcut _ w hw hemit =>
          Block.preceq_trans (hboot.sgBoot r hr hrcut w hw hemit)
            (hslot.1.heads x hx))
        (fun q hq hqd w hw B hB =>
          (hslot.2 q hq hqd w hw B hB).heads x hx)
        (fun r hr ht w hw C a hC hJ ha hemit hold hpair hT =>
          Block.preceq_trans
            (hlegacyActionRoots r hr ht
              w hw C a hC hJ ha hemit hold hpair hT)
            (hslot.1.heads x hx))
        (by
          intro r hr hrpos ht hsg hroots
          have hactionHor : S.a r ≤ rho.horizon :=
            (action_le_supportCutoff_of_lt_nextVote S ht).trans
              ((support_cutoff_mono S.E hupper).trans (by
                simpa only [Protocol.confirmation_time_eq_support_cutoff_succ]
                  using hhor))
          have hawakeR := hawake r hr
            ((Assembly.a_mono S (Nat.sub_le r 1)).trans hactionHor)
          apply WeakJoint.actionGradeFormationAt_of_awakeWindowMajority
            S adm hrpos hawakeR
          intro p hp
          apply relativeGradeCarrierAt_of_awakeWindowMajority
            S adm hrpos hawakeR
          exact WeakJoint.relativeCarrierWindowAt_of_awakeWindowHistory_w
            S adm
              (NamedOutageClosure.healthyWindowDelivery_after_gst S rho adm)
              (le_refl _) (le_refl _) hrpos
              (hspan.trans (Nat.sub_le_sub_right hr S.hc.η_SG))
              (fun k hk _ => hboot.basePost.trans (Assembly.a_mono S hk))
              hawakeR hsg hroots p hp)
  intro r hr ht
  have hcurrent := hsources r
    ((Nat.le_add_right base S.hc.η_SG).trans hr) ht
  exact ⟨hcurrent.1, hcurrent.2 hr⟩

#print axioms SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_aux

/-- A protected block at slot `s` remains protected at the actual next vote
horizon after the V4 cut. -/
theorem SettledBootstrapPreparedV4.protectedVoteSlot_succ_at_vote_core
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start s : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (hd : start ≤ s) (hhor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    {B : Block V} (hPB : Block.Preceq P.erase B)
    (hB : ProtectedVoteSlot S rho s B) :
    ProtectedVoteSlot S rho (s + 1) B := by
  have hRpos : 0 < S.hc.R :=
    lt_of_lt_of_le (by decide : 0 < 2) S.hc.R_ge_two
  have hcutpos : 0 < base + S.hc.η_SG :=
    Nat.zero_lt_of_lt (Nat.add_lt_add_left S.hc.η_SG_ge_one base)
  have hs : 0 < s :=
    (Nat.mul_pos hcutpos hRpos).trans_le (hboot.settled.trans hd)
  have hsEq : s - 1 + 1 = s := Nat.sub_add_cancel hs
  have hprevHor : Protocol.confirmation_time S.E (s - 1) ≤ rho.horizon := by
    rw [Protocol.confirmation_time_eq_support_cutoff_succ, hsEq]
    exact (support_cutoff_le_vote_time_succ S.E s).trans hhor
  have hprev := SettledBootstrapPreparedV4.protectedVoteSlots_core
    S adm hcom hboot hawake hfinality hprevHor s hd hsEq.symm.le
  have hmajority := honestWeightMajority_of_finiteWindowsFrom
    S hawake hcutpos (hboot.settled.trans hd) hsEq.symm.le hprevHor
  have hspan : base ≤ base + S.hc.η_SG - S.hc.η_SG :=
    Nat.le_sub_of_add_le (Nat.le_refl _)
  have hbaseCut : base < base + S.hc.η_SG :=
    Nat.lt_of_succ_le (Nat.add_le_add_left S.hc.η_SG_ge_one base)
  have hpost : S.E.t_GST ≤ Protocol.vote_time S.E s := by
    have ht := action_add_delta_le_openingProposal_of_round_lt S hbaseCut
    exact hboot.basePost.trans
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
        ((ht.trans (proposal_time_mono S.E (hboot.settled.trans hd))).trans
          (proposal_time_lt_vote_time S.E s).le))
  have hgap : base + S.hc.η_SG ≤ S.hc.round_of (s + 1) := by
    change base + S.hc.η_SG ≤ (s + 1) / S.hc.R
    exact (Nat.le_div_iff_mul_le hRpos).2
      ((hboot.settled.trans hd).trans (Nat.le_succ s))
  have hpositive : 0 < ((S.E.committee s) ∩ rho.honest).card := by
    have hc := hcom s
    omega
  obtain ⟨x, hxmem⟩ := Finset.card_pos.mp hpositive
  have hx : x ∈ rho.honest := (Finset.mem_inter.mp hxmem).2
  have hupper : s ≤ (s - 1) + 1 := hsEq.symm.le
  have haction :=
    SettledBootstrapPreparedV4.actionSources_preceq_voteDutyHead_aux
      S adm hcom hboot hawake hfinality hprevHor hd hupper hx
  obtain ⟨hlegacyActionRoots, hlegacyReadRoots⟩ :=
    WeakJoint.legacyRootCallbacks_of_finiteBootstrap_complete
      S adm (last := s) hboot.oldRows hfinality
        hboot.frontierSeed hboot.fgAll
  have hfullSG : ∀ k, base ≤ k → k < S.hc.round_of (s + 1) →
      ∀ u ∈ rho.honest,
      NamedRun.emits S rho u
        (Object.attest (actionAttestationAt S rho u k)) (S.a k) →
      Block.Preceq (actionSGBlockAt S rho u k)
        (voterHeadAt S rho x s) := by
    intro k hk hklt u hu hemit
    by_cases hold : k < base + S.hc.η_SG
    · exact Block.preceq_trans (hboot.sgBoot k hk hold u hu hemit)
        (hprev.1.heads x hx)
    · exact (haction k (Nat.le_of_not_gt hold)
        (action_before_vote_of_round_lt S hklt)).1 u hu hemit
  have hfgB : ∀ r, base + S.hc.η_SG ≤ r →
      S.a r < Protocol.vote_time S.E (s + 1) →
      ∀ u ∈ rho.honest, ∀ T,
      fgConfirmationWitness S (actionStoreAt S rho u r) = some T →
      Block.compatible B T = true := by
    intro r hr ht u hu T hT
    exact Block.compatible_of_preceq_common (hB.heads x hx)
      (((haction r hr ht).2 u hu).2 T hT)
  have hrootCompatB : ∀ u ∈ rho.honest, ∀ (C : NamedBlock V)
      (a : NamedAttestation V) (ta : Time),
      let R := Protocol.get_fg_root
        (rho.storeBeforeTime S u
          (Protocol.vote_time S.E (s + 1))).toHealing.toFG
      C ∈ (rho.storeBeforeTime S u
        (Protocol.vote_time S.E (s + 1))).bodies →
      (Protocol.derive_named S.E S.cfg C).J = R →
      a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (Object.attest a) ta →
      ta < Protocol.vote_time S.E (s + 1) →
      a.round < base + S.hc.η_SG →
      a.height_pair.erase = HeightPair.target
        (Protocol.derive_named S.E S.cfg C).h_j
        (Protocol.derive_named S.E S.cfg C).J.root →
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
        some R →
      Block.compatible B R = true := by
    intro u hu C a ta
    dsimp only
    intro hC hJ ha hemit hta hold hpair hT
    have hRP := hlegacyReadRoots (s + 1) (Nat.lt_succ_of_le hd)
      (le_refl _) u hu C a ta hC hJ ha hemit hta hold hpair hT
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr (Block.preceq_trans hRP hPB)
  have hrootB : ∀ u ∈ rho.honest, Block.compatible
      (Protocol.get_fg_root
        (voteDutyRead S rho u (s + 1)).st.core.toHealing.toFG) B = true := by
    intro u hu
    have hroot := WeakFG.fgRoot_compatible_of_bootstrap_and_recentActions_at_read
      S adm hmajority hu (time := Protocol.vote_time S.E (s + 1))
      (cut := base + S.hc.η_SG) (B := B) hfgB (hrootCompatB u hu)
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
      using hroot
  have hfrontierB : ∀ u ∈ rho.honest, ∀ {C : NamedBlock V}, C.erase = B →
      (Protocol.derive_named S.E S.cfg C).h <
        (voteDutyRead S rho u (s + 1)).st.core.h_max - 1 →
      RunBlock S rho C →
      ∀ (a : NamedAttestation V) (ta : Time) (K : NamedBlock V),
        a.val_index ∈ rho.honest →
        NamedRun.emits S rho a.val_index (Object.attest a) ta →
        ta < Protocol.vote_time S.E (s + 1) →
        a.height_pair.erase.height? =
          some ((voteDutyRead S rho u (s + 1)).st.core.h_max - 1) →
        fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
          some (Protocol.derive_named S.E S.cfg K).T_h →
        RunBlock S rho K →
        Block.compatible C.erase
          (Protocol.derive_named S.E S.cfg K).T_h = true := by
    intro u hu C hCB _ _ a ta K ha hemit hta hrow hselected _
    by_cases hold : a.round < base + S.hc.η_SG
    · by_cases hpre : a.round < fresh
      · rcases hboot.frontierSeed with hzero | hfrontier
        · rw [hzero] at hpre
          exact False.elim (Nat.not_lt_zero _ hpre)
        · have hbound := hboot.oldRows a ta _ ha hemit hpre hrow
          have htime : min (S.a (base + S.hc.η_SG))
              (Protocol.vote_time S.E start) ≤
              Protocol.vote_time S.E (s + 1) :=
            (min_le_right _ _).trans
              (vote_time_mono_slots S.E (hd.trans (Nat.le_succ s)))
          have hmono := storeBeforeTime_hMax_mono
            S adm.toNamedScheduleWellFormed u htime
          have hgapNow := (hfrontier u hu).trans_le hmono
          have hsame : (voteDutyRead S rho u (s + 1)).st.core.h_max =
              (rho.storeBeforeTime S u
                (Protocol.vote_time S.E (s + 1))).h_max := by rfl
          rw [hsame] at hbound
          have hcapSucc : cap + 1 ≤
              (rho.storeBeforeTime S u
                (Protocol.vote_time S.E (s + 1))).h_max - 1 :=
            Nat.le_sub_one_of_lt hgapNow
          exact False.elim
            ((Nat.not_lt_of_ge (hcapSucc.trans hbound)) (Nat.lt_succ_self cap))
      · have hTP := hboot.fgAll a ta _
          (Protocol.derive_named S.E S.cfg K).T_h
          ha hemit hrow (Nat.le_of_not_gt hpre) hold hselected
        rw [hCB]
        exact Block.compatible_of_preceq_common
          (hB.heads x hx) (Block.preceq_trans hTP (hprev.1.heads x hx))
    · have htime : S.a a.round < Protocol.vote_time S.E (s + 1) := by
        simpa only [(emits_attest_shape S hemit).2] using hta
      rw [hCB]
      exact Block.compatible_of_preceq_common (hB.heads x hx)
        (((haction a.round (Nat.le_of_not_gt hold) htime).2
          a.val_index ha).2 _ hselected)
  have hanchorB : ∀ u ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho u (s + 1)) B = true := by
    intro u hu
    by_cases hrzero : S.hc.round_of (s + 1) = 0
    · rw [WeakGenesis.voterAnchorAt_eq_fgRoot_of_round_zero
        S adm u (s + 1) hrzero]
      exact hrootB u hu
    · have hrpos : 0 < S.hc.round_of (s + 1) :=
        Nat.pos_of_ne_zero hrzero
      have hrootD : ∀ z ∈ rho.honest, Block.compatible
          (Protocol.get_fg_root
            (voteDutyRead S rho z (s + 1)).st.core.toHealing.toFG)
          (voterHeadAt S rho x s) = true := by
        intro z hz
        have hfgD : ∀ r, base + S.hc.η_SG ≤ r →
            S.a r < Protocol.vote_time S.E (s + 1) →
            ∀ y ∈ rho.honest, ∀ T,
            fgConfirmationWitness S (actionStoreAt S rho y r) = some T →
            Block.compatible (voterHeadAt S rho x s) T = true := by
          intro r hr ht y hy T hT
          exact Block.compatible_of_preceq_common
            (Block.preceq_self (voterHeadAt S rho x s))
            (((haction r hr ht).2 y hy).2 T hT)
        have hlegacyD := fun (C : NamedBlock V) (a : NamedAttestation V)
            (ta : Time) =>
          hrootCompatB z hz C a ta
        have hroot := WeakFG.fgRoot_compatible_of_bootstrap_and_recentActions_at_read
          S adm hmajority hz (time := Protocol.vote_time S.E (s + 1))
          (cut := base + S.hc.η_SG) (B := voterHeadAt S rho x s)
          hfgD (by
            intro C a ta
            dsimp only
            intro hC hJ ha hemit hta hold hpair hT
            have hRP := hlegacyReadRoots (s + 1) (Nat.lt_succ_of_le hd)
              (le_refl _) z hz C a ta hC hJ ha hemit hta hold hpair hT
            simp only [Block.compatible, Bool.or_eq_true]
            exact Or.inr (Block.preceq_trans hRP (hprev.1.heads x hx)))
        simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock]
          using hroot
      have hwindowStart : base ≤ S.hc.round_of (s + 1) - S.hc.η_SG :=
        hspan.trans (Nat.sub_le_sub_right hgap _)
      have hcapEarly : DecoupledConsensusModel.Protocol.early S.E S.hc
          (S.hc.round_of (s + 1)) .g1 ≤ rho.horizon := by
        have hdomain : DecoupledConsensusModel.Protocol.domain S.E S.hc
            (S.hc.round_of (s + 1)) .g1 ≤
            Protocol.vote_time S.E (s + 1) := by
          rw [NamedOutageClosure.domain_g1_eq_opening]
          exact (proposal_time_mono S.E
            (Nat.div_mul_le_self (s + 1) S.hc.R)).trans
              (proposal_time_lt_vote_time S.E (s + 1)).le
        exact (NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1
          S (S.hc.round_of (s + 1))).trans (hdomain.trans hhor)
      have hinterpreted := WeakJoint.interpretedInputs_at_voteDuty_w
        S adm (NamedOutageClosure.healthyWindowDelivery_after_gst S rho adm)
        (le_refl _) (base := base) (r := S.hc.round_of (s + 1))
        (d := s + 1) (B := voterHeadAt S rho x s) rfl hrpos hwindowStart
        (fun k hk _ => hboot.basePost.trans (Assembly.a_mono S hk))
        hfullSG hrootD hcapEarly hhor
      have hwindowB : Internal.PhaseGrades.WindowMajorityAt S.E S.hc
          (voteDutyRead S rho u (s + 1)).st.core.toHealing.gradeView
          (voteDutyRead S rho u (s + 1)).st.core.F
          rho.honest (S.hc.round_of (s + 1))
          (DecoupledConsensusModel.Protocol.late S.E S.hc
            (S.hc.round_of (s + 1)) .g1) := by
        apply WeakSG.windowMajorityAt_of_awakeWindowMajority S
          (hawake _ hgap ((windowSourceTime_le_vote S hrpos).trans hhor))
        intro v hv
        obtain ⟨hvHon, k, hk, huk⟩ := WeakSG.mem_honestAwakeWindow_iff.mp hv
        obtain ⟨input, hinput, -, -, -⟩ :=
          hinterpreted u hu v hvHon k hk huk
        refine ⟨input, ?_⟩
        exact GradeCutoffMono.interpretedInputs_mono
          (voteDutyRead S rho u (s + 1)).st.core.toHealing.gradeView
          (voteDutyRead S rho u (s + 1)).st.core.F
          S.hc.η_SG (S.hc.round_of (s + 1))
          (NamedOutageClosure.q10_early_le_late S
            (S.hc.round_of (s + 1)) .g1) v hinput
      have hhistoryB : ∀ k ∈ Protocol.latest_window S.hc.η_SG
          (S.hc.round_of (s + 1)),
          HonestSGEmissionsCompatibleAtRound S rho k B := by
        intro k hk y hy hemit
        have hcarrier := hfullSG k
          (hwindowStart.trans (WeakSG.mem_latestWindow_lower_bound hk))
          (mem_latestWindow_lt hk) y hy hemit
        exact Block.compatible_of_preceq_common hcarrier (hB.heads x hx)
      have hbatchB := WeakJoint.batchCompatibleAt_of_historyCutEmissions
        S adm hu hhistoryB
      let read := voteDutyRead S rho u (s + 1)
      have hslot : read.st.core.s = s + 1 :=
        voteDutyRead_slot S rho u (s + 1)
      rcases voterAnchorAt_cases S rho u (s + 1) with hroot |
          ⟨raw, A, hframe, hactive, hA⟩
      · rw [hroot]
        exact hrootB u hu
      · have hframeRead :
            (DecoupledConsensusModel.Protocol.readFrame read.cache read.st.core.toHealing
              (S.hc.round_of (s + 1))).g1 = some (some raw) := by
          simpa only [read, hslot] using hframe
        have hgrade := WeakJoint.preparedVoteDutyG1FrameGrade_of_activePrefix
          S adm rfl hrpos hhor u hu raw hframeRead A hactive
        have hanchor := WeakSG.getSgRoot_compatible_of_windowHistory_at_read
          S read (S.hc.round_of (s + 1)) B hbatchB hwindowB
          (fun raw' hframe' => by
            have heq : raw' = raw :=
              Option.some.inj (Option.some.inj (hframe'.symm.trans hframeRead))
            simpa only [heq] using hgrade)
          (hrootB u hu)
        simpa only [voterAnchorAt, Internal.PhaseGrades.nodeAnchor,
          Internal.PhaseGrades.nodeRead, Protocol.get_sg_root_with,
          read, hslot, hA] using hanchor
  exact postCut_protectedVoteSlot_succ_at_vote_of_inputs
    S adm hcom hmajority hs hpost hhor hB hfrontierB hrootB hanchorB

#print axioms SettledBootstrapPreparedV4.protectedVoteSlot_succ_at_vote_core

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
